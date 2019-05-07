use self::env_elaborator::elaborate_env_clauses;
use self::program_clauses::ToProgramClauses;
use crate::RustIrDatabase;
use chalk_ir::cast::{Cast, Caster};
use chalk_ir::could_match::CouldMatch;
use chalk_ir::*;
use rustc_hash::FxHashSet;
use std::sync::Arc;

mod env_elaborator;
pub mod program_clauses;

/// For auto-traits, we generate a default rule for every struct,
/// unless there is a manual impl for that struct given explicitly.
///
/// So, if you have `impl Send for MyList<Foo>`, then we would
/// generate no rule for `MyList` at all -- similarly if you have
/// `impl !Send for MyList<Foo>`, or `impl<T> Send for MyList<T>`.
///
/// But if you have no rules at all for `Send` / `MyList`, then we
/// generate an impl based on the field types of `MyList`. For example
/// given the following program:
///
/// ```notrust
/// #[auto] trait Send { }
///
/// struct MyList<T> {
///     data: T,
///     next: Box<Option<MyList<T>>>,
/// }
///
/// ```
///
/// we generate:
///
/// ```notrust
/// forall<T> {
///     Implemented(MyList<T>: Send) :-
///         Implemented(T: Send),
///         Implemented(Box<Option<MyList<T>>>: Send).
/// }
/// ```
pub fn push_auto_trait_impls(
    auto_trait_id: TraitId,
    struct_id: StructId,
    program: &dyn RustIrDatabase,
    vec: &mut Vec<ProgramClause>,
) {
    debug_heading!(
        "push_auto_trait_impls({:?}, {:?})",
        auto_trait_id,
        struct_id
    );

    let auto_trait = &program.trait_datum(auto_trait_id);
    let struct_datum = &program.struct_datum(struct_id);

    // Must be an auto trait.
    assert!(auto_trait.is_auto_trait());

    // Auto traits never have generic parameters of their own (apart from `Self`).
    assert_eq!(auto_trait.binders.binders.len(), 1);

    // If there is a `impl AutoTrait for Foo<..>` or `impl !AutoTrait
    // for Foo<..>`, where `Foo` is the struct we're looking at, then
    // we don't generate our own rules.
    if program.impl_provided_for(auto_trait_id, struct_id) {
        debug!("impl provided");
        return;
    }

    vec.push({
        // trait_ref = `MyStruct<...>: MyAutoTrait`
        let auto_trait_ref = TraitRef {
            trait_id: auto_trait.binders.value.trait_ref.trait_id,
            parameters: vec![Ty::Apply(struct_datum.binders.value.self_ty.clone()).cast()],
        };

        // forall<P0..Pn> { // generic parameters from struct
        //   MyStruct<...>: MyAutoTrait :-
        //      Field0: MyAutoTrait,
        //      ...
        //      FieldN: MyAutoTrait
        // }
        struct_datum
            .binders
            .map_ref(|struct_contents| ProgramClauseImplication {
                consequence: auto_trait_ref.clone().cast(),
                conditions: struct_contents
                    .fields
                    .iter()
                    .cloned()
                    .map(|field_ty| TraitRef {
                        trait_id: auto_trait_id,
                        parameters: vec![field_ty.cast()],
                    })
                    .casted()
                    .collect(),
            })
            .cast()
    });
}

/// Given some goal `goal` that must be proven, along with
/// its `environment`, figures out the program clauses that apply
/// to this goal from the Rust program. So for example if the goal
/// is `Implemented(T: Clone)`, then this function might return clauses
/// derived from the trait `Clone` and its impls.
pub fn program_clauses_for_goal<'db>(
    db: &'db dyn RustIrDatabase,
    environment: &Arc<Environment>,
    goal: &DomainGoal,
) -> Vec<ProgramClause> {
    debug_heading!(
        "program_clauses_for_goal(goal={:?}, environment={:?})",
        goal,
        environment
    );

    let mut vec = vec![];
    vec.extend(db.custom_clauses());
    program_clauses_that_could_match(db, environment, goal, &mut vec);
    program_clauses_for_env(db, environment, &mut vec);
    vec.retain(|c| c.could_match(goal));

    debug!("vec = {:#?}", vec);

    vec
}

/// Returns a set of program clauses that could possibly match
/// `goal`. This can be any superset of the correct set, but the
/// more precise you can make it, the more efficient solving will
/// be.
fn program_clauses_that_could_match(
    db: &dyn RustIrDatabase,
    environment: &Arc<Environment>,
    goal: &DomainGoal,
    clauses: &mut Vec<ProgramClause>,
) {
    match goal {
        DomainGoal::Holds(WhereClause::Implemented(trait_ref)) => {
            let trait_id = trait_ref.trait_id;

            // This is needed for the coherence related impls, as well
            // as for the `Implemented(Foo) :- FromEnv(Foo)` rule.
            db.trait_datum(trait_id).to_program_clauses(db, clauses);

            for impl_id in db.impls_for_trait(trait_id) {
                db.impl_datum(impl_id).to_program_clauses(db, clauses);
            }

            // If this is a `Foo: Send` (or any auto-trait), then add
            // the automatic impls for `Foo`.
            let trait_datum = db.trait_datum(trait_id);
            if trait_datum.is_auto_trait() {
                match trait_ref.parameters[0].assert_ty_ref() {
                    Ty::Apply(apply) => {
                        if let TypeName::TypeKindId(TypeKindId::StructId(struct_id)) = apply.name {
                            push_auto_trait_impls(trait_id, struct_id, db, clauses);
                        }
                    }
                    Ty::InferenceVar(_) => {
                        for struct_id in db.all_structs() {
                            push_auto_trait_impls(trait_id, struct_id, db, clauses);
                        }
                    }
                    _ => {}
                }
            }

            // TODO sized, unsize_trait, builtin impls?
        }
        DomainGoal::Holds(WhereClause::ProjectionEq(projection_predicate)) => {
            db.associated_ty_data(projection_predicate.projection.associated_ty_id)
                .to_program_clauses(db, clauses);
        }
        DomainGoal::WellFormed(WellFormed::Trait(trait_predicate)) => {
            db.trait_datum(trait_predicate.trait_id)
                .to_program_clauses(db, clauses);
        }
        DomainGoal::WellFormed(WellFormed::Ty(ty))
        | DomainGoal::IsUpstream(ty)
        | DomainGoal::DownstreamType(ty) => match_ty(db, environment, ty, clauses),
        DomainGoal::IsFullyVisible(ty) | DomainGoal::IsLocal(ty) => {
            match_ty(db, environment, ty, clauses)
        }
        DomainGoal::FromEnv(_) => (), // Computed in the environment
        DomainGoal::Normalize(Normalize { projection, ty: _ }) => {
            // Normalize goals derive from `AssociatedTyValue` datums,
            // which are found in impls. That is, if we are
            // normalizing (e.g.) `<T as Iterator>::Item>`, then
            // search for impls of iterator and, within those impls,
            // for associated type values:
            //
            // ```ignore
            // impl Iterator for Foo {
            //     type Item = Bar; // <-- associated type value
            // }
            // ```
            let associated_ty_datum = db.associated_ty_data(projection.associated_ty_id);
            let trait_id = associated_ty_datum.trait_id;
            push_program_clauses_for_associated_type_values_in_impls_of(db, trait_id, clauses);
        }
        DomainGoal::UnselectedNormalize(_) => {
            // An "unselected normalize" is one where the trait is not
            // known. It could be any "in-scope" trait.
            for trait_id in environment.in_scope_trait_ids() {
                debug!("in-scope trait: {:?}", trait_id);
                push_program_clauses_for_associated_type_values_in_impls_of(db, trait_id, clauses);
            }
        }
        DomainGoal::InScope(type_kind_id) => match_type_kind(db, *type_kind_id, clauses),
        DomainGoal::LocalImplAllowed(trait_ref) => db
            .trait_datum(trait_ref.trait_id)
            .to_program_clauses(db, clauses),
        DomainGoal::Compatible(()) => (),
    };
}

/// Generate program clauses from the associated-type values
/// found in impls of the given trait. i.e., if `trait_id` = Iterator,
/// then we would generate program clauses from each `type Item = ...`
/// found in any impls of `Iterator`:
/// which are found in impls. That is, if we are
/// normalizing (e.g.) `<T as Iterator>::Item>`, then
/// search for impls of iterator and, within those impls,
/// for associated type values:
///
/// ```ignore
/// impl Iterator for Foo {
///     type Item = Bar; // <-- associated type value
/// }
/// ```
fn push_program_clauses_for_associated_type_values_in_impls_of(
    db: &dyn RustIrDatabase,
    trait_id: TraitId,
    clauses: &mut Vec<ProgramClause>,
) {
    for impl_id in db.impls_for_trait(trait_id) {
        let impl_datum = db.impl_datum(impl_id);
        if !impl_datum.is_positive() {
            continue;
        }

        for atv in &impl_datum.binders.value.associated_ty_values {
            atv.to_program_clauses(db, clauses);
        }
    }
}

/// Given the "self-type" of a domain goal, push potentially relevant program
/// clauses.
fn match_ty(
    db: &dyn RustIrDatabase,
    environment: &Arc<Environment>,
    ty: &Ty,
    clauses: &mut Vec<ProgramClause>,
) {
    match ty {
        Ty::Apply(application_ty) => match application_ty.name {
            TypeName::TypeKindId(type_kind_id) => match_type_kind(db, type_kind_id, clauses),
            TypeName::Placeholder(_) => {}
            TypeName::AssociatedType(type_id) => db
                .associated_ty_data(type_id)
                .to_program_clauses(db, clauses),
        },
        Ty::Projection(projection_ty) => db
            .associated_ty_data(projection_ty.associated_ty_id)
            .to_program_clauses(db, clauses),
        Ty::ForAll(quantified_ty) => match_ty(db, environment, &quantified_ty.ty, clauses),
        Ty::UnselectedProjection(_) => {
            // FIXME: This unselected projection could normalize to
            // any type, so we need the rules from all
            // structs. Arguably though they should have some kind of
            // well-formedness rules of their own? Or else we should
            // create a custom rule that first "unselected-normalizes"
            // the result and then checks for WF on the
            // result. Something like that.
            for struct_id in db.all_structs() {
                db.struct_datum(struct_id).to_program_clauses(db, clauses);
            }
        }
        Ty::BoundVar(_) => {}
        Ty::InferenceVar(_) => {
            // If the type is an (unbound) inference variable, it
            // could be any of these things:
            for struct_id in db.all_structs() {
                db.struct_datum(struct_id).to_program_clauses(db, clauses);
            }
        }
    }
}

fn match_type_kind(
    db: &dyn RustIrDatabase,
    type_kind_id: TypeKindId,
    clauses: &mut Vec<ProgramClause>,
) {
    match type_kind_id {
        TypeKindId::TypeId(type_id) => db
            .associated_ty_data(type_id)
            .to_program_clauses(db, clauses),
        TypeKindId::TraitId(trait_id) => db.trait_datum(trait_id).to_program_clauses(db, clauses),
        TypeKindId::StructId(struct_id) => {
            db.struct_datum(struct_id).to_program_clauses(db, clauses)
        }
    }
}

fn program_clauses_for_env<'db>(
    db: &'db dyn RustIrDatabase,
    environment: &Arc<Environment>,
    clauses: &mut Vec<ProgramClause>,
) {
    let mut last_round = FxHashSet::default();
    elaborate_env_clauses(db, &environment.clauses, &mut last_round);

    let mut closure = last_round.clone();
    let mut next_round = FxHashSet::default();
    while !last_round.is_empty() {
        elaborate_env_clauses(db, &last_round.drain().collect(), &mut next_round);
        last_round.extend(
            next_round
                .drain()
                .filter(|clause| closure.insert(clause.clone())),
        );
    }

    clauses.extend(closure.drain())
}
