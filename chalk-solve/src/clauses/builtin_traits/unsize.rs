use std::collections::HashSet;
use std::iter;

use crate::clauses::ClauseBuilder;
use crate::rust_ir::AdtKind;
use crate::{Interner, RustIrDatabase, TraitRef, WellKnownTrait};
use chalk_ir::{
    cast::Cast,
    interner::HasInterner,
    visit::{ControlFlow, SuperVisit, Visit, Visitor},
    Binders, Const, ConstValue, DebruijnIndex, DomainGoal, DynTy, EqGoal, Goal, LifetimeOutlives,
    QuantifiedWhereClauses, Substitution, TraitId, Ty, TyKind, TypeOutlives, WhereClause,
};

struct UnsizeParameterCollector<'a, I: Interner> {
    interner: &'a I,
    // FIXME should probably use a bitset instead
    parameters: HashSet<usize>,
}

impl<'a, I: Interner> Visitor<'a, I> for UnsizeParameterCollector<'a, I> {
    type BreakTy = ();

    fn as_dyn(&mut self) -> &mut dyn Visitor<'a, I, BreakTy = Self::BreakTy> {
        self
    }

    fn visit_ty(&mut self, ty: &Ty<I>, outer_binder: DebruijnIndex) -> ControlFlow<()> {
        let interner = self.interner;

        match ty.kind(interner) {
            TyKind::BoundVar(bound_var) => {
                // check if bound var refers to the outermost binder
                if bound_var.debruijn.shifted_in() == outer_binder {
                    self.parameters.insert(bound_var.index);
                }
                ControlFlow::CONTINUE
            }
            _ => ty.super_visit_with(self, outer_binder),
        }
    }

    fn visit_const(&mut self, constant: &Const<I>, outer_binder: DebruijnIndex) -> ControlFlow<()> {
        let interner = self.interner;

        if let ConstValue::BoundVar(bound_var) = constant.data(interner).value {
            // check if bound var refers to the outermost binder
            if bound_var.debruijn.shifted_in() == outer_binder {
                self.parameters.insert(bound_var.index);
            }
        }
        ControlFlow::CONTINUE
    }

    fn interner(&self) -> &'a I {
        self.interner
    }
}

fn outer_binder_parameters_used<I: Interner>(
    interner: &I,
    v: &Binders<impl Visit<I> + HasInterner<Interner = I>>,
) -> HashSet<usize> {
    let mut visitor = UnsizeParameterCollector {
        interner,
        parameters: HashSet::new(),
    };
    v.visit_with(&mut visitor, DebruijnIndex::INNERMOST);
    visitor.parameters
}

// has nothing to do with occurs check
struct ParameterOccurenceCheck<'a, 'p, I: Interner> {
    interner: &'a I,
    parameters: &'p HashSet<usize>,
}

impl<'a, 'p, I: Interner> Visitor<'a, I> for ParameterOccurenceCheck<'a, 'p, I> {
    type BreakTy = ();

    fn as_dyn(&mut self) -> &mut dyn Visitor<'a, I, BreakTy = Self::BreakTy> {
        self
    }

    fn visit_ty(&mut self, ty: &Ty<I>, outer_binder: DebruijnIndex) -> ControlFlow<()> {
        let interner = self.interner;

        match ty.kind(interner) {
            TyKind::BoundVar(bound_var) => {
                if bound_var.debruijn.shifted_in() == outer_binder
                    && self.parameters.contains(&bound_var.index)
                {
                    ControlFlow::BREAK
                } else {
                    ControlFlow::CONTINUE
                }
            }
            _ => ty.super_visit_with(self, outer_binder),
        }
    }

    fn visit_const(&mut self, constant: &Const<I>, outer_binder: DebruijnIndex) -> ControlFlow<()> {
        let interner = self.interner;

        match constant.data(interner).value {
            ConstValue::BoundVar(bound_var) => {
                if bound_var.debruijn.shifted_in() == outer_binder
                    && self.parameters.contains(&bound_var.index)
                {
                    ControlFlow::BREAK
                } else {
                    ControlFlow::CONTINUE
                }
            }
            _ => ControlFlow::CONTINUE,
        }
    }

    fn interner(&self) -> &'a I {
        self.interner
    }
}

fn uses_outer_binder_params<I: Interner>(
    interner: &I,
    v: &Binders<impl Visit<I> + HasInterner<Interner = I>>,
    parameters: &HashSet<usize>,
) -> bool {
    let mut visitor = ParameterOccurenceCheck {
        interner,
        parameters,
    };
    v.visit_with(&mut visitor, DebruijnIndex::INNERMOST)
        .is_break()
}

fn principal_id<'a, I: Interner>(
    db: &dyn RustIrDatabase<I>,
    bounds: &'a Binders<QuantifiedWhereClauses<I>>,
) -> Option<TraitId<I>> {
    let interner = db.interner();

    bounds
        .skip_binders()
        .iter(interner)
        .filter_map(|b| b.trait_id())
        .find(|&id| !db.trait_datum(id).is_auto_trait())
}

fn auto_trait_ids<'a, I: Interner>(
    db: &'a dyn RustIrDatabase<I>,
    bounds: &'a Binders<QuantifiedWhereClauses<I>>,
) -> impl Iterator<Item = TraitId<I>> + 'a {
    let interner = db.interner();

    bounds
        .skip_binders()
        .iter(interner)
        .filter_map(|clause| clause.trait_id())
        .filter(move |&id| db.trait_datum(id).is_auto_trait())
}

pub fn add_unsize_program_clauses<I: Interner>(
    db: &dyn RustIrDatabase<I>,
    builder: &mut ClauseBuilder<'_, I>,
    trait_ref: TraitRef<I>,
    _ty: TyKind<I>,
) {
    let interner = db.interner();

    let source_ty = trait_ref.self_type_parameter(interner);
    let target_ty = trait_ref
        .substitution
        .at(interner, 1)
        .assert_ty_ref(interner)
        .clone();

    let unsize_trait_id = trait_ref.trait_id;

    // N.B. here rustc asserts that `TraitRef` is not a higher-ranked bound
    // i.e. `for<'a> &'a T: Unsize<dyn Trait+'a>` is never provable.
    //
    // In chalk it would be awkward to implement and I am not sure
    // there is a need for it, the original comment states that this restriction
    // could be lifted.
    //
    // for more info visit `fn assemble_candidates_for_unsizing` and
    // `fn confirm_builtin_unisize_candidate` in rustc.

    match (source_ty.kind(interner), target_ty.kind(interner)) {
        // dyn Trait + AutoX + 'a -> dyn Trait + AutoY + 'b
        (
            TyKind::Dyn(DynTy {
                bounds: bounds_a,
                lifetime: lifetime_a,
            }),
            TyKind::Dyn(DynTy {
                bounds: bounds_b,
                lifetime: lifetime_b,
            }),
        ) => {
            let principal_a = principal_id(db, bounds_a);
            let principal_b = principal_id(db, bounds_b);

            let auto_trait_ids_a: Vec<_> = auto_trait_ids(db, bounds_a).collect();
            let auto_trait_ids_b: Vec<_> = auto_trait_ids(db, bounds_b).collect();

            let may_apply = principal_a == principal_b
                && auto_trait_ids_b
                    .iter()
                    .all(|id_b| auto_trait_ids_a.iter().any(|id_a| id_a == id_b));

            if !may_apply {
                return;
            }

            // COMMENT FROM RUSTC:
            // ------------------
            // Require that the traits involved in this upcast are **equal**;
            // only the **lifetime bound** is changed.
            //
            // This condition is arguably too strong -- it would
            // suffice for the source trait to be a *subtype* of the target
            // trait. In particular, changing from something like
            // `for<'a, 'b> Foo<'a, 'b>` to `for<'a> Foo<'a, 'a>` should be
            // permitted.
            // <...>
            // I've modified this to `.eq` because I want to continue rejecting
            // that [`old-lub-glb-object.rs`] test (as we have
            // done for quite some time) before we are firmly comfortable
            // with what our behavior should be there. -nikomatsakis
            // ------------------

            // Construct a new trait object type by taking the source ty,
            // filtering out auto traits of source that are not present in target
            // and changing source lifetime to target lifetime.
            //
            // In order for the coercion to be valid, this new type
            // should be equal to target type.
            let new_source_ty = TyKind::Dyn(DynTy {
                bounds: bounds_a.map_ref(|bounds| {
                    QuantifiedWhereClauses::from_iter(
                        interner,
                        bounds.iter(interner).filter(|bound| {
                            let trait_id = match bound.trait_id() {
                                Some(id) => id,
                                None => return true,
                            };

                            if auto_trait_ids_a.iter().all(|&id_a| id_a != trait_id) {
                                return true;
                            }
                            auto_trait_ids_b.iter().any(|&id_b| id_b == trait_id)
                        }),
                    )
                }),
                lifetime: lifetime_b.clone(),
            })
            .intern(interner);

            // Check that new source is equal to target
            let eq_goal = EqGoal {
                a: new_source_ty.cast(interner),
                b: target_ty.clone().cast(interner),
            }
            .cast(interner);

            // Check that source lifetime outlives target lifetime
            let lifetime_outlives_goal: Goal<I> = WhereClause::LifetimeOutlives(LifetimeOutlives {
                a: lifetime_a.clone(),
                b: lifetime_b.clone(),
            })
            .cast(interner);

            builder.push_clause(trait_ref, [eq_goal, lifetime_outlives_goal].iter());
        }

        // T -> dyn Trait + 'a
        (_, TyKind::Dyn(DynTy { bounds, lifetime })) => {
            // Check if all traits in trait object are object safe
            let object_safe_goals = bounds
                .skip_binders()
                .iter(interner)
                .filter_map(|bound| bound.trait_id())
                .map(|id| DomainGoal::ObjectSafe(id).cast(interner));

            // Check that T implements all traits of the trait object
            let source_ty_bounds = bounds
                .clone()
                .substitute(interner, &Substitution::from1(interner, source_ty.clone()));

            // Check that T is sized because we can only make
            // a trait object from a sized type
            let self_sized_goal: WhereClause<_> = TraitRef {
                trait_id: db
                    .well_known_trait_id(WellKnownTrait::Sized)
                    .expect("Expected Sized to be defined when proving Unsize"),
                substitution: Substitution::from1(interner, source_ty.clone()),
            }
            .cast(interner);

            // Check that `source_ty` outlives `'a`
            let source_ty_outlives: Goal<_> = WhereClause::TypeOutlives(TypeOutlives {
                ty: source_ty,
                lifetime: lifetime.clone(),
            })
            .cast(interner);

            builder.push_clause(
                trait_ref,
                source_ty_bounds
                    .iter(interner)
                    .map(|bound| bound.clone().cast::<Goal<I>>(interner))
                    .chain(object_safe_goals)
                    .chain(iter::once(self_sized_goal.cast(interner)))
                    .chain(iter::once(source_ty_outlives)),
            );
        }

        (TyKind::Array(array_ty, _array_const), TyKind::Slice(slice_ty)) => {
            let eq_goal = EqGoal {
                a: array_ty.clone().cast(interner),
                b: slice_ty.clone().cast(interner),
            };

            builder.push_clause(trait_ref, iter::once(eq_goal));
        }

        // Adt<T> -> Adt<U>
        (TyKind::Adt(adt_id_a, substitution_a), TyKind::Adt(adt_id_b, substitution_b)) => {
            if adt_id_a != adt_id_b {
                return;
            }

            let adt_id = *adt_id_a;
            let adt_datum = db.adt_datum(adt_id);

            // Unsizing of enums is not allowed
            if adt_datum.kind == AdtKind::Enum {
                return;
            }

            // We have a `struct` so we're guaranteed a single variant
            let fields_len = adt_datum
                .binders
                .skip_binders()
                .variants
                .last()
                .unwrap()
                .fields
                .len();

            if fields_len == 0 {
                return;
            }

            let adt_tail_field = adt_datum
                .binders
                .map_ref(|bound| bound.variants.last().unwrap().fields.last().unwrap())
                .cloned();

            // Collect unsize parameters that last field contains and
            // ensure there at least one of them.
            let unsize_parameter_candidates =
                outer_binder_parameters_used(interner, &adt_tail_field);

            if unsize_parameter_candidates.is_empty() {
                return;
            }
            // Ensure none of the other fields mention the parameters used
            // in unsizing.
            // We specifically want variables specified by the outermost binder
            // i.e. the struct generic arguments binder.
            if uses_outer_binder_params(
                interner,
                &adt_datum
                    .binders
                    .map_ref(|bound| &bound.variants.last().unwrap().fields[..fields_len - 1]),
                &unsize_parameter_candidates,
            ) {
                return;
            }

            let parameters_a = substitution_a.as_slice(interner);
            let parameters_b = substitution_b.as_slice(interner);
            // Check that the source adt with the target's
            // unsizing parameters is equal to the target.
            // We construct a new substitution where if a parameter is used in the
            // coercion (i.e. it's a non-lifetime struct parameter used by it's last field),
            // then we take that parameter from target substitution, otherwise we take
            // it from the source substitution.
            //
            // In order for the coercion to be valid, target struct and
            // struct with this newly constructed substitution applied to it should be equal.
            let substitution = Substitution::from_iter(
                interner,
                parameters_a.iter().enumerate().map(|(i, p)| {
                    if unsize_parameter_candidates.contains(&i) {
                        &parameters_b[i]
                    } else {
                        p
                    }
                }),
            );

            let eq_goal = EqGoal {
                a: TyKind::Adt(adt_id, substitution)
                    .intern(interner)
                    .cast(interner),
                b: target_ty.clone().cast(interner),
            }
            .cast(interner);

            // Extract `TailField<T>` and `TailField<U>` from `Struct<T>` and `Struct<U>`.
            let source_tail_field = adt_tail_field.clone().substitute(interner, substitution_a);
            let target_tail_field = adt_tail_field.substitute(interner, substitution_b);

            // Check that `TailField<T>: Unsize<TailField<U>>`
            let last_field_unsizing_goal: Goal<I> = TraitRef {
                trait_id: unsize_trait_id,
                substitution: Substitution::from_iter(
                    interner,
                    [source_tail_field, target_tail_field].iter().cloned(),
                ),
            }
            .cast(interner);

            builder.push_clause(trait_ref, [eq_goal, last_field_unsizing_goal].iter());
        }

        // (.., T) -> (.., U)
        (TyKind::Tuple(arity_a, substitution_a), TyKind::Tuple(arity_b, substitution_b)) => {
            if arity_a != arity_b || *arity_a == 0 {
                return;
            }
            let arity = arity_a;

            let tail_ty_a = substitution_a.iter(interner).last().unwrap();
            let tail_ty_b = substitution_b.iter(interner).last().unwrap();

            // Check that the source tuple with the target's
            // last element is equal to the target.
            let new_tuple = TyKind::Tuple(
                *arity,
                Substitution::from_iter(
                    interner,
                    substitution_a
                        .iter(interner)
                        .take(arity - 1)
                        .chain(iter::once(tail_ty_b)),
                ),
            )
            .cast(interner)
            .intern(interner);

            let eq_goal: Goal<I> = EqGoal {
                a: new_tuple.cast(interner),
                b: target_ty.clone().cast(interner),
            }
            .cast(interner);

            // Check that `T: Unsize<U>`
            let last_field_unsizing_goal: Goal<I> = TraitRef {
                trait_id: unsize_trait_id,
                substitution: Substitution::from_iter(
                    interner,
                    [tail_ty_a, tail_ty_b].iter().cloned(),
                ),
            }
            .cast(interner);

            builder.push_clause(trait_ref, [eq_goal, last_field_unsizing_goal].iter());
        }

        _ => (),
    }
}
