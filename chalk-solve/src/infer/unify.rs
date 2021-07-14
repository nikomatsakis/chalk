use super::var::*;
use super::*;
use crate::debug_span;
use chalk_ir::cast::Cast;
use chalk_ir::fold::{Fold, Folder};
use chalk_ir::interner::{HasInterner, Interner};
use chalk_ir::zip::{Zip, Zipper};
use chalk_ir::UnificationDatabase;
use std::fmt::Debug;
use tracing::{debug, instrument};

impl<I: Interner> InferenceTable<I> {
    pub fn relate<T>(
        &mut self,
        interner: &I,
        db: &dyn UnificationDatabase<I>,
        environment: &Environment<I>,
        variance: Variance,
        a: &T,
        b: &T,
    ) -> Fallible<RelationResult<I>>
    where
        T: ?Sized + Zip<I>,
    {
        let snapshot = self.snapshot();
        match Unifier::new(interner, db, self, environment).relate(variance, a, b) {
            Ok(r) => {
                self.commit(snapshot);
                Ok(r)
            }
            Err(e) => {
                self.rollback_to(snapshot);
                Err(e)
            }
        }
    }
}

struct Unifier<'t, I: Interner> {
    table: &'t mut InferenceTable<I>,
    environment: &'t Environment<I>,
    goals: Vec<InEnvironment<Goal<I>>>,
    interner: &'t I,
    db: &'t dyn UnificationDatabase<I>,
}

#[derive(Debug)]
pub struct RelationResult<I: Interner> {
    pub goals: Vec<InEnvironment<Goal<I>>>,
}

impl<'t, I: Interner> Unifier<'t, I> {
    fn new(
        interner: &'t I,
        db: &'t dyn UnificationDatabase<I>,
        table: &'t mut InferenceTable<I>,
        environment: &'t Environment<I>,
    ) -> Self {
        Unifier {
            environment,
            table,
            goals: vec![],
            interner,
            db,
        }
    }

    /// The main entry point for the `Unifier` type and really the
    /// only type meant to be called externally. Performs a
    /// relation of `a` and `b` and returns the Unification Result.
    #[instrument(level = "debug", skip(self))]
    fn relate<T>(mut self, variance: Variance, a: &T, b: &T) -> Fallible<RelationResult<I>>
    where
        T: ?Sized + Zip<I>,
    {
        Zip::zip_with(&mut self, variance, a, b)?;
        let interner = self.interner();
        let mut goals = self.goals;
        let table = self.table;
        // Sometimes we'll produce a lifetime outlives goal which we later solve by unification
        // Technically, these *will* get canonicalized to the same bound var and so that will end up
        // as a goal like `^0.0 <: ^0.0`, which is trivially true. But, we remove those *here*, which
        // might help caching.
        goals.retain(|g| match g.goal.data(interner) {
            GoalData::SubtypeGoal(SubtypeGoal { a, b }) => {
                let n_a = table.ty_root(interner, a);
                let n_b = table.ty_root(interner, b);
                let a = n_a.as_ref().unwrap_or(a);
                let b = n_b.as_ref().unwrap_or(b);
                a != b
            }
            _ => true,
        });
        Ok(RelationResult { goals })
    }

    /// Relate `a`, `b` with the variance such that if `variance = Covariant`, `a` is
    /// a subtype of `b`.
    fn relate_ty_ty(&mut self, variance: Variance, a: &Ty<I>, b: &Ty<I>) -> Fallible<()> {
        let interner = self.interner;

        let n_a = self.table.normalize_ty_shallow(interner, a);
        let n_b = self.table.normalize_ty_shallow(interner, b);
        let a = n_a.as_ref().unwrap_or(a);
        let b = n_b.as_ref().unwrap_or(b);

        debug_span!("relate_ty_ty", ?variance, ?a, ?b);

        if a.kind(interner) == b.kind(interner) {
            return Ok(());
        }

        match (a.kind(interner), b.kind(interner)) {
            // Relating two inference variables:
            // First, if either variable is a float or int kind, then we always
            // unify if they match. This is because float and ints don't have
            // subtype relationships.
            // If both kinds are general then:
            // If `Invariant`, unify them in the underlying ena table.
            // If `Covariant` or `Contravariant`, push `SubtypeGoal`
            (&TyKind::InferenceVar(var1, kind1), &TyKind::InferenceVar(var2, kind2)) => {
                if matches!(kind1, TyVariableKind::General)
                    && matches!(kind2, TyVariableKind::General)
                {
                    // Both variable kinds are general; so unify if invariant, otherwise push subtype goal
                    match variance {
                        Variance::Invariant => self.unify_var_var(var1, var2),
                        Variance::Covariant => {
                            self.push_subtype_goal(a.clone(), b.clone());
                            Ok(())
                        }
                        Variance::Contravariant => {
                            self.push_subtype_goal(b.clone(), a.clone());
                            Ok(())
                        }
                    }
                } else if kind1 == kind2 {
                    // At least one kind is not general, but they match, so unify
                    self.unify_var_var(var1, var2)
                } else if kind1 == TyVariableKind::General {
                    // First kind is general, second isn't, unify
                    self.unify_general_var_specific_ty(var1, b.clone())
                } else if kind2 == TyVariableKind::General {
                    // Second kind is general, first isn't, unify
                    self.unify_general_var_specific_ty(var2, a.clone())
                } else {
                    debug!(
                        "Tried to unify mis-matching inference variables: {:?} and {:?}",
                        kind1, kind2
                    );
                    Err(NoSolution)
                }
            }

            // Unifying `forall<X> { T }` with some other forall type `forall<X> { U }`
            (&TyKind::Function(ref fn1), &TyKind::Function(ref fn2)) => {
                if fn1.sig == fn2.sig {
                    Zip::zip_with(
                        self,
                        variance,
                        &fn1.clone().into_binders(interner),
                        &fn2.clone().into_binders(interner),
                    )
                } else {
                    Err(NoSolution)
                }
            }

            (&TyKind::Placeholder(ref p1), &TyKind::Placeholder(ref p2)) => {
                Zip::zip_with(self, variance, p1, p2)
            }

            // Unifying two dyn is possible if they have the same bounds.
            (&TyKind::Dyn(ref qwc1), &TyKind::Dyn(ref qwc2)) => {
                Zip::zip_with(self, variance, qwc1, qwc2)
            }

            (TyKind::BoundVar(_), _) | (_, TyKind::BoundVar(_)) => panic!(
                "unification encountered bound variable: a={:?} b={:?}",
                a, b
            ),

            // Unifying an alias type with some other type `U`.
            (_, &TyKind::Alias(ref alias)) => self.relate_alias_ty(variance.invert(), alias, a),
            (&TyKind::Alias(ref alias), _) => self.relate_alias_ty(variance, alias, b),

            (&TyKind::InferenceVar(var, kind), ty_data @ _) => {
                let ty = ty_data.clone().intern(interner);
                self.relate_var_ty(variance, var, kind, &ty)
            }
            (ty_data @ _, &TyKind::InferenceVar(var, kind)) => {
                // We need to invert the variance if inference var is `b` because we pass it in
                // as `a` to relate_var_ty
                let ty = ty_data.clone().intern(interner);
                self.relate_var_ty(variance.invert(), var, kind, &ty)
            }

            // This would correspond to unifying a `fn` type with a non-fn
            // type in Rust; error.
            (&TyKind::Function(_), _) | (_, &TyKind::Function(_)) => Err(NoSolution),

            // Cannot unify (e.g.) some struct type `Foo` and a placeholder like `T`
            (_, &TyKind::Placeholder(_)) | (&TyKind::Placeholder(_), _) => Err(NoSolution),

            // Cannot unify `dyn Trait` with things like structs or placeholders
            (_, &TyKind::Dyn(_)) | (&TyKind::Dyn(_), _) => Err(NoSolution),

            (TyKind::Adt(id_a, substitution_a), TyKind::Adt(id_b, substitution_b)) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    Some(self.unification_database().adt_variance(*id_a)),
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (
                TyKind::AssociatedType(id_a, substitution_a),
                TyKind::AssociatedType(id_b, substitution_b),
            ) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    None, // TODO: AssociatedType variances?
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (TyKind::Scalar(scalar_a), TyKind::Scalar(scalar_b)) => {
                Zip::zip_with(self, variance, scalar_a, scalar_b)
            }
            (TyKind::Str, TyKind::Str) => Ok(()),
            (TyKind::Tuple(arity_a, substitution_a), TyKind::Tuple(arity_b, substitution_b)) => {
                if arity_a != arity_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    Some(Variances::from_iter(
                        &self.interner,
                        std::iter::repeat(Variance::Covariant).take(*arity_a),
                    )),
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (
                TyKind::OpaqueType(id_a, substitution_a),
                TyKind::OpaqueType(id_b, substitution_b),
            ) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    None,
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (TyKind::Slice(ty_a), TyKind::Slice(ty_b)) => Zip::zip_with(self, variance, ty_a, ty_b),
            (TyKind::FnDef(id_a, substitution_a), TyKind::FnDef(id_b, substitution_b)) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    Some(self.unification_database().fn_def_variance(*id_a)),
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (
                TyKind::Ref(mutability_a, lifetime_a, ty_a),
                TyKind::Ref(mutability_b, lifetime_b, ty_b),
            ) => {
                if mutability_a != mutability_b {
                    return Err(NoSolution);
                }
                // The lifetime is `Contravariant`
                Zip::zip_with(
                    self,
                    variance.xform(Variance::Contravariant),
                    lifetime_a,
                    lifetime_b,
                )?;
                // The type is `Covariant` when not mut, `Invariant` otherwise
                let output_variance = match mutability_a {
                    Mutability::Not => Variance::Covariant,
                    Mutability::Mut => Variance::Invariant,
                };
                Zip::zip_with(self, variance.xform(output_variance), ty_a, ty_b)
            }
            (TyKind::Raw(mutability_a, ty_a), TyKind::Raw(mutability_b, ty_b)) => {
                if mutability_a != mutability_b {
                    return Err(NoSolution);
                }
                let ty_variance = match mutability_a {
                    Mutability::Not => Variance::Covariant,
                    Mutability::Mut => Variance::Invariant,
                };
                Zip::zip_with(self, variance.xform(ty_variance), ty_a, ty_b)
            }
            (TyKind::Never, TyKind::Never) => Ok(()),
            (TyKind::Array(ty_a, const_a), TyKind::Array(ty_b, const_b)) => {
                Zip::zip_with(self, variance, ty_a, ty_b)?;
                Zip::zip_with(self, variance, const_a, const_b)
            }
            (TyKind::Closure(id_a, substitution_a), TyKind::Closure(id_b, substitution_b)) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    None,
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (TyKind::Generator(id_a, substitution_a), TyKind::Generator(id_b, substitution_b)) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    None,
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (
                TyKind::GeneratorWitness(id_a, substitution_a),
                TyKind::GeneratorWitness(id_b, substitution_b),
            ) => {
                if id_a != id_b {
                    return Err(NoSolution);
                }
                self.zip_substs(
                    variance,
                    None,
                    substitution_a.as_slice(interner),
                    substitution_b.as_slice(interner),
                )
            }
            (TyKind::Foreign(id_a), TyKind::Foreign(id_b)) => {
                Zip::zip_with(self, variance, id_a, id_b)
            }
            (TyKind::Error, TyKind::Error) => Ok(()),

            (_, _) => Err(NoSolution),
        }
    }

    /// Unify two inference variables
    #[instrument(level = "debug", skip(self))]
    fn unify_var_var(&mut self, a: InferenceVar, b: InferenceVar) -> Fallible<()> {
        let var1 = EnaVariable::from(a);
        let var2 = EnaVariable::from(b);
        Ok(self
            .table
            .unify
            .unify_var_var(var1, var2)
            .expect("unification of two unbound variables cannot fail"))
    }

    /// Unify a general inference variable with a specific inference variable
    /// (type kind is not `General`). For example, unify a `TyVariableKind::General`
    /// inference variable with a `TyVariableKind::Integer` variable, resulting in the
    /// general inference variable narrowing to an integer variable.

    #[instrument(level = "debug", skip(self))]
    fn unify_general_var_specific_ty(
        &mut self,
        general_var: InferenceVar,
        specific_ty: Ty<I>,
    ) -> Fallible<()> {
        self.table
            .unify
            .unify_var_value(
                general_var,
                InferenceValue::from_ty(self.interner, specific_ty),
            )
            .unwrap();

        Ok(())
    }

    #[instrument(level = "debug", skip(self))]
    fn relate_binders<'a, T, R>(
        &mut self,
        variance: Variance,
        a: &Binders<T>,
        b: &Binders<T>,
    ) -> Fallible<()>
    where
        T: Clone + Fold<I, Result = R> + HasInterner<Interner = I>,
        R: Zip<I> + Fold<I, Result = R>,
        't: 'a,
    {
        // for<'a...> T == for<'b...> U
        //
        // if:
        //
        // for<'a...> exists<'b...> T == U &&
        // for<'b...> exists<'a...> T == U

        // for<'a...> T <: for<'b...> U
        //
        // if
        //
        // for<'b...> exists<'a...> T <: U

        let interner = self.interner;

        if let Variance::Invariant | Variance::Contravariant = variance {
            let a_universal = self
                .table
                .instantiate_binders_universally(interner, a.clone());
            let b_existential = self
                .table
                .instantiate_binders_existentially(interner, b.clone());
            Zip::zip_with(self, Variance::Contravariant, &a_universal, &b_existential)?;
        }

        if let Variance::Invariant | Variance::Covariant = variance {
            let b_universal = self
                .table
                .instantiate_binders_universally(interner, b.clone());
            let a_existential = self
                .table
                .instantiate_binders_existentially(interner, a.clone());
            Zip::zip_with(self, Variance::Covariant, &a_existential, &b_universal)?;
        }

        Ok(())
    }

    /// Relate an alias like `<T as Trait>::Item` or `impl Trait` with some other
    /// type `ty`. If the variance is `Invariant`, creates a goal like
    ///
    /// ```notrust
    /// AliasEq(<T as Trait>::Item = U) // associated type projection
    /// AliasEq(impl Trait = U) // impl trait
    /// ```
    /// Otherwise, this creates a new variable `?X`, creates a goal like
    /// ```notrust
    /// AliasEq(Alias = ?X)
    /// ```
    /// and relates `?X` and `ty`.
    #[instrument(level = "debug", skip(self))]
    fn relate_alias_ty(
        &mut self,
        variance: Variance,
        alias: &AliasTy<I>,
        ty: &Ty<I>,
    ) -> Fallible<()> {
        let interner = self.interner;
        match variance {
            Variance::Invariant => {
                self.goals.push(InEnvironment::new(
                    self.environment,
                    AliasEq {
                        alias: alias.clone(),
                        ty: ty.clone(),
                    }
                    .cast(interner),
                ));
                Ok(())
            }
            Variance::Covariant | Variance::Contravariant => {
                let var = self
                    .table
                    .new_variable(UniverseIndex::root())
                    .to_ty(interner);
                self.goals.push(InEnvironment::new(
                    self.environment,
                    AliasEq {
                        alias: alias.clone(),
                        ty: var.clone(),
                    }
                    .cast(interner),
                ));
                self.relate_ty_ty(variance, &var, ty)
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn generalize_ty(
        &mut self,
        ty: &Ty<I>,
        universe_index: UniverseIndex,
        variance: Variance,
    ) -> Ty<I> {
        let interner = self.interner;
        match ty.kind(interner) {
            TyKind::Adt(id, substitution) => {
                let variances = if matches!(variance, Variance::Invariant) {
                    None
                } else {
                    Some(self.unification_database().adt_variance(*id))
                };
                let get_variance = |i| {
                    variances
                        .as_ref()
                        .map(|v| v.as_slice(interner)[i])
                        .unwrap_or(Variance::Invariant)
                };
                TyKind::Adt(
                    *id,
                    self.generalize_substitution(substitution, universe_index, get_variance),
                )
                .intern(interner)
            }
            TyKind::AssociatedType(id, substitution) => TyKind::AssociatedType(
                *id,
                self.generalize_substitution(substitution, universe_index, |_| variance),
            )
            .intern(interner),
            TyKind::Scalar(scalar) => TyKind::Scalar(*scalar).intern(interner),
            TyKind::Str => TyKind::Str.intern(interner),
            TyKind::Tuple(arity, substitution) => TyKind::Tuple(
                *arity,
                self.generalize_substitution(substitution, universe_index, |_| variance),
            )
            .intern(interner),
            TyKind::OpaqueType(id, substitution) => TyKind::OpaqueType(
                *id,
                self.generalize_substitution(substitution, universe_index, |_| variance),
            )
            .intern(interner),
            TyKind::Slice(ty) => {
                TyKind::Slice(self.generalize_ty(ty, universe_index, variance)).intern(interner)
            }
            TyKind::FnDef(id, substitution) => {
                let variances = if matches!(variance, Variance::Invariant) {
                    None
                } else {
                    Some(self.unification_database().fn_def_variance(*id))
                };
                let get_variance = |i| {
                    variances
                        .as_ref()
                        .map(|v| v.as_slice(interner)[i])
                        .unwrap_or(Variance::Invariant)
                };
                TyKind::FnDef(
                    *id,
                    self.generalize_substitution(substitution, universe_index, get_variance),
                )
                .intern(interner)
            }
            TyKind::Ref(mutability, lifetime, ty) => {
                let lifetime_variance = variance.xform(Variance::Contravariant);
                let ty_variance = match mutability {
                    Mutability::Not => Variance::Covariant,
                    Mutability::Mut => Variance::Invariant,
                };
                TyKind::Ref(
                    *mutability,
                    self.generalize_lifetime(lifetime, universe_index, lifetime_variance),
                    self.generalize_ty(ty, universe_index, ty_variance),
                )
                .intern(interner)
            }
            TyKind::Raw(mutability, ty) => {
                let ty_variance = match mutability {
                    Mutability::Not => Variance::Covariant,
                    Mutability::Mut => Variance::Invariant,
                };
                TyKind::Raw(
                    *mutability,
                    self.generalize_ty(ty, universe_index, ty_variance),
                )
                .intern(interner)
            }
            TyKind::Never => TyKind::Never.intern(interner),
            TyKind::Array(ty, const_) => TyKind::Array(
                self.generalize_ty(ty, universe_index, variance),
                self.generalize_const(const_, universe_index),
            )
            .intern(interner),
            TyKind::Closure(id, substitution) => TyKind::Closure(
                *id,
                self.generalize_substitution(substitution, universe_index, |_| variance),
            )
            .intern(interner),
            TyKind::Generator(id, substitution) => TyKind::Generator(
                *id,
                self.generalize_substitution(substitution, universe_index, |_| variance),
            )
            .intern(interner),
            TyKind::GeneratorWitness(id, substitution) => TyKind::GeneratorWitness(
                *id,
                self.generalize_substitution(substitution, universe_index, |_| variance),
            )
            .intern(interner),
            TyKind::Foreign(id) => TyKind::Foreign(*id).intern(interner),
            TyKind::Error => TyKind::Error.intern(interner),
            TyKind::Dyn(dyn_ty) => {
                let DynTy { bounds, lifetime } = dyn_ty;
                let lifetime = self.generalize_lifetime(
                    lifetime,
                    universe_index,
                    variance.xform(Variance::Contravariant),
                );

                let bounds = bounds.map_ref(|value| {
                    let iter = value.iter(interner).map(|sub_var| {
                        sub_var.map_ref(|clause| {
                            match clause {
                                WhereClause::Implemented(trait_ref) => {
                                    let TraitRef {
                                        ref substitution,
                                        trait_id,
                                    } = *trait_ref;
                                    let substitution = self.generalize_substitution_skip_self(
                                        substitution,
                                        universe_index,
                                        |_| Some(variance),
                                    );
                                    WhereClause::Implemented(TraitRef {
                                        substitution,
                                        trait_id,
                                    })
                                }
                                WhereClause::AliasEq(alias_eq) => {
                                    let AliasEq { alias, ty: _ } = alias_eq;
                                    let alias = match alias {
                                        AliasTy::Opaque(opaque_ty) => {
                                            let OpaqueTy {
                                                ref substitution,
                                                opaque_ty_id,
                                            } = *opaque_ty;
                                            let substitution = self.generalize_substitution(
                                                substitution,
                                                universe_index,
                                                |_| variance,
                                            );
                                            AliasTy::Opaque(OpaqueTy {
                                                substitution,
                                                opaque_ty_id,
                                            })
                                        }
                                        AliasTy::Projection(projection_ty) => {
                                            let ProjectionTy {
                                                ref substitution,
                                                associated_ty_id,
                                            } = *projection_ty;
                                            // TODO: We should be skipping "self", which
                                            // would be the first element of
                                            // "trait_params" if we had a
                                            // `RustIrDatabase` to call
                                            // `split_projection` on...
                                            // let (assoc_ty_datum, trait_params, assoc_type_params) = s.db().split_projection(&self);
                                            let substitution = self.generalize_substitution(
                                                substitution,
                                                universe_index,
                                                |_| variance,
                                            );
                                            AliasTy::Projection(ProjectionTy {
                                                substitution,
                                                associated_ty_id,
                                            })
                                        }
                                    };
                                    let ty =
                                        self.table.new_variable(universe_index).to_ty(interner);
                                    WhereClause::AliasEq(AliasEq { alias, ty })
                                }
                                WhereClause::TypeOutlives(_) => {
                                    let lifetime_var = self.table.new_variable(universe_index);
                                    let lifetime = lifetime_var.to_lifetime(interner);
                                    let ty_var = self.table.new_variable(universe_index);
                                    let ty = ty_var.to_ty(interner);
                                    WhereClause::TypeOutlives(TypeOutlives {
                                        ty: ty,
                                        lifetime: lifetime,
                                    })
                                }
                                WhereClause::LifetimeOutlives(_) => {
                                    unreachable!("dyn Trait never contains LifetimeOutlive bounds")
                                }
                            }
                        })
                    });
                    QuantifiedWhereClauses::from_iter(interner, iter)
                });

                TyKind::Dyn(DynTy { bounds, lifetime }).intern(interner)
            }
            TyKind::Function(fn_ptr) => {
                let FnPointer {
                    num_binders,
                    sig,
                    ref substitution,
                } = *fn_ptr;

                let len = substitution.0.len(interner);
                let vars = substitution.0.iter(interner).enumerate().map(|(i, var)| {
                    if i < len - 1 {
                        self.generalize_generic_var(
                            var,
                            universe_index,
                            variance.xform(Variance::Contravariant),
                        )
                    } else {
                        self.generalize_generic_var(
                            substitution.0.as_slice(interner).last().unwrap(),
                            universe_index,
                            variance,
                        )
                    }
                });

                let substitution = FnSubst(Substitution::from_iter(interner, vars));

                TyKind::Function(FnPointer {
                    num_binders,
                    sig,
                    substitution,
                })
                .intern(interner)
            }
            TyKind::Placeholder(_) | TyKind::BoundVar(_) => {
                debug!("just generalizing to the ty itself: {:?}", ty);
                // BoundVar and PlaceHolder have no internal values to be
                // generic over, so we just relate directly to it
                ty.clone()
            }
            TyKind::Alias(_) => {
                let ena_var = self.table.new_variable(universe_index);
                ena_var.to_ty(interner)
            }
            TyKind::InferenceVar(_var, kind) => {
                if matches!(kind, TyVariableKind::Integer | TyVariableKind::Float) {
                    ty.clone()
                } else if let Some(ty) = self.table.normalize_ty_shallow(interner, ty) {
                    self.generalize_ty(&ty, universe_index, variance)
                } else if matches!(variance, Variance::Invariant) {
                    ty.clone()
                } else {
                    let ena_var = self.table.new_variable(universe_index);
                    ena_var.to_ty(interner)
                }
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn generalize_lifetime(
        &mut self,
        lifetime: &Lifetime<I>,
        universe_index: UniverseIndex,
        variance: Variance,
    ) -> Lifetime<I> {
        let interner = self.interner;
        match lifetime.data(&interner) {
            LifetimeData::BoundVar(_) => {
                return lifetime.clone();
            }
            _ => {
                if matches!(variance, Variance::Invariant) {
                    lifetime.clone()
                } else {
                    let ena_var = self.table.new_variable(universe_index);
                    ena_var.to_lifetime(interner)
                }
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn generalize_const(&mut self, const_: &Const<I>, universe_index: UniverseIndex) -> Const<I> {
        let interner = self.interner;
        let data = const_.data(&interner);
        match data.value {
            ConstValue::BoundVar(_) => {
                return const_.clone();
            }
            _ => {
                let ena_var = self.table.new_variable(universe_index);
                ena_var.to_const(interner, data.ty.clone())
            }
        }
    }

    fn generalize_generic_var(
        &mut self,
        sub_var: &GenericArg<I>,
        universe_index: UniverseIndex,
        variance: Variance,
    ) -> GenericArg<I> {
        let interner = self.interner;
        (match sub_var.data(interner) {
            GenericArgData::Ty(ty) => {
                GenericArgData::Ty(self.generalize_ty(ty, universe_index, variance))
            }
            GenericArgData::Lifetime(lifetime) => GenericArgData::Lifetime(
                self.generalize_lifetime(lifetime, universe_index, variance),
            ),
            GenericArgData::Const(const_value) => {
                GenericArgData::Const(self.generalize_const(const_value, universe_index))
            }
        })
        .intern(interner)
    }

    /// Generalizes all but the first
    #[instrument(level = "debug", skip(self, get_variance))]
    fn generalize_substitution_skip_self<F: Fn(usize) -> Option<Variance>>(
        &mut self,
        substitution: &Substitution<I>,
        universe_index: UniverseIndex,
        get_variance: F,
    ) -> Substitution<I> {
        let interner = self.interner;
        let vars = substitution.iter(interner).enumerate().map(|(i, sub_var)| {
            if i == 0 {
                sub_var.clone()
            } else {
                let variance = get_variance(i).unwrap_or(Variance::Invariant);
                self.generalize_generic_var(sub_var, universe_index, variance)
            }
        });
        Substitution::from_iter(interner, vars)
    }

    #[instrument(level = "debug", skip(self, get_variance))]
    fn generalize_substitution<F: Fn(usize) -> Variance>(
        &mut self,
        substitution: &Substitution<I>,
        universe_index: UniverseIndex,
        get_variance: F,
    ) -> Substitution<I> {
        let interner = self.interner;
        let vars = substitution.iter(interner).enumerate().map(|(i, sub_var)| {
            let variance = get_variance(i);
            self.generalize_generic_var(sub_var, universe_index, variance)
        });

        Substitution::from_iter(interner, vars)
    }

    /// Unify an inference variable `var` with some non-inference
    /// variable `ty`, just bind `var` to `ty`. But we must enforce two conditions:
    ///
    /// - `var` does not appear inside of `ty` (the standard `OccursCheck`)
    /// - `ty` does not reference anything in a lifetime that could not be named in `var`
    ///   (the extended `OccursCheck` created to handle universes)
    #[instrument(level = "debug", skip(self))]
    fn relate_var_ty(
        &mut self,
        variance: Variance,
        var: InferenceVar,
        var_kind: TyVariableKind,
        ty: &Ty<I>,
    ) -> Fallible<()> {
        let interner = self.interner;

        match (var_kind, ty.is_integer(interner), ty.is_float(interner)) {
            // General inference variables can unify with any type
            (TyVariableKind::General, _, _)
            // Integer inference variables can only unify with integer types
            | (TyVariableKind::Integer, true, _)
            // Float inference variables can only unify with float types
            | (TyVariableKind::Float, _, true) => {
            },
            _ => return Err(NoSolution),
        }

        let var = EnaVariable::from(var);

        // Determine the universe index associated with this
        // variable. This is basically a count of the number of
        // `forall` binders that had been introduced at the point
        // this variable was created -- though it may change over time
        // as the variable is unified.
        let universe_index = self.table.universe_of_unbound_var(var);
        // let universe_index = self.table.max_universe();

        debug!("relate_var_ty: universe index of var: {:?}", universe_index);

        debug!("trying fold_with on {:?}", ty);
        let ty1 = ty
            .clone()
            .fold_with(
                &mut OccursCheck::new(self, var, universe_index),
                DebruijnIndex::INNERMOST,
            )
            .map_err(|e| {
                debug!("failed to fold {:?}", ty);
                e
            })?;

        // "Generalize" types. This ensures that we aren't accidentally forcing
        // too much onto `var`. Instead of directly setting `var` equal to `ty`,
        // we just take the outermost structure we _know_ `var` holds, and then
        // apply that to `ty`. This involves creating new inference vars for
        // everything inside `var`, then calling `relate_ty_ty` to relate those
        // inference vars to the things they generalized with the correct
        // variance.

        // The main problem this solves is that lifetime relationships are
        // relationships, not just eq ones. So when solving &'a u32 <: U,
        // generalizing we would end up with U = &'a u32. Instead, we want
        // U = &'b u32, with a lifetime constraint 'a <: 'b. This matters
        // especially when solving multiple constraints - for example, &'a u32
        // <: U, &'b u32 <: U (where without generalizing, we'd end up with 'a
        // <: 'b, where we really want 'a <: 'c, 'b <: 'c for some 'c).

        // Example operation: consider `ty` as `&'x SomeType`. To generalize
        // this, we create two new vars `'0` and `1`. Then we relate `var` with
        // `&'0 1` and `&'0 1` with `&'x SomeType`. The second relation will
        // recurse, and we'll end up relating `'0` with `'x` and `1` with `SomeType`.
        let generalized_val = self.generalize_ty(&ty1, universe_index, variance);

        debug!("var {:?} generalized to {:?}", var, generalized_val);

        self.table
            .unify
            .unify_var_value(
                var,
                InferenceValue::from_ty(interner, generalized_val.clone()),
            )
            .unwrap();
        debug!("var {:?} set to {:?}", var, generalized_val);

        self.relate_ty_ty(variance, &generalized_val, &ty1)?;

        debug!(
            "generalized version {:?} related to original {:?}",
            generalized_val, ty1
        );

        Ok(())
    }

    fn relate_lifetime_lifetime(
        &mut self,
        variance: Variance,
        a: &Lifetime<I>,
        b: &Lifetime<I>,
    ) -> Fallible<()> {
        let interner = self.interner;

        let n_a = self.table.normalize_lifetime_shallow(interner, a);
        let n_b = self.table.normalize_lifetime_shallow(interner, b);
        let a = n_a.as_ref().unwrap_or(a);
        let b = n_b.as_ref().unwrap_or(b);

        debug_span!("relate_lifetime_lifetime", ?variance, ?a, ?b);

        match (a.data(interner), b.data(interner)) {
            (&LifetimeData::InferenceVar(var_a), &LifetimeData::InferenceVar(var_b)) => {
                let var_a = EnaVariable::from(var_a);
                let var_b = EnaVariable::from(var_b);
                debug!(?var_a, ?var_b);
                self.table.unify.unify_var_var(var_a, var_b).unwrap();
                Ok(())
            }

            (
                &LifetimeData::InferenceVar(a_var),
                &LifetimeData::Placeholder(PlaceholderIndex { ui, .. }),
            )
            | (&LifetimeData::InferenceVar(a_var), &LifetimeData::Empty(ui)) => {
                self.unify_lifetime_var(variance, a_var, b, ui)
            }

            (
                &LifetimeData::Placeholder(PlaceholderIndex { ui, .. }),
                &LifetimeData::InferenceVar(b_var),
            )
            | (&LifetimeData::Empty(ui), &LifetimeData::InferenceVar(b_var)) => {
                self.unify_lifetime_var(variance.invert(), b_var, a, ui)
            }

            (&LifetimeData::InferenceVar(a_var), &LifetimeData::Erased)
            | (&LifetimeData::InferenceVar(a_var), &LifetimeData::Static) => {
                self.unify_lifetime_var(variance, a_var, b, UniverseIndex::root())
            }

            (&LifetimeData::Erased, &LifetimeData::InferenceVar(b_var))
            | (&LifetimeData::Static, &LifetimeData::InferenceVar(b_var)) => {
                self.unify_lifetime_var(variance.invert(), b_var, a, UniverseIndex::root())
            }

            (&LifetimeData::Static, &LifetimeData::Static)
            | (&LifetimeData::Erased, &LifetimeData::Erased) => Ok(()),

            (&LifetimeData::Static, &LifetimeData::Placeholder(_))
            | (&LifetimeData::Static, &LifetimeData::Empty(_))
            | (&LifetimeData::Static, &LifetimeData::Erased)
            | (&LifetimeData::Placeholder(_), &LifetimeData::Static)
            | (&LifetimeData::Placeholder(_), &LifetimeData::Placeholder(_))
            | (&LifetimeData::Placeholder(_), &LifetimeData::Empty(_))
            | (&LifetimeData::Placeholder(_), &LifetimeData::Erased)
            | (&LifetimeData::Empty(_), &LifetimeData::Static)
            | (&LifetimeData::Empty(_), &LifetimeData::Placeholder(_))
            | (&LifetimeData::Empty(_), &LifetimeData::Empty(_))
            | (&LifetimeData::Empty(_), &LifetimeData::Erased)
            | (&LifetimeData::Erased, &LifetimeData::Static)
            | (&LifetimeData::Erased, &LifetimeData::Placeholder(_))
            | (&LifetimeData::Erased, &LifetimeData::Empty(_)) => {
                if a != b {
                    Ok(self.push_lifetime_outlives_goals(variance, a.clone(), b.clone()))
                } else {
                    Ok(())
                }
            }

            (LifetimeData::BoundVar(_), _) | (_, LifetimeData::BoundVar(_)) => panic!(
                "unification encountered bound variable: a={:?} b={:?}",
                a, b
            ),

            (LifetimeData::Phantom(..), _) | (_, LifetimeData::Phantom(..)) => unreachable!(),
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn unify_lifetime_var(
        &mut self,
        variance: Variance,
        var: InferenceVar,
        value: &Lifetime<I>,
        value_ui: UniverseIndex,
    ) -> Fallible<()> {
        let var = EnaVariable::from(var);
        let var_ui = self.table.universe_of_unbound_var(var);
        if var_ui.can_see(value_ui) && matches!(variance, Variance::Invariant) {
            debug!("{:?} in {:?} can see {:?}; unifying", var, var_ui, value_ui);
            self.table
                .unify
                .unify_var_value(
                    var,
                    InferenceValue::from_lifetime(&self.interner, value.clone()),
                )
                .unwrap();
            Ok(())
        } else {
            debug!(
                "{:?} in {:?} cannot see {:?}; pushing constraint",
                var, var_ui, value_ui
            );
            Ok(self.push_lifetime_outlives_goals(
                variance,
                var.to_lifetime(&self.interner),
                value.clone(),
            ))
        }
    }

    fn relate_const_const<'a>(
        &mut self,
        variance: Variance,
        a: &'a Const<I>,
        b: &'a Const<I>,
    ) -> Fallible<()> {
        let interner = self.interner;

        let n_a = self.table.normalize_const_shallow(interner, a);
        let n_b = self.table.normalize_const_shallow(interner, b);
        let a = n_a.as_ref().unwrap_or(a);
        let b = n_b.as_ref().unwrap_or(b);

        debug_span!("relate_const_const", ?variance, ?a, ?b);

        let ConstData {
            ty: a_ty,
            value: a_val,
        } = a.data(interner);
        let ConstData {
            ty: b_ty,
            value: b_val,
        } = b.data(interner);

        self.relate_ty_ty(variance, a_ty, b_ty)?;

        match (a_val, b_val) {
            // Unifying two inference variables: unify them in the underlying
            // ena table.
            (&ConstValue::InferenceVar(var1), &ConstValue::InferenceVar(var2)) => {
                debug!(?var1, ?var2, "relate_ty_ty");
                let var1 = EnaVariable::from(var1);
                let var2 = EnaVariable::from(var2);
                Ok(self
                    .table
                    .unify
                    .unify_var_var(var1, var2)
                    .expect("unification of two unbound variables cannot fail"))
            }

            // Unifying an inference variables with a non-inference variable.
            (&ConstValue::InferenceVar(var), &ConstValue::Concrete(_))
            | (&ConstValue::InferenceVar(var), &ConstValue::Placeholder(_)) => {
                debug!(?var, ty=?b, "unify_var_ty");
                self.unify_var_const(var, b)
            }

            (&ConstValue::Concrete(_), &ConstValue::InferenceVar(var))
            | (&ConstValue::Placeholder(_), &ConstValue::InferenceVar(var)) => {
                debug!(?var, ty=?a, "unify_var_ty");
                self.unify_var_const(var, a)
            }

            (&ConstValue::Placeholder(p1), &ConstValue::Placeholder(p2)) => {
                Zip::zip_with(self, variance, &p1, &p2)
            }

            (&ConstValue::Concrete(ref ev1), &ConstValue::Concrete(ref ev2)) => {
                if ev1.const_eq(a_ty, ev2, interner) {
                    Ok(())
                } else {
                    Err(NoSolution)
                }
            }

            (&ConstValue::Concrete(_), &ConstValue::Placeholder(_))
            | (&ConstValue::Placeholder(_), &ConstValue::Concrete(_)) => Err(NoSolution),

            (ConstValue::BoundVar(_), _) | (_, ConstValue::BoundVar(_)) => panic!(
                "unification encountered bound variable: a={:?} b={:?}",
                a, b
            ),

            (&ConstValue::ConstProjection(_), _) | (_, &ConstValue::ConstProjection(_)) => todo!(),
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn unify_var_const(&mut self, var: InferenceVar, c: &Const<I>) -> Fallible<()> {
        let interner = self.interner;
        let var = EnaVariable::from(var);

        // Determine the universe index associated with this
        // variable. This is basically a count of the number of
        // `forall` binders that had been introduced at the point
        // this variable was created -- though it may change over time
        // as the variable is unified.
        let universe_index = self.table.universe_of_unbound_var(var);

        let c1 = c.clone().fold_with(
            &mut OccursCheck::new(self, var, universe_index),
            DebruijnIndex::INNERMOST,
        )?;

        debug!("unify_var_const: var {:?} set to {:?}", var, c1);
        self.table
            .unify
            .unify_var_value(var, InferenceValue::from_const(interner, c1))
            .unwrap();

        Ok(())
    }

    /// Relate `a`, `b` such that if `variance = Covariant`, `a` is a subtype of
    /// `b` and thus `a` must outlive `b`.
    fn push_lifetime_outlives_goals(&mut self, variance: Variance, a: Lifetime<I>, b: Lifetime<I>) {
        debug!(
            "pushing lifetime outlives goals for a={:?} b={:?} with variance {:?}",
            a, b, variance
        );
        if matches!(variance, Variance::Invariant | Variance::Contravariant) {
            self.goals.push(InEnvironment::new(
                self.environment,
                WhereClause::LifetimeOutlives(LifetimeOutlives {
                    a: a.clone(),
                    b: b.clone(),
                })
                .cast(self.interner),
            ));
        }
        if matches!(variance, Variance::Invariant | Variance::Covariant) {
            self.goals.push(InEnvironment::new(
                self.environment,
                WhereClause::LifetimeOutlives(LifetimeOutlives { a: b, b: a }).cast(self.interner),
            ));
        }
    }

    /// Pushes a goal of `a` being a subtype of `b`.
    fn push_subtype_goal(&mut self, a: Ty<I>, b: Ty<I>) {
        let subtype_goal = GoalData::SubtypeGoal(SubtypeGoal { a, b }).intern(self.interner());
        self.goals
            .push(InEnvironment::new(self.environment, subtype_goal));
    }
}

impl<'i, I: Interner> Zipper<'i, I> for Unifier<'i, I> {
    fn zip_tys(&mut self, variance: Variance, a: &Ty<I>, b: &Ty<I>) -> Fallible<()> {
        debug!("zip_tys {:?}, {:?}, {:?}", variance, a, b);
        self.relate_ty_ty(variance, a, b)
    }

    fn zip_lifetimes(
        &mut self,
        variance: Variance,
        a: &Lifetime<I>,
        b: &Lifetime<I>,
    ) -> Fallible<()> {
        self.relate_lifetime_lifetime(variance, a, b)
    }

    fn zip_consts(&mut self, variance: Variance, a: &Const<I>, b: &Const<I>) -> Fallible<()> {
        self.relate_const_const(variance, a, b)
    }

    fn zip_binders<T>(&mut self, variance: Variance, a: &Binders<T>, b: &Binders<T>) -> Fallible<()>
    where
        T: Clone + HasInterner<Interner = I> + Zip<I> + Fold<I, Result = T>,
    {
        // The binders that appear in types (apart from quantified types, which are
        // handled in `unify_ty`) appear as part of `dyn Trait` and `impl Trait` types.
        //
        // They come in two varieties:
        //
        // * The existential binder from `dyn Trait` / `impl Trait`
        //   (representing the hidden "self" type)
        // * The `for<..>` binders from higher-ranked traits.
        //
        // In both cases we can use the same `relate_binders` routine.

        self.relate_binders(variance, a, b)
    }

    fn interner(&self) -> &'i I {
        self.interner
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<I> {
        self.db
    }
}

struct OccursCheck<'u, 't, I: Interner> {
    unifier: &'u mut Unifier<'t, I>,
    var: EnaVariable<I>,
    universe_index: UniverseIndex,
}

impl<'u, 't, I: Interner> OccursCheck<'u, 't, I> {
    fn new(
        unifier: &'u mut Unifier<'t, I>,
        var: EnaVariable<I>,
        universe_index: UniverseIndex,
    ) -> Self {
        OccursCheck {
            unifier,
            var,
            universe_index,
        }
    }
}

impl<'i, I: Interner> Folder<'i, I> for OccursCheck<'_, 'i, I>
where
    I: 'i,
{
    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I> {
        self
    }

    fn fold_free_placeholder_ty(
        &mut self,
        universe: PlaceholderIndex,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Ty<I>> {
        let interner = self.interner();
        if self.universe_index < universe.ui {
            debug!(
                "OccursCheck aborting because self.universe_index ({:?}) < universe.ui ({:?})",
                self.universe_index, universe.ui
            );
            Err(NoSolution)
        } else {
            Ok(universe.to_ty(interner)) // no need to shift, not relative to depth
        }
    }

    fn fold_free_placeholder_const(
        &mut self,
        ty: Ty<I>,
        universe: PlaceholderIndex,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Const<I>> {
        let interner = self.interner();
        if self.universe_index < universe.ui {
            Err(NoSolution)
        } else {
            Ok(universe.to_const(interner, ty.clone())) // no need to shift, not relative to depth
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn fold_free_placeholder_lifetime(
        &mut self,
        ui: PlaceholderIndex,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Lifetime<I>> {
        let interner = self.interner();
        if self.universe_index < ui.ui {
            // Scenario is like:
            //
            // exists<T> forall<'b> ?T = Foo<'b>
            //
            // unlike with a type variable, this **might** be
            // ok.  Ultimately it depends on whether the
            // `forall` also introduced relations to lifetimes
            // nameable in T. To handle that, we introduce a
            // fresh region variable `'x` in same universe as `T`
            // and add a side-constraint that `'x = 'b`:
            //
            // exists<'x> forall<'b> ?T = Foo<'x>, where 'x = 'b

            let tick_x = self.unifier.table.new_variable(self.universe_index);
            self.unifier.push_lifetime_outlives_goals(
                Variance::Invariant,
                tick_x.to_lifetime(interner),
                ui.to_lifetime(interner),
            );
            Ok(tick_x.to_lifetime(interner))
        } else {
            // If the `ui` is higher than `self.universe_index`, then we can name
            // this lifetime, no problem.
            Ok(ui.to_lifetime(interner)) // no need to shift, not relative to depth
        }
    }

    fn fold_inference_ty(
        &mut self,
        var: InferenceVar,
        kind: TyVariableKind,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Ty<I>> {
        let interner = self.interner();
        let var = EnaVariable::from(var);
        match self.unifier.table.unify.probe_value(var) {
            // If this variable already has a value, fold over that value instead.
            InferenceValue::Bound(normalized_ty) => {
                let normalized_ty = normalized_ty.assert_ty_ref(interner);
                let normalized_ty = normalized_ty
                    .clone()
                    .fold_with(self, DebruijnIndex::INNERMOST)?;
                assert!(!normalized_ty.needs_shift(interner));
                Ok(normalized_ty)
            }

            // Otherwise, check the universe of the variable, and also
            // check for cycles with `self.var` (which this will soon
            // become the value of).
            InferenceValue::Unbound(ui) => {
                if self.unifier.table.unify.unioned(var, self.var) {
                    debug!(
                        "OccursCheck aborting because {:?} unioned with {:?}",
                        var, self.var,
                    );
                    return Err(NoSolution);
                }

                if self.universe_index < ui {
                    // Scenario is like:
                    //
                    // ?A = foo(?B)
                    //
                    // where ?A is in universe 0 and ?B is in universe 1.
                    // This is OK, if ?B is promoted to universe 0.
                    self.unifier
                        .table
                        .unify
                        .unify_var_value(var, InferenceValue::Unbound(self.universe_index))
                        .unwrap();
                }

                Ok(var.to_ty_with_kind(interner, kind))
            }
        }
    }

    fn fold_inference_const(
        &mut self,
        ty: Ty<I>,
        var: InferenceVar,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Const<I>> {
        let interner = self.interner();
        let var = EnaVariable::from(var);
        match self.unifier.table.unify.probe_value(var) {
            // If this variable already has a value, fold over that value instead.
            InferenceValue::Bound(normalized_const) => {
                let normalized_const = normalized_const.assert_const_ref(interner);
                let normalized_const = normalized_const
                    .clone()
                    .fold_with(self, DebruijnIndex::INNERMOST)?;
                assert!(!normalized_const.needs_shift(interner));
                Ok(normalized_const)
            }

            // Otherwise, check the universe of the variable, and also
            // check for cycles with `self.var` (which this will soon
            // become the value of).
            InferenceValue::Unbound(ui) => {
                if self.unifier.table.unify.unioned(var, self.var) {
                    return Err(NoSolution);
                }

                if self.universe_index < ui {
                    // Scenario is like:
                    //
                    // forall<const A> exists<const B> ?C = Foo<B>
                    //
                    // where A is in universe 0 and B is in universe 1.
                    // This is OK, if B is promoted to universe 0.
                    self.unifier
                        .table
                        .unify
                        .unify_var_value(var, InferenceValue::Unbound(self.universe_index))
                        .unwrap();
                }

                Ok(var.to_const(interner, ty))
            }
        }
    }

    fn fold_inference_lifetime(
        &mut self,
        var: InferenceVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Lifetime<I>> {
        // a free existentially bound region; find the
        // inference variable it corresponds to
        let interner = self.interner();
        let var = EnaVariable::from(var);
        match self.unifier.table.unify.probe_value(var) {
            InferenceValue::Unbound(ui) => {
                if self.universe_index < ui {
                    // Scenario is like:
                    //
                    // exists<T> forall<'b> exists<'a> ?T = Foo<'a>
                    //
                    // where ?A is in universe 0 and `'b` is in universe 1.
                    // This is OK, if `'b` is promoted to universe 0.
                    self.unifier
                        .table
                        .unify
                        .unify_var_value(var, InferenceValue::Unbound(self.universe_index))
                        .unwrap();
                }
                Ok(var.to_lifetime(interner))
            }

            InferenceValue::Bound(l) => {
                let l = l.assert_lifetime_ref(interner);
                let l = l.clone().fold_with(self, outer_binder)?;
                assert!(!l.needs_shift(interner));
                Ok(l)
            }
        }
    }

    fn forbid_free_vars(&self) -> bool {
        true
    }

    fn interner(&self) -> &'i I {
        self.unifier.interner
    }
}
