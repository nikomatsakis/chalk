use chalk_integration::interner::{ChalkIr, RawId};
use chalk_integration::SolverChoice;
use chalk_ir::*;
use chalk_solve::rust_ir::*;
use chalk_solve::RustIrDatabase;
use std::sync::Arc;

// FIXME: some of these are probably redundant, so we should figure out which panic in the same place in `chalk-engine`

#[derive(Debug)]
enum PanickingMethod {
    NoPanic,
    CustomClauses,
    TraitDatum,
    ImplDatum,
    ImplsForTrait,
    ProgramClausesForEnv,
    Interner,
}

impl Default for PanickingMethod {
    fn default() -> Self {
        Self::NoPanic
    }
}

#[derive(Debug, Default)]
struct MockDatabase {
    panicking_method: PanickingMethod,
}

impl UnificationDatabase<ChalkIr> for MockDatabase {
    fn fn_def_variance(&self, _fn_def_id: FnDefId<ChalkIr>) -> Variances<ChalkIr> {
        Variances::empty(self.interner())
    }

    fn adt_variance(&self, _adt_id: AdtId<ChalkIr>) -> Variances<ChalkIr> {
        Variances::empty(self.interner())
    }
}

/// This DB represents the following lowered program:
///
/// struct Foo { }
/// trait Bar { }
/// impl Bar for Foo { }
#[allow(unused_variables)]
impl RustIrDatabase<ChalkIr> for MockDatabase {
    fn custom_clauses(&self) -> Vec<ProgramClause<ChalkIr>> {
        if let PanickingMethod::CustomClauses = self.panicking_method {
            panic!("custom_clauses panic");
        }

        vec![]
    }

    fn associated_ty_data(&self, ty: AssocTypeId<ChalkIr>) -> Arc<AssociatedTyDatum<ChalkIr>> {
        unimplemented!()
    }

    fn associated_const_data(
        &self,
        ty: AssocConstId<ChalkIr>,
    ) -> Arc<AssociatedConstDatum<ChalkIr>> {
        unimplemented!()
    }

    // `trait Bar`, id `0`
    fn trait_datum(&self, id: TraitId<ChalkIr>) -> Arc<TraitDatum<ChalkIr>> {
        if let PanickingMethod::TraitDatum = self.panicking_method {
            panic!("trait_datum panic");
        }

        assert_eq!(id.0.index, 0);
        Arc::new(TraitDatum {
            id,
            binders: Binders::new(
                VariableKinds::empty(&ChalkIr),
                TraitDatumBound {
                    where_clauses: vec![],
                },
            ),
            flags: TraitFlags {
                auto: false,
                marker: false,
                upstream: false,
                fundamental: false,
                non_enumerable: false,
                coinductive: false,
            },
            associated_ty_ids: vec![],
            associated_const_ids: vec![],
            well_known: None,
        })
    }

    // `impl Bar for Foo`, id `1`
    fn impl_datum(&self, id: ImplId<ChalkIr>) -> Arc<ImplDatum<ChalkIr>> {
        if let PanickingMethod::ImplDatum = self.panicking_method {
            panic!("impl_datum panic");
        }

        assert_eq!(id.0.index, 1);

        let substitution = Ty::new(
            &ChalkIr,
            TyKind::Adt(AdtId(RawId { index: 1 }), Substitution::empty(&ChalkIr)),
        );

        let binders = Binders::new(
            VariableKinds::empty(&ChalkIr),
            ImplDatumBound {
                trait_ref: TraitRef {
                    trait_id: TraitId(RawId { index: 0 }),
                    substitution: Substitution::from1(&ChalkIr, substitution),
                },
                where_clauses: vec![],
            },
        );

        Arc::new(ImplDatum {
            polarity: Polarity::Positive,
            binders,
            impl_type: ImplType::Local,
            associated_ty_value_ids: vec![],
            associated_const_value_ids: vec![],
        })
    }

    fn associated_ty_value(
        &self,
        id: AssociatedTyValueId<ChalkIr>,
    ) -> Arc<AssociatedTyValue<ChalkIr>> {
        unimplemented!()
    }

    fn associated_const_value(
        &self,
        id: AssociatedConstValueId<ChalkIr>,
    ) -> Arc<AssociatedConstValue<ChalkIr>> {
        unimplemented!()
    }

    fn opaque_ty_data(&self, id: OpaqueTyId<ChalkIr>) -> Arc<OpaqueTyDatum<ChalkIr>> {
        unimplemented!()
    }

    fn hidden_opaque_type(&self, id: OpaqueTyId<ChalkIr>) -> Ty<ChalkIr> {
        unimplemented!()
    }

    fn adt_datum(&self, id: AdtId<ChalkIr>) -> Arc<AdtDatum<ChalkIr>> {
        // Only needed because we always access the adt datum for logging
        Arc::new(AdtDatum {
            binders: Binders::empty(
                &ChalkIr,
                AdtDatumBound {
                    variants: vec![],
                    where_clauses: vec![],
                },
            ),
            flags: AdtFlags {
                fundamental: false,
                phantom_data: false,
                upstream: false,
            },
            id,
            kind: AdtKind::Enum,
        })
    }

    fn adt_repr(&self, id: AdtId<ChalkIr>) -> Arc<AdtRepr<ChalkIr>> {
        unimplemented!()
    }

    fn fn_def_datum(&self, fn_def_id: FnDefId<ChalkIr>) -> Arc<FnDefDatum<ChalkIr>> {
        unimplemented!()
    }

    fn generator_datum(&self, generator_id: GeneratorId<ChalkIr>) -> Arc<GeneratorDatum<ChalkIr>> {
        unimplemented!()
    }

    fn generator_witness_datum(
        &self,
        generator_id: GeneratorId<ChalkIr>,
    ) -> Arc<GeneratorWitnessDatum<ChalkIr>> {
        unimplemented!()
    }

    // All `Bar` impls
    fn impls_for_trait(
        &self,
        trait_id: TraitId<ChalkIr>,
        parameters: &[GenericArg<ChalkIr>],
        binders: &CanonicalVarKinds<ChalkIr>,
    ) -> Vec<ImplId<ChalkIr>> {
        if let PanickingMethod::ImplsForTrait = self.panicking_method {
            panic!("impls_for_trait panic");
        }

        assert_eq!(trait_id.0.index, 0);
        vec![ImplId(RawId { index: 1 })]
    }

    fn local_impls_to_coherence_check(&self, trait_id: TraitId<ChalkIr>) -> Vec<ImplId<ChalkIr>> {
        unimplemented!()
    }

    fn impl_provided_for(&self, auto_trait_id: TraitId<ChalkIr>, app_ty: &TyKind<ChalkIr>) -> bool {
        unimplemented!()
    }

    fn well_known_trait_id(&self, well_known_trait: WellKnownTrait) -> Option<TraitId<ChalkIr>> {
        unimplemented!()
    }

    fn program_clauses_for_env(
        &self,
        environment: &Environment<ChalkIr>,
    ) -> ProgramClauses<ChalkIr> {
        if let PanickingMethod::ProgramClausesForEnv = self.panicking_method {
            panic!("program_clauses_for_env panic")
        }

        ProgramClauses::empty(&ChalkIr)
    }

    fn interner(&self) -> &ChalkIr {
        if let PanickingMethod::Interner = self.panicking_method {
            panic!("interner panic")
        }

        &ChalkIr
    }

    fn is_object_safe(&self, trait_id: TraitId<ChalkIr>) -> bool {
        unimplemented!()
    }

    fn closure_inputs_and_output(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> Binders<FnDefInputsAndOutputDatum<ChalkIr>> {
        unimplemented!()
    }

    fn closure_kind(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> ClosureKind {
        unimplemented!()
    }

    fn closure_upvars(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> Binders<Ty<ChalkIr>> {
        unimplemented!()
    }

    fn closure_fn_substitution(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> Substitution<ChalkIr> {
        unimplemented!()
    }

    fn discriminant_type(&self, ty: Ty<ChalkIr>) -> Ty<ChalkIr> {
        unimplemented!()
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<ChalkIr> {
        self
    }
}

fn prepare_goal() -> UCanonical<InEnvironment<Goal<ChalkIr>>> {
    use chalk_integration::interner;
    use chalk_ir::*;

    // Goal:
    //
    // Foo: Bar
    UCanonical {
        canonical: Canonical {
            binders: CanonicalVarKinds::empty(&ChalkIr),
            value: InEnvironment {
                environment: Environment::new(&ChalkIr),
                goal: GoalData::DomainGoal(DomainGoal::Holds(WhereClause::Implemented(TraitRef {
                    trait_id: TraitId(interner::RawId { index: 0 }),
                    substitution: Substitution::from1(
                        &ChalkIr,
                        Ty::new(
                            &ChalkIr,
                            TyKind::Adt(
                                AdtId(interner::RawId { index: 1 }),
                                Substitution::empty(&ChalkIr),
                            ),
                        ),
                    ),
                })))
                .intern(&ChalkIr),
            },
        },
        universes: 1,
    }
}

#[test]
fn custom_clauses_panics() {
    use std::panic;

    let peeled_goal = prepare_goal();
    let mut solver = SolverChoice::slg_default().into_solver();

    // solve goal but this will panic
    let mut db = MockDatabase {
        panicking_method: PanickingMethod::CustomClauses,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        solver.solve(&db, &peeled_goal);
    }));
    assert!(result.is_err());

    // solve again but without panicking this time
    db.panicking_method = PanickingMethod::NoPanic;
    assert!(solver.solve(&db, &peeled_goal).is_some());
}

#[test]
fn trait_datum_panics() {
    use std::panic;

    let peeled_goal = prepare_goal();
    let mut solver = SolverChoice::slg_default().into_solver();

    // solve goal but this will panic
    let mut db = MockDatabase {
        panicking_method: PanickingMethod::TraitDatum,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        solver.solve(&db, &peeled_goal);
    }));
    assert!(result.is_err());

    // solve again but without panicking this time
    db.panicking_method = PanickingMethod::NoPanic;
    assert!(solver.solve(&db, &peeled_goal).is_some());
}

#[test]
fn impl_datum_panics() {
    use std::panic;

    let peeled_goal = prepare_goal();
    let mut solver = SolverChoice::slg_default().into_solver();

    // solve goal but this will panic
    let mut db = MockDatabase {
        panicking_method: PanickingMethod::ImplDatum,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        solver.solve(&db, &peeled_goal);
    }));
    assert!(result.is_err());

    // solve again but without panicking this time
    db.panicking_method = PanickingMethod::NoPanic;
    assert!(solver.solve(&db, &peeled_goal).is_some());
}

#[test]
fn impls_for_trait() {
    use std::panic;

    let peeled_goal = prepare_goal();
    let mut solver = SolverChoice::slg_default().into_solver();

    // solve goal but this will panic
    let mut db = MockDatabase {
        panicking_method: PanickingMethod::ImplsForTrait,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        solver.solve(&db, &peeled_goal);
    }));
    assert!(result.is_err());

    // solve again but without panicking this time
    db.panicking_method = PanickingMethod::NoPanic;
    assert!(solver.solve(&db, &peeled_goal).is_some());
}

#[test]
fn program_clauses_for_env() {
    use std::panic;

    let peeled_goal = prepare_goal();
    let mut solver = SolverChoice::slg_default().into_solver();

    // solve goal but this will panic
    let mut db = MockDatabase {
        panicking_method: PanickingMethod::ProgramClausesForEnv,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        solver.solve(&db, &peeled_goal);
    }));
    assert!(result.is_err());

    // solve again but without panicking this time
    db.panicking_method = PanickingMethod::NoPanic;
    assert!(solver.solve(&db, &peeled_goal).is_some());
}

#[test]
fn interner() {
    use std::panic;

    let peeled_goal = prepare_goal();
    let mut solver = SolverChoice::slg_default().into_solver();

    // solve goal but this will panic
    let mut db = MockDatabase {
        panicking_method: PanickingMethod::Interner,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        solver.solve(&db, &peeled_goal);
    }));
    assert!(result.is_err());

    // solve again but without panicking this time
    db.panicking_method = PanickingMethod::NoPanic;
    assert!(solver.solve(&db, &peeled_goal).is_some());
}
