//! Contains a `LoggingIrDatabase` which returns stub versions of everything
//! queried.
use std::sync::Arc;

use crate::rust_ir::{GeneratorDatum, GeneratorWitnessDatum};
use crate::{
    rust_ir::{
        AdtDatumBound, AdtKind, AdtVariantDatum, AssociatedTyDatumBound, FnDefDatumBound,
        OpaqueTyDatumBound, TraitDatumBound,
    },
    RustIrDatabase,
};
use chalk_ir::{
    interner::Interner, Binders, CanonicalVarKinds, GeneratorId, Substitution, Ty,
    UnificationDatabase, VariableKinds, Variances,
};

#[derive(Debug)]
pub struct StubWrapper<'a, DB> {
    db: &'a DB,
}

impl<'a, DB> StubWrapper<'a, DB> {
    pub fn new(db: &'a DB) -> Self {
        StubWrapper { db }
    }
}

impl<I: Interner, DB: RustIrDatabase<I>> UnificationDatabase<I> for StubWrapper<'_, DB> {
    fn fn_def_variance(&self, fn_def_id: chalk_ir::FnDefId<I>) -> Variances<I> {
        self.db.unification_database().fn_def_variance(fn_def_id)
    }

    fn adt_variance(&self, adt_id: chalk_ir::AdtId<I>) -> Variances<I> {
        self.db.unification_database().adt_variance(adt_id)
    }
}

impl<I: Interner, DB: RustIrDatabase<I>> RustIrDatabase<I> for StubWrapper<'_, DB> {
    fn custom_clauses(&self) -> Vec<chalk_ir::ProgramClause<I>> {
        self.db.custom_clauses()
    }

    fn associated_ty_data(
        &self,
        ty: chalk_ir::AssocTypeId<I>,
    ) -> std::sync::Arc<crate::rust_ir::AssociatedTyDatum<I>> {
        let mut v = (*self.db.associated_ty_data(ty)).clone();
        v.binders = Binders::new(
            v.binders.binders.clone(),
            AssociatedTyDatumBound {
                where_clauses: Vec::new(),
                bounds: Vec::new(),
            },
        );
        Arc::new(v)
    }

    fn associated_const_data(
        &self,
        ty: chalk_ir::AssocConstId<I>,
    ) -> std::sync::Arc<crate::rust_ir::AssociatedConstDatum<I>> {
        let v = (*self.db.associated_const_data(ty)).clone();
        Arc::new(v)
    }

    fn trait_datum(
        &self,
        trait_id: chalk_ir::TraitId<I>,
    ) -> std::sync::Arc<crate::rust_ir::TraitDatum<I>> {
        let mut v = (*self.db.trait_datum(trait_id)).clone();
        v.binders = Binders::new(
            v.binders.binders.clone(),
            TraitDatumBound {
                where_clauses: Vec::new(),
            },
        );
        Arc::new(v)
    }

    fn adt_datum(&self, adt_id: chalk_ir::AdtId<I>) -> std::sync::Arc<crate::rust_ir::AdtDatum<I>> {
        let mut v = (*self.db.adt_datum(adt_id)).clone();
        let variants = match v.kind {
            AdtKind::Struct | AdtKind::Union => vec![AdtVariantDatum { fields: vec![] }],
            AdtKind::Enum => vec![],
        };
        v.binders = Binders::new(
            v.binders.binders.clone(),
            AdtDatumBound {
                variants,
                where_clauses: Vec::new(),
            },
        );
        Arc::new(v)
    }

    fn adt_repr(&self, id: chalk_ir::AdtId<I>) -> std::sync::Arc<crate::rust_ir::AdtRepr<I>> {
        self.db.adt_repr(id)
    }

    fn fn_def_datum(
        &self,
        fn_def_id: chalk_ir::FnDefId<I>,
    ) -> std::sync::Arc<crate::rust_ir::FnDefDatum<I>> {
        let mut v = (*self.db.fn_def_datum(fn_def_id)).clone();
        v.binders = Binders::new(
            v.binders.binders.clone(),
            FnDefDatumBound {
                inputs_and_output: v.binders.skip_binders().inputs_and_output.clone(),
                where_clauses: Vec::new(),
            },
        );
        Arc::new(v)
    }

    fn impl_datum(
        &self,
        _impl_id: chalk_ir::ImplId<I>,
    ) -> std::sync::Arc<crate::rust_ir::ImplDatum<I>> {
        unreachable!("impl items should never be stubbed")
    }

    fn associated_ty_value(
        &self,
        _id: crate::rust_ir::AssociatedTyValueId<I>,
    ) -> std::sync::Arc<crate::rust_ir::AssociatedTyValue<I>> {
        unreachable!("associated type values should never be stubbed")
    }

    fn associated_const_value(
        &self,
        _id: crate::rust_ir::AssociatedConstValueId<I>,
    ) -> std::sync::Arc<crate::rust_ir::AssociatedConstValue<I>> {
        unreachable!("associated const values should never be stubbed")
    }

    fn opaque_ty_data(
        &self,
        id: chalk_ir::OpaqueTyId<I>,
    ) -> std::sync::Arc<crate::rust_ir::OpaqueTyDatum<I>> {
        let mut v = (*self.db.opaque_ty_data(id)).clone();
        v.bound = Binders::new(
            v.bound.binders,
            OpaqueTyDatumBound {
                bounds: Binders::new(VariableKinds::empty(self.db.interner()), Vec::new()),
                where_clauses: Binders::new(VariableKinds::empty(self.db.interner()), Vec::new()),
            },
        );
        Arc::new(v)
    }

    fn hidden_opaque_type(&self, _id: chalk_ir::OpaqueTyId<I>) -> chalk_ir::Ty<I> {
        // Return a unit since the particular hidden type doesn't matter (If it
        // did matter, it would have been recorded)
        chalk_ir::TyKind::Tuple(0, Substitution::empty(self.db.interner()))
            .intern(self.db.interner())
    }

    fn impls_for_trait(
        &self,
        _trait_id: chalk_ir::TraitId<I>,
        _parameters: &[chalk_ir::GenericArg<I>],
        _binders: &CanonicalVarKinds<I>,
    ) -> Vec<chalk_ir::ImplId<I>> {
        // We panic here because the returned ids may not be collected,
        // resulting in unresolvable names.
        unimplemented!("stub display code should call this")
    }

    fn local_impls_to_coherence_check(
        &self,
        trait_id: chalk_ir::TraitId<I>,
    ) -> Vec<chalk_ir::ImplId<I>> {
        self.db.local_impls_to_coherence_check(trait_id)
    }

    fn impl_provided_for(
        &self,
        _auto_trait_id: chalk_ir::TraitId<I>,
        _ty: &chalk_ir::TyKind<I>,
    ) -> bool {
        // We panic here because the returned ids may not be collected,
        // resulting in unresolvable names.
        unimplemented!("stub display code should call this")
    }

    fn well_known_trait_id(
        &self,
        well_known_trait: crate::rust_ir::WellKnownTrait,
    ) -> Option<chalk_ir::TraitId<I>> {
        self.db.well_known_trait_id(well_known_trait)
    }

    fn program_clauses_for_env(
        &self,
        environment: &chalk_ir::Environment<I>,
    ) -> chalk_ir::ProgramClauses<I> {
        self.db.program_clauses_for_env(environment)
    }

    fn interner(&self) -> &I {
        self.db.interner()
    }

    fn is_object_safe(&self, trait_id: chalk_ir::TraitId<I>) -> bool {
        self.db.is_object_safe(trait_id)
    }

    fn closure_kind(
        &self,
        _closure_id: chalk_ir::ClosureId<I>,
        _substs: &chalk_ir::Substitution<I>,
    ) -> crate::rust_ir::ClosureKind {
        unimplemented!("cannot stub closures")
    }

    fn closure_inputs_and_output(
        &self,
        _closure_id: chalk_ir::ClosureId<I>,
        _substs: &chalk_ir::Substitution<I>,
    ) -> chalk_ir::Binders<crate::rust_ir::FnDefInputsAndOutputDatum<I>> {
        unimplemented!("cannot stub closures")
    }

    fn closure_upvars(
        &self,
        _closure_id: chalk_ir::ClosureId<I>,
        _substs: &chalk_ir::Substitution<I>,
    ) -> chalk_ir::Binders<chalk_ir::Ty<I>> {
        unimplemented!("cannot stub closures")
    }

    fn generator_datum(&self, _generator_id: GeneratorId<I>) -> Arc<GeneratorDatum<I>> {
        unimplemented!("cannot stub generator")
    }

    fn generator_witness_datum(
        &self,
        _generator_id: GeneratorId<I>,
    ) -> Arc<GeneratorWitnessDatum<I>> {
        unimplemented!("cannot stub generator witness")
    }

    fn closure_fn_substitution(
        &self,
        _closure_id: chalk_ir::ClosureId<I>,
        _substs: &chalk_ir::Substitution<I>,
    ) -> chalk_ir::Substitution<I> {
        unimplemented!("cannot stub closures")
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<I> {
        self
    }

    fn trait_name(&self, trait_id: chalk_ir::TraitId<I>) -> String {
        self.db.trait_name(trait_id)
    }

    fn adt_name(&self, struct_id: chalk_ir::AdtId<I>) -> String {
        self.db.adt_name(struct_id)
    }

    fn assoc_type_name(&self, assoc_ty_id: chalk_ir::AssocTypeId<I>) -> String {
        self.db.assoc_type_name(assoc_ty_id)
    }

    fn assoc_const_name(&self, assoc_const_id: chalk_ir::AssocConstId<I>) -> String {
        self.db.assoc_const_name(assoc_const_id)
    }

    fn opaque_type_name(&self, opaque_ty_id: chalk_ir::OpaqueTyId<I>) -> String {
        self.db.opaque_type_name(opaque_ty_id)
    }

    fn fn_def_name(&self, fn_def_id: chalk_ir::FnDefId<I>) -> String {
        self.db.fn_def_name(fn_def_id)
    }

    fn discriminant_type(&self, ty: Ty<I>) -> Ty<I> {
        self.db.discriminant_type(ty)
    }
}
