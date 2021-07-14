use crate::{
    error::ChalkError,
    interner::ChalkIr,
    lowering::lower_goal,
    program::Program,
    query::{Lowering, LoweringDatabase},
    tls, SolverChoice,
};
use chalk_ir::{
    AdtId, AssocConstId, AssocTypeId, Binders, Canonical, CanonicalVarKinds, ClosureId,
    ConstrainedSubst, Environment, FnDefId, GeneratorId, GenericArg, Goal, ImplId, InEnvironment,
    OpaqueTyId, ProgramClause, ProgramClauses, Substitution, TraitId, Ty, TyKind, UCanonical,
    UnificationDatabase, Variances,
};
use chalk_solve::rust_ir::{
    AdtDatum, AdtRepr, AssociatedConstDatum, AssociatedConstValue, AssociatedConstValueId,
    AssociatedTyDatum, AssociatedTyValue, AssociatedTyValueId, ClosureKind, FnDefDatum,
    FnDefInputsAndOutputDatum, GeneratorDatum, GeneratorWitnessDatum, ImplDatum, OpaqueTyDatum,
    TraitDatum, WellKnownTrait,
};
use chalk_solve::{RustIrDatabase, Solution, SubstitutionResult};
use salsa::Database;
use std::fmt;
use std::sync::Arc;

#[salsa::database(Lowering)]
#[derive(Default)]
pub struct ChalkDatabase {
    storage: salsa::Storage<Self>,
}

impl Database for ChalkDatabase {}

impl ChalkDatabase {
    pub fn with(program_text: &str, solver_choice: SolverChoice) -> Self {
        let mut db = ChalkDatabase::default();
        db.set_program_text(Arc::new(program_text.to_string()));
        db.set_solver_choice(solver_choice);
        db
    }

    pub fn with_program<R>(&self, op: impl FnOnce(&Program) -> R) -> R {
        let program = &self.checked_program().unwrap();
        tls::set_current_program(&program, || op(&program))
    }

    pub fn parse_and_lower_goal(&self, text: &str) -> Result<Goal<ChalkIr>, ChalkError> {
        let program = self.checked_program()?;
        Ok(lower_goal(&*chalk_parse::parse_goal(text)?, &*program)?)
    }

    pub fn solve(
        &self,
        goal: &UCanonical<InEnvironment<Goal<ChalkIr>>>,
    ) -> Option<Solution<ChalkIr>> {
        let solver = self.solver();
        let solution = solver.lock().unwrap().solve(self, goal);
        solution
    }

    /// Solves a given goal, producing the solution. This will do only
    /// as much work towards `goal` as it has to (and that works is
    /// cached for future attempts). Calls provided function `f` to
    /// iterate over multiple solutions until the function return `false`.
    pub fn solve_multiple(
        &self,
        goal: &UCanonical<InEnvironment<Goal<ChalkIr>>>,
        f: &mut dyn FnMut(SubstitutionResult<Canonical<ConstrainedSubst<ChalkIr>>>, bool) -> bool,
    ) -> bool {
        let solver = self.solver();
        let solution = solver.lock().unwrap().solve_multiple(self, goal, f);
        solution
    }
}

impl UnificationDatabase<ChalkIr> for ChalkDatabase {
    fn fn_def_variance(&self, fn_def_id: FnDefId<ChalkIr>) -> Variances<ChalkIr> {
        self.program_ir().unwrap().fn_def_variance(fn_def_id)
    }

    fn adt_variance(&self, adt_id: AdtId<ChalkIr>) -> Variances<ChalkIr> {
        self.program_ir().unwrap().adt_variance(adt_id)
    }
}

impl RustIrDatabase<ChalkIr> for ChalkDatabase {
    fn custom_clauses(&self) -> Vec<ProgramClause<ChalkIr>> {
        self.program_ir().unwrap().custom_clauses()
    }

    fn associated_ty_data(&self, ty: AssocTypeId<ChalkIr>) -> Arc<AssociatedTyDatum<ChalkIr>> {
        self.program_ir().unwrap().associated_ty_data(ty)
    }

    fn associated_const_data(
        &self,
        ty: AssocConstId<ChalkIr>,
    ) -> Arc<AssociatedConstDatum<ChalkIr>> {
        self.program_ir().unwrap().associated_const_data(ty)
    }

    fn trait_datum(&self, id: TraitId<ChalkIr>) -> Arc<TraitDatum<ChalkIr>> {
        self.program_ir().unwrap().trait_datum(id)
    }

    fn impl_datum(&self, id: ImplId<ChalkIr>) -> Arc<ImplDatum<ChalkIr>> {
        self.program_ir().unwrap().impl_datum(id)
    }

    fn associated_ty_value(
        &self,
        id: AssociatedTyValueId<ChalkIr>,
    ) -> Arc<AssociatedTyValue<ChalkIr>> {
        self.program_ir().unwrap().associated_ty_values[&id].clone()
    }

    fn associated_const_value(
        &self,
        id: AssociatedConstValueId<ChalkIr>,
    ) -> Arc<AssociatedConstValue<ChalkIr>> {
        self.program_ir().unwrap().associated_const_values[&id].clone()
    }

    fn opaque_ty_data(&self, id: OpaqueTyId<ChalkIr>) -> Arc<OpaqueTyDatum<ChalkIr>> {
        self.program_ir().unwrap().opaque_ty_data(id)
    }

    fn hidden_opaque_type(&self, id: OpaqueTyId<ChalkIr>) -> Ty<ChalkIr> {
        self.program_ir().unwrap().hidden_opaque_type(id)
    }

    fn adt_datum(&self, id: AdtId<ChalkIr>) -> Arc<AdtDatum<ChalkIr>> {
        self.program_ir().unwrap().adt_datum(id)
    }

    fn generator_datum(&self, id: GeneratorId<ChalkIr>) -> Arc<GeneratorDatum<ChalkIr>> {
        self.program_ir().unwrap().generator_datum(id)
    }

    fn generator_witness_datum(
        &self,
        id: GeneratorId<ChalkIr>,
    ) -> Arc<GeneratorWitnessDatum<ChalkIr>> {
        self.program_ir().unwrap().generator_witness_datum(id)
    }

    fn adt_repr(&self, id: AdtId<ChalkIr>) -> Arc<AdtRepr<ChalkIr>> {
        self.program_ir().unwrap().adt_repr(id)
    }

    fn fn_def_datum(&self, id: FnDefId<ChalkIr>) -> Arc<FnDefDatum<ChalkIr>> {
        self.program_ir().unwrap().fn_def_datum(id)
    }

    fn impls_for_trait(
        &self,
        trait_id: TraitId<ChalkIr>,
        generic_args: &[GenericArg<ChalkIr>],
        binders: &CanonicalVarKinds<ChalkIr>,
    ) -> Vec<ImplId<ChalkIr>> {
        self.program_ir()
            .unwrap()
            .impls_for_trait(trait_id, generic_args, binders)
    }

    fn local_impls_to_coherence_check(&self, trait_id: TraitId<ChalkIr>) -> Vec<ImplId<ChalkIr>> {
        self.program_ir()
            .unwrap()
            .local_impls_to_coherence_check(trait_id)
    }

    fn impl_provided_for(&self, auto_trait_id: TraitId<ChalkIr>, ty: &TyKind<ChalkIr>) -> bool {
        self.program_ir()
            .unwrap()
            .impl_provided_for(auto_trait_id, ty)
    }

    fn well_known_trait_id(&self, well_known_trait: WellKnownTrait) -> Option<TraitId<ChalkIr>> {
        self.program_ir()
            .unwrap()
            .well_known_trait_id(well_known_trait)
    }

    fn program_clauses_for_env(
        &self,
        environment: &Environment<ChalkIr>,
    ) -> ProgramClauses<ChalkIr> {
        chalk_solve::program_clauses_for_env(self, environment)
    }

    fn interner(&self) -> &ChalkIr {
        &ChalkIr
    }

    fn is_object_safe(&self, trait_id: TraitId<ChalkIr>) -> bool {
        self.program_ir().unwrap().is_object_safe(trait_id)
    }

    fn closure_inputs_and_output(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> Binders<FnDefInputsAndOutputDatum<ChalkIr>> {
        self.program_ir()
            .unwrap()
            .closure_inputs_and_output(closure_id, substs)
    }

    fn closure_kind(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> ClosureKind {
        self.program_ir().unwrap().closure_kind(closure_id, substs)
    }

    fn closure_upvars(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> Binders<Ty<ChalkIr>> {
        self.program_ir()
            .unwrap()
            .closure_upvars(closure_id, substs)
    }

    fn closure_fn_substitution(
        &self,
        closure_id: ClosureId<ChalkIr>,
        substs: &Substitution<ChalkIr>,
    ) -> Substitution<ChalkIr> {
        self.program_ir()
            .unwrap()
            .closure_fn_substitution(closure_id, substs)
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<ChalkIr> {
        self
    }

    fn trait_name(&self, trait_id: TraitId<ChalkIr>) -> String {
        self.program_ir().unwrap().trait_name(trait_id)
    }

    fn adt_name(&self, struct_id: AdtId<ChalkIr>) -> String {
        self.program_ir().unwrap().adt_name(struct_id)
    }

    fn assoc_type_name(&self, assoc_ty_id: AssocTypeId<ChalkIr>) -> String {
        self.program_ir().unwrap().assoc_type_name(assoc_ty_id)
    }

    fn assoc_const_name(&self, assoc_const_id: AssocConstId<ChalkIr>) -> String {
        self.program_ir().unwrap().assoc_const_name(assoc_const_id)
    }

    fn opaque_type_name(&self, opaque_ty_id: OpaqueTyId<ChalkIr>) -> String {
        self.program_ir().unwrap().opaque_type_name(opaque_ty_id)
    }

    fn fn_def_name(&self, fn_def_id: FnDefId<ChalkIr>) -> String {
        self.program_ir().unwrap().fn_def_name(fn_def_id)
    }

    fn discriminant_type(&self, ty: Ty<ChalkIr>) -> Ty<ChalkIr> {
        self.program_ir().unwrap().discriminant_type(ty)
    }
}

impl fmt::Debug for ChalkDatabase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ChalkDatabase {{ }}")
    }
}
