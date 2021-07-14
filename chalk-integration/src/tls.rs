use crate::interner::ChalkIr;
use chalk_ir::{
    debug::SeparatorTraitRef, AdtId, AliasTy, AssocConstId, AssocTypeId, CanonicalVarKinds,
    Constraints, FnDefId, GenericArg, Goal, Goals, Lifetime, OpaqueTy, OpaqueTyId, ProgramClause,
    ProgramClauseImplication, ProgramClauses, ProjectionTy, QuantifiedWhereClauses, Substitution,
    TraitId, Ty, VariableKinds, Variances,
};
use std::cell::RefCell;
use std::fmt;
use std::sync::Arc;

thread_local! {
    static PROGRAM: RefCell<Option<Arc<dyn DebugContext>>> = RefCell::new(None)
}

pub trait DebugContext {
    fn debug_adt_id(
        &self,
        id: AdtId<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_trait_id(
        &self,
        id: TraitId<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_assoc_type_id(
        &self,
        id: AssocTypeId<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_assoc_const_id(
        &self,
        id: AssocConstId<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_opaque_ty_id(
        &self,
        id: OpaqueTyId<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_fn_def_id(
        &self,
        fn_def_id: FnDefId<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_alias(
        &self,
        alias: &AliasTy<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_opaque_ty(
        &self,
        opaque_ty: &OpaqueTy<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_projection_ty(
        &self,
        proj: &ProjectionTy<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_ty(&self, ty: &Ty<ChalkIr>, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error>;

    fn debug_lifetime(
        &self,
        lifetime: &Lifetime<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_generic_arg(
        &self,
        generic_arg: &GenericArg<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_variable_kinds(
        &self,
        variable_kinds: &VariableKinds<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_variable_kinds_with_angles(
        &self,
        variable_kinds: &VariableKinds<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_canonical_var_kinds(
        &self,
        variable_kinds: &CanonicalVarKinds<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_goal(
        &self,
        goal: &Goal<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_goals(
        &self,
        goals: &Goals<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_program_clause_implication(
        &self,
        pci: &ProgramClauseImplication<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_program_clause(
        &self,
        clause: &ProgramClause<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_program_clauses(
        &self,
        clauses: &ProgramClauses<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_substitution(
        &self,
        substitution: &Substitution<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_separator_trait_ref(
        &self,
        separator_trait_ref: &SeparatorTraitRef<'_, ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_quantified_where_clauses(
        &self,
        clauses: &QuantifiedWhereClauses<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_constraints(
        &self,
        constraints: &Constraints<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;

    fn debug_variances(
        &self,
        variances: &Variances<ChalkIr>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;
}

pub fn with_current_program<R>(op: impl FnOnce(Option<&Arc<dyn DebugContext>>) -> R) -> R {
    PROGRAM.with(|prog_cell| {
        let p = prog_cell.borrow();
        op(p.as_ref())
    })
}

pub fn set_current_program<OP, R>(p: &Arc<impl DebugContext + 'static>, op: OP) -> R
where
    OP: FnOnce() -> R,
{
    let p: Arc<dyn DebugContext> = p.clone();
    PROGRAM.with(|prog_cell| {
        *prog_cell.borrow_mut() = Some(p);
        let r = op();
        *prog_cell.borrow_mut() = None;
        r
    })
}
