//! Encapsulates the concrete representation of core types such as types and goals.
use crate::AssocTypeId;
use crate::CanonicalVarKind;
use crate::CanonicalVarKinds;
use crate::ClosureId;
use crate::Constraint;
use crate::Constraints;
use crate::FnDefId;
use crate::ForeignDefId;
use crate::GeneratorId;
use crate::GenericArg;
use crate::GenericArgData;
use crate::Goal;
use crate::GoalData;
use crate::Goals;
use crate::InEnvironment;
use crate::Lifetime;
use crate::LifetimeData;
use crate::OpaqueTy;
use crate::OpaqueTyId;
use crate::ProgramClause;
use crate::ProgramClauseData;
use crate::ProgramClauseImplication;
use crate::ProgramClauses;
use crate::ProjectionTy;
use crate::QuantifiedWhereClause;
use crate::QuantifiedWhereClauses;
use crate::SeparatorTraitRef;
use crate::Substitution;
use crate::TraitId;
use crate::Ty;
use crate::TyData;
use crate::VariableKind;
use crate::VariableKinds;
use crate::Variance;
use crate::Variances;
use crate::{AdtId, TyKind};
use crate::{AliasTy, AssocConstId};
use crate::{Const, ConstData};
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::marker::PhantomData;
use std::sync::Arc;

/// A "interner" encapsulates the concrete representation of
/// certain "core types" from chalk-ir. All the types in chalk-ir are
/// parameterized by a `I: Interner`, and so (e.g.) if they want to
/// store a type, they don't store a `Ty<I>` instance directly, but
/// rather prefer a `Ty<I>`. You can think of `I::Type` as the
/// interned representation (and, indeed, it may well be an interned
/// pointer, e.g. in rustc).
///
/// Type families allow chalk to be embedded in different contexts
/// where the concrete representation of core types varies. They also
/// allow us to write generic code that reasons about multiple
/// distinct sets of types by using distinct generic type parameters
/// (e.g., `SourceI` and `TargetI`) -- even if those type parameters
/// wind up being mapped to the same underlying type families in the
/// end.
pub trait Interner: Debug + Copy + Eq + Ord + Hash {
    /// "Interned" representation of types.  In normal user code,
    /// `Self::InternedType` is not referenced. Instead, we refer to
    /// `Ty<Self>`, which wraps this type.
    ///
    /// An `InternedType` must be something that can be created from a
    /// `TyKind` (by the [`intern_ty`] method) and then later
    /// converted back (by the [`ty_data`] method). The interned form
    /// must also introduce indirection, either via a `Box`, `&`, or
    /// other pointer type.
    type InternedType: Debug + Clone + Eq + Hash;

    /// "Interned" representation of lifetimes.  In normal user code,
    /// `Self::InternedLifetime` is not referenced. Instead, we refer to
    /// `Lifetime<Self>`, which wraps this type.
    ///
    /// An `InternedLifetime` must be something that can be created
    /// from a `LifetimeData` (by the [`intern_lifetime`] method) and
    /// then later converted back (by the [`lifetime_data`] method).
    type InternedLifetime: Debug + Clone + Eq + Hash;

    /// "Interned" representation of const expressions. In normal user code,
    /// `Self::InternedConst` is not referenced. Instead, we refer to
    /// `Const<Self>`, which wraps this type.
    ///
    /// An `InternedConst` must be something that can be created
    /// from a `ConstData` (by the [`intern_const`] method) and
    /// then later converted back (by the [`const_data`] method).
    type InternedConst: Debug + Clone + Eq + Hash;

    /// "Interned" representation of an evaluated const value.
    /// `Self::InternedConcreteConst` is not referenced. Instead,
    /// we refer to `ConcreteConst<Self>`, which wraps this type.
    ///
    /// `InternedConcreteConst` instances are not created by chalk,
    /// it can only make a query asking about equality of two
    /// evaluated consts.
    type InternedConcreteConst: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "generic parameter", which can
    /// be either a type or a lifetime.  In normal user code,
    /// `Self::InternedGenericArg` is not referenced. Instead, we refer to
    /// `GenericArg<Self>`, which wraps this type.
    ///
    /// An `InternedType` is created by `intern_generic_arg` and can be
    /// converted back to its underlying data via `generic_arg_data`.
    type InternedGenericArg: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "goal".  In normal user code,
    /// `Self::InternedGoal` is not referenced. Instead, we refer to
    /// `Goal<Self>`, which wraps this type.
    ///
    /// An `InternedGoal` is created by `intern_goal` and can be
    /// converted back to its underlying data via `goal_data`.
    type InternedGoal: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of goals.  In normal user code,
    /// `Self::InternedGoals` is not referenced. Instead, we refer to
    /// `Goals<Self>`, which wraps this type.
    ///
    /// An `InternedGoals` is created by `intern_goals` and can be
    /// converted back to its underlying data via `goals_data`.
    type InternedGoals: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "substitution".  In normal user code,
    /// `Self::InternedSubstitution` is not referenced. Instead, we refer to
    /// `Substitution<Self>`, which wraps this type.
    ///
    /// An `InternedSubstitution` is created by `intern_substitution` and can be
    /// converted back to its underlying data via `substitution_data`.
    type InternedSubstitution: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of program clauses.  In normal user code,
    /// `Self::InternedProgramClauses` is not referenced. Instead, we refer to
    /// `ProgramClauses<Self>`, which wraps this type.
    ///
    /// An `InternedProgramClauses` is created by `intern_program_clauses` and can be
    /// converted back to its underlying data via `program_clauses_data`.
    type InternedProgramClauses: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "program clause".  In normal user code,
    /// `Self::InternedProgramClause` is not referenced. Instead, we refer to
    /// `ProgramClause<Self>`, which wraps this type.
    ///
    /// An `InternedProgramClause` is created by `intern_program_clause` and can be
    /// converted back to its underlying data via `program_clause_data`.
    type InternedProgramClause: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of quantified where clauses.
    /// In normal user code, `Self::InternedQuantifiedWhereClauses` is not referenced.
    /// Instead, we refer to `QuantifiedWhereClauses<Self>`, which wraps this type.
    ///
    /// An `InternedQuantifiedWhereClauses` is created by `intern_quantified_where_clauses`
    /// and can be converted back to its underlying data via `quantified_where_clauses_data`.
    type InternedQuantifiedWhereClauses: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of variable kinds.
    /// In normal user code, `Self::InternedVariableKinds` is not referenced.
    /// Instead, we refer to `VariableKinds<Self>`, which wraps this type.
    ///
    /// An `InternedVariableKinds` is created by `intern_generic_arg_kinds`
    /// and can be converted back to its underlying data via `variable_kinds_data`.
    type InternedVariableKinds: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of variable kinds with universe index.
    /// In normal user code, `Self::InternedCanonicalVarKinds` is not referenced.
    /// Instead, we refer to `CanonicalVarKinds<Self>`, which wraps this type.
    ///
    /// An `InternedCanonicalVarKinds` is created by
    /// `intern_canonical_var_kinds` and can be converted back
    /// to its underlying data via `canonical_var_kinds_data`.
    type InternedCanonicalVarKinds: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of region constraints.
    /// In normal user code, `Self::InternedConstraints` is not referenced.
    /// Instead, we refer to `Constraints<Self>`, which wraps this type.
    ///
    /// An `InternedConstraints` is created by `intern_constraints`
    /// and can be converted back to its underlying data via `constraints_data`.
    type InternedConstraints: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of `chalk_ir::Variance`.
    /// In normal user code, `Self::InternedVariances` is not referenced.
    /// Instead, we refer to `Variances<Self>`, which wraps this type.
    ///
    /// An `InternedVariances` is created by
    /// `intern_variances` and can be converted back
    /// to its underlying data via `variances_data`.
    type InternedVariances: Debug + Clone + Eq + Hash;

    /// The core "id" type used for trait-ids and the like.
    type DefId: Debug + Copy + Eq + Ord + Hash;

    /// The ID type for ADTs
    type InternedAdtId: Debug + Copy + Eq + Ord + Hash;

    /// Representation of identifiers.
    type Identifier: Debug + Clone + Eq + Hash;

    /// Representation of function ABI (e.g. calling convention).
    type FnAbi: Debug + Copy + Eq + Hash;

    /// Prints the debug representation of a type-kind-id.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_adt_id(adt_id: AdtId<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a trait id.
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    #[allow(unused_variables)]
    fn debug_trait_id(
        trait_id: TraitId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an associated-type-id.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_assoc_type_id(
        type_id: AssocTypeId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an associated-const-id.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_assoc_const_id(
        type_id: AssocConstId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an opaque type.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_opaque_ty_id(
        opaque_ty_id: OpaqueTyId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a function-def-id.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_fn_def_id(
        fn_def_id: FnDefId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a closure id.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_closure_id(
        fn_def_id: ClosureId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a foreign-def-id.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_foreign_def_id(
        foreign_def_id: ForeignDefId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an alias.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_generator_id(
        generator_id: GeneratorId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an alias. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    #[allow(unused_variables)]
    fn debug_alias(alias: &AliasTy<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a ProjectionTy.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_projection_ty(
        projection_ty: &ProjectionTy<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an OpaqueTy.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_opaque_ty(
        opaque_ty: &OpaqueTy<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a type.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_ty(ty: &Ty<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a lifetime.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_lifetime(
        lifetime: &Lifetime<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a const.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_const(constant: &Const<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an parameter.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_generic_arg(
        generic_arg: &GenericArg<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a parameter kinds list.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_variable_kinds(
        variable_kinds: &VariableKinds<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a parameter kinds list, with angle brackets.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_variable_kinds_with_angles(
        variable_kinds: &VariableKinds<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an parameter kinds list with universe index.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_canonical_var_kinds(
        canonical_var_kinds: &CanonicalVarKinds<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of an goal.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_goal(goal: &Goal<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a list of goals.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_goals(goals: &Goals<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a ProgramClauseImplication.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_program_clause_implication(
        pci: &ProgramClauseImplication<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a ProgramClause.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_program_clause(
        clause: &ProgramClause<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a ProgramClauses.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_program_clauses(
        clauses: &ProgramClauses<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a Substitution.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_substitution(
        substitution: &Substitution<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a SeparatorTraitRef.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_separator_trait_ref(
        separator_trait_ref: &SeparatorTraitRef<'_, Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a QuantifiedWhereClauses.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_quantified_where_clauses(
        clauses: &QuantifiedWhereClauses<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a Constraints.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_constraints(
        clauses: &Constraints<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Prints the debug representation of a Variances.
    /// Returns `None` to fallback to the default debug output.
    #[allow(unused_variables)]
    fn debug_variances(
        variances: &Variances<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    /// Create an "interned" type from `ty`. This is not normally
    /// invoked directly; instead, you invoke `TyKind::intern` (which
    /// will ultimately call this method).
    fn intern_ty(&self, kind: TyKind<Self>) -> Self::InternedType;

    /// Lookup the `TyKind` from an interned type.
    fn ty_data<'a>(&self, ty: &'a Self::InternedType) -> &'a TyData<Self>;

    /// Create an "interned" lifetime from `lifetime`. This is not
    /// normally invoked directly; instead, you invoke
    /// `LifetimeData::intern` (which will ultimately call this
    /// method).
    fn intern_lifetime(&self, lifetime: LifetimeData<Self>) -> Self::InternedLifetime;

    /// Lookup the `LifetimeData` that was interned to create a `InternedLifetime`.
    fn lifetime_data<'a>(&self, lifetime: &'a Self::InternedLifetime) -> &'a LifetimeData<Self>;

    /// Create an "interned" const from `const`. This is not
    /// normally invoked directly; instead, you invoke
    /// `ConstData::intern` (which will ultimately call this
    /// method).
    fn intern_const(&self, constant: ConstData<Self>) -> Self::InternedConst;

    /// Lookup the `ConstData` that was interned to create a `InternedConst`.
    fn const_data<'a>(&self, constant: &'a Self::InternedConst) -> &'a ConstData<Self>;

    /// Determine whether two concrete const values are equal.
    fn const_eq(
        &self,
        ty: &Self::InternedType,
        c1: &Self::InternedConcreteConst,
        c2: &Self::InternedConcreteConst,
    ) -> bool;

    /// Create an "interned" parameter from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `GenericArgData::intern` (which will ultimately call this
    /// method).
    fn intern_generic_arg(&self, data: GenericArgData<Self>) -> Self::InternedGenericArg;

    /// Lookup the `LifetimeData` that was interned to create a `InternedLifetime`.
    fn generic_arg_data<'a>(
        &self,
        lifetime: &'a Self::InternedGenericArg,
    ) -> &'a GenericArgData<Self>;

    /// Create an "interned" goal from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `GoalData::intern` (which will ultimately call this
    /// method).
    fn intern_goal(&self, data: GoalData<Self>) -> Self::InternedGoal;

    /// Lookup the `GoalData` that was interned to create a `InternedGoal`.
    fn goal_data<'a>(&self, goal: &'a Self::InternedGoal) -> &'a GoalData<Self>;

    /// Create an "interned" goals from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `GoalsData::intern` (which will ultimately call this
    /// method).
    fn intern_goals<E>(
        &self,
        data: impl IntoIterator<Item = Result<Goal<Self>, E>>,
    ) -> Result<Self::InternedGoals, E>;

    /// Lookup the `GoalsData` that was interned to create a `InternedGoals`.
    fn goals_data<'a>(&self, goals: &'a Self::InternedGoals) -> &'a [Goal<Self>];

    /// Create an "interned" substitution from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `SubstitutionData::intern` (which will ultimately call this
    /// method).
    fn intern_substitution<E>(
        &self,
        data: impl IntoIterator<Item = Result<GenericArg<Self>, E>>,
    ) -> Result<Self::InternedSubstitution, E>;

    /// Lookup the `SubstitutionData` that was interned to create a `InternedSubstitution`.
    fn substitution_data<'a>(
        &self,
        substitution: &'a Self::InternedSubstitution,
    ) -> &'a [GenericArg<Self>];

    /// Create an "interned" program clause from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `ProgramClauseData::intern` (which will ultimately call this
    /// method).
    fn intern_program_clause(&self, data: ProgramClauseData<Self>) -> Self::InternedProgramClause;

    /// Lookup the `ProgramClauseData` that was interned to create a `ProgramClause`.
    fn program_clause_data<'a>(
        &self,
        clause: &'a Self::InternedProgramClause,
    ) -> &'a ProgramClauseData<Self>;

    /// Create an "interned" program clauses from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `ProgramClauses::from_iter` (which will ultimately call this
    /// method).
    fn intern_program_clauses<E>(
        &self,
        data: impl IntoIterator<Item = Result<ProgramClause<Self>, E>>,
    ) -> Result<Self::InternedProgramClauses, E>;

    /// Lookup the `ProgramClauseData` that was interned to create a `ProgramClause`.
    fn program_clauses_data<'a>(
        &self,
        clauses: &'a Self::InternedProgramClauses,
    ) -> &'a [ProgramClause<Self>];

    /// Create an "interned" quantified where clauses from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `QuantifiedWhereClauses::from_iter` (which will ultimately call this
    /// method).
    fn intern_quantified_where_clauses<E>(
        &self,
        data: impl IntoIterator<Item = Result<QuantifiedWhereClause<Self>, E>>,
    ) -> Result<Self::InternedQuantifiedWhereClauses, E>;

    /// Lookup the slice of `QuantifiedWhereClause` that was interned to
    /// create a `QuantifiedWhereClauses`.
    fn quantified_where_clauses_data<'a>(
        &self,
        clauses: &'a Self::InternedQuantifiedWhereClauses,
    ) -> &'a [QuantifiedWhereClause<Self>];

    /// Create an "interned" parameter kinds from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `VariableKinds::from_iter` (which will ultimately call this
    /// method).
    fn intern_generic_arg_kinds<E>(
        &self,
        data: impl IntoIterator<Item = Result<VariableKind<Self>, E>>,
    ) -> Result<Self::InternedVariableKinds, E>;

    /// Lookup the slice of `VariableKinds` that was interned to
    /// create a `VariableKinds`.
    fn variable_kinds_data<'a>(
        &self,
        variable_kinds: &'a Self::InternedVariableKinds,
    ) -> &'a [VariableKind<Self>];

    /// Create "interned" variable kinds with universe index from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `CanonicalVarKinds::from_iter` (which will ultimately call this
    /// method).
    fn intern_canonical_var_kinds<E>(
        &self,
        data: impl IntoIterator<Item = Result<CanonicalVarKind<Self>, E>>,
    ) -> Result<Self::InternedCanonicalVarKinds, E>;

    /// Lookup the slice of `CanonicalVariableKind` that was interned to
    /// create a `CanonicalVariableKinds`.
    fn canonical_var_kinds_data<'a>(
        &self,
        canonical_var_kinds: &'a Self::InternedCanonicalVarKinds,
    ) -> &'a [CanonicalVarKind<Self>];

    /// Create "interned" constraints from `data`. This is not
    /// normally invoked dirctly; instead, you invoke
    /// `Constraints::from_iter` (which will ultimately call this
    /// method).
    fn intern_constraints<E>(
        &self,
        data: impl IntoIterator<Item = Result<InEnvironment<Constraint<Self>>, E>>,
    ) -> Result<Self::InternedConstraints, E>;

    /// Lookup the slice of `Constraint` that was interned to
    /// create a `Constraints`.
    fn constraints_data<'a>(
        &self,
        constraints: &'a Self::InternedConstraints,
    ) -> &'a [InEnvironment<Constraint<Self>>];

    /// Create "interned" variances from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `Variances::from` (which will ultimately call this
    /// method).
    fn intern_variances<E>(
        &self,
        data: impl IntoIterator<Item = Result<Variance, E>>,
    ) -> Result<Self::InternedVariances, E>;

    /// Lookup the slice of `Variance` that was interned to
    /// create a `Variances`.
    fn variances_data<'a>(&self, variances: &'a Self::InternedVariances) -> &'a [Variance];
}

/// Implemented by types that have an associated interner (which
/// are virtually all of the types in chalk-ir, for example).
/// This lets us map from a type like `Ty<I>` to the parameter `I`.
///
/// It's particularly useful for writing `Fold` impls for generic types like
/// `Binder<T>`, since it allows us to figure out the interner of `T`.
pub trait HasInterner {
    /// The interner associated with the type.
    type Interner: Interner;
}

impl<T: HasInterner> HasInterner for [T] {
    type Interner = T::Interner;
}

impl<T: HasInterner> HasInterner for Vec<T> {
    type Interner = T::Interner;
}

impl<T: HasInterner> HasInterner for Box<T> {
    type Interner = T::Interner;
}

impl<T: HasInterner> HasInterner for Arc<T> {
    type Interner = T::Interner;
}

impl<T: HasInterner + ?Sized> HasInterner for &T {
    type Interner = T::Interner;
}

impl<I: Interner> HasInterner for PhantomData<I> {
    type Interner = I;
}

impl<A, B, I> HasInterner for (A, B)
where
    A: HasInterner<Interner = I>,
    B: HasInterner<Interner = I>,
    I: Interner,
{
    type Interner = I;
}

impl<A, B, C, I> HasInterner for (A, B, C)
where
    A: HasInterner<Interner = I>,
    B: HasInterner<Interner = I>,
    C: HasInterner<Interner = I>,
    I: Interner,
{
    type Interner = I;
}

impl<'a, T: HasInterner> HasInterner for std::slice::Iter<'a, T> {
    type Interner = T::Interner;
}
