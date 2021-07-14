//! Debug impls for types.

use std::fmt::{Debug, Display, Error, Formatter};

use super::*;

impl<I: Interner> Debug for TraitId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_trait_id(*self, fmt).unwrap_or_else(|| write!(fmt, "TraitId({:?})", self.0))
    }
}

impl<I: Interner> Debug for AdtId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_adt_id(*self, fmt).unwrap_or_else(|| write!(fmt, "AdtId({:?})", self.0))
    }
}

impl<I: Interner> Debug for AssocTypeId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_assoc_type_id(*self, fmt)
            .unwrap_or_else(|| write!(fmt, "AssocTypeId({:?})", self.0))
    }
}

impl<I: Interner> Debug for AssocConstId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_assoc_const_id(*self, fmt)
            .unwrap_or_else(|| write!(fmt, "AssocConstId({:?})", self.0))
    }
}

impl<I: Interner> Debug for FnDefId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        I::debug_fn_def_id(*self, fmt).unwrap_or_else(|| write!(fmt, "FnDefId({:?})", self.0))
    }
}

impl<I: Interner> Debug for ClosureId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        I::debug_closure_id(*self, fmt).unwrap_or_else(|| write!(fmt, "ClosureId({:?})", self.0))
    }
}

impl<I: Interner> Debug for GeneratorId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        I::debug_generator_id(*self, fmt)
            .unwrap_or_else(|| write!(fmt, "GeneratorId({:?})", self.0))
    }
}

impl<I: Interner> Debug for ForeignDefId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        I::debug_foreign_def_id(*self, fmt)
            .unwrap_or_else(|| write!(fmt, "ForeignDefId({:?})", self.0))
    }
}

impl<I: Interner> Debug for Ty<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_ty(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for Lifetime<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_lifetime(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for Const<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_const(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for ConcreteConst<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{:?}", self.interned)
    }
}

impl<I: Interner> Debug for GenericArg<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_generic_arg(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for Goal<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_goal(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for Goals<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_goals(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for ProgramClauseImplication<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_program_clause_implication(self, fmt)
            .unwrap_or_else(|| write!(fmt, "ProgramClauseImplication(?)"))
    }
}

impl<I: Interner> Debug for ProgramClause<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_program_clause(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for ProgramClauses<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_program_clauses(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for Constraints<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_constraints(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for SeparatorTraitRef<'_, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_separator_trait_ref(self, fmt)
            .unwrap_or_else(|| write!(fmt, "SeparatorTraitRef(?)"))
    }
}

impl<I: Interner> Debug for AliasTy<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_alias(self, fmt).unwrap_or_else(|| write!(fmt, "AliasTy(?)"))
    }
}

impl<I: Interner> Debug for QuantifiedWhereClauses<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_quantified_where_clauses(self, fmt)
            .unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for ProjectionTy<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_projection_ty(self, fmt).unwrap_or_else(|| {
            unimplemented!("cannot format ProjectionTy without setting Program in tls")
        })
    }
}

impl<I: Interner> Debug for OpaqueTy<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_opaque_ty(self, fmt).unwrap_or_else(|| {
            unimplemented!("cannot format OpaqueTy without setting Program in tls")
        })
    }
}

impl<I: Interner> Display for Substitution<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_substitution(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<I: Interner> Debug for OpaqueTyId<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_opaque_ty_id(*self, fmt).unwrap_or_else(|| write!(fmt, "OpaqueTyId({:?})", self.0))
    }
}

impl Display for UniverseIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "U{}", self.counter)
    }
}

impl Debug for UniverseIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "U{}", self.counter)
    }
}

impl<I: Interner> Debug for TyData<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        self.kind.fmt(fmt)
    }
}

impl<I: Interner> Debug for TyKind<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            TyKind::BoundVar(db) => write!(fmt, "{:?}", db),
            TyKind::Dyn(clauses) => write!(fmt, "{:?}", clauses),
            TyKind::InferenceVar(var, TyVariableKind::General) => write!(fmt, "{:?}", var),
            TyKind::InferenceVar(var, TyVariableKind::Integer) => write!(fmt, "{:?}i", var),
            TyKind::InferenceVar(var, TyVariableKind::Float) => write!(fmt, "{:?}f", var),
            TyKind::Alias(alias) => write!(fmt, "{:?}", alias),
            TyKind::Placeholder(index) => write!(fmt, "{:?}", index),
            TyKind::Function(function) => write!(fmt, "{:?}", function),
            TyKind::Adt(id, substitution) => write!(fmt, "{:?}<{:?}>", id, substitution),
            TyKind::AssociatedType(assoc_ty, substitution) => {
                write!(fmt, "{:?}<{:?}>", assoc_ty, substitution)
            }
            TyKind::Scalar(scalar) => write!(fmt, "{:?}", scalar),
            TyKind::Str => write!(fmt, "Str"),
            TyKind::Tuple(arity, substitution) => write!(fmt, "{:?}<{:?}>", arity, substitution),
            TyKind::OpaqueType(opaque_ty, substitution) => {
                write!(fmt, "!{:?}<{:?}>", opaque_ty, substitution)
            }
            TyKind::Slice(substitution) => write!(fmt, "{{slice}}<{:?}>", substitution),
            TyKind::FnDef(fn_def, substitution) => write!(fmt, "{:?}<{:?}>", fn_def, substitution),
            TyKind::Ref(mutability, lifetime, ty) => match mutability {
                Mutability::Mut => write!(fmt, "(&{:?} mut {:?})", lifetime, ty),
                Mutability::Not => write!(fmt, "(&{:?} {:?})", lifetime, ty),
            },
            TyKind::Raw(mutability, ty) => match mutability {
                Mutability::Mut => write!(fmt, "(*mut {:?})", ty),
                Mutability::Not => write!(fmt, "(*const {:?})", ty),
            },
            TyKind::Never => write!(fmt, "Never"),
            TyKind::Array(ty, const_) => write!(fmt, "[{:?}; {:?}]", ty, const_),
            TyKind::Closure(id, substitution) => {
                write!(fmt, "{{closure:{:?}}}<{:?}>", id, substitution)
            }
            TyKind::Generator(generator, substitution) => {
                write!(fmt, "{:?}<{:?}>", generator, substitution)
            }
            TyKind::GeneratorWitness(witness, substitution) => {
                write!(fmt, "{:?}<{:?}>", witness, substitution)
            }
            TyKind::Foreign(foreign_ty) => write!(fmt, "{:?}", foreign_ty),
            TyKind::Error => write!(fmt, "{{error}}"),
        }
    }
}

impl Debug for BoundVar {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let BoundVar { debruijn, index } = self;
        write!(fmt, "{:?}.{:?}", debruijn, index)
    }
}

impl Debug for DebruijnIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let DebruijnIndex { depth } = self;
        write!(fmt, "^{}", depth)
    }
}

impl<I: Interner> Debug for DynTy<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let DynTy { bounds, lifetime } = self;
        write!(fmt, "dyn {:?} + {:?}", bounds, lifetime)
    }
}

impl Debug for InferenceVar {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "?{}", self.index)
    }
}

impl<I: Interner> Debug for FnSubst<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{:?}", self.0)
    }
}

impl<I: Interner> Debug for FnPointer<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        // FIXME -- we should introduce some names or something here
        let FnPointer {
            num_binders,
            substitution,
            sig,
        } = self;
        write!(
            fmt,
            "{}{:?} for<{}> {:?}",
            match sig.safety {
                Safety::Unsafe => "unsafe ",
                Safety::Safe => "",
            },
            sig.abi,
            num_binders,
            substitution
        )
    }
}

impl<I: Interner> Debug for LifetimeData<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            LifetimeData::BoundVar(db) => write!(fmt, "'{:?}", db),
            LifetimeData::InferenceVar(var) => write!(fmt, "'{:?}", var),
            LifetimeData::Placeholder(index) => write!(fmt, "'{:?}", index),
            LifetimeData::Static => write!(fmt, "'static"),
            LifetimeData::Empty(UniverseIndex::ROOT) => write!(fmt, "'<empty>"),
            LifetimeData::Empty(universe) => write!(fmt, "'<empty:{:?}>", universe),
            LifetimeData::Erased => write!(fmt, "'<erased>"),
            LifetimeData::Phantom(..) => unreachable!(),
        }
    }
}

impl<I: Interner> VariableKinds<I> {
    fn debug(&self) -> VariableKindsDebug<'_, I> {
        VariableKindsDebug(self)
    }

    /// Helper method for debugging variable kinds.
    pub fn inner_debug<'a>(&'a self, interner: &'a I) -> VariableKindsInnerDebug<'a, I> {
        VariableKindsInnerDebug {
            variable_kinds: self,
            interner,
        }
    }
}

struct VariableKindsDebug<'a, I: Interner>(&'a VariableKinds<I>);

impl<'a, I: Interner> Debug for VariableKindsDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_variable_kinds_with_angles(self.0, fmt)
            .unwrap_or_else(|| write!(fmt, "{:?}", self.0.interned))
    }
}

/// Helper struct for showing debug output for `VariableKinds`.
pub struct VariableKindsInnerDebug<'a, I: Interner> {
    variable_kinds: &'a VariableKinds<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for VariableKindsInnerDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        // NB: We print variable kinds as a list delimited by `<>`,
        // like `<K1, K2, ..>`. This is because variable kind lists
        // are always associated with binders like `forall<type> {
        // ... }`.
        write!(fmt, "<")?;
        for (index, binder) in self.variable_kinds.iter(self.interner).enumerate() {
            if index > 0 {
                write!(fmt, ", ")?;
            }
            match binder {
                VariableKind::Ty(TyVariableKind::General) => write!(fmt, "type")?,
                VariableKind::Ty(TyVariableKind::Integer) => write!(fmt, "integer type")?,
                VariableKind::Ty(TyVariableKind::Float) => write!(fmt, "float type")?,
                VariableKind::Lifetime => write!(fmt, "lifetime")?,
                VariableKind::Const(ty) => write!(fmt, "const: {:?}", ty)?,
            }
        }
        write!(fmt, ">")
    }
}

impl<I: Interner> Debug for ConstData<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match &self.value {
            ConstValue::BoundVar(db) => write!(fmt, "{:?}", db),
            ConstValue::InferenceVar(var) => write!(fmt, "{:?}", var),
            ConstValue::Placeholder(index) => write!(fmt, "{:?}", index),
            ConstValue::Concrete(evaluated) => write!(fmt, "{:?}", evaluated),
            ConstValue::ConstProjection(_) => todo!(),
        }
    }
}

impl<I: Interner> Debug for GoalData<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            GoalData::Quantified(qkind, ref subgoal) => write!(
                fmt,
                "{:?}{:?} {{ {:?} }}",
                qkind,
                subgoal.binders.debug(),
                subgoal.value
            ),
            GoalData::Implies(ref wc, ref g) => write!(fmt, "if ({:?}) {{ {:?} }}", wc, g),
            GoalData::All(ref goals) => write!(fmt, "all{:?}", goals),
            GoalData::Not(ref g) => write!(fmt, "not {{ {:?} }}", g),
            GoalData::EqGoal(ref wc) => write!(fmt, "{:?}", wc),
            GoalData::SubtypeGoal(ref wc) => write!(fmt, "{:?}", wc),
            GoalData::DomainGoal(ref wc) => write!(fmt, "{:?}", wc),
            GoalData::CannotProve => write!(fmt, r"¯\_(ツ)_/¯"),
        }
    }
}

/// Helper struct for showing debug output for `Goals`.
pub struct GoalsDebug<'a, I: Interner> {
    goals: &'a Goals<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for GoalsDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "(")?;
        for (goal, index) in self.goals.iter(self.interner).zip(0..) {
            if index > 0 {
                write!(fmt, ", ")?;
            }
            write!(fmt, "{:?}", goal)?;
        }
        write!(fmt, ")")?;
        Ok(())
    }
}

impl<I: Interner> Goals<I> {
    /// Show debug output for `Goals`.
    pub fn debug<'a>(&'a self, interner: &'a I) -> GoalsDebug<'a, I> {
        GoalsDebug {
            goals: self,
            interner,
        }
    }
}

/// Helper struct for showing debug output for `GenericArgData`.
pub struct GenericArgDataInnerDebug<'a, I: Interner>(&'a GenericArgData<I>);

impl<'a, I: Interner> Debug for GenericArgDataInnerDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self.0 {
            GenericArgData::Ty(n) => write!(fmt, "{:?}", n),
            GenericArgData::Lifetime(n) => write!(fmt, "{:?}", n),
            GenericArgData::Const(n) => write!(fmt, "{:?}", n),
        }
    }
}

impl<I: Interner> GenericArgData<I> {
    /// Helper method for debugging `GenericArgData`.
    pub fn inner_debug(&self) -> GenericArgDataInnerDebug<'_, I> {
        GenericArgDataInnerDebug(self)
    }
}

/// Helper struct for showing debug output for program clause implications.
pub struct ProgramClauseImplicationDebug<'a, I: Interner> {
    pci: &'a ProgramClauseImplication<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for ProgramClauseImplicationDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let ProgramClauseImplicationDebug { pci, interner } = self;
        write!(fmt, "{:?}", pci.consequence)?;

        let conditions = pci.conditions.as_slice(interner);

        let conds = conditions.len();
        if conds == 0 {
            return Ok(());
        }

        write!(fmt, " :- ")?;
        for cond in &conditions[..conds - 1] {
            write!(fmt, "{:?}, ", cond)?;
        }
        write!(fmt, "{:?}", conditions[conds - 1])
    }
}

impl<I: Interner> ProgramClauseImplication<I> {
    /// Show debug output for the program clause implication.
    pub fn debug<'a>(&'a self, interner: &'a I) -> ProgramClauseImplicationDebug<'a, I> {
        ProgramClauseImplicationDebug {
            pci: self,
            interner,
        }
    }
}

/// Helper struct for showing debug output for application types.
pub struct TyKindDebug<'a, I: Interner> {
    ty: &'a TyKind<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for TyKindDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let interner = self.interner;
        match self.ty {
            TyKind::BoundVar(db) => write!(fmt, "{:?}", db),
            TyKind::Dyn(clauses) => write!(fmt, "{:?}", clauses),
            TyKind::InferenceVar(var, TyVariableKind::General) => write!(fmt, "{:?}", var),
            TyKind::InferenceVar(var, TyVariableKind::Integer) => write!(fmt, "{:?}i", var),
            TyKind::InferenceVar(var, TyVariableKind::Float) => write!(fmt, "{:?}f", var),
            TyKind::Alias(alias) => write!(fmt, "{:?}", alias),
            TyKind::Placeholder(index) => write!(fmt, "{:?}", index),
            TyKind::Function(function) => write!(fmt, "{:?}", function),
            TyKind::Adt(id, substitution) => {
                write!(fmt, "{:?}{:?}", id, substitution.with_angle(interner))
            }
            TyKind::AssociatedType(assoc_ty, substitution) => {
                write!(fmt, "{:?}{:?}", assoc_ty, substitution.with_angle(interner))
            }
            TyKind::Scalar(scalar) => write!(fmt, "{:?}", scalar),
            TyKind::Str => write!(fmt, "Str"),
            TyKind::Tuple(arity, substitution) => {
                write!(fmt, "{:?}{:?}", arity, substitution.with_angle(interner))
            }
            TyKind::OpaqueType(opaque_ty, substitution) => write!(
                fmt,
                "!{:?}{:?}",
                opaque_ty,
                substitution.with_angle(interner)
            ),
            TyKind::Slice(ty) => write!(fmt, "[{:?}]", ty),
            TyKind::FnDef(fn_def, substitution) => {
                write!(fmt, "{:?}{:?}", fn_def, substitution.with_angle(interner))
            }
            TyKind::Ref(mutability, lifetime, ty) => match mutability {
                Mutability::Mut => write!(fmt, "(&{:?} mut {:?})", lifetime, ty),
                Mutability::Not => write!(fmt, "(&{:?} {:?})", lifetime, ty),
            },
            TyKind::Raw(mutability, ty) => match mutability {
                Mutability::Mut => write!(fmt, "(*mut {:?})", ty),
                Mutability::Not => write!(fmt, "(*const {:?})", ty),
            },
            TyKind::Never => write!(fmt, "Never"),
            TyKind::Array(ty, const_) => write!(fmt, "[{:?}; {:?}]", ty, const_),
            TyKind::Closure(id, substitution) => write!(
                fmt,
                "{{closure:{:?}}}{:?}",
                id,
                substitution.with_angle(interner)
            ),
            TyKind::Generator(generator, substitution) => write!(
                fmt,
                "{:?}{:?}",
                generator,
                substitution.with_angle(interner)
            ),
            TyKind::GeneratorWitness(witness, substitution) => {
                write!(fmt, "{:?}{:?}", witness, substitution.with_angle(interner))
            }
            TyKind::Foreign(foreign_ty) => write!(fmt, "{:?}", foreign_ty,),
            TyKind::Error => write!(fmt, "{{error}}"),
        }
    }
}

impl<I: Interner> TyKind<I> {
    /// Show debug output for the application type.
    pub fn debug<'a>(&'a self, interner: &'a I) -> TyKindDebug<'a, I> {
        TyKindDebug { ty: self, interner }
    }
}

/// Helper struct for showing debug output for substitutions.
pub struct SubstitutionDebug<'a, I: Interner> {
    substitution: &'a Substitution<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for SubstitutionDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let SubstitutionDebug {
            substitution,
            interner,
        } = self;
        let mut first = true;

        write!(fmt, "[")?;

        for (index, value) in substitution.iter(interner).enumerate() {
            if first {
                first = false;
            } else {
                write!(fmt, ", ")?;
            }

            write!(fmt, "?{} := {:?}", index, value)?;
        }

        write!(fmt, "]")?;

        Ok(())
    }
}

impl<I: Interner> Substitution<I> {
    /// Show debug output for the substitution.
    pub fn debug<'a>(&'a self, interner: &'a I) -> SubstitutionDebug<'a, I> {
        SubstitutionDebug {
            substitution: self,
            interner,
        }
    }
}

impl Debug for PlaceholderIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let PlaceholderIndex { ui, idx } = self;
        write!(fmt, "!{}_{}", ui.counter, idx)
    }
}

impl<I: Interner> TraitRef<I> {
    /// Returns a "Debuggable" type that prints like `P0 as Trait<P1..>`.
    pub fn with_as(&self) -> impl std::fmt::Debug + '_ {
        SeparatorTraitRef {
            trait_ref: self,
            separator: " as ",
        }
    }

    /// Returns a "Debuggable" type that prints like `P0: Trait<P1..>`.
    pub fn with_colon(&self) -> impl std::fmt::Debug + '_ {
        SeparatorTraitRef {
            trait_ref: self,
            separator: ": ",
        }
    }
}

impl<I: Interner> Debug for TraitRef<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        Debug::fmt(&self.with_as(), fmt)
    }
}

/// Trait ref with associated separator used for debug output.
pub struct SeparatorTraitRef<'me, I: Interner> {
    /// The `TraitRef` itself.
    pub trait_ref: &'me TraitRef<I>,

    /// The separator used for displaying the `TraitRef`.
    pub separator: &'me str,
}

/// Helper struct for showing debug output for the `SeperatorTraitRef`.
pub struct SeparatorTraitRefDebug<'a, 'me, I: Interner> {
    separator_trait_ref: &'a SeparatorTraitRef<'me, I>,
    interner: &'a I,
}

impl<'a, 'me, I: Interner> Debug for SeparatorTraitRefDebug<'a, 'me, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let SeparatorTraitRefDebug {
            separator_trait_ref,
            interner,
        } = self;
        let parameters = separator_trait_ref
            .trait_ref
            .substitution
            .as_slice(interner);
        write!(
            fmt,
            "{:?}{}{:?}{:?}",
            parameters[0],
            separator_trait_ref.separator,
            separator_trait_ref.trait_ref.trait_id,
            Angle(&parameters[1..])
        )
    }
}

impl<'me, I: Interner> SeparatorTraitRef<'me, I> {
    /// Show debug output for the `SeperatorTraitRef`.
    pub fn debug<'a>(&'a self, interner: &'a I) -> SeparatorTraitRefDebug<'a, 'me, I> {
        SeparatorTraitRefDebug {
            separator_trait_ref: self,
            interner,
        }
    }
}

impl<I: Interner> Debug for LifetimeOutlives<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{:?}: {:?}", self.a, self.b)
    }
}

impl<I: Interner> Debug for TypeOutlives<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{:?}: {:?}", self.ty, self.lifetime)
    }
}

/// Helper struct for showing debug output for projection types.
pub struct ProjectionTyDebug<'a, I: Interner> {
    projection_ty: &'a ProjectionTy<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for ProjectionTyDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let ProjectionTyDebug {
            projection_ty,
            interner,
        } = self;
        write!(
            fmt,
            "({:?}){:?}",
            projection_ty.associated_ty_id,
            projection_ty.substitution.with_angle(interner)
        )
    }
}

impl<I: Interner> ProjectionTy<I> {
    /// Show debug output for the projection type.
    pub fn debug<'a>(&'a self, interner: &'a I) -> ProjectionTyDebug<'a, I> {
        ProjectionTyDebug {
            projection_ty: self,
            interner,
        }
    }
}

/// Helper struct for showing debug output for opaque types.
pub struct OpaqueTyDebug<'a, I: Interner> {
    opaque_ty: &'a OpaqueTy<I>,
    interner: &'a I,
}

impl<'a, I: Interner> Debug for OpaqueTyDebug<'a, I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let OpaqueTyDebug {
            opaque_ty,
            interner,
        } = self;
        write!(
            fmt,
            "{:?}{:?}",
            opaque_ty.opaque_ty_id,
            opaque_ty.substitution.with_angle(interner)
        )
    }
}

impl<I: Interner> OpaqueTy<I> {
    /// Show debug output for the opaque type.
    pub fn debug<'a>(&'a self, interner: &'a I) -> OpaqueTyDebug<'a, I> {
        OpaqueTyDebug {
            opaque_ty: self,
            interner,
        }
    }
}

/// Wraps debug output in angle brackets (`<>`).
pub struct Angle<'a, T>(pub &'a [T]);

impl<'a, T: Debug> Debug for Angle<'a, T> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        if !self.0.is_empty() {
            write!(fmt, "<")?;
            for (index, elem) in self.0.iter().enumerate() {
                if index > 0 {
                    write!(fmt, ", {:?}", elem)?;
                } else {
                    write!(fmt, "{:?}", elem)?;
                }
            }
            write!(fmt, ">")?;
        }
        Ok(())
    }
}

impl<I: Interner> Debug for Normalize<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "Normalize({:?} -> {:?})", self.alias, self.ty)
    }
}

impl<I: Interner> Debug for AliasEq<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "AliasEq({:?} = {:?})", self.alias, self.ty)
    }
}

impl<I: Interner> Debug for WhereClause<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            WhereClause::Implemented(tr) => write!(fmt, "Implemented({:?})", tr.with_colon()),
            WhereClause::AliasEq(a) => write!(fmt, "{:?}", a),
            WhereClause::LifetimeOutlives(l_o) => write!(fmt, "{:?}", l_o),
            WhereClause::TypeOutlives(t_o) => write!(fmt, "{:?}", t_o),
        }
    }
}

impl<I: Interner> Debug for FromEnv<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            FromEnv::Trait(t) => write!(fmt, "FromEnv({:?})", t.with_colon()),
            FromEnv::Ty(t) => write!(fmt, "FromEnv({:?})", t),
        }
    }
}

impl<I: Interner> Debug for WellFormed<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            WellFormed::Trait(t) => write!(fmt, "WellFormed({:?})", t.with_colon()),
            WellFormed::Ty(t) => write!(fmt, "WellFormed({:?})", t),
        }
    }
}

impl<I: Interner> Debug for DomainGoal<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            DomainGoal::Holds(n) => write!(fmt, "{:?}", n),
            DomainGoal::WellFormed(n) => write!(fmt, "{:?}", n),
            DomainGoal::FromEnv(n) => write!(fmt, "{:?}", n),
            DomainGoal::Normalize(n) => write!(fmt, "{:?}", n),
            DomainGoal::IsLocal(n) => write!(fmt, "IsLocal({:?})", n),
            DomainGoal::IsUpstream(n) => write!(fmt, "IsUpstream({:?})", n),
            DomainGoal::IsFullyVisible(n) => write!(fmt, "IsFullyVisible({:?})", n),
            DomainGoal::LocalImplAllowed(tr) => {
                write!(fmt, "LocalImplAllowed({:?})", tr.with_colon(),)
            }
            DomainGoal::Compatible => write!(fmt, "Compatible"),
            DomainGoal::DownstreamType(n) => write!(fmt, "DownstreamType({:?})", n),
            DomainGoal::Reveal => write!(fmt, "Reveal"),
            DomainGoal::ObjectSafe(n) => write!(fmt, "ObjectSafe({:?})", n),
        }
    }
}

impl<I: Interner> Debug for EqGoal<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "({:?} = {:?})", self.a, self.b)
    }
}

impl<I: Interner> Debug for SubtypeGoal<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "({:?} <: {:?})", self.a, self.b)
    }
}

impl<T: HasInterner + Debug> Debug for Binders<T> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let Binders {
            ref binders,
            ref value,
        } = *self;
        write!(fmt, "for{:?} ", binders.debug())?;
        Debug::fmt(value, fmt)
    }
}

impl<I: Interner> Debug for ProgramClauseData<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{:?}", self.0)
    }
}

impl<I: Interner> Debug for Environment<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "Env({:?})", self.clauses)
    }
}

impl<I: Interner> Debug for CanonicalVarKinds<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_canonical_var_kinds(self, fmt)
            .unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}

impl<T: HasInterner + Display> Canonical<T> {
    /// Display the canonicalized item.
    pub fn display<'a>(&'a self, interner: &'a T::Interner) -> CanonicalDisplay<'a, T> {
        CanonicalDisplay {
            canonical: self,
            interner,
        }
    }
}

/// Helper struct for displaying canonicalized items.
pub struct CanonicalDisplay<'a, T: HasInterner> {
    canonical: &'a Canonical<T>,
    interner: &'a T::Interner,
}

impl<'a, T: HasInterner + Display> Display for CanonicalDisplay<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let Canonical { binders, value } = self.canonical;
        let interner = self.interner;
        let binders = binders.as_slice(interner);
        if binders.is_empty() {
            // Ordinarily, we try to print all binder levels, if they
            // are empty, but we can skip in this *particular* case
            // because we know that `Canonical` terms are never
            // supposed to contain free variables.  In other words,
            // all "bound variables" that appear inside the canonical
            // value must reference values that appear in `binders`.
            write!(f, "{}", value)?;
        } else {
            write!(f, "for<")?;

            for (i, pk) in binders.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, "?{}", pk.skip_kind())?;
            }

            write!(f, "> {{ {} }}", value)?;
        }

        Ok(())
    }
}

impl<I: Interner> Debug for GenericArgData<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            GenericArgData::Ty(t) => write!(fmt, "Ty({:?})", t),
            GenericArgData::Lifetime(l) => write!(fmt, "Lifetime({:?})", l),
            GenericArgData::Const(c) => write!(fmt, "Const({:?})", c),
        }
    }
}

impl<I: Interner> Debug for VariableKind<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            VariableKind::Ty(TyVariableKind::General) => write!(fmt, "type"),
            VariableKind::Ty(TyVariableKind::Integer) => write!(fmt, "integer type"),
            VariableKind::Ty(TyVariableKind::Float) => write!(fmt, "float type"),
            VariableKind::Lifetime => write!(fmt, "lifetime"),
            VariableKind::Const(ty) => write!(fmt, "const: {:?}", ty),
        }
    }
}

impl<I: Interner, T: Debug> Debug for WithKind<I, T> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let value = self.skip_kind();
        match &self.kind {
            VariableKind::Ty(TyVariableKind::General) => write!(fmt, "{:?} with kind type", value),
            VariableKind::Ty(TyVariableKind::Integer) => {
                write!(fmt, "{:?} with kind integer type", value)
            }
            VariableKind::Ty(TyVariableKind::Float) => {
                write!(fmt, "{:?} with kind float type", value)
            }
            VariableKind::Lifetime => write!(fmt, "{:?} with kind lifetime", value),
            VariableKind::Const(ty) => write!(fmt, "{:?} with kind {:?}", value, ty),
        }
    }
}

impl<I: Interner> Debug for Constraint<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Constraint::LifetimeOutlives(a, b) => write!(fmt, "{:?}: {:?}", a, b),
            Constraint::TypeOutlives(ty, lifetime) => write!(fmt, "{:?}: {:?}", ty, lifetime),
        }
    }
}

impl<I: Interner> Display for ConstrainedSubst<I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let ConstrainedSubst { subst, constraints } = self;

        write!(
            f,
            "substitution {}, lifetime constraints {:?}",
            subst, constraints,
        )
    }
}

impl<I: Interner> Substitution<I> {
    /// Displays the substitution in the form `< P0, .. Pn >`, or (if
    /// the substitution is empty) as an empty string.
    pub fn with_angle(&self, interner: &I) -> Angle<'_, GenericArg<I>> {
        Angle(self.as_slice(interner))
    }
}

impl<I: Interner> Debug for Substitution<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        Display::fmt(self, fmt)
    }
}

impl<I: Interner> Debug for Variances<I> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        I::debug_variances(self, fmt).unwrap_or_else(|| write!(fmt, "{:?}", self.interned))
    }
}
