mod env;
mod program_lowerer;

use chalk_ir::cast::{Cast, Caster};
use chalk_ir::{
    self, BoundVar, ClausePriority, DebruijnIndex, ImplId, QuantifiedWhereClauses, Substitution,
    TyVariableKind,
};
use chalk_parse::ast::*;
use chalk_solve::rust_ir::{self, IntoWhereClauses};
use program_lowerer::ProgramLowerer;
use std::collections::BTreeMap;
use string_cache::DefaultAtom as Atom;
use tracing::debug;

use crate::error::RustIrError;
use crate::interner::{ChalkFnAbi, ChalkIr};
use crate::program::Program as LoweredProgram;
use crate::{Identifier as Ident, TypeSort};
use env::*;

const SELF: &str = "Self";
const FIXME_SELF: &str = "__FIXME_SELF__";

trait LowerWithEnv {
    type Lowered;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered>;
}

pub trait Lower {
    type Lowered;

    fn lower(&self) -> Self::Lowered;
}

impl Lower for Program {
    type Lowered = LowerResult<LoweredProgram>;

    fn lower(&self) -> Self::Lowered {
        let mut lowerer = ProgramLowerer::default();

        // Make a vector mapping each thing in `items` to an id,
        // based just on its position:
        let raw_ids = self.items.iter().map(|_| lowerer.next_item_id()).collect();

        lowerer.extract_associated_types(self, &raw_ids)?;
        lowerer.extract_ids(self, &raw_ids)?;
        lowerer.lower(self, &raw_ids)
    }
}

trait LowerParameterMap {
    fn synthetic_parameters(&self) -> Option<chalk_ir::WithKind<ChalkIr, Ident>>;
    fn declared_parameters(&self) -> &[VariableKind];
    fn all_parameters(&self) -> Vec<chalk_ir::WithKind<ChalkIr, Ident>> {
        self.synthetic_parameters()
            .into_iter()
            .chain(self.declared_parameters().iter().map(|id| id.lower()))
            .collect()

        /* TODO: switch to this ordering, but adjust *all* the code to match

        self.declared_parameters()
            .iter()
            .map(|id| id.lower())
            .chain(self.synthetic_parameters()) // (*) see below
            .collect()
         */

        // (*) It is important that the declared parameters come
        // before the synthetic parameters in the ordering. This is
        // because of traits, when used as types, only have the first
        // N parameters in their kind (that is, they do not have Self).
        //
        // Note that if `Self` appears in the where-clauses etc, the
        // trait is not object-safe, and hence not supposed to be used
        // as an object. Actually the handling of object types is
        // probably just kind of messed up right now. That's ok.
    }
}

macro_rules! lower_param_map {
    ($type: ident, $synthetic: expr) => {
        impl LowerParameterMap for $type {
            fn synthetic_parameters(&self) -> Option<chalk_ir::WithKind<ChalkIr, Ident>> {
                $synthetic
            }
            fn declared_parameters(&self) -> &[VariableKind] {
                &self.variable_kinds
            }
        }
    };
}
lower_param_map!(AdtDefn, None);
lower_param_map!(FnDefn, None);
lower_param_map!(ClosureDefn, None);
lower_param_map!(Impl, None);
lower_param_map!(AssocTyDefn, None);
lower_param_map!(AssocTyValue, None);
lower_param_map!(Clause, None);
lower_param_map!(
    TraitDefn,
    Some(chalk_ir::WithKind::new(
        chalk_ir::VariableKind::Ty(TyVariableKind::General),
        Atom::from(SELF),
    ))
);

fn get_type_of_u32() -> chalk_ir::Ty<ChalkIr> {
    chalk_ir::TyKind::Scalar(chalk_ir::Scalar::Uint(chalk_ir::UintTy::U32)).intern(&ChalkIr)
}

impl Lower for VariableKind {
    type Lowered = chalk_ir::WithKind<ChalkIr, Ident>;
    fn lower(&self) -> Self::Lowered {
        let (kind, n) = match self {
            VariableKind::Ty(n) => (
                chalk_ir::VariableKind::Ty(chalk_ir::TyVariableKind::General),
                n,
            ),
            VariableKind::IntegerTy(n) => (
                chalk_ir::VariableKind::Ty(chalk_ir::TyVariableKind::Integer),
                n,
            ),
            VariableKind::FloatTy(n) => (
                chalk_ir::VariableKind::Ty(chalk_ir::TyVariableKind::Float),
                n,
            ),
            VariableKind::Lifetime(n) => (chalk_ir::VariableKind::Lifetime, n),
            VariableKind::Const(ref n) => (chalk_ir::VariableKind::Const(get_type_of_u32()), n),
        };

        chalk_ir::WithKind::new(kind, n.str.clone())
    }
}

impl LowerWithEnv for [QuantifiedWhereClause] {
    type Lowered = Vec<chalk_ir::QuantifiedWhereClause<ChalkIr>>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        self.iter()
            .flat_map(|wc| match wc.lower(env) {
                Ok(v) => v.into_iter().map(Ok).collect(),
                Err(e) => vec![Err(e)],
            })
            .collect()
    }
}

impl LowerWithEnv for WhereClause {
    type Lowered = Vec<chalk_ir::WhereClause<ChalkIr>>;

    /// Lower from an AST `where` clause to an internal IR.
    /// Some AST `where` clauses can lower to multiple ones, this is why we return a `Vec`.
    /// As for now, this is the only the case for `where T: Foo<Item = U>` which lowers to
    /// `Implemented(T: Foo)` and `ProjectionEq(<T as Foo>::Item = U)`.
    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        Ok(match self {
            WhereClause::Implemented { trait_ref } => {
                vec![chalk_ir::WhereClause::Implemented(trait_ref.lower(env)?)]
            }
            WhereClause::ProjectionEq { projection, ty } => vec![
                chalk_ir::WhereClause::AliasEq(chalk_ir::AliasEq {
                    alias: chalk_ir::AliasTy::Projection(projection.lower(env)?),
                    ty: ty.lower(env)?,
                }),
                chalk_ir::WhereClause::Implemented(projection.trait_ref.lower(env)?),
            ],
            WhereClause::LifetimeOutlives { a, b } => {
                vec![chalk_ir::WhereClause::LifetimeOutlives(
                    chalk_ir::LifetimeOutlives {
                        a: a.lower(env)?,
                        b: b.lower(env)?,
                    },
                )]
            }
            WhereClause::TypeOutlives { ty, lifetime } => {
                vec![chalk_ir::WhereClause::TypeOutlives(
                    chalk_ir::TypeOutlives {
                        ty: ty.lower(env)?,
                        lifetime: lifetime.lower(env)?,
                    },
                )]
            }
        })
    }
}

impl LowerWithEnv for QuantifiedWhereClause {
    type Lowered = Vec<chalk_ir::QuantifiedWhereClause<ChalkIr>>;

    /// Lower from an AST `where` clause to an internal IR.
    /// Some AST `where` clauses can lower to multiple ones, this is why we return a `Vec`.
    /// As for now, this is the only the case for `where T: Foo<Item = U>` which lowers to
    /// `Implemented(T: Foo)` and `ProjectionEq(<T as Foo>::Item = U)`.
    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let variable_kinds = self.variable_kinds.iter().map(|k| k.lower());
        let binders = env.in_binders(variable_kinds, |env| Ok(self.where_clause.lower(env)?))?;
        Ok(binders.into_iter().collect())
    }
}

impl LowerWithEnv for DomainGoal {
    type Lowered = Vec<chalk_ir::DomainGoal<ChalkIr>>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        Ok(match self {
            DomainGoal::Holds { where_clause } => where_clause
                .lower(env)?
                .into_iter()
                .casted(interner)
                .collect(),
            DomainGoal::Normalize { projection, ty } => {
                vec![chalk_ir::DomainGoal::Normalize(chalk_ir::Normalize {
                    alias: chalk_ir::AliasTy::Projection(projection.lower(env)?),
                    ty: ty.lower(env)?,
                })]
            }
            DomainGoal::TyWellFormed { ty } => vec![chalk_ir::DomainGoal::WellFormed(
                chalk_ir::WellFormed::Ty(ty.lower(env)?),
            )],
            DomainGoal::TraitRefWellFormed { trait_ref } => vec![chalk_ir::DomainGoal::WellFormed(
                chalk_ir::WellFormed::Trait(trait_ref.lower(env)?),
            )],
            DomainGoal::TyFromEnv { ty } => vec![chalk_ir::DomainGoal::FromEnv(
                chalk_ir::FromEnv::Ty(ty.lower(env)?),
            )],
            DomainGoal::TraitRefFromEnv { trait_ref } => vec![chalk_ir::DomainGoal::FromEnv(
                chalk_ir::FromEnv::Trait(trait_ref.lower(env)?),
            )],
            DomainGoal::IsLocal { ty } => vec![chalk_ir::DomainGoal::IsLocal(ty.lower(env)?)],
            DomainGoal::IsUpstream { ty } => vec![chalk_ir::DomainGoal::IsUpstream(ty.lower(env)?)],
            DomainGoal::IsFullyVisible { ty } => {
                vec![chalk_ir::DomainGoal::IsFullyVisible(ty.lower(env)?)]
            }
            DomainGoal::LocalImplAllowed { trait_ref } => {
                vec![chalk_ir::DomainGoal::LocalImplAllowed(
                    trait_ref.lower(env)?,
                )]
            }
            DomainGoal::Compatible => vec![chalk_ir::DomainGoal::Compatible],
            DomainGoal::DownstreamType { ty } => {
                vec![chalk_ir::DomainGoal::DownstreamType(ty.lower(env)?)]
            }
            DomainGoal::Reveal => vec![chalk_ir::DomainGoal::Reveal],
            DomainGoal::ObjectSafe { id } => {
                vec![chalk_ir::DomainGoal::ObjectSafe(env.lookup_trait(id)?)]
            }
        })
    }
}

impl LowerWithEnv for LeafGoal {
    type Lowered = chalk_ir::Goal<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        Ok(match self {
            LeafGoal::DomainGoal { goal } => {
                chalk_ir::Goal::all(interner, goal.lower(env)?.into_iter().casted(interner))
            }
            LeafGoal::UnifyGenericArgs { a, b } => chalk_ir::EqGoal {
                a: a.lower(env)?.cast(interner),
                b: b.lower(env)?.cast(interner),
            }
            .cast::<chalk_ir::Goal<ChalkIr>>(interner),
            LeafGoal::SubtypeGenericArgs { a, b } => chalk_ir::SubtypeGoal {
                a: a.lower(env)?,
                b: b.lower(env)?,
            }
            .cast::<chalk_ir::Goal<ChalkIr>>(interner),
        })
    }
}

impl LowerWithEnv for (&AdtDefn, chalk_ir::AdtId<ChalkIr>) {
    type Lowered = rust_ir::AdtDatum<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let (adt_defn, adt_id) = self;

        if adt_defn.flags.fundamental && adt_defn.all_parameters().len() < 1 {
            Err(RustIrError::InvalidFundamentalTypesParameters(
                adt_defn.name.clone(),
            ))?;
        }

        let binders = env.in_binders(adt_defn.all_parameters(), |env| {
            Ok(rust_ir::AdtDatumBound {
                variants: adt_defn
                    .variants
                    .iter()
                    .map(|v| {
                        let fields: LowerResult<_> =
                            v.fields.iter().map(|f| f.ty.lower(env)).collect();
                        Ok(rust_ir::AdtVariantDatum { fields: fields? })
                    })
                    .collect::<LowerResult<_>>()?,
                where_clauses: adt_defn.where_clauses.lower(env)?,
            })
        })?;

        let flags = rust_ir::AdtFlags {
            upstream: adt_defn.flags.upstream,
            fundamental: adt_defn.flags.fundamental,
            phantom_data: adt_defn.flags.phantom_data,
        };

        Ok(rust_ir::AdtDatum {
            id: *adt_id,
            binders,
            flags,
            kind: match adt_defn.flags.kind {
                AdtKind::Struct => rust_ir::AdtKind::Struct,
                AdtKind::Enum => rust_ir::AdtKind::Enum,
                AdtKind::Union => rust_ir::AdtKind::Union,
            },
        })
    }
}

impl LowerWithEnv for AdtRepr {
    type Lowered = rust_ir::AdtRepr<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        Ok(rust_ir::AdtRepr {
            c: self.c,
            packed: self.packed,
            int: self.int.as_ref().map(|i| i.lower(env)).transpose()?,
        })
    }
}

impl LowerWithEnv for (&FnDefn, chalk_ir::FnDefId<ChalkIr>) {
    type Lowered = rust_ir::FnDefDatum<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let (fn_defn, fn_def_id) = self;

        let binders = env.in_binders(fn_defn.all_parameters(), |env| {
            let where_clauses = fn_defn.where_clauses.lower(env)?;

            let inputs_and_output = env.in_binders(vec![], |env| {
                let args: LowerResult<_> = fn_defn
                    .argument_types
                    .iter()
                    .map(|t| t.lower(env))
                    .collect();
                let return_type = fn_defn.return_type.lower(env)?;
                Ok(rust_ir::FnDefInputsAndOutputDatum {
                    argument_types: args?,
                    return_type,
                })
            })?;
            Ok(rust_ir::FnDefDatumBound {
                inputs_and_output,
                where_clauses,
            })
        })?;

        Ok(rust_ir::FnDefDatum {
            id: *fn_def_id,
            sig: fn_defn.sig.lower()?,
            binders,
        })
    }
}

impl Lower for FnSig {
    type Lowered = LowerResult<chalk_ir::FnSig<ChalkIr>>;

    fn lower(&self) -> Self::Lowered {
        Ok(chalk_ir::FnSig {
            abi: self.abi.lower()?,
            safety: self.safety.lower(),
            variadic: self.variadic,
        })
    }
}

impl Lower for FnAbi {
    type Lowered = LowerResult<ChalkFnAbi>;
    fn lower(&self) -> Self::Lowered {
        match self.0.as_ref() {
            "Rust" => Ok(ChalkFnAbi::Rust),
            "C" => Ok(ChalkFnAbi::C),
            _ => Err(RustIrError::InvalidExternAbi(self.0.clone())),
        }
    }
}

impl LowerWithEnv for ClosureDefn {
    type Lowered = (
        rust_ir::ClosureKind,
        chalk_ir::Binders<rust_ir::FnDefInputsAndOutputDatum<ChalkIr>>,
    );

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let inputs_and_output = env.in_binders(self.all_parameters(), |env| {
            let args: LowerResult<_> = self.argument_types.iter().map(|t| t.lower(env)).collect();
            let return_type = self.return_type.lower(env)?;
            Ok(rust_ir::FnDefInputsAndOutputDatum {
                argument_types: args?,
                return_type,
            })
        })?;

        Ok((self.kind.lower(), inputs_and_output))
    }
}

impl Lower for ClosureKind {
    type Lowered = rust_ir::ClosureKind;

    fn lower(&self) -> Self::Lowered {
        match self {
            ClosureKind::Fn => rust_ir::ClosureKind::Fn,
            ClosureKind::FnMut => rust_ir::ClosureKind::FnMut,
            ClosureKind::FnOnce => rust_ir::ClosureKind::FnOnce,
        }
    }
}

impl LowerWithEnv for TraitRef {
    type Lowered = chalk_ir::TraitRef<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        let without_self = TraitBound {
            trait_name: self.trait_name.clone(),
            args_no_self: self.args.iter().cloned().skip(1).collect(),
        }
        .lower(env)?;

        let self_parameter = self.args[0].lower(env)?;
        Ok(without_self.as_trait_ref(interner, self_parameter.assert_ty_ref(interner).clone()))
    }
}

impl LowerWithEnv for TraitBound {
    type Lowered = rust_ir::TraitBound<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        let trait_id = env.lookup_trait(&self.trait_name)?;

        let k = env.trait_kind(trait_id);
        if k.sort != TypeSort::Trait {
            Err(RustIrError::NotTrait(self.trait_name.clone()))?;
        }

        let parameters = self
            .args_no_self
            .iter()
            .map(|a| a.lower(env))
            .collect::<LowerResult<Vec<_>>>()?;

        if parameters.len() != k.binders.len(interner) {
            Err(RustIrError::IncorrectNumberOfTypeParameters {
                identifier: self.trait_name.clone(),
                expected: k.binders.len(interner),
                actual: parameters.len(),
            })?;
        }

        for (binder, param) in k.binders.binders.iter(interner).zip(parameters.iter()) {
            if binder.kind() != param.kind() {
                Err(RustIrError::IncorrectTraitParameterKind {
                    identifier: self.trait_name.clone(),
                    expected: binder.kind(),
                    actual: param.kind(),
                })?;
            }
        }

        Ok(rust_ir::TraitBound {
            trait_id,
            args_no_self: parameters,
        })
    }
}

impl LowerWithEnv for AliasEqBound {
    type Lowered = rust_ir::AliasEqBound<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let trait_bound = self.trait_bound.lower(env)?;
        let lookup = env.lookup_associated_ty(trait_bound.trait_id, &self.name)?;
        let args: Vec<_> = self
            .args
            .iter()
            .map(|a| a.lower(env))
            .collect::<LowerResult<_>>()?;

        if args.len() != lookup.addl_variable_kinds.len() {
            Err(RustIrError::IncorrectNumberOfAssociatedTypeParameters {
                identifier: self.name.clone(),
                expected: lookup.addl_variable_kinds.len(),
                actual: args.len(),
            })?;
        }

        for (param, arg) in lookup.addl_variable_kinds.iter().zip(args.iter()) {
            if param.kind() != arg.kind() {
                Err(RustIrError::IncorrectAssociatedTypeParameterKind {
                    identifier: self.name.clone(),
                    expected: param.kind(),
                    actual: arg.kind(),
                })?;
            }
        }

        Ok(rust_ir::AliasEqBound {
            trait_bound,
            associated_ty_id: lookup.id,
            parameters: args,
            value: self.value.lower(env)?,
        })
    }
}

impl LowerWithEnv for InlineBound {
    type Lowered = rust_ir::InlineBound<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        Ok(match self {
            InlineBound::TraitBound(b) => rust_ir::InlineBound::TraitBound(b.lower(&env)?),
            InlineBound::AliasEqBound(b) => rust_ir::InlineBound::AliasEqBound(b.lower(&env)?),
        })
    }
}

impl LowerWithEnv for QuantifiedInlineBound {
    type Lowered = rust_ir::QuantifiedInlineBound<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let variable_kinds = self.variable_kinds.iter().map(|k| k.lower());
        env.in_binders(variable_kinds, |env| self.bound.lower(env))
    }
}

impl LowerWithEnv for [QuantifiedInlineBound] {
    type Lowered = Vec<rust_ir::QuantifiedInlineBound<ChalkIr>>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        fn trait_identifier(bound: &InlineBound) -> &Identifier {
            match bound {
                InlineBound::TraitBound(tb) => &tb.trait_name,
                InlineBound::AliasEqBound(ab) => &ab.trait_bound.trait_name,
            }
        }

        let mut regular_traits = Vec::new();
        let mut auto_traits = Vec::new();

        for b in self {
            let id = env.lookup_trait(trait_identifier(&b.bound))?;
            if env.auto_trait(id) {
                auto_traits.push((b, id))
            } else {
                regular_traits.push((b, id))
            }
        }

        auto_traits.sort_by_key(|b| b.1);

        regular_traits
            .iter()
            .chain(auto_traits.iter())
            .map(|(b, _)| b.lower(env))
            .collect()
    }
}

impl Lower for Polarity {
    type Lowered = rust_ir::Polarity;

    fn lower(&self) -> Self::Lowered {
        match self {
            Polarity::Positive => rust_ir::Polarity::Positive,
            Polarity::Negative => rust_ir::Polarity::Negative,
        }
    }
}

impl Lower for ImplType {
    type Lowered = rust_ir::ImplType;
    fn lower(&self) -> Self::Lowered {
        match self {
            ImplType::Local => rust_ir::ImplType::Local,
            ImplType::External => rust_ir::ImplType::External,
        }
    }
}

impl Lower for TraitFlags {
    type Lowered = rust_ir::TraitFlags;

    fn lower(&self) -> Self::Lowered {
        rust_ir::TraitFlags {
            auto: self.auto,
            marker: self.marker,
            upstream: self.upstream,
            fundamental: self.fundamental,
            non_enumerable: self.non_enumerable,
            coinductive: self.coinductive,
        }
    }
}

impl LowerWithEnv for ProjectionTy {
    type Lowered = chalk_ir::ProjectionTy<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let ProjectionTy {
            ref trait_ref,
            ref name,
            ref args,
        } = *self;
        let interner = env.interner();
        let chalk_ir::TraitRef {
            trait_id,
            substitution: trait_substitution,
        } = trait_ref.lower(env)?;
        let lookup = env.lookup_associated_ty(trait_id, name)?;
        let mut args: Vec<_> = args
            .iter()
            .map(|a| a.lower(env))
            .collect::<LowerResult<_>>()?;

        if args.len() != lookup.addl_variable_kinds.len() {
            Err(RustIrError::IncorrectNumberOfAssociatedTypeParameters {
                identifier: self.name.clone(),
                expected: lookup.addl_variable_kinds.len(),
                actual: args.len(),
            })?;
        }

        for (param, arg) in lookup.addl_variable_kinds.iter().zip(args.iter()) {
            if param.kind() != arg.kind() {
                Err(RustIrError::IncorrectAssociatedTypeParameterKind {
                    identifier: self.name.clone(),
                    expected: param.kind(),
                    actual: arg.kind(),
                })?;
            }
        }

        args.extend(trait_substitution.iter(interner).cloned());

        Ok(chalk_ir::ProjectionTy {
            associated_ty_id: lookup.id,
            substitution: chalk_ir::Substitution::from_iter(interner, args),
        })
    }
}

impl LowerWithEnv for Ty {
    type Lowered = chalk_ir::Ty<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        Ok(match self {
            Ty::Id { name } => {
                let parameter = env.lookup_generic_arg(&name)?;
                parameter.ty(interner).map(|ty| ty.clone()).ok_or_else(|| {
                    RustIrError::IncorrectParameterKind {
                        identifier: name.clone(),
                        expected: Kind::Ty,
                        actual: parameter.kind(),
                    }
                })?
            }
            Ty::Dyn {
                ref bounds,
                ref lifetime,
            } => chalk_ir::TyKind::Dyn(chalk_ir::DynTy {
                bounds: env.in_binders(
                    // FIXME: Figure out a proper name for this type parameter
                    Some(chalk_ir::WithKind::new(
                        chalk_ir::VariableKind::Ty(TyVariableKind::General),
                        Atom::from(FIXME_SELF),
                    )),
                    |env| {
                        Ok(QuantifiedWhereClauses::from_iter(
                            interner,
                            bounds.lower(env)?.iter().flat_map(|qil| {
                                qil.into_where_clauses(
                                    interner,
                                    chalk_ir::TyKind::BoundVar(BoundVar::new(
                                        DebruijnIndex::INNERMOST,
                                        0,
                                    ))
                                    .intern(interner),
                                )
                            }),
                        ))
                    },
                )?,
                lifetime: lifetime.lower(env)?,
            })
            .intern(interner),

            Ty::Apply { name, ref args } => {
                macro_rules! tykind {
                    ($k:expr, $tykind:ident, $id:expr) => {{
                        if $k.binders.len(interner) != args.len() {
                            Err(RustIrError::IncorrectNumberOfTypeParameters {
                                identifier: name.clone(),
                                expected: $k.binders.len(interner),
                                actual: args.len(),
                            })?;
                        }

                        let substitution = chalk_ir::Substitution::from_fallible(
                            interner,
                            args.iter().map(|t| Ok(t.lower(env)?)),
                        )?;

                        for (param, arg) in $k
                            .binders
                            .binders
                            .iter(interner)
                            .zip(substitution.iter(interner))
                        {
                            if param.kind() != arg.kind() {
                                Err(RustIrError::IncorrectParameterKind {
                                    identifier: name.clone(),
                                    expected: param.kind(),
                                    actual: arg.kind(),
                                })?;
                            }
                        }
                        chalk_ir::TyKind::$tykind($id, substitution).intern(interner)
                    }};
                }
                match env.lookup_type(&name)? {
                    TypeLookup::Parameter(_) => {
                        return Err(RustIrError::CannotApplyTypeParameter(name.clone()))
                    }
                    TypeLookup::Adt(id) => tykind!(env.adt_kind(id), Adt, id),
                    TypeLookup::FnDef(id) => tykind!(env.fn_def_kind(id), FnDef, id),
                    TypeLookup::Closure(id) => tykind!(env.closure_kind(id), Closure, id),
                    TypeLookup::Opaque(id) => tykind!(env.opaque_kind(id), OpaqueType, id),
                    TypeLookup::Generator(id) => tykind!(env.generator_kind(id), Generator, id),
                    TypeLookup::Foreign(_) | TypeLookup::Trait(_) => {
                        panic!("Unexpected apply type")
                    }
                }
            }

            Ty::Projection { ref proj } => {
                chalk_ir::TyKind::Alias(chalk_ir::AliasTy::Projection(proj.lower(env)?))
                    .intern(interner)
            }

            Ty::ForAll {
                lifetime_names,
                types,
                sig,
            } => {
                let quantified_env = env.introduce(lifetime_names.iter().map(|id| {
                    chalk_ir::WithKind::new(chalk_ir::VariableKind::Lifetime, id.str.clone())
                }))?;

                let mut lowered_tys = Vec::with_capacity(types.len());
                for ty in types {
                    lowered_tys.push(ty.lower(&quantified_env)?.cast(interner));
                }

                let function = chalk_ir::FnPointer {
                    num_binders: lifetime_names.len(),
                    substitution: chalk_ir::FnSubst(Substitution::from_iter(interner, lowered_tys)),
                    sig: sig.lower()?,
                };
                chalk_ir::TyKind::Function(function).intern(interner)
            }
            Ty::Tuple { ref types } => chalk_ir::TyKind::Tuple(
                types.len(),
                chalk_ir::Substitution::from_fallible(
                    interner,
                    types.iter().map(|t| Ok(t.lower(env)?)),
                )?,
            )
            .intern(interner),

            Ty::Scalar { ty } => chalk_ir::TyKind::Scalar(ty.lower()).intern(interner),

            Ty::Array { ty, len } => {
                chalk_ir::TyKind::Array(ty.lower(env)?, len.lower(env)?).intern(interner)
            }

            Ty::Slice { ty } => chalk_ir::TyKind::Slice(ty.lower(env)?).intern(interner),

            Ty::Raw { mutability, ty } => {
                chalk_ir::TyKind::Raw(mutability.lower(), ty.lower(env)?).intern(interner)
            }

            Ty::Ref {
                mutability,
                lifetime,
                ty,
            } => chalk_ir::TyKind::Ref(mutability.lower(), lifetime.lower(env)?, ty.lower(env)?)
                .intern(interner),

            Ty::Str => chalk_ir::TyKind::Str.intern(interner),

            Ty::Never => chalk_ir::TyKind::Never.intern(interner),
        })
    }
}

impl LowerWithEnv for Const {
    type Lowered = chalk_ir::Const<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        match self {
            Const::Id(name) => {
                let parameter = env.lookup_generic_arg(name)?;
                parameter
                    .constant(interner)
                    .ok_or_else(|| RustIrError::IncorrectParameterKind {
                        identifier: name.clone(),
                        expected: Kind::Const,
                        actual: parameter.kind(),
                    })
                    .map(|c| c.clone())
            }
            Const::Value(value) => Ok(chalk_ir::ConstData {
                ty: get_type_of_u32(),
                value: chalk_ir::ConstValue::Concrete(chalk_ir::ConcreteConst { interned: *value }),
            }
            .intern(interner)),
        }
    }
}

impl LowerWithEnv for GenericArg {
    type Lowered = chalk_ir::GenericArg<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        match self {
            GenericArg::Ty(ref t) => Ok(t.lower(env)?.cast(interner)),
            GenericArg::Lifetime(ref l) => Ok(l.lower(env)?.cast(interner)),
            GenericArg::Id(name) => env.lookup_generic_arg(&name),
            GenericArg::Const(c) => Ok(c.lower(env)?.cast(interner)),
        }
    }
}

impl LowerWithEnv for Lifetime {
    type Lowered = chalk_ir::Lifetime<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        match self {
            Lifetime::Id { name } => {
                let parameter = env.lookup_generic_arg(&name)?;
                parameter.lifetime(interner).copied().ok_or_else(|| {
                    RustIrError::IncorrectParameterKind {
                        identifier: name.clone(),
                        expected: Kind::Lifetime,
                        actual: parameter.kind(),
                    }
                })
            }
            Lifetime::Static => Ok(chalk_ir::Lifetime::new(
                interner,
                chalk_ir::LifetimeData::Static,
            )),
            Lifetime::Empty => Ok(chalk_ir::Lifetime::new(
                interner,
                chalk_ir::LifetimeData::Empty(chalk_ir::UniverseIndex { counter: 0 }),
            )),
            Lifetime::Erased => Ok(chalk_ir::Lifetime::new(
                interner,
                chalk_ir::LifetimeData::Erased,
            )),
        }
    }
}

impl LowerWithEnv
    for (
        &Impl,
        ImplId<ChalkIr>,
        &AssociatedTyValueIds,
        &AssociatedConstValueIds,
    )
{
    type Lowered = rust_ir::ImplDatum<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let (impl_, impl_id, associated_ty_value_ids, associated_const_value_ids) = self;

        let polarity = impl_.polarity.lower();
        let binders = env.in_binders(impl_.all_parameters(), |env| {
            let trait_ref = impl_.trait_ref.lower(env)?;
            debug!(?trait_ref);

            if !polarity.is_positive()
                && impl_
                    .assoc_item_values
                    .iter()
                    .any(|item| item.ty().is_some())
            {
                Err(RustIrError::NegativeImplAssociatedValues(
                    impl_.trait_ref.trait_name.clone(),
                ))?;
            }

            let where_clauses = impl_.where_clauses.lower(&env)?;
            debug!(where_clauses = ?trait_ref);
            Ok(rust_ir::ImplDatumBound {
                trait_ref,
                where_clauses,
            })
        })?;

        // lookup the ids for each of the "associated type values"
        // within the impl, which should have already assigned and
        // stored in the map
        let associated_ty_value_ids = impl_
            .assoc_item_values
            .iter()
            .filter_map(|item| item.ty())
            .map(|atv| associated_ty_value_ids[&(*impl_id, atv.name.str.clone())])
            .collect();

        debug!(?associated_ty_value_ids);

        let associated_const_value_ids = impl_
            .assoc_item_values
            .iter()
            .filter_map(|item| item.const_())
            .map(|acv| associated_const_value_ids[&(*impl_id, acv.name.str.clone())])
            .collect();

        debug!(?associated_const_value_ids);

        Ok(rust_ir::ImplDatum {
            polarity,
            binders,
            impl_type: impl_.impl_type.lower(),
            associated_ty_value_ids,
            associated_const_value_ids,
        })
    }
}

impl LowerWithEnv for Clause {
    type Lowered = Vec<chalk_ir::ProgramClause<ChalkIr>>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        let implications = env.in_binders(self.all_parameters(), |env| {
            let consequences: Vec<chalk_ir::DomainGoal<ChalkIr>> = self.consequence.lower(env)?;

            let conditions = chalk_ir::Goals::from_fallible(
                interner,
                // Subtle: in the SLG solver, we pop conditions from R to
                // L. To preserve the expected order (L to R), we must
                // therefore reverse.
                self.conditions.iter().map(|g| g.lower(env)).rev(),
            )?;

            let implications = consequences
                .into_iter()
                .map(|consequence| chalk_ir::ProgramClauseImplication {
                    consequence,
                    conditions: conditions.clone(),
                    constraints: chalk_ir::Constraints::empty(interner),
                    priority: ClausePriority::High,
                })
                .collect::<Vec<_>>();
            Ok(implications)
        })?;

        let clauses = implications
            .into_iter()
            .map(
                |implication: chalk_ir::Binders<chalk_ir::ProgramClauseImplication<ChalkIr>>| {
                    chalk_ir::ProgramClauseData(implication).intern(interner)
                },
            )
            .collect();
        Ok(clauses)
    }
}

impl LowerWithEnv for (&TraitDefn, chalk_ir::TraitId<ChalkIr>) {
    type Lowered = rust_ir::TraitDatum<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let (trait_defn, trait_id) = self;

        let all_parameters = trait_defn.all_parameters();
        let all_parameters_len = all_parameters.len();
        let binders = env.in_binders(all_parameters, |env| {
            if trait_defn.flags.auto {
                if all_parameters_len > 1 {
                    Err(RustIrError::AutoTraitParameters(trait_defn.name.clone()))?;
                }
                if !trait_defn.where_clauses.is_empty() {
                    Err(RustIrError::AutoTraitWhereClauses(trait_defn.name.clone()))?;
                }
            }

            Ok(rust_ir::TraitDatumBound {
                where_clauses: trait_defn.where_clauses.lower(env)?,
            })
        })?;

        let associated_ty_ids: Vec<_> = trait_defn
            .assoc_item_defns
            .iter()
            .filter_map(|item| item.ty())
            .map(|defn| env.lookup_associated_ty(*trait_id, &defn.name).unwrap().id)
            .collect();

        let associated_const_ids: Vec<_> = trait_defn
            .assoc_item_defns
            .iter()
            .filter_map(|item| item.const_())
            .map(|defn| {
                env.lookup_associated_const(*trait_id, &defn.name)
                    .unwrap()
                    .id
            })
            .collect();

        let trait_datum = rust_ir::TraitDatum {
            id: *trait_id,
            binders,
            flags: trait_defn.flags.lower(),
            associated_ty_ids,
            associated_const_ids,
            well_known: trait_defn.well_known.map(|def| def.lower()),
        };

        debug!(?trait_datum);

        Ok(trait_datum)
    }
}

pub fn lower_goal(goal: &Goal, program: &LoweredProgram) -> LowerResult<chalk_ir::Goal<ChalkIr>> {
    let interner = &ChalkIr;
    let associated_ty_lookups: BTreeMap<_, _> = program
        .associated_ty_data
        .iter()
        .map(|(&associated_ty_id, datum)| {
            let trait_datum = &program.trait_data[&datum.trait_id];
            let num_trait_params = trait_datum.binders.len(interner);
            let num_addl_params = datum.binders.len(interner) - num_trait_params;
            let addl_variable_kinds =
                datum.binders.binders.as_slice(interner)[..num_addl_params].to_owned();
            let lookup = AssociatedTyLookup {
                id: associated_ty_id,
                addl_variable_kinds,
            };
            ((datum.trait_id, datum.name.clone()), lookup)
        })
        .collect();
    let associated_const_lookups: BTreeMap<_, _> = program
        .associated_const_data
        .iter()
        .map(|(&associated_const_id, datum)| {
            let lookup = AssociatedConstLookup {
                id: associated_const_id,
            };
            ((datum.trait_id, datum.name.clone()), lookup)
        })
        .collect();

    let auto_traits = program
        .trait_data
        .iter()
        .map(|(&trait_id, datum)| (trait_id, datum.flags.auto))
        .collect();

    let env = Env {
        adt_ids: &program.adt_ids,
        fn_def_ids: &program.fn_def_ids,
        closure_ids: &program.closure_ids,
        trait_ids: &program.trait_ids,
        opaque_ty_ids: &program.opaque_ty_ids,
        generator_ids: &program.generator_ids,
        generator_kinds: &program.generator_kinds,
        adt_kinds: &program.adt_kinds,
        fn_def_kinds: &program.fn_def_kinds,
        closure_kinds: &program.closure_kinds,
        trait_kinds: &program.trait_kinds,
        opaque_ty_kinds: &program.opaque_ty_kinds,
        associated_ty_lookups: &associated_ty_lookups,
        associated_const_lookups: &associated_const_lookups,
        foreign_ty_ids: &program.foreign_ty_ids,
        parameter_map: BTreeMap::new(),
        auto_traits: &auto_traits,
    };

    goal.lower(&env)
}

impl LowerWithEnv for Goal {
    type Lowered = chalk_ir::Goal<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let interner = env.interner();
        match self {
            Goal::ForAll(ids, g) => (&**g, chalk_ir::QuantifierKind::ForAll, ids).lower(&env),
            Goal::Exists(ids, g) => (&**g, chalk_ir::QuantifierKind::Exists, ids).lower(&env),
            Goal::Implies(hyp, g) => {
                // We "elaborate" implied bounds by lowering goals like `T: Trait` and
                // `T: Trait<Assoc = U>` to `FromEnv(T: Trait)` and `FromEnv(T: Trait<Assoc = U>)`
                // in the assumptions of an `if` goal, e.g. `if (T: Trait) { ... }` lowers to
                // `if (FromEnv(T: Trait)) { ... /* this part is untouched */ ... }`.
                let where_clauses = hyp
                    .iter()
                    .flat_map(|clause| match clause.lower(env) {
                        Ok(v) => v.into_iter().map(Ok).collect(),
                        Err(e) => vec![Err(e)],
                    })
                    .map(|result| result.map(|h| h.into_from_env_clause(interner)));
                let where_clauses =
                    chalk_ir::ProgramClauses::from_fallible(interner, where_clauses);
                Ok(chalk_ir::GoalData::Implies(where_clauses?, g.lower(env)?).intern(interner))
            }
            Goal::And(g1, g2s) => {
                let goals = chalk_ir::Goals::from_fallible(
                    interner,
                    Some(g1).into_iter().chain(g2s).map(|g| g.lower(env)),
                )?;
                Ok(chalk_ir::GoalData::All(goals).intern(interner))
            }
            Goal::Not(g) => Ok(chalk_ir::GoalData::Not(g.lower(env)?).intern(interner)),
            Goal::Compatible(g) => Ok(g.lower(env)?.compatible(interner)),
            Goal::Leaf(leaf) => {
                // A where clause can lower to multiple leaf goals; wrap these in Goal::And.
                Ok(leaf.lower(env)?)
            }
        }
    }
}

impl LowerWithEnv for (&Goal, chalk_ir::QuantifierKind, &Vec<VariableKind>) {
    type Lowered = chalk_ir::Goal<ChalkIr>;

    fn lower(&self, env: &Env) -> LowerResult<Self::Lowered> {
        let (goal, quantifier_kind, variable_kinds) = self;

        let interner = env.interner();
        if variable_kinds.is_empty() {
            return goal.lower(env);
        }

        let variable_kinds = variable_kinds.iter().map(|k| k.lower());
        let subgoal = env.in_binders(variable_kinds, |env| goal.lower(env))?;
        Ok(chalk_ir::GoalData::Quantified(*quantifier_kind, subgoal).intern(interner))
    }
}

impl Lower for WellKnownTrait {
    type Lowered = rust_ir::WellKnownTrait;

    fn lower(&self) -> Self::Lowered {
        match self {
            WellKnownTrait::Sized => rust_ir::WellKnownTrait::Sized,
            WellKnownTrait::Copy => rust_ir::WellKnownTrait::Copy,
            WellKnownTrait::Clone => rust_ir::WellKnownTrait::Clone,
            WellKnownTrait::Drop => rust_ir::WellKnownTrait::Drop,
            WellKnownTrait::FnOnce => rust_ir::WellKnownTrait::FnOnce,
            WellKnownTrait::FnMut => rust_ir::WellKnownTrait::FnMut,
            WellKnownTrait::Fn => rust_ir::WellKnownTrait::Fn,
            WellKnownTrait::Unsize => rust_ir::WellKnownTrait::Unsize,
            WellKnownTrait::Unpin => rust_ir::WellKnownTrait::Unpin,
            WellKnownTrait::CoerceUnsized => rust_ir::WellKnownTrait::CoerceUnsized,
            WellKnownTrait::DiscriminantKind => rust_ir::WellKnownTrait::DiscriminantKind,
        }
    }
}

trait Kinded {
    fn kind(&self) -> Kind;
}

impl Kinded for chalk_ir::VariableKind<ChalkIr> {
    fn kind(&self) -> Kind {
        match self {
            chalk_ir::VariableKind::Ty(_) => Kind::Ty,
            chalk_ir::VariableKind::Lifetime => Kind::Lifetime,
            chalk_ir::VariableKind::Const(_) => Kind::Const,
        }
    }
}

impl Kinded for chalk_ir::GenericArg<ChalkIr> {
    fn kind(&self) -> Kind {
        let interner = &ChalkIr;
        match self.data(interner) {
            chalk_ir::GenericArgData::Ty(_) => Kind::Ty,
            chalk_ir::GenericArgData::Lifetime(_) => Kind::Lifetime,
            chalk_ir::GenericArgData::Const(_) => Kind::Const,
        }
    }
}

impl Lower for IntTy {
    type Lowered = chalk_ir::IntTy;

    fn lower(&self) -> Self::Lowered {
        match self {
            IntTy::I8 => chalk_ir::IntTy::I8,
            IntTy::I16 => chalk_ir::IntTy::I16,
            IntTy::I32 => chalk_ir::IntTy::I32,
            IntTy::I64 => chalk_ir::IntTy::I64,
            IntTy::I128 => chalk_ir::IntTy::I128,
            IntTy::Isize => chalk_ir::IntTy::Isize,
        }
    }
}

impl Lower for UintTy {
    type Lowered = chalk_ir::UintTy;

    fn lower(&self) -> Self::Lowered {
        match self {
            UintTy::U8 => chalk_ir::UintTy::U8,
            UintTy::U16 => chalk_ir::UintTy::U16,
            UintTy::U32 => chalk_ir::UintTy::U32,
            UintTy::U64 => chalk_ir::UintTy::U64,
            UintTy::U128 => chalk_ir::UintTy::U128,
            UintTy::Usize => chalk_ir::UintTy::Usize,
        }
    }
}

impl Lower for FloatTy {
    type Lowered = chalk_ir::FloatTy;

    fn lower(&self) -> Self::Lowered {
        match self {
            FloatTy::F32 => chalk_ir::FloatTy::F32,
            FloatTy::F64 => chalk_ir::FloatTy::F64,
        }
    }
}

impl Lower for ScalarType {
    type Lowered = chalk_ir::Scalar;

    fn lower(&self) -> Self::Lowered {
        match self {
            ScalarType::Int(int) => chalk_ir::Scalar::Int(int.lower()),
            ScalarType::Uint(uint) => chalk_ir::Scalar::Uint(uint.lower()),
            ScalarType::Float(float) => chalk_ir::Scalar::Float(float.lower()),
            ScalarType::Bool => chalk_ir::Scalar::Bool,
            ScalarType::Char => chalk_ir::Scalar::Char,
        }
    }
}

impl Lower for Mutability {
    type Lowered = chalk_ir::Mutability;
    fn lower(&self) -> Self::Lowered {
        match self {
            Mutability::Mut => chalk_ir::Mutability::Mut,
            Mutability::Not => chalk_ir::Mutability::Not,
        }
    }
}

impl Lower for Safety {
    type Lowered = chalk_ir::Safety;
    fn lower(&self) -> Self::Lowered {
        match self {
            Safety::Safe => chalk_ir::Safety::Safe,
            Safety::Unsafe => chalk_ir::Safety::Unsafe,
        }
    }
}

impl Lower for Movability {
    type Lowered = rust_ir::Movability;
    fn lower(&self) -> Self::Lowered {
        match self {
            Movability::Static => rust_ir::Movability::Static,
            Movability::Movable => rust_ir::Movability::Movable,
        }
    }
}
