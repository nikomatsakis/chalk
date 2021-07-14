use chalk_ir::interner::HasInterner;
use chalk_ir::{
    self, AdtId, BoundVar, ClosureId, DebruijnIndex, FnDefId, GeneratorId, OpaqueTyId, TraitId,
    VariableKinds,
};
use chalk_ir::{cast::Cast, ForeignDefId, WithKind};
use chalk_parse::ast::*;
use chalk_solve::rust_ir::{AssociatedConstValueId, AssociatedTyValueId};
use std::collections::BTreeMap;

use crate::error::RustIrError;
use crate::interner::ChalkIr;
use crate::{Identifier as Ident, TypeKind};

pub type AdtIds = BTreeMap<Ident, chalk_ir::AdtId<ChalkIr>>;
pub type FnDefIds = BTreeMap<Ident, chalk_ir::FnDefId<ChalkIr>>;
pub type ClosureIds = BTreeMap<Ident, chalk_ir::ClosureId<ChalkIr>>;
pub type TraitIds = BTreeMap<Ident, chalk_ir::TraitId<ChalkIr>>;
pub type GeneratorIds = BTreeMap<Ident, chalk_ir::GeneratorId<ChalkIr>>;
pub type OpaqueTyIds = BTreeMap<Ident, chalk_ir::OpaqueTyId<ChalkIr>>;
pub type AdtKinds = BTreeMap<chalk_ir::AdtId<ChalkIr>, TypeKind>;
pub type FnDefKinds = BTreeMap<chalk_ir::FnDefId<ChalkIr>, TypeKind>;
pub type ClosureKinds = BTreeMap<chalk_ir::ClosureId<ChalkIr>, TypeKind>;
pub type TraitKinds = BTreeMap<chalk_ir::TraitId<ChalkIr>, TypeKind>;
pub type AutoTraits = BTreeMap<chalk_ir::TraitId<ChalkIr>, bool>;
pub type OpaqueTyVariableKinds = BTreeMap<chalk_ir::OpaqueTyId<ChalkIr>, TypeKind>;
pub type GeneratorKinds = BTreeMap<chalk_ir::GeneratorId<ChalkIr>, TypeKind>;
pub type AssociatedTyLookups = BTreeMap<(chalk_ir::TraitId<ChalkIr>, Ident), AssociatedTyLookup>;
pub type AssociatedConstLookups =
    BTreeMap<(chalk_ir::TraitId<ChalkIr>, Ident), AssociatedConstLookup>;
pub type AssociatedTyValueIds =
    BTreeMap<(chalk_ir::ImplId<ChalkIr>, Ident), AssociatedTyValueId<ChalkIr>>;
pub type AssociatedConstValueIds =
    BTreeMap<(chalk_ir::ImplId<ChalkIr>, Ident), AssociatedConstValueId<ChalkIr>>;
pub type ForeignIds = BTreeMap<Ident, chalk_ir::ForeignDefId<ChalkIr>>;

pub type ParameterMap = BTreeMap<Ident, chalk_ir::WithKind<ChalkIr, BoundVar>>;

pub type LowerResult<T> = Result<T, RustIrError>;

#[derive(Clone, Debug)]
pub struct Env<'k> {
    pub adt_ids: &'k AdtIds,
    pub adt_kinds: &'k AdtKinds,
    pub fn_def_ids: &'k FnDefIds,
    pub fn_def_kinds: &'k FnDefKinds,
    pub closure_ids: &'k ClosureIds,
    pub closure_kinds: &'k ClosureKinds,
    pub trait_ids: &'k TraitIds,
    pub trait_kinds: &'k TraitKinds,
    pub opaque_ty_ids: &'k OpaqueTyIds,
    pub opaque_ty_kinds: &'k OpaqueTyVariableKinds,
    pub associated_ty_lookups: &'k AssociatedTyLookups,
    pub associated_const_lookups: &'k AssociatedConstLookups,
    pub auto_traits: &'k AutoTraits,
    pub foreign_ty_ids: &'k ForeignIds,
    pub generator_ids: &'k GeneratorIds,
    pub generator_kinds: &'k GeneratorKinds,
    /// GenericArg identifiers are used as keys, therefore
    /// all identifiers in an environment must be unique (no shadowing).
    pub parameter_map: ParameterMap,
}

/// Information about an associated type **declaration** (i.e., an
/// `AssociatedTyDatum`). This information is gathered in the first
/// phase of creating the Rust IR and is then later used to lookup the
/// "id" of an associated type.
///
/// ```ignore
/// trait Foo {
///     type Bar<'a>; // <-- associated type declaration
///          // ----
///          // |
///          // addl_variable_kinds
/// }
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct AssociatedTyLookup {
    pub id: chalk_ir::AssocTypeId<ChalkIr>,
    pub addl_variable_kinds: Vec<chalk_ir::VariableKind<ChalkIr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct AssociatedConstLookup {
    pub id: chalk_ir::AssocConstId<ChalkIr>,
}

pub enum TypeLookup<'k> {
    Parameter(&'k WithKind<ChalkIr, BoundVar>),
    Adt(AdtId<ChalkIr>),
    FnDef(FnDefId<ChalkIr>),
    Closure(ClosureId<ChalkIr>),
    Opaque(OpaqueTyId<ChalkIr>),
    Foreign(ForeignDefId<ChalkIr>),
    Trait(TraitId<ChalkIr>),
    Generator(GeneratorId<ChalkIr>),
}

impl Env<'_> {
    pub fn interner(&self) -> &ChalkIr {
        &ChalkIr
    }

    pub fn lookup_generic_arg(
        &self,
        name: &Identifier,
    ) -> LowerResult<chalk_ir::GenericArg<ChalkIr>> {
        let interner = self.interner();

        macro_rules! tykind {
            ($k:expr, $tykind:ident, $id:expr) => {
                if $k.binders.len(interner) > 0 {
                    Err(RustIrError::IncorrectNumberOfTypeParameters {
                        identifier: name.clone(),
                        expected: $k.binders.len(interner),
                        actual: 0,
                    })
                } else {
                    Ok(
                        chalk_ir::TyKind::$tykind($id, chalk_ir::Substitution::empty(interner))
                            .intern(interner),
                    )
                    .cast(interner)
                }
            };
        }

        match self.lookup_type(name) {
            Ok(TypeLookup::Parameter(p)) => {
                let b = p.skip_kind();
                Ok(match &p.kind {
                    chalk_ir::VariableKind::Ty(_) => chalk_ir::TyKind::BoundVar(*b)
                        .intern(interner)
                        .cast(interner),
                    chalk_ir::VariableKind::Lifetime => chalk_ir::LifetimeData::BoundVar(*b)
                        .intern(interner)
                        .cast(interner),
                    chalk_ir::VariableKind::Const(ty) => {
                        b.to_const(interner, ty.clone()).cast(interner)
                    }
                })
            }
            Ok(TypeLookup::Adt(id)) => tykind!(self.adt_kind(id), Adt, id),
            Ok(TypeLookup::FnDef(id)) => tykind!(self.fn_def_kind(id), FnDef, id),
            Ok(TypeLookup::Closure(id)) => tykind!(self.closure_kind(id), Closure, id),
            Ok(TypeLookup::Generator(id)) => tykind!(self.generator_kind(id), Generator, id),
            Ok(TypeLookup::Opaque(id)) => Ok(chalk_ir::TyKind::Alias(chalk_ir::AliasTy::Opaque(
                chalk_ir::OpaqueTy {
                    opaque_ty_id: id,
                    substitution: chalk_ir::Substitution::empty(interner),
                },
            ))
            .intern(interner)
            .cast(interner)),
            Ok(TypeLookup::Foreign(id)) => Ok(chalk_ir::TyKind::Foreign(id)
                .intern(interner)
                .cast(interner)),
            Ok(TypeLookup::Trait(_)) => Err(RustIrError::NotStruct(name.clone())),
            Err(_) => Err(RustIrError::InvalidParameterName(name.clone())),
        }
    }

    pub fn lookup_type(&self, name: &Identifier) -> LowerResult<TypeLookup> {
        if let Some(id) = self.parameter_map.get(&name.str) {
            Ok(TypeLookup::Parameter(id))
        } else if let Some(id) = self.adt_ids.get(&name.str) {
            Ok(TypeLookup::Adt(*id))
        } else if let Some(id) = self.fn_def_ids.get(&name.str) {
            Ok(TypeLookup::FnDef(*id))
        } else if let Some(id) = self.closure_ids.get(&name.str) {
            Ok(TypeLookup::Closure(*id))
        } else if let Some(id) = self.opaque_ty_ids.get(&name.str) {
            Ok(TypeLookup::Opaque(*id))
        } else if let Some(id) = self.foreign_ty_ids.get(&name.str) {
            Ok(TypeLookup::Foreign(*id))
        } else if let Some(id) = self.trait_ids.get(&name.str) {
            Ok(TypeLookup::Trait(*id))
        } else if let Some(id) = self.generator_ids.get(&name.str) {
            Ok(TypeLookup::Generator(*id))
        } else {
            Err(RustIrError::NotStruct(name.clone()))
        }
    }

    pub fn auto_trait(&self, id: chalk_ir::TraitId<ChalkIr>) -> bool {
        self.auto_traits[&id]
    }

    pub fn lookup_trait(&self, name: &Identifier) -> LowerResult<TraitId<ChalkIr>> {
        if let Some(_) = self.parameter_map.get(&name.str) {
            Err(RustIrError::NotTrait(name.clone()))
        } else if let Some(_) = self.adt_ids.get(&name.str) {
            Err(RustIrError::NotTrait(name.clone()))
        } else if let Some(id) = self.trait_ids.get(&name.str) {
            Ok(*id)
        } else {
            Err(RustIrError::InvalidTraitName(name.clone()))
        }
    }

    pub fn trait_kind(&self, id: chalk_ir::TraitId<ChalkIr>) -> &TypeKind {
        &self.trait_kinds[&id]
    }

    pub fn adt_kind(&self, id: chalk_ir::AdtId<ChalkIr>) -> &TypeKind {
        &self.adt_kinds[&id]
    }

    pub fn fn_def_kind(&self, id: chalk_ir::FnDefId<ChalkIr>) -> &TypeKind {
        &self.fn_def_kinds[&id]
    }

    pub fn closure_kind(&self, id: chalk_ir::ClosureId<ChalkIr>) -> &TypeKind {
        &self.closure_kinds[&id]
    }

    pub fn opaque_kind(&self, id: chalk_ir::OpaqueTyId<ChalkIr>) -> &TypeKind {
        &self.opaque_ty_kinds[&id]
    }

    pub fn generator_kind(&self, id: chalk_ir::GeneratorId<ChalkIr>) -> &TypeKind {
        &self.generator_kinds[&id]
    }

    pub fn lookup_associated_ty(
        &self,
        trait_id: TraitId<ChalkIr>,
        ident: &Identifier,
    ) -> LowerResult<&AssociatedTyLookup> {
        self.associated_ty_lookups
            .get(&(trait_id, ident.str.clone()))
            .ok_or(RustIrError::MissingAssociatedType(ident.clone()))
    }

    pub fn lookup_associated_const(
        &self,
        trait_id: TraitId<ChalkIr>,
        ident: &Identifier,
    ) -> LowerResult<&AssociatedConstLookup> {
        self.associated_const_lookups
            .get(&(trait_id, ident.str.clone()))
            .ok_or(RustIrError::MissingAssociatedConst(ident.clone()))
    }

    /// Introduces new parameters, shifting the indices of existing
    /// parameters to accommodate them. The indices of the new binders
    /// will be assigned in order as they are iterated.
    pub fn introduce<I>(&self, binders: I) -> LowerResult<Self>
    where
        I: IntoIterator<Item = chalk_ir::WithKind<ChalkIr, Ident>>,
        I::IntoIter: ExactSizeIterator,
    {
        // As binders to introduce we recieve `ParameterKind<Ident>`,
        // which we need to transform into `(Ident, ParameterKind<BoundVar>)`,
        // because that is the key-value pair for ParameterMap.
        // `swap_inner` lets us do precisely that, replacing `Ident` inside
        // `ParameterKind<Ident>` with a `BoundVar` and returning both.
        let binders = binders.into_iter().enumerate().map(|(i, k)| {
            let (kind, name) = k.into();
            (
                name,
                chalk_ir::WithKind::new(kind, BoundVar::new(DebruijnIndex::INNERMOST, i)),
            )
        });
        let len = binders.len();

        // For things already in the parameter map, we take each existing key-value pair
        // `(Ident, ParameterKind<BoundVar>)` and shift in the inner `BoundVar`.
        let parameter_map: ParameterMap = self
            .parameter_map
            .iter()
            .map(|(k, v)| (k.clone(), v.map_ref(|b| b.shifted_in())))
            .chain(binders)
            .collect();
        if parameter_map.len() != self.parameter_map.len() + len {
            Err(RustIrError::DuplicateOrShadowedParameters)?;
        }
        Ok(Env {
            parameter_map,
            ..*self
        })
    }

    pub fn in_binders<I, T, OP>(&self, binders: I, op: OP) -> LowerResult<chalk_ir::Binders<T>>
    where
        I: IntoIterator<Item = chalk_ir::WithKind<ChalkIr, Ident>>,
        I::IntoIter: ExactSizeIterator,
        T: HasInterner<Interner = ChalkIr>,
        OP: FnOnce(&Self) -> LowerResult<T>,
    {
        let binders: Vec<_> = binders.into_iter().collect();
        let env = self.introduce(binders.iter().cloned())?;
        Ok(chalk_ir::Binders::new(
            VariableKinds::from_iter(self.interner(), binders.iter().map(|v| v.kind.clone())),
            op(&env)?,
        ))
    }
}
