//! Contains the definition for the "Rust IR" -- this is basically a "lowered"
//! version of the AST, roughly corresponding to [the HIR] in the Rust
//! compiler.

use chalk_ir::fold::shift::Shift;
use chalk_ir::tls;
use chalk_ir::{
    ApplicationTy, Binders, Identifier, ItemId, Lifetime, Parameter, ParameterKind, ProgramClause,
    ProjectionEq, ProjectionTy, QuantifiedWhereClause, TraitRef, Ty, WhereClause,
    InlineBound, QuantifiedInlineBound, TraitBound, ProjectionEqBound,
};
use chalk_ir::debug::Angle;
use std::collections::BTreeMap;
use std::fmt;

pub mod lowering;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    /// From type-name to item-id. Used during lowering only.
    crate type_ids: BTreeMap<Identifier, ItemId>,

    /// For each struct/trait:
    crate type_kinds: BTreeMap<ItemId, TypeKind>,

    /// For each struct:
    crate struct_data: BTreeMap<ItemId, StructDatum>,

    /// For each impl:
    crate impl_data: BTreeMap<ItemId, ImplDatum>,

    /// For each trait:
    crate trait_data: BTreeMap<ItemId, TraitDatum>,

    /// For each associated ty:
    crate associated_ty_data: BTreeMap<ItemId, AssociatedTyDatum>,

    /// For each default impl (automatically generated for auto traits):
    crate default_impl_data: Vec<DefaultImplDatum>,

    /// For each user-specified clause
    crate custom_clauses: Vec<ProgramClause>,

    /// Special types and traits.
    crate lang_items: BTreeMap<LangItem, ItemId>,
}

impl Program {
    /// Given a projection of an associated type, split the type parameters
    /// into those that come from the *trait* and those that come from the
    /// *associated type itself*. So e.g. if you have `(Iterator::Item)<F>`,
    /// this would return `([F], [])`, since `Iterator::Item` is not generic
    /// and hence doesn't have any type parameters itself.
    ///
    /// Used primarily for debugging output.
    crate fn split_projection<'p>(
        &self,
        projection: &'p ProjectionTy,
    ) -> (&AssociatedTyDatum, &'p [Parameter], &'p [Parameter]) {
        let ProjectionTy {
            associated_ty_id,
            ref parameters,
        } = *projection;
        let associated_ty_data = &self.associated_ty_data[&associated_ty_id];
        let trait_datum = &self.trait_data[&associated_ty_data.trait_id];
        let trait_num_params = trait_datum.binders.len();
        let split_point = parameters.len() - trait_num_params;
        let (other_params, trait_params) = parameters.split_at(split_point);
        (associated_ty_data, trait_params, other_params)
    }
}

impl tls::DebugContext for Program {
    fn debug_item_id(&self, item_id: ItemId, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let Some(k) = self.type_kinds.get(&item_id) {
            write!(fmt, "{}", k.name)
        } else if let Some(k) = self.associated_ty_data.get(&item_id) {
            write!(fmt, "({:?}::{})", k.trait_id, k.name)
        } else {
            fmt.debug_struct("InvalidItemId")
                .field("index", &item_id.index)
                .finish()
        }
    }

    fn debug_projection(
        &self,
        projection_ty: &ProjectionTy,
        fmt: &mut fmt::Formatter,
    ) -> Result<(), fmt::Error> {
        let (associated_ty_data, trait_params, other_params) =
            self.split_projection(projection_ty);
        write!(
            fmt,
            "<{:?} as {:?}{:?}>::{}{:?}",
            &trait_params[0],
            associated_ty_data.trait_id,
            Angle(&trait_params[1..]),
            associated_ty_data.name,
            Angle(&other_params)
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LangItem {
    DerefTrait,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImplDatum {
    crate binders: Binders<ImplDatumBound>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImplDatumBound {
    crate trait_ref: PolarizedTraitRef,
    crate where_clauses: Vec<QuantifiedWhereClause>,
    crate associated_ty_values: Vec<AssociatedTyValue>,
    crate specialization_priority: usize,
    crate impl_type: ImplType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ImplType {
    Local,
    External,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultImplDatum {
    crate binders: Binders<DefaultImplDatumBound>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultImplDatumBound {
    crate trait_ref: TraitRef,
    crate accessible_tys: Vec<Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructDatum {
    crate binders: Binders<StructDatumBound>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructDatumBound {
    crate self_ty: ApplicationTy,
    crate fields: Vec<Ty>,
    crate where_clauses: Vec<QuantifiedWhereClause>,
    crate flags: StructFlags,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructFlags {
    crate upstream: bool,
    crate fundamental: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitDatum {
    crate binders: Binders<TraitDatumBound>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitDatumBound {
    crate trait_ref: TraitRef,
    crate where_clauses: Vec<QuantifiedWhereClause>,
    crate flags: TraitFlags,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitFlags {
    crate auto: bool,
    crate marker: bool,
    crate upstream: bool,
    crate fundamental: bool,
    pub deref: bool,
}

crate trait IntoWhereClauses {
    type Output;

    fn into_where_clauses(&self, self_ty: Ty) -> Vec<Self::Output>;
}

impl IntoWhereClauses for InlineBound {
    type Output = WhereClause;

    /// Applies the `InlineBound` to `self_ty` and lowers to a
    /// [`chalk_ir::DomainGoal`].
    ///
    /// Because an `InlineBound` does not know anything about what it's binding,
    /// you must provide that type as `self_ty`.
    fn into_where_clauses(&self, self_ty: Ty) -> Vec<WhereClause> {
        match self {
            InlineBound::TraitBound(b) => b.into_where_clauses(self_ty),
            InlineBound::ProjectionEqBound(b) => b.into_where_clauses(self_ty),
        }
    }
}

impl IntoWhereClauses for QuantifiedInlineBound {
    type Output = QuantifiedWhereClause;

    fn into_where_clauses(&self, self_ty: Ty) -> Vec<QuantifiedWhereClause> {
        let self_ty = self_ty.shifted_in(self.binders.len());
        self.value
            .into_where_clauses(self_ty)
            .into_iter()
            .map(|wc| Binders {
                binders: self.binders.clone(),
                value: wc,
            }).collect()
    }
}

impl IntoWhereClauses for TraitBound {
    type Output = WhereClause;

    fn into_where_clauses(&self, self_ty: Ty) -> Vec<WhereClause> {
        let trait_ref = self.as_trait_ref(self_ty);
        vec![WhereClause::Implemented(trait_ref)]
    }
}

impl IntoWhereClauses for ProjectionEqBound {
    type Output = WhereClause;

    fn into_where_clauses(&self, self_ty: Ty) -> Vec<WhereClause> {
        let trait_ref = self.trait_bound.as_trait_ref(self_ty);

        let mut parameters = self.parameters.clone();
        parameters.extend(trait_ref.parameters.clone());

        vec![
            WhereClause::Implemented(trait_ref),
            WhereClause::ProjectionEq(ProjectionEq {
                projection: ProjectionTy {
                    associated_ty_id: self.associated_ty_id,
                    parameters: parameters,
                },
                ty: self.value.clone(),
            }),
        ]
    }
}

pub trait Anonymize {
    /// Utility function that converts from a list of generic parameters
    /// which *have* names (`ParameterKind<Identifier>`) to a list of
    /// "anonymous" generic parameters that just preserves their
    /// kinds (`ParameterKind<()>`). Often convenient in lowering.
    fn anonymize(&self) -> Vec<ParameterKind<()>>;
}

impl Anonymize for [ParameterKind<Identifier>] {
    fn anonymize(&self) -> Vec<ParameterKind<()>> {
        self.iter().map(|pk| pk.map(|_| ())).collect()
    }
}

pub trait ToParameter {
    /// Utility for converting a list of all the binders into scope
    /// into references to those binders. Simply pair the binders with
    /// the indices, and invoke `to_parameter()` on the `(binder,
    /// index)` pair. The result will be a reference to a bound
    /// variable of appropriate kind at the corresponding index.
    fn to_parameter(&self) -> Parameter;
}

impl<'a> ToParameter for (&'a ParameterKind<()>, usize) {
    fn to_parameter(&self) -> Parameter {
        let &(binder, index) = self;
        match *binder {
            ParameterKind::Lifetime(_) => ParameterKind::Lifetime(Lifetime::BoundVar(index)),
            ParameterKind::Ty(_) => ParameterKind::Ty(Ty::BoundVar(index)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssociatedTyDatum {
    /// The trait this associated type is defined in.
    crate trait_id: ItemId,

    /// The ID of this associated type
    crate id: ItemId,

    /// Name of this associated type.
    crate name: Identifier,

    /// Parameters on this associated type, beginning with those from the trait,
    /// but possibly including more.
    crate parameter_kinds: Vec<ParameterKind<Identifier>>,

    /// Bounds on the associated type itself.
    ///
    /// These must be proven by the implementer, for all possible parameters that
    /// would result in a well-formed projection.
    crate bounds: Vec<QuantifiedInlineBound>,

    /// Where clauses that must hold for the projection to be well-formed.
    crate where_clauses: Vec<QuantifiedWhereClause>,
}

impl AssociatedTyDatum {
    /// Returns the associated ty's bounds applied to the projection type, e.g.:
    ///
    /// ```notrust
    /// Implemented(<?0 as Foo>::Item<?1>: Sized)
    /// ```
    crate fn bounds_on_self(&self) -> Vec<QuantifiedWhereClause> {
        let parameters = self
            .parameter_kinds
            .anonymize()
            .iter()
            .zip(0..)
            .map(|p| p.to_parameter())
            .collect();
        let self_ty = Ty::Projection(ProjectionTy {
            associated_ty_id: self.id,
            parameters,
        });
        self.bounds
            .iter()
            .flat_map(|b| b.into_where_clauses(self_ty.clone()))
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssociatedTyValue {
    crate associated_ty_id: ItemId,

    // note: these binders are in addition to those from the impl
    crate value: Binders<AssociatedTyValueBound>,
}

struct_fold!(AssociatedTyValue {
    associated_ty_id,
    value,
});

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssociatedTyValueBound {
    /// Type that we normalize to. The X in `type Foo<'a> = X`.
    crate ty: Ty,
}

struct_fold!(AssociatedTyValueBound { ty });

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeKind {
    crate sort: TypeSort,
    crate name: Identifier,
    crate binders: Binders<()>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSort {
    Struct,
    Trait,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum PolarizedTraitRef {
    Positive(TraitRef),
    Negative(TraitRef),
}

enum_fold!(PolarizedTraitRef[] { Positive(a), Negative(a) });

impl PolarizedTraitRef {
    crate fn is_positive(&self) -> bool {
        match *self {
            PolarizedTraitRef::Positive(_) => true,
            PolarizedTraitRef::Negative(_) => false,
        }
    }

    crate fn trait_ref(&self) -> &TraitRef {
        match *self {
            PolarizedTraitRef::Positive(ref tr) | PolarizedTraitRef::Negative(ref tr) => tr,
        }
    }
}
