//! Contains the definition for the "Rust IR" -- this is basically a "lowered"
//! version of the AST, roughly corresponding to [the HIR] in the Rust
//! compiler.

use chalk_derive::{Fold, HasInterner, Visit};
use chalk_ir::fold::shift::Shift;
use chalk_ir::interner::Interner;
use chalk_ir::{cast::Cast, AssocConstId, Const};
use chalk_ir::{
    try_break,
    visit::{ControlFlow, Visit},
    AdtId, AliasEq, AliasTy, AssocTypeId, Binders, DebruijnIndex, FnDefId, GenericArg, ImplId,
    OpaqueTyId, ProjectionTy, QuantifiedWhereClause, Substitution, ToGenericArg, TraitId, TraitRef,
    Ty, TyKind, VariableKind, WhereClause, WithKind,
};
use std::iter;

/// Identifier for an "associated type value" found in some impl.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssociatedTyValueId<I: Interner>(pub I::DefId);

chalk_ir::id_visit!(AssociatedTyValueId);
chalk_ir::id_fold!(AssociatedTyValueId);

/// Identifier for an "associated const value" found in some impl.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssociatedConstValueId<I: Interner>(pub I::DefId);

chalk_ir::id_visit!(AssociatedConstValueId);
chalk_ir::id_fold!(AssociatedConstValueId);

#[derive(Clone, Debug, PartialEq, Eq, Hash, Visit)]
pub struct ImplDatum<I: Interner> {
    pub polarity: Polarity,
    pub binders: Binders<ImplDatumBound<I>>,
    pub impl_type: ImplType,
    pub associated_ty_value_ids: Vec<AssociatedTyValueId<I>>,
    pub associated_const_value_ids: Vec<AssociatedConstValueId<I>>,
}

impl<I: Interner> ImplDatum<I> {
    pub fn is_positive(&self) -> bool {
        self.polarity.is_positive()
    }

    pub fn trait_id(&self) -> TraitId<I> {
        self.binders.skip_binders().trait_ref.trait_id
    }

    pub fn self_type_adt_id(&self, interner: &I) -> Option<AdtId<I>> {
        match self
            .binders
            .skip_binders()
            .trait_ref
            .self_type_parameter(interner)
            .kind(interner)
        {
            TyKind::Adt(id, _) => Some(*id),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, HasInterner, Fold, Visit)]
pub struct ImplDatumBound<I: Interner> {
    pub trait_ref: TraitRef<I>,
    pub where_clauses: Vec<QuantifiedWhereClause<I>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ImplType {
    Local,
    External,
}

chalk_ir::const_visit!(ImplType);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultImplDatum<I: Interner> {
    pub binders: Binders<DefaultImplDatumBound<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, HasInterner)]
pub struct DefaultImplDatumBound<I: Interner> {
    pub trait_ref: TraitRef<I>,
    pub accessible_tys: Vec<Ty<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Visit)]
pub struct AdtDatum<I: Interner> {
    pub binders: Binders<AdtDatumBound<I>>,
    pub id: AdtId<I>,
    pub flags: AdtFlags,
    pub kind: AdtKind,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum AdtKind {
    Struct,
    Enum,
    Union,
}

chalk_ir::const_visit!(AdtKind);

#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner, Visit)]
pub struct AdtDatumBound<I: Interner> {
    pub variants: Vec<AdtVariantDatum<I>>,
    pub where_clauses: Vec<QuantifiedWhereClause<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner, Visit)]
pub struct AdtVariantDatum<I: Interner> {
    pub fields: Vec<Ty<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AdtFlags {
    pub upstream: bool,
    pub fundamental: bool,
    pub phantom_data: bool,
}

chalk_ir::const_visit!(AdtFlags);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AdtRepr<I: Interner> {
    pub c: bool,
    pub packed: bool,
    pub int: Option<chalk_ir::Ty<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A rust intermediate represention (rust_ir) of a function definition/declaration.
/// For example, in the following rust code:
///
/// ```ignore
/// fn foo<T>() -> i32 where T: Eq;
/// ```
///
/// This would represent the declaration of `foo`.
///
/// Note this is distinct from a function pointer, which points to
/// a function with a given type signature, whereas this represents
/// a specific function definition.
pub struct FnDefDatum<I: Interner> {
    pub id: FnDefId<I>,
    pub sig: chalk_ir::FnSig<I>,
    pub binders: Binders<FnDefDatumBound<I>>,
}

/// Avoids visiting `I::FnAbi`
impl<I: Interner> Visit<I> for FnDefDatum<I> {
    fn visit_with<'i, B>(
        &self,
        visitor: &mut dyn chalk_ir::visit::Visitor<'i, I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>
    where
        I: 'i,
    {
        try_break!(self.id.visit_with(visitor, outer_binder));
        self.binders.visit_with(visitor, outer_binder)
    }
}

/// Represents the inputs and outputs on a `FnDefDatum`. This is split
/// from the where clauses, since these can contain bound lifetimes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner, Visit)]
pub struct FnDefInputsAndOutputDatum<I: Interner> {
    /// Types of the function's arguments
    /// ```ignore
    /// fn foo<T>(bar: i32, baz: T);
    ///                ^^^       ^
    /// ```
    ///
    pub argument_types: Vec<Ty<I>>,
    /// Return type of the function
    /// ```ignore
    /// fn foo<T>() -> i32;
    ///                ^^^
    /// ```
    pub return_type: Ty<I>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner, Visit)]
/// Represents the bounds on a `FnDefDatum`, including
/// the function definition's type signature and where clauses.
pub struct FnDefDatumBound<I: Interner> {
    /// Inputs and outputs defined on a function
    /// These are needed for late-bound regions in rustc. For example the
    /// lifetime `'a` in
    /// ```ignore
    /// fn foo<'a, T>(&'a T);
    ///        ^^
    /// ```
    /// Rustc doesn't pass in late-bound the regions in substs, but the inputs
    /// and outputs may use them. `where_clauses` don't need an extra set of
    /// `Binders`, since any lifetimes found in where clauses are not late-bound.
    ///
    /// For more information, see [this rustc-dev-guide chapter](https://rustc-dev-guide.rust-lang.org/early-late-bound.html).
    pub inputs_and_output: Binders<FnDefInputsAndOutputDatum<I>>,

    /// Where clauses defined on the function
    /// ```ignore
    /// fn foo<T>() where T: Eq;
    ///             ^^^^^^^^^^^
    /// ```
    pub where_clauses: Vec<QuantifiedWhereClause<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A rust intermediate representation (rust_ir) of a Trait Definition. For
/// example, given the following rust code:
///
/// ```compile_fail
/// use std::fmt::Debug;
///
/// trait Foo<T>
/// where
///     T: Debug,
/// {
///     type Bar<U>;
/// }
/// ```
///
/// This would represent the `trait Foo` declaration. Note that the details of
/// the trait members (e.g., the associated type declaration (`type Bar<U>`) are
/// not contained in this type, and are represented separately (e.g., in
/// [`AssociatedTyDatum`]).
///
/// Not to be confused with the rust_ir for a Trait Implementation, which is
/// represented by [`ImplDatum`]
///
/// [`ImplDatum`]: struct.ImplDatum.html
/// [`AssociatedTyDatum`]: struct.AssociatedTyDatum.html
#[derive(Visit)]
pub struct TraitDatum<I: Interner> {
    pub id: TraitId<I>,

    pub binders: Binders<TraitDatumBound<I>>,

    /// "Flags" indicate special kinds of traits, like auto traits.
    /// In Rust syntax these are represented in different ways, but in
    /// chalk we add annotations like `#[auto]`.
    pub flags: TraitFlags,

    pub associated_ty_ids: Vec<AssocTypeId<I>>,
    pub associated_const_ids: Vec<AssocConstId<I>>,

    /// If this is a well-known trait, which one? If `None`, this is a regular,
    /// user-defined trait.
    pub well_known: Option<WellKnownTrait>,
}

/// A list of the traits that are "well known" to chalk, which means that
/// the chalk-solve crate has special, hard-coded impls for them.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum WellKnownTrait {
    Sized,
    Copy,
    Clone,
    Drop,
    /// The trait `FnOnce<Args>` - the generic argument `Args` is always a tuple
    /// corresponding to the arguments of a function implementing this trait.
    /// E.g. `fn(u8, bool): FnOnce<(u8, bool)>`
    FnOnce,
    FnMut,
    Fn,
    Unsize,
    Unpin,
    CoerceUnsized,
    DiscriminantKind,
}

chalk_ir::const_visit!(WellKnownTrait);

impl<I: Interner> TraitDatum<I> {
    pub fn is_auto_trait(&self) -> bool {
        self.flags.auto
    }

    pub fn is_non_enumerable_trait(&self) -> bool {
        self.flags.non_enumerable
    }

    pub fn is_coinductive_trait(&self) -> bool {
        self.flags.coinductive
    }

    /// Gives access to the where clauses of the trait, quantified over the type parameters of the trait:
    ///
    /// ```ignore
    /// trait Foo<T> where T: Debug { }
    ///              ^^^^^^^^^^^^^^
    /// ```
    pub fn where_clauses(&self) -> Binders<&Vec<QuantifiedWhereClause<I>>> {
        self.binders.as_ref().map(|td| &td.where_clauses)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, HasInterner, Visit)]
pub struct TraitDatumBound<I: Interner> {
    /// Where clauses defined on the trait:
    ///
    /// ```ignore
    /// trait Foo<T> where T: Debug { }
    ///              ^^^^^^^^^^^^^^
    /// ```
    pub where_clauses: Vec<QuantifiedWhereClause<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitFlags {
    /// An "auto trait" is one that is "automatically implemented" for every
    /// struct, so long as no explicit impl is given.
    ///
    /// Examples are `Send` and `Sync`.
    pub auto: bool,

    pub marker: bool,

    /// Indicate that a trait is defined upstream (in a dependency), used during
    /// coherence checking.
    pub upstream: bool,

    /// A fundamental trait is a trait where adding an impl for an existing type
    /// is considered a breaking change. Examples of fundamental traits are the
    /// closure traits like `Fn` and `FnMut`.
    ///
    /// As of this writing (2020-03-27), fundamental traits are declared by the
    /// unstable `#[fundamental]` attribute in rustc, and hence cannot appear
    /// outside of the standard library.
    pub fundamental: bool,

    /// Indicates that chalk cannot list all of the implementations of the given
    /// trait, likely because it is a publicly exported trait in a library.
    ///
    /// Currently (2020-03-27) rustc and rust-analyzer mark all traits as
    /// non_enumerable, and in the future it may become the only option.
    pub non_enumerable: bool,

    pub coinductive: bool,
}

chalk_ir::const_visit!(TraitFlags);

/// An inline bound, e.g. `: Foo<K>` in `impl<K, T: Foo<K>> SomeType<T>`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub enum InlineBound<I: Interner> {
    TraitBound(TraitBound<I>),
    AliasEqBound(AliasEqBound<I>),
}

#[allow(type_alias_bounds)]
pub type QuantifiedInlineBound<I: Interner> = Binders<InlineBound<I>>;

pub trait IntoWhereClauses<I: Interner> {
    type Output;

    fn into_where_clauses(&self, interner: &I, self_ty: Ty<I>) -> Vec<Self::Output>;
}

impl<I: Interner> IntoWhereClauses<I> for InlineBound<I> {
    type Output = WhereClause<I>;

    /// Applies the `InlineBound` to `self_ty` and lowers to a
    /// [`chalk_ir::DomainGoal`].
    ///
    /// Because an `InlineBound` does not know anything about what it's binding,
    /// you must provide that type as `self_ty`.
    fn into_where_clauses(&self, interner: &I, self_ty: Ty<I>) -> Vec<WhereClause<I>> {
        match self {
            InlineBound::TraitBound(b) => b.into_where_clauses(interner, self_ty),
            InlineBound::AliasEqBound(b) => b.into_where_clauses(interner, self_ty),
        }
    }
}

impl<I: Interner> IntoWhereClauses<I> for QuantifiedInlineBound<I> {
    type Output = QuantifiedWhereClause<I>;

    fn into_where_clauses(&self, interner: &I, self_ty: Ty<I>) -> Vec<QuantifiedWhereClause<I>> {
        let self_ty = self_ty.shifted_in(interner);
        self.map_ref(|b| b.into_where_clauses(interner, self_ty))
            .into_iter()
            .collect()
    }
}

/// Represents a trait bound on e.g. a type or type parameter.
/// Does not know anything about what it's binding.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit)]
pub struct TraitBound<I: Interner> {
    pub trait_id: TraitId<I>,
    pub args_no_self: Vec<GenericArg<I>>,
}

impl<I: Interner> TraitBound<I> {
    fn into_where_clauses(&self, interner: &I, self_ty: Ty<I>) -> Vec<WhereClause<I>> {
        let trait_ref = self.as_trait_ref(interner, self_ty);
        vec![WhereClause::Implemented(trait_ref)]
    }

    pub fn as_trait_ref(&self, interner: &I, self_ty: Ty<I>) -> TraitRef<I> {
        TraitRef {
            trait_id: self.trait_id,
            substitution: Substitution::from_iter(
                interner,
                iter::once(self_ty.cast(interner)).chain(self.args_no_self.iter().cloned()),
            ),
        }
    }
}

/// Represents an alias equality bound on e.g. a type or type parameter.
/// Does not know anything about what it's binding.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit)]
pub struct AliasEqBound<I: Interner> {
    pub trait_bound: TraitBound<I>,
    pub associated_ty_id: AssocTypeId<I>,
    /// Does not include trait parameters.
    pub parameters: Vec<GenericArg<I>>,
    pub value: Ty<I>,
}

impl<I: Interner> AliasEqBound<I> {
    fn into_where_clauses(&self, interner: &I, self_ty: Ty<I>) -> Vec<WhereClause<I>> {
        let trait_ref = self.trait_bound.as_trait_ref(interner, self_ty);

        let substitution = Substitution::from_iter(
            interner,
            self.parameters
                .iter()
                .cloned()
                .chain(trait_ref.substitution.iter(interner).cloned()),
        );

        vec![
            WhereClause::Implemented(trait_ref),
            WhereClause::AliasEq(AliasEq {
                alias: AliasTy::Projection(ProjectionTy {
                    associated_ty_id: self.associated_ty_id,
                    substitution,
                }),
                ty: self.value.clone(),
            }),
        ]
    }
}

pub trait Anonymize<I: Interner> {
    /// Utility function that converts from a list of generic arguments
    /// which *have* associated data (`WithKind<I, T>`) to a list of
    /// "anonymous" generic parameters that just preserves their
    /// kinds (`VariableKind<I>`). Often convenient in lowering.
    fn anonymize(&self) -> Vec<VariableKind<I>>;
}

impl<I: Interner, T> Anonymize<I> for [WithKind<I, T>] {
    fn anonymize(&self) -> Vec<VariableKind<I>> {
        self.iter().map(|pk| pk.kind.clone()).collect()
    }
}

/// Represents an associated type declaration found inside of a trait:
///
/// ```notrust
/// trait Foo<P1..Pn> { // P0 is Self
///     type Bar<Pn..Pm>: [bounds]
///     where
///         [where_clauses];
/// }
/// ```
///
/// The meaning of each of these parts:
///
/// * The *parameters* `P0...Pm` are all in scope for this associated type.
/// * The *bounds* `bounds` are things that the impl must prove to be true.
/// * The *where clauses* `where_clauses` are things that the impl can *assume* to be true
///   (but which projectors must prove).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssociatedTyDatum<I: Interner> {
    /// The trait this associated type is defined in.
    pub trait_id: TraitId<I>,

    /// The ID of this associated type
    pub id: AssocTypeId<I>,

    /// Name of this associated type.
    pub name: I::Identifier,

    /// These binders represent the `P0...Pm` variables.  The binders
    /// are in the order `[Pn..Pm; P0..Pn]`. That is, the variables
    /// from `Bar` come first (corresponding to the de bruijn concept
    /// that "inner" binders are lower indices, although within a
    /// given binder we do not have an ordering).
    pub binders: Binders<AssociatedTyDatumBound<I>>,
}

// Manual implementation to avoid I::Identifier type.
impl<I: Interner> Visit<I> for AssociatedTyDatum<I> {
    fn visit_with<'i, B>(
        &self,
        visitor: &mut dyn chalk_ir::visit::Visitor<'i, I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>
    where
        I: 'i,
    {
        try_break!(self.trait_id.visit_with(visitor, outer_binder));
        try_break!(self.id.visit_with(visitor, outer_binder));
        self.binders.visit_with(visitor, outer_binder)
    }
}

/// Represents an associated const declaration found inside of a trait:
///
/// ```notrust
/// trait Foo<P1..Pn> { // P0 is Self
///     const Bar: [type] (= [const]);
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssociatedConstDatum<I: Interner> {
    /// The trait this associated const is defined in.
    pub trait_id: TraitId<I>,

    /// The ID of this associated const.
    pub id: AssocConstId<I>,

    /// Name of this associated const.
    pub name: I::Identifier,

    /// Type of this associated const.
    pub ty: Ty<I>,

    /// Value of this associated const with variables `P0...Pn`
    /// from the trait the assoc const is in.
    pub binders: Option<Binders<Const<I>>>,
}

// Manual implementation to avoid I::Identifier type.
impl<I: Interner> Visit<I> for AssociatedConstDatum<I> {
    fn visit_with<'i, B>(
        &self,
        visitor: &mut dyn chalk_ir::visit::Visitor<'i, I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>
    where
        I: 'i,
    {
        try_break!(self.trait_id.visit_with(visitor, outer_binder));
        try_break!(self.id.visit_with(visitor, outer_binder));
        try_break!(self.ty.visit_with(visitor, outer_binder));
        self.binders.visit_with(visitor, outer_binder)
    }
}

/// Encodes the parts of `AssociatedTyDatum` where the parameters
/// `P0..Pm` are in scope (`bounds` and `where_clauses`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct AssociatedTyDatumBound<I: Interner> {
    /// Bounds on the associated type itself.
    ///
    /// These must be proven by the implementer, for all possible parameters that
    /// would result in a well-formed projection.
    pub bounds: Vec<QuantifiedInlineBound<I>>,

    /// Where clauses that must hold for the projection to be well-formed.
    pub where_clauses: Vec<QuantifiedWhereClause<I>>,
}

impl<I: Interner> AssociatedTyDatum<I> {
    /// Returns the associated ty's bounds applied to the projection type, e.g.:
    ///
    /// ```notrust
    /// Implemented(<?0 as Foo>::Item<?1>: Sized)
    /// ```
    ///
    /// these quantified where clauses are in the scope of the
    /// `binders` field.
    pub fn bounds_on_self(&self, interner: &I) -> Vec<QuantifiedWhereClause<I>> {
        let (binders, assoc_ty_datum) = self.binders.as_ref().into();
        // Create a list `P0...Pn` of references to the binders in
        // scope for this associated type:
        let substitution = Substitution::from_iter(
            interner,
            binders
                .iter(interner)
                .enumerate()
                .map(|p| p.to_generic_arg(interner)),
        );

        // The self type will be `<P0 as Foo<P1..Pn>>::Item<Pn..Pm>` etc
        let self_ty = TyKind::Alias(AliasTy::Projection(ProjectionTy {
            associated_ty_id: self.id,
            substitution,
        }))
        .intern(interner);

        // Now use that as the self type for the bounds, transforming
        // something like `type Bar<Pn..Pm>: Debug` into
        //
        // ```
        // <P0 as Foo<P1..Pn>>::Item<Pn..Pm>: Debug
        // ```
        assoc_ty_datum
            .bounds
            .iter()
            .flat_map(|b| b.into_where_clauses(interner, self_ty.clone()))
            .collect()
    }
}

/// Represents the *value* of an associated type that is assigned
/// from within some impl.
///
/// ```ignore
/// impl Iterator for Foo {
///     type Item = XXX; // <-- represents this line!
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit)]
pub struct AssociatedTyValue<I: Interner> {
    /// Impl in which this associated type value is found.  You might
    /// need to look at this to find the generic parameters defined on
    /// the impl, for example.
    ///
    /// ```ignore
    /// impl Iterator for Foo { // <-- refers to this impl
    ///     type Item = XXX; // <-- (where this is self)
    /// }
    /// ```
    pub impl_id: ImplId<I>,

    /// Associated type being defined.
    ///
    /// ```ignore
    /// impl Iterator for Foo {
    ///     type Item = XXX; // <-- (where this is self)
    /// }
    /// ...
    /// trait Iterator {
    ///     type Item; // <-- refers to this declaration here!
    /// }
    /// ```
    pub associated_ty_id: AssocTypeId<I>,

    /// Additional binders declared on the associated type itself,
    /// beyond those from the impl. This would be empty for normal
    /// associated types, but non-empty for generic associated types.
    ///
    /// ```ignore
    /// impl<T> Iterable for Vec<T> {
    ///     type Iter<'a> = vec::Iter<'a, T>;
    ///           // ^^^^ refers to these generics here
    /// }
    /// ```
    pub value: Binders<AssociatedTyValueBound<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct AssociatedTyValueBound<I: Interner> {
    /// Type that we normalize to. The X in `type Foo<'a> = X`.
    pub ty: Ty<I>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit)]
pub struct AssociatedConstValue<I: Interner> {
    pub impl_id: ImplId<I>,
    pub associated_const_id: AssocConstId<I>,
    pub value: Binders<Const<I>>,
}

/// Represents the bounds for an `impl Trait` type.
///
/// ```ignore
/// opaque type T: A + B = HiddenTy;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit)]
pub struct OpaqueTyDatum<I: Interner> {
    /// The placeholder `!T` that corresponds to the opaque type `T`.
    pub opaque_ty_id: OpaqueTyId<I>,

    /// The type bound to when revealed.
    pub bound: Binders<OpaqueTyDatumBound<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner, Visit)]
pub struct OpaqueTyDatumBound<I: Interner> {
    /// Trait bounds for the opaque type. These are bounds that the hidden type must meet.
    pub bounds: Binders<Vec<QuantifiedWhereClause<I>>>,
    /// Where clauses that inform well-formedness conditions for the opaque type.
    /// These are conditions on the generic parameters of the opaque type which must be true
    /// for a reference to the opaque type to be well-formed.
    pub where_clauses: Binders<Vec<QuantifiedWhereClause<I>>>,
}

// The movability of a generator: whether a generator contains self-references,
// causing it to be !Unpin
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Movability {
    Static,
    Movable,
}
chalk_ir::copy_fold!(Movability);

/// Represents a generator type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner)]
pub struct GeneratorDatum<I: Interner> {
    // Can the generator be moved (is Unpin or not)
    pub movability: Movability,
    /// All of the nested types for this generator. The `Binder`
    /// represents the types and lifetimes that this generator is generic over -
    /// this behaves in the same way as `AdtDatum.binders`
    pub input_output: Binders<GeneratorInputOutputDatum<I>>,
}

/// The nested types for a generator. This always appears inside a `GeneratorDatum`
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner)]
pub struct GeneratorInputOutputDatum<I: Interner> {
    /// The generator resume type - a value of this type
    /// is supplied by the caller when resuming the generator.
    /// Currently, this plays no rule in goal resolution.
    pub resume_type: Ty<I>,
    /// The generator yield type - a value of this type
    /// is supplied by the generator during a yield.
    /// Currently, this plays no role in goal resolution.
    pub yield_type: Ty<I>,
    /// The generator return type - a value of this type
    /// is supplied by the generator when it returns.
    /// Currently, this plays no role in goal resolution
    pub return_type: Ty<I>,
    /// The upvars stored by the generator. These represent
    /// types captured from the generator's environment,
    /// and are stored across all yields. These types (along with the witness types)
    /// are considered 'constituent types' for the purposes of determining auto trait
    /// implementations - that its, a generator impls an auto trait A
    /// iff all of its constituent types implement A.
    pub upvars: Vec<Ty<I>>,
}

/// The generator witness data. Each `GeneratorId` has both a `GeneratorDatum`
/// and a `GeneratorWitnessDatum` - these represent two distinct types in Rust.
/// `GeneratorWitnessDatum` is logically 'inside' a generator - this only
/// matters when we treat the witness type as a 'constituent type for the
/// purposes of determining auto trait implementations.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner)]
pub struct GeneratorWitnessDatum<I: Interner> {
    /// This binder is identical to the `input_output` binder in `GeneratorWitness` -
    /// it binds the types and lifetimes that the generator is generic over.
    /// There is an additional binder inside `GeneratorWitnessExistential`, which
    /// is treated specially.
    pub inner_types: Binders<GeneratorWitnessExistential<I>>,
}

/// The generator witness types, together with existentially bound lifetimes.
/// Each 'witness type' represents a type stored inside the generator across
/// a yield. When a generator type is constructed, the precise region relationships
/// found in the generator body are erased. As a result, we are left with existential
/// lifetimes - each type is parameterized over *some* lifetimes, but we do not
/// know their precise values.
///
/// Unlike the binder in `GeneratorWitnessDatum`, this `Binder` never gets substituted
/// via an `Ty`. Instead, we handle this `Binders` specially when determining
/// auto trait impls. See `push_auto_trait_impls_generator_witness` for more details.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, HasInterner)]
pub struct GeneratorWitnessExistential<I: Interner> {
    pub types: Binders<Vec<Ty<I>>>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Polarity {
    Positive,
    Negative,
}

chalk_ir::const_visit!(Polarity);

impl Polarity {
    pub fn is_positive(&self) -> bool {
        match *self {
            Polarity::Positive => true,
            Polarity::Negative => false,
        }
    }
}

/// Indicates the "most permissive" Fn-like trait that the closure implements.
/// If the closure kind for a closure is FnMut, for example, then the closure
/// implements FnMut and FnOnce.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}
