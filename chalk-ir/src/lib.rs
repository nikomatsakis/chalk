//! Defines the IR for types and logical predicates.

#![deny(rust_2018_idioms)]
#![warn(missing_docs)]

// Allows macros to refer to this crate as `::chalk_ir`
extern crate self as chalk_ir;

use crate::cast::{Cast, CastTo, Caster};
use crate::fold::shift::Shift;
use crate::fold::{Fold, Folder, Subst, SuperFold};
use crate::visit::{ControlFlow, SuperVisit, Visit, VisitExt, Visitor};
use chalk_derive::{Fold, HasInterner, SuperVisit, Visit, Zip};
use std::marker::PhantomData;

pub use crate::debug::SeparatorTraitRef;
#[macro_use(bitflags)]
extern crate bitflags;
/// Uninhabited (empty) type, used in combination with `PhantomData`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Void {}

/// Many of our internal operations (e.g., unification) are an attempt
/// to perform some operation which may not complete.
pub type Fallible<T> = Result<T, NoSolution>;

/// A combination of `Fallible` and `Floundered`.
pub enum FallibleOrFloundered<T> {
    /// Success
    Ok(T),
    /// No solution. See `chalk_ir::NoSolution`.
    NoSolution,
    /// Floundered. See `chalk_ir::Floundered`.
    Floundered,
}

/// Indicates that the attempted operation has "no solution" -- i.e.,
/// cannot be performed.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NoSolution;

/// Indicates that the complete set of program clauses for this goal
/// cannot be enumerated.
pub struct Floundered;

macro_rules! impl_debugs {
    ($($id:ident), *) => {
        $(
            impl<I: Interner> std::fmt::Debug for $id<I> {
                fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                    write!(fmt, "{}({:?})", stringify!($id), self.0)
                }
            }
        )*
    };
}

#[macro_use]
pub mod zip;

#[macro_use]
pub mod fold;

#[macro_use]
pub mod visit;

pub mod cast;

pub mod interner;
use interner::{HasInterner, Interner};

pub mod could_match;
pub mod debug;

/// Variance
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Variance {
    /// a <: b
    Covariant,
    /// a == b
    Invariant,
    /// b <: a
    Contravariant,
}

impl Variance {
    /// `a.xform(b)` combines the variance of a context with the
    /// variance of a type with the following meaning. If we are in a
    /// context with variance `a`, and we encounter a type argument in
    /// a position with variance `b`, then `a.xform(b)` is the new
    /// variance with which the argument appears.
    ///
    /// Example 1:
    ///
    /// ```ignore
    /// *mut Vec<i32>
    /// ```
    ///
    /// Here, the "ambient" variance starts as covariant. `*mut T` is
    /// invariant with respect to `T`, so the variance in which the
    /// `Vec<i32>` appears is `Covariant.xform(Invariant)`, which
    /// yields `Invariant`. Now, the type `Vec<T>` is covariant with
    /// respect to its type argument `T`, and hence the variance of
    /// the `i32` here is `Invariant.xform(Covariant)`, which results
    /// (again) in `Invariant`.
    ///
    /// Example 2:
    ///
    /// ```ignore
    /// fn(*const Vec<i32>, *mut Vec<i32)
    /// ```
    ///
    /// The ambient variance is covariant. A `fn` type is
    /// contravariant with respect to its parameters, so the variance
    /// within which both pointer types appear is
    /// `Covariant.xform(Contravariant)`, or `Contravariant`. `*const
    /// T` is covariant with respect to `T`, so the variance within
    /// which the first `Vec<i32>` appears is
    /// `Contravariant.xform(Covariant)` or `Contravariant`. The same
    /// is true for its `i32` argument. In the `*mut T` case, the
    /// variance of `Vec<i32>` is `Contravariant.xform(Invariant)`,
    /// and hence the outermost type is `Invariant` with respect to
    /// `Vec<i32>` (and its `i32` argument).
    ///
    /// Source: Figure 1 of "Taming the Wildcards:
    /// Combining Definition- and Use-Site Variance" published in PLDI'11.
    /// (Doc from rustc)
    pub fn xform(self, other: Variance) -> Variance {
        match (self, other) {
            (Variance::Invariant, _) => Variance::Invariant,
            (_, Variance::Invariant) => Variance::Invariant,
            (_, Variance::Covariant) => self,
            (Variance::Covariant, Variance::Contravariant) => Variance::Contravariant,
            (Variance::Contravariant, Variance::Contravariant) => Variance::Covariant,
        }
    }

    /// Converts `Covariant` into `Contravariant` and vice-versa. `Invariant`
    /// stays the same.
    pub fn invert(self) -> Variance {
        match self {
            Variance::Invariant => Variance::Invariant,
            Variance::Covariant => Variance::Contravariant,
            Variance::Contravariant => Variance::Covariant,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
/// The set of assumptions we've made so far, and the current number of
/// universal (forall) quantifiers we're within.
pub struct Environment<I: Interner> {
    /// The clauses in the environment.
    pub clauses: ProgramClauses<I>,
}

impl<I: Interner> Copy for Environment<I> where I::InternedProgramClauses: Copy {}

impl<I: Interner> Environment<I> {
    /// Creates a new environment.
    pub fn new(interner: &I) -> Self {
        Environment {
            clauses: ProgramClauses::empty(interner),
        }
    }

    /// Adds (an iterator of) clauses to the environment.
    pub fn add_clauses<II>(&self, interner: &I, clauses: II) -> Self
    where
        II: IntoIterator<Item = ProgramClause<I>>,
    {
        let mut env = self.clone();
        env.clauses =
            ProgramClauses::from_iter(interner, env.clauses.iter(interner).cloned().chain(clauses));
        env
    }

    /// True if any of the clauses in the environment have a consequence of `Compatible`.
    /// Panics if the conditions or constraints of that clause are not empty.
    pub fn has_compatible_clause(&self, interner: &I) -> bool {
        self.clauses.as_slice(interner).iter().any(|c| {
            let ProgramClauseData(implication) = c.data(interner);
            match implication.skip_binders().consequence {
                DomainGoal::Compatible => {
                    // We currently don't generate `Compatible` with any conditions or constraints
                    // If this was needed, for whatever reason, then a third "yes, but must evaluate"
                    // return value would have to be added.
                    assert!(implication.skip_binders().conditions.is_empty(interner));
                    assert!(implication.skip_binders().constraints.is_empty(interner));
                    true
                }
                _ => false,
            }
        })
    }
}

/// A goal with an environment to solve it in.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit)]
#[allow(missing_docs)]
pub struct InEnvironment<G: HasInterner> {
    pub environment: Environment<G::Interner>,
    pub goal: G,
}

impl<G: HasInterner<Interner = I> + Copy, I: Interner> Copy for InEnvironment<G> where
    I::InternedProgramClauses: Copy
{
}

impl<G: HasInterner> InEnvironment<G> {
    /// Creates a new environment/goal pair.
    pub fn new(environment: &Environment<G::Interner>, goal: G) -> Self {
        InEnvironment {
            environment: environment.clone(),
            goal,
        }
    }

    /// Maps the goal without touching the environment.
    pub fn map<OP, H>(self, op: OP) -> InEnvironment<H>
    where
        OP: FnOnce(G) -> H,
        H: HasInterner<Interner = G::Interner>,
    {
        InEnvironment {
            environment: self.environment,
            goal: op(self.goal),
        }
    }
}

impl<G: HasInterner> HasInterner for InEnvironment<G> {
    type Interner = G::Interner;
}

/// Different signed int types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

/// Different unsigned int types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

/// Different kinds of float types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum FloatTy {
    F32,
    F64,
}

/// Types of scalar values.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum Scalar {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
}

/// Whether a function is safe or not.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Safety {
    /// Safe
    Safe,
    /// Unsafe
    Unsafe,
}

/// Whether a type is mutable or not.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mutability {
    /// Mutable
    Mut,
    /// Immutable
    Not,
}

/// An universe index is how a universally quantified parameter is
/// represented when it's binder is moved into the environment.
/// An example chain of transformations would be:
/// `forall<T> { Goal(T) }` (syntactical representation)
/// `forall { Goal(?0) }` (used a DeBruijn index)
/// `Goal(!U1)` (the quantifier was moved to the environment and replaced with a universe index)
/// See https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html#placeholders-and-universes for more.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniverseIndex {
    /// The counter for the universe index, starts with 0.
    pub counter: usize,
}

impl UniverseIndex {
    /// Root universe index (0).
    pub const ROOT: UniverseIndex = UniverseIndex { counter: 0 };

    /// Root universe index (0).
    pub fn root() -> UniverseIndex {
        Self::ROOT
    }

    /// Whether one universe can "see" another.
    pub fn can_see(self, ui: UniverseIndex) -> bool {
        self.counter >= ui.counter
    }

    /// Increases the index counter.
    pub fn next(self) -> UniverseIndex {
        UniverseIndex {
            counter: self.counter + 1,
        }
    }
}

/// Maps the universes found in the `u_canonicalize` result (the
/// "canonical" universes) to the universes found in the original
/// value (and vice versa). When used as a folder -- i.e., from
/// outside this module -- converts from "canonical" universes to the
/// original (but see the `UMapToCanonical` folder).
#[derive(Clone, Debug)]
pub struct UniverseMap {
    /// A reverse map -- for each universe Ux that appears in
    /// `quantified`, the corresponding universe in the original was
    /// `universes[x]`.
    pub universes: Vec<UniverseIndex>,
}

impl UniverseMap {
    /// Creates a new universe map.
    pub fn new() -> Self {
        UniverseMap {
            universes: vec![UniverseIndex::root()],
        }
    }

    /// Number of canonical universes.
    pub fn num_canonical_universes(&self) -> usize {
        self.universes.len()
    }
}

/// The id for an Abstract Data Type (i.e. structs, unions and enums).
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AdtId<I: Interner>(pub I::InternedAdtId);

/// The id of a trait definition; could be used to load the trait datum by
/// invoking the [`trait_datum`] method.
///
/// [`trait_datum`]: ../chalk_solve/trait.RustIrDatabase.html#tymethod.trait_datum
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TraitId<I: Interner>(pub I::DefId);

/// The id for an impl.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ImplId<I: Interner>(pub I::DefId);

/// Id for a specific clause.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId<I: Interner>(pub I::DefId);

/// The id for the associated type member of a trait. The details of the type
/// can be found by invoking the [`associated_ty_data`] method.
///
/// [`associated_ty_data`]: ../chalk_solve/trait.RustIrDatabase.html#tymethod.associated_ty_data
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssocTypeId<I: Interner>(pub I::DefId);

/// Id for the associated const of a trait.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssocConstId<I: Interner>(pub I::DefId);

/// Id for an opaque type.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OpaqueTyId<I: Interner>(pub I::DefId);

/// Function definition id.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FnDefId<I: Interner>(pub I::DefId);

/// Id for Rust closures.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClosureId<I: Interner>(pub I::DefId);

/// Id for Rust generators.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GeneratorId<I: Interner>(pub I::DefId);

/// Id for foreign types.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ForeignDefId<I: Interner>(pub I::DefId);

impl_debugs!(ImplId, ClauseId);

/// A Rust type. The actual type data is stored in `TyKind`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub struct Ty<I: Interner> {
    interned: I::InternedType,
}

impl<I: Interner> Ty<I> {
    /// Creates a type from `TyKind`.
    pub fn new(interner: &I, data: impl CastTo<TyKind<I>>) -> Self {
        let ty_kind = data.cast(&interner);
        Ty {
            interned: I::intern_ty(interner, ty_kind),
        }
    }

    /// Gets the interned type.
    pub fn interned(&self) -> &I::InternedType {
        &self.interned
    }

    /// Gets the underlying type data.
    pub fn data(&self, interner: &I) -> &TyData<I> {
        I::ty_data(interner, &self.interned)
    }

    /// Gets the underlying type kind.
    pub fn kind(&self, interner: &I) -> &TyKind<I> {
        &I::ty_data(interner, &self.interned).kind
    }

    /// Creates a `FromEnv` constraint using this type.
    pub fn from_env(&self) -> FromEnv<I> {
        FromEnv::Ty(self.clone())
    }

    /// Creates a WF-constraint for this type.
    pub fn well_formed(&self) -> WellFormed<I> {
        WellFormed::Ty(self.clone())
    }

    /// Creates a domain goal `FromEnv(T)` where `T` is this type.
    pub fn into_from_env_goal(self, interner: &I) -> DomainGoal<I> {
        self.from_env().cast(interner)
    }

    /// If this is a `TyKind::BoundVar(d)`, returns `Some(d)` else `None`.
    pub fn bound_var(&self, interner: &I) -> Option<BoundVar> {
        if let TyKind::BoundVar(bv) = self.kind(interner) {
            Some(*bv)
        } else {
            None
        }
    }

    /// If this is a `TyKind::InferenceVar(d)`, returns `Some(d)` else `None`.
    pub fn inference_var(&self, interner: &I) -> Option<InferenceVar> {
        if let TyKind::InferenceVar(depth, _) = self.kind(interner) {
            Some(*depth)
        } else {
            None
        }
    }

    /// Returns true if this is a `BoundVar` or an `InferenceVar` of `TyVariableKind::General`.
    pub fn is_general_var(&self, interner: &I, binders: &CanonicalVarKinds<I>) -> bool {
        match self.kind(interner) {
            TyKind::BoundVar(bv)
                if bv.debruijn == DebruijnIndex::INNERMOST
                    && binders.at(interner, bv.index).kind
                        == VariableKind::Ty(TyVariableKind::General) =>
            {
                true
            }
            TyKind::InferenceVar(_, TyVariableKind::General) => true,
            _ => false,
        }
    }

    /// Returns true if this is an `Alias`.
    pub fn is_alias(&self, interner: &I) -> bool {
        match self.kind(interner) {
            TyKind::Alias(..) => true,
            _ => false,
        }
    }

    /// Returns true if this is an `IntTy` or `UintTy`.
    pub fn is_integer(&self, interner: &I) -> bool {
        match self.kind(interner) {
            TyKind::Scalar(Scalar::Int(_)) | TyKind::Scalar(Scalar::Uint(_)) => true,
            _ => false,
        }
    }

    /// Returns true if this is a `FloatTy`.
    pub fn is_float(&self, interner: &I) -> bool {
        match self.kind(interner) {
            TyKind::Scalar(Scalar::Float(_)) => true,
            _ => false,
        }
    }

    /// Returns `Some(adt_id)` if this is an ADT, `None` otherwise
    pub fn adt_id(&self, interner: &I) -> Option<AdtId<I>> {
        match self.kind(interner) {
            TyKind::Adt(adt_id, _) => Some(*adt_id),
            _ => None,
        }
    }

    /// True if this type contains "bound" types/lifetimes, and hence
    /// needs to be shifted across binders. This is a very inefficient
    /// check, intended only for debug assertions, because I am lazy.
    pub fn needs_shift(&self, interner: &I) -> bool {
        self.has_free_vars(interner)
    }
}

/// Contains the data for a Ty
#[derive(Clone, PartialEq, Eq, Hash, HasInterner)]
pub struct TyData<I: Interner> {
    /// The kind
    pub kind: TyKind<I>,
    /// Type flags
    pub flags: TypeFlags,
}

bitflags! {
    /// Contains flags indicating various properties of a Ty
    pub struct TypeFlags : u16 {
        /// Does the type contain an InferenceVar
        const HAS_TY_INFER                = 1;
        /// Does the type contain a lifetime with an InferenceVar
        const HAS_RE_INFER                = 1 << 1;
        /// Does the type contain a ConstValue with an InferenceVar
        const HAS_CT_INFER                = 1 << 2;
        /// Does the type contain a Placeholder TyKind
        const HAS_TY_PLACEHOLDER          = 1 << 3;
        /// Does the type contain a lifetime with a Placeholder
        const HAS_RE_PLACEHOLDER          = 1 << 4;
        /// Does the type contain a ConstValue Placeholder
        const HAS_CT_PLACEHOLDER          = 1 << 5;
        /// True when the type has free lifetimes related to a local context
        const HAS_FREE_LOCAL_REGIONS      = 1 << 6;
        /// Does the type contain a projection of an associated type
        const HAS_TY_PROJECTION           = 1 << 7;
        /// Does the type contain an opaque type
        const HAS_TY_OPAQUE               = 1 << 8;
        /// Does the type contain an unevaluated const projection
        const HAS_CT_PROJECTION           = 1 << 9;
        /// Does the type contain an error
        const HAS_ERROR                   = 1 << 10;
        /// Does the type contain any free lifetimes
        const HAS_FREE_REGIONS            = 1 << 11;
        /// True when the type contains lifetimes that will be substituted when function is called
        const HAS_RE_LATE_BOUND           = 1 << 12;
        /// True when the type contains an erased lifetime
        const HAS_RE_ERASED               = 1 << 13;
        /// Does the type contain placeholders or inference variables that could be replaced later
        const STILL_FURTHER_SPECIALIZABLE = 1 << 14;

        /// True when the type contains free names local to a particular context
        const HAS_FREE_LOCAL_NAMES        = TypeFlags::HAS_TY_INFER.bits
                                          | TypeFlags::HAS_CT_INFER.bits
                                          | TypeFlags::HAS_TY_PLACEHOLDER.bits
                                          | TypeFlags::HAS_CT_PLACEHOLDER.bits
                                          | TypeFlags::HAS_FREE_LOCAL_REGIONS.bits;

        /// Does the type contain any form of projection
        const HAS_PROJECTION              = TypeFlags::HAS_TY_PROJECTION.bits
                                          | TypeFlags::HAS_TY_OPAQUE.bits
                                          | TypeFlags::HAS_CT_PROJECTION.bits;
    }
}
/// Type data, which holds the actual type information.
#[derive(Clone, PartialEq, Eq, Hash, HasInterner)]
pub enum TyKind<I: Interner> {
    /// Abstract data types, i.e., structs, unions, or enumerations.
    /// For example, a type like `Vec<T>`.
    Adt(AdtId<I>, Substitution<I>),

    /// an associated type like `Iterator::Item`; see `AssociatedType` for details
    AssociatedType(AssocTypeId<I>, Substitution<I>),

    /// a scalar type like `bool` or `u32`
    Scalar(Scalar),

    /// a tuple of the given arity
    Tuple(usize, Substitution<I>),

    /// an array type like `[T; N]`
    Array(Ty<I>, Const<I>),

    /// a slice type like `[T]`
    Slice(Ty<I>),

    /// a raw pointer type like `*const T` or `*mut T`
    Raw(Mutability, Ty<I>),

    /// a reference type like `&T` or `&mut T`
    Ref(Mutability, Lifetime<I>, Ty<I>),

    /// a placeholder for opaque types like `impl Trait`
    OpaqueType(OpaqueTyId<I>, Substitution<I>),

    /// a function definition
    FnDef(FnDefId<I>, Substitution<I>),

    /// the string primitive type
    Str,

    /// the never type `!`
    Never,

    /// A closure.
    Closure(ClosureId<I>, Substitution<I>),

    /// A generator.
    Generator(GeneratorId<I>, Substitution<I>),

    /// A generator witness.
    GeneratorWitness(GeneratorId<I>, Substitution<I>),

    /// foreign types
    Foreign(ForeignDefId<I>),

    /// This can be used to represent an error, e.g. during name resolution of a type.
    /// Chalk itself will not produce this, just pass it through when given.
    Error,

    /// instantiated from a universally quantified type, e.g., from
    /// `forall<T> { .. }`. Stands in as a representative of "some
    /// unknown type".
    Placeholder(PlaceholderIndex),

    /// A "dyn" type is a trait object type created via the "dyn Trait" syntax.
    /// In the chalk parser, the traits that the object represents is parsed as
    /// a QuantifiedInlineBound, and is then changed to a list of where clauses
    /// during lowering.
    ///
    /// See the `Opaque` variant for a discussion about the use of
    /// binders here.
    Dyn(DynTy<I>),

    /// An "alias" type represents some form of type alias, such as:
    /// - An associated type projection like `<T as Iterator>::Item`
    /// - `impl Trait` types
    /// - Named type aliases like `type Foo<X> = Vec<X>`
    Alias(AliasTy<I>),

    /// A function type such as `for<'a> fn(&'a u32)`.
    /// Note that "higher-ranked" types (starting with `for<>`) are either
    /// function types or dyn types, and do not appear otherwise in Rust
    /// surface syntax.
    Function(FnPointer<I>),

    /// References the binding at the given depth. The index is a [de
    /// Bruijn index], so it counts back through the in-scope binders.
    BoundVar(BoundVar),

    /// Inference variable defined in the current inference context.
    InferenceVar(InferenceVar, TyVariableKind),
}

impl<I: Interner> Copy for TyKind<I>
where
    I::InternedLifetime: Copy,
    I::InternedSubstitution: Copy,
    I::InternedVariableKinds: Copy,
    I::InternedQuantifiedWhereClauses: Copy,
    I::InternedType: Copy,
    I::InternedConst: Copy,
{
}

impl<I: Interner> TyKind<I> {
    /// Casts the type data to a type.
    pub fn intern(self, interner: &I) -> Ty<I> {
        Ty::new(interner, self)
    }

    /// Compute type flags for a TyKind
    pub fn compute_flags(&self, interner: &I) -> TypeFlags {
        match self {
            TyKind::Adt(_, substitution)
            | TyKind::AssociatedType(_, substitution)
            | TyKind::Tuple(_, substitution)
            | TyKind::Closure(_, substitution)
            | TyKind::Generator(_, substitution)
            | TyKind::GeneratorWitness(_, substitution)
            | TyKind::FnDef(_, substitution)
            | TyKind::OpaqueType(_, substitution) => substitution.compute_flags(interner),
            TyKind::Scalar(_) | TyKind::Str | TyKind::Never | TyKind::Foreign(_) => {
                TypeFlags::empty()
            }
            TyKind::Error => TypeFlags::HAS_ERROR,
            TyKind::Slice(ty) | TyKind::Raw(_, ty) => ty.data(interner).flags,
            TyKind::Ref(_, lifetime, ty) => {
                lifetime.compute_flags(interner) | ty.data(interner).flags
            }
            TyKind::Array(ty, const_ty) => {
                let flags = ty.data(interner).flags;
                let const_data = const_ty.data(interner);
                flags
                    | const_data.ty.data(interner).flags
                    | match const_data.value {
                        ConstValue::BoundVar(_) | ConstValue::Concrete(_) => TypeFlags::empty(),
                        ConstValue::InferenceVar(_) => {
                            TypeFlags::HAS_CT_INFER | TypeFlags::STILL_FURTHER_SPECIALIZABLE
                        }
                        ConstValue::Placeholder(_) => {
                            TypeFlags::HAS_CT_PLACEHOLDER | TypeFlags::STILL_FURTHER_SPECIALIZABLE
                        }
                        ConstValue::ConstProjection(_) => todo!(),
                    }
            }
            TyKind::Placeholder(_) => TypeFlags::HAS_TY_PLACEHOLDER,
            TyKind::Dyn(dyn_ty) => {
                let lifetime_flags = dyn_ty.lifetime.compute_flags(interner);
                let mut dyn_flags = TypeFlags::empty();
                for var_kind in dyn_ty.bounds.skip_binders().iter(interner) {
                    match &(var_kind.skip_binders()) {
                        WhereClause::Implemented(trait_ref) => {
                            dyn_flags |= trait_ref.substitution.compute_flags(interner)
                        }
                        WhereClause::AliasEq(alias_eq) => {
                            dyn_flags |= alias_eq.alias.compute_flags(interner);
                            dyn_flags |= alias_eq.ty.data(interner).flags;
                        }
                        WhereClause::LifetimeOutlives(lifetime_outlives) => {
                            dyn_flags |= lifetime_outlives.a.compute_flags(interner)
                                | lifetime_outlives.b.compute_flags(interner);
                        }
                        WhereClause::TypeOutlives(type_outlives) => {
                            dyn_flags |= type_outlives.ty.data(interner).flags;
                            dyn_flags |= type_outlives.lifetime.compute_flags(interner);
                        }
                    }
                }
                lifetime_flags | dyn_flags
            }
            TyKind::Alias(alias_ty) => alias_ty.compute_flags(&interner),
            TyKind::BoundVar(_) => TypeFlags::empty(),
            TyKind::InferenceVar(_, _) => TypeFlags::HAS_TY_INFER,
            TyKind::Function(fn_pointer) => fn_pointer.substitution.0.compute_flags(interner),
        }
    }
}

/// Identifies a particular bound variable within a binder.
/// Variables are identified by the combination of a [`DebruijnIndex`],
/// which identifies the *binder*, and an index within that binder.
///
/// Consider this case:
///
/// ```ignore
/// forall<'a, 'b> { forall<'c, 'd> { ... } }
/// ```
///
/// Within the `...` term:
///
/// * the variable `'a` have a debruijn index of 1 and index 0
/// * the variable `'b` have a debruijn index of 1 and index 1
/// * the variable `'c` have a debruijn index of 0 and index 0
/// * the variable `'d` have a debruijn index of 0 and index 1
///
/// The variables `'a` and `'b` both have debruijn index of 1 because,
/// counting out, they are the 2nd binder enclosing `...`. The indices
/// identify the location *within* that binder.
///
/// The variables `'c` and `'d` both have debruijn index of 0 because
/// they appear in the *innermost* binder enclosing the `...`. The
/// indices identify the location *within* that binder.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoundVar {
    /// Debruijn index, which identifies the binder.
    pub debruijn: DebruijnIndex,
    /// Index within the binder.
    pub index: usize,
}

impl BoundVar {
    /// Creates a new bound variable.
    pub fn new(debruijn: DebruijnIndex, index: usize) -> Self {
        Self { debruijn, index }
    }

    /// Casts the bound variable to a type.
    pub fn to_ty<I: Interner>(self, interner: &I) -> Ty<I> {
        TyKind::<I>::BoundVar(self).intern(interner)
    }

    /// Wrap the bound variable in a lifetime.
    pub fn to_lifetime<I: Interner>(self, interner: &I) -> Lifetime<I> {
        LifetimeData::<I>::BoundVar(self).intern(interner)
    }

    /// Wraps the bound variable in a constant.
    pub fn to_const<I: Interner>(self, interner: &I, ty: Ty<I>) -> Const<I> {
        ConstData {
            ty,
            value: ConstValue::<I>::BoundVar(self),
        }
        .intern(interner)
    }

    /// True if this variable is bound within the `amount` innermost binders.
    pub fn bound_within(self, outer_binder: DebruijnIndex) -> bool {
        self.debruijn.within(outer_binder)
    }

    /// Adjusts the debruijn index (see [`DebruijnIndex::shifted_in`]).
    #[must_use]
    pub fn shifted_in(self) -> Self {
        BoundVar::new(self.debruijn.shifted_in(), self.index)
    }

    /// Adjusts the debruijn index (see [`DebruijnIndex::shifted_in`]).
    #[must_use]
    pub fn shifted_in_from(self, outer_binder: DebruijnIndex) -> Self {
        BoundVar::new(self.debruijn.shifted_in_from(outer_binder), self.index)
    }

    /// Adjusts the debruijn index (see [`DebruijnIndex::shifted_in`]).
    #[must_use]
    pub fn shifted_out(self) -> Option<Self> {
        self.debruijn
            .shifted_out()
            .map(|db| BoundVar::new(db, self.index))
    }

    /// Adjusts the debruijn index (see [`DebruijnIndex::shifted_in`]).
    #[must_use]
    pub fn shifted_out_to(self, outer_binder: DebruijnIndex) -> Option<Self> {
        self.debruijn
            .shifted_out_to(outer_binder)
            .map(|db| BoundVar::new(db, self.index))
    }

    /// Return the index of the bound variable, but only if it is bound
    /// at the innermost binder. Otherwise, returns `None`.
    pub fn index_if_innermost(self) -> Option<usize> {
        self.index_if_bound_at(DebruijnIndex::INNERMOST)
    }

    /// Return the index of the bound variable, but only if it is bound
    /// at the innermost binder. Otherwise, returns `None`.
    pub fn index_if_bound_at(self, debruijn: DebruijnIndex) -> Option<usize> {
        if self.debruijn == debruijn {
            Some(self.index)
        } else {
            None
        }
    }
}

/// References the binder at the given depth. The index is a [de
/// Bruijn index], so it counts back through the in-scope binders,
/// with 0 being the innermost binder. This is used in impls and
/// the like. For example, if we had a rule like `for<T> { (T:
/// Clone) :- (T: Copy) }`, then `T` would be represented as a
/// `BoundVar(0)` (as the `for` is the innermost binder).
///
/// [de Bruijn index]: https://en.wikipedia.org/wiki/De_Bruijn_index
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DebruijnIndex {
    depth: u32,
}

impl DebruijnIndex {
    /// Innermost index.
    pub const INNERMOST: DebruijnIndex = DebruijnIndex { depth: 0 };
    /// One level higher than the innermost index.
    pub const ONE: DebruijnIndex = DebruijnIndex { depth: 1 };

    /// Creates a new de Bruijn index with a given depth.
    pub fn new(depth: u32) -> Self {
        DebruijnIndex { depth }
    }

    /// Depth of the De Bruijn index, counting from 0 starting with
    /// the innermost binder.
    pub fn depth(self) -> u32 {
        self.depth
    }

    /// True if the binder identified by this index is within the
    /// binder identified by the index `outer_binder`.
    ///
    /// # Example
    ///
    /// Imagine you have the following binders in scope
    ///
    /// ```ignore
    /// forall<a> forall<b> forall<c>
    /// ```
    ///
    /// then the Debruijn index for `c` would be `0`, the index for
    /// `b` would be 1, and so on. Now consider the following calls:
    ///
    /// * `c.within(a) = true`
    /// * `b.within(a) = true`
    /// * `a.within(a) = false`
    /// * `a.within(c) = false`
    pub fn within(self, outer_binder: DebruijnIndex) -> bool {
        self < outer_binder
    }

    /// Returns the resulting index when this value is moved into
    /// through one binder.
    #[must_use]
    pub fn shifted_in(self) -> DebruijnIndex {
        self.shifted_in_from(DebruijnIndex::ONE)
    }

    /// Update this index in place by shifting it "in" through
    /// `amount` number of binders.
    pub fn shift_in(&mut self) {
        *self = self.shifted_in();
    }

    /// Adds `outer_binder` levels to the `self` index. Intuitively, this
    /// shifts the `self` index, which was valid at the outer binder,
    /// so that it is valid at the innermost binder.
    ///
    /// Example: Assume that the following binders are in scope:
    ///
    /// ```ignore
    /// for<A> for<B> for<C> for<D>
    ///            ^ outer binder
    /// ```
    ///
    /// Assume further that the `outer_binder` argument is 2,
    /// which means that it is referring to the `for<B>` binder
    /// (since `D` would be the innermost binder).
    ///
    /// This means that `self` is relative to the binder `B` -- so
    /// if `self` is 0 (`INNERMOST`), then it refers to `B`,
    /// and if `self` is 1, then it refers to `A`.
    ///
    /// We will return as follows:
    ///
    /// * `0.shifted_in_from(2) = 2` -- i.e., `B`, when shifted in to the binding level `D`, has index 2
    /// * `1.shifted_in_from(2) = 3` -- i.e., `A`, when shifted in to the binding level `D`, has index 3
    /// * `2.shifted_in_from(1) = 3` -- here, we changed the `outer_binder`  to refer to `C`.
    ///   Therefore `2` (relative to `C`) refers to `A`, so the result is still 3 (since `A`, relative to the
    ///   innermost binder, has index 3).
    #[must_use]
    pub fn shifted_in_from(self, outer_binder: DebruijnIndex) -> DebruijnIndex {
        DebruijnIndex::new(self.depth() + outer_binder.depth())
    }

    /// Returns the resulting index when this value is moved out from
    /// `amount` number of new binders.
    #[must_use]
    pub fn shifted_out(self) -> Option<DebruijnIndex> {
        self.shifted_out_to(DebruijnIndex::ONE)
    }

    /// Update in place by shifting out from `amount` binders.
    pub fn shift_out(&mut self) {
        *self = self.shifted_out().unwrap();
    }

    /// Subtracts `outer_binder` levels from the `self` index. Intuitively, this
    /// shifts the `self` index, which was valid at the innermost
    /// binder, to one that is valid at the binder `outer_binder`.
    ///
    /// This will return `None` if the `self` index is internal to the
    /// outer binder (i.e., if `self < outer_binder`).
    ///
    /// Example: Assume that the following binders are in scope:
    ///
    /// ```ignore
    /// for<A> for<B> for<C> for<D>
    ///            ^ outer binder
    /// ```
    ///
    /// Assume further that the `outer_binder` argument is 2,
    /// which means that it is referring to the `for<B>` binder
    /// (since `D` would be the innermost binder).
    ///
    /// This means that the result is relative to the binder `B` -- so
    /// if `self` is 0 (`INNERMOST`), then it refers to `B`,
    /// and if `self` is 1, then it refers to `A`.
    ///
    /// We will return as follows:
    ///
    /// * `1.shifted_out_to(2) = None` -- i.e., the binder for `C` can't be named from the binding level `B`
    /// * `3.shifted_out_to(2) = Some(1)` -- i.e., `A`, when shifted out to the binding level `B`, has index 1
    pub fn shifted_out_to(self, outer_binder: DebruijnIndex) -> Option<DebruijnIndex> {
        if self.within(outer_binder) {
            None
        } else {
            Some(DebruijnIndex::new(self.depth() - outer_binder.depth()))
        }
    }
}

/// A "DynTy" represents a trait object (`dyn Trait`). Trait objects
/// are conceptually very related to an "existential type" of the form
/// `exists<T> { T: Trait }` (another example of such type is `impl Trait`).
/// `DynTy` represents the bounds on that type.
///
/// The "bounds" here represents the unknown self type. So, a type like
/// `dyn for<'a> Fn(&'a u32)` would be represented with two-levels of
/// binder, as "depicted" here:
///
/// ```notrust
/// exists<type> {
///    vec![
///        // A QuantifiedWhereClause:
///        forall<region> { ^1.0: Fn(&^0.0 u32) }
///    ]
/// }
/// ```
///
/// The outer `exists<type>` binder indicates that there exists
/// some type that meets the criteria within, but that type is not
/// known. It is referenced within the type using `^1.0`, indicating
/// a bound type with debruijn index 1 (i.e., skipping through one
/// level of binder).
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct DynTy<I: Interner> {
    /// The unknown self type.
    pub bounds: Binders<QuantifiedWhereClauses<I>>,
    /// Lifetime of the `DynTy`.
    pub lifetime: Lifetime<I>,
}

impl<I: Interner> Copy for DynTy<I>
where
    I::InternedLifetime: Copy,
    I::InternedQuantifiedWhereClauses: Copy,
    I::InternedVariableKinds: Copy,
{
}

/// A type, lifetime or constant whose value is being inferred.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InferenceVar {
    index: u32,
}

impl From<u32> for InferenceVar {
    fn from(index: u32) -> InferenceVar {
        InferenceVar { index }
    }
}

impl InferenceVar {
    /// Gets the underlying index value.
    pub fn index(self) -> u32 {
        self.index
    }

    /// Wraps the inference variable in a type.
    pub fn to_ty<I: Interner>(self, interner: &I, kind: TyVariableKind) -> Ty<I> {
        TyKind::<I>::InferenceVar(self, kind).intern(interner)
    }

    /// Wraps the inference variable in a lifetime.
    pub fn to_lifetime<I: Interner>(self, interner: &I) -> Lifetime<I> {
        LifetimeData::<I>::InferenceVar(self).intern(interner)
    }

    /// Wraps the inference variable in a constant.
    pub fn to_const<I: Interner>(self, interner: &I, ty: Ty<I>) -> Const<I> {
        ConstData {
            ty,
            value: ConstValue::<I>::InferenceVar(self),
        }
        .intern(interner)
    }
}

/// A function signature.
#[derive(Clone, Copy, PartialEq, Eq, Hash, HasInterner, Debug)]
#[allow(missing_docs)]
pub struct FnSig<I: Interner> {
    pub abi: I::FnAbi,
    pub safety: Safety,
    pub variadic: bool,
}
/// A wrapper for the substs on a Fn.
#[derive(Clone, PartialEq, Eq, Hash, HasInterner, Fold, Visit)]
pub struct FnSubst<I: Interner>(pub Substitution<I>);

impl<I: Interner> Copy for FnSubst<I> where I::InternedSubstitution: Copy {}

/// for<'a...'z> X -- all binders are instantiated at once,
/// and we use deBruijn indices within `self.ty`
#[derive(Clone, PartialEq, Eq, Hash, HasInterner)]
#[allow(missing_docs)]
pub struct FnPointer<I: Interner> {
    pub num_binders: usize,
    pub sig: FnSig<I>,
    pub substitution: FnSubst<I>,
}

impl<I: Interner> Copy for FnPointer<I> where I::InternedSubstitution: Copy {}

impl<I: Interner> FnPointer<I> {
    /// Represent the current `Fn` as if it was wrapped in `Binders`
    pub fn into_binders(self, interner: &I) -> Binders<FnSubst<I>> {
        Binders::new(
            VariableKinds::from_iter(
                interner,
                (0..self.num_binders).map(|_| VariableKind::Lifetime),
            ),
            self.substitution,
        )
    }

    /// Represent the current `Fn` as if it was wrapped in `Binders`
    pub fn as_binders(&self, interner: &I) -> Binders<&FnSubst<I>> {
        Binders::new(
            VariableKinds::from_iter(
                interner,
                (0..self.num_binders).map(|_| VariableKind::Lifetime),
            ),
            &self.substitution,
        )
    }
}

/// Constants.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub struct Const<I: Interner> {
    interned: I::InternedConst,
}

impl<I: Interner> Const<I> {
    /// Create a `Const` using something that can be cast to const data.
    pub fn new(interner: &I, data: impl CastTo<ConstData<I>>) -> Self {
        Const {
            interned: I::intern_const(interner, data.cast(interner)),
        }
    }

    /// Gets the interned constant.
    pub fn interned(&self) -> &I::InternedConst {
        &self.interned
    }

    /// Gets the constant data from the interner.
    pub fn data(&self, interner: &I) -> &ConstData<I> {
        I::const_data(interner, &self.interned)
    }

    /// If this is a `ConstData::BoundVar(d)`, returns `Some(d)` else `None`.
    pub fn bound_var(&self, interner: &I) -> Option<BoundVar> {
        if let ConstValue::BoundVar(bv) = &self.data(interner).value {
            Some(*bv)
        } else {
            None
        }
    }

    /// If this is a `ConstData::InferenceVar(d)`, returns `Some(d)` else `None`.
    pub fn inference_var(&self, interner: &I) -> Option<InferenceVar> {
        if let ConstValue::InferenceVar(iv) = &self.data(interner).value {
            Some(*iv)
        } else {
            None
        }
    }

    /// True if this const is a "bound" const, and hence
    /// needs to be shifted across binders. Meant for debug assertions.
    pub fn needs_shift(&self, interner: &I) -> bool {
        match &self.data(interner).value {
            ConstValue::BoundVar(_) => true,
            ConstValue::InferenceVar(_) => false,
            ConstValue::Placeholder(_) => false,
            ConstValue::Concrete(_) => false,
            ConstValue::ConstProjection(_) => todo!(),
        }
    }
}

/// Constant data, containing the constant's type and value.
#[derive(Clone, PartialEq, Eq, Hash, HasInterner)]
pub struct ConstData<I: Interner> {
    /// Type that holds the constant.
    pub ty: Ty<I>,
    /// The value of the constant.
    pub value: ConstValue<I>,
}

/// A constant value, not necessarily concrete.
#[derive(Clone, PartialEq, Eq, Hash, HasInterner)]
pub enum ConstValue<I: Interner> {
    /// Bound var (e.g. a parameter).
    BoundVar(BoundVar),
    /// Constant whose value is being inferred.
    InferenceVar(InferenceVar),
    /// Lifetime on some yet-unknown placeholder.
    Placeholder(PlaceholderIndex),
    /// Concrete constant value.
    Concrete(ConcreteConst<I>),
    /// Projection for associated constant.
    ConstProjection(ConstProjection<I>),
}

// impl<I: Interner> Copy for ConstValue<I> where I::InternedConcreteConst: Copy {}

impl<I: Interner> ConstData<I> {
    /// Wraps the constant data in a `Const`.
    pub fn intern(self, interner: &I) -> Const<I> {
        Const::new(interner, self)
    }
}

/// Concrete constant, whose value is known (as opposed to
/// inferred constants and placeholders).
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub struct ConcreteConst<I: Interner> {
    /// The interned constant.
    pub interned: I::InternedConcreteConst,
}

impl<I: Interner> ConcreteConst<I> {
    /// Checks whether two concrete constants are equal.
    pub fn const_eq(&self, ty: &Ty<I>, other: &ConcreteConst<I>, interner: &I) -> bool {
        interner.const_eq(&ty.interned, &self.interned, &other.interned)
    }
}

/// Projection for an associated constant.
#[derive(Clone, PartialEq, Eq, Hash, HasInterner)]
pub struct ConstProjection<I: Interner> {
    /// The id for the associated constant.
    pub associated_const_id: AssocConstId<I>,
    /// The substitution for the projection.
    pub substitution: Substitution<I>,
}

/// A Rust lifetime.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub struct Lifetime<I: Interner> {
    interned: I::InternedLifetime,
}

impl<I: Interner> Lifetime<I> {
    /// Create a lifetime from lifetime data
    /// (or something that can be cast to lifetime data).
    pub fn new(interner: &I, data: impl CastTo<LifetimeData<I>>) -> Self {
        Lifetime {
            interned: I::intern_lifetime(interner, data.cast(interner)),
        }
    }

    /// Gets the interned value.
    pub fn interned(&self) -> &I::InternedLifetime {
        &self.interned
    }

    /// Gets the lifetime data.
    pub fn data(&self, interner: &I) -> &LifetimeData<I> {
        I::lifetime_data(interner, &self.interned)
    }

    /// If this is a `Lifetime::BoundVar(d)`, returns `Some(d)` else `None`.
    pub fn bound_var(&self, interner: &I) -> Option<BoundVar> {
        if let LifetimeData::BoundVar(bv) = self.data(interner) {
            Some(*bv)
        } else {
            None
        }
    }

    /// If this is a `Lifetime::InferenceVar(d)`, returns `Some(d)` else `None`.
    pub fn inference_var(&self, interner: &I) -> Option<InferenceVar> {
        if let LifetimeData::InferenceVar(depth) = self.data(interner) {
            Some(*depth)
        } else {
            None
        }
    }

    /// True if this lifetime is a "bound" lifetime, and hence
    /// needs to be shifted across binders. Meant for debug assertions.
    pub fn needs_shift(&self, interner: &I) -> bool {
        match self.data(interner) {
            LifetimeData::BoundVar(_) => true,
            LifetimeData::InferenceVar(_) => false,
            LifetimeData::Placeholder(_) => false,
            LifetimeData::Static => false,
            LifetimeData::Empty(_) => false,
            LifetimeData::Erased => false,
            LifetimeData::Phantom(..) => unreachable!(),
        }
    }

    ///compute type flags for Lifetime
    fn compute_flags(&self, interner: &I) -> TypeFlags {
        match self.data(&interner) {
            LifetimeData::InferenceVar(_) => {
                TypeFlags::HAS_RE_INFER
                    | TypeFlags::HAS_FREE_LOCAL_REGIONS
                    | TypeFlags::HAS_FREE_REGIONS
            }
            LifetimeData::Placeholder(_) => {
                TypeFlags::HAS_RE_PLACEHOLDER
                    | TypeFlags::HAS_FREE_LOCAL_REGIONS
                    | TypeFlags::HAS_FREE_REGIONS
            }
            LifetimeData::Static | LifetimeData::Empty(_) => TypeFlags::HAS_FREE_REGIONS,
            LifetimeData::Phantom(_, _) => TypeFlags::empty(),
            LifetimeData::BoundVar(_) => TypeFlags::HAS_RE_LATE_BOUND,
            LifetimeData::Erased => TypeFlags::HAS_RE_ERASED,
        }
    }
}

/// Lifetime data, including what kind of lifetime it is and what it points to.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub enum LifetimeData<I: Interner> {
    /// See TyKind::BoundVar.
    BoundVar(BoundVar),
    /// Lifetime whose value is being inferred.
    InferenceVar(InferenceVar),
    /// Lifetime on some yet-unknown placeholder.
    Placeholder(PlaceholderIndex),
    /// Static lifetime
    Static,
    /// An empty lifetime: a lifetime shorter than any other lifetime in a
    /// universe with a lesser or equal index. The universe only non-zero in
    /// lexical region resolve in rustc, so chalk shouldn't ever see a non-zero
    /// index.
    Empty(UniverseIndex),
    /// An erased lifetime, used by rustc to improve caching when we doesn't
    /// care about lifetimes
    Erased,
    /// Lifetime on phantom data.
    Phantom(Void, PhantomData<I>),
}

impl<I: Interner> LifetimeData<I> {
    /// Wrap the lifetime data in a lifetime.
    pub fn intern(self, interner: &I) -> Lifetime<I> {
        Lifetime::new(interner, self)
    }
}

/// Index of an universally quantified parameter in the environment.
/// Two indexes are required, the one of the universe itself
/// and the relative index inside the universe.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlaceholderIndex {
    /// Index *of* the universe.
    pub ui: UniverseIndex,
    /// Index *in* the universe.
    pub idx: usize,
}

impl PlaceholderIndex {
    /// Wrap the placeholder instance in a lifetime.
    pub fn to_lifetime<I: Interner>(self, interner: &I) -> Lifetime<I> {
        LifetimeData::<I>::Placeholder(self).intern(interner)
    }

    /// Create an interned type.
    pub fn to_ty<I: Interner>(self, interner: &I) -> Ty<I> {
        TyKind::Placeholder(self).intern(interner)
    }

    /// Wrap the placeholder index in a constant.
    pub fn to_const<I: Interner>(self, interner: &I, ty: Ty<I>) -> Const<I> {
        ConstData {
            ty,
            value: ConstValue::Placeholder(self),
        }
        .intern(interner)
    }
}
/// Represents some extra knowledge we may have about the type variable.
/// ```ignore
/// let x: &[u32];
/// let i = 1;
/// x[i]
/// ```
/// In this example, `i` is known to be some type of integer. We can infer that
/// it is `usize` because that is the only integer type that slices have an
/// `Index` impl for. `i` would have a `TyVariableKind` of `Integer` to guide the
/// inference process.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum TyVariableKind {
    General,
    Integer,
    Float,
}

/// The "kind" of variable. Type, lifetime or constant.
#[derive(Clone, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum VariableKind<I: Interner> {
    Ty(TyVariableKind),
    Lifetime,
    Const(Ty<I>),
}

impl<I: Interner> interner::HasInterner for VariableKind<I> {
    type Interner = I;
}

impl<I: Interner> Copy for VariableKind<I> where I::InternedType: Copy {}

impl<I: Interner> VariableKind<I> {
    fn to_bound_variable(&self, interner: &I, bound_var: BoundVar) -> GenericArg<I> {
        match self {
            VariableKind::Ty(_) => {
                GenericArgData::Ty(TyKind::BoundVar(bound_var).intern(interner)).intern(interner)
            }
            VariableKind::Lifetime => {
                GenericArgData::Lifetime(LifetimeData::BoundVar(bound_var).intern(interner))
                    .intern(interner)
            }
            VariableKind::Const(ty) => GenericArgData::Const(
                ConstData {
                    ty: ty.clone(),
                    value: ConstValue::BoundVar(bound_var),
                }
                .intern(interner),
            )
            .intern(interner),
        }
    }
}

/// A generic argument, see `GenericArgData` for more information.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub struct GenericArg<I: Interner> {
    interned: I::InternedGenericArg,
}

impl<I: Interner> GenericArg<I> {
    /// Constructs a generic argument using `GenericArgData`.
    pub fn new(interner: &I, data: GenericArgData<I>) -> Self {
        let interned = I::intern_generic_arg(interner, data);
        GenericArg { interned }
    }

    /// Gets the interned value.
    pub fn interned(&self) -> &I::InternedGenericArg {
        &self.interned
    }

    /// Gets the underlying data.
    pub fn data(&self, interner: &I) -> &GenericArgData<I> {
        I::generic_arg_data(interner, &self.interned)
    }

    /// Asserts that this is a type argument.
    pub fn assert_ty_ref(&self, interner: &I) -> &Ty<I> {
        self.ty(interner).unwrap()
    }

    /// Asserts that this is a lifetime argument.
    pub fn assert_lifetime_ref(&self, interner: &I) -> &Lifetime<I> {
        self.lifetime(interner).unwrap()
    }

    /// Asserts that this is a constant argument.
    pub fn assert_const_ref(&self, interner: &I) -> &Const<I> {
        self.constant(interner).unwrap()
    }

    /// Checks whether the generic argument is a type.
    pub fn is_ty(&self, interner: &I) -> bool {
        match self.data(interner) {
            GenericArgData::Ty(_) => true,
            GenericArgData::Lifetime(_) => false,
            GenericArgData::Const(_) => false,
        }
    }

    /// Returns the type if it is one, `None` otherwise.
    pub fn ty(&self, interner: &I) -> Option<&Ty<I>> {
        match self.data(interner) {
            GenericArgData::Ty(t) => Some(t),
            _ => None,
        }
    }

    /// Returns the lifetime if it is one, `None` otherwise.
    pub fn lifetime(&self, interner: &I) -> Option<&Lifetime<I>> {
        match self.data(interner) {
            GenericArgData::Lifetime(t) => Some(t),
            _ => None,
        }
    }

    /// Returns the constant if it is one, `None` otherwise.
    pub fn constant(&self, interner: &I) -> Option<&Const<I>> {
        match self.data(interner) {
            GenericArgData::Const(c) => Some(c),
            _ => None,
        }
    }

    /// Compute type flags for GenericArg<I>
    fn compute_flags(&self, interner: &I) -> TypeFlags {
        match self.data(&interner) {
            GenericArgData::Ty(ty) => ty.data(interner).flags,
            GenericArgData::Lifetime(lifetime) => lifetime.compute_flags(interner),
            GenericArgData::Const(constant) => {
                let data = constant.data(&interner);
                let flags = data.ty.data(interner).flags;
                match data.value {
                    ConstValue::BoundVar(_) => flags,
                    ConstValue::InferenceVar(_) => {
                        flags | TypeFlags::HAS_CT_INFER | TypeFlags::STILL_FURTHER_SPECIALIZABLE
                    }
                    ConstValue::Placeholder(_) => {
                        flags
                            | TypeFlags::HAS_CT_PLACEHOLDER
                            | TypeFlags::STILL_FURTHER_SPECIALIZABLE
                    }
                    ConstValue::Concrete(_) => flags,
                    ConstValue::ConstProjection(_) => todo!(),
                }
            }
        }
    }
}

/// Generic arguments data.
#[derive(Clone, PartialEq, Eq, Hash, Visit, Fold, Zip)]
pub enum GenericArgData<I: Interner> {
    /// Type argument
    Ty(Ty<I>),
    /// Lifetime argument
    Lifetime(Lifetime<I>),
    /// Constant argument
    Const(Const<I>),
}

impl<I: Interner> Copy for GenericArgData<I>
where
    I::InternedType: Copy,
    I::InternedLifetime: Copy,
    I::InternedConst: Copy,
{
}

impl<I: Interner> GenericArgData<I> {
    /// Create an interned type.
    pub fn intern(self, interner: &I) -> GenericArg<I> {
        GenericArg::new(interner, self)
    }
}

/// A value with an associated variable kind.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct WithKind<I: Interner, T> {
    /// The associated variable kind.
    pub kind: VariableKind<I>,
    /// The wrapped value.
    value: T,
}

impl<I: Interner, T: Copy> Copy for WithKind<I, T> where I::InternedType: Copy {}

impl<I: Interner, T> HasInterner for WithKind<I, T> {
    type Interner = I;
}

impl<I: Interner, T> From<WithKind<I, T>> for (VariableKind<I>, T) {
    fn from(with_kind: WithKind<I, T>) -> Self {
        (with_kind.kind, with_kind.value)
    }
}

impl<I: Interner, T> WithKind<I, T> {
    /// Creates a `WithKind` from a variable kind and a value.
    pub fn new(kind: VariableKind<I>, value: T) -> Self {
        Self { kind, value }
    }

    /// Maps the value in `WithKind`.
    pub fn map<U, OP>(self, op: OP) -> WithKind<I, U>
    where
        OP: FnOnce(T) -> U,
    {
        WithKind {
            kind: self.kind,
            value: op(self.value),
        }
    }

    /// Maps a function taking `WithKind<I, &T>` over `&WithKind<I, T>`.
    pub fn map_ref<U, OP>(&self, op: OP) -> WithKind<I, U>
    where
        OP: FnOnce(&T) -> U,
    {
        WithKind {
            kind: self.kind.clone(),
            value: op(&self.value),
        }
    }

    /// Extract the value, ignoring the variable kind.
    pub fn skip_kind(&self) -> &T {
        &self.value
    }
}

/// A variable kind with universe index.
#[allow(type_alias_bounds)]
pub type CanonicalVarKind<I: Interner> = WithKind<I, UniverseIndex>;

/// An alias, which is a trait indirection such as a projection or opaque type.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
pub enum AliasTy<I: Interner> {
    /// An associated type projection.
    Projection(ProjectionTy<I>),
    /// An opaque type.
    Opaque(OpaqueTy<I>),
}

impl<I: Interner> Copy for AliasTy<I> where I::InternedSubstitution: Copy {}

impl<I: Interner> AliasTy<I> {
    /// Create an interned type for this alias.
    pub fn intern(self, interner: &I) -> Ty<I> {
        Ty::new(interner, self)
    }

    /// Compute type flags for aliases
    fn compute_flags(&self, interner: &I) -> TypeFlags {
        match self {
            AliasTy::Projection(projection_ty) => {
                TypeFlags::HAS_TY_PROJECTION | projection_ty.substitution.compute_flags(interner)
            }
            AliasTy::Opaque(opaque_ty) => {
                TypeFlags::HAS_TY_OPAQUE | opaque_ty.substitution.compute_flags(interner)
            }
        }
    }
}

/// A projection `<P0 as TraitName<P1..Pn>>::AssocItem<Pn+1..Pm>`.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct ProjectionTy<I: Interner> {
    /// The id for the associated type member.
    pub associated_ty_id: AssocTypeId<I>,
    /// The substitution for the projection.
    pub substitution: Substitution<I>,
}

impl<I: Interner> Copy for ProjectionTy<I> where I::InternedSubstitution: Copy {}

impl<I: Interner> ProjectionTy<I> {
    /// Gets the type parameters of the `Self` type in this alias type.
    pub fn self_type_parameter(&self, interner: &I) -> Ty<I> {
        self.substitution
            .iter(interner)
            .find_map(move |p| p.ty(interner))
            .unwrap()
            .clone()
    }
}

/// An opaque type `opaque type T<..>: Trait = HiddenTy`.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct OpaqueTy<I: Interner> {
    /// The id for the opaque type.
    pub opaque_ty_id: OpaqueTyId<I>,
    /// The substitution for the opaque type.
    pub substitution: Substitution<I>,
}

impl<I: Interner> Copy for OpaqueTy<I> where I::InternedSubstitution: Copy {}

/// A trait reference describes the relationship between a type and a trait.
/// This can be used in two forms:
/// - `P0: Trait<P1..Pn>` (e.g. `i32: Copy`), which mentions that the type
///   implements the trait.
/// - `<P0 as Trait<P1..Pn>>` (e.g. `i32 as Copy`), which casts the type to
///   that specific trait.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct TraitRef<I: Interner> {
    /// The trait id.
    pub trait_id: TraitId<I>,
    /// The substitution, containing both the `Self` type and the parameters.
    pub substitution: Substitution<I>,
}

impl<I: Interner> Copy for TraitRef<I> where I::InternedSubstitution: Copy {}

impl<I: Interner> TraitRef<I> {
    /// Gets all type parameters in this trait ref, including `Self`.
    pub fn type_parameters<'a>(&'a self, interner: &'a I) -> impl Iterator<Item = Ty<I>> + 'a {
        self.substitution
            .iter(interner)
            .filter_map(move |p| p.ty(interner))
            .cloned()
    }

    /// Gets the type parameters of the `Self` type in this trait ref.
    pub fn self_type_parameter(&self, interner: &I) -> Ty<I> {
        self.type_parameters(interner).next().unwrap()
    }

    /// Construct a `FromEnv` using this trait ref.
    pub fn from_env(self) -> FromEnv<I> {
        FromEnv::Trait(self)
    }

    /// Construct a `WellFormed` using this trait ref.
    pub fn well_formed(self) -> WellFormed<I> {
        WellFormed::Trait(self)
    }
}

/// Lifetime outlives, which for `'a: 'b`` checks that the lifetime `'a`
/// is a superset of the value of `'b`.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
#[allow(missing_docs)]
pub struct LifetimeOutlives<I: Interner> {
    pub a: Lifetime<I>,
    pub b: Lifetime<I>,
}

impl<I: Interner> Copy for LifetimeOutlives<I> where I::InternedLifetime: Copy {}

/// Type outlives, which for `T: 'a` checks that the type `T`
/// lives at least as long as the lifetime `'a`
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
pub struct TypeOutlives<I: Interner> {
    /// The type which must outlive the given lifetime.
    pub ty: Ty<I>,
    /// The lifetime which the type must outlive.
    pub lifetime: Lifetime<I>,
}

impl<I: Interner> Copy for TypeOutlives<I>
where
    I::InternedLifetime: Copy,
    I::InternedType: Copy,
{
}

/// Where clauses that can be written by a Rust programmer.
#[derive(Clone, PartialEq, Eq, Hash, Fold, SuperVisit, HasInterner, Zip)]
pub enum WhereClause<I: Interner> {
    /// Type implements a trait.
    Implemented(TraitRef<I>),
    /// Type is equal to an alias.
    AliasEq(AliasEq<I>),
    /// One lifetime outlives another.
    LifetimeOutlives(LifetimeOutlives<I>),
    /// Type outlives a lifetime.
    TypeOutlives(TypeOutlives<I>),
}

impl<I: Interner> Copy for WhereClause<I>
where
    I::InternedSubstitution: Copy,
    I::InternedLifetime: Copy,
    I::InternedType: Copy,
{
}

/// Checks whether a type or trait ref is well-formed.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
pub enum WellFormed<I: Interner> {
    /// A predicate which is true when some trait ref is well-formed.
    /// For example, given the following trait definitions:
    ///
    /// ```notrust
    /// trait Clone { ... }
    /// trait Copy where Self: Clone { ... }
    /// ```
    ///
    /// then we have the following rule:
    ///
    /// ```notrust
    /// WellFormed(?Self: Copy) :- ?Self: Copy, WellFormed(?Self: Clone)
    /// ```
    Trait(TraitRef<I>),

    /// A predicate which is true when some type is well-formed.
    /// For example, given the following type definition:
    ///
    /// ```notrust
    /// struct Set<K> where K: Hash {
    ///     ...
    /// }
    /// ```
    ///
    /// then we have the following rule: `WellFormedTy(Set<K>) :- Implemented(K: Hash)`.
    Ty(Ty<I>),
}

impl<I: Interner> Copy for WellFormed<I>
where
    I::InternedType: Copy,
    I::InternedSubstitution: Copy,
{
}

/// Checks whether a type or trait ref can be derived from the contents of the environment.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
pub enum FromEnv<I: Interner> {
    /// A predicate which enables deriving everything which should be true if we *know* that
    /// some trait ref is well-formed. For example given the above trait definitions, we can use
    /// `FromEnv(T: Copy)` to derive that `T: Clone`, like in:
    ///
    /// ```notrust
    /// forall<T> {
    ///     if (FromEnv(T: Copy)) {
    ///         T: Clone
    ///     }
    /// }
    /// ```
    Trait(TraitRef<I>),

    /// A predicate which enables deriving everything which should be true if we *know* that
    /// some type is well-formed. For example given the above type definition, we can use
    /// `FromEnv(Set<K>)` to derive that `K: Hash`, like in:
    ///
    /// ```notrust
    /// forall<K> {
    ///     if (FromEnv(Set<K>)) {
    ///         K: Hash
    ///     }
    /// }
    /// ```
    Ty(Ty<I>),
}

impl<I: Interner> Copy for FromEnv<I>
where
    I::InternedType: Copy,
    I::InternedSubstitution: Copy,
{
}

/// A "domain goal" is a goal that is directly about Rust, rather than a pure
/// logical statement. As much as possible, the Chalk solver should avoid
/// decomposing this enum, and instead treat its values opaquely.
#[derive(Clone, PartialEq, Eq, Hash, Fold, SuperVisit, HasInterner, Zip)]
pub enum DomainGoal<I: Interner> {
    /// Simple goal that is true if the where clause is true.
    Holds(WhereClause<I>),

    /// True if the type or trait ref is well-formed.
    WellFormed(WellFormed<I>),

    /// True if the trait ref can be derived from in-scope where clauses.
    FromEnv(FromEnv<I>),

    /// True if the alias type can be normalized to some other type
    Normalize(Normalize<I>),

    /// True if a type is considered to have been "defined" by the current crate. This is true for
    /// a `struct Foo { }` but false for a `#[upstream] struct Foo { }`. However, for fundamental types
    /// like `Box<T>`, it is true if `T` is local.
    IsLocal(Ty<I>),

    /// True if a type is *not* considered to have been "defined" by the current crate. This is
    /// false for a `struct Foo { }` but true for a `#[upstream] struct Foo { }`. However, for
    /// fundamental types like `Box<T>`, it is true if `T` is upstream.
    IsUpstream(Ty<I>),

    /// True if a type and its input types are fully visible, known types. That is, there are no
    /// unknown type parameters anywhere in this type.
    ///
    /// More formally, for each struct S<P0..Pn>:
    /// forall<P0..Pn> {
    ///     IsFullyVisible(S<P0...Pn>) :-
    ///         IsFullyVisible(P0),
    ///         ...
    ///         IsFullyVisible(Pn)
    /// }
    ///
    /// Note that any of these types can have lifetimes in their parameters too, but we only
    /// consider type parameters.
    IsFullyVisible(Ty<I>),

    /// Used to dictate when trait impls are allowed in the current (local) crate based on the
    /// orphan rules.
    ///
    /// `LocalImplAllowed(T: Trait)` is true if the type T is allowed to impl trait Trait in
    /// the current crate. Under the current rules, this is unconditionally true for all types if
    /// the Trait is considered to be "defined" in the current crate. If that is not the case, then
    /// `LocalImplAllowed(T: Trait)` can still be true if `IsLocal(T)` is true.
    LocalImplAllowed(TraitRef<I>),

    /// Used to activate the "compatible modality" rules. Rules that introduce predicates that have
    /// to do with "all compatible universes" should depend on this clause so that they only apply
    /// if this is present.
    Compatible,

    /// Used to indicate that a given type is in a downstream crate. Downstream crates contain the
    /// current crate at some level of their dependencies.
    ///
    /// Since chalk does not actually see downstream types, this is usually introduced with
    /// implication on a fresh, universally quantified type.
    ///
    /// forall<T> { if (DownstreamType(T)) { /* ... */ } }
    ///
    /// This makes a new type `T` available and makes `DownstreamType(T)` provable for that type.
    DownstreamType(Ty<I>),

    /// Used to activate the "reveal mode", in which opaque (`impl Trait`) types can be equated
    /// to their actual type.
    Reveal,

    /// Used to indicate that a trait is object safe.
    ObjectSafe(TraitId<I>),
}

impl<I: Interner> Copy for DomainGoal<I>
where
    I::InternedSubstitution: Copy,
    I::InternedLifetime: Copy,
    I::InternedType: Copy,
{
}

/// A where clause that can contain `forall<>` or `exists<>` quantifiers.
pub type QuantifiedWhereClause<I> = Binders<WhereClause<I>>;

impl<I: Interner> WhereClause<I> {
    /// Turn a where clause into the WF version of it i.e.:
    /// * `Implemented(T: Trait)` maps to `WellFormed(T: Trait)`
    /// * `ProjectionEq(<T as Trait>::Item = Foo)` maps to `WellFormed(<T as Trait>::Item = Foo)`
    /// * any other clause maps to itself
    pub fn into_well_formed_goal(self, interner: &I) -> DomainGoal<I> {
        match self {
            WhereClause::Implemented(trait_ref) => WellFormed::Trait(trait_ref).cast(interner),
            wc => wc.cast(interner),
        }
    }

    /// Same as `into_well_formed_goal` but with the `FromEnv` predicate instead of `WellFormed`.
    pub fn into_from_env_goal(self, interner: &I) -> DomainGoal<I> {
        match self {
            WhereClause::Implemented(trait_ref) => FromEnv::Trait(trait_ref).cast(interner),
            wc => wc.cast(interner),
        }
    }

    /// If where clause is a `TraitRef`, returns its trait id.
    pub fn trait_id(&self) -> Option<TraitId<I>> {
        match self {
            WhereClause::Implemented(trait_ref) => Some(trait_ref.trait_id),
            WhereClause::AliasEq(_) => None,
            WhereClause::LifetimeOutlives(_) => None,
            WhereClause::TypeOutlives(_) => None,
        }
    }
}

impl<I: Interner> QuantifiedWhereClause<I> {
    /// As with `WhereClause::into_well_formed_goal`, but for a
    /// quantified where clause. For example, `forall<T> {
    /// Implemented(T: Trait)}` would map to `forall<T> {
    /// WellFormed(T: Trait) }`.
    pub fn into_well_formed_goal(self, interner: &I) -> Binders<DomainGoal<I>> {
        self.map(|wc| wc.into_well_formed_goal(interner))
    }

    /// As with `WhereClause::into_from_env_goal`, but mapped over any
    /// binders. For example, `forall<T> {
    /// Implemented(T: Trait)}` would map to `forall<T> {
    /// FromEnv(T: Trait) }`.
    pub fn into_from_env_goal(self, interner: &I) -> Binders<DomainGoal<I>> {
        self.map(|wc| wc.into_from_env_goal(interner))
    }

    /// If the underlying where clause is a `TraitRef`, returns its trait id.
    pub fn trait_id(&self) -> Option<TraitId<I>> {
        self.skip_binders().trait_id()
    }
}

impl<I: Interner> DomainGoal<I> {
    /// Convert `Implemented(...)` into `FromEnv(...)`, but leave other
    /// goals unchanged.
    pub fn into_from_env_goal(self, interner: &I) -> DomainGoal<I> {
        match self {
            DomainGoal::Holds(wc) => wc.into_from_env_goal(interner),
            goal => goal,
        }
    }

    /// Lists generic arguments that are inputs to this domain goal.
    pub fn inputs(&self, interner: &I) -> Vec<GenericArg<I>> {
        match self {
            DomainGoal::Holds(WhereClause::AliasEq(alias_eq)) => {
                vec![GenericArgData::Ty(alias_eq.alias.clone().intern(interner)).intern(interner)]
            }
            _ => Vec::new(),
        }
    }
}

/// Equality goal: tries to prove that two values are equal.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, Zip)]
#[allow(missing_docs)]
pub struct EqGoal<I: Interner> {
    pub a: GenericArg<I>,
    pub b: GenericArg<I>,
}

impl<I: Interner> Copy for EqGoal<I> where I::InternedGenericArg: Copy {}

/// Subtype goal: tries to prove that `a` is a subtype of `b`
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, Zip)]
#[allow(missing_docs)]
pub struct SubtypeGoal<I: Interner> {
    pub a: Ty<I>,
    pub b: Ty<I>,
}

impl<I: Interner> Copy for SubtypeGoal<I> where I::InternedType: Copy {}

/// Proves that the given type alias **normalizes** to the given
/// type. A projection `T::Foo` normalizes to the type `U` if we can
/// **match it to an impl** and that impl has a `type Foo = V` where
/// `U = V`.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, Zip)]
#[allow(missing_docs)]
pub struct Normalize<I: Interner> {
    pub alias: AliasTy<I>,
    pub ty: Ty<I>,
}

impl<I: Interner> Copy for Normalize<I>
where
    I::InternedSubstitution: Copy,
    I::InternedType: Copy,
{
}

/// Proves **equality** between an alias and a type.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, Zip)]
#[allow(missing_docs)]
pub struct AliasEq<I: Interner> {
    pub alias: AliasTy<I>,
    pub ty: Ty<I>,
}

impl<I: Interner> Copy for AliasEq<I>
where
    I::InternedSubstitution: Copy,
    I::InternedType: Copy,
{
}

impl<I: Interner> HasInterner for AliasEq<I> {
    type Interner = I;
}

/// Indicates that the `value` is universally quantified over `N`
/// parameters of the given kinds, where `N == self.binders.len()`. A
/// variable with depth `i < N` refers to the value at
/// `self.binders[i]`. Variables with depth `>= N` are free.
///
/// (IOW, we use deBruijn indices, where binders are introduced in reverse order
/// of `self.binders`.)
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Binders<T: HasInterner> {
    /// The binders that quantify over the value.
    pub binders: VariableKinds<T::Interner>,

    /// The value being quantified over.
    value: T,
}

impl<T: HasInterner + Copy> Copy for Binders<T> where
    <T::Interner as Interner>::InternedVariableKinds: Copy
{
}

impl<T: HasInterner> HasInterner for Binders<T> {
    type Interner = T::Interner;
}

impl<T: Clone + HasInterner> Binders<&T> {
    /// Converts a `Binders<&T>` to a `Binders<T>` by cloning `T`.
    pub fn cloned(self) -> Binders<T> {
        self.map(Clone::clone)
    }
}

impl<T: HasInterner> Binders<T> {
    /// Create new binders.
    pub fn new(binders: VariableKinds<T::Interner>, value: T) -> Self {
        Self { binders, value }
    }

    /// Wraps the given value in a binder without variables, i.e. `for<>
    /// (value)`. Since our deBruijn indices count binders, not variables, this
    /// is sometimes useful.
    pub fn empty(interner: &T::Interner, value: T) -> Self {
        let binders = VariableKinds::empty(interner);
        Self { binders, value }
    }

    /// Skips the binder and returns the "bound" value. This is a
    /// risky thing to do because it's easy to get confused about
    /// De Bruijn indices and the like. `skip_binder` is only valid
    /// when you are either extracting data that has nothing to
    /// do with bound vars, or you are being very careful about
    /// your depth accounting.
    ///
    /// Some examples where `skip_binder` is reasonable:
    ///
    /// - extracting the `TraitId` from a TraitRef;
    /// - checking if there are any fields in a StructDatum
    pub fn skip_binders(&self) -> &T {
        &self.value
    }

    /// Skips the binder and returns the "bound" value as well as the skipped free variables. This
    /// is just as risky as [`skip_binders`].
    pub fn into_value_and_skipped_binders(self) -> (T, VariableKinds<T::Interner>) {
        (self.value, self.binders)
    }

    /// Converts `&Binders<T>` to `Binders<&T>`. Produces new `Binders`
    /// with cloned quantifiers containing a reference to the original
    /// value, leaving the original in place.
    pub fn as_ref(&self) -> Binders<&T> {
        Binders {
            binders: self.binders.clone(),
            value: &self.value,
        }
    }

    /// Maps the binders by applying a function.
    pub fn map<U, OP>(self, op: OP) -> Binders<U>
    where
        OP: FnOnce(T) -> U,
        U: HasInterner<Interner = T::Interner>,
    {
        let value = op(self.value);
        Binders {
            binders: self.binders,
            value,
        }
    }

    /// Transforms the inner value according to the given function; returns
    /// `None` if the function returns `None`.
    pub fn filter_map<U, OP>(self, op: OP) -> Option<Binders<U>>
    where
        OP: FnOnce(T) -> Option<U>,
        U: HasInterner<Interner = T::Interner>,
    {
        let value = op(self.value)?;
        Some(Binders {
            binders: self.binders,
            value,
        })
    }

    /// Maps a function taking `Binders<&T>` over `&Binders<T>`.
    pub fn map_ref<'a, U, OP>(&'a self, op: OP) -> Binders<U>
    where
        OP: FnOnce(&'a T) -> U,
        U: HasInterner<Interner = T::Interner>,
    {
        self.as_ref().map(op)
    }

    /// Creates a `Substitution` containing bound vars such that applying this
    /// substitution will not change the value, i.e. `^0.0, ^0.1, ^0.2` and so
    /// on.
    pub fn identity_substitution(&self, interner: &T::Interner) -> Substitution<T::Interner> {
        Substitution::from_iter(
            interner,
            self.binders
                .iter(interner)
                .enumerate()
                .map(|p| p.to_generic_arg(interner)),
        )
    }

    /// Creates a fresh binders that contains a single type
    /// variable. The result of the closure will be embedded in this
    /// binder. Note that you should be careful with what you return
    /// from the closure to account for the binder that will be added.
    ///
    /// XXX FIXME -- this is potentially a pretty footgun-y function.
    pub fn with_fresh_type_var(
        interner: &T::Interner,
        op: impl FnOnce(Ty<T::Interner>) -> T,
    ) -> Binders<T> {
        // The new variable is at the front and everything afterwards is shifted up by 1
        let new_var = TyKind::BoundVar(BoundVar::new(DebruijnIndex::INNERMOST, 0)).intern(interner);
        let value = op(new_var);
        let binders = VariableKinds::from1(interner, VariableKind::Ty(TyVariableKind::General));
        Binders { binders, value }
    }

    /// Returns the number of binders.
    pub fn len(&self, interner: &T::Interner) -> usize {
        self.binders.len(interner)
    }
}

impl<T, I> Binders<Binders<T>>
where
    T: Fold<I> + HasInterner<Interner = I>,
    T::Result: HasInterner<Interner = I>,
    I: Interner,
{
    /// This turns two levels of binders (`for<A> for<B>`) into one level (`for<A, B>`).
    pub fn fuse_binders(self, interner: &T::Interner) -> Binders<T::Result> {
        let num_binders = self.len(interner);
        // generate a substitution to shift the indexes of the inner binder:
        let subst = Substitution::from_iter(
            interner,
            self.value
                .binders
                .iter(interner)
                .enumerate()
                .map(|(i, pk)| (i + num_binders, pk).to_generic_arg(interner)),
        );
        let binders = VariableKinds::from_iter(
            interner,
            self.binders
                .iter(interner)
                .chain(self.value.binders.iter(interner))
                .cloned(),
        );
        let value = self.value.substitute(interner, &subst);
        Binders { binders, value }
    }
}

impl<T: HasInterner> From<Binders<T>> for (VariableKinds<T::Interner>, T) {
    fn from(binders: Binders<T>) -> Self {
        (binders.binders, binders.value)
    }
}

impl<T, I> Binders<T>
where
    T: Fold<I> + HasInterner<Interner = I>,
    I: Interner,
{
    /// Substitute `parameters` for the variables introduced by these
    /// binders. So if the binders represent (e.g.) `<X, Y> { T }` and
    /// parameters is the slice `[A, B]`, then returns `[X => A, Y =>
    /// B] T`.
    pub fn substitute(
        self,
        interner: &I,
        parameters: &(impl AsParameters<I> + ?Sized),
    ) -> T::Result {
        let parameters = parameters.as_parameters(interner);
        assert_eq!(self.binders.len(interner), parameters.len());
        Subst::apply(interner, parameters, self.value)
    }
}

/// Allows iterating over a Binders<Vec<T>>, for instance.
/// Each element will include the same set of parameter bounds.
impl<V, U> IntoIterator for Binders<V>
where
    V: HasInterner + IntoIterator<Item = U>,
    U: HasInterner<Interner = V::Interner>,
{
    type Item = Binders<U>;
    type IntoIter = BindersIntoIterator<V>;

    fn into_iter(self) -> Self::IntoIter {
        BindersIntoIterator {
            iter: self.value.into_iter(),
            binders: self.binders,
        }
    }
}

/// `IntoIterator` for binders.
pub struct BindersIntoIterator<V: HasInterner + IntoIterator> {
    iter: <V as IntoIterator>::IntoIter,
    binders: VariableKinds<V::Interner>,
}

impl<V> Iterator for BindersIntoIterator<V>
where
    V: HasInterner + IntoIterator,
    <V as IntoIterator>::Item: HasInterner<Interner = V::Interner>,
{
    type Item = Binders<<V as IntoIterator>::Item>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|v| Binders::new(self.binders.clone(), v))
    }
}

/// Represents one clause of the form `consequence :- conditions` where
/// `conditions = cond_1 && cond_2 && ...` is the conjunction of the individual
/// conditions.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
pub struct ProgramClauseImplication<I: Interner> {
    /// The consequence of the clause, which holds if the conditions holds.
    pub consequence: DomainGoal<I>,

    /// The condition goals that should hold.
    pub conditions: Goals<I>,

    /// The lifetime constraints that should be proven.
    pub constraints: Constraints<I>,

    /// The relative priority of the implication.
    pub priority: ClausePriority,
}

/// Specifies how important an implication is.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum ClausePriority {
    /// High priority, the solver should prioritize this.
    High,

    /// Low priority, this implication has lower chance to be relevant to the goal.
    Low,
}

impl std::ops::BitAnd for ClausePriority {
    type Output = ClausePriority;
    fn bitand(self, rhs: ClausePriority) -> Self::Output {
        match (self, rhs) {
            (ClausePriority::High, ClausePriority::High) => ClausePriority::High,
            _ => ClausePriority::Low,
        }
    }
}

/// Contains the data for a program clause.
#[derive(Clone, PartialEq, Eq, Hash, Fold, HasInterner, Zip)]
pub struct ProgramClauseData<I: Interner>(pub Binders<ProgramClauseImplication<I>>);

impl<I: Interner> ProgramClauseImplication<I> {
    /// Change the implication into an application holding a `FromEnv` goal.
    pub fn into_from_env_clause(self, interner: &I) -> ProgramClauseImplication<I> {
        if self.conditions.is_empty(interner) {
            ProgramClauseImplication {
                consequence: self.consequence.into_from_env_goal(interner),
                conditions: self.conditions.clone(),
                constraints: self.constraints.clone(),
                priority: self.priority,
            }
        } else {
            self
        }
    }
}

impl<I: Interner> ProgramClauseData<I> {
    /// Change the program clause data into a `FromEnv` program clause.
    pub fn into_from_env_clause(self, interner: &I) -> ProgramClauseData<I> {
        ProgramClauseData(self.0.map(|i| i.into_from_env_clause(interner)))
    }

    /// Intern the program clause data.
    pub fn intern(self, interner: &I) -> ProgramClause<I> {
        ProgramClause {
            interned: interner.intern_program_clause(self),
        }
    }
}

/// A program clause is a logic expression used to describe a part of the program.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
pub struct ProgramClause<I: Interner> {
    interned: I::InternedProgramClause,
}

impl<I: Interner> ProgramClause<I> {
    /// Create a new program clause using `ProgramClauseData`.
    pub fn new(interner: &I, clause: ProgramClauseData<I>) -> Self {
        let interned = interner.intern_program_clause(clause);
        Self { interned }
    }

    /// Change the clause into a `FromEnv` clause.
    pub fn into_from_env_clause(self, interner: &I) -> ProgramClause<I> {
        let program_clause_data = self.data(interner);
        let new_clause = program_clause_data.clone().into_from_env_clause(interner);
        Self::new(interner, new_clause)
    }

    /// Get the interned program clause.
    pub fn interned(&self) -> &I::InternedProgramClause {
        &self.interned
    }

    /// Get the program clause data.
    pub fn data(&self, interner: &I) -> &ProgramClauseData<I> {
        interner.program_clause_data(&self.interned)
    }
}

/// Wraps a "canonicalized item". Items are canonicalized as follows:
///
/// All unresolved existential variables are "renumbered" according to their
/// first appearance; the kind/universe of the variable is recorded in the
/// `binders` field.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Canonical<T: HasInterner> {
    /// The item that is canonicalized.
    pub value: T,

    /// The kind/universe of the variable.
    pub binders: CanonicalVarKinds<T::Interner>,
}

impl<T: HasInterner> HasInterner for Canonical<T> {
    type Interner = T::Interner;
}

/// A "universe canonical" value. This is a wrapper around a
/// `Canonical`, indicating that the universes within have been
/// "renumbered" to start from 0 and collapse unimportant
/// distinctions.
///
/// To produce one of these values, use the `u_canonicalize` method.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UCanonical<T: HasInterner> {
    /// The wrapped `Canonical`.
    pub canonical: Canonical<T>,

    /// The number of universes that have been collapsed.
    pub universes: usize,
}

impl<T: HasInterner> UCanonical<T> {
    /// Checks whether the universe canonical value is a trivial
    /// substitution (e.g. an identity substitution).
    pub fn is_trivial_substitution(
        &self,
        interner: &T::Interner,
        canonical_subst: &Canonical<AnswerSubst<T::Interner>>,
    ) -> bool {
        let subst = &canonical_subst.value.subst;
        assert_eq!(
            self.canonical.binders.len(interner),
            subst.as_slice(interner).len()
        );
        subst.is_identity_subst(interner)
    }

    /// Creates an identity substitution.
    pub fn trivial_substitution(&self, interner: &T::Interner) -> Substitution<T::Interner> {
        let binders = &self.canonical.binders;
        Substitution::from_iter(
            interner,
            binders
                .iter(interner)
                .enumerate()
                .map(|(index, pk)| {
                    let bound_var = BoundVar::new(DebruijnIndex::INNERMOST, index);
                    match &pk.kind {
                        VariableKind::Ty(_) => {
                            GenericArgData::Ty(TyKind::BoundVar(bound_var).intern(interner))
                                .intern(interner)
                        }
                        VariableKind::Lifetime => GenericArgData::Lifetime(
                            LifetimeData::BoundVar(bound_var).intern(interner),
                        )
                        .intern(interner),
                        VariableKind::Const(ty) => GenericArgData::Const(
                            ConstData {
                                ty: ty.clone(),
                                value: ConstValue::BoundVar(bound_var),
                            }
                            .intern(interner),
                        )
                        .intern(interner),
                    }
                })
                .collect::<Vec<_>>(),
        )
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
/// A general goal; this is the full range of questions you can pose to Chalk.
pub struct Goal<I: Interner> {
    interned: I::InternedGoal,
}

impl<I: Interner> Goal<I> {
    /// Create a new goal using `GoalData`.
    pub fn new(interner: &I, interned: GoalData<I>) -> Self {
        let interned = I::intern_goal(interner, interned);
        Self { interned }
    }

    /// Gets the interned goal.
    pub fn interned(&self) -> &I::InternedGoal {
        &self.interned
    }

    /// Gets the interned goal data.
    pub fn data(&self, interner: &I) -> &GoalData<I> {
        interner.goal_data(&self.interned)
    }

    /// Create a goal using a `forall` or `exists` quantifier.
    pub fn quantify(
        self,
        interner: &I,
        kind: QuantifierKind,
        binders: VariableKinds<I>,
    ) -> Goal<I> {
        GoalData::Quantified(kind, Binders::new(binders, self)).intern(interner)
    }

    /// Takes a goal `G` and turns it into `not { G }`.
    pub fn negate(self, interner: &I) -> Self {
        GoalData::Not(self).intern(interner)
    }

    /// Takes a goal `G` and turns it into `compatible { G }`.
    pub fn compatible(self, interner: &I) -> Self {
        // compatible { G } desugars into: forall<T> { if (Compatible, DownstreamType(T)) { G } }
        // This activates the compatible modality rules and introduces an anonymous downstream type
        GoalData::Quantified(
            QuantifierKind::ForAll,
            Binders::with_fresh_type_var(interner, |ty| {
                GoalData::Implies(
                    ProgramClauses::from_iter(
                        interner,
                        vec![DomainGoal::Compatible, DomainGoal::DownstreamType(ty)],
                    ),
                    self.shifted_in(interner),
                )
                .intern(interner)
            }),
        )
        .intern(interner)
    }

    /// Create an implication goal that holds if the predicates are true.
    pub fn implied_by(self, interner: &I, predicates: ProgramClauses<I>) -> Goal<I> {
        GoalData::Implies(predicates, self).intern(interner)
    }

    /// True if this goal is "trivially true" -- i.e., no work is
    /// required to prove it.
    pub fn is_trivially_true(&self, interner: &I) -> bool {
        match self.data(interner) {
            GoalData::All(goals) => goals.is_empty(interner),
            _ => false,
        }
    }
}

impl<I> Goal<I>
where
    I: Interner,
{
    /// Creates a single goal that only holds if a list of goals holds.
    pub fn all<II>(interner: &I, iter: II) -> Self
    where
        II: IntoIterator<Item = Goal<I>>,
    {
        let mut iter = iter.into_iter();
        if let Some(goal0) = iter.next() {
            if let Some(goal1) = iter.next() {
                // More than one goal to prove
                let goals = Goals::from_iter(
                    interner,
                    Some(goal0).into_iter().chain(Some(goal1)).chain(iter),
                );
                GoalData::All(goals).intern(interner)
            } else {
                // One goal to prove
                goal0
            }
        } else {
            // No goals to prove, always true
            GoalData::All(Goals::empty(interner)).intern(interner)
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
/// A general goal; this is the full range of questions you can pose to Chalk.
pub enum GoalData<I: Interner> {
    /// Introduces a binding at depth 0, shifting other bindings up
    /// (deBruijn index).
    Quantified(QuantifierKind, Binders<Goal<I>>),

    /// A goal that holds given some clauses (like an if-statement).
    Implies(ProgramClauses<I>, Goal<I>),

    /// List of goals that all should hold.
    All(Goals<I>),

    /// Negation: the inner goal should not hold.
    Not(Goal<I>),

    /// Make two things equal; the rules for doing so are well known to the logic
    EqGoal(EqGoal<I>),

    /// Make one thing a subtype of another; the rules for doing so are well known to the logic
    SubtypeGoal(SubtypeGoal<I>),

    /// A "domain goal" indicates some base sort of goal that can be
    /// proven via program clauses
    DomainGoal(DomainGoal<I>),

    /// Indicates something that cannot be proven to be true or false
    /// definitively. This can occur with overflow but also with
    /// unifications of skolemized variables like `forall<X,Y> { X = Y
    /// }`. Of course, that statement is false, as there exist types
    /// X, Y where `X = Y` is not true. But we treat it as "cannot
    /// prove" so that `forall<X,Y> { not { X = Y } }` also winds up
    /// as cannot prove.
    CannotProve,
}

impl<I: Interner> Copy for GoalData<I>
where
    I::InternedType: Copy,
    I::InternedLifetime: Copy,
    I::InternedGenericArg: Copy,
    I::InternedSubstitution: Copy,
    I::InternedGoal: Copy,
    I::InternedGoals: Copy,
    I::InternedProgramClauses: Copy,
    I::InternedVariableKinds: Copy,
{
}

impl<I: Interner> GoalData<I> {
    /// Create an interned goal.
    pub fn intern(self, interner: &I) -> Goal<I> {
        Goal::new(interner, self)
    }
}

/// Kinds of quantifiers in the logic, such as `forall` and `exists`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum QuantifierKind {
    /// Universal quantifier `ForAll`.
    ///
    /// A formula with the universal quantifier `forall(x). P(x)` is satisfiable
    /// if and only if the subformula `P(x)` is true for all possible values for x.
    ForAll,

    /// Existential quantifier `Exists`.
    ///
    /// A formula with the existential quantifier `exists(x). P(x)` is satisfiable
    /// if and only if there exists at least one value for all possible values of x
    /// which satisfies the subformula `P(x)`.

    /// In the context of chalk, the existential quantifier usually demands the
    /// existence of exactly one instance (i.e. type) that satisfies the formula
    /// (i.e. type constraints). More than one instance means that the result is ambiguous.
    Exists,
}

/// A constraint on lifetimes.
///
/// When we search for solutions within the trait system, we essentially ignore
/// lifetime constraints, instead gathering them up to return with our solution
/// for later checking. This allows for decoupling between type and region
/// checking in the compiler.
#[derive(Clone, PartialEq, Eq, Hash, Fold, Visit, HasInterner, Zip)]
pub enum Constraint<I: Interner> {
    /// Outlives constraint `'a: 'b`, indicating that the value of `'a` must be
    /// a superset of the value of `'b`.
    LifetimeOutlives(Lifetime<I>, Lifetime<I>),

    /// Type outlives constraint `T: 'a`, indicating that the type `T` must live
    /// at least as long as the value of `'a`.
    TypeOutlives(Ty<I>, Lifetime<I>),
}

impl<I: Interner> Copy for Constraint<I>
where
    I::InternedLifetime: Copy,
    I::InternedType: Copy,
{
}

impl<I: Interner> Substitution<I> {
    /// A substitution is an **identity substitution** if it looks
    /// like this
    ///
    /// ```text
    /// ?0 := ?0
    /// ?1 := ?1
    /// ?2 := ?2
    /// ...
    /// ```
    ///
    /// Basically, each value is mapped to a type or lifetime with its
    /// same index.
    pub fn is_identity_subst(&self, interner: &I) -> bool {
        self.iter(interner).zip(0..).all(|(generic_arg, index)| {
            let index_db = BoundVar::new(DebruijnIndex::INNERMOST, index);
            match generic_arg.data(interner) {
                GenericArgData::Ty(ty) => match ty.kind(interner) {
                    TyKind::BoundVar(depth) => index_db == *depth,
                    _ => false,
                },
                GenericArgData::Lifetime(lifetime) => match lifetime.data(interner) {
                    LifetimeData::BoundVar(depth) => index_db == *depth,
                    _ => false,
                },
                GenericArgData::Const(constant) => match &constant.data(interner).value {
                    ConstValue::BoundVar(depth) => index_db == *depth,
                    _ => false,
                },
            }
        })
    }

    /// Apply the substitution to a value.
    pub fn apply<T>(&self, value: T, interner: &I) -> T::Result
    where
        T: Fold<I>,
    {
        Substitute::apply(self, value, interner)
    }

    /// Gets an iterator of all type parameters.
    pub fn type_parameters<'a>(&'a self, interner: &'a I) -> impl Iterator<Item = Ty<I>> + 'a {
        self.iter(interner)
            .filter_map(move |p| p.ty(interner))
            .cloned()
    }

    /// Compute type flags for Substitution<I>
    fn compute_flags(&self, interner: &I) -> TypeFlags {
        let mut flags = TypeFlags::empty();
        for generic_arg in self.iter(&interner) {
            flags |= generic_arg.compute_flags(interner);
        }
        flags
    }
}

struct SubstFolder<'i, I: Interner, A: AsParameters<I>> {
    interner: &'i I,
    subst: &'i A,
}

impl<I: Interner, A: AsParameters<I>> SubstFolder<'_, I, A> {
    /// Index into the list of parameters.
    pub fn at(&self, index: usize) -> &GenericArg<I> {
        let interner = self.interner;
        &self.subst.as_parameters(interner)[index]
    }
}

/// Convert a value to a list of parameters.
pub trait AsParameters<I: Interner> {
    /// Convert the current value to parameters.
    fn as_parameters(&self, interner: &I) -> &[GenericArg<I>];
}

impl<I: Interner> AsParameters<I> for Substitution<I> {
    #[allow(unreachable_code, unused_variables)]
    fn as_parameters(&self, interner: &I) -> &[GenericArg<I>] {
        self.as_slice(interner)
    }
}

impl<I: Interner> AsParameters<I> for [GenericArg<I>] {
    fn as_parameters(&self, _interner: &I) -> &[GenericArg<I>] {
        self
    }
}

impl<I: Interner> AsParameters<I> for [GenericArg<I>; 1] {
    fn as_parameters(&self, _interner: &I) -> &[GenericArg<I>] {
        self
    }
}

impl<I: Interner> AsParameters<I> for Vec<GenericArg<I>> {
    fn as_parameters(&self, _interner: &I) -> &[GenericArg<I>] {
        self
    }
}

impl<T, I: Interner> AsParameters<I> for &T
where
    T: ?Sized + AsParameters<I>,
{
    fn as_parameters(&self, interner: &I) -> &[GenericArg<I>] {
        T::as_parameters(self, interner)
    }
}

/// An extension trait to anything that can be represented as list of `GenericArg`s that signifies
/// that it can applied as a substituion to a value
pub trait Substitute<I: Interner>: AsParameters<I> {
    /// Apply the substitution to a value.
    fn apply<T: Fold<I>>(&self, value: T, interner: &I) -> T::Result;
}

impl<I: Interner, A: AsParameters<I>> Substitute<I> for A {
    fn apply<T>(&self, value: T, interner: &I) -> T::Result
    where
        T: Fold<I>,
    {
        value
            .fold_with(
                &mut &SubstFolder {
                    interner,
                    subst: self,
                },
                DebruijnIndex::INNERMOST,
            )
            .unwrap()
    }
}

/// Utility for converting a list of all the binders into scope
/// into references to those binders. Simply pair the binders with
/// the indices, and invoke `to_generic_arg()` on the `(binder,
/// index)` pair. The result will be a reference to a bound
/// variable of appropriate kind at the corresponding index.
pub trait ToGenericArg<I: Interner> {
    /// Converts the binders in scope to references to those binders.
    fn to_generic_arg(&self, interner: &I) -> GenericArg<I> {
        self.to_generic_arg_at_depth(interner, DebruijnIndex::INNERMOST)
    }

    /// Converts the binders at the specified depth to references to those binders.
    fn to_generic_arg_at_depth(&self, interner: &I, debruijn: DebruijnIndex) -> GenericArg<I>;
}

impl<'a, I: Interner> ToGenericArg<I> for (usize, &'a VariableKind<I>) {
    fn to_generic_arg_at_depth(&self, interner: &I, debruijn: DebruijnIndex) -> GenericArg<I> {
        let &(index, binder) = self;
        let bound_var = BoundVar::new(debruijn, index);
        binder.to_bound_variable(interner, bound_var)
    }
}

impl<'i, I: Interner, A: AsParameters<I>> Folder<'i, I> for &SubstFolder<'i, I, A> {
    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I> {
        self
    }

    fn fold_free_var_ty(
        &mut self,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Ty<I>> {
        assert_eq!(bound_var.debruijn, DebruijnIndex::INNERMOST);
        let ty = self.at(bound_var.index);
        let ty = ty.assert_ty_ref(self.interner());
        Ok(ty.clone().shifted_in_from(self.interner(), outer_binder))
    }

    fn fold_free_var_lifetime(
        &mut self,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Lifetime<I>> {
        assert_eq!(bound_var.debruijn, DebruijnIndex::INNERMOST);
        let l = self.at(bound_var.index);
        let l = l.assert_lifetime_ref(self.interner());
        Ok(l.clone().shifted_in_from(self.interner(), outer_binder))
    }

    fn fold_free_var_const(
        &mut self,
        _ty: Ty<I>,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Const<I>> {
        assert_eq!(bound_var.debruijn, DebruijnIndex::INNERMOST);
        let c = self.at(bound_var.index);
        let c = c.assert_const_ref(self.interner());
        Ok(c.clone().shifted_in_from(self.interner(), outer_binder))
    }

    fn interner(&self) -> &'i I {
        self.interner
    }
}

macro_rules! interned_slice_common {
    ($seq:ident, $data:ident => $elem:ty, $intern:ident => $interned:ident) => {
        /// List of interned elements.
        #[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, HasInterner)]
        pub struct $seq<I: Interner> {
            interned: I::$interned,
        }

        impl<I: Interner> $seq<I> {
            /// Get the interned elements.
            pub fn interned(&self) -> &I::$interned {
                &self.interned
            }

            /// Returns a slice containing the elements.
            pub fn as_slice(&self, interner: &I) -> &[$elem] {
                Interner::$data(interner, &self.interned)
            }

            /// Index into the sequence.
            pub fn at(&self, interner: &I, index: usize) -> &$elem {
                &self.as_slice(interner)[index]
            }

            /// Create an empty sequence.
            pub fn empty(interner: &I) -> Self {
                Self::from_iter(interner, None::<$elem>)
            }

            /// Check whether this is an empty sequence.
            pub fn is_empty(&self, interner: &I) -> bool {
                self.as_slice(interner).is_empty()
            }

            /// Get an iterator over the elements of the sequence.
            pub fn iter(&self, interner: &I) -> std::slice::Iter<'_, $elem> {
                self.as_slice(interner).iter()
            }

            /// Get the length of the sequence.
            pub fn len(&self, interner: &I) -> usize {
                self.as_slice(interner).len()
            }
        }
    };
}

macro_rules! interned_slice {
    ($seq:ident, $data:ident => $elem:ty, $intern:ident => $interned:ident) => {
        interned_slice_common!($seq, $data => $elem, $intern => $interned);

        impl<I: Interner> $seq<I> {
            /// Tries to create a sequence using an iterator of element-like things.
            pub fn from_fallible<E>(
                interner: &I,
                elements: impl IntoIterator<Item = Result<impl CastTo<$elem>, E>>,
            ) -> Result<Self, E> {
                Ok(Self {
                    interned: I::$intern(interner, elements.into_iter().casted(interner))?,
                })
            }

            /// Create a sequence from elements
            pub fn from_iter(
                interner: &I,
                elements: impl IntoIterator<Item = impl CastTo<$elem>>,
            ) -> Self {
                Self::from_fallible(
                    interner,
                    elements
                        .into_iter()
                        .map(|el| -> Result<$elem, ()> { Ok(el.cast(interner)) }),
                )
                .unwrap()
            }

            /// Create a sequence from a single element.
            pub fn from1(interner: &I, element: impl CastTo<$elem>) -> Self {
                Self::from_iter(interner, Some(element))
            }
        }
    };
}

interned_slice!(
    QuantifiedWhereClauses,
    quantified_where_clauses_data => QuantifiedWhereClause<I>,
    intern_quantified_where_clauses => InternedQuantifiedWhereClauses
);

interned_slice!(
    ProgramClauses,
    program_clauses_data => ProgramClause<I>,
    intern_program_clauses => InternedProgramClauses
);

interned_slice!(
    VariableKinds,
    variable_kinds_data => VariableKind<I>,
    intern_generic_arg_kinds => InternedVariableKinds
);

interned_slice!(
    CanonicalVarKinds,
    canonical_var_kinds_data => CanonicalVarKind<I>,
    intern_canonical_var_kinds => InternedCanonicalVarKinds
);

interned_slice!(Goals, goals_data => Goal<I>, intern_goals => InternedGoals);

interned_slice!(
    Constraints,
    constraints_data => InEnvironment<Constraint<I>>,
    intern_constraints => InternedConstraints
);

interned_slice!(
    Substitution,
    substitution_data => GenericArg<I>,
    intern_substitution => InternedSubstitution
);

interned_slice_common!(
    Variances,
    variances_data => Variance,
    intern_variance => InternedVariances
);

impl<I: Interner> Variances<I> {
    /// Tries to create a list of canonical variable kinds using an iterator.
    pub fn from_fallible<E>(
        interner: &I,
        variances: impl IntoIterator<Item = Result<Variance, E>>,
    ) -> Result<Self, E> {
        Ok(Variances {
            interned: I::intern_variances(interner, variances.into_iter())?,
        })
    }

    /// Creates a list of canonical variable kinds using an iterator.
    pub fn from_iter(interner: &I, variances: impl IntoIterator<Item = Variance>) -> Self {
        Self::from_fallible(
            interner,
            variances
                .into_iter()
                .map(|p| -> Result<Variance, ()> { Ok(p) }),
        )
        .unwrap()
    }

    /// Creates a list of canonical variable kinds from a single canonical variable kind.
    pub fn from1(interner: &I, variance: Variance) -> Self {
        Self::from_iter(interner, Some(variance))
    }
}

/// Combines a substitution (`subst`) with a set of region constraints
/// (`constraints`). This represents the result of a query; the
/// substitution stores the values for the query's unknown variables,
/// and the constraints represents any region constraints that must
/// additionally be solved.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct ConstrainedSubst<I: Interner> {
    /// The substitution that is being constrained.
    ///
    /// NB: The `is_trivial` routine relies on the fact that `subst` is folded first.
    pub subst: Substitution<I>,

    /// Region constraints that constrain the substitution.
    pub constraints: Constraints<I>,
}

/// The resulting substitution after solving a goal.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Fold, Visit, HasInterner)]
pub struct AnswerSubst<I: Interner> {
    /// The substitution result.
    ///
    /// NB: The `is_trivial` routine relies on the fact that `subst` is folded first.
    pub subst: Substitution<I>,

    /// List of constraints that are part of the answer.
    pub constraints: Constraints<I>,

    /// Delayed subgoals, used when the solver answered with an (incomplete) `Answer` (instead of a `CompleteAnswer`).
    pub delayed_subgoals: Vec<InEnvironment<Goal<I>>>,
}

/// Logic to decide the Variance for a given subst
pub trait UnificationDatabase<I>
where
    Self: std::fmt::Debug,
    I: Interner,
{
    /// Gets the variances for the substitution of a fn def
    fn fn_def_variance(&self, fn_def_id: FnDefId<I>) -> Variances<I>;

    /// Gets the variances for the substitution of a adt
    fn adt_variance(&self, adt_id: AdtId<I>) -> Variances<I>;
}
