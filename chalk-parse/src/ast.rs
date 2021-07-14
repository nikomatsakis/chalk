use std::fmt;
use string_cache::DefaultAtom as Atom;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl Span {
    pub fn new(lo: usize, hi: usize) -> Self {
        Span { lo, hi }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Program {
    pub items: Vec<Item>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Item {
    AdtDefn(AdtDefn),
    FnDefn(FnDefn),
    ClosureDefn(ClosureDefn),
    TraitDefn(TraitDefn),
    OpaqueTyDefn(OpaqueTyDefn),
    GeneratorDefn(GeneratorDefn),
    Impl(Impl),
    Clause(Clause),
    Foreign(ForeignDefn),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ForeignDefn(pub Identifier);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AdtDefn {
    pub name: Identifier,
    pub variable_kinds: Vec<VariableKind>,
    pub where_clauses: Vec<QuantifiedWhereClause>,
    pub variants: Vec<Variant>,
    pub flags: AdtFlags,
    pub repr: AdtRepr,
    pub variances: Option<Vec<Variance>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Variant {
    pub name: Identifier,
    pub fields: Vec<Field>,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Movability {
    Static,
    Movable,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GeneratorDefn {
    pub name: Identifier,
    pub movability: Movability,
    pub variable_kinds: Vec<VariableKind>,
    pub upvars: Vec<Ty>,
    pub resume_ty: Ty,
    pub yield_ty: Ty,
    pub return_ty: Ty,
    pub witness_types: Vec<Ty>,
    pub witness_lifetimes: Vec<Identifier>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AdtFlags {
    pub upstream: bool,
    pub fundamental: bool,
    pub phantom_data: bool,
    pub kind: AdtKind,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum AdtKind {
    Struct,
    Enum,
    Union,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AdtReprAttr {
    C,
    Packed,
    Int(Ty),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AdtRepr {
    pub c: bool,
    pub packed: bool,
    pub int: Option<Ty>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FnSig {
    pub abi: FnAbi,
    pub safety: Safety,
    pub variadic: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FnDefn {
    pub name: Identifier,
    pub variable_kinds: Vec<VariableKind>,
    pub where_clauses: Vec<QuantifiedWhereClause>,
    pub argument_types: Vec<Ty>,
    pub return_type: Ty,
    pub sig: FnSig,
    pub variances: Option<Vec<Variance>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ClosureDefn {
    pub name: Identifier,
    pub kind: ClosureKind,
    pub variable_kinds: Vec<VariableKind>,
    pub argument_types: Vec<Ty>,
    pub return_type: Ty,
    pub upvars: Vec<Ty>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FnAbi(pub Atom);

impl Default for FnAbi {
    fn default() -> Self {
        FnAbi(Atom::from("Rust"))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TraitDefn {
    pub name: Identifier,
    pub variable_kinds: Vec<VariableKind>,
    pub where_clauses: Vec<QuantifiedWhereClause>,
    pub assoc_item_defns: Vec<AssocItemDefn>,
    pub flags: TraitFlags,
    pub well_known: Option<WellKnownTrait>,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum WellKnownTrait {
    Sized,
    Copy,
    Clone,
    Drop,
    FnOnce,
    FnMut,
    Fn,
    Unsize,
    Unpin,
    CoerceUnsized,
    DiscriminantKind,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TraitFlags {
    pub auto: bool,
    pub marker: bool,
    pub upstream: bool,
    pub fundamental: bool,
    pub non_enumerable: bool,
    pub coinductive: bool,
    pub object_safe: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AssocItemDefn {
    Ty(AssocTyDefn),
    Const(AssocConstDefn),
}

impl AssocItemDefn {
    /// Returns the type value if it is one, `None` otherwise.
    pub fn ty(&self) -> Option<&AssocTyDefn> {
        match self {
            AssocItemDefn::Ty(ty) => Some(ty),
            _ => None,
        }
    }

    /// Returns the const value if it is one, `None` otherwise.
    pub fn const_(&self) -> Option<&AssocConstDefn> {
        match self {
            AssocItemDefn::Const(c) => Some(c),
            _ => None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssocTyDefn {
    pub name: Identifier,
    pub variable_kinds: Vec<VariableKind>,
    pub bounds: Vec<QuantifiedInlineBound>,
    pub where_clauses: Vec<QuantifiedWhereClause>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssocConstDefn {
    pub name: Identifier,
    pub ty: Ty,
    pub value: Option<Const>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OpaqueTyDefn {
    pub ty: Ty,
    pub variable_kinds: Vec<VariableKind>,
    pub name: Identifier,
    pub bounds: Vec<QuantifiedInlineBound>,
    pub where_clauses: Vec<QuantifiedWhereClause>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum VariableKind {
    Ty(Identifier),
    IntegerTy(Identifier),
    FloatTy(Identifier),
    Lifetime(Identifier),
    Const(Identifier),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Lifetime),
    Id(Identifier),
    Const(Const),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Const {
    Id(Identifier),
    Value(u32),
}

#[derive(Clone, PartialEq, Eq, Debug)]
/// An inline bound, e.g. `: Foo<K>` in `impl<K, T: Foo<K>> SomeType<T>`.
pub enum InlineBound {
    TraitBound(TraitBound),
    AliasEqBound(AliasEqBound),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct QuantifiedInlineBound {
    pub variable_kinds: Vec<VariableKind>,
    pub bound: InlineBound,
}

#[derive(Clone, PartialEq, Eq, Debug)]
/// Represents a trait bound on e.g. a type or type parameter.
/// Does not know anything about what it's binding.
pub struct TraitBound {
    pub trait_name: Identifier,
    pub args_no_self: Vec<GenericArg>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
/// Represents an alias equality bound on e.g. a type or type parameter.
/// Does not know anything about what it's binding.
pub struct AliasEqBound {
    pub trait_bound: TraitBound,
    pub name: Identifier,
    pub args: Vec<GenericArg>,
    pub value: Ty,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Kind {
    Ty,
    Lifetime,
    Const,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match *self {
            Kind::Ty => "type",
            Kind::Lifetime => "lifetime",
            Kind::Const => "const",
        })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Impl {
    pub variable_kinds: Vec<VariableKind>,
    pub trait_ref: TraitRef,
    pub polarity: Polarity,
    pub where_clauses: Vec<QuantifiedWhereClause>,
    pub assoc_item_values: Vec<AssocItemValue>,
    pub impl_type: ImplType,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ImplType {
    Local,
    External,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AssocItemValue {
    Ty(AssocTyValue),
    Const(AssocConstValue),
}

impl AssocItemValue {
    /// Returns the type value if it is one, `None` otherwise.
    pub fn ty(&self) -> Option<&AssocTyValue> {
        match self {
            AssocItemValue::Ty(ty) => Some(ty),
            _ => None,
        }
    }

    /// Returns the type value if it is one, `None` otherwise.
    pub fn const_(&self) -> Option<&AssocConstValue> {
        match self {
            AssocItemValue::Const(c) => Some(c),
            _ => None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssocTyValue {
    pub name: Identifier,
    pub variable_kinds: Vec<VariableKind>,
    pub value: Ty,
    pub default: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssocConstValue {
    pub name: Identifier,
    pub ty: Ty,
    pub value: Const,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Id {
        name: Identifier,
    },
    Dyn {
        bounds: Vec<QuantifiedInlineBound>,
        lifetime: Lifetime,
    },
    Apply {
        name: Identifier,
        args: Vec<GenericArg>,
    },
    Projection {
        proj: ProjectionTy,
    },
    ForAll {
        lifetime_names: Vec<Identifier>,
        types: Vec<Box<Ty>>,
        sig: FnSig,
    },
    Tuple {
        types: Vec<Box<Ty>>,
    },
    Scalar {
        ty: ScalarType,
    },
    Slice {
        ty: Box<Ty>,
    },
    Array {
        ty: Box<Ty>,
        len: Const,
    },
    Raw {
        mutability: Mutability,
        ty: Box<Ty>,
    },
    Ref {
        mutability: Mutability,
        lifetime: Lifetime,
        ty: Box<Ty>,
    },
    Str,
    Never,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum FloatTy {
    F32,
    F64,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ScalarType {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Mutability {
    Mut,
    Not,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Safety {
    Safe,
    Unsafe,
}

impl Default for Safety {
    fn default() -> Self {
        Self::Safe
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Lifetime {
    Id { name: Identifier },
    Static,
    Erased,
    Empty,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ProjectionTy {
    pub trait_ref: TraitRef,
    pub name: Identifier,
    pub args: Vec<GenericArg>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TraitRef {
    pub trait_name: Identifier,
    pub args: Vec<GenericArg>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Polarity {
    /// `impl Foo for Bar`
    Positive,

    /// `impl !Foo for Bar`
    Negative,
}

impl Polarity {
    pub fn from_bool(polarity: bool) -> Polarity {
        if polarity {
            Polarity::Positive
        } else {
            Polarity::Negative
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Identifier {
    pub str: Atom,
    pub span: Span,
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum WhereClause {
    Implemented { trait_ref: TraitRef },
    ProjectionEq { projection: ProjectionTy, ty: Ty },
    LifetimeOutlives { a: Lifetime, b: Lifetime },
    TypeOutlives { ty: Ty, lifetime: Lifetime },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DomainGoal {
    Holds { where_clause: WhereClause },
    Normalize { projection: ProjectionTy, ty: Ty },
    TraitRefWellFormed { trait_ref: TraitRef },
    TyWellFormed { ty: Ty },
    TyFromEnv { ty: Ty },
    TraitRefFromEnv { trait_ref: TraitRef },
    IsLocal { ty: Ty },
    IsUpstream { ty: Ty },
    IsFullyVisible { ty: Ty },
    LocalImplAllowed { trait_ref: TraitRef },
    Compatible,
    DownstreamType { ty: Ty },
    Reveal,
    ObjectSafe { id: Identifier },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LeafGoal {
    DomainGoal { goal: DomainGoal },
    UnifyGenericArgs { a: GenericArg, b: GenericArg },
    SubtypeGenericArgs { a: Ty, b: Ty },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct QuantifiedWhereClause {
    pub variable_kinds: Vec<VariableKind>,
    pub where_clause: WhereClause,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Field {
    pub name: Identifier,
    pub ty: Ty,
}

#[derive(Clone, PartialEq, Eq, Debug)]
/// This allows users to add arbitrary `A :- B` clauses into the
/// logic; it has no equivalent in Rust, but it's useful for testing.
pub struct Clause {
    pub variable_kinds: Vec<VariableKind>,
    pub consequence: DomainGoal,
    pub conditions: Vec<Box<Goal>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Goal {
    ForAll(Vec<VariableKind>, Box<Goal>),
    Exists(Vec<VariableKind>, Box<Goal>),
    Implies(Vec<Clause>, Box<Goal>),
    And(Box<Goal>, Vec<Box<Goal>>),
    Not(Box<Goal>),

    /// The `compatible { G }` syntax
    Compatible(Box<Goal>),

    // Additional kinds of goals:
    Leaf(LeafGoal),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FnArg {
    NonVariadic(Ty),
    Variadic,
}
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FnArgs {
    NonVariadic(Vec<Ty>),
    Variadic(Vec<Ty>),
}

impl FnArgs {
    pub fn is_variadic(&self) -> bool {
        match self {
            Self::Variadic(..) => true,
            _ => false,
        }
    }

    pub fn to_tys(self) -> Vec<Ty> {
        match self {
            Self::NonVariadic(tys) | Self::Variadic(tys) => tys,
        }
    }

    pub fn from_vec(mut args: Vec<FnArg>) -> Result<Self, &'static str> {
        let mut tys = Vec::with_capacity(args.len());
        let last = args.pop();
        for arg in args {
            match arg {
                FnArg::NonVariadic(ty) => tys.push(ty),
                FnArg::Variadic => {
                    return Err("a variadic argument must be the last parameter in a function");
                }
            }
        }

        Ok(match last {
            Some(FnArg::NonVariadic(ty)) => {
                tys.push(ty);
                FnArgs::NonVariadic(tys)
            }
            Some(FnArg::Variadic) => FnArgs::Variadic(tys),
            None => FnArgs::NonVariadic(tys),
        })
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Variance {
    Invariant,
    Covariant,
    Contravariant,
}
