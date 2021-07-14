//! Traits for transforming bits of IR.

use crate::*;
use std::fmt::Debug;

mod binder_impls;
mod boring_impls;
mod in_place;
pub mod shift;
mod subst;

pub use self::shift::Shift;
pub use self::subst::Subst;

/// A "folder" is a transformer that can be used to make a copy of
/// some term -- that is, some bit of IR, such as a `Goal` -- with
/// certain changes applied. The idea is that it contains methods that
/// let you swap types/lifetimes for new types/lifetimes; meanwhile,
/// each bit of IR implements the `Fold` trait which, given a
/// `Folder`, will reconstruct itself, invoking the folder's methods
/// to transform each of the types/lifetimes embedded within.
///
/// # Usage patterns
///
/// ## Substituting for free variables
///
/// Most of the time, though, we are not interested in adjust
/// arbitrary types/lifetimes, but rather just free variables (even
/// more often, just free existential variables) that appear within
/// the term.
///
/// For this reason, the `Folder` trait extends two other traits that
/// contain methods that are invoked when just those particular
///
/// In particular, folders can intercept references to free variables
/// (either existentially or universally quantified) and replace them
/// with other types/lifetimes as appropriate.
///
/// To create a folder `F`, one never implements `Folder` directly, but instead
/// implements one of each of these three sub-traits:
///
/// - `FreeVarFolder` -- folds `BoundVar` instances that appear free
///   in the term being folded (use `DefaultFreeVarFolder` to
///   ignore/forbid these altogether)
/// - `InferenceFolder` -- folds existential `InferenceVar` instances
///   that appear in the term being folded (use
///   `DefaultInferenceFolder` to ignore/forbid these altogether)
/// - `PlaceholderFolder` -- folds universal `Placeholder` instances
///   that appear in the term being folded (use
///   `DefaultPlaceholderFolder` to ignore/forbid these altogether)
///
/// To **apply** a folder, use the `Fold::fold_with` method, like so
///
/// ```rust,ignore
/// let x = x.fold_with(&mut folder, 0);
/// ```
pub trait Folder<'i, I: Interner>
where
    I: 'i,
{
    /// The type this folder returns when folding fails. This is
    /// commonly [`NoSolution`].
    type Error;

    /// Creates a `dyn` value from this folder. Unfortunately, this
    /// must be added manually to each impl of Folder; it permits the
    /// default implements below to create a `&mut dyn Folder` from
    /// `Self` without knowing what `Self` is (by invoking this
    /// method). Effectively, this limits impls of `Folder` to types
    /// for which we are able to create a dyn value (i.e., not `[T]`
    /// types).
    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I, Error = Self::Error>;

    /// Top-level callback: invoked for each `Ty<I>` that is
    /// encountered when folding. By default, invokes
    /// `super_fold_with`, which will in turn invoke the more
    /// specialized folding methods below, like `fold_free_var_ty`.
    fn fold_ty(&mut self, ty: Ty<I>, outer_binder: DebruijnIndex) -> Result<Ty<I>, Self::Error> {
        ty.super_fold_with(self.as_dyn(), outer_binder)
    }

    /// Top-level callback: invoked for each `Lifetime<I>` that is
    /// encountered when folding. By default, invokes
    /// `super_fold_with`, which will in turn invoke the more
    /// specialized folding methods below, like `fold_free_var_lifetime`.
    fn fold_lifetime(
        &mut self,
        lifetime: Lifetime<I>,
        outer_binder: DebruijnIndex,
    ) -> Result<Lifetime<I>, Self::Error> {
        lifetime.super_fold_with(self.as_dyn(), outer_binder)
    }

    /// Top-level callback: invoked for each `Const<I>` that is
    /// encountered when folding. By default, invokes
    /// `super_fold_with`, which will in turn invoke the more
    /// specialized folding methods below, like `fold_free_var_const`.
    fn fold_const(
        &mut self,
        constant: Const<I>,
        outer_binder: DebruijnIndex,
    ) -> Result<Const<I>, Self::Error> {
        constant.super_fold_with(self.as_dyn(), outer_binder)
    }

    /// Invoked for every program clause. By default, recursively folds the goals contents.
    fn fold_program_clause(
        &mut self,
        clause: ProgramClause<I>,
        outer_binder: DebruijnIndex,
    ) -> Result<ProgramClause<I>, Self::Error> {
        clause.super_fold_with(self.as_dyn(), outer_binder)
    }

    /// Invoked for every goal. By default, recursively folds the goals contents.
    fn fold_goal(
        &mut self,
        goal: Goal<I>,
        outer_binder: DebruijnIndex,
    ) -> Result<Goal<I>, Self::Error> {
        goal.super_fold_with(self.as_dyn(), outer_binder)
    }

    /// If overridden to return true, then folding will panic if a
    /// free variable is encountered. This should be done if free
    /// type/lifetime variables are not expected.
    fn forbid_free_vars(&self) -> bool {
        false
    }

    /// Invoked for `TyKind::BoundVar` instances that are not bound
    /// within the type being folded over:
    ///
    /// - `depth` is the depth of the `TyKind::BoundVar`; this has
    ///   been adjusted to account for binders in scope.
    /// - `binders` is the number of binders in scope.
    ///
    /// This should return a type suitable for a context with
    /// `binders` in scope.
    fn fold_free_var_ty(
        &mut self,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Result<Ty<I>, Self::Error> {
        if self.forbid_free_vars() {
            panic!(
                "unexpected free variable with depth `{:?}` with outer binder {:?}",
                bound_var, outer_binder
            )
        } else {
            let bound_var = bound_var.shifted_in_from(outer_binder);
            Ok(TyKind::<I>::BoundVar(bound_var).intern(self.interner()))
        }
    }

    /// As `fold_free_var_ty`, but for lifetimes.
    fn fold_free_var_lifetime(
        &mut self,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Result<Lifetime<I>, Self::Error> {
        if self.forbid_free_vars() {
            panic!(
                "unexpected free variable with depth `{:?}` with outer binder {:?}",
                bound_var, outer_binder
            )
        } else {
            let bound_var = bound_var.shifted_in_from(outer_binder);
            Ok(LifetimeData::<I>::BoundVar(bound_var).intern(self.interner()))
        }
    }

    /// As `fold_free_var_ty`, but for constants.
    fn fold_free_var_const(
        &mut self,
        ty: Ty<I>,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Result<Const<I>, Self::Error> {
        if self.forbid_free_vars() {
            panic!(
                "unexpected free variable with depth `{:?}` with outer binder {:?}",
                bound_var, outer_binder
            )
        } else {
            let bound_var = bound_var.shifted_in_from(outer_binder);
            Ok(ConstData {
                ty: ty.clone().fold_with(self.as_dyn(), outer_binder)?,
                value: ConstValue::<I>::BoundVar(bound_var),
            }
            .intern(self.interner()))
        }
    }

    /// If overridden to return true, we will panic when a free
    /// placeholder type/lifetime/const is encountered.
    fn forbid_free_placeholders(&self) -> bool {
        false
    }

    /// Invoked for each occurrence of a placeholder type; these are
    /// used when we instantiate binders universally. Returns a type
    /// to use instead, which should be suitably shifted to account
    /// for `binders`.
    ///
    /// - `universe` is the universe of the `TypeName::ForAll` that was found
    /// - `binders` is the number of binders in scope
    #[allow(unused_variables)]
    fn fold_free_placeholder_ty(
        &mut self,
        universe: PlaceholderIndex,
        outer_binder: DebruijnIndex,
    ) -> Result<Ty<I>, Self::Error> {
        if self.forbid_free_placeholders() {
            panic!("unexpected placeholder type `{:?}`", universe)
        } else {
            Ok(universe.to_ty::<I>(self.interner()))
        }
    }

    /// As with `fold_free_placeholder_ty`, but for lifetimes.
    #[allow(unused_variables)]
    fn fold_free_placeholder_lifetime(
        &mut self,
        universe: PlaceholderIndex,
        outer_binder: DebruijnIndex,
    ) -> Result<Lifetime<I>, Self::Error> {
        if self.forbid_free_placeholders() {
            panic!("unexpected placeholder lifetime `{:?}`", universe)
        } else {
            Ok(universe.to_lifetime(self.interner()))
        }
    }

    /// As with `fold_free_placeholder_ty`, but for constants.
    #[allow(unused_variables)]
    fn fold_free_placeholder_const(
        &mut self,
        ty: Ty<I>,
        universe: PlaceholderIndex,
        outer_binder: DebruijnIndex,
    ) -> Result<Const<I>, Self::Error> {
        if self.forbid_free_placeholders() {
            panic!("unexpected placeholder const `{:?}`", universe)
        } else {
            Ok(universe.to_const(self.interner(), ty.fold_with(self.as_dyn(), outer_binder)?))
        }
    }

    /// If overridden to return true, inference variables will trigger
    /// panics when folded. Used when inference variables are
    /// unexpected.
    fn forbid_inference_vars(&self) -> bool {
        false
    }

    /// Invoked for each occurrence of a inference type; these are
    /// used when we instantiate binders universally. Returns a type
    /// to use instead, which should be suitably shifted to account
    /// for `binders`.
    ///
    /// - `universe` is the universe of the `TypeName::ForAll` that was found
    /// - `binders` is the number of binders in scope
    #[allow(unused_variables)]
    fn fold_inference_ty(
        &mut self,
        var: InferenceVar,
        kind: TyVariableKind,
        outer_binder: DebruijnIndex,
    ) -> Result<Ty<I>, Self::Error> {
        if self.forbid_inference_vars() {
            panic!("unexpected inference type `{:?}`", var)
        } else {
            Ok(var.to_ty(self.interner(), kind))
        }
    }

    /// As with `fold_inference_ty`, but for lifetimes.
    #[allow(unused_variables)]
    fn fold_inference_lifetime(
        &mut self,
        var: InferenceVar,
        outer_binder: DebruijnIndex,
    ) -> Result<Lifetime<I>, Self::Error> {
        if self.forbid_inference_vars() {
            panic!("unexpected inference lifetime `'{:?}`", var)
        } else {
            Ok(var.to_lifetime(self.interner()))
        }
    }

    /// As with `fold_inference_ty`, but for constants.
    #[allow(unused_variables)]
    fn fold_inference_const(
        &mut self,
        ty: Ty<I>,
        var: InferenceVar,
        outer_binder: DebruijnIndex,
    ) -> Result<Const<I>, Self::Error> {
        if self.forbid_inference_vars() {
            panic!("unexpected inference const `{:?}`", var)
        } else {
            Ok(var.to_const(self.interner(), ty.fold_with(self.as_dyn(), outer_binder)?))
        }
    }

    /// Gets the interner that is being folded from.
    fn interner(&self) -> &'i I;
}

/// Applies the given `Folder` to a value, producing a folded result
/// of type `Self::Result`. The result type is typically the same as
/// the source type, but in some cases we convert from borrowed
/// to owned as well (e.g., the folder for `&T` will fold to a fresh
/// `T`; well, actually `T::Result`).
pub trait Fold<I: Interner>: Debug {
    /// The type of value that will be produced once folding is done.
    /// Typically this is `Self`, unless `Self` contains borrowed
    /// values, in which case owned values are produced (for example,
    /// one can fold over a `&T` value where `T: Fold`, in which case
    /// you get back a `T`, not a `&T`).
    type Result;

    /// Apply the given folder `folder` to `self`; `binders` is the
    /// number of binders that are in scope when beginning the
    /// folder. Typically `binders` starts as 0, but is adjusted when
    /// we encounter `Binders<T>` in the IR or other similar
    /// constructs.
    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i;
}

/// For types where "fold" invokes a callback on the `Folder`, the
/// `SuperFold` trait captures the recursive behavior that folds all
/// the contents of the type.
pub trait SuperFold<I: Interner>: Fold<I> {
    /// Recursively folds the value.
    fn super_fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i;
}

/// "Folding" a type invokes the `fold_ty` method on the folder; this
/// usually (in turn) invokes `super_fold_ty` to fold the individual
/// parts.
impl<I: Interner> Fold<I> for Ty<I> {
    type Result = Ty<I>;

    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        folder.fold_ty(self, outer_binder)
    }
}

/// "Super fold" for a type invokes te more detailed callbacks on the type
impl<I> SuperFold<I> for Ty<I>
where
    I: Interner,
{
    fn super_fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Ty<I>, E>
    where
        I: 'i,
    {
        let interner = folder.interner();
        Ok(match self.kind(interner) {
            TyKind::BoundVar(bound_var) => {
                if let Some(bound_var1) = bound_var.shifted_out_to(outer_binder) {
                    // This variable was bound outside of the binders
                    // that we have traversed during folding;
                    // therefore, it is free. Let the folder have a
                    // crack at it.
                    folder.fold_free_var_ty(bound_var1, outer_binder)?
                } else {
                    // This variable was bound within the binders that
                    // we folded over, so just return a bound
                    // variable.
                    self
                }
            }
            TyKind::Dyn(clauses) => TyKind::Dyn(clauses.clone().fold_with(folder, outer_binder)?)
                .intern(folder.interner()),
            TyKind::InferenceVar(var, kind) => {
                folder.fold_inference_ty(*var, *kind, outer_binder)?
            }
            TyKind::Placeholder(ui) => folder.fold_free_placeholder_ty(*ui, outer_binder)?,
            TyKind::Alias(proj) => TyKind::Alias(proj.clone().fold_with(folder, outer_binder)?)
                .intern(folder.interner()),
            TyKind::Function(fun) => TyKind::Function(fun.clone().fold_with(folder, outer_binder)?)
                .intern(folder.interner()),
            TyKind::Adt(id, substitution) => TyKind::Adt(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::AssociatedType(assoc_ty, substitution) => TyKind::AssociatedType(
                assoc_ty.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Scalar(scalar) => {
                TyKind::Scalar(scalar.fold_with(folder, outer_binder)?).intern(folder.interner())
            }
            TyKind::Str => TyKind::Str.intern(folder.interner()),
            TyKind::Tuple(arity, substitution) => TyKind::Tuple(
                *arity,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::OpaqueType(opaque_ty, substitution) => TyKind::OpaqueType(
                opaque_ty.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Slice(substitution) => {
                TyKind::Slice(substitution.clone().fold_with(folder, outer_binder)?)
                    .intern(folder.interner())
            }
            TyKind::FnDef(fn_def, substitution) => TyKind::FnDef(
                fn_def.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Ref(mutability, lifetime, ty) => TyKind::Ref(
                mutability.fold_with(folder, outer_binder)?,
                lifetime.clone().fold_with(folder, outer_binder)?,
                ty.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Raw(mutability, ty) => TyKind::Raw(
                mutability.fold_with(folder, outer_binder)?,
                ty.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Never => TyKind::Never.intern(folder.interner()),
            TyKind::Array(ty, const_) => TyKind::Array(
                ty.clone().fold_with(folder, outer_binder)?,
                const_.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Closure(id, substitution) => TyKind::Closure(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Generator(id, substitution) => TyKind::Generator(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::GeneratorWitness(id, substitution) => TyKind::GeneratorWitness(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Foreign(id) => {
                TyKind::Foreign(id.fold_with(folder, outer_binder)?).intern(folder.interner())
            }
            TyKind::Error => TyKind::Error.intern(folder.interner()),
        })
    }
}

/// "Folding" a lifetime invokes the `fold_lifetime` method on the folder; this
/// usually (in turn) invokes `super_fold_lifetime` to fold the individual
/// parts.
impl<I: Interner> Fold<I> for Lifetime<I> {
    type Result = Lifetime<I>;

    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        folder.fold_lifetime(self, outer_binder)
    }
}

impl<I> SuperFold<I> for Lifetime<I>
where
    I: Interner,
{
    fn super_fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Lifetime<I>, E>
    where
        I: 'i,
    {
        let interner = folder.interner();
        match self.data(interner) {
            LifetimeData::BoundVar(bound_var) => {
                if let Some(bound_var1) = bound_var.shifted_out_to(outer_binder) {
                    // This variable was bound outside of the binders
                    // that we have traversed during folding;
                    // therefore, it is free. Let the folder have a
                    // crack at it.
                    folder.fold_free_var_lifetime(bound_var1, outer_binder)
                } else {
                    // This variable was bound within the binders that
                    // we folded over, so just return a bound
                    // variable.
                    Ok(self)
                }
            }
            LifetimeData::InferenceVar(var) => folder.fold_inference_lifetime(*var, outer_binder),
            LifetimeData::Placeholder(universe) => {
                folder.fold_free_placeholder_lifetime(*universe, outer_binder)
            }
            LifetimeData::Static => Ok(LifetimeData::<I>::Static.intern(folder.interner())),
            LifetimeData::Empty(ui) => Ok(LifetimeData::<I>::Empty(*ui).intern(folder.interner())),
            LifetimeData::Erased => Ok(LifetimeData::<I>::Erased.intern(folder.interner())),
            LifetimeData::Phantom(void, ..) => match *void {},
        }
    }
}

/// "Folding" a const invokes the `fold_const` method on the folder; this
/// usually (in turn) invokes `super_fold_const` to fold the individual
/// parts.
impl<I: Interner> Fold<I> for Const<I> {
    type Result = Const<I>;

    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        folder.fold_const(self, outer_binder)
    }
}

impl<I> SuperFold<I> for Const<I>
where
    I: Interner,
{
    fn super_fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Const<I>, E>
    where
        I: 'i,
    {
        let interner = folder.interner();
        let ConstData { ref ty, ref value } = self.data(interner);
        let mut fold_ty = || ty.clone().fold_with(folder, outer_binder);
        match value {
            ConstValue::BoundVar(bound_var) => {
                if let Some(bound_var1) = bound_var.shifted_out_to(outer_binder) {
                    folder.fold_free_var_const(ty.clone(), bound_var1, outer_binder)
                } else {
                    Ok(self)
                }
            }
            ConstValue::InferenceVar(var) => {
                folder.fold_inference_const(ty.clone(), *var, outer_binder)
            }
            ConstValue::Placeholder(universe) => {
                folder.fold_free_placeholder_const(ty.clone(), *universe, outer_binder)
            }
            ConstValue::Concrete(ev) => Ok(ConstData {
                ty: fold_ty()?,
                value: ConstValue::Concrete(ConcreteConst {
                    interned: ev.interned.clone(),
                }),
            }
            .intern(folder.interner())),
        }
    }
}

/// Folding a goal invokes the `fold_goal` callback (which will, by
/// default, invoke super-fold).
impl<I: Interner> Fold<I> for Goal<I> {
    type Result = Goal<I>;

    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        folder.fold_goal(self, outer_binder)
    }
}

/// Superfold folds recursively.
impl<I: Interner> SuperFold<I> for Goal<I> {
    fn super_fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        let interner = folder.interner();
        Ok(Goal::new(
            interner,
            self.data(interner)
                .clone()
                .fold_with(folder, outer_binder)?,
        ))
    }
}

/// Folding a program clause invokes the `fold_program_clause`
/// callback on the folder (which will, by default, invoke the
/// `super_fold_with` method on the program clause).
impl<I: Interner> Fold<I> for ProgramClause<I> {
    type Result = ProgramClause<I>;

    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        folder.fold_program_clause(self, outer_binder)
    }
}
