use super::*;
use crate::fold::shift::Shift;

/// Substitution used during folding
pub struct Subst<'s, 'i, I: Interner> {
    /// Values to substitute. A reference to a free variable with
    /// index `i` will be mapped to `parameters[i]` -- if `i >
    /// parameters.len()`, then we will leave the variable untouched.
    parameters: &'s [GenericArg<I>],
    interner: &'i I,
}

impl<I: Interner> Subst<'_, '_, I> {
    /// Applies the substitution by folding
    pub fn apply<T: Fold<I>>(interner: &I, parameters: &[GenericArg<I>], value: T) -> T::Result {
        value
            .fold_with(
                &mut Subst {
                    parameters,
                    interner,
                },
                DebruijnIndex::INNERMOST,
            )
            .unwrap()
    }
}

impl<'i, I: Interner> Folder<'i, I> for Subst<'_, 'i, I> {
    type Error = NoSolution;

    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I, Error = Self::Error> {
        self
    }

    /// We are eliminating one binder, but binders outside of that get preserved.
    ///
    /// So e.g. consider this:
    ///
    /// ```notrust
    /// for<A, B> { for<C> { [A, C] } }
    /// //          ^ the binder we are substituing with `[u32]`
    /// ```
    ///
    /// Here, `A` would be `^1.0` and `C` would be `^0.0`. We will replace `^0.0` with the
    /// 0th index from the list (`u32`). We will convert `^1.0` (A) to `^0.0` -- i.e., shift
    /// it **out** of one level of binder (the `for<C>` binder we are eliminating).
    ///
    /// This gives us as a result:
    ///
    /// ```notrust
    /// for<A, B> { [A, u32] }
    ///              ^ represented as `^0.0`
    /// ```
    fn fold_free_var_ty(
        &mut self,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Ty<I>> {
        if let Some(index) = bound_var.index_if_innermost() {
            match self.parameters[index].data(self.interner()) {
                GenericArgData::Ty(t) => {
                    Ok(t.clone().shifted_in_from(self.interner(), outer_binder))
                }
                _ => panic!("mismatched kinds in substitution"),
            }
        } else {
            Ok(bound_var
                .shifted_out()
                .expect("cannot fail because this is not the innermost")
                .shifted_in_from(outer_binder)
                .to_ty(self.interner()))
        }
    }

    /// see `fold_free_var_ty`
    fn fold_free_var_lifetime(
        &mut self,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Lifetime<I>> {
        if let Some(index) = bound_var.index_if_innermost() {
            match self.parameters[index].data(self.interner()) {
                GenericArgData::Lifetime(l) => {
                    Ok(l.clone().shifted_in_from(self.interner(), outer_binder))
                }
                _ => panic!("mismatched kinds in substitution"),
            }
        } else {
            Ok(bound_var
                .shifted_out()
                .unwrap()
                .shifted_in_from(outer_binder)
                .to_lifetime(self.interner()))
        }
    }

    /// see `fold_free_var_ty`
    fn fold_free_var_const(
        &mut self,
        ty: Ty<I>,
        bound_var: BoundVar,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Const<I>> {
        if let Some(index) = bound_var.index_if_innermost() {
            match self.parameters[index].data(self.interner()) {
                GenericArgData::Const(c) => {
                    Ok(c.clone().shifted_in_from(self.interner(), outer_binder))
                }
                _ => panic!("mismatched kinds in substitution"),
            }
        } else {
            Ok(bound_var
                .shifted_out()
                .unwrap()
                .shifted_in_from(outer_binder)
                .to_const(self.interner(), ty))
        }
    }

    fn interner(&self) -> &'i I {
        self.interner
    }
}
