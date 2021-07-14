//! This module contains impls of `Visit` for those types that
//! introduce binders.
//!
//! The more interesting impls of `Visit` remain in the `visit` module.

use crate::interner::HasInterner;
use crate::{Binders, Canonical, ControlFlow, DebruijnIndex, FnPointer, Interner, Visit, Visitor};

impl<I: Interner> Visit<I> for FnPointer<I> {
    fn visit_with<'i, B>(
        &self,
        visitor: &mut dyn Visitor<'i, I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>
    where
        I: 'i,
    {
        visitor.before_fn_pointer_substs(self.num_binders);
        let result = self
            .substitution
            .visit_with(visitor, outer_binder.shifted_in());
        visitor.after_any_binders();
        result
    }
}

impl<T, I: Interner> Visit<I> for Binders<T>
where
    T: HasInterner<Interner = I> + Visit<I>,
{
    fn visit_with<'i, B>(
        &self,
        visitor: &mut dyn Visitor<'i, I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>
    where
        I: 'i,
    {
        visitor.before_binders(&self.binders);
        let result = self.value.visit_with(visitor, outer_binder.shifted_in());
        visitor.after_any_binders();
        result
    }
}

impl<I, T> Visit<I> for Canonical<T>
where
    I: Interner,
    T: HasInterner<Interner = I> + Visit<I>,
{
    fn visit_with<'i, B>(
        &self,
        visitor: &mut dyn Visitor<'i, I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>
    where
        I: 'i,
    {
        visitor.before_canonical(&self.binders);
        let result = self.value.visit_with(visitor, outer_binder.shifted_in());
        visitor.after_any_binders();
        result
    }
}
