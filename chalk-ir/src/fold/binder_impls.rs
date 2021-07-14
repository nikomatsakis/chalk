//! This module contains impls of `Fold` for those types that
//! introduce binders.
//!
//! The more interesting impls of `Fold` remain in the `fold` module.

use crate::*;

impl<I: Interner> Fold<I> for FnPointer<I> {
    type Result = FnPointer<I>;
    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        let FnPointer {
            num_binders,
            substitution,
            sig,
        } = self;
        Ok(FnPointer {
            num_binders,
            substitution: substitution.fold_with(folder, outer_binder.shifted_in())?,
            sig: FnSig {
                abi: sig.abi,
                safety: sig.safety,
                variadic: sig.variadic,
            },
        })
    }
}

impl<T, I: Interner> Fold<I> for Binders<T>
where
    T: HasInterner<Interner = I> + Fold<I>,
    <T as Fold<I>>::Result: HasInterner<Interner = I>,
    I: Interner,
{
    type Result = Binders<T::Result>;
    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        let Binders {
            binders: self_binders,
            value: self_value,
        } = self;
        let value = self_value.fold_with(folder, outer_binder.shifted_in())?;
        let binders = VariableKinds {
            interned: self_binders.interned().clone(),
        };
        Ok(Binders::new(binders, value))
    }
}

impl<I, T> Fold<I> for Canonical<T>
where
    I: Interner,
    T: HasInterner<Interner = I> + Fold<I>,
    <T as Fold<I>>::Result: HasInterner<Interner = I>,
{
    type Result = Canonical<T::Result>;
    fn fold_with<'i, E>(
        self,
        folder: &mut dyn Folder<'i, I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>
    where
        I: 'i,
    {
        let Canonical {
            binders: self_binders,
            value: self_value,
        } = self;
        let value = self_value.fold_with(folder, outer_binder.shifted_in())?;
        let binders = CanonicalVarKinds {
            interned: self_binders.interned().clone(),
        };
        Ok(Canonical { binders, value })
    }
}
