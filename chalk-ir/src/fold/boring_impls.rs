//! This module contains "rote and uninteresting" impls of `Fold` for
//! various types. In general, we prefer to derive `Fold`, but
//! sometimes that doesn't work for whatever reason.
//!
//! The more interesting impls of `Fold` remain in the `fold` module.

use super::in_place;
use crate::*;
use std::marker::PhantomData;

impl<T: Fold<I>, I: Interner> Fold<I> for Vec<T> {
    type Result = Vec<T::Result>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        in_place::fallible_map_vec(self, |e| e.fold_with(folder, outer_binder))
    }
}

impl<T: Fold<I>, I: Interner> Fold<I> for Box<T> {
    type Result = Box<T::Result>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        in_place::fallible_map_box(self, |e| e.fold_with(folder, outer_binder))
    }
}

macro_rules! tuple_fold {
    ($($n:ident),*) => {
        impl<$($n: Fold<I>,)* I: Interner> Fold<I> for ($($n,)*) {
            type Result = ($($n::Result,)*);
            fn fold_with<'i>(self, folder: &mut dyn Folder<'i, I>, outer_binder: DebruijnIndex) -> Fallible<Self::Result>
            where
                I: 'i,
            {
                #[allow(non_snake_case)]
                let ($($n),*) = self;
                Ok(($($n.fold_with(folder, outer_binder)?,)*))
            }
        }
    }
}

tuple_fold!(A, B);
tuple_fold!(A, B, C);
tuple_fold!(A, B, C, D);
tuple_fold!(A, B, C, D, E);

impl<T: Fold<I>, I: Interner> Fold<I> for Option<T> {
    type Result = Option<T::Result>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        match self {
            None => Ok(None),
            Some(e) => Ok(Some(e.fold_with(folder, outer_binder)?)),
        }
    }
}

impl<I: Interner> Fold<I> for GenericArg<I> {
    type Result = GenericArg<I>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        let interner = folder.interner();

        let data = self
            .data(interner)
            .clone()
            .fold_with(folder, outer_binder)?;
        Ok(GenericArg::new(interner, data))
    }
}

impl<I: Interner> Fold<I> for Substitution<I> {
    type Result = Substitution<I>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        let interner = folder.interner();

        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Ok(Substitution::from_fallible(interner, folded)?)
    }
}

impl<I: Interner> Fold<I> for Goals<I> {
    type Result = Goals<I>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Ok(Goals::from_fallible(interner, folded)?)
    }
}

impl<I: Interner> Fold<I> for ProgramClauses<I> {
    type Result = ProgramClauses<I>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Ok(ProgramClauses::from_fallible(interner, folded)?)
    }
}

impl<I: Interner> Fold<I> for QuantifiedWhereClauses<I> {
    type Result = QuantifiedWhereClauses<I>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Ok(QuantifiedWhereClauses::from_fallible(interner, folded)?)
    }
}

impl<I: Interner> Fold<I> for Constraints<I> {
    type Result = Constraints<I>;
    fn fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<Self::Result>
    where
        I: 'i,
    {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Ok(Constraints::from_fallible(interner, folded)?)
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! copy_fold {
    ($t:ty) => {
        impl<I: Interner> $crate::fold::Fold<I> for $t {
            type Result = Self;
            fn fold_with<'i>(
                self,
                _folder: &mut dyn ($crate::fold::Folder<'i, I>),
                _outer_binder: DebruijnIndex,
            ) -> ::chalk_ir::Fallible<Self::Result>
            where
                I: 'i,
            {
                Ok(self)
            }
        }
    };
}

copy_fold!(bool);
copy_fold!(usize);
copy_fold!(UniverseIndex);
copy_fold!(PlaceholderIndex);
copy_fold!(QuantifierKind);
copy_fold!(DebruijnIndex);
copy_fold!(());
copy_fold!(UintTy);
copy_fold!(IntTy);
copy_fold!(FloatTy);
copy_fold!(Scalar);
copy_fold!(ClausePriority);
copy_fold!(Mutability);
copy_fold!(Safety);

#[doc(hidden)]
#[macro_export]
macro_rules! id_fold {
    ($t:ident) => {
        impl<I: Interner> $crate::fold::Fold<I> for $t<I> {
            type Result = $t<I>;
            fn fold_with<'i>(
                self,
                _folder: &mut dyn ($crate::fold::Folder<'i, I>),
                _outer_binder: DebruijnIndex,
            ) -> ::chalk_ir::Fallible<Self::Result>
            where
                I: 'i,
            {
                Ok(self)
            }
        }
    };
}

id_fold!(ImplId);
id_fold!(AdtId);
id_fold!(TraitId);
id_fold!(AssocTypeId);
id_fold!(AssocConstId);
id_fold!(OpaqueTyId);
id_fold!(FnDefId);
id_fold!(ClosureId);
id_fold!(GeneratorId);
id_fold!(ForeignDefId);

impl<I: Interner> SuperFold<I> for ProgramClauseData<I> {
    fn super_fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> ::chalk_ir::Fallible<Self::Result>
    where
        I: 'i,
    {
        Ok(ProgramClauseData(self.0.fold_with(folder, outer_binder)?))
    }
}

impl<I: Interner> SuperFold<I> for ProgramClause<I> {
    fn super_fold_with<'i>(
        self,
        folder: &mut dyn Folder<'i, I>,
        outer_binder: DebruijnIndex,
    ) -> ::chalk_ir::Fallible<Self::Result>
    where
        I: 'i,
    {
        let clause = self.data(folder.interner()).clone();
        Ok(clause
            .super_fold_with(folder, outer_binder)?
            .intern(folder.interner()))
    }
}

impl<I: Interner> Fold<I> for PhantomData<I> {
    type Result = PhantomData<I>;

    fn fold_with<'i>(
        self,
        _folder: &mut dyn Folder<'i, I>,
        _outer_binder: DebruijnIndex,
    ) -> ::chalk_ir::Fallible<Self::Result>
    where
        I: 'i,
    {
        Ok(PhantomData)
    }
}
