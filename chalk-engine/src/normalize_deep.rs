use chalk_ir::fold::shift::Shift;
use chalk_ir::fold::{Fold, Folder};
use chalk_ir::interner::Interner;
use chalk_ir::*;
use chalk_solve::infer::InferenceTable;

pub(crate) struct DeepNormalizer<'table, 'i, I: Interner> {
    table: &'table mut InferenceTable<I>,
    interner: &'i I,
}

impl<I: Interner> DeepNormalizer<'_, '_, I> {
    /// Given a value `value` with variables in it, replaces those variables
    /// with their instantiated values (if any). Uninstantiated variables are
    /// left as-is.
    ///
    /// This is mainly intended for getting final values to dump to
    /// the user and its use should otherwise be avoided, particularly
    /// given the possibility of snapshots and rollbacks.
    ///
    /// See also `InferenceTable::canonicalize`, which -- during real
    /// processing -- is often used to capture the "current state" of
    /// variables.
    pub fn normalize_deep<T: Fold<I>>(
        table: &mut InferenceTable<I>,
        interner: &I,
        value: T,
    ) -> T::Result {
        value
            .fold_with(
                &mut DeepNormalizer { interner, table },
                DebruijnIndex::INNERMOST,
            )
            .unwrap()
    }
}

impl<'i, I: Interner> Folder<'i, I> for DeepNormalizer<'_, 'i, I>
where
    I: 'i,
{
    type Error = NoSolution;

    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I, Error = Self::Error> {
        self
    }

    fn fold_inference_ty(
        &mut self,
        var: InferenceVar,
        kind: TyVariableKind,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Ty<I>> {
        let interner = self.interner;
        match self.table.probe_var(var) {
            Some(ty) => Ok(ty
                .assert_ty_ref(interner)
                .clone()
                .fold_with(self, DebruijnIndex::INNERMOST)?
                .shifted_in(interner)), // FIXME shift
            None => {
                // Normalize all inference vars which have been unified into a
                // single variable. Ena calls this the "root" variable.
                Ok(self.table.inference_var_root(var).to_ty(interner, kind))
            }
        }
    }

    fn fold_inference_lifetime(
        &mut self,
        var: InferenceVar,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Lifetime<I>> {
        let interner = self.interner;
        match self.table.probe_var(var) {
            Some(l) => Ok(l
                .assert_lifetime_ref(interner)
                .clone()
                .fold_with(self, DebruijnIndex::INNERMOST)?
                .shifted_in(interner)),
            None => Ok(var.to_lifetime(interner)), // FIXME shift
        }
    }

    fn fold_inference_const(
        &mut self,
        ty: Ty<I>,
        var: InferenceVar,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Const<I>> {
        let interner = self.interner;
        match self.table.probe_var(var) {
            Some(c) => Ok(c
                .assert_const_ref(interner)
                .clone()
                .fold_with(self, DebruijnIndex::INNERMOST)?
                .shifted_in(interner)),
            None => Ok(var.to_const(interner, ty)), // FIXME shift
        }
    }

    fn forbid_free_vars(&self) -> bool {
        true
    }

    fn interner(&self) -> &'i I {
        self.interner
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use chalk_integration::interner::ChalkIr;
    use chalk_integration::{arg, ty};

    const U0: UniverseIndex = UniverseIndex { counter: 0 };

    // We just use a vec of 20 `Invariant`, since this is zipped and no substs are
    // longer than this
    #[derive(Debug)]
    struct TestDatabase;
    impl UnificationDatabase<ChalkIr> for TestDatabase {
        fn fn_def_variance(&self, _fn_def_id: FnDefId<ChalkIr>) -> Variances<ChalkIr> {
            Variances::from_iter(&ChalkIr, [Variance::Invariant; 20].iter().copied())
        }

        fn adt_variance(&self, _adt_id: AdtId<ChalkIr>) -> Variances<ChalkIr> {
            Variances::from_iter(&ChalkIr, [Variance::Invariant; 20].iter().copied())
        }
    }

    #[test]
    fn infer() {
        let interner = &ChalkIr;
        let mut table: InferenceTable<ChalkIr> = InferenceTable::new();
        let environment0 = Environment::new(interner);
        let a = table.new_variable(U0).to_ty(interner);
        let b = table.new_variable(U0).to_ty(interner);
        table
            .relate(
                interner,
                &TestDatabase,
                &environment0,
                Variance::Invariant,
                &a,
                &ty!(apply (item 0) (expr b)),
            )
            .unwrap();
        // a is unified to Adt<#0>(c), where 'c' is a new inference var
        // created by the generalizer to generalize 'b'. It then unifies 'b'
        // and 'c', and when we normalize them, they'll both be output as
        // the same "root" variable. However, there are no guarantees for
        // _which_ of 'b' and 'c' becomes the root. We need to normalize
        // "b" too, then, to ensure we get a consistent result.
        assert_eq!(
            DeepNormalizer::normalize_deep(&mut table, interner, a.clone()),
            ty!(apply (item 0) (expr DeepNormalizer::normalize_deep(&mut table, interner, b.clone()))),
        );
        table
            .relate(
                interner,
                &TestDatabase,
                &environment0,
                Variance::Invariant,
                &b,
                &ty!(apply (item 1)),
            )
            .unwrap();
        assert_eq!(
            DeepNormalizer::normalize_deep(&mut table, interner, a),
            ty!(apply (item 0) (apply (item 1)))
        );
    }
}
