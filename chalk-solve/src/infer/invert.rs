use chalk_ir::fold::shift::Shift;
use chalk_ir::fold::{Fold, Folder};
use chalk_ir::interner::HasInterner;
use chalk_ir::interner::Interner;
use chalk_ir::*;
use rustc_hash::FxHashMap;

use super::canonicalize::Canonicalized;
use super::{EnaVariable, InferenceTable};

impl<I: Interner> InferenceTable<I> {
    /// Converts `value` into a "negation" value -- meaning one that,
    /// if we can find any answer to it, then the negation fails. For
    /// goals that do not contain any free variables, then this is a
    /// no-op operation.
    ///
    /// If `value` contains any existential variables that have not
    /// yet been assigned a value, then this function will return
    /// `None`, indicating that we cannot prove negation for this goal
    /// yet.  This follows the approach in Clark's original
    /// negation-as-failure paper [1], where negative goals are only
    /// permitted if they contain no free (existential) variables.
    ///
    /// [1] https://www.doc.ic.ac.uk/~klc/NegAsFailure.pdf
    ///
    /// Restricting free existential variables is done because the
    /// semantics of such queries is not what you expect: it basically
    /// treats the existential as a universal. For example, consider:
    ///
    /// ```rust,ignore
    /// struct Vec<T> {}
    /// struct i32 {}
    /// struct u32 {}
    /// trait Foo {}
    /// impl Foo for Vec<u32> {}
    /// ```
    ///
    /// If we ask `exists<T> { not { Vec<T>: Foo } }`, what should happen?
    /// If we allow negative queries to be definitively answered even when
    /// they contain free variables, we will get a definitive *no* to the
    /// entire goal! From a logical perspective, that's just wrong: there
    /// does exists a `T` such that `not { Vec<T>: Foo }`, namely `i32`. The
    /// problem is that the proof search procedure is actually trying to
    /// prove something stronger, that there is *no* such `T`.
    ///
    /// An additional complication arises around free universal
    /// variables.  Consider a query like `not { !0 = !1 }`, where
    /// `!0` and `!1` are placeholders for universally quantified
    /// types (i.e., `TyKind::Placeholder`). If we just tried to
    /// prove `!0 = !1`, we would get false, because those types
    /// cannot be unified -- this would then allow us to conclude that
    /// `not { !0 = !1 }`, i.e., `forall<X, Y> { not { X = Y } }`, but
    /// this is clearly not true -- what if X were to be equal to Y?
    ///
    /// Interestingly, the semantics of existential variables turns
    /// out to be exactly what we want here. So, in addition to
    /// forbidding existential variables in the original query, the
    /// `negated` query also converts all universals *into*
    /// existentials. Hence `negated` applies to `!0 = !1` would yield
    /// `exists<X,Y> { X = Y }` (note that a canonical, i.e. closed,
    /// result is returned). Naturally this has a solution, and hence
    /// `not { !0 = !1 }` fails, as we expect.
    ///
    /// (One could imagine converting free existentials into
    /// universals, rather than forbidding them altogether. This would
    /// be conceivable, but overly strict. For example, the goal
    /// `exists<T> { not { ?T: Clone }, ?T = Vec<i32> }` would come
    /// back as false, when clearly this is true. This is because we
    /// would wind up proving that `?T: Clone` can *never* be
    /// satisfied (which is false), when we only really care about
    /// `?T: Clone` in the case where `?T = Vec<i32>`. The current
    /// version would delay processing the negative goal (i.e., return
    /// `None`) until the second unification has occurred.)
    pub fn invert<T>(&mut self, interner: &I, value: T) -> Option<T::Result>
    where
        T: Fold<I, Result = T> + HasInterner<Interner = I>,
    {
        let Canonicalized {
            free_vars,
            quantified,
            ..
        } = self.canonicalize(interner, value);

        // If the original contains free existential variables, give up.
        if !free_vars.is_empty() {
            return None;
        }

        // If this contains free universal variables, replace them with existentials.
        assert!(quantified.binders.is_empty(interner));
        let inverted = quantified
            .value
            .fold_with(&mut Inverter::new(interner, self), DebruijnIndex::INNERMOST)
            .unwrap();
        Some(inverted)
    }

    /// As `negated_instantiated`, but canonicalizes before
    /// returning. Just a convenience function.
    pub fn invert_then_canonicalize<T>(
        &mut self,
        interner: &I,
        value: T,
    ) -> Option<Canonical<T::Result>>
    where
        T: Fold<I, Result = T> + HasInterner<Interner = I>,
    {
        let snapshot = self.snapshot();
        let result = self.invert(interner, value);
        let result = result.map(|r| self.canonicalize(interner, r).quantified);
        self.rollback_to(snapshot);
        result
    }
}

struct Inverter<'q, I: Interner> {
    table: &'q mut InferenceTable<I>,
    inverted_ty: FxHashMap<PlaceholderIndex, EnaVariable<I>>,
    inverted_lifetime: FxHashMap<PlaceholderIndex, EnaVariable<I>>,
    interner: &'q I,
}

impl<'q, I: Interner> Inverter<'q, I> {
    fn new(interner: &'q I, table: &'q mut InferenceTable<I>) -> Self {
        Inverter {
            table,
            inverted_ty: FxHashMap::default(),
            inverted_lifetime: FxHashMap::default(),
            interner,
        }
    }
}

impl<'i, I: Interner> Folder<'i, I> for Inverter<'i, I>
where
    I: 'i,
{
    type Error = NoSolution;

    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I, Error = Self::Error> {
        self
    }

    fn fold_free_placeholder_ty(
        &mut self,
        universe: PlaceholderIndex,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Ty<I>> {
        let table = &mut self.table;
        Ok(self
            .inverted_ty
            .entry(universe)
            .or_insert_with(|| table.new_variable(universe.ui))
            .to_ty(self.interner())
            .shifted_in(self.interner()))
    }

    fn fold_free_placeholder_lifetime(
        &mut self,
        universe: PlaceholderIndex,
        _outer_binder: DebruijnIndex,
    ) -> Fallible<Lifetime<I>> {
        let table = &mut self.table;
        Ok(self
            .inverted_lifetime
            .entry(universe)
            .or_insert_with(|| table.new_variable(universe.ui))
            .to_lifetime(self.interner())
            .shifted_in(self.interner()))
    }

    fn forbid_free_vars(&self) -> bool {
        true
    }

    fn forbid_inference_vars(&self) -> bool {
        true
    }

    fn interner(&self) -> &'i I {
        self.interner
    }
}
