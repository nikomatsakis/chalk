use chalk_engine::fallible::*;
use chalk_ir::fold::{
    DefaultFreeVarFolder, DefaultInferenceFolder, DefaultTypeFolder, Fold, PlaceholderFolder,
};
use chalk_ir::*;

use super::InferenceTable;

impl InferenceTable {
    pub(crate) fn u_canonicalize<T: Fold>(
        &mut self,
        value0: &Canonical<T>,
    ) -> UCanonicalized<T::Result> {
        debug!("u_canonicalize({:#?})", value0);

        // First, find all the universes that appear in `value`.
        let mut universes = UniverseMap::new();
        value0
            .value
            .fold_with(
                &mut UCollector {
                    universes: &mut universes,
                },
                0,
            )
            .unwrap();

        // Now re-map the universes found in value. We have to do this
        // in a second pass because it is only then that we know the
        // full set of universes found in the original value.
        let value1 = value0
            .value
            .fold_with(
                &mut UMapToCanonical {
                    universes: &universes,
                },
                0,
            )
            .unwrap();
        let binders = value0
            .binders
            .iter()
            .map(|pk| pk.map(|ui| universes.map_universe_to_canonical(ui)))
            .collect();

        UCanonicalized {
            quantified: UCanonical {
                universes: universes.num_canonical_universes(),
                canonical: Canonical {
                    value: value1,
                    binders,
                },
            },
            universes,
        }
    }
}

#[derive(Debug)]
pub(crate) struct UCanonicalized<T> {
    /// The canonicalized result.
    pub(crate) quantified: UCanonical<T>,

    /// A map between the universes in `quantified` and the original universes
    pub(crate) universes: UniverseMap,
}

/// Maps the universes found in the `u_canonicalize` result (the
/// "canonical" universes) to the universes found in the original
/// value (and vice versa). When used as a folder -- i.e., from
/// outside this module -- converts from "canonical" universes to the
/// original (but see the `UMapToCanonical` folder).
#[derive(Clone, Debug)]
pub(crate) struct UniverseMap {
    /// A reverse map -- for each universe Ux that appears in
    /// `quantified`, the corresponding universe in the original was
    /// `universes[x]`.
    universes: Vec<UniverseIndex>,
}

impl UniverseMap {
    fn new() -> Self {
        UniverseMap {
            universes: vec![UniverseIndex::root()],
        }
    }

    /// Number of canonical universes.
    fn num_canonical_universes(&self) -> usize {
        self.universes.len()
    }

    fn add(&mut self, universe: UniverseIndex) {
        if let Err(i) = self.universes.binary_search(&universe) {
            self.universes.insert(i, universe);
        }
    }

    /// Given a universe U that appeared in our original value, return
    /// the universe to use in the u-canonical value. This is done by
    /// looking for the index I of U in `self.universes`. We will
    /// return the universe with "counter" I. This effectively
    /// "compresses" the range of universes to things from
    /// `0..self.universes.len()`.
    ///
    /// There is one subtle point, though: if we don't find U in the
    /// vector, what should we return? This can only occur when we are
    /// mapping the universes for existentially quantified variables
    /// appearing in the original value. For example, if we have an initial
    /// query like
    ///
    /// ```notrust
    /// !U1: Foo<?X, !U3>
    /// ```
    ///
    /// where `?X` is an existential variable in universe U2, and
    /// `!U1` (resp. `!U3`) is a placeholder variable in universe U1
    /// (resp. U3), then this will be canonicalized to
    ///
    /// ```notrust
    /// exists<U2> { !U1: Foo<?0, !U3>
    /// ```
    ///
    /// We will then collect the universe vector `[Root, 1, 3]`.
    /// Hence we would remap the inner part to `!U1': Foo<?0, !U2'>`
    /// (I am using the convention of writing U1' and U2' to indicate
    /// the target universes that we are mappin to, which are
    /// logically distincte).  But what universe should we use for the
    /// `exists` binder? `U2` is not in the set of universes we
    /// collected initially.  The answer is that we will remap U2 to
    /// U1' in the final result, giving:
    ///
    /// ```notrust
    /// exists<U1'> { !U1': Foo<?0, !U2'>
    /// ```
    ///
    /// More generally, we pick the highest numbered universe we did
    /// find that is still lower then the universe U we are
    /// mapping. Effectivelly we "remapped" from U2 (in the original
    /// multiverse) to U1; this is a sound approximation, because all
    /// names from U1 are visible to U2 (but not vice
    /// versa). Moreover, since there are no placeholders from U2 in
    /// the original query, there is no way we would have equated `?0`
    /// with such a name.
    fn map_universe_to_canonical(&self, universe: UniverseIndex) -> UniverseIndex {
        match self.universes.binary_search(&universe) {
            Ok(index) => UniverseIndex { counter: index },

            // `index` is the location in the vector where universe
            // *would have* gone.  So, in our example from the comment
            // above, if we were looking up `U2` we would get back 2,
            // since it would go betewen U1 (with index 1) and U3
            // (with index 2). Therefore, we want to subtract one to
            // get the biggest universe that is still lower than
            // `universe`.
            //
            // Note that `index` can never be 0: that is always the
            // root universe, we always add that to the vector.
            Err(index) => {
                assert!(index > 0);
                UniverseIndex { counter: index - 1 }
            }
        }
    }

    /// Given a "canonical universe" -- one found in the
    /// `u_canonicalize` result -- returns the original universe that
    /// it corresponded to.
    fn map_universe_from_canonical(&self, universe: UniverseIndex) -> UniverseIndex {
        if universe.counter < self.universes.len() {
            self.universes[universe.counter]
        } else {
            // If this universe is out of bounds, we assume an
            // implicit `forall` binder, effectively, and map to a
            // "big enough" universe in the original space. See
            // comments on `map_from_canonical` for a detailed
            // explanation.
            let difference = universe.counter - self.universes.len();
            let max_counter = self.universes.last().unwrap().counter;
            let new_counter = max_counter + difference + 1;
            UniverseIndex {
                counter: new_counter,
            }
        }
    }

    /// Returns a mapped version of `value` where the universes have
    /// been translated from canonical universes into the original
    /// universes.
    ///
    /// In some cases, `value` may contain fresh universes that are
    /// not described in the original map. This occurs when we return
    /// region constraints -- for example, if we were to process a
    /// constraint like `for<'a> 'a == 'b`, where `'b` is an inference
    /// variable, that would generate a region constraint that `!2 ==
    /// ?0`. (This constraint is typically not, as it happens,
    /// satisfiable, but it may be, depending on the bounds on `!2`.)
    /// In effect, there is a "for all" binder around the constraint,
    /// but it is not represented explicitly -- only implicitly, by
    /// the presence of a U2 variable.
    ///
    /// If we encounter universes like this, which are "out of bounds"
    /// from our original set of universes, we map them to a distinct
    /// universe in the original space that is greater than all the
    /// other universes in the map. That is, if we encounter a
    /// canonical universe `Ux` where our canonical vector is (say)
    /// `[U0, U3]`, we would compute the difference `d = x - 2` and
    /// then return the universe `3 + d + 1`.
    ///
    /// The important thing is that we preserve (a) the relative order
    /// of universes, since that determines visibility, and (b) that
    /// the universe we produce does not correspond to any of the
    /// other original universes.
    pub(crate) fn map_from_canonical<T: Fold>(&self, value: &T) -> T::Result {
        debug!("map_from_canonical(value={:?})", value);
        debug!("map_from_canonical: universes = {:?}", self.universes);
        value
            .fold_with(&mut UMapFromCanonical { universes: self }, 0)
            .unwrap()
    }
}

/// The `UCollector` is a "no-op" in terms of the value, but along the
/// way it collects all universes that were found into a vector.
struct UCollector<'q> {
    universes: &'q mut UniverseMap,
}

impl<'q> DefaultTypeFolder for UCollector<'q> {}

impl<'q> PlaceholderFolder for UCollector<'q> {
    fn fold_free_placeholder_ty(
        &mut self,
        universe: PlaceholderIndex,
        _binders: usize,
    ) -> Fallible<Ty> {
        self.universes.add(universe.ui);
        Ok(universe.to_ty())
    }

    fn fold_free_placeholder_lifetime(
        &mut self,
        universe: PlaceholderIndex,
        _binders: usize,
    ) -> Fallible<Lifetime> {
        self.universes.add(universe.ui);
        Ok(universe.to_lifetime())
    }
}

impl<'q> DefaultFreeVarFolder for UCollector<'q> {}

impl<'q> DefaultInferenceFolder for UCollector<'q> {
    fn forbid() -> bool {
        true
    }
}

struct UMapToCanonical<'q> {
    universes: &'q UniverseMap,
}

impl<'q> DefaultTypeFolder for UMapToCanonical<'q> {}

impl<'q> DefaultInferenceFolder for UMapToCanonical<'q> {
    fn forbid() -> bool {
        true
    }
}

impl<'q> PlaceholderFolder for UMapToCanonical<'q> {
    fn fold_free_placeholder_ty(
        &mut self,
        universe0: PlaceholderIndex,
        _binders: usize,
    ) -> Fallible<Ty> {
        let ui = self.universes.map_universe_to_canonical(universe0.ui);
        Ok(PlaceholderIndex {
            ui,
            idx: universe0.idx,
        }
        .to_ty())
    }

    fn fold_free_placeholder_lifetime(
        &mut self,
        universe0: PlaceholderIndex,
        _binders: usize,
    ) -> Fallible<Lifetime> {
        let universe = self.universes.map_universe_to_canonical(universe0.ui);
        Ok(PlaceholderIndex {
            ui: universe,
            idx: universe0.idx,
        }
        .to_lifetime())
    }
}

impl<'q> DefaultFreeVarFolder for UMapToCanonical<'q> {}

struct UMapFromCanonical<'q> {
    universes: &'q UniverseMap,
}

impl<'q> DefaultTypeFolder for UMapFromCanonical<'q> {}

impl<'q> PlaceholderFolder for UMapFromCanonical<'q> {
    fn fold_free_placeholder_ty(
        &mut self,
        universe0: PlaceholderIndex,
        _binders: usize,
    ) -> Fallible<Ty> {
        let ui = self.universes.map_universe_from_canonical(universe0.ui);
        Ok(PlaceholderIndex {
            ui,
            idx: universe0.idx,
        }
        .to_ty())
    }

    fn fold_free_placeholder_lifetime(
        &mut self,
        universe0: PlaceholderIndex,
        _binders: usize,
    ) -> Fallible<Lifetime> {
        let universe = self.universes.map_universe_from_canonical(universe0.ui);
        Ok(PlaceholderIndex {
            ui: universe,
            idx: universe0.idx,
        }
        .to_lifetime())
    }
}

impl<'q> DefaultFreeVarFolder for UMapFromCanonical<'q> {}

impl<'q> DefaultInferenceFolder for UMapFromCanonical<'q> {
    fn forbid() -> bool {
        true
    }
}
