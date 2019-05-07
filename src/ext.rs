use crate::infer::InferenceTable;
use chalk_ir::fold::Fold;
use chalk_ir::*;

pub trait CanonicalExt<T> {
    fn map<OP, U>(self, op: OP) -> Canonical<U::Result>
    where
        OP: FnOnce(T::Result) -> U,
        T: Fold,
        U: Fold;
}

impl<T> CanonicalExt<T> for Canonical<T> {
    /// Maps the contents using `op`, but preserving the binders.
    ///
    /// NB. `op` will be invoked with an instantiated version of the
    /// canonical value, where inference variables (from a fresh
    /// inference context) are used in place of the quantified free
    /// variables. The result should be in terms of those same
    /// inference variables and will be re-canonicalized.
    fn map<OP, U>(self, op: OP) -> Canonical<U::Result>
    where
        OP: FnOnce(T::Result) -> U,
        T: Fold,
        U: Fold,
    {
        // Subtle: It is only quite rarely correct to apply `op` and
        // just re-use our existing binders. For that to be valid, the
        // result of `op` would have to ensure that it re-uses all the
        // existing free variables and in the same order. Otherwise,
        // the canonical form would be different: the variables might
        // be numbered differently, or some may not longer be used.
        // This would mean that two canonical values could no longer
        // be compared with `Eq`, which defeats a key invariant of the
        // `Canonical` type (indeed, its entire reason for existence).
        let mut infer = InferenceTable::new();
        let snapshot = infer.snapshot();
        let instantiated_value = infer.instantiate_canonical(&self);
        let mapped_value = op(instantiated_value);
        let result = infer.canonicalize(&mapped_value);
        infer.rollback_to(snapshot);
        result.quantified
    }
}

pub trait GoalExt {
    fn into_peeled_goal(self) -> UCanonical<InEnvironment<Goal>>;
    fn into_closed_goal(self) -> UCanonical<InEnvironment<Goal>>;
}

impl GoalExt for Goal {
    /// Returns a canonical goal in which the outermost `exists<>` and
    /// `forall<>` quantifiers (as well as implications) have been
    /// "peeled" and are converted into free universal or existential
    /// variables. Assumes that this goal is a "closed goal" which
    /// does not -- at present -- contain any variables. Useful for
    /// REPLs and tests but not much else.
    fn into_peeled_goal(self) -> UCanonical<InEnvironment<Goal>> {
        let mut infer = InferenceTable::new();
        let peeled_goal = {
            let mut env_goal = InEnvironment::new(&Environment::new(), self);
            loop {
                let InEnvironment { environment, goal } = env_goal;
                match goal {
                    Goal::Quantified(QuantifierKind::ForAll, subgoal) => {
                        let subgoal = infer.instantiate_binders_universally(&subgoal);
                        env_goal = InEnvironment::new(&environment, *subgoal);
                    }

                    Goal::Quantified(QuantifierKind::Exists, subgoal) => {
                        let subgoal = infer.instantiate_binders_existentially(&subgoal);
                        env_goal = InEnvironment::new(&environment, *subgoal);
                    }

                    Goal::Implies(wc, subgoal) => {
                        let new_environment = &environment.add_clauses(wc);
                        env_goal = InEnvironment::new(&new_environment, *subgoal);
                    }

                    _ => break InEnvironment::new(&environment, goal),
                }
            }
        };
        let canonical = infer.canonicalize(&peeled_goal).quantified;
        infer.u_canonicalize(&canonical).quantified
    }

    /// Given a goal with no free variables (a "closed" goal), creates
    /// a canonical form suitable for solving. This is a suitable
    /// choice if you don't actually care about the values of any of
    /// the variables within; otherwise, you might want
    /// `into_peeled_goal`.
    ///
    /// # Panics
    ///
    /// Will panic if this goal does in fact contain free variables.
    fn into_closed_goal(self) -> UCanonical<InEnvironment<Goal>> {
        let mut infer = InferenceTable::new();
        let env_goal = InEnvironment::new(&Environment::new(), self);
        let canonical_goal = infer.canonicalize(&env_goal).quantified;
        infer.u_canonicalize(&canonical_goal).quantified
    }
}
