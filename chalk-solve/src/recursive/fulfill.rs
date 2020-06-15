use super::lib::{Guidance, Minimums, Solution};
use super::{search_graph::DepthFirstNumber, solve::SolveDatabase};
use chalk_ir::cast::Cast;
use chalk_ir::fold::Fold;
use chalk_ir::interner::{HasInterner, Interner};
use chalk_ir::visit::Visit;
use chalk_ir::zip::Zip;
use chalk_ir::{debug, debug_heading};
use chalk_ir::{
    Binders, Canonical, ConstrainedSubst, Constraint, DomainGoal, Environment, EqGoal, Fallible,
    GenericArg, Goal, GoalData, InEnvironment, LifetimeOutlives, NoSolution,
    ProgramClauseImplication, QuantifierKind, Substitution, UCanonical, UniverseMap, WhereClause,
};
use rustc_hash::FxHashSet;
use std::fmt::Debug;

enum Outcome {
    Complete,
    Incomplete,
}

impl Outcome {
    fn is_complete(&self) -> bool {
        match *self {
            Outcome::Complete => true,
            _ => false,
        }
    }
}

/// A goal that must be resolved
#[derive(Clone, Debug, PartialEq, Eq)]
enum Obligation<I: Interner> {
    /// For "positive" goals, we flatten all the way out to leafs within the
    /// current `Fulfill`
    Prove(InEnvironment<Goal<I>>),

    /// For "negative" goals, we don't flatten in *this* `Fulfill`, which would
    /// require having a logical "or" operator. Instead, we recursively solve in
    /// a fresh `Fulfill`.
    Refute(InEnvironment<Goal<I>>),
}

/// When proving a leaf goal, we record the free variables that appear within it
/// so that we can update inference state accordingly.
#[derive(Clone, Debug)]
struct PositiveSolution<I: Interner> {
    free_vars: Vec<GenericArg<I>>,
    universes: UniverseMap,
    solution: Solution<I>,
}

/// When refuting a goal, there's no impact on inference state.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum NegativeSolution {
    Refuted,
    Ambiguous,
}

pub(super) trait RecursiveInferenceTable<I: Interner> {
    fn instantiate_binders_universally<'a, T>(
        &mut self,
        interner: &'a I,
        arg: &'a Binders<T>,
    ) -> T::Result
    where
        T: Fold<I> + HasInterner<Interner = I>;

    fn instantiate_binders_existentially<'a, T>(
        &mut self,
        interner: &'a I,
        arg: &'a Binders<T>,
    ) -> T::Result
    where
        T: Fold<I> + HasInterner<Interner = I>;

    fn canonicalize<T>(
        &mut self,
        interner: &I,
        value: &T,
    ) -> (Canonical<T::Result>, Vec<GenericArg<I>>)
    where
        T: Fold<I>,
        T::Result: HasInterner<Interner = I>;

    fn u_canonicalize<T>(
        &mut self,
        interner: &I,
        value0: &Canonical<T>,
    ) -> (UCanonical<T::Result>, UniverseMap)
    where
        T: HasInterner<Interner = I> + Fold<I> + Visit<I>,
        T::Result: HasInterner<Interner = I>;

    fn unify<T>(
        &mut self,
        interner: &I,
        environment: &Environment<I>,
        a: &T,
        b: &T,
    ) -> Fallible<(
        Vec<InEnvironment<DomainGoal<I>>>,
        Vec<InEnvironment<Constraint<I>>>,
    )>
    where
        T: ?Sized + Zip<I>;

    fn instantiate_canonical<T>(&mut self, interner: &I, bound: &Canonical<T>) -> T::Result
    where
        T: HasInterner<Interner = I> + Fold<I> + Debug;

    fn invert_then_canonicalize<T>(
        &mut self,
        interner: &I,
        value: &T,
    ) -> Option<Canonical<T::Result>>
    where
        T: Fold<I, Result = T> + HasInterner<Interner = I>;

    fn needs_truncation(&mut self, interner: &I, max_size: usize, value: impl Visit<I>) -> bool;
}

/// A `Fulfill` is where we actually break down complex goals, instantiate
/// variables, and perform inference. It's highly stateful. It's generally used
/// in Chalk to try to solve a goal, and then package up what was learned in a
/// stateless, canonical way.
///
/// In rustc, you can think of there being an outermost `Fulfill` that's used when
/// type checking each function body, etc. There, the state reflects the state
/// of type inference in general. But when solving trait constraints, *fresh*
/// `Fulfill` instances will be created to solve canonicalized, free-standing
/// goals, and transport what was learned back to the outer context.
pub(super) struct Fulfill<
    's,
    I: Interner,
    Solver: SolveDatabase<I>,
    Infer: RecursiveInferenceTable<I>,
> {
    solver: &'s mut Solver,
    subst: Substitution<I>,
    infer: Infer,

    /// The dfn of the current goal being solved.
    /// Used to detect negative cycles.
    dfn: DepthFirstNumber,

    /// The remaining goals to prove or refute
    obligations: Vec<Obligation<I>>,

    /// Lifetime constraints that must be fulfilled for a solution to be fully
    /// validated.
    constraints: FxHashSet<InEnvironment<Constraint<I>>>,

    /// Record that a goal has been processed that can neither be proved nor
    /// refuted. In such a case the solution will be either `CannotProve`, or `Err`
    /// in the case where some other goal leads to an error.
    cannot_prove: bool,
}

impl<'s, I: Interner, Solver: SolveDatabase<I>, Infer: RecursiveInferenceTable<I>>
    Fulfill<'s, I, Solver, Infer>
{
    pub(super) fn new_with_clause(
        solver: &'s mut Solver,
        infer: Infer,
        subst: Substitution<I>,
        dfn: DepthFirstNumber,
        canonical_goal: InEnvironment<DomainGoal<I>>,
        clause: &Binders<ProgramClauseImplication<I>>,
    ) -> Fallible<Self> {
        let mut fulfill = Fulfill {
            solver,
            infer,
            subst,
            dfn,
            obligations: vec![],
            constraints: FxHashSet::default(),
            cannot_prove: false,
        };

        let ProgramClauseImplication {
            consequence,
            conditions,
            priority: _,
        } = fulfill
            .infer
            .instantiate_binders_existentially(fulfill.solver.interner(), clause);

        debug!("the subst is {:?}", fulfill.subst);

        if let Err(e) = fulfill.unify(
            &canonical_goal.environment,
            &canonical_goal.goal,
            &consequence,
        ) {
            return Err(e);
        }

        // if so, toss in all of its premises
        for condition in conditions.as_slice(fulfill.solver.interner()) {
            if let Err(e) = fulfill.push_goal(&canonical_goal.environment, condition.clone()) {
                return Err(e);
            }
        }

        Ok(fulfill)
    }

    pub(super) fn new_with_simplification(
        solver: &'s mut Solver,
        infer: Infer,
        subst: Substitution<I>,
        dfn: DepthFirstNumber,
        canonical_goal: InEnvironment<Goal<I>>,
    ) -> Fallible<Self> {
        let mut fulfill = Fulfill {
            solver,
            infer,
            subst,
            dfn,
            obligations: vec![],
            constraints: FxHashSet::default(),
            cannot_prove: false,
        };

        if let Err(e) = fulfill.push_goal(&canonical_goal.environment, canonical_goal.goal.clone())
        {
            return Err(e);
        }

        Ok(fulfill)
    }

    fn push_obligation(&mut self, obligation: Obligation<I>) {
        // truncate to avoid overflows
        match &obligation {
            Obligation::Prove(goal) => {
                if self
                    .infer
                    .needs_truncation(self.solver.interner(), 30, goal)
                {
                    // the goal is too big. Record that we should return Ambiguous
                    self.cannot_prove = true;
                    return;
                }
            }
            Obligation::Refute(goal) => {
                if self
                    .infer
                    .needs_truncation(self.solver.interner(), 30, goal)
                {
                    // the goal is too big. Record that we should return Ambiguous
                    self.cannot_prove = true;
                    return;
                }
            }
        };
        self.obligations.push(obligation);
    }

    /// Unifies `a` and `b` in the given environment.
    ///
    /// Wraps `InferenceTable::unify`; any resulting normalizations are added
    /// into our list of pending obligations with the given environment.
    pub(super) fn unify<T>(&mut self, environment: &Environment<I>, a: &T, b: &T) -> Fallible<()>
    where
        T: ?Sized + Zip<I> + Debug,
    {
        let (goals, constraints) = self
            .infer
            .unify(self.solver.interner(), environment, a, b)?;
        debug!("unify({:?}, {:?}) succeeded", a, b);
        debug!("unify: goals={:?}", goals);
        debug!("unify: constraints={:?}", constraints);
        self.constraints.extend(constraints);
        for goal in goals {
            let goal = goal.cast(self.solver.interner());
            self.push_obligation(Obligation::Prove(goal));
        }
        Ok(())
    }

    /// Create obligations for the given goal in the given environment. This may
    /// ultimately create any number of obligations.
    pub(super) fn push_goal(
        &mut self,
        environment: &Environment<I>,
        goal: Goal<I>,
    ) -> Fallible<()> {
        debug!("push_goal({:?}, {:?})", goal, environment);
        let interner = self.interner();
        match goal.data(interner) {
            GoalData::Quantified(QuantifierKind::ForAll, subgoal) => {
                let subgoal = self
                    .infer
                    .instantiate_binders_universally(self.solver.interner(), subgoal);
                self.push_goal(environment, subgoal)?;
            }
            GoalData::Quantified(QuantifierKind::Exists, subgoal) => {
                let subgoal = self
                    .infer
                    .instantiate_binders_existentially(self.solver.interner(), subgoal);
                self.push_goal(environment, subgoal)?;
            }
            GoalData::Implies(wc, subgoal) => {
                let new_environment =
                    &environment.add_clauses(interner, wc.iter(interner).cloned());
                self.push_goal(new_environment, subgoal.clone())?;
            }
            GoalData::All(goals) => {
                for subgoal in goals.as_slice(interner) {
                    self.push_goal(environment, subgoal.clone())?;
                }
            }
            GoalData::Not(subgoal) => {
                let in_env = InEnvironment::new(environment, subgoal.clone());
                self.push_obligation(Obligation::Refute(in_env));
            }
            GoalData::DomainGoal(domain_goal) => match domain_goal {
                DomainGoal::Holds(WhereClause::LifetimeOutlives(LifetimeOutlives { a, b })) => {
                    self.constraints.insert(InEnvironment::new(
                        &environment,
                        Constraint::Outlives(a.clone(), b.clone()),
                    ));
                }
                _ => {
                    let in_env = InEnvironment::new(environment, goal);
                    self.push_obligation(Obligation::Prove(in_env));
                }
            },
            GoalData::EqGoal(EqGoal { a, b }) => {
                self.unify(&environment, &a, &b)?;
            }
            GoalData::CannotProve(()) => {
                self.cannot_prove = true;
            }
        }
        Ok(())
    }

    fn prove(
        &mut self,
        wc: &InEnvironment<Goal<I>>,
        minimums: &mut Minimums,
    ) -> Fallible<PositiveSolution<I>> {
        let interner = self.solver.interner();
        let (quantified, free_vars) = self.infer.canonicalize(interner, &wc);
        let (quantified, universes) = self.infer.u_canonicalize(interner, &quantified);
        let result = self.solver.solve_goal(quantified, minimums);
        Ok(PositiveSolution {
            free_vars,
            universes,
            solution: result?,
        })
    }

    fn refute(&mut self, goal: &InEnvironment<Goal<I>>) -> Fallible<NegativeSolution> {
        let canonicalized = match self
            .infer
            .invert_then_canonicalize(self.solver.interner(), goal)
        {
            Some(v) => v,
            None => {
                // Treat non-ground negatives as ambiguous. Note that, as inference
                // proceeds, we may wind up with more information here.
                return Ok(NegativeSolution::Ambiguous);
            }
        };

        // Negate the result
        let (quantified, _) = self
            .infer
            .u_canonicalize(self.solver.interner(), &canonicalized);
        let mut minimums = Minimums::new(); // FIXME -- minimums here seems wrong
        if let Ok(solution) = self.solver.solve_goal(quantified, &mut minimums) {
            if solution.is_unique() {
                Err(NoSolution)
            } else {
                Ok(NegativeSolution::Ambiguous)
            }
        } else {
            Ok(NegativeSolution::Refuted)
        }
    }

    /// Trying to prove some goal led to a the substitution `subst`; we
    /// wish to apply that substitution to our own inference variables
    /// (and incorporate any region constraints). This substitution
    /// requires some mapping to get it into our namespace -- first,
    /// the universes it refers to have been canonicalized, and
    /// `universes` stores the mapping back into our
    /// universes. Second, the free variables that appear within can
    /// be mapped into our variables with `free_vars`.
    fn apply_solution(
        &mut self,
        free_vars: Vec<GenericArg<I>>,
        universes: UniverseMap,
        subst: Canonical<ConstrainedSubst<I>>,
    ) {
        use crate::infer::ucanonicalize::UniverseMapExt;
        let subst = universes.map_from_canonical(self.interner(), &subst);
        let ConstrainedSubst { subst, constraints } = self
            .infer
            .instantiate_canonical(self.solver.interner(), &subst);

        debug!(
            "fulfill::apply_solution: adding constraints {:?}",
            constraints
        );
        self.constraints.extend(constraints);

        // We use the empty environment for unification here because we're
        // really just doing a substitution on unconstrained variables, which is
        // guaranteed to succeed without generating any new constraints.
        let empty_env = &Environment::new(self.solver.interner());

        for (i, free_var) in free_vars.into_iter().enumerate() {
            let subst_value = subst.at(self.interner(), i);
            self.unify(empty_env, &free_var, subst_value)
                .unwrap_or_else(|err| {
                    panic!(
                        "apply_solution failed with free_var={:?}, subst_value={:?}: {:?}",
                        free_var, subst_value, err
                    );
                });
        }
    }

    fn fulfill(&mut self, minimums: &mut Minimums) -> Fallible<Outcome> {
        debug_heading!("fulfill(obligations={:#?})", self.obligations);

        // Try to solve all the obligations. We do this via a fixed-point
        // iteration. We try to solve each obligation in turn. Anything which is
        // successful, we drop; anything ambiguous, we retain in the
        // `obligations` array. This process is repeated so long as we are
        // learning new things about our inference state.
        let mut obligations = Vec::with_capacity(self.obligations.len());
        let mut progress = true;

        while progress {
            progress = false;
            debug_heading!("start of round, {} obligations", self.obligations.len());

            // Take the list of `obligations` to solve this round and replace it
            // with an empty vector. Iterate through each obligation to solve
            // and solve it if we can. If not (because of ambiguity), then push
            // it back onto `self.to_prove` for next round. Note that
            // `solve_one` may also push onto the `self.to_prove` list
            // directly.
            assert!(obligations.is_empty());
            while let Some(obligation) = self.obligations.pop() {
                let ambiguous = match obligation {
                    Obligation::Prove(ref wc) => {
                        let PositiveSolution {
                            free_vars,
                            universes,
                            solution,
                        } = self.prove(wc, minimums)?;

                        if solution.has_definite() {
                            if let Some(constrained_subst) = solution.constrained_subst() {
                                self.apply_solution(free_vars, universes, constrained_subst);
                                progress = true;
                            }
                        }

                        solution.is_ambig()
                    }
                    Obligation::Refute(ref goal) => {
                        let answer = self.refute(goal)?;
                        answer == NegativeSolution::Ambiguous
                    }
                };

                if ambiguous {
                    debug!("ambiguous result: {:?}", obligation);
                    obligations.push(obligation);
                }
            }

            self.obligations.extend(obligations.drain(..));
            debug!("end of round, {} obligations left", self.obligations.len());
        }

        // At the end of this process, `self.obligations` should have
        // all of the ambiguous obligations, and `obligations` should
        // be empty.
        assert!(obligations.is_empty());

        if self.obligations.is_empty() {
            Ok(Outcome::Complete)
        } else {
            Ok(Outcome::Incomplete)
        }
    }

    /// Try to fulfill all pending obligations and build the resulting
    /// solution. The returned solution will transform `subst` substitution with
    /// the outcome of type inference by updating the replacements it provides.
    pub(super) fn solve(mut self, minimums: &mut Minimums) -> Fallible<Solution<I>> {
        let outcome = match self.fulfill(minimums) {
            Ok(o) => o,
            Err(e) => return Err(e),
        };

        if self.cannot_prove {
            return Ok(Solution::Ambig(Guidance::Unknown));
        }

        if outcome.is_complete() {
            // No obligations remain, so we have definitively solved our goals,
            // and the current inference state is the unique way to solve them.

            let constraints = self.constraints.into_iter().collect();
            let constrained = self.infer.canonicalize(
                self.solver.interner(),
                &ConstrainedSubst {
                    subst: self.subst,
                    constraints,
                },
            );
            return Ok(Solution::Unique(constrained.0));
        }

        // Otherwise, we have (positive or negative) obligations remaining, but
        // haven't proved that it's *impossible* to satisfy out obligations. we
        // need to determine how to package up what we learned about type
        // inference as an ambiguous solution.

        let interner = self.solver.interner();
        let canonical_subst = self.infer.canonicalize(interner, &self.subst);

        if canonical_subst.0.value.is_identity_subst(interner) {
            // In this case, we didn't learn *anything* definitively. So now, we
            // go one last time through the positive obligations, this time
            // applying even *tentative* inference suggestions, so that we can
            // yield these upwards as our own suggestions. There are no
            // particular guarantees about *which* obligaiton we derive
            // suggestions from.

            while let Some(obligation) = self.obligations.pop() {
                if let Obligation::Prove(goal) = obligation {
                    let PositiveSolution {
                        free_vars,
                        universes,
                        solution,
                    } = self.prove(&goal, minimums).unwrap();
                    if let Some(constrained_subst) = solution.constrained_subst() {
                        self.apply_solution(free_vars, universes, constrained_subst);
                        return Ok(Solution::Ambig(Guidance::Suggested(canonical_subst.0)));
                    }
                }
            }

            Ok(Solution::Ambig(Guidance::Unknown))
        } else {
            // While we failed to prove the goal, we still learned that
            // something had to hold. Here's an example where this happens:
            //
            // ```rust
            // trait Display {}
            // trait Debug {}
            // struct Foo<T> {}
            // struct Bar {}
            // struct Baz {}
            //
            // impl Display for Bar {}
            // impl Display for Baz {}
            //
            // impl<T> Debug for Foo<T> where T: Display {}
            // ```
            //
            // If we pose the goal `exists<T> { T: Debug }`, we can't say
            // for sure what `T` must be (it could be either `Foo<Bar>` or
            // `Foo<Baz>`, but we *can* say for sure that it must be of the
            // form `Foo<?0>`.
            Ok(Solution::Ambig(Guidance::Definite(canonical_subst.0)))
        }
    }

    fn interner(&self) -> &I {
        self.solver.interner()
    }
}
