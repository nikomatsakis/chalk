use super::combine;
use super::fulfill::{Fulfill, RecursiveInferenceTable};
use super::lib::{Guidance, Solution, UCanonicalGoal};
use crate::clauses::program_clauses_for_goal;
use crate::infer::{InferenceTable, ParameterEnaVariableExt};
use crate::{solve::truncate, RustIrDatabase};
use chalk_ir::fold::Fold;
use chalk_ir::interner::{HasInterner, Interner};
use chalk_ir::visit::Visit;
use chalk_ir::zip::Zip;
use chalk_ir::{debug, debug_heading, info_heading};
use chalk_ir::{
    Binders, Canonical, ClausePriority, Constraint, DomainGoal, Environment, Fallible, Floundered,
    GenericArg, Goal, GoalData, InEnvironment, NoSolution, ProgramClause, ProgramClauseData,
    ProgramClauseImplication, Substitution, UCanonical, UniverseMap, VariableKinds,
};
use std::fmt::Debug;

pub(super) trait SolveDatabase<I: Interner>: Sized {
    fn solve_goal(&mut self, goal: UCanonical<InEnvironment<Goal<I>>>) -> Fallible<Solution<I>>;

    fn interner(&self) -> &I;

    fn db(&self) -> &dyn RustIrDatabase<I>;
}

/// The `solve_iteration` method -- implemented for any type that implements
/// `SolveDb`.
pub(super) trait SolveIteration<I: Interner>: SolveDatabase<I> {
    /// Executes one iteration of the recursive solver, computing the current
    /// solution to the given canonical goal. This is used as part of a loop in
    /// the case of cyclic goals.
    fn solve_iteration(
        &mut self,
        canonical_goal: &UCanonicalGoal<I>,
    ) -> (Fallible<Solution<I>>, ClausePriority) {
        let UCanonical {
            universes,
            canonical:
                Canonical {
                    binders,
                    value: InEnvironment { environment, goal },
                },
        } = canonical_goal.clone();

        match goal.data(self.interner()) {
            GoalData::DomainGoal(domain_goal) => {
                let canonical_goal = UCanonical {
                    universes,
                    canonical: Canonical {
                        binders,
                        value: InEnvironment {
                            environment,
                            goal: domain_goal.clone(),
                        },
                    },
                };

                // "Domain" goals (i.e., leaf goals that are Rust-specific) are
                // always solved via some form of implication. We can either
                // apply assumptions from our environment (i.e. where clauses),
                // or from the lowered program, which includes fallback
                // clauses. We try each approach in turn:

                let InEnvironment { environment, goal } = &canonical_goal.canonical.value;

                let (prog_solution, prog_prio) = {
                    debug_heading!("prog_clauses");

                    let prog_clauses = self.program_clauses_for_goal(environment, &goal);
                    match prog_clauses {
                        Ok(clauses) => self.solve_from_clauses(&canonical_goal, clauses),
                        Err(Floundered) => {
                            (Ok(Solution::Ambig(Guidance::Unknown)), ClausePriority::High)
                        }
                    }
                };
                debug!("prog_solution={:?}", prog_solution);

                (prog_solution, prog_prio)
            }

            _ => {
                let canonical_goal = UCanonical {
                    universes,
                    canonical: Canonical {
                        binders,
                        value: InEnvironment { environment, goal },
                    },
                };

                self.solve_via_simplification(&canonical_goal)
            }
        }
    }
}

impl<S, I> SolveIteration<I> for S
where
    S: SolveDatabase<I>,
    I: Interner,
{
}

/// Helper methods for `solve_iteration`, private to this module.
trait SolveIterationHelpers<I: Interner>: SolveDatabase<I> {
    fn solve_via_simplification(
        &mut self,
        canonical_goal: &UCanonicalGoal<I>,
    ) -> (Fallible<Solution<I>>, ClausePriority) {
        debug_heading!("solve_via_simplification({:?})", canonical_goal);
        let (infer, subst, goal) = self.new_inference_table(canonical_goal);
        match Fulfill::new_with_simplification(self, infer, subst, goal) {
            Ok(fulfill) => (fulfill.solve(), ClausePriority::High),
            Err(e) => (Err(e), ClausePriority::High),
        }
    }

    /// See whether we can solve a goal by implication on any of the given
    /// clauses. If multiple such solutions are possible, we attempt to combine
    /// them.
    fn solve_from_clauses<C>(
        &mut self,
        canonical_goal: &UCanonical<InEnvironment<DomainGoal<I>>>,
        clauses: C,
    ) -> (Fallible<Solution<I>>, ClausePriority)
    where
        C: IntoIterator<Item = ProgramClause<I>>,
    {
        let mut cur_solution = None;
        for program_clause in clauses {
            debug_heading!("clause={:?}", program_clause);

            // If we have a completely ambiguous answer, it's not going to get better, so stop
            if cur_solution == Some((Solution::Ambig(Guidance::Unknown), ClausePriority::High)) {
                return (Ok(Solution::Ambig(Guidance::Unknown)), ClausePriority::High);
            }

            let res = match program_clause.data(self.interner()) {
                ProgramClauseData::Implies(implication) => self.solve_via_implication(
                    canonical_goal,
                    &Binders::new(
                        VariableKinds::from(self.interner(), vec![]),
                        implication.clone(),
                    ),
                ),
                ProgramClauseData::ForAll(implication) => {
                    self.solve_via_implication(canonical_goal, implication)
                }
            };
            if let (Ok(solution), priority) = res {
                debug!("ok: solution={:?} prio={:?}", solution, priority);
                cur_solution = Some(match cur_solution {
                    None => (solution, priority),
                    Some((cur, cur_priority)) => combine::with_priorities(
                        self.interner(),
                        &canonical_goal.canonical.value.goal,
                        cur,
                        cur_priority,
                        solution,
                        priority,
                    ),
                });
            } else {
                debug!("error");
            }
        }
        cur_solution.map_or((Err(NoSolution), ClausePriority::High), |(s, p)| (Ok(s), p))
    }

    /// Modus ponens! That is: try to apply an implication by proving its premises.
    fn solve_via_implication(
        &mut self,
        canonical_goal: &UCanonical<InEnvironment<DomainGoal<I>>>,
        clause: &Binders<ProgramClauseImplication<I>>,
    ) -> (Fallible<Solution<I>>, ClausePriority) {
        info_heading!(
            "solve_via_implication(\
         \n    canonical_goal={:?},\
         \n    clause={:?})",
            canonical_goal,
            clause
        );

        let (infer, subst, goal) = self.new_inference_table(canonical_goal);
        match Fulfill::new_with_clause(self, infer, subst, goal, clause) {
            Ok(fulfill) => (fulfill.solve(), clause.skip_binders().priority),
            Err(e) => (Err(e), ClausePriority::High),
        }
    }

    fn new_inference_table<T: Fold<I, I, Result = T> + HasInterner<Interner = I> + Clone>(
        &self,
        ucanonical_goal: &UCanonical<InEnvironment<T>>,
    ) -> (
        RecursiveInferenceTableImpl<I>,
        Substitution<I>,
        InEnvironment<T::Result>,
    ) {
        let (infer, subst, canonical_goal) = InferenceTable::from_canonical(
            self.interner(),
            ucanonical_goal.universes,
            &ucanonical_goal.canonical,
        );
        let infer = RecursiveInferenceTableImpl { infer };
        (infer, subst, canonical_goal)
    }

    fn program_clauses_for_goal(
        &self,
        environment: &Environment<I>,
        goal: &DomainGoal<I>,
    ) -> Result<Vec<ProgramClause<I>>, Floundered> {
        program_clauses_for_goal(self.db(), environment, goal)
    }
}

impl<S, I> SolveIterationHelpers<I> for S
where
    S: SolveDatabase<I>,
    I: Interner,
{
}

struct RecursiveInferenceTableImpl<I: Interner> {
    infer: InferenceTable<I>,
}

impl<I: Interner> RecursiveInferenceTable<I> for RecursiveInferenceTableImpl<I> {
    fn instantiate_binders_universally<'a, T>(
        &mut self,
        interner: &'a I,
        arg: &'a Binders<T>,
    ) -> T::Result
    where
        T: Fold<I> + HasInterner<Interner = I>,
    {
        self.infer.instantiate_binders_universally(interner, arg)
    }

    fn instantiate_binders_existentially<'a, T>(
        &mut self,
        interner: &'a I,
        arg: &'a Binders<T>,
    ) -> T::Result
    where
        T: Fold<I> + HasInterner<Interner = I>,
    {
        self.infer.instantiate_binders_existentially(interner, arg)
    }

    fn canonicalize<T>(
        &mut self,
        interner: &I,
        value: &T,
    ) -> (Canonical<T::Result>, Vec<GenericArg<I>>)
    where
        T: Fold<I>,
        T::Result: HasInterner<Interner = I>,
    {
        let res = self.infer.canonicalize(interner, value);
        let free_vars = res
            .free_vars
            .into_iter()
            .map(|free_var| free_var.to_generic_arg(interner))
            .collect();
        (res.quantified, free_vars)
    }

    fn u_canonicalize<T>(
        &mut self,
        interner: &I,
        value0: &Canonical<T>,
    ) -> (UCanonical<T::Result>, UniverseMap)
    where
        T: HasInterner<Interner = I> + Fold<I> + Visit<I>,
        T::Result: HasInterner<Interner = I>,
    {
        let res = self.infer.u_canonicalize(interner, value0);
        (res.quantified, res.universes)
    }

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
        T: ?Sized + Zip<I>,
    {
        let res = self.infer.unify(interner, environment, a, b)?;
        Ok((res.goals, res.constraints))
    }

    fn instantiate_canonical<T>(&mut self, interner: &I, bound: &Canonical<T>) -> T::Result
    where
        T: HasInterner<Interner = I> + Fold<I> + Debug,
    {
        self.infer.instantiate_canonical(interner, bound)
    }

    fn invert_then_canonicalize<T>(
        &mut self,
        interner: &I,
        value: &T,
    ) -> Option<Canonical<T::Result>>
    where
        T: Fold<I, Result = T> + HasInterner<Interner = I>,
    {
        self.infer.invert_then_canonicalize(interner, value)
    }

    fn needs_truncation(&mut self, interner: &I, max_size: usize, value: impl Visit<I>) -> bool {
        truncate::needs_truncation(interner, &mut self.infer, max_size, value)
    }
}
