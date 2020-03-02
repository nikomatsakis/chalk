use crate::clauses::program_clauses_for_goal;
use crate::coinductive_goal::IsCoinductive;
use crate::infer::ucanonicalize::{UCanonicalized, UniverseMap};
use crate::infer::unify::UnificationResult;
use crate::infer::InferenceTable;
use crate::solve::truncate::{self, Truncated};
use crate::solve::Solution;
use crate::RustIrDatabase;
use chalk_derive::HasInterner;
use chalk_engine::context;
use chalk_engine::context::Floundered;
use chalk_engine::fallible::Fallible;
use chalk_engine::hh::HhGoal;
use chalk_engine::{CompleteAnswer, ExClause, Literal};
use chalk_ir::cast::Cast;
use chalk_ir::cast::Caster;
use chalk_ir::could_match::CouldMatch;
use chalk_ir::interner::HasInterner;
use chalk_ir::interner::Interner;
use chalk_ir::*;

use std::fmt::Debug;
use std::marker::PhantomData;

mod aggregate;
mod resolvent;

#[derive(Clone, Debug, HasInterner)]
pub(crate) struct SlgContext<I: Interner> {
    max_size: usize,
    /// The expected number of answers for a solution.
    /// Only really sseful for tests, since `make_solution`
    /// will panic if the number of cached answers does not
    /// equal this when a solution is made.
    expected_answers: Option<usize>,
    phantom: PhantomData<I>,
}

impl<I: Interner> SlgContext<I> {
    pub(crate) fn new(max_size: usize, expected_answers: Option<usize>) -> SlgContext<I> {
        SlgContext {
            max_size,
            expected_answers,
            phantom: PhantomData,
        }
    }

    pub(crate) fn ops<'p>(&self, program: &'p dyn RustIrDatabase<I>) -> SlgContextOps<'p, I> {
        SlgContextOps {
            program,
            max_size: self.max_size,
            expected_answers: self.expected_answers,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SlgContextOps<'me, I: Interner> {
    program: &'me dyn RustIrDatabase<I>,
    max_size: usize,
    expected_answers: Option<usize>,
}

#[derive(Clone)]
pub struct TruncatingInferenceTable<I: Interner> {
    max_size: usize,
    infer: InferenceTable<I>,
}

impl<I: Interner> context::Context for SlgContext<I> {
    type CanonicalGoalInEnvironment = Canonical<InEnvironment<Goal<I>>>;
    type CanonicalExClause = Canonical<ExClause<Self>>;
    type UCanonicalGoalInEnvironment = UCanonical<InEnvironment<Goal<I>>>;
    type UniverseMap = UniverseMap;
    type InferenceNormalizedSubst = Substitution<I>;
    type Solution = Solution<I>;
    type InferenceTable = TruncatingInferenceTable<I>;
    type Environment = Environment<I>;
    type DomainGoal = DomainGoal<I>;
    type Goal = Goal<I>;
    type BindersGoal = Binders<Goal<I>>;
    type Parameter = Parameter<I>;
    type ProgramClause = ProgramClause<I>;
    type ProgramClauses = Vec<ProgramClause<I>>;
    type CanonicalConstrainedSubst = Canonical<ConstrainedSubst<I>>;
    type CanonicalAnswerSubst = Canonical<AnswerSubst<I>>;
    type GoalInEnvironment = InEnvironment<Goal<I>>;
    type Substitution = Substitution<I>;
    type RegionConstraint = InEnvironment<Constraint<I>>;
    type Variance = ();
    type Interner = I;

    fn goal_in_environment(environment: &Environment<I>, goal: Goal<I>) -> InEnvironment<Goal<I>> {
        InEnvironment::new(environment, goal)
    }

    fn inference_normalized_subst_from_ex_clause(
        canon_ex_clause: &Canonical<ExClause<SlgContext<I>>>,
    ) -> &Substitution<I> {
        &canon_ex_clause.value.subst
    }

    fn empty_constraints(ccs: &Canonical<AnswerSubst<I>>) -> bool {
        ccs.value.constraints.is_empty()
    }

    fn inference_normalized_subst_from_subst(ccs: &Canonical<AnswerSubst<I>>) -> &Substitution<I> {
        &ccs.value.subst
    }

    fn canonical(
        u_canon: &UCanonical<InEnvironment<Goal<I>>>,
    ) -> &Canonical<InEnvironment<Goal<I>>> {
        &u_canon.canonical
    }

    fn is_trivial_substitution(
        u_canon: &UCanonical<InEnvironment<Goal<I>>>,
        canonical_subst: &Canonical<AnswerSubst<I>>,
    ) -> bool {
        u_canon.is_trivial_substitution(canonical_subst)
    }

    fn has_delayed_subgoals(canonical_subst: &Canonical<AnswerSubst<I>>) -> bool {
        !canonical_subst.value.delayed_subgoals.is_empty()
    }

    fn num_universes(u_canon: &UCanonical<InEnvironment<Goal<I>>>) -> usize {
        u_canon.universes
    }

    fn canonical_constrained_subst_from_canonical_constrained_answer(
        canonical_subst: &Canonical<AnswerSubst<I>>,
    ) -> Canonical<ConstrainedSubst<I>> {
        Canonical {
            binders: canonical_subst.binders.clone(),
            value: ConstrainedSubst {
                subst: canonical_subst.value.subst.clone(),
                constraints: canonical_subst.value.constraints.clone(),
            },
        }
    }

    fn goal_from_goal_in_environment(goal: &InEnvironment<Goal<I>>) -> &Goal<I> {
        &goal.goal
    }

    fn into_hh_goal(goal: Goal<I>) -> HhGoal<SlgContext<I>> {
        match goal.data().clone() {
            GoalData::Quantified(QuantifierKind::ForAll, binders_goal) => {
                HhGoal::ForAll(binders_goal)
            }
            GoalData::Quantified(QuantifierKind::Exists, binders_goal) => {
                HhGoal::Exists(binders_goal)
            }
            GoalData::Implies(dg, subgoal) => HhGoal::Implies(dg, subgoal),
            GoalData::All(goals) => HhGoal::All(goals.iter().cloned().collect()),
            GoalData::Not(g1) => HhGoal::Not(g1),
            GoalData::EqGoal(EqGoal { a, b }) => HhGoal::Unify((), a, b),
            GoalData::DomainGoal(domain_goal) => HhGoal::DomainGoal(domain_goal),
            GoalData::CannotProve(()) => HhGoal::CannotProve,
        }
    }

    // Used by: simplify
    fn add_clauses(env: &Environment<I>, clauses: Vec<ProgramClause<I>>) -> Environment<I> {
        Environment::add_clauses(env, clauses)
    }

    fn into_goal(domain_goal: DomainGoal<I>) -> Goal<I> {
        domain_goal.cast()
    }

    // Used by: logic
    fn next_subgoal_index(ex_clause: &ExClause<SlgContext<I>>) -> usize {
        // For now, we always pick the last subgoal in the
        // list.
        //
        // FIXME(rust-lang-nursery/chalk#80) -- we should be more
        // selective. For example, we don't want to pick a
        // negative literal that will flounder, and we don't want
        // to pick things like `?T: Sized` if we can help it.
        ex_clause.subgoals.len() - 1
    }
}

impl<'me, I: Interner> context::ContextOps<SlgContext<I>> for SlgContextOps<'me, I> {
    fn is_coinductive(&self, goal: &UCanonical<InEnvironment<Goal<I>>>) -> bool {
        goal.is_coinductive(self.program)
    }

    fn map_goal_from_canonical(
        &self,
        map: &UniverseMap,
        value: &Canonical<InEnvironment<Goal<I>>>,
    ) -> Canonical<InEnvironment<Goal<I>>> {
        map.map_from_canonical(self.program.interner(), value)
    }

    fn map_subst_from_canonical(
        &self,
        map: &UniverseMap,
        value: &Canonical<AnswerSubst<I>>,
    ) -> Canonical<AnswerSubst<I>> {
        map.map_from_canonical(self.program.interner(), value)
    }

    fn program_clauses(
        &self,
        environment: &Environment<I>,
        goal: &DomainGoal<I>,
        infer: &mut TruncatingInferenceTable<I>,
    ) -> Result<Vec<ProgramClause<I>>, Floundered> {
        // Look for floundering goals:
        match goal {
            // Check for a goal like `?T: Foo` where `Foo` is not enumerable.
            DomainGoal::Holds(WhereClause::Implemented(trait_ref)) => {
                let trait_datum = self.program.trait_datum(trait_ref.trait_id);
                if trait_datum.is_non_enumerable_trait() || trait_datum.is_auto_trait() {
                    let self_ty = trait_ref.self_type_parameter();
                    if let Some(v) = self_ty.inference_var() {
                        if !infer.infer.var_is_bound(v) {
                            return Err(Floundered);
                        }
                    }
                }
            }

            DomainGoal::WellFormed(WellFormed::Ty(ty))
            | DomainGoal::IsUpstream(ty)
            | DomainGoal::DownstreamType(ty)
            | DomainGoal::IsFullyVisible(ty)
            | DomainGoal::IsLocal(ty) => match ty.data() {
                TyData::InferenceVar(_) => return Err(Floundered),
                _ => {}
            },

            _ => {}
        }

        let mut clauses: Vec<_> = program_clauses_for_goal(self.program, environment, goal);

        clauses.extend(
            environment
                .clauses
                .iter()
                .filter(|&env_clause| env_clause.could_match(goal))
                .cloned(),
        );

        Ok(clauses)
    }

    fn instantiate_ucanonical_goal(
        &self,
        arg: &UCanonical<InEnvironment<Goal<I>>>,
    ) -> (
        TruncatingInferenceTable<I>,
        Substitution<I>,
        Environment<I>,
        Goal<I>,
    ) {
        let (infer, subst, InEnvironment { environment, goal }) =
            InferenceTable::from_canonical(self.program.interner(), arg.universes, &arg.canonical);
        let infer_table = TruncatingInferenceTable::new(self.max_size, infer);
        (infer_table, subst, environment, goal)
    }

    fn instantiate_ex_clause(
        &self,
        num_universes: usize,
        canonical_ex_clause: &Canonical<ExClause<SlgContext<I>>>,
    ) -> (TruncatingInferenceTable<I>, ExClause<SlgContext<I>>) {
        let (infer, _subst, ex_cluse) = InferenceTable::from_canonical(
            self.program.interner(),
            num_universes,
            canonical_ex_clause,
        );
        let infer_table = TruncatingInferenceTable::new(self.max_size, infer);
        (infer_table, ex_cluse)
    }

    fn instantiate_answer_subst(
        &self,
        num_universes: usize,
        answer: &Canonical<AnswerSubst<I>>,
    ) -> (
        TruncatingInferenceTable<I>,
        Substitution<I>,
        Vec<InEnvironment<Constraint<I>>>,
        Vec<InEnvironment<Goal<I>>>,
    ) {
        let (
            infer,
            _subst,
            AnswerSubst {
                subst,
                constraints,
                delayed_subgoals,
            },
        ) = InferenceTable::from_canonical(self.program.interner(), num_universes, answer);
        let infer_table = TruncatingInferenceTable::new(self.max_size, infer);
        (infer_table, subst, constraints, delayed_subgoals)
    }

    fn constrained_subst_from_answer(
        &self,
        answer: CompleteAnswer<SlgContext<I>>,
    ) -> Canonical<ConstrainedSubst<I>> {
        let CompleteAnswer { subst, .. } = answer;
        subst
    }

    fn identity_constrained_subst(
        &self,
        goal: &UCanonical<InEnvironment<Goal<I>>>,
    ) -> Canonical<ConstrainedSubst<I>> {
        let (mut infer, subst, _) = InferenceTable::from_canonical(
            self.program.interner(),
            goal.universes,
            &goal.canonical,
        );
        infer
            .canonicalize(
                self.program.interner(),
                &ConstrainedSubst {
                    subst,
                    constraints: vec![],
                },
            )
            .quantified
    }

    fn interner(&self) -> &I {
        self.program.interner()
    }
}

impl<I: Interner> TruncatingInferenceTable<I> {
    fn new(max_size: usize, infer: InferenceTable<I>) -> Self {
        Self { max_size, infer }
    }
}

impl<I: Interner> context::TruncateOps<SlgContext<I>> for TruncatingInferenceTable<I> {
    fn truncate_goal(
        &mut self,
        interner: &I,
        subgoal: &InEnvironment<Goal<I>>,
    ) -> Option<InEnvironment<Goal<I>>> {
        // We only want to truncate the goal itself. We keep the environment intact.
        // See rust-lang/chalk#280
        let InEnvironment { environment, goal } = subgoal;
        let Truncated { overflow, value } =
            truncate::truncate(interner, &mut self.infer, self.max_size, goal);
        if overflow {
            Some(InEnvironment {
                environment: environment.clone(),
                goal: value,
            })
        } else {
            None
        }
    }

    fn truncate_answer(
        &mut self,
        interner: &I,
        subst: &Substitution<I>,
    ) -> Option<Substitution<I>> {
        let Truncated { overflow, value } =
            truncate::truncate(interner, &mut self.infer, self.max_size, subst);
        if overflow {
            Some(value)
        } else {
            None
        }
    }
}

impl<I: Interner> context::InferenceTable<SlgContext<I>> for TruncatingInferenceTable<I> {}

impl<I: Interner> context::UnificationOps<SlgContext<I>> for TruncatingInferenceTable<I> {
    fn instantiate_binders_universally(&mut self, interner: &I, arg: &Binders<Goal<I>>) -> Goal<I> {
        self.infer.instantiate_binders_universally(interner, arg)
    }

    fn instantiate_binders_existentially(
        &mut self,
        interner: &I,
        arg: &Binders<Goal<I>>,
    ) -> Goal<I> {
        self.infer.instantiate_binders_existentially(interner, arg)
    }

    fn debug_ex_clause<'v>(
        &mut self,
        interner: &I,
        value: &'v ExClause<SlgContext<I>>,
    ) -> Box<dyn Debug + 'v> {
        Box::new(self.infer.normalize_deep(interner, value))
    }

    fn fully_canonicalize_goal(
        &mut self,
        interner: &I,
        value: &InEnvironment<Goal<I>>,
    ) -> (UCanonical<InEnvironment<Goal<I>>>, UniverseMap) {
        let canonicalized_goal = self.infer.canonicalize(interner, value).quantified;
        let UCanonicalized {
            quantified,
            universes,
        } = self.infer.u_canonicalize(interner, &canonicalized_goal);
        (quantified, universes)
    }

    fn canonicalize_ex_clause(
        &mut self,
        interner: &I,
        value: &ExClause<SlgContext<I>>,
    ) -> Canonical<ExClause<SlgContext<I>>> {
        self.infer.canonicalize(interner, value).quantified
    }

    fn canonicalize_constrained_subst(
        &mut self,
        interner: &I,
        subst: Substitution<I>,
        constraints: Vec<InEnvironment<Constraint<I>>>,
    ) -> Canonical<ConstrainedSubst<I>> {
        self.infer
            .canonicalize(interner, &ConstrainedSubst { subst, constraints })
            .quantified
    }

    fn canonicalize_answer_subst(
        &mut self,
        interner: &I,
        subst: Substitution<I>,
        constraints: Vec<InEnvironment<Constraint<I>>>,
        delayed_subgoals: Vec<InEnvironment<Goal<I>>>,
    ) -> Canonical<AnswerSubst<I>> {
        self.infer
            .canonicalize(
                interner,
                &AnswerSubst {
                    subst,
                    constraints,
                    delayed_subgoals,
                },
            )
            .quantified
    }

    fn invert_goal(
        &mut self,
        interner: &I,
        value: &InEnvironment<Goal<I>>,
    ) -> Option<InEnvironment<Goal<I>>> {
        self.infer.invert(interner, value)
    }

    fn unify_parameters_into_ex_clause(
        &mut self,
        interner: &I,
        environment: &Environment<I>,
        _: (),
        a: &Parameter<I>,
        b: &Parameter<I>,
        ex_clause: &mut ExClause<SlgContext<I>>,
    ) -> Fallible<()> {
        let result = self.infer.unify(interner, environment, a, b)?;
        Ok(into_ex_clause(result, ex_clause))
    }
}

/// Helper function
fn into_ex_clause<I: Interner>(
    result: UnificationResult<I>,
    ex_clause: &mut ExClause<SlgContext<I>>,
) {
    ex_clause
        .subgoals
        .extend(result.goals.into_iter().casted().map(Literal::Positive));
    ex_clause.constraints.extend(result.constraints);
}

trait SubstitutionExt<I: Interner> {
    fn may_invalidate(&self, subst: &Canonical<Substitution<I>>) -> bool;
}

impl<I: Interner> SubstitutionExt<I> for Substitution<I> {
    fn may_invalidate(&self, subst: &Canonical<Substitution<I>>) -> bool {
        self.iter()
            .zip(subst.value.iter())
            .any(|(new, current)| MayInvalidate.aggregate_parameters(new, current))
    }
}

// This is a struct in case we need to add state at any point like in AntiUnifier
struct MayInvalidate;

impl MayInvalidate {
    fn aggregate_parameters<I: Interner>(
        &mut self,
        new: &Parameter<I>,
        current: &Parameter<I>,
    ) -> bool {
        match (new.data(), current.data()) {
            (ParameterKind::Ty(ty1), ParameterKind::Ty(ty2)) => self.aggregate_tys(ty1, ty2),
            (ParameterKind::Lifetime(l1), ParameterKind::Lifetime(l2)) => {
                self.aggregate_lifetimes(l1, l2)
            }
            (ParameterKind::Ty(_), _) | (ParameterKind::Lifetime(_), _) => panic!(
                "mismatched parameter kinds: new={:?} current={:?}",
                new, current
            ),
        }
    }

    // Returns true if the two types could be unequal.
    fn aggregate_tys<I: Interner>(&mut self, new: &Ty<I>, current: &Ty<I>) -> bool {
        match (new.data(), current.data()) {
            (_, TyData::BoundVar(_)) => {
                // If the aggregate solution already has an inference
                // variable here, then no matter what type we produce,
                // the aggregate cannot get 'more generalized' than it
                // already is. So return false, we cannot invalidate.
                //
                // (Note that "inference variables" show up as *bound
                // variables* here, because we are looking at the
                // canonical form.)
                false
            }

            (TyData::BoundVar(_), _) => {
                // If we see a type variable in the potential future
                // solution, we have to be conservative. We don't know
                // what type variable will wind up being! Remember
                // that the future solution could be any instantiation
                // of `ty0` -- or it could leave this variable
                // unbound, if the result is true for all types.
                //
                // (Note that "inference variables" show up as *bound
                // variables* here, because we are looking at the
                // canonical form.)
                true
            }

            (TyData::InferenceVar(_), _) | (_, TyData::InferenceVar(_)) => {
                panic!(
                    "unexpected free inference variable in may-invalidate: {:?} vs {:?}",
                    new, current,
                );
            }

            (TyData::Apply(apply1), TyData::Apply(apply2)) => {
                self.aggregate_application_tys(apply1, apply2)
            }

            (TyData::Placeholder(p1), TyData::Placeholder(p2)) => {
                self.aggregate_placeholder_tys(p1, p2)
            }

            (TyData::Alias(alias1), TyData::Alias(alias2)) => {
                self.aggregate_alias_tys(alias1, alias2)
            }

            // For everything else, be conservative here and just say we may invalidate.
            (TyData::Function(_), _)
            | (TyData::Dyn(_), _)
            | (TyData::Apply(_), _)
            | (TyData::Placeholder(_), _)
            | (TyData::Alias(_), _) => true,
        }
    }

    fn aggregate_lifetimes<I: Interner>(&mut self, _: &Lifetime<I>, _: &Lifetime<I>) -> bool {
        true
    }

    fn aggregate_application_tys<I: Interner>(
        &mut self,
        new: &ApplicationTy<I>,
        current: &ApplicationTy<I>,
    ) -> bool {
        let ApplicationTy {
            name: new_name,
            substitution: new_substitution,
        } = new;
        let ApplicationTy {
            name: current_name,
            substitution: current_substitution,
        } = current;

        self.aggregate_name_and_substs(
            new_name,
            new_substitution,
            current_name,
            current_substitution,
        )
    }

    fn aggregate_placeholder_tys(
        &mut self,
        new: &PlaceholderIndex,
        current: &PlaceholderIndex,
    ) -> bool {
        new != current
    }

    fn aggregate_alias_tys<I: Interner>(&mut self, new: &AliasTy<I>, current: &AliasTy<I>) -> bool {
        let AliasTy {
            associated_ty_id: new_name,
            substitution: new_substitution,
        } = new;
        let AliasTy {
            associated_ty_id: current_name,
            substitution: current_substitution,
        } = current;

        self.aggregate_name_and_substs(
            new_name,
            new_substitution,
            current_name,
            current_substitution,
        )
    }

    fn aggregate_name_and_substs<N, I>(
        &mut self,
        new_name: N,
        new_substitution: &Substitution<I>,
        current_name: N,
        current_substitution: &Substitution<I>,
    ) -> bool
    where
        N: Copy + Eq + Debug,
        I: Interner,
    {
        if new_name != current_name {
            return true;
        }

        let name = new_name;

        assert_eq!(
            new_substitution.len(),
            current_substitution.len(),
            "does {:?} take {} substitution or {}? can't both be right",
            name,
            new_substitution.len(),
            current_substitution.len()
        );

        new_substitution
            .iter()
            .zip(current_substitution)
            .any(|(new, current)| self.aggregate_parameters(new, current))
    }
}
