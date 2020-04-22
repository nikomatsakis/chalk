use crate::infer::InferenceTable;
use crate::solve::slg::{self, SlgContext, TruncatingInferenceTable};
use chalk_engine::fallible::Fallible;
use chalk_ir::fold::shift::Shift;
use chalk_ir::fold::Fold;
use chalk_ir::interner::{HasInterner, Interner};
use chalk_ir::zip::{Zip, Zipper};
use chalk_ir::*;

use chalk_engine::context;
use chalk_engine::{ExClause, Literal, TimeStamp};

///////////////////////////////////////////////////////////////////////////
// SLG RESOLVENTS
//
// The "SLG Resolvent" is used to combine a *goal* G with some
// clause or answer *C*.  It unifies the goal's selected literal
// with the clause and then inserts the clause's conditions into
// the goal's list of things to prove, basically. Although this is
// one operation in EWFS, we have specialized variants for merging
// a program clause and an answer (though they share some code in
// common).
//
// Terminology note: The NFTD and RR papers use the term
// "resolvent" to mean both the factor and the resolvent, but EWFS
// distinguishes the two. We follow EWFS here since -- in the code
// -- we tend to know whether there are delayed literals or not,
// and hence to know which code path we actually want.
//
// From EWFS:
//
// Let G be an X-clause A :- D | L1,...Ln, where N > 0, and Li be selected atom.
//
// Let C be an X-clause with no delayed literals. Let
//
//     C' = A' :- L'1...L'm
//
// be a variant of C such that G and C' have no variables in
// common.
//
// Let Li and A' be unified with MGU S.
//
// Then:
//
//     S(A :- D | L1...Li-1, L1'...L'm, Li+1...Ln)
//
// is the SLG resolvent of G with C.

impl<I: Interner> context::ResolventOps<SlgContext<I>> for TruncatingInferenceTable<I> {
    /// Applies the SLG resolvent algorithm to incorporate a program
    /// clause into the main X-clause, producing a new X-clause that
    /// must be solved.
    ///
    /// # Parameters
    ///
    /// - `goal` is the goal G that we are trying to solve
    /// - `clause` is the program clause that may be useful to that end
    #[instrument(level = "debug", skip(self, interner, environment, subst))]
    fn resolvent_clause(
        &mut self,
        interner: &I,
        environment: &Environment<I>,
        goal: &DomainGoal<I>,
        subst: &Substitution<I>,
        clause: &ProgramClause<I>,
    ) -> Fallible<ExClause<SlgContext<I>>> {
        // Relating the above description to our situation:
        //
        // - `goal` G, except with binders for any existential variables.
        //   - Also, we always select the first literal in `ex_clause.literals`, so `i` is 0.
        // - `clause` is C, except with binders for any existential variables.

        // C' in the description above is `consequence :- conditions`.
        //
        // Note that G and C' have no variables in common.
        let ProgramClauseImplication {
            consequence,
            conditions,
            priority: _,
        } = match clause.data(interner) {
            ProgramClauseData::Implies(implication) => implication.clone(),
            ProgramClauseData::ForAll(implication) => self
                .infer
                .instantiate_binders_existentially(interner, implication),
        };
        debug!("consequence = {:?}", consequence);
        debug!("conditions = {:?}", conditions);

        // Unify the selected literal Li with C'.
        let unification_result = self
            .infer
            .unify(interner, environment, goal, &consequence)?;

        // Final X-clause that we will return.
        let mut ex_clause = ExClause {
            subst: subst.clone(),
            ambiguous: false,
            constraints: vec![],
            subgoals: vec![],
            delayed_subgoals: vec![],
            answer_time: TimeStamp::default(),
            floundered_subgoals: vec![],
        };

        // Add the subgoals/region-constraints that unification gave us.
        slg::into_ex_clause(interner, unification_result, &mut ex_clause);

        // Add the `conditions` from the program clause into the result too.
        ex_clause
            .subgoals
            .extend(conditions.iter(interner).map(|c| match c.data(interner) {
                GoalData::Not(c1) => {
                    Literal::Negative(InEnvironment::new(environment, Goal::clone(c1)))
                }
                _ => Literal::Positive(InEnvironment::new(environment, Goal::clone(c))),
            }));

        Ok(ex_clause)
    }

    ///////////////////////////////////////////////////////////////////////////
    // apply_answer_subst
    //
    // Apply answer subst has the job of "plugging in" the answer to a
    // query into the pending ex-clause. To see how it works, it's worth stepping
    // up one level. Imagine that first we are trying to prove a goal A:
    //
    //     A :- T: Foo<Vec<?U>>, ?U: Bar
    //
    // this spawns a subgoal `T: Foo<Vec<?0>>`, and it's this subgoal that
    // has now produced an answer `?0 = u32`. When the goal A spawned the
    // subgoal, it will also have registered a `PendingExClause` with its
    // current state.  At the point where *this* method has been invoked,
    // that pending ex-clause has been instantiated with fresh variables and setup,
    // so we have four bits of incoming information:
    //
    // - `ex_clause`, which is the remaining stuff to prove for the goal A.
    //   Here, the inference variable `?U` has been instantiated with a fresh variable
    //   `?X`.
    //   - `A :- ?X: Bar`
    // - `selected_goal`, which is the thing we were trying to prove when we
    //   spawned the subgoal. It shares inference variables with `ex_clause`.
    //   - `T: Foo<Vec<?X>>`
    // - `answer_table_goal`, which is the subgoal in canonical form:
    //   - `for<type> T: Foo<Vec<?0>>`
    // - `canonical_answer_subst`, which is an answer to `answer_table_goal`.
    //   - `[?0 = u32]`
    //
    // In this case, this function will (a) unify `u32` and `?X` and then
    // (b) return `ex_clause` (extended possibly with new region constraints
    // and subgoals).
    //
    // One way to do this would be to (a) substitute
    // `canonical_answer_subst` into `answer_table_goal` (yielding `T:
    // Foo<Vec<u32>>`) and then (b) instantiate the result with fresh
    // variables (no effect in this instance) and then (c) unify that with
    // `selected_goal` (yielding, indirectly, that `?X = u32`). But that
    // is not what we do: it's inefficient, to start, but it also causes
    // problems because unification of projections can make new
    // sub-goals. That is, even if the answers don't involve any
    // projections, the table goals might, and this can create an infinite
    // loop (see also #74).
    //
    // What we do instead is to (a) instantiate the substitution, which
    // may have free variables in it (in this case, it would not, and the
    // instantiation would have no effect) and then (b) zip
    // `answer_table_goal` and `selected_goal` without having done any
    // substitution. After all, these ought to be basically the same,
    // since `answer_table_goal` was created by canonicalizing (and
    // possibly truncating, but we'll get to that later)
    // `selected_goal`. Then, whenever we reach a "free variable" in
    // `answer_table_goal`, say `?0`, we go to the instantiated answer
    // substitution and lookup the result (in this case, `u32`). We take
    // that result and unify it with whatever we find in `selected_goal`
    // (in this case, `?X`).
    //
    // Let's cover then some corner cases. First off, what is this
    // business of instantiating the answer? Well, the answer may not be a
    // simple type like `u32`, it could be a "family" of types, like
    // `for<type> Vec<?0>` -- i.e., `Vec<X>: Bar` for *any* `X`. In that
    // case, the instantiation would produce a substitution `[?0 :=
    // Vec<?Y>]` (note that the key is not affected, just the value). So
    // when we do the unification, instead of unifying `?X = u32`, we
    // would unify `?X = Vec<?Y>`.
    //
    // Next, truncation. One key thing is that the `answer_table_goal` may
    // not be *exactly* the same as the `selected_goal` -- we will
    // truncate it if it gets too deep. so, in our example, it may be that
    // instead of `answer_table_goal` being `for<type> T: Foo<Vec<?0>>`,
    // it could have been truncated to `for<type> T: Foo<?0>` (which is a
    // more general goal).  In that case, let's say that the answer is
    // still `[?0 = u32]`, meaning that `T: Foo<u32>` is true (which isn't
    // actually interesting to our original goal). When we do the zip
    // then, we will encounter `?0` in the `answer_table_goal` and pair
    // that with `Vec<?X>` from the pending goal. We will attempt to unify
    // `Vec<?X>` with `u32` (from the substitution), which will fail. That
    // failure will get propagated back up.

    #[instrument(level = "debug", skip(self, interner))]
    fn apply_answer_subst(
        &mut self,
        interner: &I,
        ex_clause: &mut ExClause<SlgContext<I>>,
        selected_goal: &InEnvironment<Goal<I>>,
        answer_table_goal: &Canonical<InEnvironment<Goal<I>>>,
        canonical_answer_subst: &Canonical<AnswerSubst<I>>,
    ) -> Fallible<()> {
        // C' is now `answer`. No variables in common with G.
        let AnswerSubst {
            subst: answer_subst,

            // Assuming unification succeeds, we incorporate the
            // region constraints from the answer into the result;
            // we'll need them if this answer (which is not yet known
            // to be true) winds up being true, and otherwise (if the
            // answer is false or unknown) it doesn't matter.
            constraints: answer_constraints,

            delayed_subgoals,
        } = self
            .infer
            .instantiate_canonical(interner, &canonical_answer_subst);

        let table_goal = self
            .infer
            .instantiate_canonical(interner, &answer_table_goal);

        AnswerSubstitutor::substitute(
            interner,
            &mut self.infer,
            &selected_goal.environment,
            &answer_subst,
            ex_clause,
            &answer_table_goal.value,
            selected_goal,
        )?;
        ex_clause.constraints.extend(answer_constraints);

        for delayed_subgoal in delayed_subgoals {
            // FIXME: is this always valid or would we ever run
            // into an issue with normalization? (Would this even
            // be a "trivial self-cycle"?)
            // Only add the delayed_subgoals to the ex-clause if
            // it isn't a trivial self-cycle
            if delayed_subgoal.goal != table_goal.goal {
                ex_clause.delayed_subgoals.push(delayed_subgoal);
            }
        }

        Ok(())
    }
}

struct AnswerSubstitutor<'t, I: Interner> {
    table: &'t mut InferenceTable<I>,
    environment: &'t Environment<I>,
    answer_subst: &'t Substitution<I>,

    /// Tracks the debrujn index of the first binder that is outside
    /// the term we are traversing. This starts as `DebruijnIndex::INNERMOST`,
    /// since we have not yet traversed *any* binders, but when we visit
    /// the inside of a binder, it would be incremented.
    ///
    /// Example: If we are visiting `(for<type> A, B, C, for<type> for<type> D)`,
    /// then this would be:
    ///
    /// * `1`, when visiting `A`,
    /// * `0`, when visiting `B` and `C`,
    /// * `2`, when visiting `D`.
    outer_binder: DebruijnIndex,

    ex_clause: &'t mut ExClause<SlgContext<I>>,
    interner: &'t I,
}

impl<I: Interner> AnswerSubstitutor<'_, I> {
    fn substitute<T: Zip<I>>(
        interner: &I,
        table: &mut InferenceTable<I>,
        environment: &Environment<I>,
        answer_subst: &Substitution<I>,
        ex_clause: &mut ExClause<SlgContext<I>>,
        answer: &T,
        pending: &T,
    ) -> Fallible<()> {
        let mut this = AnswerSubstitutor {
            interner,
            table,
            environment,
            answer_subst,
            ex_clause,
            outer_binder: DebruijnIndex::INNERMOST,
        };
        Zip::zip_with(&mut this, answer, pending)?;
        Ok(())
    }

    fn unify_free_answer_var(
        &mut self,
        interner: &I,
        answer_var: BoundVar,
        pending: ParameterKind<&Ty<I>, &Lifetime<I>>,
    ) -> Fallible<bool> {
        let answer_index = match answer_var.index_if_bound_at(self.outer_binder) {
            Some(index) => index,

            // This variable is bound in the answer, not free, so it
            // doesn't represent a reference into the answer substitution.
            None => return Ok(false),
        };

        let answer_param = self.answer_subst.at(interner, answer_index);

        let pending_shifted = pending
            .shifted_out_to(interner, self.outer_binder)
            .unwrap_or_else(|_| {
                panic!(
                    "truncate extracted a pending value that references internal binder: {:?}",
                    pending,
                )
            });

        slg::into_ex_clause(
            interner,
            self.table.unify(
                interner,
                &self.environment,
                answer_param,
                &Parameter::new(interner, pending_shifted),
            )?,
            self.ex_clause,
        );

        Ok(true)
    }

    /// When we encounter a variable in the answer goal, we first try
    /// `unify_free_answer_var`. Assuming that this fails, the
    /// variable must be a bound variable in the answer goal -- in
    /// that case, there should be a corresponding bound variable in
    /// the pending goal. This bit of code just checks that latter
    /// case.
    fn assert_matching_vars(
        &mut self,
        answer_var: BoundVar,
        pending_var: BoundVar,
    ) -> Fallible<()> {
        let BoundVar {
            debruijn: answer_depth,
            index: answer_index,
        } = answer_var;
        let BoundVar {
            debruijn: pending_depth,
            index: pending_index,
        } = pending_var;

        // Both bound variables are bound within the term we are matching
        assert!(answer_depth.within(self.outer_binder));

        // They are bound at the same (relative) depth
        assert_eq!(answer_depth, pending_depth);

        // They are bound at the same index within the binder
        assert_eq!(answer_index, pending_index,);

        Ok(())
    }
}

impl<'i, I: Interner> Zipper<'i, I> for AnswerSubstitutor<'i, I> {
    fn zip_tys(&mut self, answer: &Ty<I>, pending: &Ty<I>) -> Fallible<()> {
        let interner = self.interner;

        if let Some(pending) = self.table.normalize_shallow(interner, pending) {
            return Zip::zip_with(self, answer, &pending);
        }

        // If the answer has a variable here, then this is one of the
        // "inputs" to the subgoal table. We need to extract the
        // resulting answer that the subgoal found and unify it with
        // the value from our "pending subgoal".
        if let TyData::BoundVar(answer_depth) = answer.data(interner) {
            if self.unify_free_answer_var(interner, *answer_depth, ParameterKind::Ty(pending))? {
                return Ok(());
            }
        }

        // Otherwise, the answer and the selected subgoal ought to be a perfect match for
        // one another.
        match (answer.data(interner), pending.data(interner)) {
            (TyData::BoundVar(answer_depth), TyData::BoundVar(pending_depth)) => {
                self.assert_matching_vars(*answer_depth, *pending_depth)
            }

            (TyData::Apply(answer), TyData::Apply(pending)) => Zip::zip_with(self, answer, pending),

            (TyData::Dyn(answer), TyData::Dyn(pending)) => Zip::zip_with(self, answer, pending),

            (TyData::Alias(answer), TyData::Alias(pending)) => Zip::zip_with(self, answer, pending),

            (TyData::Placeholder(answer), TyData::Placeholder(pending)) => {
                Zip::zip_with(self, answer, pending)
            }

            (TyData::Function(answer), TyData::Function(pending)) => {
                self.outer_binder.shift_in();
                Zip::zip_with(self, &answer.substitution, &pending.substitution)?;
                self.outer_binder.shift_out();
                Ok(())
            }

            (TyData::InferenceVar(_), _) | (_, TyData::InferenceVar(_)) => panic!(
                "unexpected inference var in answer `{:?}` or pending goal `{:?}`",
                answer, pending,
            ),

            (TyData::BoundVar(_), _)
            | (TyData::Apply(_), _)
            | (TyData::Dyn(_), _)
            | (TyData::Alias(_), _)
            | (TyData::Placeholder(_), _)
            | (TyData::Function(_), _) => panic!(
                "structural mismatch between answer `{:?}` and pending goal `{:?}`",
                answer, pending,
            ),
        }
    }

    fn zip_lifetimes(&mut self, answer: &Lifetime<I>, pending: &Lifetime<I>) -> Fallible<()> {
        let interner = self.interner;
        if let Some(pending) = self.table.normalize_lifetime(interner, pending) {
            return Zip::zip_with(self, answer, &pending);
        }

        if let LifetimeData::BoundVar(answer_depth) = answer.data(interner) {
            if self.unify_free_answer_var(
                interner,
                *answer_depth,
                ParameterKind::Lifetime(pending),
            )? {
                return Ok(());
            }
        }

        match (answer.data(interner), pending.data(interner)) {
            (LifetimeData::BoundVar(answer_depth), LifetimeData::BoundVar(pending_depth)) => {
                self.assert_matching_vars(*answer_depth, *pending_depth)
            }

            (LifetimeData::Placeholder(_), LifetimeData::Placeholder(_)) => {
                assert_eq!(answer, pending);
                Ok(())
            }

            (LifetimeData::InferenceVar(_), _) | (_, LifetimeData::InferenceVar(_)) => panic!(
                "unexpected inference var in answer `{:?}` or pending goal `{:?}`",
                answer, pending,
            ),

            (LifetimeData::BoundVar(_), _) | (LifetimeData::Placeholder(_), _) => panic!(
                "structural mismatch between answer `{:?}` and pending goal `{:?}`",
                answer, pending,
            ),

            (LifetimeData::Phantom(..), _) => unreachable!(),
        }
    }

    fn zip_binders<T>(&mut self, answer: &Binders<T>, pending: &Binders<T>) -> Fallible<()>
    where
        T: HasInterner<Interner = I> + Zip<I> + Fold<I, Result = T>,
    {
        self.outer_binder.shift_in();
        Zip::zip_with(self, answer.skip_binders(), pending.skip_binders())?;
        self.outer_binder.shift_out();
        Ok(())
    }

    fn interner(&self) -> &'i I {
        self.interner
    }
}
