use std::{iter, mem::replace};

use chalk_ir::{
    cast::Cast,
    fold::{shift::Shift, Fold, Folder, SuperFold},
    interner::Interner,
    AliasEq, AliasTy, Binders, BoundVar, DebruijnIndex, Fallible, Goal, GoalData, Goals,
    ProgramClause, ProgramClauseData, ProgramClauseImplication, QuantifierKind, Ty, TyData, TyKind,
    VariableKind, VariableKinds,
};

pub fn syn_eq_lower<I: Interner, T: Fold<I>>(interner: &I, clause: &T) -> <T as Fold<I>>::Result {
    let mut folder = SynEqFolder {
        interner,
        new_params: vec![],
        new_goals: vec![],
        binders_len: 0,
    };

    clause
        .fold_with(&mut folder, DebruijnIndex::INNERMOST)
        .unwrap()
}

struct SynEqFolder<'i, I: Interner> {
    interner: &'i I,
    new_params: Vec<VariableKind<I>>,
    new_goals: Vec<Goal<I>>,
    binders_len: usize,
}

impl<'i, I: Interner> Folder<'i, I> for SynEqFolder<'i, I> {
    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I> {
        self
    }

    fn fold_ty(&mut self, ty: &Ty<I>, outer_binder: DebruijnIndex) -> Fallible<Ty<I>> {
        let interner = self.interner;
        let bound_var = BoundVar::new(DebruijnIndex::INNERMOST, self.binders_len);

        let new_ty = TyData::BoundVar(bound_var).intern(interner);
        match ty.data(interner) {
            TyData::Alias(alias @ AliasTy::Projection(_)) => {
                self.new_params.push(VariableKind::Ty(TyKind::General));
                self.new_goals.push(
                    AliasEq {
                        alias: alias.clone(),
                        ty: new_ty.clone(),
                    }
                    .cast(interner),
                );
                self.binders_len += 1;
                ty.super_fold_with(self, outer_binder)?;
                Ok(new_ty)
            }
            TyData::Function(_) => Ok(ty.clone()),
            _ => Ok(ty.super_fold_with(self, outer_binder)?),
        }
    }

    /// Convert a program clause to rem
    ///
    /// Consider this (nonsense) example:
    ///
    /// ```notrust
    /// forall<X> {
    ///     Implemented(<X as Iterator>::Item>: Debug) :-
    ///         Implemented(X: Debug)
    /// }
    /// ```
    ///
    /// we would lower this into:
    ///
    /// ```notrust
    /// forall<X, Y> {
    ///     Implemented(Y: Debug) :-
    ///         AliasEq(<X as Iterator>::Item>, Y),
    ///         Implemented(X: Debug)
    /// }
    /// ```
    fn fold_program_clause(
        &mut self,
        clause: &ProgramClause<I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<ProgramClause<I>> {
        let interner = self.interner;
        assert!(self.new_params.is_empty());
        assert!(self.new_goals.is_empty());

        let ProgramClauseData(binders) = clause.data(interner);

        let implication = binders.skip_binders();
        let mut binders: Vec<_> = binders.binders.as_slice(interner).into();

        // Adjust the outer binder to account for the binder in the program clause
        let outer_binder = outer_binder.shifted_in();

        // First lower the "consequence" -- in our example that is
        //
        // ```
        // Implemented(<X as Iterator>::Item: Debug)
        // ```
        //
        // then save out the `new_params` and `new_goals` vectors to store any new variables created as a result.
        // In this case, that would be the `Y` parameter and `AliasEq(<X as Iterator>::Item, Y)` goals.
        //
        // Note that these new parameters will have indices that come after the existing parameters,
        // so any references to existing parameters like `X` in the "conditions" are still valid even if we insert new parameters.
        self.binders_len = binders.len();

        let consequence = implication.consequence.fold_with(self, outer_binder)?;
        let mut new_params = replace(&mut self.new_params, vec![]);
        let mut new_goals = replace(&mut self.new_goals, vec![]);

        // Now fold the conditions (in our example, Implemented(X: Debug).
        // The resulting list might be expanded to include new AliasEq goals.

        let mut conditions = implication.conditions.fold_with(self, outer_binder)?;

        new_params.extend(replace(&mut self.new_params, vec![]));
        new_goals.extend(replace(&mut self.new_goals, vec![]));

        let constraints = implication.constraints.fold_with(self, outer_binder)?;

        binders.extend(new_params.into_iter());

        conditions = Goals::from_iter(
            interner,
            conditions.iter(interner).cloned().chain(new_goals),
        );

        Ok(ProgramClauseData(Binders::new(
            VariableKinds::from_iter(interner, binders),
            ProgramClauseImplication {
                consequence,
                conditions,
                constraints,
                priority: implication.priority,
            },
        ))
        .intern(interner))
    }

    fn fold_goal(&mut self, goal: &Goal<I>, outer_binder: DebruijnIndex) -> Fallible<Goal<I>> {
        assert!(self.new_params.is_empty());
        assert!(self.new_goals.is_empty());

        let interner = self.interner;
        match goal.data(interner) {
            GoalData::DomainGoal(_) | GoalData::EqGoal(_) => (),
            _ => return goal.super_fold_with(self, outer_binder),
        };

        self.binders_len = 0;
        // shifted in because we introduce a new binder
        let outer_binder = outer_binder.shifted_in();
        let syn_goal = goal
            .shifted_in(interner)
            .super_fold_with(self, outer_binder)?;
        let new_params = replace(&mut self.new_params, vec![]);
        let new_goals = replace(&mut self.new_goals, vec![]);

        if new_params.is_empty() {
            return Ok(goal.clone());
        }

        let goal = GoalData::All(Goals::from_iter(
            interner,
            iter::once(syn_goal).into_iter().chain(new_goals),
        ))
        .intern(interner);

        Ok(GoalData::Quantified(
            QuantifierKind::Exists,
            Binders::new(VariableKinds::from_iter(interner, new_params), goal),
        )
        .intern(interner))
    }

    fn interner(&self) -> &'i I {
        self.interner
    }

    fn target_interner(&self) -> &'i I {
        self.interner
    }
}
