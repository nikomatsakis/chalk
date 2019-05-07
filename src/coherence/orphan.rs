use crate::coherence::CoherenceError;
use crate::ext::GoalExt;
use crate::solve::SolverChoice;
use crate::RustIrDatabase;
use chalk_ir::cast::*;
use chalk_ir::*;
use failure::Fallible;

// Test if a local impl violates the orphan rules.
//
// For `impl<T> Trait for MyType<T>` we generate:
//
//     forall<T> { LocalImplAllowed(MyType<T>: Trait) }
//
// This must be provable in order to pass the orphan check.
pub fn perform_orphan_check(
    db: &dyn RustIrDatabase,
    solver_choice: SolverChoice,
    impl_id: ImplId,
) -> Fallible<()> {
    debug_heading!("orphan_check(impl={:#?})", impl_id);

    let impl_datum = db.impl_datum(impl_id);
    debug!("impl_datum={:#?}", impl_datum);

    let impl_allowed: Goal = impl_datum
        .binders
        .map_ref(|bound_impl| {
            // Ignoring the polarization of the impl's polarized trait ref
            DomainGoal::LocalImplAllowed(bound_impl.trait_ref.trait_ref().clone())
        })
        .cast();

    let canonical_goal = &impl_allowed.into_closed_goal();
    let is_allowed = solver_choice
        .into_solver()
        .solve(db, canonical_goal)
        .is_some();
    debug!("overlaps = {:?}", is_allowed);

    if !is_allowed {
        let trait_id = impl_datum.binders.value.trait_ref.trait_ref().trait_id;
        let trait_name = db.type_name(trait_id.into());
        Err(CoherenceError::FailedOrphanCheck(trait_name))?;
    }

    Ok(())
}
