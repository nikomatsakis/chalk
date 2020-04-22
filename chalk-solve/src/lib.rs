use chalk_ir::interner::Interner;
use chalk_ir::*;
use chalk_rust_ir::*;
use std::fmt::Debug;
use std::sync::Arc;

#[macro_use]
extern crate tracing;

pub mod clauses;
pub mod coherence;
mod coinductive_goal;
pub mod ext;
mod infer;
mod solve;
pub mod split;
pub mod wf;

pub trait RustIrDatabase<I: Interner>: Debug {
    /// Returns any "custom program clauses" that do not derive from
    /// Rust IR. Used only in testing the underlying solver.
    fn custom_clauses(&self) -> Vec<ProgramClause<I>>;

    /// Returns the datum for the associated type with the given id.
    fn associated_ty_data(&self, ty: AssocTypeId<I>) -> Arc<AssociatedTyDatum<I>>;

    /// Returns the datum for the impl with the given id.
    fn trait_datum(&self, trait_id: TraitId<I>) -> Arc<TraitDatum<I>>;

    /// Returns the datum for the impl with the given id.
    fn struct_datum(&self, struct_id: StructId<I>) -> Arc<StructDatum<I>>;

    /// Returns the datum for the impl with the given id.
    fn impl_datum(&self, impl_id: ImplId<I>) -> Arc<ImplDatum<I>>;

    /// Returns the `AssociatedTyValue` with the given id.
    fn associated_ty_value(&self, id: AssociatedTyValueId<I>) -> Arc<AssociatedTyValue<I>>;

    /// If `id` is a struct id, returns `Some(id)` (but cast to `StructId`).
    fn as_struct_id(&self, id: &TypeName<I>) -> Option<StructId<I>>;

    /// Returns a list of potentially relevant impls for a given
    /// trait-id; we also supply the type parameters that we are
    /// trying to match (if known: these parameters may contain
    /// inference variables, for example). The implementor is
    /// permitted to return any superset of the applicable impls;
    /// chalk will narrow down the list to only those that truly
    /// apply. The parameters are provided as a "hint" to help the
    /// implementor do less work, but can be completely ignored if
    /// desired.
    fn impls_for_trait(&self, trait_id: TraitId<I>, parameters: &[Parameter<I>]) -> Vec<ImplId<I>>;

    /// Returns the impls that require coherence checking. This is not the
    /// full set of impls that exist:
    ///
    /// - It can exclude impls not defined in the current crate.
    /// - It can exclude "built-in" impls, like those for closures; only the
    ///   impls actually written by users need to be checked.
    fn local_impls_to_coherence_check(&self, trait_id: TraitId<I>) -> Vec<ImplId<I>>;

    /// Returns true if there is an explicit impl of the auto trait
    /// `auto_trait_id` for the struct `struct_id`. This is part of
    /// the auto trait handling -- if there is no explicit impl given
    /// by the user for the struct, then we provide default impls
    /// based on the field types (otherwise, we rely on the impls the
    /// user gave).
    fn impl_provided_for(&self, auto_trait_id: TraitId<I>, struct_id: StructId<I>) -> bool;

    fn interner(&self) -> &I;
}

pub use solve::Guidance;
pub use solve::Solution;
pub use solve::Solver;
pub use solve::SolverChoice;
