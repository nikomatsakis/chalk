#![deny(rust_2018_idioms)]

use crate::display::sanitize_debug_name;
use crate::rust_ir::*;
use chalk_ir::interner::Interner;

use chalk_ir::*;
use std::fmt::Debug;
use std::sync::Arc;

pub mod clauses;
pub mod coherence;
pub mod coinductive_goal;
pub mod display;
pub mod ext;
pub mod goal_builder;
pub mod infer;
pub mod logging;
pub mod logging_db;
pub mod rust_ir;
pub mod solve;
pub mod split;
pub mod wf;

/// Trait representing access to a database of rust types.
///
/// # `*_name` methods
///
/// This trait has a number of `*_name` methods with default implementations.
/// These are used in the implementation for [`LoggingRustIrDatabase`], so that
/// when printing `.chalk` files equivalent to the data used, we can use real
/// names.
///
/// The default implementations simply fall back to calling [`Interner`] debug
/// methods, and printing `"UnknownN"` (where `N` is the demultiplexing integer)
/// if those methods return `None`.
///
/// The [`display::sanitize_debug_name`] utility is used in the default
/// implementations, and might be useful when providing custom implementations.
///
/// [`LoggingRustIrDatabase`]: crate::logging_db::LoggingRustIrDatabase
/// [`display::sanitize_debug_name`]: crate::display::sanitize_debug_name
/// [`Interner`]: Interner
pub trait RustIrDatabase<I: Interner>: Debug {
    /// Returns any "custom program clauses" that do not derive from
    /// Rust IR. Used only in testing the underlying solver.
    fn custom_clauses(&self) -> Vec<ProgramClause<I>>;

    /// Returns the datum for the associated type with the given id.
    fn associated_ty_data(&self, ty: AssocTypeId<I>) -> Arc<AssociatedTyDatum<I>>;

    /// Returns the datum for the associated conts with the given id.
    fn associated_const_data(&self, ty: AssocConstId<I>) -> Arc<AssociatedConstDatum<I>>;

    /// Returns the datum for the definition with the given id.
    fn trait_datum(&self, trait_id: TraitId<I>) -> Arc<TraitDatum<I>>;

    /// Returns the datum for the ADT with the given id.
    fn adt_datum(&self, adt_id: AdtId<I>) -> Arc<AdtDatum<I>>;

    /// Returns the generator datum for the generator with the given id.
    fn generator_datum(&self, generator_id: GeneratorId<I>) -> Arc<GeneratorDatum<I>>;

    /// Returns the generator witness datum for the generator with the given id.
    fn generator_witness_datum(
        &self,
        generator_id: GeneratorId<I>,
    ) -> Arc<GeneratorWitnessDatum<I>>;

    /// Returns the representation for the ADT definition with the given id.
    fn adt_repr(&self, id: AdtId<I>) -> Arc<AdtRepr<I>>;

    /// Returns the datum for the fn definition with the given id.
    fn fn_def_datum(&self, fn_def_id: FnDefId<I>) -> Arc<FnDefDatum<I>>;

    /// Returns the datum for the impl with the given id.
    fn impl_datum(&self, impl_id: ImplId<I>) -> Arc<ImplDatum<I>>;

    /// Returns the `AssociatedTyValue` with the given id.
    fn associated_ty_value(&self, id: AssociatedTyValueId<I>) -> Arc<AssociatedTyValue<I>>;

    /// Returns the `AssociatedConstValue` with the given id.
    fn associated_const_value(&self, id: AssociatedConstValueId<I>)
        -> Arc<AssociatedConstValue<I>>;

    /// Returns the `OpaqueTyDatum` with the given id.
    fn opaque_ty_data(&self, id: OpaqueTyId<I>) -> Arc<OpaqueTyDatum<I>>;

    /// Returns the "hidden type" corresponding with the opaque type.
    fn hidden_opaque_type(&self, id: OpaqueTyId<I>) -> Ty<I>;

    /// Returns a list of potentially relevant impls for a given
    /// trait-id; we also supply the type parameters that we are
    /// trying to match (if known: these parameters may contain
    /// inference variables, for example). The implementor is
    /// permitted to return any superset of the applicable impls;
    /// chalk will narrow down the list to only those that truly
    /// apply. The parameters are provided as a "hint" to help the
    /// implementor do less work, but can be completely ignored if
    /// desired.
    ///
    /// The `binders` are for the `parameters`; if the recursive solver is used,
    /// the parameters can contain bound variables referring to these binders.
    fn impls_for_trait(
        &self,
        trait_id: TraitId<I>,
        parameters: &[GenericArg<I>],
        binders: &CanonicalVarKinds<I>,
    ) -> Vec<ImplId<I>>;

    /// Returns the impls that require coherence checking. This is not the
    /// full set of impls that exist:
    ///
    /// - It can exclude impls not defined in the current crate.
    /// - It can exclude "built-in" impls, like those for closures; only the
    ///   impls actually written by users need to be checked.
    fn local_impls_to_coherence_check(&self, trait_id: TraitId<I>) -> Vec<ImplId<I>>;

    /// Returns true if there is an explicit impl of the auto trait
    /// `auto_trait_id` for the type `ty`. This is part of
    /// the auto trait handling -- if there is no explicit impl given
    /// by the user for `ty`, then we provide default impls
    /// (otherwise, we rely on the impls the user gave).
    fn impl_provided_for(&self, auto_trait_id: TraitId<I>, ty: &TyKind<I>) -> bool;

    /// Returns id of a trait lang item, if found
    fn well_known_trait_id(&self, well_known_trait: WellKnownTrait) -> Option<TraitId<I>>;

    /// Calculates program clauses from an env. This is intended to call the
    /// `program_clauses_for_env` function and then possibly cache the clauses.
    fn program_clauses_for_env(&self, environment: &Environment<I>) -> ProgramClauses<I>;

    fn interner(&self) -> &I;

    /// Check if a trait is object safe
    fn is_object_safe(&self, trait_id: TraitId<I>) -> bool;

    /// Gets the `ClosureKind` for a given closure and substitution.
    fn closure_kind(&self, closure_id: ClosureId<I>, substs: &Substitution<I>) -> ClosureKind;

    /// Gets the inputs and output for a given closure id and substitution. We
    /// pass both the `ClosureId` and it's `Substituion` to give implementors
    /// the freedom to store associated data in the substitution (like rustc) or
    /// separately (like chalk-integration).
    fn closure_inputs_and_output(
        &self,
        closure_id: ClosureId<I>,
        substs: &Substitution<I>,
    ) -> Binders<FnDefInputsAndOutputDatum<I>>;

    /// Gets the upvars as a `Ty` for a given closure id and substitution. There
    /// are no restrictions on the type of upvars.
    fn closure_upvars(&self, closure_id: ClosureId<I>, substs: &Substitution<I>) -> Binders<Ty<I>>;

    /// Gets the substitution for the closure when used as a function.
    /// For example, for the following (not-quite-)rust code:
    /// ```ignore
    /// let foo = |a: &mut u32| { a += 1; };
    /// let c: &'a u32 = &0;
    /// foo(c);
    /// ```
    ///
    /// This would return a `Substitution` of `[&'a]`. This could either be
    /// substituted into the inputs and output, or into the upvars.
    fn closure_fn_substitution(
        &self,
        closure_id: ClosureId<I>,
        substs: &Substitution<I>,
    ) -> Substitution<I>;

    fn unification_database(&self) -> &dyn UnificationDatabase<I>;

    /// Retrieves a trait's original name. No uniqueness guarantees, but must
    /// be a valid Rust identifier.
    fn trait_name(&self, trait_id: TraitId<I>) -> String {
        sanitize_debug_name(|f| I::debug_trait_id(trait_id, f))
    }

    /// Retrieves a struct's original name. No uniqueness guarantees, but must
    /// be a valid Rust identifier.
    fn adt_name(&self, adt_id: AdtId<I>) -> String {
        sanitize_debug_name(|f| I::debug_adt_id(adt_id, f))
    }

    /// Retrieves the name of an associated type. No uniqueness guarantees, but must
    /// be a valid Rust identifier.
    fn assoc_type_name(&self, assoc_ty_id: AssocTypeId<I>) -> String {
        sanitize_debug_name(|f| I::debug_assoc_type_id(assoc_ty_id, f))
    }

    /// Retrieves the name of an associated constant. No uniqueness guarantees, but must
    /// be a valid Rust identifier.
    fn assoc_const_name(&self, assoc_const_id: AssocConstId<I>) -> String {
        sanitize_debug_name(|f| I::debug_assoc_const_id(assoc_const_id, f))
    }

    /// Retrieves the name of an opaque type. No uniqueness guarantees, but must
    /// be a valid Rust identifier.
    fn opaque_type_name(&self, opaque_ty_id: OpaqueTyId<I>) -> String {
        sanitize_debug_name(|f| I::debug_opaque_ty_id(opaque_ty_id, f))
    }

    /// Retrieves the name of a function definition. No uniqueness guarantees, but must
    /// be a valid Rust identifier.
    fn fn_def_name(&self, fn_def_id: FnDefId<I>) -> String {
        sanitize_debug_name(|f| I::debug_fn_def_id(fn_def_id, f))
    }

    // Retrieves the discriminant type for a type (mirror of rustc `TyS::discriminant_ty`)
    fn discriminant_type(&self, ty: Ty<I>) -> Ty<I>;
}

pub use clauses::program_clauses_for_env;

pub use solve::Guidance;
pub use solve::Solution;
pub use solve::Solver;
pub use solve::SubstitutionResult;

#[macro_use]
mod debug_macros {
    #[macro_export]
    macro_rules! debug_span {
        ($($t: tt)*) => {
            let __span = tracing::debug_span!($($t)*);
            let __span = __span.enter();
        };
    }
}
