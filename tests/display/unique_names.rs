use chalk_integration::{program::Program, query::LoweringDatabase, tls};
use chalk_ir::{interner::Interner, UnificationDatabase};
use chalk_solve::{
    display::{write_items, WriterState},
    RustIrDatabase,
};
use std::marker::PhantomData;
use std::sync::Arc;

use super::util::{program_item_ids, ReparseTestResult};

/// `DuplicateNamesDb` implements `RustIrDatabase`, and returns `Foo` for all
/// requested item names. This allows us to test that names are correctly
/// de-duplicated by the display code.
#[derive(Debug)]
struct DuplicateNamesDb<'a, I, DB>
where
    I: Interner,
    DB: RustIrDatabase<I>,
{
    db: &'a DB,
    _phantom: PhantomData<I>,
}

impl<'a, I, DB> DuplicateNamesDb<'a, I, DB>
where
    I: Interner,
    DB: RustIrDatabase<I>,
{
    fn new(db: &'a DB) -> Self {
        DuplicateNamesDb {
            db,
            _phantom: PhantomData,
        }
    }
}

impl<'a, I, DB> RustIrDatabase<I> for DuplicateNamesDb<'a, I, DB>
where
    I: Interner,
    DB: RustIrDatabase<I>,
{
    fn trait_name(&self, _trait_id: chalk_ir::TraitId<I>) -> String {
        "Foo".to_owned()
    }
    fn adt_name(&self, _adt_id: chalk_ir::AdtId<I>) -> String {
        "Foo".to_owned()
    }
    fn assoc_type_name(&self, _assoc_ty_id: chalk_ir::AssocTypeId<I>) -> String {
        "Foo".to_owned()
    }
    fn assoc_const_name(&self, _assoc_const_id: chalk_ir::AssocConstId<I>) -> String {
        "Foo".to_owned()
    }
    fn opaque_type_name(&self, _opaque_ty_id: chalk_ir::OpaqueTyId<I>) -> String {
        "Foo".to_owned()
    }
    fn fn_def_name(&self, _fn_def_id: chalk_ir::FnDefId<I>) -> String {
        "Foo".to_owned()
    }
    fn custom_clauses(&self) -> Vec<chalk_ir::ProgramClause<I>> {
        self.db.custom_clauses()
    }
    fn associated_ty_data(
        &self,
        ty: chalk_ir::AssocTypeId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::AssociatedTyDatum<I>> {
        self.db.associated_ty_data(ty)
    }
    fn associated_const_data(
        &self,
        ty: chalk_ir::AssocConstId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::AssociatedConstDatum<I>> {
        self.db.associated_const_data(ty)
    }
    fn trait_datum(
        &self,
        trait_id: chalk_ir::TraitId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::TraitDatum<I>> {
        self.db.trait_datum(trait_id)
    }
    fn adt_datum(
        &self,
        adt_id: chalk_ir::AdtId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::AdtDatum<I>> {
        self.db.adt_datum(adt_id)
    }
    fn adt_repr(&self, id: chalk_ir::AdtId<I>) -> Arc<chalk_solve::rust_ir::AdtRepr<I>> {
        self.db.adt_repr(id)
    }
    fn fn_def_datum(
        &self,
        fn_def_id: chalk_ir::FnDefId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::FnDefDatum<I>> {
        self.db.fn_def_datum(fn_def_id)
    }
    fn impl_datum(
        &self,
        impl_id: chalk_ir::ImplId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::ImplDatum<I>> {
        self.db.impl_datum(impl_id)
    }
    fn associated_ty_value(
        &self,
        id: chalk_solve::rust_ir::AssociatedTyValueId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::AssociatedTyValue<I>> {
        self.db.associated_ty_value(id)
    }
    fn associated_const_value(
        &self,
        id: chalk_solve::rust_ir::AssociatedConstValueId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::AssociatedConstValue<I>> {
        self.db.associated_const_value(id)
    }
    fn generator_datum(
        &self,
        generator_id: chalk_ir::GeneratorId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::GeneratorDatum<I>> {
        self.db.generator_datum(generator_id)
    }
    fn generator_witness_datum(
        &self,
        generator_id: chalk_ir::GeneratorId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::GeneratorWitnessDatum<I>> {
        self.db.generator_witness_datum(generator_id)
    }
    fn opaque_ty_data(
        &self,
        id: chalk_ir::OpaqueTyId<I>,
    ) -> std::sync::Arc<chalk_solve::rust_ir::OpaqueTyDatum<I>> {
        self.db.opaque_ty_data(id)
    }
    fn hidden_opaque_type(&self, id: chalk_ir::OpaqueTyId<I>) -> chalk_ir::Ty<I> {
        self.db.hidden_opaque_type(id)
    }
    fn impls_for_trait(
        &self,
        trait_id: chalk_ir::TraitId<I>,
        parameters: &[chalk_ir::GenericArg<I>],
        binders: &chalk_ir::CanonicalVarKinds<I>,
    ) -> Vec<chalk_ir::ImplId<I>> {
        self.db.impls_for_trait(trait_id, parameters, binders)
    }
    fn local_impls_to_coherence_check(
        &self,
        trait_id: chalk_ir::TraitId<I>,
    ) -> Vec<chalk_ir::ImplId<I>> {
        self.db.local_impls_to_coherence_check(trait_id)
    }
    fn impl_provided_for(
        &self,
        auto_trait_id: chalk_ir::TraitId<I>,
        app_ty: &chalk_ir::TyKind<I>,
    ) -> bool {
        self.db.impl_provided_for(auto_trait_id, app_ty)
    }
    fn well_known_trait_id(
        &self,
        well_known_trait: chalk_solve::rust_ir::WellKnownTrait,
    ) -> Option<chalk_ir::TraitId<I>> {
        self.db.well_known_trait_id(well_known_trait)
    }
    fn program_clauses_for_env(
        &self,
        environment: &chalk_ir::Environment<I>,
    ) -> chalk_ir::ProgramClauses<I> {
        self.db.program_clauses_for_env(environment)
    }
    fn interner(&self) -> &I {
        self.db.interner()
    }
    fn is_object_safe(&self, trait_id: chalk_ir::TraitId<I>) -> bool {
        self.db.is_object_safe(trait_id)
    }
    fn closure_kind(
        &self,
        closure_id: chalk_ir::ClosureId<I>,
        substs: &chalk_ir::Substitution<I>,
    ) -> chalk_solve::rust_ir::ClosureKind {
        self.db.closure_kind(closure_id, substs)
    }
    fn closure_inputs_and_output(
        &self,
        closure_id: chalk_ir::ClosureId<I>,
        substs: &chalk_ir::Substitution<I>,
    ) -> chalk_ir::Binders<chalk_solve::rust_ir::FnDefInputsAndOutputDatum<I>> {
        self.db.closure_inputs_and_output(closure_id, substs)
    }
    fn closure_upvars(
        &self,
        closure_id: chalk_ir::ClosureId<I>,
        substs: &chalk_ir::Substitution<I>,
    ) -> chalk_ir::Binders<chalk_ir::Ty<I>> {
        self.db.closure_upvars(closure_id, substs)
    }
    fn closure_fn_substitution(
        &self,
        closure_id: chalk_ir::ClosureId<I>,
        substs: &chalk_ir::Substitution<I>,
    ) -> chalk_ir::Substitution<I> {
        self.db.closure_fn_substitution(closure_id, substs)
    }

    fn discriminant_type(&self, ty: chalk_ir::Ty<I>) -> chalk_ir::Ty<I> {
        self.db.discriminant_type(ty)
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<I> {
        self.db.unification_database()
    }
}

/// Writes the given program with all names duplicated and then deduplicated by
/// display code.
///
/// This additionally tests to ensure that duplicated names are deduplicated
/// across `write_items` calls, by making one write_items call per item.
pub fn write_program_duplicated_names(db: &Program) -> String {
    let mut out = String::new();
    let ids = program_item_ids(db);
    let db = DuplicateNamesDb::new(db);
    let ws = WriterState::new(db);
    // Test that names are preserved between write_items calls
    for id in ids {
        write_items(&mut out, &ws, std::iter::once(id)).unwrap();
    }
    out
}

/// Tests that a given source file can function given a database which always
/// returns the same name for all variables.
///
/// Only checks that the resulting program parses, not that it matches any
/// particular format. Use returned data to perform further checks.
pub fn run_reparse_with_duplicate_names<'a>(program_text: &'a str) -> ReparseTestResult<'a> {
    let original_db = chalk_integration::db::ChalkDatabase::with(program_text, <_>::default());
    let original_program = original_db.program_ir().unwrap_or_else(|e| {
        panic!(
            "unable to lower test program:\n{}\nSource:\n{}\n",
            e, program_text
        )
    });
    let output_text = tls::set_current_program(&original_program, || {
        write_program_duplicated_names(&*original_program)
    });
    let output_db = chalk_integration::db::ChalkDatabase::with(&output_text, <_>::default());
    let output_program = output_db.program_ir().unwrap_or_else(|e| {
        panic!(
            "error lowering writer output:\n{}\nNew source:\n{}\n",
            e, output_text
        )
    });
    eprintln!("\nTest Succeeded:\n\n{}\n---", output_text);
    ReparseTestResult {
        original_text: program_text,
        output_text,
        target_text: "",
        original_program: original_program.clone(),
        output_program,
        target_program: original_program,
    }
}

/// Performs a test on chalk's `display` code to render programs as `.chalk` files.
macro_rules! reparse_with_duplicated_names {
    (program $program:tt) => {
        run_reparse_with_duplicate_names(crate::display::util::strip_leading_trailing_braces(
            stringify!($program),
        ))
    };
}

#[test]
fn lots_of_structs() {
    reparse_with_duplicated_names! {
        program {
            struct A {}
            struct B {}
            struct C {}
            struct D {}
        }
    };
}
#[test]
fn lots_of_traits() {
    reparse_with_duplicated_names! {
        program {
            trait A {}
            trait B {}
            trait C {}
            trait D {}
        }
    };
}
#[test]
fn traits_and_structs() {
    reparse_with_duplicated_names! {
        program {
            trait A {}
            struct B {}
            trait C {}
            struct D {}
        }
    };
}
#[test]
fn assoc_types() {
    reparse_with_duplicated_names! {
        program {
            trait A {
                type A;
                type A;
                type C;
                type D;
            }
            trait B {
                type A;
                type B;
                type C;
                type D;
            }
            struct Test<T> where T: B {
                field: <T as B>::C,
            }
        }
    };
}
