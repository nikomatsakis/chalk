//! Provides wrappers over `RustIrDatabase` which record used definitions and write
//! `.chalk` files containing those definitions.
use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering},
    collections::BTreeSet,
    fmt::{self, Debug, Display},
    io::Write,
    marker::PhantomData,
    sync::Arc,
    sync::Mutex,
};

use crate::rust_ir::*;
use crate::{
    display::{self, WriterState},
    RustIrDatabase,
};
use chalk_ir::{interner::Interner, *};

mod id_collector;

/// Wraps another `RustIrDatabase` (`DB`) and records which definitions are
/// used.
///
/// A full .chalk file containing all used definitions can be recovered through
/// `LoggingRustIrDatabase`'s `Display` implementation.
///
/// Uses a separate type, `P`, for the database stored inside to account for
/// `Arc` or wrapping other storage mediums.
#[derive(Debug)]
pub struct LoggingRustIrDatabase<I, DB, P = DB>
where
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
    I: Interner,
{
    ws: WriterState<I, DB, P>,
    def_ids: Mutex<BTreeSet<RecordedItemId<I>>>,
    _phantom: PhantomData<DB>,
}

impl<I, DB, P> LoggingRustIrDatabase<I, DB, P>
where
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
    I: Interner,
{
    pub fn new(db: P) -> Self {
        LoggingRustIrDatabase {
            ws: WriterState::new(db),
            def_ids: Default::default(),
            _phantom: PhantomData,
        }
    }
}

impl<I, DB, P> Display for LoggingRustIrDatabase<I, DB, P>
where
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
    I: Interner,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let def_ids = self.def_ids.lock().unwrap();
        let stub_ids = id_collector::collect_unrecorded_ids(self.ws.db(), &def_ids);
        display::write_stub_items(f, &self.ws, stub_ids)?;
        display::write_items(f, &self.ws, def_ids.iter().copied())
    }
}

impl<I, DB, P> LoggingRustIrDatabase<I, DB, P>
where
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
    I: Interner,
{
    fn record(&self, id: impl Into<RecordedItemId<I>>) {
        self.def_ids.lock().unwrap().insert(id.into());
    }

    fn record_all<T, U>(&self, ids: T)
    where
        T: IntoIterator<Item = U>,
        U: Into<RecordedItemId<I>>,
    {
        self.def_ids
            .lock()
            .unwrap()
            .extend(ids.into_iter().map(Into::into));
    }
}

impl<I, DB, P> UnificationDatabase<I> for LoggingRustIrDatabase<I, DB, P>
where
    DB: RustIrDatabase<I>,
    P: Borrow<DB> + Debug,
    I: Interner,
{
    fn fn_def_variance(&self, fn_def_id: chalk_ir::FnDefId<I>) -> Variances<I> {
        self.ws
            .db()
            .unification_database()
            .fn_def_variance(fn_def_id)
    }

    fn adt_variance(&self, adt_id: chalk_ir::AdtId<I>) -> Variances<I> {
        self.ws.db().unification_database().adt_variance(adt_id)
    }
}

impl<I, DB, P> RustIrDatabase<I> for LoggingRustIrDatabase<I, DB, P>
where
    DB: RustIrDatabase<I>,
    P: Borrow<DB> + Debug,
    I: Interner,
{
    fn custom_clauses(&self) -> Vec<chalk_ir::ProgramClause<I>> {
        self.ws.db().custom_clauses()
    }

    fn associated_ty_data(
        &self,
        ty: chalk_ir::AssocTypeId<I>,
    ) -> Arc<crate::rust_ir::AssociatedTyDatum<I>> {
        let ty_datum = self.ws.db().associated_ty_data(ty);
        self.record(ty_datum.trait_id);
        ty_datum
    }

    fn associated_const_data(
        &self,
        ty: chalk_ir::AssocConstId<I>,
    ) -> Arc<crate::rust_ir::AssociatedConstDatum<I>> {
        let ty_datum = self.ws.db().associated_const_data(ty);
        self.record(ty_datum.trait_id);
        ty_datum
    }

    fn trait_datum(&self, trait_id: TraitId<I>) -> Arc<TraitDatum<I>> {
        self.record(trait_id);
        self.ws.db().trait_datum(trait_id)
    }

    fn adt_datum(&self, adt_id: AdtId<I>) -> Arc<AdtDatum<I>> {
        self.record(adt_id);
        self.ws.db().adt_datum(adt_id)
    }

    fn generator_datum(&self, generator_id: GeneratorId<I>) -> Arc<GeneratorDatum<I>> {
        self.record(generator_id);
        self.ws.db().borrow().generator_datum(generator_id)
    }

    fn generator_witness_datum(
        &self,
        generator_id: GeneratorId<I>,
    ) -> Arc<GeneratorWitnessDatum<I>> {
        self.record(generator_id);
        self.ws.db().borrow().generator_witness_datum(generator_id)
    }

    fn adt_repr(&self, id: AdtId<I>) -> Arc<AdtRepr<I>> {
        self.record(id);
        self.ws.db().adt_repr(id)
    }

    fn impl_datum(&self, impl_id: ImplId<I>) -> Arc<ImplDatum<I>> {
        self.record(impl_id);
        self.ws.db().impl_datum(impl_id)
    }

    fn hidden_opaque_type(&self, id: OpaqueTyId<I>) -> Ty<I> {
        self.record(id);
        self.ws.db().hidden_opaque_type(id)
    }

    fn associated_ty_value(
        &self,
        id: crate::rust_ir::AssociatedTyValueId<I>,
    ) -> Arc<crate::rust_ir::AssociatedTyValue<I>> {
        let value = self.ws.db().associated_ty_value(id);
        self.record(value.impl_id);
        value
    }

    fn associated_const_value(
        &self,
        id: crate::rust_ir::AssociatedConstValueId<I>,
    ) -> Arc<crate::rust_ir::AssociatedConstValue<I>> {
        let value = self.ws.db().associated_const_value(id);
        self.record(value.impl_id);
        value
    }

    fn opaque_ty_data(&self, id: OpaqueTyId<I>) -> Arc<OpaqueTyDatum<I>> {
        self.record(id);
        self.ws.db().opaque_ty_data(id)
    }

    fn impls_for_trait(
        &self,
        trait_id: TraitId<I>,
        parameters: &[chalk_ir::GenericArg<I>],
        binders: &CanonicalVarKinds<I>,
    ) -> Vec<ImplId<I>> {
        self.record(trait_id);
        let impl_ids = self.ws.db().impls_for_trait(trait_id, parameters, binders);
        self.record_all(impl_ids.iter().copied());
        impl_ids
    }

    fn local_impls_to_coherence_check(&self, trait_id: TraitId<I>) -> Vec<ImplId<I>> {
        self.record(trait_id);
        self.ws.db().local_impls_to_coherence_check(trait_id)
    }

    fn impl_provided_for(&self, auto_trait_id: TraitId<I>, ty: &TyKind<I>) -> bool {
        self.record(auto_trait_id);
        if let TyKind::Adt(adt_id, _) = ty {
            self.record(*adt_id);
        }
        self.ws.db().impl_provided_for(auto_trait_id, ty)
    }

    fn well_known_trait_id(
        &self,
        well_known_trait: crate::rust_ir::WellKnownTrait,
    ) -> Option<TraitId<I>> {
        let trait_id = self.ws.db().well_known_trait_id(well_known_trait);
        trait_id.map(|id| self.record(id));
        trait_id
    }

    fn program_clauses_for_env(
        &self,
        environment: &chalk_ir::Environment<I>,
    ) -> chalk_ir::ProgramClauses<I> {
        self.ws.db().program_clauses_for_env(environment)
    }

    fn interner(&self) -> &I {
        self.ws.db().interner()
    }

    fn trait_name(&self, trait_id: TraitId<I>) -> String {
        self.ws.db().trait_name(trait_id)
    }

    fn adt_name(&self, adt_id: AdtId<I>) -> String {
        self.ws.db().adt_name(adt_id)
    }

    fn assoc_type_name(&self, assoc_ty_id: AssocTypeId<I>) -> String {
        self.ws.db().assoc_type_name(assoc_ty_id)
    }

    fn assoc_const_name(&self, assoc_const_id: AssocConstId<I>) -> String {
        self.ws.db().assoc_const_name(assoc_const_id)
    }

    fn opaque_type_name(&self, opaque_ty_id: OpaqueTyId<I>) -> String {
        self.ws.db().opaque_type_name(opaque_ty_id)
    }

    fn is_object_safe(&self, trait_id: TraitId<I>) -> bool {
        self.record(trait_id);
        self.ws.db().is_object_safe(trait_id)
    }

    fn fn_def_datum(&self, fn_def_id: chalk_ir::FnDefId<I>) -> Arc<FnDefDatum<I>> {
        self.record(fn_def_id);
        self.ws.db().fn_def_datum(fn_def_id)
    }

    fn fn_def_name(&self, fn_def_id: FnDefId<I>) -> String {
        self.ws.db().fn_def_name(fn_def_id)
    }

    fn closure_kind(&self, closure_id: ClosureId<I>, substs: &Substitution<I>) -> ClosureKind {
        // TODO: record closure IDs
        self.ws.db().closure_kind(closure_id, substs)
    }

    fn closure_inputs_and_output(
        &self,
        closure_id: ClosureId<I>,
        substs: &Substitution<I>,
    ) -> Binders<FnDefInputsAndOutputDatum<I>> {
        // TODO: record closure IDs
        self.ws.db().closure_inputs_and_output(closure_id, substs)
    }

    fn closure_upvars(&self, closure_id: ClosureId<I>, substs: &Substitution<I>) -> Binders<Ty<I>> {
        // TODO: record closure IDs
        self.ws.db().closure_upvars(closure_id, substs)
    }

    fn closure_fn_substitution(
        &self,
        closure_id: ClosureId<I>,
        substs: &Substitution<I>,
    ) -> Substitution<I> {
        // TODO: record closure IDs
        self.ws.db().closure_fn_substitution(closure_id, substs)
    }

    fn discriminant_type(&self, ty: Ty<I>) -> Ty<I> {
        self.ws.db().discriminant_type(ty)
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<I> {
        self
    }
}

/// Wraps a [`RustIrDatabase`], and, when dropped, writes out all used
/// definition to the given file.
///
/// Uses [`LoggingRustIrDatabase`] internally.
///
/// Uses a separate type, `P`, for the database stored inside to account for
/// `Arc` or wrapping other storage mediums.
pub struct WriteOnDropRustIrDatabase<I, W, DB, P = DB>
where
    I: Interner,
    W: Write,
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
{
    db: LoggingRustIrDatabase<I, DB, P>,
    write: W,
}

impl<I, W, DB, P> fmt::Debug for WriteOnDropRustIrDatabase<I, W, DB, P>
where
    I: Interner,
    W: Write,
    DB: RustIrDatabase<I>,
    P: Borrow<DB> + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WriteOnDropRustIrDatabase")
            .field("db", &self.db)
            .field("write", &"<opaque>")
            .finish()
    }
}

impl<I, W, DB, P> WriteOnDropRustIrDatabase<I, W, DB, P>
where
    I: Interner,
    W: Write,
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
{
    pub fn new(db: P, write: W) -> Self {
        WriteOnDropRustIrDatabase {
            db: LoggingRustIrDatabase::new(db),
            write,
        }
    }

    pub fn from_logging_db(db: LoggingRustIrDatabase<I, DB, P>, write: W) -> Self {
        WriteOnDropRustIrDatabase { db, write }
    }
}

impl<I, W, DB, P> Drop for WriteOnDropRustIrDatabase<I, W, DB, P>
where
    I: Interner,
    W: Write,
    DB: RustIrDatabase<I>,
    P: Borrow<DB>,
{
    fn drop(&mut self) {
        write!(self.write, "{}", self.db)
            .and_then(|_| self.write.flush())
            .expect("expected to be able to write rust ir database");
    }
}

impl<I, W, DB, P> UnificationDatabase<I> for WriteOnDropRustIrDatabase<I, W, DB, P>
where
    I: Interner,
    W: Write,
    DB: RustIrDatabase<I>,
    P: Borrow<DB> + Debug,
{
    fn fn_def_variance(&self, fn_def_id: chalk_ir::FnDefId<I>) -> Variances<I> {
        self.db
            .borrow()
            .unification_database()
            .fn_def_variance(fn_def_id)
    }

    fn adt_variance(&self, adt_id: chalk_ir::AdtId<I>) -> Variances<I> {
        self.db.borrow().unification_database().adt_variance(adt_id)
    }
}

impl<I, W, DB, P> RustIrDatabase<I> for WriteOnDropRustIrDatabase<I, W, DB, P>
where
    I: Interner,
    W: Write,
    DB: RustIrDatabase<I>,
    P: Borrow<DB> + Debug,
{
    fn custom_clauses(&self) -> Vec<chalk_ir::ProgramClause<I>> {
        self.db.custom_clauses()
    }

    fn associated_ty_data(
        &self,
        ty: chalk_ir::AssocTypeId<I>,
    ) -> Arc<crate::rust_ir::AssociatedTyDatum<I>> {
        self.db.associated_ty_data(ty)
    }

    fn associated_const_data(
        &self,
        ty: chalk_ir::AssocConstId<I>,
    ) -> Arc<crate::rust_ir::AssociatedConstDatum<I>> {
        self.db.associated_const_data(ty)
    }

    fn trait_datum(&self, trait_id: TraitId<I>) -> Arc<TraitDatum<I>> {
        self.db.trait_datum(trait_id)
    }

    fn adt_datum(&self, adt_id: AdtId<I>) -> Arc<AdtDatum<I>> {
        self.db.adt_datum(adt_id)
    }

    fn generator_datum(&self, generator_id: GeneratorId<I>) -> Arc<GeneratorDatum<I>> {
        self.db.borrow().generator_datum(generator_id)
    }

    /// Returns the generator witness datum for the generator with the given id.
    fn generator_witness_datum(
        &self,
        generator_id: GeneratorId<I>,
    ) -> Arc<GeneratorWitnessDatum<I>> {
        self.db.borrow().generator_witness_datum(generator_id)
    }

    fn adt_repr(&self, id: AdtId<I>) -> Arc<AdtRepr<I>> {
        self.db.adt_repr(id)
    }

    fn impl_datum(&self, impl_id: ImplId<I>) -> Arc<ImplDatum<I>> {
        self.db.impl_datum(impl_id)
    }

    fn associated_ty_value(
        &self,
        id: crate::rust_ir::AssociatedTyValueId<I>,
    ) -> Arc<crate::rust_ir::AssociatedTyValue<I>> {
        self.db.associated_ty_value(id)
    }

    fn associated_const_value(
        &self,
        id: crate::rust_ir::AssociatedConstValueId<I>,
    ) -> Arc<crate::rust_ir::AssociatedConstValue<I>> {
        self.db.associated_const_value(id)
    }

    fn opaque_ty_data(&self, id: OpaqueTyId<I>) -> Arc<OpaqueTyDatum<I>> {
        self.db.opaque_ty_data(id)
    }

    fn hidden_opaque_type(&self, id: OpaqueTyId<I>) -> Ty<I> {
        self.db.hidden_opaque_type(id)
    }

    fn impls_for_trait(
        &self,
        trait_id: TraitId<I>,
        parameters: &[chalk_ir::GenericArg<I>],
        binders: &CanonicalVarKinds<I>,
    ) -> Vec<ImplId<I>> {
        self.db.impls_for_trait(trait_id, parameters, binders)
    }

    fn local_impls_to_coherence_check(&self, trait_id: TraitId<I>) -> Vec<ImplId<I>> {
        self.db.local_impls_to_coherence_check(trait_id)
    }

    fn impl_provided_for(&self, auto_trait_id: TraitId<I>, ty: &TyKind<I>) -> bool {
        self.db.impl_provided_for(auto_trait_id, ty)
    }

    fn well_known_trait_id(
        &self,
        well_known_trait: crate::rust_ir::WellKnownTrait,
    ) -> Option<TraitId<I>> {
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

    fn is_object_safe(&self, trait_id: TraitId<I>) -> bool {
        self.db.is_object_safe(trait_id)
    }

    fn unification_database(&self) -> &dyn UnificationDatabase<I> {
        self
    }

    fn trait_name(&self, trait_id: TraitId<I>) -> String {
        self.db.trait_name(trait_id)
    }

    fn adt_name(&self, adt_id: AdtId<I>) -> String {
        self.db.adt_name(adt_id)
    }

    fn assoc_type_name(&self, assoc_ty_id: AssocTypeId<I>) -> String {
        self.db.assoc_type_name(assoc_ty_id)
    }

    fn assoc_const_name(&self, assoc_const_id: AssocConstId<I>) -> String {
        self.db.assoc_const_name(assoc_const_id)
    }

    fn opaque_type_name(&self, opaque_ty_id: OpaqueTyId<I>) -> String {
        self.db.opaque_type_name(opaque_ty_id)
    }

    fn fn_def_datum(&self, fn_def_id: chalk_ir::FnDefId<I>) -> Arc<FnDefDatum<I>> {
        self.db.fn_def_datum(fn_def_id)
    }

    fn fn_def_name(&self, fn_def_id: FnDefId<I>) -> String {
        self.db.fn_def_name(fn_def_id)
    }

    fn closure_kind(&self, closure_id: ClosureId<I>, substs: &Substitution<I>) -> ClosureKind {
        // TODO: record closure IDs
        self.db.closure_kind(closure_id, substs)
    }

    fn closure_inputs_and_output(
        &self,
        closure_id: ClosureId<I>,
        substs: &Substitution<I>,
    ) -> Binders<FnDefInputsAndOutputDatum<I>> {
        self.db.closure_inputs_and_output(closure_id, substs)
    }

    fn closure_upvars(&self, closure_id: ClosureId<I>, substs: &Substitution<I>) -> Binders<Ty<I>> {
        self.db.closure_upvars(closure_id, substs)
    }

    fn closure_fn_substitution(
        &self,
        closure_id: ClosureId<I>,
        substs: &Substitution<I>,
    ) -> Substitution<I> {
        self.db.closure_fn_substitution(closure_id, substs)
    }

    fn discriminant_type(&self, ty: Ty<I>) -> Ty<I> {
        self.db.discriminant_type(ty)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RecordedItemId<I: Interner> {
    Adt(AdtId<I>),
    Trait(TraitId<I>),
    Impl(ImplId<I>),
    OpaqueTy(OpaqueTyId<I>),
    FnDef(FnDefId<I>),
    Generator(GeneratorId<I>),
}

impl<I: Interner> From<AdtId<I>> for RecordedItemId<I> {
    fn from(v: AdtId<I>) -> Self {
        RecordedItemId::Adt(v)
    }
}

impl<I: Interner> From<TraitId<I>> for RecordedItemId<I> {
    fn from(v: TraitId<I>) -> Self {
        RecordedItemId::Trait(v)
    }
}

impl<I: Interner> From<ImplId<I>> for RecordedItemId<I> {
    fn from(v: ImplId<I>) -> Self {
        RecordedItemId::Impl(v)
    }
}

impl<I: Interner> From<OpaqueTyId<I>> for RecordedItemId<I> {
    fn from(v: OpaqueTyId<I>) -> Self {
        RecordedItemId::OpaqueTy(v)
    }
}

impl<I: Interner> From<FnDefId<I>> for RecordedItemId<I> {
    fn from(v: FnDefId<I>) -> Self {
        RecordedItemId::FnDef(v)
    }
}

impl<I: Interner> From<GeneratorId<I>> for RecordedItemId<I> {
    fn from(v: GeneratorId<I>) -> Self {
        RecordedItemId::Generator(v)
    }
}

/// Utility for implementing Ord for RecordedItemId.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum OrderedItemId<'a, DefId, AdtId> {
    DefId(&'a DefId),
    AdtId(&'a AdtId),
}

impl<I: Interner> RecordedItemId<I> {
    /// Extract internal identifier. Allows for absolute ordering matching the
    /// order in which chalk saw things (and thus reproducing that order in
    /// printed programs)
    fn ordered_item_id(&self) -> OrderedItemId<'_, I::DefId, I::InternedAdtId> {
        match self {
            RecordedItemId::Trait(TraitId(x))
            | RecordedItemId::Impl(ImplId(x))
            | RecordedItemId::OpaqueTy(OpaqueTyId(x))
            | RecordedItemId::Generator(GeneratorId(x))
            | RecordedItemId::FnDef(FnDefId(x)) => OrderedItemId::DefId(x),
            RecordedItemId::Adt(AdtId(x)) => OrderedItemId::AdtId(x),
        }
    }
}

impl<I: Interner> PartialOrd for RecordedItemId<I> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Interner> Ord for RecordedItemId<I> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.ordered_item_id().cmp(&other.ordered_item_id())
    }
}
