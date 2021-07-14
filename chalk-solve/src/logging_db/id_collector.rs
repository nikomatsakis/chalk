use super::RecordedItemId;
use crate::RustIrDatabase;
use chalk_ir::{
    interner::Interner,
    visit::{ControlFlow, Visitor},
    visit::{SuperVisit, Visit},
    AliasTy, DebruijnIndex, TyKind, WhereClause,
};
use std::collections::BTreeSet;

/// Collects the identifiers needed to resolve all the names for a given
/// set of identifiers, excluding identifiers we already have.
///
/// When recording identifiers to print, the `LoggingRustIrDatabase` only
/// records identifiers the solver uses. But the solver assumes well-formedness,
/// and thus skips over many names referenced in the definitions.
///
/// For instance, if we have:
///
/// ```rust,ignore
/// struct S {}
///
/// trait Parent {}
/// trait Child where Self: Parent {}
/// impl Parent for S {}
/// impl Child for S {}
/// ```
///
/// And our goal is `S: Child`, we will only render `S`, `impl Child for S`, and
/// `trait Child`. This will not parse because the `Child` trait's definition
/// references parent. IdCollector solves this by collecting all of the directly
/// related identifiers, allowing those to be rendered as well, ensuring name
/// resolution is successful.
pub fn collect_unrecorded_ids<'i, I: Interner, DB: RustIrDatabase<I>>(
    db: &'i DB,
    identifiers: &'_ BTreeSet<RecordedItemId<I>>,
) -> BTreeSet<RecordedItemId<I>> {
    let mut collector = IdCollector {
        db,
        found_identifiers: BTreeSet::new(),
    };
    for id in identifiers {
        match *id {
            RecordedItemId::Adt(adt_id) => {
                collector
                    .db
                    .adt_datum(adt_id)
                    .visit_with(&mut collector, DebruijnIndex::INNERMOST);
            }
            RecordedItemId::FnDef(fn_def) => {
                collector
                    .db
                    .fn_def_datum(fn_def)
                    .visit_with(&mut collector, DebruijnIndex::INNERMOST);
            }
            RecordedItemId::Generator(_generator_id) => unimplemented!(),
            RecordedItemId::Trait(trait_id) => {
                let trait_datum = collector.db.trait_datum(trait_id);

                trait_datum.visit_with(&mut collector, DebruijnIndex::INNERMOST);
                for assoc_ty_id in &trait_datum.associated_ty_ids {
                    let assoc_ty_datum = collector.db.associated_ty_data(*assoc_ty_id);
                    assoc_ty_datum
                        .bounds_on_self(collector.db.interner())
                        .visit_with(&mut collector, DebruijnIndex::INNERMOST);
                    assoc_ty_datum.visit_with(&mut collector, DebruijnIndex::INNERMOST);
                }
                for assoc_const_id in &trait_datum.associated_const_ids {
                    let assoc_const_datum = collector.db.associated_const_data(*assoc_const_id);
                    assoc_const_datum.visit_with(&mut collector, DebruijnIndex::INNERMOST);
                }
            }
            RecordedItemId::OpaqueTy(opaque_id) => {
                collector
                    .db
                    .opaque_ty_data(opaque_id)
                    .visit_with(&mut collector, DebruijnIndex::INNERMOST);
                collector
                    .db
                    .hidden_opaque_type(opaque_id)
                    .visit_with(&mut collector, DebruijnIndex::INNERMOST);
            }
            RecordedItemId::Impl(impl_id) => {
                let impl_datum = collector.db.impl_datum(impl_id);
                for id in &impl_datum.associated_ty_value_ids {
                    let assoc_ty_value = collector.db.associated_ty_value(*id);
                    assoc_ty_value.visit_with(&mut collector, DebruijnIndex::INNERMOST);
                }
                for id in &impl_datum.associated_const_value_ids {
                    let assoc_const_value = collector.db.associated_const_value(*id);
                    assoc_const_value.visit_with(&mut collector, DebruijnIndex::INNERMOST);
                }
                impl_datum.visit_with(&mut collector, DebruijnIndex::INNERMOST);
            }
        }
    }
    collector
        .found_identifiers
        .difference(identifiers)
        .copied()
        .collect()
}

struct IdCollector<'i, I: Interner, DB: RustIrDatabase<I>> {
    db: &'i DB,
    found_identifiers: BTreeSet<RecordedItemId<I>>,
}

impl<'i, I: Interner, DB: RustIrDatabase<I>> IdCollector<'i, I, DB> {
    fn record(&mut self, id: impl Into<RecordedItemId<I>>) {
        self.found_identifiers.insert(id.into());
    }

    fn visit_alias(&mut self, alias: &AliasTy<I>) {
        match alias {
            AliasTy::Projection(projection_ty) => {
                let assoc_ty_datum = self.db.associated_ty_data(projection_ty.associated_ty_id);
                self.record(assoc_ty_datum.trait_id)
            }
            AliasTy::Opaque(opaque_ty) => self.record(opaque_ty.opaque_ty_id),
        }
    }
}

impl<'i, I: Interner, DB: RustIrDatabase<I>> Visitor<'i, I> for IdCollector<'i, I, DB>
where
    I: 'i,
{
    type BreakTy = ();

    fn as_dyn(&mut self) -> &mut dyn Visitor<'i, I, BreakTy = Self::BreakTy> {
        self
    }
    fn interner(&self) -> &'i I {
        self.db.interner()
    }

    fn visit_ty(
        &mut self,
        ty: &chalk_ir::Ty<I>,
        outer_binder: chalk_ir::DebruijnIndex,
    ) -> ControlFlow<()> {
        match ty.kind(self.db.interner()) {
            TyKind::Adt(adt, _) => self.record(*adt),
            TyKind::FnDef(fn_def, _) => self.record(*fn_def),
            TyKind::OpaqueType(opaque, _) => self.record(*opaque),
            TyKind::Alias(alias) => self.visit_alias(&alias),
            TyKind::BoundVar(..) => (),
            TyKind::Dyn(..) => (),
            TyKind::Function(..) => (),
            TyKind::InferenceVar(..) => (),
            TyKind::Placeholder(..) => (),
            _ => {}
        }
        ty.super_visit_with(self, outer_binder)
    }

    fn visit_where_clause(
        &mut self,
        where_clause: &WhereClause<I>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<()> {
        match where_clause {
            WhereClause::Implemented(trait_ref) => self.record(trait_ref.trait_id),
            WhereClause::AliasEq(alias_eq) => self.visit_alias(&alias_eq.alias),
            WhereClause::LifetimeOutlives(_lifetime_outlives) => (),
            WhereClause::TypeOutlives(_type_outlives) => (),
        }
        where_clause.super_visit_with(self.as_dyn(), outer_binder)
    }
}
