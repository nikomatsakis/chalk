//! Writer logic for simple IDs
//!
//! `RenderAsRust` impls for identifiers which are either too small or too
//! shared to belong anywhere else belong here.
use std::fmt::{Formatter, Result};

use chalk_ir::interner::Interner;
use chalk_ir::*;

use super::{render_trait::RenderAsRust, state::InternalWriterState};

impl<I: Interner> RenderAsRust<I> for AdtId<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // TODO: use debug methods?
        write!(
            f,
            "{}",
            s.alias_for_adt_id_name(self.0, s.db().adt_name(*self))
        )
    }
}

impl<I: Interner> RenderAsRust<I> for TraitId<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // TODO: use debug methods?
        write!(
            f,
            "{}",
            s.alias_for_id_name(self.0, s.db().trait_name(*self))
        )
    }
}

impl<I: Interner> RenderAsRust<I> for AssocTypeId<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // TODO: use debug methods?
        write!(
            f,
            "{}",
            s.alias_for_id_name(self.0, s.db().assoc_type_name(*self))
        )
    }
}

impl<I: Interner> RenderAsRust<I> for AssocConstId<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // TODO: use debug methods?
        write!(
            f,
            "{}",
            s.alias_for_id_name(self.0, s.db().assoc_const_name(*self))
        )
    }
}

impl<I: Interner> RenderAsRust<I> for OpaqueTyId<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // TODO: use debug methods?
        write!(
            f,
            "{}",
            s.alias_for_id_name(self.0, s.db().opaque_type_name(*self))
        )
    }
}
