//! Writer logic for top level items.
//!
//! Contains code specific to top-level items and other structures specific to a
//! single top-level item.

use std::fmt::{Formatter, Result};

use crate::rust_ir::*;
use crate::split::Split;
use chalk_ir::interner::Interner;
use itertools::Itertools;

use super::{
    display_self_where_clauses_as_bounds, display_type_with_generics, render_trait::RenderAsRust,
    state::InternalWriterState,
};

/// Used in `AdtDatum` and `TraitDatum` to write n flags from a flags struct
/// to a writer. Each flag field turns into an if expression + write!, so we can
/// just list the names and not repeat this pattern over and over.
///
/// This macro will error if unknown flags are specified. This will also error
/// if any flags are missing.
///
/// # Usage
///
/// ```rust,ignore
/// write_flags!(f, self.flags, XFlags { red, green })
/// ```
///
/// Turns into
///
/// ```rust,ignore
/// match self.flags {
///     XFlags { red, green } => {
///         if red {
///             write!(f, "#[red]")?;
///         }
///         if green {
///             write!(f, "#[green]")?;
///         }
///     }
/// }
/// ```
macro_rules! write_flags {
    ($writer:ident, $val:expr, $struct_name:ident { $($n:ident $(: $extra_arg:tt)?),* }) => {
        match $val {
            // if any fields are missing, the destructuring will error
            $struct_name {
                $($n,)*
            } => {
                $(if $n {
                    write!($writer, "#[{}]\n", write_flags!(@default $n $(: $extra_arg)*))?;
                })*
            }
        }
    };
    (@default $n:ident : $name:literal) => {
        $name
    };
    (@default $n:ident ) => {
        stringify!($n)
    };
}

impl<'a, I: Interner> RenderAsRust<I> for (&'a GeneratorDatum<I>, &'a GeneratorWitnessDatum<I>) {
    fn fmt(&self, _s: &InternalWriterState<'_, I>, _f: &'_ mut Formatter<'_>) -> Result {
        unimplemented!()
    }
}

impl<I: Interner> RenderAsRust<I> for AdtDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // When support for Self in structs is added, self_binding should be
        // changed to Some(0)
        let s = &s.add_debrujin_index(None);
        let value = self.binders.skip_binders();

        // flags
        write_flags!(
            f,
            self.flags,
            AdtFlags {
                // Ordering matters
                upstream,
                fundamental,
                phantom_data
            }
        );

        // repr
        let repr = s.db().adt_repr(self.id);

        if repr.c {
            write!(f, "#[repr(C)]")?;
        }
        if repr.packed {
            write!(f, "#[repr(packed)]")?;
        }
        if let Some(t) = &repr.int {
            write!(f, "#[repr({})]", t.display(s))?;
        }

        // name
        match self.kind {
            AdtKind::Struct => write!(f, "struct {}", self.id.display(s),)?,
            AdtKind::Enum => write!(f, "enum {}", self.id.display(s),)?,
            AdtKind::Union => write!(f, "union {}", self.id.display(s),)?,
        }
        write_joined_non_empty_list!(f, "<{}>", s.binder_var_display(&self.binders.binders), ", ")?;

        // where clauses
        if !value.where_clauses.is_empty() {
            let s = &s.add_indent();
            write!(f, "\nwhere\n{}\n", value.where_clauses.display(s))?;
        } else {
            write!(f, " ")?;
        }

        // body
        write!(f, "{{")?;
        let s = &s.add_indent();
        match self.kind {
            AdtKind::Struct | AdtKind::Union => {
                write_joined_non_empty_list!(
                    f,
                    "\n{}\n",
                    value.variants[0]
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(idx, field)| {
                            format!("{}field_{}: {}", s.indent(), idx, field.display(s))
                        }),
                    ",\n"
                )?;
            }
            AdtKind::Enum => {
                for (variant_idx, variant) in value.variants.iter().enumerate() {
                    write!(f, "\n{}variant_{} {{", s.indent(), variant_idx)?;
                    let s = &s.add_indent();
                    write_joined_non_empty_list!(
                        f,
                        "\n{}\n",
                        variant.fields.iter().enumerate().map(|(idx, field)| {
                            format!("{}field_{}: {}", s.indent(), idx, field.display(s))
                        }),
                        ",\n"
                    )?;
                    write!(f, "{}}},", s.indent())?;
                }
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for Polarity {
    fn fmt(&self, _s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        if !self.is_positive() {
            write!(f, "!")?;
        }
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for TraitDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        let s = &s.add_debrujin_index(Some(0));
        let value = self.binders.skip_binders();

        // flags
        write_flags!(
            f,
            self.flags,
            TraitFlags {
                auto,
                marker,
                upstream,
                fundamental,
                non_enumerable,
                coinductive
            }
        );

        // object safe
        if s.db().is_object_safe(self.id) {
            writeln!(f, "#[object_safe]")?;
        }

        // well-known
        if let Some(well_known) = self.well_known {
            let name = match well_known {
                WellKnownTrait::Sized => "sized",
                WellKnownTrait::Copy => "copy",
                WellKnownTrait::Clone => "clone",
                WellKnownTrait::Drop => "drop",
                WellKnownTrait::FnOnce => "fn_once",
                WellKnownTrait::FnMut => "fn_mut",
                WellKnownTrait::Fn => "fn",
                WellKnownTrait::Unsize => "unsize",
                WellKnownTrait::Unpin => "unpin",
                WellKnownTrait::CoerceUnsized => "coerce_unsized",
                WellKnownTrait::DiscriminantKind => "discriminant_kind",
            };
            writeln!(f, "#[lang({})]", name)?;
        }

        // trait declaration
        let binders = s.binder_var_display(&self.binders.binders).skip(1);
        write!(f, "trait {}", self.id.display(s))?;
        write_joined_non_empty_list!(f, "<{}>", binders, ", ")?;

        // where clauses
        if !value.where_clauses.is_empty() {
            let s = &s.add_indent();
            write!(f, "\nwhere\n{}\n", value.where_clauses.display(s))?;
        } else {
            write!(f, " ")?;
        }

        // body
        write!(f, "{{")?;
        let s = &s.add_indent();
        write_joined_non_empty_list!(
            f,
            "\n{}\n",
            self.associated_ty_ids.iter().map(|assoc_ty_id| {
                let assoc_ty_data = s.db().associated_ty_data(*assoc_ty_id);
                format!("{}{}", s.indent(), (*assoc_ty_data).display(s))
            }),
            "\n"
        )?;

        write_joined_non_empty_list!(
            f,
            "\n{}\n",
            self.associated_const_ids.iter().map(|assoc_const_id| {
                let assoc_const_data = s.db().associated_const_data(*assoc_const_id);
                format!("{}{}", s.indent(), (*assoc_const_data).display(s))
            }),
            "\n"
        )?;

        write!(f, "}}")?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for ImplDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        let interner = s.db().interner();

        let s = &s.add_debrujin_index(None);
        let binders = s.binder_var_display(&self.binders.binders);
        let value = self.binders.skip_binders();

        // annotations
        // #[upstream]
        // ^^^^^^^^^^^
        // impl<T> Foo<T> for Bar<T> where T: Baz { }
        if self.impl_type == ImplType::External {
            writeln!(f, "#[upstream]")?;
        }

        // impl keyword
        // impl<T> Foo<T> for Bar<T> where T: Baz { }
        // ^^^^
        write!(f, "impl")?;
        let trait_ref = &value.trait_ref;

        // generic binders
        // impl<T> Foo<T> for Bar<T> where T: Baz
        //     ^^^
        write_joined_non_empty_list!(f, "<{}>", binders, ", ")?;

        // trait, type and parameters
        // impl<T> Foo<T> for Bar<T> where T: Baz { }
        //         ^^^^^^^^^^^^^^^^^
        let full_trait_name = display_type_with_generics(
            s,
            trait_ref.trait_id,
            // Ignore automatically added Self parameter by skipping first parameter
            &trait_ref.substitution.as_slice(interner)[1..],
        );
        write!(
            f,
            " {}{} for {}",
            self.polarity.display(s),
            full_trait_name,
            trait_ref.self_type_parameter(interner).display(s)
        )?;

        // where clauses
        // impl<T> Foo<T> for Bar<T> where T: Baz { }
        //                           ^^^^^^^^^^^^
        if !value.where_clauses.is_empty() {
            let s = &s.add_indent();
            write!(f, "\nwhere\n{}\n", value.where_clauses.display(s))?;
        } else {
            write!(f, " ")?;
        }

        // body
        // impl<T> Foo<T> for Bar<T> where T: Baz { }
        //                                        ^^^
        write!(f, "{{")?;
        {
            let s = &s.add_indent();
            let assoc_ty_values = self.associated_ty_value_ids.iter().map(|assoc_ty_value| {
                s.db()
                    .associated_ty_value(*assoc_ty_value)
                    .display(s)
                    .to_string()
            });
            write_joined_non_empty_list!(f, "\n{}\n", assoc_ty_values, "\n")?;

            let assoc_const_values =
                self.associated_const_value_ids
                    .iter()
                    .map(|assoc_const_value| {
                        s.db()
                            .associated_const_value(*assoc_const_value)
                            .display(s)
                            .to_string()
                    });
            write_joined_non_empty_list!(f, "\n{}\n", assoc_const_values, "\n")?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for OpaqueTyDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &mut Formatter<'_>) -> Result {
        let s = &s.add_debrujin_index(None);
        let bounds = self.bound.skip_binders();
        write!(f, "opaque type {}", self.opaque_ty_id.display(s))?;
        write_joined_non_empty_list!(f, "<{}>", s.binder_var_display(&self.bound.binders), ", ")?;
        {
            let s = &s.add_debrujin_index(Some(0));
            let clauses = bounds.bounds.skip_binders();
            write!(
                f,
                ": {} = ",
                display_self_where_clauses_as_bounds(s, clauses)
            )?;
        }
        write!(
            f,
            "{};",
            s.db().hidden_opaque_type(self.opaque_ty_id).display(s)
        )?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for AssociatedTyDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // In lowering, a completely new empty environment is created for each
        // AssociatedTyDatum, and it's given generic parameters for each generic
        // parameter that its trait had. We want to map the new binders for
        // those generic parameters back into their original names. To do that,
        // first find their original names (trait_binder_names), then the names
        // they have inside the AssociatedTyDatum (assoc_ty_names_for_trait_params),
        // and then add that mapping to the WriterState when writing bounds and
        // where clauses.
        let trait_datum = s.db().trait_datum(self.trait_id);
        // inverted Debrujin indices for the trait's parameters in the trait
        // environment
        let trait_param_names_in_trait_env = s.binder_var_indices(&trait_datum.binders.binders);
        let s = &s.add_debrujin_index(None);
        // inverted Debrujin indices for the trait's parameters in the
        // associated type environment
        let param_names_in_assoc_ty_env = s
            .binder_var_indices(&self.binders.binders)
            .collect::<Vec<_>>();
        // inverted Debrujin indices to render the trait's parameters in the
        // associated type environment
        let (trait_param_names_in_assoc_ty_env, _) = s
            .db()
            .split_associated_ty_parameters(&param_names_in_assoc_ty_env, self);

        let s = &s.add_parameter_mapping(
            trait_param_names_in_assoc_ty_env.iter().copied(),
            trait_param_names_in_trait_env,
        );

        // rendered names for the associated type's generics in the associated
        // type environment
        let binder_display_in_assoc_ty = s
            .binder_var_display(&self.binders.binders)
            .collect::<Vec<_>>();

        let (_, assoc_ty_params) = s
            .db()
            .split_associated_ty_parameters(&binder_display_in_assoc_ty, self);
        write!(f, "type {}", self.id.display(s))?;
        write_joined_non_empty_list!(f, "<{}>", assoc_ty_params, ", ")?;

        let datum_bounds = &self.binders.skip_binders();

        if !datum_bounds.bounds.is_empty() {
            write!(f, ": ")?;
        }

        // bounds is `A: V, B: D, C = E`?
        // type Foo<A: V, B:D, C = E>: X + Y + Z;
        let bounds = datum_bounds
            .bounds
            .iter()
            .map(|bound| bound.display(s).to_string())
            .format(" + ");
        write!(f, "{}", bounds)?;

        // where_clause is 'X: Y, Z: D'
        // type Foo<...>: ... where X: Y, Z: D;

        // note: it's a quantified clause b/c we could have `for<'a> T: Foo<'a>`
        // within 'where'
        if !datum_bounds.where_clauses.is_empty() {
            let where_s = &s.add_indent();
            let where_clauses = datum_bounds.where_clauses.display(where_s);
            write!(f, "\n{}where\n{}", s.indent(), where_clauses)?;
        }
        write!(f, ";")?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for AssociatedTyValue<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &'_ mut Formatter<'_>) -> Result {
        // see comments for a similar empty env operation in AssociatedTyDatum's
        // impl of RenderAsRust.
        let assoc_ty_data = s.db().associated_ty_data(self.associated_ty_id);
        let impl_datum = s.db().impl_datum(self.impl_id);

        let impl_param_names_in_impl_env = s.binder_var_indices(&impl_datum.binders.binders);

        let s = &s.add_debrujin_index(None);
        let value = self.value.skip_binders();

        let param_names_in_assoc_ty_value_env = s
            .binder_var_indices(&self.value.binders)
            .collect::<Vec<_>>();

        let (impl_params_in_assoc_ty_value_env, _assoc_ty_value_params) = s
            .db()
            .split_associated_ty_value_parameters(&param_names_in_assoc_ty_value_env, self);

        let s = &s.add_parameter_mapping(
            impl_params_in_assoc_ty_value_env.iter().cloned(),
            impl_param_names_in_impl_env,
        );

        let display_params = s
            .binder_var_display(&self.value.binders)
            .collect::<Vec<_>>();

        let (_impl_display, assoc_ty_value_display) = s
            .db()
            .split_associated_ty_value_parameters(&display_params, self);

        write!(f, "{}type {}", s.indent(), assoc_ty_data.id.display(s))?;
        write_joined_non_empty_list!(f, "<{}>", &assoc_ty_value_display, ", ")?;
        write!(f, " = {};", value.ty.display(s))?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for AssociatedConstDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &mut Formatter<'_>) -> Result {
        let assoc_const_data = s.db().associated_const_data(self.id);

        write!(f, "{}const {}", s.indent(), assoc_const_data.id.display(s))?;
        write!(f, ": {};", assoc_const_data.ty.display(s))?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for AssociatedConstValue<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &mut Formatter<'_>) -> Result {
        let assoc_const_data = s.db().associated_const_data(self.associated_const_id);

        write!(f, "{}const {}", s.indent(), assoc_const_data.id.display(s))?;
        write!(f, ": {}", assoc_const_data.ty.display(s))?;
        write!(f, " = {};", self.value.skip_binders().display(s))?;
        Ok(())
    }
}

impl<I: Interner> RenderAsRust<I> for FnDefDatum<I> {
    fn fmt(&self, s: &InternalWriterState<'_, I>, f: &mut Formatter<'_>) -> Result {
        let s = &s.add_debrujin_index(None);
        let bound_datum = self.binders.skip_binders();

        // declaration
        // fn foo<T>(arg: u32, arg2: T) -> Result<T> where T: Bar
        // ^^^^^^
        write!(f, "fn {}", s.db().fn_def_name(self.id))?;

        // binders
        // fn foo<T>(arg: u32, arg2: T) -> Result<T> where T: Bar
        //       ^^^
        let binders = s.binder_var_display(&self.binders.binders);
        write_joined_non_empty_list!(f, "<{}>", binders, ", ")?;

        {
            let s = &s.add_debrujin_index(None);
            let inputs_and_output = bound_datum.inputs_and_output.skip_binders();

            // arguments
            // fn foo<T>(arg: u32, arg2: T) -> Result<T> where T: Bar
            //          ^^^^^^^^^^^^^^^^^^^
            let arguments = inputs_and_output
                .argument_types
                .iter()
                .enumerate()
                .map(|(idx, arg)| format!("arg_{}: {}", idx, arg.display(s)))
                .format(", ");

            write!(f, "({})", arguments)?;

            // return Type
            // fn foo<T>(arg: u32, arg2: T) -> Result<T> where T: Bar
            //                             ^^^^^^^^^^^^^
            write!(f, " -> {}", inputs_and_output.return_type.display(s))?;
        }

        // where clause
        // fn foo<T>(arg: u32, arg2: T) -> Result<T> where T: Bar
        //                                           ^^^^^^^^^^^^
        if !bound_datum.where_clauses.is_empty() {
            let s = &s.add_indent();
            write!(f, "\nwhere\n{}", bound_datum.where_clauses.display(s))?;
        }

        write!(f, ";")?;

        Ok(())
    }
}
