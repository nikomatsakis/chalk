use chalk_ir::{
    self, AdtId, AssocTypeId, BoundVar, ClosureId, DebruijnIndex, FnDefId, ForeignDefId,
    GeneratorId, ImplId, OpaqueTyId, TraitId, TyVariableKind, VariableKinds,
};
use chalk_ir::{cast::Cast, AssocConstId};
use chalk_parse::ast::*;
use chalk_solve::rust_ir::{
    self, Anonymize, AssociatedConstValueId, AssociatedTyValueId, GeneratorDatum,
    GeneratorInputOutputDatum, GeneratorWitnessDatum, GeneratorWitnessExistential, OpaqueTyDatum,
    OpaqueTyDatumBound,
};
use rust_ir::IntoWhereClauses;
use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;
use string_cache::DefaultAtom as Atom;

use super::{env::*, Lower, LowerParameterMap, LowerWithEnv, FIXME_SELF};
use crate::error::RustIrError;
use crate::program::Program as LoweredProgram;
use crate::RawId;
use crate::{interner::ChalkIr, TypeKind, TypeSort};

#[derive(Default)]
pub(super) struct ProgramLowerer {
    next_item_index: u32,

    associated_ty_lookups: AssociatedTyLookups,
    associated_ty_value_ids: AssociatedTyValueIds,
    associated_const_lookups: AssociatedConstLookups,
    associated_const_value_ids: AssociatedConstValueIds,
    adt_ids: AdtIds,
    fn_def_ids: FnDefIds,
    closure_ids: ClosureIds,
    trait_ids: TraitIds,
    auto_traits: AutoTraits,
    opaque_ty_ids: OpaqueTyIds,
    adt_kinds: AdtKinds,
    fn_def_kinds: FnDefKinds,
    generator_ids: GeneratorIds,
    generator_kinds: GeneratorKinds,
    closure_kinds: ClosureKinds,
    trait_kinds: TraitKinds,
    opaque_ty_kinds: OpaqueTyVariableKinds,
    object_safe_traits: HashSet<TraitId<ChalkIr>>,
    foreign_ty_ids: ForeignIds,
}

impl ProgramLowerer {
    pub fn next_item_id(&mut self) -> RawId {
        let index = self.next_item_index;
        self.next_item_index += 1;
        RawId { index }
    }

    /// Create ids for associated type declarations and values
    pub fn extract_associated_types(
        &mut self,
        program: &Program,
        raw_ids: &Vec<RawId>,
    ) -> LowerResult<()> {
        for (item, &raw_id) in program.items.iter().zip(raw_ids) {
            match item {
                Item::TraitDefn(d) => {
                    if d.flags.auto && !d.assoc_item_defns.is_empty() {
                        Err(RustIrError::AutoTraitAssociatedTypes(d.name.clone()))?;
                    }
                    for defn in &d.assoc_item_defns {
                        match defn {
                            AssocItemDefn::Ty(defn) => {
                                let addl_variable_kinds = defn.all_parameters();
                                let lookup = AssociatedTyLookup {
                                    id: AssocTypeId(self.next_item_id()),
                                    addl_variable_kinds: addl_variable_kinds.anonymize(),
                                };
                                self.associated_ty_lookups
                                    .insert((TraitId(raw_id), defn.name.str.clone()), lookup);
                            }
                            AssocItemDefn::Const(defn) => {
                                let lookup = AssociatedConstLookup {
                                    id: AssocConstId(self.next_item_id()),
                                };
                                self.associated_const_lookups
                                    .insert((TraitId(raw_id), defn.name.str.clone()), lookup);
                            }
                        }
                    }
                }

                Item::Impl(d) => {
                    for aiv in &d.assoc_item_values {
                        match aiv {
                            AssocItemValue::Ty(atv) => {
                                let atv_id = AssociatedTyValueId(self.next_item_id());
                                self.associated_ty_value_ids
                                    .insert((ImplId(raw_id), atv.name.str.clone()), atv_id);
                            }
                            AssocItemValue::Const(acv) => {
                                let acv_id = AssociatedConstValueId(self.next_item_id());
                                self.associated_const_value_ids
                                    .insert((ImplId(raw_id), acv.name.str.clone()), acv_id);
                            }
                        }
                    }
                }

                _ => {}
            }
        }
        Ok(())
    }

    pub fn extract_ids(&mut self, program: &Program, raw_ids: &Vec<RawId>) -> LowerResult<()> {
        for (item, &raw_id) in program.items.iter().zip(raw_ids) {
            match item {
                Item::AdtDefn(defn) => {
                    let type_kind = defn.lower_type_kind()?;
                    let id = AdtId(raw_id);
                    self.adt_ids.insert(type_kind.name.clone(), id);
                    self.adt_kinds.insert(id, type_kind);
                }
                Item::FnDefn(defn) => {
                    let type_kind = defn.lower_type_kind()?;
                    let id = FnDefId(raw_id);
                    self.fn_def_ids.insert(type_kind.name.clone(), id);
                    self.fn_def_kinds.insert(id, type_kind);
                }
                Item::ClosureDefn(defn) => {
                    let type_kind = defn.lower_type_kind()?;
                    let id = ClosureId(raw_id);
                    self.closure_ids.insert(defn.name.str.clone(), id);
                    self.closure_kinds.insert(id, type_kind);
                }
                Item::TraitDefn(defn) => {
                    let type_kind = defn.lower_type_kind()?;
                    let id = TraitId(raw_id);
                    self.trait_ids.insert(type_kind.name.clone(), id);
                    self.trait_kinds.insert(id, type_kind);
                    self.auto_traits.insert(id, defn.flags.auto);

                    if defn.flags.object_safe {
                        self.object_safe_traits.insert(id);
                    }
                }
                Item::OpaqueTyDefn(defn) => {
                    let type_kind = defn.lower_type_kind()?;
                    let id = OpaqueTyId(raw_id);
                    self.opaque_ty_ids.insert(defn.name.str.clone(), id);
                    self.opaque_ty_kinds.insert(id, type_kind);
                }
                Item::Foreign(ForeignDefn(ref ident)) => {
                    self.foreign_ty_ids
                        .insert(ident.str.clone(), ForeignDefId(raw_id));
                }
                Item::GeneratorDefn(defn) => {
                    let id = GeneratorId(raw_id);
                    self.generator_ids.insert(defn.name.str.clone(), id);
                    self.generator_kinds.insert(id, defn.lower_type_kind()?);
                }
                Item::Impl(_) => continue,
                Item::Clause(_) => continue,
            };
        }
        Ok(())
    }

    pub fn lower(self, program: &Program, raw_ids: &Vec<RawId>) -> LowerResult<LoweredProgram> {
        let mut adt_data = BTreeMap::new();
        let mut adt_reprs = BTreeMap::new();
        let mut adt_variances = BTreeMap::new();
        let mut fn_def_data = BTreeMap::new();
        let mut fn_def_variances = BTreeMap::new();
        let mut closure_inputs_and_output = BTreeMap::new();
        let mut closure_closure_kind = BTreeMap::new();
        let mut closure_upvars = BTreeMap::new();
        let mut trait_data = BTreeMap::new();
        let mut well_known_traits = BTreeMap::new();
        let mut impl_data = BTreeMap::new();
        let mut associated_ty_data = BTreeMap::new();
        let mut associated_ty_values = BTreeMap::new();
        let mut associated_const_data = BTreeMap::new();
        let mut associated_const_values = BTreeMap::new();
        let mut opaque_ty_data = BTreeMap::new();
        let mut generator_data = BTreeMap::new();
        let mut generator_witness_data = BTreeMap::new();
        let mut hidden_opaque_types = BTreeMap::new();
        let mut custom_clauses = Vec::new();

        for (item, &raw_id) in program.items.iter().zip(raw_ids) {
            let empty_env = Env {
                adt_ids: &self.adt_ids,
                adt_kinds: &self.adt_kinds,
                fn_def_ids: &self.fn_def_ids,
                fn_def_kinds: &self.fn_def_kinds,
                closure_ids: &self.closure_ids,
                closure_kinds: &self.closure_kinds,
                trait_ids: &self.trait_ids,
                trait_kinds: &self.trait_kinds,
                opaque_ty_ids: &self.opaque_ty_ids,
                opaque_ty_kinds: &self.opaque_ty_kinds,
                generator_ids: &self.generator_ids,
                generator_kinds: &self.generator_kinds,
                associated_ty_lookups: &self.associated_ty_lookups,
                associated_const_lookups: &self.associated_const_lookups,
                parameter_map: BTreeMap::new(),
                auto_traits: &self.auto_traits,
                foreign_ty_ids: &self.foreign_ty_ids,
            };

            match *item {
                Item::AdtDefn(ref d) => {
                    let identifier = d.name.clone();
                    let adt_id = AdtId(raw_id);
                    adt_data.insert(adt_id, Arc::new((d, adt_id).lower(&empty_env)?));
                    adt_reprs.insert(adt_id, Arc::new(d.repr.lower(&empty_env)?));
                    let n_params = d.all_parameters().len();
                    let variances = match d.variances.clone() {
                        Some(v) => {
                            if v.len() != n_params {
                                return Err(RustIrError::IncorrectNumberOfVarianceParameters {
                                    identifier,
                                    expected: n_params,
                                    actual: v.len(),
                                });
                            }
                            v.into_iter()
                                .map(|v| match v {
                                    Variance::Invariant => chalk_ir::Variance::Invariant,
                                    Variance::Covariant => chalk_ir::Variance::Covariant,
                                    Variance::Contravariant => chalk_ir::Variance::Contravariant,
                                })
                                .collect()
                        }
                        None => (0..n_params)
                            .map(|_| chalk_ir::Variance::Invariant)
                            .collect(),
                    };
                    adt_variances.insert(adt_id, variances);
                }
                Item::FnDefn(ref defn) => {
                    let identifier = defn.name.clone();
                    let fn_def_id = FnDefId(raw_id);
                    fn_def_data.insert(fn_def_id, Arc::new((defn, fn_def_id).lower(&empty_env)?));
                    let n_params = defn.all_parameters().len();
                    let variances = match defn.variances.clone() {
                        Some(v) => {
                            if v.len() != n_params {
                                return Err(RustIrError::IncorrectNumberOfVarianceParameters {
                                    identifier,
                                    expected: n_params,
                                    actual: v.len(),
                                });
                            }
                            v.into_iter()
                                .map(|v| match v {
                                    Variance::Invariant => chalk_ir::Variance::Invariant,
                                    Variance::Covariant => chalk_ir::Variance::Covariant,
                                    Variance::Contravariant => chalk_ir::Variance::Contravariant,
                                })
                                .collect()
                        }
                        None => (0..n_params)
                            .map(|_| chalk_ir::Variance::Invariant)
                            .collect(),
                    };
                    fn_def_variances.insert(fn_def_id, variances);
                }
                Item::ClosureDefn(ref defn) => {
                    let closure_def_id = ClosureId(raw_id);
                    let (kind, inputs_and_output) = defn.lower(&empty_env)?;
                    closure_closure_kind.insert(closure_def_id, kind);
                    closure_inputs_and_output.insert(closure_def_id, inputs_and_output);
                    let upvars = empty_env.in_binders(defn.all_parameters(), |env| {
                        let upvar_tys: LowerResult<Vec<chalk_ir::Ty<ChalkIr>>> =
                            defn.upvars.iter().map(|ty| ty.lower(&env)).collect();
                        let substitution = chalk_ir::Substitution::from_iter(
                            &ChalkIr,
                            upvar_tys?.into_iter().map(|ty| ty.cast(&ChalkIr)),
                        );
                        Ok(chalk_ir::TyKind::Tuple(defn.upvars.len(), substitution)
                            .intern(&ChalkIr))
                    })?;
                    closure_upvars.insert(closure_def_id, upvars);
                }
                Item::TraitDefn(ref trait_defn) => {
                    let trait_id = TraitId(raw_id);
                    let trait_datum = (trait_defn, trait_id).lower(&empty_env)?;

                    if let Some(well_known) = trait_datum.well_known {
                        well_known_traits.insert(well_known, trait_id);
                    }

                    trait_data.insert(trait_id, Arc::new(trait_datum));

                    for assoc_item_defn in &trait_defn.assoc_item_defns {
                        match assoc_item_defn {
                            AssocItemDefn::Ty(assoc_ty_defn) => {
                                let lookup = &self.associated_ty_lookups
                                    [&(trait_id, assoc_ty_defn.name.str.clone())];

                                // The parameters in scope for the associated
                                // type definitions are *both* those from the
                                // trait *and* those from the associated type
                                // itself.
                                //
                                // Insert the associated type parameters first
                                // into the list so that they are given the
                                // indices starting from 0. This corresponds
                                // to the "de bruijn" convention where "more
                                // inner" sets of parameters get the lower
                                // indices:
                                //
                                // e.g., in this example, the indices would be
                                // assigned `[A0, A1, T0, T1]`:
                                //
                                // ```
                                // trait Foo<T0, T1> {
                                //     type Bar<A0, A1>;
                                // }
                                // ```
                                let mut variable_kinds = assoc_ty_defn.all_parameters();
                                variable_kinds.extend(trait_defn.all_parameters());

                                let binders = empty_env.in_binders(variable_kinds, |env| {
                                    Ok(rust_ir::AssociatedTyDatumBound {
                                        bounds: assoc_ty_defn.bounds.lower(&env)?,
                                        where_clauses: assoc_ty_defn.where_clauses.lower(&env)?,
                                    })
                                })?;

                                associated_ty_data.insert(
                                    lookup.id,
                                    Arc::new(rust_ir::AssociatedTyDatum {
                                        trait_id: TraitId(raw_id),
                                        id: lookup.id,
                                        name: assoc_ty_defn.name.str.clone(),
                                        binders,
                                    }),
                                );
                            }
                            AssocItemDefn::Const(assoc_const_defn) => {
                                let lookup = &self.associated_const_lookups
                                    [&(trait_id, assoc_const_defn.name.str.clone())];

                                let variable_kinds = trait_defn.all_parameters();
                                let binders = assoc_const_defn
                                    .value
                                    .as_ref()
                                    .map(|value| {
                                        empty_env
                                            .in_binders(variable_kinds, |env| value.lower(&env))
                                    })
                                    .transpose()?;
                                associated_const_data.insert(
                                    lookup.id,
                                    Arc::new(rust_ir::AssociatedConstDatum {
                                        trait_id: TraitId(raw_id),
                                        id: lookup.id,
                                        name: assoc_const_defn.name.str.clone(),
                                        ty: assoc_const_defn.ty.lower(&empty_env)?,
                                        binders,
                                    }),
                                );
                            }
                        }
                    }
                }
                Item::Impl(ref impl_defn) => {
                    let impl_id = ImplId(raw_id);
                    let impl_datum = Arc::new(
                        (
                            impl_defn,
                            impl_id,
                            &self.associated_ty_value_ids,
                            &self.associated_const_value_ids,
                        )
                            .lower(&empty_env)?,
                    );
                    impl_data.insert(impl_id, impl_datum.clone());
                    let trait_id = impl_datum.trait_id();

                    for aiv in &impl_defn.assoc_item_values {
                        match aiv {
                            AssocItemValue::Ty(atv) => {
                                let atv_id =
                                    self.associated_ty_value_ids[&(impl_id, atv.name.str.clone())];
                                let lookup =
                                    &self.associated_ty_lookups[&(trait_id, atv.name.str.clone())];

                                // The parameters in scope for the associated
                                // type definitions are *both* those from the
                                // impl *and* those from the associated type
                                // itself. As in the "trait" case above, we begin
                                // with the parameters from the impl.
                                let mut variable_kinds = atv.all_parameters();
                                variable_kinds.extend(impl_defn.all_parameters());

                                let value = empty_env.in_binders(variable_kinds, |env| {
                                    Ok(rust_ir::AssociatedTyValueBound {
                                        ty: atv.value.lower(env)?,
                                    })
                                })?;

                                associated_ty_values.insert(
                                    atv_id,
                                    Arc::new(rust_ir::AssociatedTyValue {
                                        impl_id,
                                        associated_ty_id: lookup.id,
                                        value,
                                    }),
                                );
                            }
                            AssocItemValue::Const(acv) => {
                                let acv_id = self.associated_const_value_ids
                                    [&(impl_id, acv.name.str.clone())];
                                let lookup = &self.associated_const_lookups
                                    [&(trait_id, acv.name.str.clone())];

                                let variable_kinds = impl_defn.all_parameters();
                                let value = empty_env
                                    .in_binders(variable_kinds, |env| acv.value.lower(env))?;
                                associated_const_values.insert(
                                    acv_id,
                                    Arc::new(rust_ir::AssociatedConstValue {
                                        impl_id,
                                        associated_const_id: lookup.id,
                                        value,
                                    }),
                                );
                            }
                        }
                    }
                }
                Item::Clause(ref clause) => {
                    custom_clauses.extend(clause.lower(&empty_env)?);
                }
                Item::OpaqueTyDefn(ref opaque_ty) => {
                    if let Some(&opaque_ty_id) = self.opaque_ty_ids.get(&opaque_ty.name.str) {
                        let variable_kinds = opaque_ty
                            .variable_kinds
                            .iter()
                            .map(|k| k.lower())
                            .collect::<Vec<_>>();

                        // Introduce the parameters declared on the opaque type definition.
                        // So if we have `type Foo<P1..Pn> = impl Trait<T1..Tn>`, this would introduce `P1..Pn`
                        let binders = empty_env.in_binders(variable_kinds, |env| {
                            let hidden_ty = opaque_ty.ty.lower(&env)?;
                            hidden_opaque_types.insert(opaque_ty_id, Arc::new(hidden_ty));

                            // Introduce a variable to represent the hidden "self type". This will be used in the bounds.
                            // So the `impl Trait<T1..Tn>` will be lowered to `exists<Self> { Self: Trait<T1..Tn> }`.
                            let bounds: chalk_ir::Binders<Vec<chalk_ir::Binders<_>>> = env
                                .in_binders(
                                    Some(chalk_ir::WithKind::new(
                                        chalk_ir::VariableKind::Ty(TyVariableKind::General),
                                        Atom::from(FIXME_SELF),
                                    )),
                                    |env| {
                                        let interner = env.interner();
                                        Ok(opaque_ty
                                            .bounds
                                            .lower(&env)?
                                            .iter()
                                            .flat_map(|qil| {
                                                // Instantiate the bounds with the innermost bound variable, which represents Self, as the self type.
                                                qil.into_where_clauses(
                                                    interner,
                                                    chalk_ir::TyKind::BoundVar(BoundVar::new(
                                                        DebruijnIndex::INNERMOST,
                                                        0,
                                                    ))
                                                    .intern(interner),
                                                )
                                            })
                                            .collect())
                                    },
                                )?;
                            let where_clauses: chalk_ir::Binders<Vec<chalk_ir::Binders<_>>> = env
                                .in_binders(
                                Some(chalk_ir::WithKind::new(
                                    chalk_ir::VariableKind::Ty(TyVariableKind::General),
                                    Atom::from(FIXME_SELF),
                                )),
                                |env| opaque_ty.where_clauses.lower(env),
                            )?;

                            Ok(OpaqueTyDatumBound {
                                bounds,
                                where_clauses,
                            })
                        })?;

                        opaque_ty_data.insert(
                            opaque_ty_id,
                            Arc::new(OpaqueTyDatum {
                                opaque_ty_id,
                                bound: binders,
                            }),
                        );
                    }
                }
                Item::GeneratorDefn(ref defn) => {
                    let variable_kinds = defn
                        .variable_kinds
                        .iter()
                        .map(|k| k.lower())
                        .collect::<Vec<_>>();

                    let witness_lifetimes = defn
                        .witness_lifetimes
                        .iter()
                        .map(|i| VariableKind::Lifetime(i.clone()).lower())
                        .collect::<Vec<_>>();

                    let input_output = empty_env.in_binders(variable_kinds.clone(), |env| {
                        let yield_type = defn.yield_ty.lower(&env)?;
                        let resume_type = defn.resume_ty.lower(&env)?;
                        let return_type = defn.return_ty.lower(&env)?;
                        let upvars: Result<Vec<_>, _> =
                            defn.upvars.iter().map(|ty| ty.lower(&env)).collect();

                        Ok(GeneratorInputOutputDatum {
                            resume_type,
                            yield_type,
                            return_type,
                            upvars: upvars?,
                        })
                    })?;

                    let inner_types = empty_env.in_binders(variable_kinds, |env| {
                        let witnesses = env.in_binders(witness_lifetimes, |env| {
                            let witnesses: Result<Vec<_>, _> =
                                defn.witness_types.iter().map(|ty| ty.lower(&env)).collect();
                            witnesses
                        })?;

                        Ok(GeneratorWitnessExistential { types: witnesses })
                    })?;

                    let generator_datum = GeneratorDatum {
                        movability: defn.movability.lower(),
                        input_output,
                    };
                    let generator_witness = GeneratorWitnessDatum { inner_types };

                    let id = self.generator_ids[&defn.name.str];
                    generator_data.insert(id, Arc::new(generator_datum));
                    generator_witness_data.insert(id, Arc::new(generator_witness));
                }
                Item::Foreign(_) => {}
            }
        }

        Ok(LoweredProgram {
            adt_ids: self.adt_ids,
            fn_def_ids: self.fn_def_ids,
            closure_ids: self.closure_ids,
            closure_upvars,
            closure_kinds: self.closure_kinds,
            trait_ids: self.trait_ids,
            adt_kinds: self.adt_kinds,
            fn_def_kinds: self.fn_def_kinds,
            trait_kinds: self.trait_kinds,
            adt_data,
            adt_reprs,
            adt_variances,
            fn_def_data,
            fn_def_variances,
            closure_inputs_and_output,
            closure_closure_kind,
            generator_ids: self.generator_ids,
            generator_kinds: self.generator_kinds,
            generator_data,
            generator_witness_data,
            trait_data,
            well_known_traits,
            impl_data,
            associated_ty_values,
            associated_ty_data,
            associated_const_values,
            associated_const_data,
            opaque_ty_ids: self.opaque_ty_ids,
            opaque_ty_kinds: self.opaque_ty_kinds,
            opaque_ty_data,
            hidden_opaque_types,
            custom_clauses,
            object_safe_traits: self.object_safe_traits,
            foreign_ty_ids: self.foreign_ty_ids,
        })
    }
}

trait LowerTypeKind {
    fn lower_type_kind(&self) -> LowerResult<TypeKind>;
}

macro_rules! lower_type_kind {
    ($type: ident, $sort: ident, $params: expr) => {
        impl LowerTypeKind for $type {
            fn lower_type_kind(&self) -> LowerResult<TypeKind> {
                Ok(TypeKind {
                    sort: TypeSort::$sort,
                    name: self.name.str.clone(),
                    binders: chalk_ir::Binders::new(
                        VariableKinds::from_iter(&ChalkIr, $params(self).anonymize()),
                        crate::Unit,
                    ),
                })
            }
        }
    };
}

lower_type_kind!(AdtDefn, Adt, |defn: &AdtDefn| defn.all_parameters());
lower_type_kind!(FnDefn, FnDef, |defn: &FnDefn| defn.all_parameters());
lower_type_kind!(ClosureDefn, Closure, |defn: &ClosureDefn| defn
    .all_parameters());
lower_type_kind!(GeneratorDefn, Generator, |defn: &GeneratorDefn| defn
    .variable_kinds
    .iter()
    .map(|k| k.lower())
    .collect::<Vec<_>>());
lower_type_kind!(TraitDefn, Trait, |defn: &TraitDefn| defn
    .variable_kinds
    .iter()
    .map(|k| k.lower())
    .collect::<Vec<_>>());
lower_type_kind!(OpaqueTyDefn, Opaque, |defn: &OpaqueTyDefn| defn
    .variable_kinds
    .iter()
    .map(|k| k.lower())
    .collect::<Vec<_>>());
