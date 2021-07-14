//! Visitor helpers

use crate::{BoundVar, ControlFlow, DebruijnIndex, Interner, Visit, Visitor};

/// Visitor extensions.
pub trait VisitExt<I: Interner>: Visit<I> {
    /// Check whether there are free (non-bound) variables.
    fn has_free_vars(&self, interner: &I) -> bool {
        self.visit_with(
            &mut FindFreeVarsVisitor { interner },
            DebruijnIndex::INNERMOST,
        )
        .is_break()
    }

    /// Validates binders.
    fn validate_binders(&self, interner: &I) -> bool {
        self.visit_with(
            &mut binders_check::BindersValidator {
                interner,
                stack: Vec::new(),
            },
            DebruijnIndex::INNERMOST,
        )
        .is_continue()
    }
}

impl<T, I: Interner> VisitExt<I> for T where T: Visit<I> {}

struct FindFreeVarsVisitor<'i, I: Interner> {
    interner: &'i I,
}

impl<'i, I: Interner> Visitor<'i, I> for FindFreeVarsVisitor<'i, I> {
    type BreakTy = ();

    fn as_dyn(&mut self) -> &mut dyn Visitor<'i, I, BreakTy = Self::BreakTy> {
        self
    }

    fn interner(&self) -> &'i I {
        self.interner
    }

    fn visit_free_var(
        &mut self,
        _bound_var: BoundVar,
        _outer_binder: DebruijnIndex,
    ) -> ControlFlow<()> {
        ControlFlow::BREAK
    }
}

mod binders_check {
    use crate::{
        interner::Interner,
        visit::{ControlFlow, SuperVisit, Visitor},
        Const, DebruijnIndex, Lifetime, Ty, VariableKind,
    };

    pub struct BindersValidator<'i, I: Interner> {
        pub(crate) interner: &'i I,
        pub(crate) stack: Vec<Vec<VariableKind<I>>>,
    }

    impl<'i, I: Interner> Visitor<'i, I> for BindersValidator<'i, I> {
        type BreakTy = ();

        fn as_dyn(&mut self) -> &mut dyn Visitor<'i, I, BreakTy = Self::BreakTy> {
            self
        }

        fn interner(&self) -> &'i I {
            self.interner
        }

        fn visit_ty(
            &mut self,
            ty: &Ty<I>,
            outer_binder: DebruijnIndex,
        ) -> ControlFlow<Self::BreakTy> {
            if let Some(bv) = ty.bound_var(self.interner) {
                assert_eq!(self.stack.len(), outer_binder.depth() as usize);
                if bv.debruijn < outer_binder {
                    let kinds = &self.stack[self.stack.len() - 1 - bv.debruijn.depth() as usize];
                    match kinds.get(bv.index) {
                        Some(VariableKind::Ty(_)) => {}
                        _ => {
                            return ControlFlow::BREAK;
                        }
                    }
                } else {
                    return ControlFlow::BREAK;
                }
            }
            ty.super_visit_with(self.as_dyn(), outer_binder)
        }

        fn visit_const(
            &mut self,
            constant: &Const<I>,
            outer_binder: DebruijnIndex,
        ) -> ControlFlow<Self::BreakTy> {
            if let Some(bv) = constant.bound_var(self.interner) {
                assert_eq!(self.stack.len(), outer_binder.depth() as usize);
                if bv.debruijn < outer_binder {
                    let kinds = &self.stack[self.stack.len() - 1 - bv.debruijn.depth() as usize];
                    match kinds.get(bv.index) {
                        Some(VariableKind::Const(_ty)) => {
                            // FIXME: validate that type can match?
                        }
                        _ => {
                            return ControlFlow::BREAK;
                        }
                    }
                } else {
                    return ControlFlow::BREAK;
                }
            }
            constant.super_visit_with(self.as_dyn(), outer_binder)
        }

        fn visit_lifetime(
            &mut self,
            lifetime: &Lifetime<I>,
            outer_binder: DebruijnIndex,
        ) -> ControlFlow<Self::BreakTy> {
            if let Some(bv) = lifetime.bound_var(self.interner) {
                assert_eq!(self.stack.len(), outer_binder.depth() as usize);
                if bv.debruijn < outer_binder {
                    let kinds = &self.stack[self.stack.len() - 1 - bv.debruijn.depth() as usize];
                    match kinds.get(bv.index) {
                        Some(VariableKind::Lifetime) => {}
                        _ => {
                            return ControlFlow::BREAK;
                        }
                    }
                } else {
                    return ControlFlow::BREAK;
                }
            }
            lifetime.super_visit_with(self.as_dyn(), outer_binder)
        }

        fn before_binders(&mut self, kinds: &crate::VariableKinds<I>) {
            self.stack.push(kinds.as_slice(self.interner).to_vec());
        }

        fn before_canonical(&mut self, kinds: &crate::CanonicalVarKinds<I>) {
            self.stack.push(
                kinds
                    .iter(self.interner)
                    .map(|wk| wk.kind.clone())
                    .collect(),
            );
        }

        fn before_fn_pointer_substs(&mut self, number: usize) {
            self.stack.push(
                std::iter::repeat_with(|| VariableKind::Lifetime)
                    .take(number)
                    .collect(),
            )
        }

        fn after_any_binders(&mut self) {
            self.stack.pop().unwrap();
        }
    }
}
