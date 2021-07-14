use crate::interner::ChalkIr;
use chalk_parse::ast::{Identifier, Kind};
use chalk_solve::coherence::CoherenceError;
use chalk_solve::wf::WfError;
use string_cache::DefaultAtom as Atom;

/// Wrapper type for the various errors that can occur during chalk
/// processing.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ChalkError {
    /// For now, we just convert the error into a string, which makes
    /// it trivially hashable etc.
    error_text: String,
}

impl From<Box<dyn std::error::Error>> for ChalkError {
    fn from(value: Box<dyn std::error::Error>) -> Self {
        ChalkError {
            error_text: value.to_string(),
        }
    }
}

impl From<WfError<ChalkIr>> for ChalkError {
    fn from(value: WfError<ChalkIr>) -> Self {
        ChalkError {
            error_text: value.to_string(),
        }
    }
}

impl From<CoherenceError<ChalkIr>> for ChalkError {
    fn from(value: CoherenceError<ChalkIr>) -> Self {
        ChalkError {
            error_text: value.to_string(),
        }
    }
}

impl From<RustIrError> for ChalkError {
    fn from(value: RustIrError) -> Self {
        ChalkError {
            error_text: value.to_string(),
        }
    }
}

impl std::fmt::Display for ChalkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.error_text)
    }
}

impl std::error::Error for ChalkError {}

#[derive(Debug)]
pub enum RustIrError {
    InvalidParameterName(Identifier),
    InvalidTraitName(Identifier),
    NotTrait(Identifier),
    NotStruct(Identifier),
    DuplicateOrShadowedParameters,
    AutoTraitAssociatedTypes(Identifier),
    AutoTraitParameters(Identifier),
    AutoTraitWhereClauses(Identifier),
    InvalidFundamentalTypesParameters(Identifier),
    NegativeImplAssociatedValues(Identifier),
    MissingAssociatedType(Identifier),
    MissingAssociatedConst(Identifier),
    IncorrectNumberOfVarianceParameters {
        identifier: Identifier,
        expected: usize,
        actual: usize,
    },
    IncorrectNumberOfTypeParameters {
        identifier: Identifier,
        expected: usize,
        actual: usize,
    },
    IncorrectNumberOfAssociatedTypeParameters {
        identifier: Identifier,
        expected: usize,
        actual: usize,
    },
    IncorrectParameterKind {
        identifier: Identifier,
        expected: Kind,
        actual: Kind,
    },
    IncorrectTraitParameterKind {
        identifier: Identifier,
        expected: Kind,
        actual: Kind,
    },
    IncorrectAssociatedTypeParameterKind {
        identifier: Identifier,
        expected: Kind,
        actual: Kind,
    },
    CannotApplyTypeParameter(Identifier),
    InvalidExternAbi(Atom),
}

impl std::fmt::Display for RustIrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RustIrError::InvalidParameterName(name) => {
                write!(f, "invalid parameter name `{}`", name)
            }
            RustIrError::InvalidTraitName(name) => write!(f, "invalid trait name `{}`", name),
            RustIrError::NotTrait(name) => write!(
                f,
                "expected a trait, found `{}`, which is not a trait",
                name
            ),
            RustIrError::NotStruct(name) => write!(
                f,
                "expected a struct, found `{}`, which is not a struct",
                name
            ),
            RustIrError::DuplicateOrShadowedParameters => {
                write!(f, "duplicate or shadowed parameters")
            }
            RustIrError::AutoTraitAssociatedTypes(name) => {
                write!(f, "auto trait `{}` cannot define associated types", name)
            }
            RustIrError::AutoTraitParameters(name) => {
                write!(f, "auto trait `{}` cannot have parameters", name)
            }
            RustIrError::AutoTraitWhereClauses(name) => {
                write!(f, "auto trait `{}` cannot have where clauses", name)
            }
            RustIrError::InvalidFundamentalTypesParameters(name) => write!(
                f,
                "only a single parameter supported for fundamental type `{}`",
                name
            ),
            RustIrError::NegativeImplAssociatedValues(name) => write!(
                f,
                "negative impl for trait `{}` cannot define associated values",
                name
            ),
            RustIrError::MissingAssociatedType(name) => {
                write!(f, "no associated type `{}` defined in trait", name)
            }
            RustIrError::MissingAssociatedConst(name) => {
                write!(f, "no associated constant `{}` defined in trait", name)
            }
            RustIrError::IncorrectNumberOfVarianceParameters {
                identifier,
                expected,
                actual,
            } => write!(
                f,
                "`{}` has {} type parameters, not {}, which were passed for variance",
                identifier, expected, actual
            ),
            RustIrError::IncorrectNumberOfTypeParameters {
                identifier,
                expected,
                actual,
            } => write!(
                f,
                "`{}` takes {} type parameters, not {}",
                identifier, expected, actual
            ),
            RustIrError::IncorrectNumberOfAssociatedTypeParameters {
                identifier,
                expected,
                actual,
            } => write!(
                f,
                "wrong number of parameters for associated type `{}` (expected {}, got {})",
                identifier, expected, actual
            ),
            RustIrError::IncorrectParameterKind {
                identifier,
                expected,
                actual,
            } => write!(
                f,
                "incorrect parameter kind for `{}`: expected {}, found {}",
                identifier, expected, actual
            ),
            RustIrError::IncorrectTraitParameterKind {
                identifier,
                expected,
                actual,
            } => write!(
                f,
                "incorrect parameter kind for trait `{}`: expected {}, found {}",
                identifier, expected, actual
            ),
            RustIrError::IncorrectAssociatedTypeParameterKind {
                identifier,
                expected,
                actual,
            } => write!(
                f,
                "incorrect associated type parameter kind for `{}`: expected {}, found {}",
                identifier, expected, actual
            ),
            RustIrError::CannotApplyTypeParameter(name) => {
                write!(f, "cannot apply type parameter `{}`", name)
            }
            RustIrError::InvalidExternAbi(abi) => write!(f, "invalid extern ABI `{}`", abi),
        }
    }
}

impl std::error::Error for RustIrError {}
