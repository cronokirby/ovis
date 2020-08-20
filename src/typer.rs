use crate::ast::AST;
use crate::interner::Ident;

use std::error::Error;
use std::fmt::{Display, Formatter, Result as FmtResult};

/// Represents a base type in our language
///
/// The only basic types in our language are the primitive integer
/// and string types.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BaseType {
    /// The primitive integer type
    I64,
    /// The primitive string type
    String,
}

use BaseType::*;

impl Display for BaseType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            I64 => write!(f, "I64"),
            String => write!(f, "String"),
        }
    }
}

/// Represents the recursive structure of types.
///
/// This is parametrized over the kind of basic types we have. This is useful
/// to have the same structure over potentially unknown types. This allows us
/// to have some type as (? -> A) (for example), in order to have just part of
/// the full type be unknown.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeStructure<T> {
    /// A base type
    Base(T),
    /// A function type between two other types, potentially functions
    Function(Box<TypeStructure<T>>, Box<TypeStructure<T>>),
}

use TypeStructure::*;

impl<T: Display> Display for TypeStructure<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Base(t) => write!(f, "{}", t),
            Function(func, t2) => match func.as_ref() {
                // We want to wrap parens in the correct way
                Function(_, _) => write!(f, "({}) -> {}", func, t2),
                Base(t1) => write!(f, "{} -> {}", t1, t2),
            },
        }
    }
}

/// Represents a fully evaluated type for some expression
pub type Type = TypeStructure<BaseType>;

/// A base type where we can represent not knowing what type something is.
///
/// This is useful to us as an intermediate stage, allowing us to deal with unknowns
/// in arbitrary locations, until we know nothing more can be learned about some
/// expression, forcing us to provide an unambiguous type.
#[derive(Copy, Clone, Debug, PartialEq)]
enum MaybeBase {
    Unknown,
    Known(BaseType),
}

use MaybeBase::*;

impl Display for MaybeBase {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Unknown => write!(f, "?"),
            Known(b) => write!(f, "{}", b),
        }
    }
}

/// A full set of types, where the basic types can potentially include the absence of knowledge.
type MaybeType = TypeStructure<MaybeBase>;

/// This represents the errors that can occurr will assigning types to the program tree
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TypeError {
    Unknown,
}

impl Display for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            TypeError::Unknown => write!(f, "Unknown Type Error"),
        }
    }
}

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Try and assign types to a syntax tree
///
/// Of course, this can potentially fail, in which case we'll return an error describing
/// the kind of error that occurred.
pub fn typer(untyped: AST<Ident, ()>) -> Result<AST<Ident, Type>, TypeError> {
    Err(TypeError::Unknown)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn types_display_correctly() {
        assert_eq!("I64", format!("{}", I64));
        assert_eq!("String", format!("{}", String));
        assert_eq!(
            "I64 -> String",
            format!("{}", Function(Box::new(Base(I64)), Box::new(Base(String))))
        );
        assert_eq!(
            "(I64 -> I64) -> I64",
            format!(
                "{}",
                Function(
                    Box::new(Function(Box::new(Base(I64)), Box::new(Base(I64)))),
                    Box::new(Base(I64))
                )
            )
        );
        assert_eq!(
            "? -> I64",
            format!(
                "{}",
                Function(Box::new(Base(Unknown)), Box::new(Base(Known(I64))))
            )
        );
    }
}
