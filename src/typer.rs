use crate::ast::AST;
use crate::interner::Ident;

use std::error::Error;
use std::fmt;

/// Represents a fully evaluated Type for some expression or identifier
///
/// We'll use this as the type to fill in our typed AST later
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// The primitive integer type
    I64,
    /// The primitive string type
    String,
    /// A function type between two other types
    Function(Box<Type>, Box<Type>),
}

/// This represents the errors that can occurr will assigning types to the program tree
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TypeError {
    Unknown,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
