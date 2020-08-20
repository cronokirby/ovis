use crate::ast::AST;
use crate::interner::Ident;
use std::collections::HashMap;

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

/// Holds a context assigning types to specific identifiers
///
/// This also handles concerns like lexical scoping, allowing us to work with
/// multiple scopes, and variables shadowing those with the same name in higher
/// scopes.
#[derive(Debug)]
struct Context {
    /// A stack of mappings from identifier to type
    ///
    /// Invariant: scopes is never empty
    ///
    /// When we enter a new lexical scope, we push a new object onto this stack,
    /// because of this, it means that the last element of this stack is always
    /// the latest lexical scope.
    scopes: Vec<HashMap<Ident, MaybeType>>,
}

impl Context {
    /// Create a new context, with the right global scope
    fn new() -> Context {
        // We start out with a single global scope, naturally
        Context {
            scopes: vec![HashMap::new()],
        }
    }

    /// Enter a new lexical scope, i.e. we're seeing new variables that are allowed
    /// to shadow previous ones.
    fn enter(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Exit the latest lexical scope.
    ///
    /// If this causes there to be no current scope, this panics.
    /// When we're at the end of a global scope, we should simple do nothing,
    /// to avoid this panic.
    fn exit(&mut self) {
        self.scopes.pop();
        // We want to panic early if the context is ever empty
        // We always have the global context to work with
        if self.scopes.is_empty() {
            panic!("Context has been completely emptied")
        }
    }

    /// Introduce a new variable in a scope.
    ///
    /// This should be called before assigning a type to that identifier.
    fn introduce(&mut self, ident: Ident) {
        // We don't even bother with crawling, since we'll always need to introduce a new
        // variable in the latest scope.
        // Unwrapping is safe, because of the invariant
        let last = self.scopes.last_mut().unwrap();
        // We only want to introduce a variable if it's not already there
        last.entry(ident).or_insert(Base(Unknown));
    }

    /// Assign a new type, or concrete type, to a variable already in scope
    ///
    /// This is useful in inference, but should always be called after introduce,
    /// otherwise it will panic.
    ///
    /// Precisely, it will panic whenever we're not able to find the variable in some scope above us.
    fn assign(&mut self, ident: Ident, typ: MaybeType) {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(v) = scope.get_mut(&ident) {
                *v = typ;
                return;
            }
        }
        panic!(
            "Unthinkable: Tried to assign a type to {:?}, which is present in no scope",
            ident
        );
    }

    /// Find the type of a specific identifer, if it exists.
    ///
    /// This will modify the most recent occurrence of the identifier, which
    /// is correct in terms of shadowing.
    fn type_of(&self, ident: Ident) -> Option<&MaybeType> {
        self.scopes.iter().rev().find_map(|map| map.get(&ident))
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
