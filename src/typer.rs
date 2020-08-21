use crate::ast::{Definition, Expr, TypeExpr, AST};
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
    Strng,
}

use BaseType::*;

impl Display for BaseType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            I64 => write!(f, "I64"),
            Strng => write!(f, "String"),
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

/// Try and find the most specialized version of two types
fn specialize(t1: &MaybeType, t2: &MaybeType) -> Option<MaybeType> {
    match (t1, t2) {
        (Base(Known(t1)), Base(Known(t2))) => {
            if t1 != t2 {
                None
            } else {
                Some(Base(Known(t2.clone())))
            }
        }
        (Base(Unknown), t2) => Some(t2.clone()),
        (t1, Base(Unknown)) => Some(t1.clone()),
        (Function(_, _), Base(_)) => None,
        (Base(_), Function(_, _)) => None,
        (Function(f1, a1), Function(f2, a2)) => {
            let s1 = specialize(f1, f2)?;
            let s2 = specialize(a1, a2)?;
            Some(Function(Box::new(s1), Box::new(s2)))
        }
    }
}

/// Try and convert a type expression to a maybe type
fn parse_type_expr(expr: &TypeExpr) -> MaybeType {
    match expr {
        TypeExpr::I64 => Base(Known(I64)),
        TypeExpr::Strng => Base(Known(Strng)),
        TypeExpr::Function(t1, t2) => {
            Function(Box::new(parse_type_expr(t1)), Box::new(parse_type_expr(t2)))
        }
    }
}

/// This represents the errors that can occurr will assigning types to the program tree
#[derive(Clone, Debug, PartialEq)]
pub enum TypeError {
    UndefinedName(Ident),
    Expected(MaybeType, MaybeType),
    ConflictingTypes(Ident, MaybeType, MaybeType),
    Unknown,
}

impl Display for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            TypeError::UndefinedName(i) => write!(f, "Undefined identifier {:?}", i),
            TypeError::Expected(t1, t2) => write!(f, "Expected {}, found {}", t1, t2),
            TypeError::ConflictingTypes(i, t1, t2) => {
                write!(f, "Conflicting types for {:?}, {}, and {}", i, t1, t2)
            }
            TypeError::Unknown => write!(f, "Unknown Type Error"),
        }
    }
}

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Expect to find a certain type, and report an error if we can't specialize to that type
fn expect_type(expected: MaybeType, actual: MaybeType) -> Result<MaybeType, TypeError> {
    match specialize(&expected, &actual) {
        None => Err(TypeError::Expected(expected, actual)),
        Some(t) => Ok(t),
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
    ///
    /// It will also fail if we try to assign a type that's incompatible with the current type we have
    fn assign(&mut self, ident: Ident, typ: MaybeType) -> Result<(), TypeError> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(v) = scope.get_mut(&ident) {
                return match specialize(v, &typ) {
                    None => Err(TypeError::ConflictingTypes(ident, v.clone(), typ)),
                    Some(t) => {
                        *v = t;
                        Ok(())
                    }
                };
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

/// Represents a struct containing the information we need to type things
struct Typer {
    /// The context containing the types we're working with
    context: Context,
}

impl Typer {
    fn new() -> Self {
        Typer {
            context: Context::new(),
        }
    }

    fn apply(
        &mut self,
        f: Expr<Ident, ()>,
        e: Expr<Ident, ()>,
    ) -> Result<(Expr<Ident, Type>, MaybeType), TypeError> {
        let (fr, ft) = self.expr(f)?;
        let (er, et) = self.expr(e)?;
        // We expect the function type to conform with the argument type
        let ft = expect_type(Function(Box::new(et), Box::new(Base(Unknown))), ft)?;
        // And the final type for this expression is whatever we've managed to infer for the return type
        let result_type = match ft {
            Function(_, rt) => *rt,
            _ => panic!("Unthinkable: specialized function type is not function type"),
        };
        Ok((Expr::Apply(Box::new(fr), Box::new(er)), result_type))
    }

    fn expr(&mut self, expr: Expr<Ident, ()>) -> Result<(Expr<Ident, Type>, MaybeType), TypeError> {
        match expr {
            Expr::Name(n) => match self.context.type_of(n) {
                None => Err(TypeError::UndefinedName(n)),
                Some(typ) => Ok((Expr::Name(n), typ.clone())),
            },
            Expr::NumberLitt(n) => Ok((Expr::NumberLitt(n), Base(Known(I64)))),
            Expr::StringLitt(s) => Ok((Expr::StringLitt(s), Base(Known(Strng)))),
            Expr::Binary(op, e1, e2) => {
                let (r1, t1) = self.expr(*e1)?;
                expect_type(Base(Known(I64)), t1)?;
                let (r2, t2) = self.expr(*e2)?;
                expect_type(Base(Known(I64)), t2)?;
                // We know that the result of a binary expression is always an integer
                Ok((
                    Expr::Binary(op, Box::new(r1), Box::new(r2)),
                    Base(Known(I64)),
                ))
            }
            Expr::Negate(e) => {
                let (r, t) = self.expr(*e)?;
                expect_type(Base(Known(I64)), t)?;

                Ok((Expr::Negate(Box::new(r)), Base(Known(I64))))
            }
            Expr::Apply(f, e) => self.apply(*f, *e),
            _ => unimplemented!(),
        }
    }

    fn run(&mut self, untyped: AST<Ident, ()>) -> Result<AST<Ident, Type>, TypeError> {
        // First, try and gather all the top level type annotations
        for d in &untyped.definitions {
            match d {
                Definition::Val(_, _, _) => {}
                Definition::Type(i, t) => {
                    self.context.introduce(*i);
                    self.context.assign(*i, parse_type_expr(t))?;
                }
            }
        }
        unimplemented!()
    }
}

/// Try and assign types to a syntax tree
///
/// Of course, this can potentially fail, in which case we'll return an error describing
/// the kind of error that occurred.
pub fn typer(untyped: AST<Ident, ()>) -> Result<AST<Ident, Type>, TypeError> {
    let mut typer = Typer::new();
    typer.run(untyped)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn types_display_correctly() {
        assert_eq!("I64", format!("{}", I64));
        assert_eq!("String", format!("{}", Strng));
        assert_eq!(
            "I64 -> String",
            format!("{}", Function(Box::new(Base(I64)), Box::new(Base(Strng))))
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
