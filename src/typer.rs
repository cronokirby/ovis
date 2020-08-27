use crate::ast::{Definition, Expr, TypeExpr, AST};
use crate::interner::Ident;
use std::collections::HashMap;

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

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

impl<T> TypeStructure<T> {
    fn as_function(&self) -> Option<(&TypeStructure<T>, &TypeStructure<T>)> {
        match self {
            Base(_) => None,
            Function(f, a) => Some((f, a)),
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
pub enum MaybeBase {
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
pub type MaybeType = TypeStructure<MaybeBase>;

/// Try and find the most specialized version of two types
///
/// This will fail if the two types cannot be unified, because they have conflicting
/// information.
fn unify(t1: &MaybeType, t2: &MaybeType) -> Option<MaybeType> {
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
            let s1 = unify(f1, f2)?;
            let s2 = unify(a1, a2)?;
            Some(Function(Box::new(s1), Box::new(s2)))
        }
    }
}

fn unwrap_partial(t: &MaybeType) -> Option<Type> {
    match t {
        Base(Known(t)) => Some(Base(t.clone())),
        Function(t1, t2) => {
            let t1 = unwrap_partial(t1)?;
            let t2 = unwrap_partial(t2)?;
            Some(Function(Box::new(t1), Box::new(t2)))
        }
        _ => None,
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
pub enum TypeError<I> {
    UndefinedName(I),
    Expected(MaybeType, MaybeType),
    PartialType(I, MaybeType),
    ConflictingTypes(I, MaybeType, MaybeType),
}

impl<I: Display> Display for TypeError<I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            TypeError::UndefinedName(i) => write!(f, "Identifier {} is undefined", i),
            TypeError::Expected(t1, t2) => write!(f, "Expected {}, found {}", t1, t2),
            TypeError::ConflictingTypes(i, t1, t2) => write!(
                f,
                "Identifier {} has conflicting types {} and {}",
                i, t1, t2
            ),
            TypeError::PartialType(i, t) => {
                write!(f, "Identifier {} only reached partial type {}", i, t)
            }
        }
    }
}

impl<I: Display + Debug> Error for TypeError<I> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

type TypeResult<T> = Result<T, TypeError<Ident>>;

impl<I> TypeError<I> {
    pub fn replace_idents<J, F: FnMut(I) -> J>(self, mut f: F) -> TypeError<J> {
        match self {
            TypeError::UndefinedName(i) => TypeError::UndefinedName(f(i)),
            TypeError::Expected(t1, t2) => TypeError::Expected(t1, t2),
            TypeError::ConflictingTypes(i, t1, t2) => TypeError::ConflictingTypes(f(i), t1, t2),
            TypeError::PartialType(i, t) => TypeError::PartialType(f(i), t),
        }
    }
}

/// Expect to find a certain type, and report an error if we can't specialize to that type
fn try_unify(expected: &MaybeType, actual: &MaybeType) -> TypeResult<MaybeType> {
    match unify(expected, actual) {
        None => Err(TypeError::Expected(expected.clone(), actual.clone())),
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
    fn assign(&mut self, ident: Ident, typ: MaybeType) -> TypeResult<MaybeType> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(v) = scope.get_mut(&ident) {
                return match unify(v, &typ) {
                    None => Err(TypeError::ConflictingTypes(ident, v.clone(), typ)),
                    Some(t) => {
                        *v = t.clone();
                        Ok(t)
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
        expected: MaybeType,
        f: Expr<Ident, ()>,
        e: Expr<Ident, ()>,
    ) -> TypeResult<(Expr<Ident, Type>, MaybeType)> {
        // We want to try and infer the type of the argument first
        let (er, et) = self.expr(Base(Unknown), e)?;
        let (fr, ft) = self.expr(Function(Box::new(et), Box::new(expected.clone())), f)?;
        // And the final type for this expression is whatever we've managed to infer for the return type
        let (_, result_type) = ft
            .as_function()
            .expect("Unthinkable: specialized function type is not function type");
        let result_type = try_unify(&expected, result_type)?;
        Ok((Expr::Apply(Box::new(fr), Box::new(er)), result_type))
    }

    fn lambda(
        &mut self,
        expected: MaybeType,
        i: Ident,
        typ: Option<TypeExpr>,
        e: Expr<Ident, ()>,
    ) -> TypeResult<(Expr<Ident, Type>, MaybeType)> {
        // First we already know that we're going to end up with a lambda,
        // so we can go ahead and unify that information with the expected type, and catch
        // things like 3 + \x -> ... early
        let expected_function = try_unify(
            &expected,
            &Function(Box::new(Base(Unknown)), Box::new(Base(Unknown))),
        )?;
        let (expected_input, expected_output) = expected_function
            .as_function()
            .expect("Unthinkable: specialized function type is not function type");
        let i_declared = typ
            .clone()
            .map(|x| parse_type_expr(&x))
            .unwrap_or(Base(Unknown));
        self.context.enter();
        self.context.introduce(i);
        // Now we can try and assign the declared type and the expected input together
        self.context.assign(i, i_declared)?;
        self.context.assign(i, expected_input.clone())?;
        let (er, et) = self.expr(expected_output.clone(), e)?;
        // We've assigned it a type, so we can unwrap
        let maybe_i = self.context.type_of(i).unwrap();
        let typeof_i = unwrap_partial(maybe_i).ok_or(TypeError::PartialType(i, maybe_i.clone()))?;
        let maybe_i = maybe_i.clone();
        self.context.exit();
        let result_type = try_unify(
            &expected_function,
            &Function(Box::new(maybe_i), Box::new(et)),
        )?;
        Ok((Expr::Lambda(i, typ, typeof_i, Box::new(er)), result_type))
    }

    fn definitions(
        &mut self,
        defs: Vec<Definition<Ident, ()>>,
    ) -> TypeResult<Vec<Definition<Ident, Type>>> {
        let mut new_defs: Vec<Definition<Ident, Type>> = Vec::new();
        for d in defs {
            match d {
                Definition::Type(i, t) => {
                    self.context.introduce(i);
                    self.context.assign(i, parse_type_expr(&t))?;
                }
                Definition::Val(i, _, e) => {
                    // Reintroduction does nothing if we've already introduced this value
                    self.context.introduce(i);
                    // We expect to get whatever type we know of so far, or a unified version of it
                    let (re, rt) = self.expr(self.context.type_of(i).unwrap().clone(), e)?;
                    let rt = self.context.assign(i, rt)?;
                    // If after specializing both the potential type signature, and the
                    // inferred type for the expression body, we have a partial type,
                    // then that's a no-no
                    let rt = unwrap_partial(&rt).ok_or(TypeError::PartialType(i, rt))?;
                    new_defs.push(Definition::Val(i, rt, re))
                }
            }
        }
        Ok(new_defs)
    }

    fn handle_let(
        &mut self,
        expected: MaybeType,
        defs: Vec<Definition<Ident, ()>>,
        expr: Expr<Ident, ()>,
    ) -> TypeResult<(Expr<Ident, Type>, MaybeType)> {
        self.context.enter();
        let new_defs = self.definitions(defs)?;
        let (re, rt) = self.expr(expected.clone(), expr)?;
        self.context.exit();
        let rt = try_unify(&expected, &rt)?;
        Ok((Expr::Let(new_defs, Box::new(re)), rt))
    }

    fn expr(
        &mut self,
        expected: MaybeType,
        expr: Expr<Ident, ()>,
    ) -> TypeResult<(Expr<Ident, Type>, MaybeType)> {
        match expr {
            Expr::Name(n) => match self.context.type_of(n) {
                None => Err(TypeError::UndefinedName(n)),
                Some(_) => {
                    // We push down the expected type to the value, and
                    // then the result of the expression is the new unified type
                    let t = self.context.assign(n, expected)?;
                    Ok((Expr::Name(n), t))
                }
            },
            Expr::NumberLitt(n) => {
                let t = try_unify(&expected, &Base(Known(I64)))?;
                Ok((Expr::NumberLitt(n), t))
            }
            Expr::StringLitt(s) => {
                let t = try_unify(&expected, &Base(Known(Strng)))?;
                Ok((Expr::StringLitt(s), t))
            }
            Expr::Binary(op, e1, e2) => {
                let (r1, _) = self.expr(Base(Known(I64)), *e1)?;
                let (r2, _) = self.expr(Base(Known(I64)), *e2)?;
                let t = try_unify(&expected, &Base(Known(I64)))?;
                Ok((Expr::Binary(op, Box::new(r1), Box::new(r2)), t))
            }
            Expr::Negate(e) => {
                let (r, _) = self.expr(Base(Known(I64)), *e)?;
                let t = try_unify(&expected, &Base(Known(I64)))?;
                Ok((Expr::Negate(Box::new(r)), t))
            }
            Expr::Apply(f, e) => self.apply(expected, *f, *e),
            Expr::Lambda(i, typ, _, e) => self.lambda(expected, i, typ, *e),
            Expr::Let(defs, expr) => self.handle_let(expected, defs, *expr),
        }
    }

    fn run(&mut self, untyped: AST<Ident, ()>) -> TypeResult<AST<Ident, Type>> {
        let new_defs = self.definitions(untyped.definitions)?;
        Ok(AST {
            definitions: new_defs,
        })
    }
}

/// Try and assign types to a syntax tree
///
/// Of course, this can potentially fail, in which case we'll return an error describing
/// the kind of error that occurred.
pub fn typer(untyped: AST<Ident, ()>) -> TypeResult<AST<Ident, Type>> {
    let mut typer = Typer::new();
    typer.run(untyped)
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! assert_types {
        ($input:expr) => {{
            use crate::{interner, lexer, parser};
            let tokens = lexer::lex($input).unwrap();
            let ast = parser::parse(&tokens).unwrap();
            let (interned_ast, dict) = interner::intern(ast);
            let res = typer(interned_ast)
                .map_err(|e| e.replace_idents(|i| dict.get(i).unwrap().to_string()));
            assert!(
                res.is_ok(),
                "`{}` failed to type check: {}",
                $input,
                res.unwrap_err()
            );
        }};
    }

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

    #[test]
    fn basic_programs_type_check() {
        assert_types!("x : I64; x = 3");
        assert_types!(r#"x : String; x = "foo" "#);
        assert_types!(r#"f : I64 -> I64; f = \x -> x"#);
        assert_types!(r#"f : I64 -> I64 -> I64; f = \x -> \y -> y"#);
        assert_types!(r#"f : (I64 -> String) -> I64 -> String; f = \g -> \x -> g x"#);
        assert_types!(r#"f : (I64 -> I64) -> (I64 -> I64); f = \g -> g"#)
    }

    #[test]
    fn litterals_can_be_inferred() {
        assert_types!("x = 3");
        assert_types!(r#"x = "foo""#);
    }

    #[test]
    fn function_types_can_be_inferred_by_use() {
        assert_types!(r#"f = \x -> x + 2"#);
    }

    #[test]
    fn we_can_type_let() {
        assert_types!(
            r#"
        x =
          let
            f = \x -> x + 2
            b = 3
          in f b
        "#
        );
    }
}
