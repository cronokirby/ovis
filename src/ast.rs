/// Represents a binary operator we can use in arithmetic expressions
#[derive(Debug, PartialEq)]
pub enum BinOp {
    /// The + operator
    Add,
    /// The - operator
    Sub,
    /// The * operator
    Mul,
    /// The / operator
    Div,
}

/// Represents a single expression in our language
#[derive(Debug, PartialEq)]
pub enum Expr<I, T> {
    /// A lambda abstraction / function litteral
    Lambda(I, T, Box<Expr<I, T>>),
    /// A let expression, where we have a sequence of definitions bound before
    /// an expression.
    Let(Vec<Definition<I, T>>, Box<Expr<I, T>>),
    /// A reference to a variable name or definition
    Name(I),
    /// A reference to a positive number
    NumberLitt(i64),
    /// A reference to a string litteral
    StringLitt(String),
    /// A binary operation between expressions
    Binary(BinOp, Box<Expr<I, T>>, Box<Expr<I, T>>),
    /// Unary negation of an expression
    Negate(Box<Expr<I, T>>),
    /// Represents the application of one function to an argument
    Apply(Box<Expr<I, T>>, Box<Expr<I, T>>),
}

impl<I, T> Expr<I, T> {
    fn replace_idents<J, F: FnMut(I) -> J>(self, f: &mut F) -> Expr<J, T> {
        match self {
            Expr::Lambda(i, t, e) => Expr::Lambda(f(i), t, Box::new(e.replace_idents(f))),
            Expr::Let(defs, e) => Expr::Let(
                defs.into_iter().map(|d| d.replace_idents(f)).collect(),
                Box::new(e.replace_idents(f)),
            ),
            Expr::Name(i) => Expr::Name(f(i)),
            Expr::NumberLitt(n) => Expr::NumberLitt(n),
            Expr::StringLitt(s) => Expr::StringLitt(s),
            Expr::Binary(op, e1, e2) => Expr::Binary(
                op,
                Box::new(e1.replace_idents(f)),
                Box::new(e2.replace_idents(f)),
            ),
            Expr::Negate(e) => Expr::Negate(Box::new(e.replace_idents(f))),
            Expr::Apply(ef, e) => Expr::Apply(
                Box::new(ef.replace_idents(f)),
                Box::new(e.replace_idents(f)),
            ),
        }
    }
}

/// Represents a type, formed through primitive types, or composition of other types
#[derive(Clone, Debug, PartialEq)]
pub enum TypeExpr<I> {
    /// A function A -> B
    Function(Box<TypeExpr<I>>, Box<TypeExpr<I>>),
    /// The primitive integer type
    I64,
    /// The primitive string type
    Strng,
    /// A reference to some identifier, e.g. `a`
    ///
    /// Of course, that type variable has to be quantified in some scope for this
    /// to make any sense.
    TypeVar(I),
}

impl<I> TypeExpr<I> {
    fn replace_idents<J, F: FnMut(I) -> J>(self, f: &mut F) -> TypeExpr<J> {
        match self {
            TypeExpr::TypeVar(i) => TypeExpr::TypeVar(f(i)),
            TypeExpr::Function(fe, e) => TypeExpr::Function(
                Box::new(fe.replace_idents(f)),
                Box::new(e.replace_idents(f)),
            ),
            TypeExpr::I64 => TypeExpr::I64,
            TypeExpr::Strng => TypeExpr::Strng,
        }
    }
}

/// Represents an expression of a scheme, i.e. type with quantified polymorphic vars.
///
/// This is used to represent some declaration of a scheme, e.g. `{a} => a -> a`.
#[derive(Clone, Debug, PartialEq)]
pub struct SchemeExpr<I> {
    /// The polymorphic variables being quantified over
    ///
    /// They also have whatever kind of identifier we use for variable names.
    pub type_vars: Vec<I>,
    /// The expression being quantified over
    pub typ: TypeExpr<I>,
}

impl<I> SchemeExpr<I> {
    fn replace_idents<J, F: FnMut(I) -> J>(self, f: &mut F) -> SchemeExpr<J> {
        let typ = self.typ.replace_idents(f);
        let type_vars = self.type_vars.into_iter().map(f).collect();
        SchemeExpr { type_vars, typ }
    }
}

/// Represents a definition or annotation
///
/// A definition assigns a name to an expression, and a type annotation assigns
/// an explicit type to a name. Type annotations are optional in our language.
#[derive(Debug, PartialEq)]
pub enum Definition<I, T> {
    /// Represents an annotation of a name with a given type
    Type(I, SchemeExpr<I>),
    /// Represents the definition of name, with its corresponding expression
    Val(I, T, Expr<I, T>),
}

impl<I, T> Definition<I, T> {
    fn replace_idents<J, F: FnMut(I) -> J>(self, f: &mut F) -> Definition<J, T> {
        match self {
            Definition::Type(i, t) => Definition::Type(f(i), t.replace_idents(f)),
            Definition::Val(i, t, e) => Definition::Val(f(i), t, e.replace_idents(f)),
        }
    }
}

/// Represents a program in our language.
///
/// This is parametrized over the type of identifiers
///
/// A program is just a sequence of value or type annotations
#[derive(Debug, PartialEq)]
pub struct AST<I, T = ()> {
    pub definitions: Vec<Definition<I, T>>,
}

impl<I, T> AST<I, T> {
    pub fn replace_idents<J, F: FnMut(I) -> J>(self, mut f: F) -> AST<J, T> {
        AST {
            definitions: self
                .definitions
                .into_iter()
                .map(|d| d.replace_idents(&mut f))
                .collect(),
        }
    }
}
