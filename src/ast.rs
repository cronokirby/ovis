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
pub enum Expr<I> {
    /// A lambda abstraction / function litteral
    Lambda(I, Box<Expr<I>>),
    /// A let expression, where we have a sequence of definitions bound before
    /// an expression.
    Let(Vec<Definition<I>>, Box<Expr<I>>),
    /// A reference to a variable name or definition
    Name(I),
    /// A reference to a positive number
    NumberLitt(i64),
    /// A reference to a string litteral
    StringLitt(String),
    /// A binary operation between expressions
    Binary(BinOp, Box<Expr<I>>, Box<Expr<I>>),
    /// Unary negation of an expression
    Negate(Box<Expr<I>>),
    /// Represents the application of one function to an argument
    Apply(Box<Expr<I>>, Box<Expr<I>>),
}

/// Represents a type, formed through primitive types, or composition of other types
#[derive(Debug, PartialEq)]
pub enum TypeExpr {
    /// A function A -> B
    Function(Box<TypeExpr>, Box<TypeExpr>),
    /// The primitive integer type
    I64,
    /// The primitive string type
    Strng,
}

/// Represents a definition or annotation
///
/// A definition assigns a name to an expression, and a type annotation assigns
/// an explicit type to a name. Type annotations are optional in our language.
#[derive(Debug, PartialEq)]
pub enum Definition<I> {
    /// Represents an annotation of a name with a given type
    Type(I, TypeExpr),
    /// Represents the definition of name, with its corresponding expression
    Val(I, Expr<I>),
}

/// Represents a program in our language.
///
/// This is parametrized over the type of identifiers
///
/// A program is just a sequence of value or type annotations
#[derive(Debug, PartialEq)]
pub struct AST<I> {
    pub definitions: Vec<Definition<I>>,
}
