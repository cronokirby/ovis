use std::error::Error;

use peg;

use crate::lexer::Token;

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
pub enum Expr {
    /// A lambda abstraction / function litteral
    Lambda(String, Box<Expr>),
    /// A reference to a variable name or definition
    Name(String),
    /// A reference to a positive number
    NumberLitt(i64),
    /// A binary operation between expressions
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// Unary negation of an expression
    Negate(Box<Expr>),
    /// Represents the application of one function to an argument
    Apply(Box<Expr>, Box<Expr>),
}

/// Represents a type, formed through primitive types, or composition of other types
#[derive(Debug, PartialEq)]
pub enum TypeExpr {
    /// A function A -> B
    Function(Box<TypeExpr>, Box<TypeExpr>),
    /// The primitive integer type
    I64,
}

/// Represents a definition or annotation
///
/// A definition assigns a name to an expression, and a type annotation assigns
/// an explicit type to a name. Type annotations are optional in our language.
#[derive(Debug, PartialEq)]
pub enum Definition {
    /// Represents an annotation of a name with a given type
    Type(String, TypeExpr),
    /// Represents the definition of name, with its corresponding expression
    Val(String, Expr),
}

/// Represents a program in our language.
///
/// A program is just a sequence of value or type annotations
#[derive(Debug, PartialEq)]
pub struct AST {
    definitions: Vec<Definition>,
}

peg::parser! {
    grammar ast_parser() for [Token] {
        use Token::*;

        rule number_litt() -> Expr
            = n:$[NumberLitt(_)] { Expr::NumberLitt(n[0].get_number().unwrap()) }

        rule name() -> String
            = n:$[Name(_)] { n[0].get_name().unwrap().to_string() }

        rule typ() -> TypeExpr = precedence!{
            a:@ [RightArrow] b:(@) { TypeExpr::Function(Box::new(a), Box::new(b)) }
            --
            [LeftParens] t:typ() [RightParens] { t }
            t:primitive_type() { t }
        }

        rule primitive_type() -> TypeExpr
            = [TypeI64] { TypeExpr::I64 }


        rule expr() -> Expr = e:lambda_expr() { e }

        rule lambda_expr() -> Expr
            = [BSlash] n:name() [RightArrow] e:arithmetic() { Expr::Lambda(n, Box::new(e)) }
            / e:arithmetic() { e }

        rule arithmetic() -> Expr = precedence!{
            a:(@) [Plus] b:@ { Expr::Binary(BinOp::Add, Box::new(a), Box::new(b)) }
            a:(@) [Minus] b:@ { Expr::Binary(BinOp::Sub, Box::new(a), Box::new(b)) }
            --
            a:(@) [Asterisk] b:@ { Expr::Binary(BinOp::Mul, Box::new(a), Box::new(b)) }
            a:(@) [FSlash] b:@ { Expr::Binary(BinOp::Div, Box::new(a), Box::new(b)) }
            --
            e:unary_minus_expr() { e }
        }

        rule unary_minus_expr() -> Expr
            = [Minus] e:app_expr() { Expr::Negate(Box::new(e)) } / e:app_expr() { e }

        rule app_expr() -> Expr
            = f:factor() x:factor() { Expr::Apply(Box::new(f), Box::new(x))}
            / e:factor() { e }

        rule factor() -> Expr
            = e:number_litt() { e }
            / n:name() { Expr::Name(n) }
            / [LeftParens] e:expr() [RightParens] { e }


        rule definition() -> Definition
            = n:name() [Equal] e:expr() { Definition::Val(n, e) }
            / n:name() [Colon] t:typ() { Definition::Type(n, t) }

        pub rule ast() -> AST = ds:(definition() ** [Semicolon]) { AST { definitions: ds } }
    }
}

/// Parse a string with into our first AST.
///
/// This can fail if the string doesn't match the syntax of our language. We return
/// `impl Error` in order to hide the internal implementation of errors. There's nothing
/// useful we can do in terms of recovery anyways. If parsing fails, we should just
/// present that error to the user.
///
/// # Examples
///
/// ```
/// let result = parse("-69");
/// assert_eq!(result, Ok(AST::NumberLitt(69)));
/// ```
pub fn parse(input: &[Token]) -> Result<AST, impl Error> {
    ast_parser::ast(input)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lexer::lex;

    /// Assert that a string correctly parses to a given AST
    macro_rules! assert_parse {
        ($a:expr, $b:expr) => {{
            let tokens = lex($a);
            dbg!(&tokens);
            assert!(tokens.is_ok());
            let tokens = tokens.unwrap();
            let res = parse(&tokens);
            dbg!(&res);
            assert!(res.is_ok());
            assert_eq!(res.unwrap(), $b);
        }};
    }

    macro_rules! val_def {
        ($x:expr, $e:expr) => {
            AST {
                definitions: vec![Definition::Val($x.into(), $e)],
            }
        };
    }

    #[test]
    fn parsing_numbers_works() {
        assert_parse!(
            "x = -69",
            val_def!("x", Expr::Negate(Box::new(Expr::NumberLitt(69))))
        );
        assert_parse!("x = 69", val_def!("x", Expr::NumberLitt(69)));
    }

    macro_rules! binary {
        ($op:expr, $a:literal, $b:literal) => {
            binary!($op, Expr::NumberLitt($a), Expr::NumberLitt($b))
        };
        ($op:expr, $a:expr, $b:expr) => {
            Expr::Binary($op, Box::new($a), Box::new($b))
        };
    }

    #[test]
    fn parsing_arithmetic_works() {
        assert_parse!("x = 2 + 2", val_def!("x", binary!(BinOp::Add, 2, 2)));
        assert_parse!("x = 2 * 2", val_def!("x", binary!(BinOp::Mul, 2, 2)));
        assert_parse!("x = 2 / 2", val_def!("x", binary!(BinOp::Div, 2, 2)));
        assert_parse!(
            "x = 2 / 3 / (4 / 5)",
            val_def!(
                "x",
                binary!(
                    BinOp::Div,
                    binary!(BinOp::Div, 2, 3),
                    binary!(BinOp::Div, 4, 5)
                )
            )
        );
        assert_parse!(
            "x = 2 * 3 + 4 * 5",
            val_def!(
                "x",
                binary!(
                    BinOp::Add,
                    binary!(BinOp::Mul, 2, 3),
                    binary!(BinOp::Mul, 4, 5)
                )
            )
        );
    }

    #[test]
    fn unary_minus_and_binary_minus_work() {
        assert_parse!(
            "x = - 3 - 4",
            val_def!(
                "x",
                binary!(
                    BinOp::Sub,
                    Expr::Negate(Box::new(Expr::NumberLitt(3))),
                    Expr::NumberLitt(4)
                )
            )
        );
    }

    #[test]
    fn lambda_expressions_parse() {
        assert_parse!(
            r#"x = \y -> 2"#,
            val_def!("x", Expr::Lambda("y".into(), Box::new(Expr::NumberLitt(2))))
        );
    }

    #[test]
    fn names_in_arithmetic_expressions_parse() {
        assert_parse!(
            "x = y + z",
            val_def!(
                "x",
                binary!(BinOp::Add, Expr::Name("y".into()), Expr::Name("z".into()))
            )
        );
    }

    #[test]
    fn type_definitions_parse() {
        assert_parse!(
            "apply : (I64 -> I64) -> I64 -> I64",
            AST {
                definitions: vec![Definition::Type(
                    "apply".into(),
                    TypeExpr::Function(
                        Box::new(TypeExpr::Function(
                            Box::new(TypeExpr::I64),
                            Box::new(TypeExpr::I64)
                        )),
                        Box::new(TypeExpr::Function(
                            Box::new(TypeExpr::I64),
                            Box::new(TypeExpr::I64)
                        )),
                    )
                )]
            }
        )
    }

    #[test]
    fn multiple_definitions_parse() {
        assert_parse!(
            "x = 3;y = 5",
            AST {
                definitions: vec![
                    Definition::Val("x".into(), Expr::NumberLitt(3)),
                    Definition::Val("y".into(), Expr::NumberLitt(5))
                ]
            }
        )
    }
}
