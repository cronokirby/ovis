use std::error::Error;
use std::fmt;

use peg;

use crate::ast::{BinOp, TypeExpr};
use crate::lexer::Token;

/// Represents the results of parsing out an expression
#[derive(Debug, PartialEq)]
pub enum Expr {
    /// A lambda introducing a single name, potentially
    /// with a type annotation, and having a body as another expression
    Lambda(Vec<(String, Option<TypeExpr>)>, Box<Expr>),
    /// A let expression, with multiple definitions before
    /// a final expression using those definitions
    Let(Vec<Definition>, Box<Expr>),
    Name(String),
    NumberLitt(i64),
    StringLitt(String),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Negate(Box<Expr>),
    Apply(Box<Expr>, Box<Expr>),
}

/// Represents the parse result of some definition
#[derive(Debug, PartialEq)]
pub enum Definition {
    /// A definition assigning some type to some identifier
    Type(String, TypeExpr),
    /// A definition assigning some expression to some identifier
    Val(String, Expr),
}

#[derive(Debug, PartialEq)]
pub struct AST {
    pub definitions: Vec<Definition>,
}

peg::parser! {
    grammar ast_parser() for [Token] {
        use Token::*;

        rule number_litt() -> Expr
            = n:$[NumberLitt(_)] { Expr::NumberLitt(n[0].get_number().unwrap()) }

        rule string_litt() -> Expr
            = s:$[StringLitt(_)] { Expr::StringLitt(s[0].get_string().unwrap().to_string()) }

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
            / [TypeString] { TypeExpr::Strng }


        rule expr() -> Expr = lambda_expr() / let_expr() / arithmetic()

        rule lambda_name() -> (String, Option<TypeExpr>)
            = [LeftParens] n:name() [Colon] t:typ() [RightParens] { (n, Some(t)) }
            / n:name() { (n, None) }

        rule lambda_expr() -> Expr
            = [BSlash] nt:lambda_name()+ [RightArrow] e:expr() { Expr::Lambda(nt,  Box::new(e)) }

        rule let_expr() -> Expr
            = [Let] [LeftBrace] ds:(definition() ** [Semicolon]) [RightBrace] [In] e:expr() { Expr::Let(ds, Box::new(e)) }

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
            / s:string_litt()
            / n:name() { Expr::Name(n) }
            / [LeftParens] e:expr() [RightParens] { e }


        rule definition() -> Definition
            = n:name() [Equal] e:expr() { Definition::Val(n, e) }
            / n:name() [Colon] t:typ() { Definition::Type(n, t) }

        pub rule ast() -> AST = [LeftBrace] ds:(definition() ** [Semicolon]) [RightBrace] { AST { definitions: ds } }
    }
}

/// Represents the type of error that can occurr while parsing
///
/// This is an opaque type, and should be presented to the user directly, more or less.
/// There's no way to recover from a parse error, with this compiler architecture, anyways.
#[derive(Debug, PartialEq)]
pub struct ParseError(peg::error::ParseError<usize>);

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0.source()
    }
}

impl From<peg::error::ParseError<usize>> for ParseError {
    fn from(e: peg::error::ParseError<usize>) -> Self {
        ParseError(e)
    }
}

/// Parse a string with into our first AST.
///
/// This can fail if the string doesn't match the syntax of our language.
///
/// # Examples
///
/// ```
/// let result = parse("-69");
/// assert_eq!(result, Ok(AST::NumberLitt(69)));
/// ```
pub fn parse(input: &[Token]) -> Result<AST, ParseError> {
    ast_parser::ast(input).map_err(|x| x.into())
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
            val_def!(
                "x",
                Expr::Lambda(vec![("y".into(), None)], Box::new(Expr::NumberLitt(2)))
            )
        );
        assert_parse!(
            r#"x = \a -> \b -> 2"#,
            val_def!(
                "x",
                Expr::Lambda(
                    vec![("a".into(), None)],
                    Box::new(Expr::Lambda(
                        vec![("b".into(), None)],
                        Box::new(Expr::NumberLitt(2))
                    ))
                )
            )
        );
        assert_parse!(
            r#"f = \(x : I64) y -> x"#,
            val_def!(
                "f",
                Expr::Lambda(
                    vec![("x".into(), Some(TypeExpr::I64)), ("y".into(), None)],
                    Box::new(Expr::Name("x".into()))
                )
            )
        )
    }

    #[test]
    fn string_expressions_parse() {
        assert_parse!(
            "x : String\nx = \"foo\"",
            AST {
                definitions: vec![
                    Definition::Type("x".into(), TypeExpr::Strng),
                    Definition::Val("x".into(), Expr::StringLitt("foo".into()))
                ]
            }
        )
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

    #[test]
    fn let_expressions_can_parse() {
        assert_parse!(
            "x = let { y = 2; z = 3 } in 4",
            val_def!(
                "x",
                Expr::Let(
                    vec![
                        Definition::Val("y".into(), Expr::NumberLitt(2)),
                        Definition::Val("z".into(), Expr::NumberLitt(3))
                    ],
                    Box::new(Expr::NumberLitt(4))
                )
            )
        );
    }
}
