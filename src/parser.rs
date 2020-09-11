use std::error::Error;
use std::fmt;

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

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
        }
    }
}

/// Represents the syntactic form of a type
///
/// This is somewhat similar to the way we define our internal representation of types, modulo
/// what kind of identifier we use. This will always try to represent what kind of types
/// the user can write down in the source code, whereas our internal representation might diverge
/// from that.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeExpr {
    /// A function A -> B
    Function(Box<TypeExpr>, Box<TypeExpr>),
    /// The primitive integer type
    I64,
    /// The primitive string type
    Strng,
    /// A reference to some identifier, e.g. `a`
    TypeVar(String),
}

impl fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeExpr::Function(t1, t2) => write!(f, "(-> {} {})", t1, t2),
            TypeExpr::TypeVar(n) => write!(f, "{}", n),
            TypeExpr::I64 => write!(f, "I64"),
            TypeExpr::Strng => write!(f, "String"),
        }
    }
}

/// Represents an expression of a scheme, i.e. type with quantified polymorphic vars.
///
/// This is used to represent some declaration of a scheme, e.g. `{a} => a -> a`.
#[derive(Clone, Debug, PartialEq)]
pub struct SchemeExpr {
    /// The polymorphic variables being quantified over
    ///
    /// They also have whatever kind of identifier we use for variable names.
    pub type_vars: Vec<String>,
    /// The expression being quantified over
    pub typ: TypeExpr,
}

impl fmt::Display for SchemeExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.type_vars.is_empty() {
            write!(f, "(=> (")?;
            let mut i = 0;
            for v in &self.type_vars {
                if i == 0 {
                    write!(f, "{}", v)?;
                } else {
                    write!(f, " {}", v)?;
                }
                i += 1;
            }
            write!(f, ") {})", self.typ)
        } else {
            write!(f, "{}", self.typ)
        }
    }
}

/// Represents the results of parsing out an expression
#[derive(Debug, PartialEq)]
pub enum Expr {
    /// A lambda introducing multiple names, that will be bound inside an expression
    Lambda(Vec<String>, Box<Expr>),
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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Lambda(names, expr) => {
                write!(f, "(λ (")?;
                let mut i = 0;
                for name in names {
                    if i == 0 {
                        write!(f, "{}", name)?;
                    } else {
                        write!(f, " {}", name)?;
                    }
                    i += 1;
                }
                write!(f, ") {})", expr)?;
            }
            Expr::Name(n) => write!(f, "{}", n)?,
            Expr::NumberLitt(i) => write!(f, "{}", i)?,
            Expr::StringLitt(s) => write!(f, "\"{}\"", s)?,
            Expr::Binary(op, e1, e2) => write!(f, "({} {} {})", op, e1, e2)?,
            Expr::Negate(e) => write!(f, "(- {})", e)?,
            Expr::Apply(e1, e2) => write!(f, "(apply {} {})", e1, e2)?,
            Expr::Let(defs, e) => {
                write!(f, "(let (")?;
                let mut i = 0;
                for d in defs {
                    if i == 0 {
                        write!(f, "{}", d)?;
                    } else {
                        write!(f, " {}", d)?;
                    }
                    i += 1;
                }
                write!(f, ") {})", e)?;
            }
        }
        Ok(())
    }
}

/// Represents the parse result of some definition
#[derive(Debug, PartialEq)]
pub enum Definition {
    /// A definition assigning some type to some identifier
    Type(String, SchemeExpr),
    /// A definition assigning some expression to some identifier
    Val(String, Expr),
}

impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Definition::Type(n, s) => write!(f, "(: {} {})", n, s),
            Definition::Val(n, e) => write!(f, "(= {} {})", n, e),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct AST {
    pub definitions: Vec<Definition>,
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(ast")?;
        for def in &self.definitions {
            writeln!(f, "  {}", def)?;
        }
        write!(f, ")")
    }
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

        rule scheme() -> SchemeExpr
            = [LeftBrace] vs:(name() ** [Comma]) [RightBrace] [FatArrow] t:typ() { SchemeExpr { type_vars: vs, typ: t } }
            / t:typ() { SchemeExpr { type_vars: Vec::new(), typ: t }}

        rule typ() -> TypeExpr = precedence!{
            a:@ [RightArrow] b:(@) { TypeExpr::Function(Box::new(a), Box::new(b)) }
            --
            [LeftParens] t:typ() [RightParens] { t }
            n:name() { TypeExpr::TypeVar(n) }
            t:primitive_type() { t }
        }

        rule primitive_type() -> TypeExpr
            = [TypeI64] { TypeExpr::I64 }
            / [TypeString] { TypeExpr::Strng }


        rule expr() -> Expr = lambda_expr() / let_expr() / arithmetic()

        rule lambda_expr() -> Expr
            = [BSlash] ns:name()+ [RightArrow] e:expr() { Expr::Lambda(ns,  Box::new(e)) }

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
            / n:name() [Colon] t:scheme() { Definition::Type(n, t) }

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
                Expr::Lambda(vec!["y".into()], Box::new(Expr::NumberLitt(2)))
            )
        );
        assert_parse!(
            r#"x = \a -> \b -> 2"#,
            val_def!(
                "x",
                Expr::Lambda(
                    vec!["a".into()],
                    Box::new(Expr::Lambda(
                        vec!["b".into()],
                        Box::new(Expr::NumberLitt(2))
                    ))
                )
            )
        );
        assert_parse!(
            r#"f = \x y -> x"#,
            val_def!(
                "f",
                Expr::Lambda(
                    vec!["x".into(), "y".into()],
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
                    Definition::Type(
                        "x".into(),
                        SchemeExpr {
                            type_vars: Vec::new(),
                            typ: TypeExpr::Strng
                        }
                    ),
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
                    SchemeExpr {
                        type_vars: Vec::new(),
                        typ: TypeExpr::Function(
                            Box::new(TypeExpr::Function(
                                Box::new(TypeExpr::I64),
                                Box::new(TypeExpr::I64)
                            )),
                            Box::new(TypeExpr::Function(
                                Box::new(TypeExpr::I64),
                                Box::new(TypeExpr::I64)
                            )),
                        )
                    }
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

    #[test]
    fn polymorphic_schemes_parse() {
        assert_parse!(
            "const : {a, b} => a",
            AST {
                definitions: vec![Definition::Type(
                    "const".into(),
                    SchemeExpr {
                        type_vars: vec!["a".into(), "b".into()],
                        typ: TypeExpr::TypeVar("a".into())
                    }
                )]
            }
        );
        assert_parse!(
            "void : {a} => a",
            AST {
                definitions: vec![Definition::Type(
                    "void".into(),
                    SchemeExpr {
                        type_vars: vec!["a".into()],
                        typ: TypeExpr::TypeVar("a".into())
                    }
                )]
            }
        );
    }
}
