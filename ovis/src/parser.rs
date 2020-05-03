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

#[derive(Debug, PartialEq)]
pub enum AST {
    NumberLitt(i64),
    Binary(BinOp, Box<AST>, Box<AST>),
    Negate(Box<AST>),
}

peg::parser! {
    grammar ast_parser() for [Token] {
        use Token::*;

        rule number_litt() -> AST
            = n:$[NumberLitt(_)] { AST::NumberLitt(n[0].get_number().unwrap()) }

        rule arithmetic() -> AST = precedence!{
            a:(@) [Plus] b:@ { AST::Binary(BinOp::Add, Box::new(a), Box::new(b)) }
            a:(@) [Minus] b:@ { AST::Binary(BinOp::Sub, Box::new(a), Box::new(b)) }
            --
            a:(@) [Asterisk] b:@ { AST::Binary(BinOp::Mul, Box::new(a), Box::new(b)) }
            a:(@) [FSlash] b:@ { AST::Binary(BinOp::Div, Box::new(a), Box::new(b)) }
            --
            e:unary_minus_expr() { e }
        }

        rule unary_minus_expr() -> AST =
            [Minus] e:factor() { AST::Negate(Box::new(e)) } / e:factor() { e }

        rule factor() -> AST =
            e:number_litt() { e } / [LeftParens] e:arithmetic() [RightParens] { e }

        pub rule ast() -> AST = e:arithmetic() { e }
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
            assert!(tokens.is_ok());
            let tokens = tokens.unwrap();
            let res = parse(&tokens);
            assert!(res.is_ok());
            assert_eq!(res.unwrap(), $b);
        }};
    }

    #[test]
    fn parsing_numbers_works() {
        assert_parse!("-69", AST::Negate(Box::new(AST::NumberLitt(69))));
        assert_parse!("69", AST::NumberLitt(69));
    }

    macro_rules! binary {
        ($op:expr, $a:literal, $b:literal) => {
            binary!($op, AST::NumberLitt($a), AST::NumberLitt($b))
        };
        ($op:expr, $a:expr, $b:expr) => {
            AST::Binary($op, Box::new($a), Box::new($b))
        };
    }

    #[test]
    fn parsing_arithmetic_works() {
        assert_parse!("2 + 2", binary!(BinOp::Add, 2, 2));
        assert_parse!("2 * 2", binary!(BinOp::Mul, 2, 2));
        assert_parse!("2 / 2", binary!(BinOp::Div, 2, 2));
        assert_parse!(
            "2 / 3 / (4 / 5)",
            binary!(
                BinOp::Div,
                binary!(BinOp::Div, 2, 3),
                binary!(BinOp::Div, 4, 5)
            )
        );
        assert_parse!(
            "2 * 3 + 4 * 5",
            binary!(
                BinOp::Add,
                binary!(BinOp::Mul, 2, 3),
                binary!(BinOp::Mul, 4, 5)
            )
        );
    }

    #[test]
    fn unary_minus_and_binary_minus_work() {
        assert_parse!(
            "- 3 - 4",
            binary!(
                BinOp::Sub,
                AST::Negate(Box::new(AST::NumberLitt(3))),
                AST::NumberLitt(4)
            )
        );
    }
}
