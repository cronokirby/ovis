use peg;
use std::error::Error;

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
}

peg::parser! {
    grammar ast_parser() for str {
        rule number_litt() -> AST
            = n:$("-"? ['0'..='9']+) { AST::NumberLitt(n.parse().unwrap()) }

        rule arithmetic() -> AST = precedence!{
            a:(@) "+" b:@ { AST::Binary(BinOp::Add, Box::new(a), Box::new(b)) }
            a:(@) "-" b:@ { AST::Binary(BinOp::Sub, Box::new(a), Box::new(b)) }
            --
            a:(@) "*" b:@ { AST::Binary(BinOp::Mul, Box::new(a), Box::new(b)) }
            a:(@) "/" b:@ { AST::Binary(BinOp::Div, Box::new(a), Box::new(b)) }
            --
            n:number_litt() { n }
            "(" e:arithmetic() ")" { e }
        }

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
pub fn parse(input: &str) -> Result<AST, impl Error> {
    ast_parser::ast(input)
}

#[cfg(test)]
mod test {
    use super::*;

    /// Assert that a string correctly parses to a given AST
    macro_rules! assert_parse {
        ($a:expr, $b:expr) => {{
            let res = parse($a);
            assert!(res.is_ok());
            assert_eq!(res.unwrap(), $b);
        }};
    }

    #[test]
    fn parsing_numbers_works() {
        assert_parse!("-69", AST::NumberLitt(-69));
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
        assert_parse!("2+2", binary!(BinOp::Add, 2, 2));
        assert_parse!("2*2", binary!(BinOp::Mul, 2, 2));
        assert_parse!("2/2", binary!(BinOp::Div, 2, 2));
        assert_parse!(
            "2/3/(4/5)",
            binary!(
                BinOp::Div,
                binary!(BinOp::Div, 2, 3),
                binary!(BinOp::Div, 4, 5)
            )
        );
        assert_parse!(
            "2*3+4*5",
            binary!(
                BinOp::Add,
                binary!(BinOp::Mul, 2, 3),
                binary!(BinOp::Mul, 4, 5)
            )
        );
    }
}
