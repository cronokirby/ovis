use peg;
use std::error::Error;

#[derive(Debug, PartialEq)]
pub enum AST {
    NumberLitt(i64),
}

peg::parser! {
    grammar ast_parser() for str {
        pub rule ast() -> AST
            = n:$("-"? ['0'..='9']+) { AST::NumberLitt(n.parse().unwrap()) }
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
}
