mod ast;
mod interner;
mod lexer;
mod parser;
mod typer;

use std::error::Error;
use std::fmt;
use std::fs;

#[derive(Debug, PartialEq)]
enum CompileError {
    /// An error occurring while lexing
    LexError(Vec<lexer::LexError>),
    /// An error occurring while parsing
    ParseError(parser::ParseError),
    /// An error occurring while typing
    TypeError(typer::TypeError),
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompileError::LexError(errors) => {
                writeln!(f, "Errors encountered during Lexing:")?;
                for e in errors {
                    writeln!(f, "{}", e)?;
                }
                Ok(())
            }
            CompileError::ParseError(e) => write!(f, "Parse Error: {}", e),
            CompileError::TypeError(e) => write!(f, "Type Error: {}", e),
        }
    }
}

impl Error for CompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            CompileError::LexError(_) => None,
            CompileError::ParseError(e) => Some(e),
            CompileError::TypeError(e) => Some(e),
        }
    }
}

impl From<Vec<lexer::LexError>> for CompileError {
    fn from(e: Vec<lexer::LexError>) -> Self {
        CompileError::LexError(e)
    }
}

impl From<parser::ParseError> for CompileError {
    fn from(e: parser::ParseError) -> Self {
        CompileError::ParseError(e)
    }
}

impl From<typer::TypeError> for CompileError {
    fn from(e: typer::TypeError) -> Self {
        CompileError::TypeError(e)
    }
}

fn parse_and_type(contents: &str) -> Result<ast::AST<interner::Ident, typer::Type>, CompileError> {
    let tokens = lexer::lex(contents)?;
    let ast = parser::parse(&tokens)?;
    let interned = interner::intern(ast);
    let typed = typer::typer(interned.ast)?;
    Ok(typed)
}

fn main() {
    let all_args: Vec<String> = std::env::args().collect();
    match all_args.get(1).map(String::as_str) {
        Some("compile") => match all_args.get(2) {
            None => println!("Insufficient arguments"),
            Some(path) => {
                let contents = fs::read_to_string(path).expect("Couldn't read file");
                match parse_and_type(&contents) {
                    Err(e) => println!("{}", e),
                    Ok(ast) => println!("Typed AST: {:?}", ast),
                }
            }
        },
        _ => println!("Insufficient arguments"),
    }
}
