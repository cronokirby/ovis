mod ast;
mod interner;
mod lexer;
mod parser;
mod typer;

use std::error::Error;
use std::fmt;
use std::fs;

#[derive(Debug)]
enum CompileError {
    /// We couldn't read a file while trying to compile it
    CouldntRead(String),
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
            CompileError::CouldntRead(path) => writeln!(f, "Failed to read file: {}", path),
            CompileError::LexError(errors) => {
                writeln!(f, "Errors encountered during Lexing:")?;
                for e in errors {
                    writeln!(f, "{}", e)?;
                }
                Ok(())
            }
            CompileError::ParseError(e) => writeln!(f, "Parse Error: {}", e),
            CompileError::TypeError(e) => writeln!(f, "Type Error: {}", e),
        }
    }
}

impl Error for CompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            CompileError::CouldntRead(_) => None,
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

fn parse_and_type(path: &str) -> Result<ast::AST<interner::Ident, typer::Type>, CompileError> {
    let contents =
        fs::read_to_string(path).map_err(|_| CompileError::CouldntRead(path.to_owned()))?;
    let tokens = lexer::lex(&contents)?;
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
            Some(path) => match parse_and_type(path) {
                Err(e) => println!("{}", e),
                Ok(ast) => println!("Typed AST: {:?}", ast),
            },
        },
        _ => println!("Insufficient arguments"),
    }
}
