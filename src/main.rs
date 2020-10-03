mod identifiers;
mod interner;
mod lexer;
mod parser;
mod simplifier;

use interner::WithDict;
use std::convert::TryFrom;
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
        }
    }
}

impl<'a> Error for CompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            CompileError::CouldntRead(_) => None,
            CompileError::LexError(_) => None,
            CompileError::ParseError(e) => Some(e),
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

#[derive(Debug, PartialEq, PartialOrd)]
/// Represents the stage up to which the user would like us to go
enum Stage {
    /// The user wants us to stop after lexing
    Lex,
    /// The user wants us to stop after parsing (and thus lexing)
    Parse,
    /// The user wants us to stop after simplifying the parse tree (and thus parsing)
    Simplify,
}

impl TryFrom<&str> for Stage {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "lex" => Ok(Stage::Lex),
            "parse" => Ok(Stage::Parse),
            "simplify" => Ok(Stage::Simplify),
            _ => Err(()),
        }
    }
}

/// Represents the type of arguments provided to us
struct Args {
    /// The stage we need to go to
    stage: Stage,
    /// The path for the file we're operating on
    path: String,
}

impl TryFrom<&[String]> for Args {
    type Error = ();

    fn try_from(args: &[String]) -> Result<Self, Self::Error> {
        if args.len() < 3 {
            Err(())
        } else {
            let stage = Stage::try_from(args[1].as_ref())?;
            let path = args[2].to_string();
            Ok(Args { stage, path })
        }
    }
}

fn real_main(args: Args) -> Result<(), CompileError> {
    let mut source = identifiers::IdentSource::new();

    let contents =
        fs::read_to_string(&args.path).map_err(|_| CompileError::CouldntRead(args.path.clone()))?;
    let tokens = lexer::lex(&contents)?;
    if args.stage <= Stage::Lex {
        println!("Lexed:\n");
        for t in tokens {
            print!("{}  ", t);
        }
        println!("");
        return Ok(());
    }
    let ast = parser::parse(&tokens)?;
    if args.stage <= Stage::Parse {
        println!("Parsed:\n\n{}", ast);
        return Ok(());
    }
    let (simplified, dict) = simplifier::simplify(ast, &mut source);
    if args.stage <= Stage::Simplify {
        println!("Simplified:\n\n{}", WithDict::new(&simplified, &dict));
        return Ok(());
    }
    Ok(())
}

fn main() {
    let arg_strings: Vec<String> = std::env::args().collect();
    match Args::try_from(arg_strings.as_ref()) {
        Err(_) => println!("Insufficient Arguments"),
        Ok(args) => match real_main(args) {
            Err(e) => println!("{}", e),
            Ok(_) => {}
        },
    }
}
