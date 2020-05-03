mod codegen;
mod lexer;
mod parser;

use std::fs;

fn generate() {
    let mut generator = codegen::CodeGen::new("gen.o");
    generator.generate().unwrap();
    generator.finish();
}

fn main() {
    let all_args: Vec<String> = std::env::args().collect();
    match all_args.get(1).map(String::as_str) {
        Some("generate") => generate(),
        Some("parse") => match all_args.get(2) {
            None => println!("Insufficient arguments"),
            Some(path) => {
                let contents = fs::read_to_string(path).expect("Couldn't read file");
                match lexer::lex(&contents) {
                    Err(errors) => {
                        println!("Errors encountered during Lexing:");
                        for e in errors {
                            println!("{}", e);
                        }
                    }
                    Ok(tokens) => match parser::parse(&tokens) {
                        Err(e) => println!("Parse Error: {}", e),
                        Ok(ast) => println!("{:?}", ast),
                    },
                }
            }
        },
        _ => println!("Insufficient arguments"),
    }
}
