mod codegen;
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
                let parsed = parser::parse(&contents);
                match parsed {
                    Ok(ast) => println!("{:?}", ast),
                    Err(e) => println!("Error: {}", e),
                }
            }
        },
        _ => println!("Insufficient arguments"),
    }
}
