mod codegen;

fn main() {
    let mut generator = codegen::CodeGen::new("gen.o");
    generator.generate().unwrap();
    generator.finish();
}
