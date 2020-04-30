use std::fs::File;
use std::str::FromStr;

use cranelift::codegen::binemit::NullTrapSink;
use cranelift::prelude::*;
use cranelift_faerie::{FaerieBackend, FaerieBuilder};
use cranelift_module::{Linkage, Module};
use target_lexicon::triple;

pub struct CodeGen {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    module: Module<FaerieBackend>,
}

impl CodeGen {
    pub fn new(name: &str) -> Self {
        if cfg!(windows) {
            unimplemented!();
        }
        let mut flag_builder = settings::builder();
        flag_builder.enable("is_pic").unwrap();
        let isa_builder = isa::lookup(triple!("x86_64-unknown-unknown-elf")).unwrap();
        let isa = isa_builder.finish(settings::Flags::new(flag_builder));

        let builder = FaerieBuilder::new(
            isa,
            name.to_owned(),
            cranelift_module::default_libcall_names(),
        )
        .unwrap();
        let module = Module::new(builder);
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            module,
        }
    }

    pub fn generate(&mut self) -> Result<(), String> {
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);
        let sig = self.module.make_signature();
        let callee = self
            .module
            .declare_function("ovis_hello_world", Linkage::Import, &sig)
            .map_err(|e| e.to_string())?;
        let local_callee = self.module.declare_func_in_func(callee, &mut builder.func);
        builder.ins().call(local_callee, &[]);
        builder.ins().return_(&[]);
        builder.finalize();
        let id = self
            .module
            .declare_function("main", Linkage::Export, &self.ctx.func.signature)
            .map_err(|e| e.to_string())?;
        self.module
            .define_function(id, &mut self.ctx, &mut NullTrapSink {})
            .map_err(|e| e.to_string())?;
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions();
        Ok(())
    }

    /// Consume self and write out an object file.
    pub fn finish(self) {
        let product = self.module.finish();
        let file = File::create(product.name()).expect("error opening file");
        product.write(file).expect("error writing to file");
    }
}
