use crate::interner::DisplayWithDict;
use crate::parser::BinOp;
use crate::simplifier::{Scheme, AST};
use crate::{identifiers::Ident, interner::Dictionary};
use std::collections::HashMap;
use std::fmt;

/// Represents an instruction for our abstract machine.
///
/// These are all used to manipulate the graph-reduction machine.
#[derive(Clone, Debug)]
enum Instruction {
    /// Push an integer onto the stack
    PushInt(i64),
    /// Push a string onto the stack
    PushString(String),
    /// Push a global reference to some name onto the stack
    PushGlobal(Ident),
    /// Push the value N elements below onto the top of the stack
    Push(u64),
    /// Update the value N elements below
    Update(u64),
    /// Slide the stack down N elements
    Slide(u64),
    /// Pop the stack N elements
    Pop(u64),
    /// Apply a binary operation to the top two elements
    Binary(BinOp),
    /// Create a function application between the top two nodes
    MkApp,
    /// Evaluate the spine of a chain of evaluations
    Unwind,
    /// Move our focus to another part of the graph
    Eval,
    /// Allocate a placeholder for some node
    Alloc,
}

impl DisplayWithDict for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        match self {
            Instruction::PushInt(i) => write!(f, "int {}", i),
            Instruction::PushString(s) => write!(f, "string {:?}", s),
            Instruction::PushGlobal(g) => write!(f, "global {}", dict.get(*g).unwrap()),
            Instruction::Push(n) => write!(f, "push {}", n),
            Instruction::Update(n) => write!(f, "update {}", n),
            Instruction::Slide(n) => write!(f, "slide {}", n),
            Instruction::Pop(n) => write!(f, "pop {}", n),
            Instruction::Binary(op) => write!(f, "binary {}", op),
            Instruction::MkApp => write!(f, "mkapp"),
            Instruction::Unwind => write!(f, "unwind"),
            Instruction::Eval => write!(f, "eval"),
            Instruction::Alloc => write!(f, "alloc"),
        }
    }
}

pub struct GlobalInfo {
    name: Ident,
    num_args: u64,
    instructions: Vec<Instruction>,
}

impl DisplayWithDict for GlobalInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        writeln!(f, "{}({}):", dict.get(self.name).unwrap(), self.num_args)?;
        for i in &self.instructions {
            write!(f, "  ")?;
            i.fmt(f, dict)?;
            write!(f, "\n")?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
struct Pointer(u64);

impl fmt::Display for Pointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#X}", self.0)
    }
}

#[derive(Debug)]
struct Frame {
    instructions: Vec<Instruction>,
    stack: Vec<Pointer>,
}

#[derive(Clone, Debug)]
/// Represents the type of items on the heap.
enum HeapItem {
    /// An integer on the heap
    I64(i64),
    /// A string contained on the heap
    Strng(String),
    /// An indirection pointing to some other item on the heap
    Ind(Pointer),
    App(Pointer, Pointer),
    /// Global function information
    Global(u64, Vec<Instruction>),
}

/// Represents a heap where we can allocate scratch memory for nodes
///
/// This is completely un-garbage collected. Once we've added a node to the Heap,
/// we're not going to ever remove it.
#[derive(Debug)]
struct Heap(Vec<HeapItem>);

impl Heap {
    /// Create a new Heap.
    fn new() -> Self {
        Self(Vec::new())
    }

    /// Allocate a new item onto the Heap, returning its address
    fn alloc(&mut self, item: HeapItem) -> Pointer {
        self.0.push(item);
        Pointer(self.0.len() as u64 - 1)
    }

    fn set(&mut self, at: Pointer, item: HeapItem) {
        self.0[at.0 as usize] = item;
    }

    /// Retrieve a reference to the item at a certain address in the heap
    fn at(&self, p: Pointer) -> &HeapItem {
        &self.0[p.0 as usize]
    }

    /// Retrieve the integer at a certain address, panicing if not
    fn at_as_int(&self, p: Pointer) -> i64 {
        match self.at(p) {
            HeapItem::I64(i) => *i,
            item => panic!("UNTHINKABLE: expected I64 at {} found: {:?}", p, item),
        }
    }

    fn at_as_string(&self, p: Pointer) -> &String {
        match self.at(p) {
            HeapItem::Strng(s) => s,
            item => panic!("UNTHINKABLE: expected String at {} found: {:?}", p, item),
        }
    }

    fn at_app_right(&self, p: Pointer) -> Pointer {
        match self.at(p) {
            HeapItem::App(_, r) => *r,
            item => panic!(
                "UNTHINKABLE: expected application at {} found: {:?}",
                p, item
            ),
        }
    }
}

#[derive(Debug)]
struct Machine {
    instructions: Vec<Instruction>,
    stack: Vec<Pointer>,
    dump: Vec<Frame>,
    heap: Heap,
    globals: HashMap<Ident, Pointer>,
}

impl Machine {
    fn new(instructions: Vec<Instruction>) -> Self {
        Self {
            instructions,
            stack: Vec::new(),
            dump: Vec::new(),
            heap: Heap::new(),
            globals: HashMap::new(),
        }
    }

    fn add_global(&mut self, info: GlobalInfo) {
        let addr = self
            .heap
            .alloc(HeapItem::Global(info.num_args, info.instructions));
        self.globals.insert(info.name, addr);
    }

    fn pop(&mut self) -> Pointer {
        self.stack.pop().expect("UNTHINKABLE: Not enough stack")
    }

    fn push_int(&mut self, n: i64) {
        let a = self.heap.alloc(HeapItem::I64(n));
        self.stack.push(a);
    }

    fn push_string(&mut self, s: String) {
        let a = self.heap.alloc(HeapItem::Strng(s));
        self.stack.push(a);
    }

    fn push_global(&mut self, g: Ident) {
        let &a = self
            .globals
            .get(&g)
            .expect(&format!("UNTHINKABLE: Couldn't find global {}", g));
        self.stack.push(a);
    }

    fn binary(&mut self, op: BinOp) {
        let a1 = self.pop();
        let a2 = self.pop();
        match op {
            BinOp::Concat => {
                let s1 = self.heap.at_as_string(a1);
                let s2 = self.heap.at_as_string(a2);
                let mut res = String::new();
                res.push_str(s1);
                res.push_str(s2);
                self.push_string(res);
            }
            BinOp::Add => {
                let i1 = self.heap.at_as_int(a1);
                let i2 = self.heap.at_as_int(a2);
                self.push_int(i1 + i2);
            }
            BinOp::Sub => {
                let i1 = self.heap.at_as_int(a1);
                let i2 = self.heap.at_as_int(a2);
                self.push_int(i1 - i2);
            }
            BinOp::Mul => {
                let i1 = self.heap.at_as_int(a1);
                let i2 = self.heap.at_as_int(a2);
                self.push_int(i1 * i2);
            }
            BinOp::Div => {
                let i1 = self.heap.at_as_int(a1);
                let i2 = self.heap.at_as_int(a2);
                self.push_int(i1 * i2);
            }
        }
    }

    fn pop_n(&mut self, n: u64) {
        for _ in 0..n {
            self.stack.pop();
        }
    }

    fn push_n(&mut self, n: u64) {
        let item = self.stack[self.stack.len() - 1 - (n as usize)];
        self.stack.push(item);
    }

    fn slide(&mut self, n: u64) {
        let top = self.pop();
        self.pop_n(n);
        self.stack.push(top);
    }

    fn mkapp(&mut self) {
        let f = self.pop();
        let a = self.pop();
        let addr = self.heap.alloc(HeapItem::App(f, a));
        self.stack.push(addr)
    }

    fn update(&mut self, n: u64) {
        let a = self.pop();
        let item = self.stack[self.stack.len() - 1 - (n as usize)];
        self.heap.set(a, HeapItem::Ind(item));
    }

    fn alloc(&mut self) {
        let a = self.heap.alloc(HeapItem::Ind(Pointer(0)));
        self.stack.push(a);
    }

    fn eval(&mut self) {
        let a = self.stack[self.stack.len() - 1];
        let mut stack = vec![a];
        let mut instructions = vec![Instruction::Unwind];
        std::mem::swap(&mut self.instructions, &mut instructions);
        std::mem::swap(&mut self.stack, &mut stack);
        self.dump.push(Frame {
            stack,
            instructions,
        });
    }

    fn unwind(&mut self) {
        let a = self.stack[self.stack.len() - 1];
        match self.heap.at(a) {
            HeapItem::App(a1, _a2) => {
                self.stack.push(*a1);
                self.instructions.push(Instruction::Unwind);
            }
            HeapItem::Global(n, c) => {
                for i in 0..(*n as usize) {
                    let ind = self.stack.len() - 1 - i;
                    let app = self.stack[ind - 1];
                    self.stack[ind] = self.heap.at_app_right(app);
                }
                self.instructions = c.clone();
            }
            HeapItem::Ind(i) => {
                self.stack.pop();
                self.stack.push(*i);
                self.instructions.push(Instruction::Unwind);
            }
            HeapItem::I64(_) | HeapItem::Strng(_) => {
                if let Some(frame) = self.dump.pop() {
                    self.instructions = frame.instructions;
                    self.stack = frame.stack;
                } else {
                    self.instructions = Vec::new();
                    self.stack = Vec::new();
                }
                self.stack.push(a);
            }
        }
    }

    fn handle(&mut self, instr: Instruction) {
        match instr {
            Instruction::PushInt(n) => self.push_int(n),
            Instruction::PushString(s) => self.push_string(s),
            Instruction::PushGlobal(g) => self.push_global(g),
            Instruction::Binary(op) => self.binary(op),
            Instruction::Pop(n) => self.pop_n(n),
            Instruction::Push(n) => self.push_n(n),
            Instruction::Slide(n) => self.slide(n),
            Instruction::MkApp => self.mkapp(),
            Instruction::Update(n) => self.update(n),
            Instruction::Unwind => self.unwind(),
            Instruction::Eval => self.eval(),
            Instruction::Alloc => self.alloc(),
        }
    }

    fn execute(&mut self) {
        while let Some(instr) = self.instructions.pop() {
            self.handle(instr);
        }
    }

    fn top_value(&mut self) -> Option<Value> {
        let top = self.stack[self.stack.len() - 1];
        match self.heap.at(top) {
            HeapItem::I64(i) => Some(Value::I64(*i)),
            HeapItem::Strng(s) => Some(Value::Strng(s.clone())),
            _ => None,
        }
    }
}

/// Represents the kind of value that can result from interpretation
#[derive(Debug)]
pub enum Value {
    /// An integer value
    I64(i64),
    /// String value
    Strng(String),
}

pub fn interpret(globals: Vec<GlobalInfo>, entry: Ident) -> Option<Value> {
    let instructions = globals
        .iter()
        .find(|g| g.name == entry)
        .map(|g| g.instructions.clone())
        .expect("UNTHINKABLE: no such entry found");
    let mut machine = Machine::new(instructions);
    for g in globals {
        machine.add_global(g);
    }
    machine.execute();
    machine.top_value()
}

pub fn compile(ast: AST<Scheme>, main: Ident) -> Vec<GlobalInfo> {
    let g: GlobalInfo = GlobalInfo {
        name: main,
        num_args: 0,
        instructions: vec![Instruction::PushInt(42)],
    };
    vec![g]
}
