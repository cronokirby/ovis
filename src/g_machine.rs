use crate::identifiers::Ident;
use crate::parser::BinOp;
use std::collections::HashMap;

/// Represents an instruction for our abstract machine.
///
/// These are all used to manipulate the graph-reduction machine.
#[derive(Debug)]
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
    /// Return from a specific focus
    UnwindReturn,
    /// Move our focus to another part of the graph
    Eval,
    /// Allocate a placeholder for some node
    Alloc,
}

#[derive(Clone, Debug)]
struct Pointer(u64);

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

    /// Retrieve a reference to the item at a certain address in the heap
    fn at(&self, p: Pointer) -> &HeapItem {
        &self.0[p.0 as usize]
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
}
