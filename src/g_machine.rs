use crate::identifiers::Ident;
use crate::parser::BinOp;

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
