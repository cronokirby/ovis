/// Represents a fully evaluated Type for some expression or identifier
///
/// We'll use this as the type to fill in our typed AST later
#[derive(Clone, Debug, PartialEq)]
enum Type {
    /// The primitive integer type
    I64,
    /// The primitive string type
    String,
    /// A function type between two other types
    Function(Box<Type>, Box<Type>),
}
