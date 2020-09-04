use crate::parser;

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use std::fmt::{Display, Formatter, Result as FmtResult};

/// A name we can use for an identifier.
///
/// This idea is that anywhere we could have used a string based identifier,
/// we can replace that exact identifier with this instead, saving on space.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Ident(u64);

impl Ident {
    // Return the next identifier after this one
    fn succ(self) -> Self {
        Ident(self.0 + 1)
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{{{}}}", self.0)
    }
}

/// A struct providing us with an easy source of new identifiers
#[derive(Clone)]
pub struct IdentSource {
    next: Ident,
}

impl IdentSource {
    /// Create a new source of identifiers
    pub fn new() -> Self {
        IdentSource { next: Ident(0) }
    }

    /// Get the next identifier from this source
    pub fn next(&mut self) -> Ident {
        let ret = self.next;
        self.next = self.next.succ();
        ret
    }
}

/// A mapping allowing us to retrieve a name for each identifier
///
/// This is useful to be able to have nice error messages using variable
/// names at later point, when working with the identifiers
#[derive(Debug)]
pub struct Dictionary {
    // The mapping we have from each identifier to the string corresponding to it
    map: HashMap<Ident, String>,
}

impl Dictionary {
    fn new() -> Self {
        Dictionary {
            map: HashMap::new(),
        }
    }

    fn insert(&mut self, ident: Ident, name: String) {
        self.map.insert(ident, name);
    }

    /// Try and get the string corresponding to an identifier
    pub fn get(&self, ident: Ident) -> Option<&str> {
        // I wonder if we can avoid the map here
        self.map.get(&ident).map(|t| t.as_ref())
    }
}

/// Represents a bidirectional mapping
struct Interner {
    dict: Dictionary,
    lookup: HashMap<String, Ident>,
    source: IdentSource,
}

impl Interner {
    // Create a new interner, which will contain the built-in identifiers we
    // know of as well
    fn new() -> Self {
        Interner {
            dict: Dictionary::new(),
            lookup: HashMap::new(),
            source: IdentSource::new(),
        }
    }

    // Insert a new string, giving it a new identifier, and incrementing the state
    // of the identifier, and what not
    fn insert(&mut self, v: String) -> Ident {
        let key = self.source.next();
        self.dict.insert(key, v.clone());
        self.lookup.insert(v, key);
        key
    }

    // Get the identifier that a string should have, either looking
    // up what it is, or creating a new identifier for it if it doesn't have one
    fn ident(&mut self, v: String) -> Ident {
        match self.lookup.get(&v) {
            Some(x) => *x,
            None => self.insert(v),
        }
    }
}

/// We simply reuse the binary operations provided by the parser
pub type BinOp = parser::BinOp;

/// Represents a single expression in our language
#[derive(Debug, PartialEq)]
pub enum Expr<T> {
    /// A lambda abstraction / function litteral
    Lambda(Ident, T, Box<Expr<T>>),
    /// A let expression, where we have a sequence of definitions bound before
    /// an expression.
    Let(Vec<Definition<T>>, Box<Expr<T>>),
    /// A reference to a variable name or definition
    Name(Ident),
    /// A reference to a positive number
    NumberLitt(i64),
    /// A reference to a string litteral
    StringLitt(String),
    /// A binary operation between expressions
    Binary(BinOp, Box<Expr<T>>, Box<Expr<T>>),
    /// Unary negation of an expression
    Negate(Box<Expr<T>>),
    /// Represents the application of one function to an argument
    Apply(Box<Expr<T>>, Box<Expr<T>>),
}
/// Represents a type, formed through primitive types, or composition of other types
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A function A -> B
    Function(Box<Type>, Box<Type>),
    /// The primitive integer type
    I64,
    /// The primitive string type
    Strng,
    /// A reference to some identifier, e.g. `a`
    ///
    /// Of course, that type variable has to be quantified in some scope for this
    /// to make any sense.
    TypeVar(Ident),
}

/// Represents an expression of a scheme, i.e. type with quantified polymorphic vars.
///
/// This is used to represent some declaration of a scheme, e.g. `{a} => a -> a`.
#[derive(Clone, Debug, PartialEq)]
pub struct Scheme {
    /// The polymorphic variables being quantified over
    ///
    /// They also have whatever kind of identifier we use for variable names.
    pub type_vars: HashSet<Ident>,
    /// The expression being quantified over
    pub typ: Type,
}

/// Represents a definition or annotation
///
/// A definition assigns a name to an expression, and a type annotation assigns
/// an explicit type to a name. Type annotations are optional in our language.
#[derive(Debug, PartialEq)]
pub enum Definition<T> {
    /// Represents an annotation of a name with a given type
    Type(Ident, Scheme),
    /// Represents the definition of name, with its corresponding expression
    Val(Ident, T, Expr<T>),
}

/// Represents a program in our language.
///
/// This is parametrized over the type of identifiers
///
/// A program is just a sequence of value or type annotations
#[derive(Debug, PartialEq)]
pub struct AST<T = ()> {
    pub definitions: Vec<Definition<T>>,
}

struct Simplifier {
    interner: Interner,
}

impl Simplifier {
    fn new() -> Self {
        Simplifier {
            interner: Interner::new(),
        }
    }

    fn type_expr(&mut self, e: parser::TypeExpr) -> Type {
        match e {
            parser::TypeExpr::Function(t1, t2) => {
                Type::Function(Box::new(self.type_expr(*t1)), Box::new(self.type_expr(*t2)))
            }
            parser::TypeExpr::TypeVar(n) => Type::TypeVar(self.interner.ident(n)),
            parser::TypeExpr::I64 => Type::I64,
            parser::TypeExpr::Strng => Type::Strng,
        }
    }

    fn scheme(&mut self, e: parser::SchemeExpr) -> Scheme {
        let mut type_vars = HashSet::new();
        for name in e.type_vars {
            type_vars.insert(self.interner.ident(name));
        }
        let typ = self.type_expr(e.typ);
        Scheme { type_vars, typ }
    }

    fn expr(&mut self, e: parser::Expr) -> Expr<()> {
        match e {
            parser::Expr::Name(n) => Expr::Name(self.interner.ident(n)),
            parser::Expr::StringLitt(s) => Expr::StringLitt(s),
            parser::Expr::NumberLitt(n) => Expr::NumberLitt(n),
            parser::Expr::Let(defs, body) => {
                Expr::Let(self.definitions(defs), Box::new(self.expr(*body)))
            }
            parser::Expr::Negate(body) => Expr::Negate(Box::new(self.expr(*body))),
            parser::Expr::Binary(op, e1, e2) => {
                Expr::Binary(op, Box::new(self.expr(*e1)), Box::new(self.expr(*e2)))
            }
            parser::Expr::Apply(e1, e2) => {
                Expr::Apply(Box::new(self.expr(*e1)), Box::new(self.expr(*e2)))
            }
            parser::Expr::Lambda(bindings, body) => {
                let mut seed = self.expr(*body);
                for name in bindings.into_iter().rev() {
                    seed = Expr::Lambda(self.interner.ident(name), (), Box::new(seed))
                }
                seed
            }
        }
    }

    fn definition(&mut self, def: parser::Definition) -> Definition<()> {
        match def {
            parser::Definition::Type(name, scheme) => {
                Definition::Type(self.interner.ident(name), self.scheme(scheme))
            }
            parser::Definition::Val(name, expr) => {
                Definition::Val(self.interner.ident(name), (), self.expr(expr))
            }
        }
    }

    fn definitions(&mut self, defs: Vec<parser::Definition>) -> Vec<Definition<()>> {
        defs.into_iter().map(|x| self.definition(x)).collect()
    }

    fn ast(&mut self, parsed: parser::AST) -> AST {
        AST {
            definitions: self.definitions(parsed.definitions),
        }
    }
}
/// Simplify a parsed AST to a representation of an equivalent program.
///
/// We want to simplify to remove so-called "Syntax Sugar", allowing us to
/// work more directly with certain constructs
pub fn simplify(parsed: parser::AST) -> (AST, Dictionary) {
    let mut simplifier = Simplifier::new();
    let ast = simplifier.ast(parsed);
    (ast, simplifier.interner.dict)
}
