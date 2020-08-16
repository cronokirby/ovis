use crate::ast::{Definition, Expr, AST};
use std::collections::HashMap;
use std::hash::Hash;

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

    /// Retreive the string connected to a given identifier, if it exists
    pub fn get(&self, ident: Ident) -> Option<&str> {
        // I wonder if we can avoid the map here
        self.map.get(&ident).map(|t| t.as_ref())
    }
}

/// Represents an AST where all of the string based identifier have been interned
///
/// This means that they've been replaced with unique numeric identifiers, allowing
/// us to save a lot of space.
///
/// We also have a dictionary for the reverse mapping, in order to still be able
/// to present variable as strings afterwards.
#[derive(Debug)]
pub struct InternedAST {
    /// The dictionary mapping identifiers back to strings
    pub dict: Dictionary,
    /// The AST itself, now using identifiers instead of strings like after parsing
    pub ast: AST<Ident>,
}

/// Represents a bidirectional mapping
struct Interner {
    dict: Dictionary,
    lookup: HashMap<String, Ident>,
    next: Ident,
}

impl Interner {
    // Create a new interner, which will contain the built-in identifiers we
    // know of as well
    fn new() -> Self {
        Interner {
            dict: Dictionary::new(),
            lookup: HashMap::new(),
            next: Ident(0),
        }
    }

    // Insert a new string, giving it a new identifier, and incrementing the state
    // of the identifier, and what not
    fn insert(&mut self, v: String) -> Ident {
        let key = self.next;
        self.next = self.next.succ();
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

    fn ast(&mut self, ast: AST<String>) -> AST<Ident> {
        AST {
            definitions: self.definitions(ast.definitions),
        }
    }

    fn definitions(&mut self, definitions: Vec<Definition<String>>) -> Vec<Definition<Ident>> {
        definitions
            .into_iter()
            .map(|x| self.definition(x))
            .collect()
    }

    fn definition(&mut self, ast: Definition<String>) -> Definition<Ident> {
        match ast {
            Definition::Type(name, e) => Definition::Type(self.ident(name), e),
            Definition::Val(name, e) => Definition::Val(self.ident(name), self.expr(e)),
        }
    }

    fn expr(&mut self, ast: Expr<String>) -> Expr<Ident> {
        match ast {
            Expr::Lambda(name, e) => Expr::Lambda(self.ident(name), Box::new(self.expr(*e))),
            Expr::Let(definitions, e) => {
                Expr::Let(self.definitions(definitions), Box::new(self.expr(*e)))
            }
            Expr::Name(name) => Expr::Name(self.ident(name)),
            Expr::Binary(op, l, r) => {
                Expr::Binary(op, Box::new(self.expr(*l)), Box::new(self.expr(*r)))
            }
            Expr::Negate(e) => Expr::Negate(Box::new(self.expr(*e))),
            Expr::Apply(f, e) => Expr::Apply(Box::new(self.expr(*f)), Box::new(self.expr(*e))),
            Expr::NumberLitt(n) => Expr::NumberLitt(n),
            Expr::StringLitt(s) => Expr::StringLitt(s),
        }
    }
}

/// Intern an AST, by replacing all of the strings with unique identifiers
pub fn intern(ast: AST<String>) -> InternedAST {
    let mut interner = Interner::new();
    let ast = interner.ast(ast);
    InternedAST {
        ast,
        dict: interner.dict,
    }
}
