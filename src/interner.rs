use crate::ast::{Definition, Expr, AST};
use std::collections::HashMap;
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

    fn get(&self, ident: Ident) -> Option<&str> {
        // I wonder if we can avoid the map here
        self.map.get(&ident).map(|t| t.as_ref())
    }

    /// Replace all instances of identifiers with the corresponding strings
    pub fn unintern<T>(&self, ast: AST<Ident, T>) -> AST<String, T> {
        ast.replace_idents(|i| self.get(i).unwrap().to_string())
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
}

/// Intern an AST, by replacing all of the strings with unique identifiers
pub fn intern(ast: AST<String>) -> InternedAST {
    let mut interner = Interner::new();
    let ast = ast.replace_idents(|i| interner.ident(i));
    InternedAST {
        ast,
        dict: interner.dict,
    }
}
