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

/// The identifier for the I64 known string
pub const IDENT_I64: Ident = Ident(0);

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
        let mut interner = Interner {
            dict: Dictionary::new(),
            lookup: HashMap::new(),
            next: Ident(0),
        };
        interner.insert("I64".to_string());
        interner
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
    fn get_or_insert(&mut self, v: String) -> Ident {
        match self.lookup.get(&v) {
            Some(x) => *x,
            None => self.insert(v),
        }
    }
}
