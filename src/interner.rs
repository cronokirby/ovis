use crate::identifiers::{Ident, IdentSource};

use std::collections::HashMap;

use std::fmt::{Display, Formatter, Result as FmtResult};

/// A mapping allowing us to retrieve a name for each identifier
///
/// This is useful to be able to have nice error messages using variable
/// names at later point, when working with the identifiers
#[derive(Clone, Debug)]
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

    /// Get the string corresponding to an identifier or display the identifier directly
    pub fn get_or_str(&self, ident: Ident) -> String {
        match self.get(ident) {
            None => format!("{}", ident),
            Some(x) => x.to_string(),
        }
    }
}

/// A struct allowing us to build up a bidirectional mapping between strings and identifiers.
///
/// The main utility of this class is in being able to traverse an AST and construct
/// a mapping between the strings present in the AST and unique identifiers.
pub struct Interner<'a> {
    dict: Dictionary,
    lookup: HashMap<String, Ident>,
    source: &'a mut IdentSource,
}

impl<'a> Interner<'a> {
    // Create a new interner, which will contain the built-in identifiers we
    // know of as well
    pub fn new(source: &'a mut IdentSource) -> Self {
        Interner {
            dict: Dictionary::new(),
            lookup: HashMap::new(),
            source,
        }
    }

    // Insert a new string, giving it a new identifier, and incrementing the state
    // of the identifier, and what not
    pub fn insert(&mut self, v: String) -> Ident {
        let key = self.source.next();
        self.dict.insert(key, v.clone());
        self.lookup.insert(v, key);
        key
    }

    // Get the identifier that a string should have, either looking
    // up what it is, or creating a new identifier for it if it doesn't have one
    pub fn ident(&mut self, v: String) -> Ident {
        match self.lookup.get(&v) {
            Some(x) => *x,
            None => self.insert(v),
        }
    }

    /// Access the dictionary created in this interner
    pub fn dictionary(self) -> Dictionary {
        self.dict
    }
}

/// A trait for things that can be displayed nicely in presence of a dictionary
///
/// This is useful for interned syntax trees, allowing us to pretty print them
/// using a reference to a dictionary.
pub trait DisplayWithDict {
    fn fmt(&self, f: &mut Formatter<'_>, dict: &Dictionary) -> FmtResult;
}

impl<T: Display> DisplayWithDict for T {
    fn fmt(&self, f: &mut Formatter<'_>, _dict: &Dictionary) -> FmtResult {
        write!(f, "{}", self)
    }
}

/// A struct bundling some type together with a dictionary.
///
/// The main utility in this struct is that it implements `Display` whenever
/// the type it wraps implements `DisplayWithDict`. Because of this, it makes
/// it easy to use those types in situations where we expect to be able to
/// use Display.
///
/// For example, `println!("{}", WithDict::new(ast, dict))` becomes possible.
pub struct WithDict<'a, T> {
    dict: &'a Dictionary,
    t: &'a T,
}

impl<'a, T> WithDict<'a, T> {
    /// Create a new wrapper from a reference to a type and dictionary.
    pub fn new(t: &'a T, dict: &'a Dictionary) -> Self {
        WithDict { t, dict }
    }
}

impl<'a, T: DisplayWithDict> Display for WithDict<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        self.t.fmt(f, self.dict)
    }
}

#[derive(Debug)]
pub struct OwnDict<T> {
    dict: Dictionary,
    t: T,
}

impl<T> OwnDict<T> {
    pub fn new(t: T, dict: Dictionary) -> Self {
        OwnDict { dict, t }
    }
}

impl<T: DisplayWithDict> Display for OwnDict<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        self.t.fmt(f, &self.dict)
    }
}
