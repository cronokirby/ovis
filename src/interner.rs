use std::collections::HashMap;
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
    fn new(map: HashMap<Ident, String>) -> Self {
        Dictionary { map }
    }

    /// Retreive the string connected to a given identifier, if it exists
    pub fn get(&self, ident: Ident) -> Option<&str> {
        // I wonder if we can avoid the map here
        self.map.get(&ident).map(|t| t.as_ref())
    }
}
