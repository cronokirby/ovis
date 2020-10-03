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
