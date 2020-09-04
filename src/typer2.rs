use crate::ast::{SchemeExpr, TypeExpr};
use crate::interner::{Ident, IdentSource};
use std::collections::HashMap;

/// Represents a type we can assign to some expression
///
/// This happens to be completely isomorphic to the syntactic expressions of
/// the possible types an expression can have, hence why we reuse the AST struct.
type Type = TypeExpr<Ident>;

/// Represents a scheme, i.e. a type with explicitly quantified variables
///
/// Similarly to `Type`, this is isomorphic to the syntactic expression.
type Scheme = SchemeExpr<Ident>;

/// Represents an environment mapping names to schemes.
///
/// This environment supports scoping, where we can enter and exit scopes,
/// handling things like shadowing and having temporary bindings.
struct ScopedEnv {
    scopes: Vec<HashMap<Ident, Scheme>>,
}

impl ScopedEnv {
    /// Create a new scoped environment, containing nothing.
    ///
    /// This will also create a global scope to begin with.
    fn new() -> Self {
        ScopedEnv {
            scopes: vec![HashMap::new()],
        }
    }

    /// Extend the environment by mapping a name into a specific scheme
    fn extend(&mut self, name: Ident, scheme: Scheme) {
        // We throw an error if scopes becomes empty upon exiting a scope
        let last = self.scopes.last_mut().unwrap();
        last.insert(name, scheme);
    }

    /// Find the scheme associated with a certain identifier
    fn lookup(&self, name: Ident) -> Option<&Scheme> {
        for scope in self.scopes.iter().rev() {
            if let Some(scheme) = scope.get(&name) {
                return Some(scheme);
            }
        }
        None
    }

    /// Enter a new scope
    fn enter(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Exit the current scope
    ///
    /// This will panic if we try to exit the global scope
    fn exit(&mut self) {
        // We might as well check whether we'll end up in a bad state first,
        // so we can avoid popping needlessly
        if self.scopes.len() <= 1 {
            panic!("UNTHINKABLE: Tried to exit global scope!")
        }
        self.scopes.pop();
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn scoped_environment_works() {
        let scheme_a: Scheme = SchemeExpr {
            type_vars: Vec::new(),
            typ: TypeExpr::I64,
        };
        let scheme_b: Scheme = SchemeExpr {
            type_vars: Vec::new(),
            typ: TypeExpr::Strng,
        };
        let mut env = ScopedEnv::new();
        let mut source = IdentSource::new();
        let a = source.next();
        let b = source.next();

        env.extend(a, scheme_a.clone());
        assert_eq!(env.lookup(a), Some(&scheme_a));
        assert_eq!(env.lookup(b), None);
        env.extend(a, scheme_b.clone());
        assert_eq!(env.lookup(a), Some(&scheme_b));
        env.extend(b, scheme_b.clone());
        env.enter();
        env.extend(a, scheme_a.clone());
        assert_eq!(env.lookup(b), Some(&scheme_b));
        assert_eq!(env.lookup(a), Some(&scheme_a));
        env.exit();
        assert_eq!(env.lookup(a), Some(&scheme_b));
    }
}
