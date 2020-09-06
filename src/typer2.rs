use crate::simplifier::{Ident, IdentSource, Scheme, Type};
use std::collections::{HashMap, HashSet};

/// A synonym for identifiers belonging to type variables
type TypeVar = Ident;

/// A synonym for identifiers belonging to variables
type Var = Ident;

/// A substitution maps type variables to fully instantiated types.
///
/// The idea is that our end goal is to be able to replace all of the type variables
/// we've gathered using a concrete substitution scheme, in a way that satisfies
/// all the constraints on what types are possible through observing how different variables
/// are used throughout the program.
struct Substitution(HashMap<TypeVar, Type>);

impl Substitution {
    /// A substition that replaces no type variables
    fn empty() -> Self {
        Substitution(HashMap::new())
    }

    /// Add a new binding to this substitution
    fn with(&mut self, t_var: TypeVar, typ: Type) {
        self.0.insert(t_var, typ);
    }

    /// Try and find the type corresponding to a given variable, if any
    fn get(&self, t_var: TypeVar) -> Option<&Type> {
        self.0.get(&t_var)
    }

    /// Clone this substitution to another, without including a set of type variables
    ///
    /// This is useful when editing a substitution to not include certain bound variables.
    fn clone_without(&self, vars: &HashSet<TypeVar>) -> Self {
        let mut ret = Substitution::empty();
        for (k, v) in &self.0 {
            if !vars.contains(k) {
                ret.with(*k, v.clone());
            }
        }
        ret
    }
}

/// Represents some kind of type in which we can apply substitutions
trait Substitutable {
    /// Apply a given substitution to this type
    fn subst(&mut self, map: &Substitution);

    /// Calculate the free type variables present in this type
    fn free_t_vars(&self, buf: &mut HashSet<TypeVar>);
}

impl Substitutable for Type {
    fn subst(&mut self, map: &Substitution) {
        match self {
            Type::Function(l, r) => {
                l.subst(map);
                r.subst(map);
            }
            Type::TypeVar(n) => {
                if let Some(t) = map.get(*n) {
                    *self = t.clone();
                }
            }
            Type::I64 | Type::Strng => {}
        }
    }

    fn free_t_vars(&self, buf: &mut HashSet<TypeVar>) {
        match self {
            Type::Function(l, r) => {
                l.free_t_vars(buf);
                r.free_t_vars(buf);
            }
            Type::TypeVar(n) => {
                buf.insert(*n);
            }
            Type::I64 | Type::Strng => {}
        }
    }
}

impl Substitutable for Scheme {
    fn subst(&mut self, map: &Substitution) {
        let no_bound = map.clone_without(&self.type_vars);
        self.typ.subst(&no_bound);
    }

    fn free_t_vars(&self, buf: &mut HashSet<TypeVar>) {
        self.typ.free_t_vars(buf);
        for v in &self.type_vars {
            buf.remove(v);
        }
    }
}

/// Represents an environment mapping names to schemes.
///
/// This environment supports scoping, where we can enter and exit scopes,
/// handling things like shadowing and having temporary bindings.
struct ScopedEnv {
    scopes: Vec<HashMap<Var, Scheme>>,
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
    fn extend(&mut self, name: Var, scheme: Scheme) {
        // We throw an error if scopes becomes empty upon exiting a scope
        let last = self.scopes.last_mut().unwrap();
        last.insert(name, scheme);
    }

    /// Find the scheme associated with a certain identifier
    fn lookup(&self, name: Var) -> Option<&Scheme> {
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

impl Substitutable for ScopedEnv {
    fn subst(&mut self, map: &Substitution) {
        for scope in &mut self.scopes {
            for typ in scope.values_mut() {
                typ.subst(map);
            }
        }
    }

    fn free_t_vars(&self, buf: &mut HashSet<TypeVar>) {
        for scope in &self.scopes {
            for typ in scope.values() {
                typ.free_t_vars(buf);
            }
        }
    }
}

/// A constraint represents come kind of unfication that we know needs to happen.
///
/// The idea is to gather a bunch of constraints, usually between variables and
/// concrete types, and then solve them later
type Constraint = (Type, Type);

/// The constrainer's job is to traverse the AST and gather constraints.
///
/// Constraints will look at the usage of certain types in order to tie together
/// free type variables with concrete types that they're used as. The idea is that
/// it's much easier to gather all this information over the whole tree, and then
/// try and solve it with a concrete substitution with schemes later.
struct Constrainer {
    /// This gives us access to an environment mapping variables to schemes
    env: ScopedEnv,
    /// A collection of constraints we've managed to gather so far
    constraints: Vec<Constraint>,
    /// This gives us the next fresh type variable to use
    source: IdentSource,
}

impl Constrainer {
    /// Declare that two different types must have a unification
    fn unify(&mut self, t1: Type, t2: Type) {
        self.constraints.push((t1, t2));
    }

    fn fresh_t_var(&mut self) -> TypeVar {
        self.source.next()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn scoped_environment_works() {
        let scheme_a: Scheme = Scheme {
            type_vars: HashSet::new(),
            typ: Type::I64,
        };
        let scheme_b: Scheme = Scheme {
            type_vars: HashSet::new(),
            typ: Type::Strng,
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
