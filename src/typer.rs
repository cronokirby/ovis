use crate::identifiers::Ident;
use crate::simplifier::{Scheme, Type};
use std::collections::{HashMap, HashSet};

/// The type we use to represent type-level variables.
type TypeVar = Ident;

/// The type we use to represent variables
type Var = Ident;

/// Represents a kind of constraint we create when typing.
///
/// The idea is to have a constraint generation phase, and then
/// a final constraint gathering phase later.
enum Constraint {
    /// An assertion that two types must be equal
    SameType(Type, Type),
    /// The first type must be able to be seen as an instance of some scheme
    ExplicitInst(Type, Scheme),
    /// The first type should be an instance of the second, generalized over some type variables
    ImplicitInst(Type, HashSet<TypeVar>, Type),
}

/// Represents a substitution of type variables for concrete types
struct Substititon {
    map: HashMap<TypeVar, Type>,
}

impl Substititon {
    /// The substitution where nothing happens
    fn empty() -> Self {
        Substititon {
            map: HashMap::new(),
        }
    }

    /// Add a new mapping to this substitution
    fn add(&mut self, var: TypeVar, typ: Type) {
        self.map.insert(var, typ);
    }
}

/// A set of assumptions we have gathered so far about variables and their types
struct Assumptions(Vec<(Var, Type)>);

impl Assumptions {
    /// No assumptions whatsoever
    fn empty() -> Self {
        Assumptions(Vec::new())
    }

    /// Extend the assumptions with a new fact
    fn extend(&mut self, var: Var, typ: Type) {
        self.0.push((var, typ))
    }

    /// Collect the set of variables we have an assumption about
    fn vars(&self, buf: &mut HashSet<Var>) {
        for (v, _) in &self.0 {
            buf.insert(*v);
        }
    }
}
