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
struct Substitution {
    map: HashMap<TypeVar, Type>,
}

impl Substitution {
    /// The substitution where nothing happens
    fn empty() -> Self {
        Substitution {
            map: HashMap::new(),
        }
    }

    /// Add a new mapping to this substitution
    fn add(&mut self, var: TypeVar, typ: Type) {
        self.map.insert(var, typ);
    }

    fn get(&self, var: TypeVar) -> Option<&Type> {
        self.map.get(&var)
    }
}

fn hidden_lookup_or(
    subst: &Substitution,
    hiding: Option<&HashSet<TypeVar>>,
    var: TypeVar,
    default: Type,
) -> Type {
    hiding
        .and_then(|hidden| {
            if hidden.contains(&var) {
                Some(default.clone())
            } else {
                None
            }
        })
        .or_else(|| subst.get(var).cloned())
        .unwrap_or(default)
}

trait Substitutable {
    fn substitute(&mut self, subst: &Substitution, hiding: Option<&HashSet<TypeVar>>);
}

impl Substitutable for Ident {
    fn substitute(&mut self, subst: &Substitution, hiding: Option<&HashSet<TypeVar>>) {
        match hidden_lookup_or(subst, hiding, *self, Type::TypeVar(*self)) {
            Type::TypeVar(tv) => *self = tv,
            _ => {}
        }
    }
}

impl Substitutable for Type {
    fn substitute(&mut self, subst: &Substitution, hiding: Option<&HashSet<Var>>) {
        match self {
            Type::TypeVar(a) => *self = hidden_lookup_or(subst, hiding, *a, Type::TypeVar(*a)),
            Type::Function(t1, t2) => {
                t1.substitute(subst, hiding);
                t2.substitute(subst, hiding);
            }
            _ => {}
        }
    }
}

impl Substitutable for Scheme {
    fn substitute(&mut self, subst: &Substitution, hiding: Option<&HashSet<TypeVar>>) {
        let mut temp = HashSet::new();
        let new_hiding = match hiding {
            Some(h) => {
                for x in self.type_vars.intersection(h) {
                    temp.insert(*x);
                }
                &temp
            }
            None => &self.type_vars,
        };

        self.typ.substitute(subst, Some(new_hiding))
    }
}

impl Substitutable for Constraint {
    fn substitute(&mut self, subst: &Substitution, hiding: Option<&HashSet<TypeVar>>) {
        match self {
            Constraint::SameType(t1, t2) => {
                t1.substitute(subst, hiding);
                t2.substitute(subst, hiding);
            }
            Constraint::ExplicitInst(typ, scheme) => {
                typ.substitute(subst, hiding);
                scheme.substitute(subst, hiding);
            }
            Constraint::ImplicitInst(t1, vars, t2) => {
                t1.substitute(subst, hiding);
                t2.substitute(subst, hiding);
                let mut new_vars = HashSet::new();
                for v in vars.iter() {
                    let mut mv = *v;
                    mv.substitute(subst, hiding);
                    new_vars.insert(mv);
                }
                *vars = new_vars;
            }
        }
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
