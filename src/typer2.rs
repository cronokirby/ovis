use crate::simplifier::{Definition, Expr, Ident, IdentSource, Scheme, Type, WithDict, AST};
use std::collections::{HashMap, HashSet};
use std::fmt;

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

    /// Generalize a type by closing over all the variables that are not in this environment
    fn generalize(&self, typ: Type) -> Scheme {
        let mut type_vars = HashSet::new();
        typ.free_t_vars(&mut type_vars);
        let mut scoped_vars = HashSet::new();
        self.free_t_vars(&mut scoped_vars);
        for v in scoped_vars {
            type_vars.remove(&v);
        }
        Scheme { type_vars, typ }
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

/// Represents some kind of error that can occur during type-checking
pub enum TypeError {
    /// An identifier being referenced has not been defined before
    UndefinedName(Ident),
}

impl<'a> fmt::Display for WithDict<'a, TypeError> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.view {
            TypeError::UndefinedName(n) => write!(
                f,
                "Identifier `{}` is undefined",
                self.dict.get(*n).unwrap()
            ),
        }
    }
}

pub type TypeResult<T> = Result<T, TypeError>;

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

    /// Generate a fresh type variable
    fn fresh_t_var(&mut self) -> Type {
        Type::TypeVar(self.source.next())
    }

    /// Instantiate some scheme, replacing all polymorphic variables with concrete ones
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mut subst = Substitution::empty();
        for v in &scheme.type_vars {
            subst.with(*v, self.fresh_t_var())
        }
        let mut typ = scheme.typ.clone();
        typ.subst(&subst);
        typ
    }

    fn lookup(&mut self, var: Var) -> TypeResult<Type> {
        let scheme = self
            .env
            .lookup(var)
            .ok_or(TypeError::UndefinedName(var))?
            .clone();
        Ok(self.instantiate(&scheme))
    }

    fn infer_expr(&mut self, expr: Expr) -> TypeResult<Type> {
        match expr {
            Expr::NumberLitt(_) => Ok(Type::I64),
            Expr::StringLitt(_) => Ok(Type::Strng),
            Expr::Name(n) => self.lookup(n),
            Expr::Negate(e) => {
                let te = self.infer_expr(*e)?;
                let tv = self.fresh_t_var();
                // We need whatever this operation looks like to conform with I64 -> I64
                let expected = Type::Function(Box::new(Type::I64), Box::new(Type::I64));
                let inferred = Type::Function(Box::new(te), Box::new(tv.clone()));
                self.unify(expected, inferred);
                Ok(tv)
            }
            Expr::Binary(_, l, r) => {
                let tl = self.infer_expr(*l)?;
                let tr = self.infer_expr(*r)?;
                let tv = self.fresh_t_var();
                // Whatever the shape of things are, we need it to conform with I64 -> I64 -> I64
                // All of our operations are of this type, for now
                let expected = Type::Function(
                    Box::new(Type::I64),
                    Box::new(Type::Function(Box::new(Type::I64), Box::new(Type::I64))),
                );
                let inferred = Type::Function(
                    Box::new(tl),
                    Box::new(Type::Function(Box::new(tr), Box::new(tv.clone()))),
                );
                self.unify(expected, inferred);
                Ok(tv)
            }
            Expr::Apply(f, e) => {
                let tf = self.infer_expr(*f)?;
                let te = self.infer_expr(*e)?;
                let tv = self.fresh_t_var();
                self.unify(tf, Type::Function(Box::new(te), Box::new(tv.clone())));
                Ok(tv)
            }
            Expr::Let(defs, e) => {
                self.env.enter();
                for d in defs {
                    self.infer_definition(d)?;
                }
                let te = self.infer_expr(*e)?;
                self.env.exit();
                Ok(te)
            }
            Expr::Lambda(n, _, e) => {
                let tv = self.fresh_t_var();
                self.env.enter();
                let scheme = Scheme {
                    type_vars: HashSet::new(),
                    typ: tv.clone(),
                };
                self.env.extend(n, scheme);
                let t = self.infer_expr(*e)?;
                self.env.exit();
                Ok(Type::Function(Box::new(tv), Box::new(t)))
            }
        }
    }

    fn infer_definition(&mut self, def: Definition) -> TypeResult<()> {
        match def {
            // TODO: Handle declared types
            Definition::Type(_, _) => Ok(()),
            Definition::Val(n, _, e) => {
                let t = self.infer_expr(e)?;
                let scheme = self.env.generalize(t);
                self.env.extend(n, scheme);
                Ok(())
            }
        }
    }

    fn infer(&mut self, ast: AST) -> TypeResult<()> {
        for def in ast.definitions {
            self.infer_definition(def)?;
        }
        Ok(())
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
