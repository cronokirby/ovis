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
#[derive(Debug)]
pub enum TypeError {
    /// An identifier being referenced has not been defined before
    UndefinedName(Ident),
    /// A type contains a type variable, so unifying that variable with that type
    /// would require the construction of an infinite type.
    InfiniteType(TypeVar, Type),
    /// Two types could not be unified
    UnificationMismatch(Type, Type),
}

impl<'a> fmt::Display for WithDict<'a, TypeError> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.view {
            TypeError::UndefinedName(n) => {
                write!(f, "Identifier `{}` is undefined", self.dict.get_or_str(*n))
            }
            TypeError::InfiniteType(v, t) => write!(
                f,
                "Tried to unify infinite type: {} ~ {}",
                self.dict.get_or_str(*v),
                self.with_view(t)
            ),
            TypeError::UnificationMismatch(t1, t2) => write!(
                f,
                "Failed to unify: {} ~ {}",
                self.with_view(t1),
                self.with_view(t2)
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
    fn new() -> Self {
        let env = ScopedEnv::new();
        let constraints = Vec::new();
        let source = IdentSource::odd();
        Constrainer {
            env,
            constraints,
            source,
        }
    }

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

    fn infer_expr(&mut self, expr: Expr) -> TypeResult<(Type, Expr<Scheme>)> {
        match expr {
            Expr::NumberLitt(n) => Ok((Type::I64, Expr::NumberLitt(n))),
            Expr::StringLitt(s) => Ok((Type::Strng, Expr::StringLitt(s))),
            Expr::Name(n) => Ok((self.lookup(n)?, Expr::Name(n))),
            Expr::Negate(e) => {
                let (te, re) = self.infer_expr(*e)?;
                let tv = self.fresh_t_var();
                // We need whatever this operation looks like to conform with I64 -> I64
                let expected = Type::Function(Box::new(Type::I64), Box::new(Type::I64));
                let inferred = Type::Function(Box::new(te), Box::new(tv.clone()));
                self.unify(expected, inferred);
                Ok((tv, Expr::Negate(Box::new(re))))
            }
            Expr::Binary(op, l, r) => {
                let (tl, rl) = self.infer_expr(*l)?;
                let (tr, rr) = self.infer_expr(*r)?;
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
                Ok((tv, Expr::Binary(op, Box::new(rl), Box::new(rr))))
            }
            Expr::Apply(f, e) => {
                let (tf, rf) = self.infer_expr(*f)?;
                let (te, re) = self.infer_expr(*e)?;
                let tv = self.fresh_t_var();
                self.unify(tf, Type::Function(Box::new(te), Box::new(tv.clone())));
                Ok((tv, Expr::Apply(Box::new(rf), Box::new(re))))
            }
            Expr::Let(defs, e) => {
                self.env.enter();
                let mut new_defs: Vec<Definition<Scheme>> = Vec::new();
                for d in defs {
                    if let Some(d) = self.infer_definition(d)? {
                        new_defs.push(d);
                    }
                }
                let (te, re) = self.infer_expr(*e)?;
                self.env.exit();
                Ok((te, Expr::Let(new_defs, Box::new(re))))
            }
            Expr::Lambda(n, _, e) => {
                let tv = self.fresh_t_var();
                self.env.enter();
                let scheme = Scheme::over(tv.clone());
                self.env.extend(n, scheme.clone());
                let (te, re) = self.infer_expr(*e)?;
                self.env.exit();
                Ok((
                    Type::Function(Box::new(tv), Box::new(te)),
                    Expr::Lambda(n, scheme, Box::new(re)),
                ))
            }
        }
    }

    fn infer_definition(&mut self, def: Definition) -> TypeResult<Option<Definition<Scheme>>> {
        match def {
            // TODO: Handle declared types
            Definition::Type(_, _) => Ok(None),
            Definition::Val(n, _, e) => {
                let (te, re) = self.infer_expr(e)?;
                let scheme = self.env.generalize(te);
                self.env.extend(n, scheme.clone());
                Ok(Some(Definition::Val(n, scheme, re)))
            }
        }
    }

    fn infer(&mut self, ast: AST) -> TypeResult<AST<Scheme>> {
        let mut new_defs = Vec::new();
        for def in ast.definitions {
            if let Some(d) = self.infer_definition(def)? {
                new_defs.push(d);
            }
        }
        Ok(AST {
            definitions: new_defs,
        })
    }
}

/// The solver is responsible for finding a substitution that solves all of our constraints
struct Solver {
    /// The current substitution we've managed to construct
    subst: Substitution,
}

impl Solver {
    fn new() -> Self {
        Solver {
            subst: Substitution::empty(),
        }
    }

    /// Try and bind a variable to a given type, returning the substitution making this work
    ///
    /// This will error out of the type features the type variable, in which case only an infinite
    /// type would solve that constraint.
    fn bind(&mut self, var: TypeVar, typ: Type) -> TypeResult<()> {
        if typ == Type::TypeVar(var) {
            Ok(())
        } else {
            let mut ftvs = HashSet::new();
            typ.free_t_vars(&mut ftvs);
            if ftvs.contains(&var) {
                Err(TypeError::InfiniteType(var, typ))
            } else {
                self.subst.with(var, typ);
                Ok(())
            }
        }
    }

    /// Try and unify two different types
    fn unify(&mut self, t1: Type, t2: Type) -> TypeResult<()> {
        match (t1, t2) {
            (t1, t2) if t1 == t2 => Ok(()),
            (Type::TypeVar(v), t) => self.bind(v, t),
            (t, Type::TypeVar(v)) => self.bind(v, t),
            (Type::Function(l1, r1), Type::Function(l2, r2)) => {
                self.unify(*l1, *l2)?;
                self.unify(*r1, *r2)
            }
            (t1, t2) => Err(TypeError::UnificationMismatch(t1, t2)),
        }
    }

    /// Try and solve a collection of constraints
    fn solve(&mut self, constraints: Vec<Constraint>) -> TypeResult<()> {
        for (mut t1, mut t2) in constraints {
            t1.subst(&self.subst);
            t2.subst(&self.subst);
            self.unify(t1, t2)?;
        }
        Ok(())
    }
}

fn substitute_ast(subst: &Substitution, ast: AST<Scheme>) -> AST<Scheme> {
    fn substitute_expr(subst: &Substitution, expr: Expr<Scheme>) -> Expr<Scheme> {
        match expr {
            Expr::Lambda(n, mut t, e) => {
                t.subst(subst);
                Expr::Lambda(n, t, e)
            }
            Expr::Let(defs, e) => {
                let mut definitions = Vec::new();
                for d in defs {
                    definitions.push(substitute_definition(subst, d));
                }
                Expr::Let(definitions, e)
            }
            e => e,
        }
    }

    fn substitute_definition(
        subst: &Substitution,
        definition: Definition<Scheme>,
    ) -> Definition<Scheme> {
        match definition {
            Definition::Val(n, mut t, e) => {
                t.subst(subst);
                Definition::Val(n, t, e)
            }
            // By the time we get here, the type definitions have already been removed
            Definition::Type(_, _) => unreachable!(),
        }
    }

    let mut definitions = Vec::new();
    for d in ast.definitions {
        definitions.push(substitute_definition(subst, d));
    }
    AST { definitions }
}

/// Try and assign types to a syntax tree
///
/// Of course, this can potentially fail, in which case we'll return an error describing
/// the kind of error that occurred.
pub fn typer(untyped: AST) -> TypeResult<AST<Scheme>> {
    let mut constrainer = Constrainer::new();
    let partially_typed = constrainer.infer(untyped)?;
    let mut solver = Solver::new();
    solver.solve(constrainer.constraints)?;
    Ok(substitute_ast(&solver.subst, partially_typed))
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
        let mut source = IdentSource::odd();
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
