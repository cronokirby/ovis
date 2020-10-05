use crate::identifiers::{Ident, IdentSource};
use crate::interner::{Dictionary, DisplayWithDict};
use crate::simplifier::{Definition, Expr, Scheme, Type, AST};
use std::collections::{HashMap, HashSet};
use std::fmt::{Formatter, Result as FmtResult};

/// The type we use to represent type-level variables.
type TypeVar = Ident;

/// The type we use to represent variables
type Var = Ident;

/// Represents a kind of constraint we create when typing.
///
/// The idea is to have a constraint generation phase, and then
/// a final constraint gathering phase later.
#[derive(Clone, Debug)]
enum Constraint {
    /// An assertion that two types must be equal
    SameType(Type, Type),
    /// The first type must be able to be seen as an instance of some scheme
    ExplicitInst(Type, Scheme),
    /// The first type should be an instance of the second, generalized over some type variables
    ImplicitInst(Type, HashSet<TypeVar>, Type),
}

impl Constraint {
    fn active_type_vars(&self, buf: &mut HashSet<TypeVar>) {
        match self {
            Constraint::SameType(t1, t2) => {
                t1.free_type_vars(buf);
                t2.free_type_vars(buf);
            }
            Constraint::ExplicitInst(typ, scheme) => {
                typ.free_type_vars(buf);
                scheme.free_type_vars(buf);
            }
            Constraint::ImplicitInst(t1, vars, t2) => {
                let mut tmp = HashSet::new();
                t2.free_type_vars(&mut tmp);
                for v in tmp.intersection(vars) {
                    buf.insert(*v);
                }
                t1.free_type_vars(buf);
            }
        }
    }
}

/// Represents a substitution of type variables for concrete types
#[derive(Debug)]
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

    fn unify(&mut self, t1: Type, t2: Type) -> TypeResult<()> {
        match (t1, t2) {
            (t1, t2) if t1 == t2 => Ok(()),
            (Type::TypeVar(a), t) | (t, Type::TypeVar(a)) => {
                if t == Type::TypeVar(a) {
                    Ok(())
                } else {
                    let mut free = HashSet::new();
                    t.free_type_vars(&mut free);
                    if free.contains(&a) {
                        Err(TypeError::InfiniteType(a, t))
                    } else {
                        self.add(a, t);
                        Ok(())
                    }
                }
            }
            (Type::Function(t1, mut t2), Type::Function(t3, mut t4)) => {
                self.unify(*t1, *t3)?;
                t2.substitute(self, None);
                t4.substitute(self, None);
                self.unify(*t2, *t4)?;
                Ok(())
            }
            (t1, t2) => Err(TypeError::Mismatch(t1, t2)),
        }
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

fn instantiate(source: &mut IdentSource, mut scheme: Scheme) -> Type {
    let mut subst = Substitution::empty();
    for v in &scheme.type_vars {
        subst.add(*v, Type::TypeVar(source.next()));
    }
    scheme.typ.substitute(&subst, None);
    scheme.typ
}

fn generalize(free: &HashSet<TypeVar>, typ: Type) -> Scheme {
    let mut type_vars = HashSet::new();
    typ.free_type_vars(&mut type_vars);
    for v in free {
        type_vars.remove(&v);
    }
    Scheme { type_vars, typ }
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

    fn remove(&mut self, var: Var) {
        self.0 = self
            .0
            .iter()
            .filter(|x| x.0 != var)
            .map(|x| (x.0, x.1.clone()))
            .collect();
    }

    /// Collect the set of variables we have an assumption about
    fn vars(&self, buf: &mut HashSet<Var>) {
        for (v, _) in &self.0 {
            buf.insert(*v);
        }
    }

    fn lookup(&self, var: Var) -> impl Iterator<Item = &(Var, Type)> {
        self.0.iter().filter(move |x| x.0 == var)
    }
}

trait FreeTypeVars {
    fn free_type_vars(&self, buf: &mut HashSet<TypeVar>);
}

impl FreeTypeVars for Ident {
    fn free_type_vars(&self, buf: &mut HashSet<TypeVar>) {
        buf.insert(*self);
    }
}

impl FreeTypeVars for Type {
    fn free_type_vars(&self, buf: &mut HashSet<TypeVar>) {
        match self {
            Type::TypeVar(a) => {
                buf.insert(*a);
            }
            Type::Function(t1, t2) => {
                t1.free_type_vars(buf);
                t2.free_type_vars(buf);
            }
            _ => {}
        }
    }
}

impl FreeTypeVars for Scheme {
    fn free_type_vars(&self, buf: &mut HashSet<TypeVar>) {
        self.typ.free_type_vars(buf);
        for v in &self.type_vars {
            buf.remove(v);
        }
    }
}

struct Context {
    scopes: Vec<HashSet<TypeVar>>,
}

impl Context {
    fn empty() -> Self {
        Context {
            scopes: vec![HashSet::new()],
        }
    }

    fn enter(&mut self) {
        self.scopes.push(HashSet::new())
    }

    fn exit(&mut self) {
        self.scopes.pop();
    }

    fn add(&mut self, tv: TypeVar) {
        self.scopes.last_mut().unwrap().insert(tv);
    }

    fn bound(&self, buf: &mut HashSet<TypeVar>) {
        for scope in &self.scopes {
            for v in scope {
                buf.insert(*v);
            }
        }
    }
}

#[derive(Debug)]
pub enum TypeError {
    Mismatch(Type, Type),
    InfiniteType(TypeVar, Type),
    UnboundVar(Var),
}

impl DisplayWithDict for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>, dict: &Dictionary) -> FmtResult {
        match self {
            TypeError::Mismatch(t1, t2) => {
                write!(f, "Mismatched types: ")?;
                t1.fmt(f, dict)?;
                write!(f, " != ")?;
                t2.fmt(f, dict)
            }
            TypeError::InfiniteType(v, t) => {
                write!(f, "Cannot unify infinite type: {} ~ ", dict.get_or_str(*v))?;
                t.fmt(f, dict)
            }
            TypeError::UnboundVar(v) => write!(f, "Unbound variable: {}", dict.get_or_str(*v)),
        }
    }
}

pub type TypeResult<T> = Result<T, TypeError>;

struct Inferencer<'a> {
    ctx: Context,
    source: &'a mut IdentSource,
    constraints: Vec<Constraint>,
    assumptions: Assumptions,
}

impl<'a> Inferencer<'a> {
    fn new(source: &'a mut IdentSource) -> Self {
        Inferencer {
            ctx: Context::empty(),
            source,
            constraints: Vec::new(),
            assumptions: Assumptions::empty(),
        }
    }

    fn infer_expr(&mut self, expr: Expr) -> (Type, Expr<Type>) {
        match expr {
            Expr::NumberLitt(n) => (Type::I64, Expr::NumberLitt(n)),
            Expr::StringLitt(s) => (Type::Strng, Expr::StringLitt(s)),
            Expr::Name(v) => {
                let tv = Type::TypeVar(self.source.next());
                self.assumptions.extend(v, tv.clone());
                (tv, Expr::Name(v))
            }
            Expr::Lambda(v, _, e) => {
                let tv = Type::TypeVar(self.source.next());

                self.ctx.enter();
                self.ctx.add(v);
                let (rt, re) = self.infer_expr(*e);
                self.ctx.exit();

                for (_, t) in self.assumptions.lookup(v) {
                    self.constraints
                        .push(Constraint::SameType(t.clone(), tv.clone()));
                }
                self.assumptions.remove(v);
                (
                    Type::Function(Box::new(tv.clone()), Box::new(rt)),
                    Expr::Lambda(v, tv, Box::new(re)),
                )
            }
            Expr::Let(def, e2) => {
                let Definition::Val(v, _, declared, e1) = *def;
                let (rt1, re1) = self.infer_expr(e1);
                let (rt2, re2) = self.infer_expr(*e2);
                let mut bound = HashSet::new();
                self.ctx.bound(&mut bound);

                if let Some(d) = declared {
                    self.constraints
                        .push(Constraint::ExplicitInst(rt1.clone(), d));
                }

                for (_, t) in self.assumptions.lookup(v) {
                    self.constraints.push(Constraint::ImplicitInst(
                        t.clone(),
                        bound.clone(),
                        rt1.clone(),
                    ))
                }
                self.assumptions.remove(v);

                let new_def = Definition::Val(v, rt1, None, re1);
                (rt2, Expr::Let(Box::new(new_def), Box::new(re2)))
            }
            Expr::Binary(op, e1, e2) => {
                let (rt1, re1) = self.infer_expr(*e1);
                let (rt2, re2) = self.infer_expr(*e2);
                let tv = Type::TypeVar(self.source.next());
                let actual = Type::Function(
                    Box::new(rt1),
                    Box::new(Type::Function(Box::new(rt2), Box::new(tv.clone()))),
                );
                let expected = Type::Function(
                    Box::new(Type::I64),
                    Box::new(Type::Function(Box::new(Type::I64), Box::new(Type::I64))),
                );
                self.constraints
                    .push(Constraint::SameType(actual, expected));
                (tv, Expr::Binary(op, Box::new(re1), Box::new(re2)))
            }
            Expr::Negate(e) => {
                let (rt, re) = self.infer_expr(*e);
                let tv = Type::TypeVar(self.source.next());
                let actual = Type::Function(Box::new(rt), Box::new(tv.clone()));
                let expected = Type::Function(Box::new(Type::I64), Box::new(Type::I64));
                self.constraints
                    .push(Constraint::SameType(actual, expected));
                (tv, Expr::Negate(Box::new(re)))
            }
            Expr::Apply(e1, e2) => {
                let (rt1, re1) = self.infer_expr(*e1);
                let (rt2, re2) = self.infer_expr(*e2);
                let tv = Type::TypeVar(self.source.next());
                let expected = Type::Function(Box::new(rt2), Box::new(tv.clone()));
                self.constraints.push(Constraint::SameType(rt1, expected));
                (tv, Expr::Apply(Box::new(re1), Box::new(re2)))
            }
        }
    }

    fn infer(&mut self, ast: AST) -> AST<Type> {
        let mut definitions = Vec::new();
        for Definition::Val(v, _, declared, e) in ast.definitions {
            let (rt, re) = self.infer_expr(e);
            if let Some(d) = declared {
                self.constraints
                    .push(Constraint::ExplicitInst(rt.clone(), d))
            }
            definitions.push(Definition::Val(v, rt, None, re))
        }
        AST { definitions }
    }
}

struct Solver<'a> {
    constraints: Vec<Constraint>,
    solved: HashSet<usize>,
    source: &'a mut IdentSource,
    substitution: Substitution,
}

impl<'a> Solver<'a> {
    fn new(constraints: Vec<Constraint>, source: &'a mut IdentSource) -> Self {
        Solver {
            constraints,
            solved: HashSet::new(),
            source,
            substitution: Substitution::empty(),
        }
    }

    fn solvable(&self, constraint: &Constraint, at: usize) -> bool {
        match constraint {
            Constraint::SameType(_, _) => true,
            Constraint::ExplicitInst(_, _) => true,
            // An implicit instantation is solvable only if there is no overlap
            // between the active type variables in the constraints, and the
            // free type variables in the instantiating type
            Constraint::ImplicitInst(_, bound, t2) => {
                let mut active = HashSet::new();
                for i in 0..self.constraints.len() {
                    if i == at || self.solved.contains(&i) {
                        continue;
                    }
                    self.constraints[i].active_type_vars(&mut active);
                }
                let mut free = HashSet::new();
                t2.free_type_vars(&mut free);
                for v in free.difference(bound) {
                    if active.contains(v) {
                        return false;
                    }
                }
                true
            }
        }
    }

    fn next_constraint(&mut self) -> Constraint {
        for i in 0..self.constraints.len() {
            if self.solved.contains(&i) {
                continue;
            }
            if self.solvable(&self.constraints[i], i) {
                self.solved.insert(i);
                return self.constraints[i].clone();
            }
        }
        panic!("IMPOSSIBLE: No constraints are solvable in type checker")
    }

    fn has_constraints(&self) -> bool {
        self.constraints.len() > self.solved.len()
    }

    fn solve(&mut self) -> TypeResult<()> {
        while self.has_constraints() {
            match self.next_constraint() {
                Constraint::SameType(t1, t2) => {
                    self.substitution.unify(t1, t2)?;
                    for c in &mut self.constraints {
                        c.substitute(&self.substitution, None);
                    }
                }
                Constraint::ExplicitInst(t, scheme) => {
                    let inst = instantiate(self.source, scheme);
                    self.constraints.push(Constraint::SameType(inst, t));
                }
                Constraint::ImplicitInst(t1, bound, t2) => {
                    let generalized = generalize(&bound, t2);
                    self.constraints
                        .push(Constraint::ExplicitInst(t1, generalized));
                }
            }
        }
        Ok(())
    }
}

struct Typer {
    subst: Substitution,
    bound: HashSet<TypeVar>,
}

impl Typer {
    fn new(subst: Substitution) -> Self {
        Typer {
            subst,
            bound: HashSet::new(),
        }
    }

    fn scheme_for(&self, mut typ: Type) -> Scheme {
        typ.substitute(&self.subst, None);
        generalize(&self.bound, typ)
    }

    fn apply_expr(&mut self, expr: Expr<Type>) -> Expr<Scheme> {
        match expr {
            Expr::NumberLitt(n) => Expr::NumberLitt(n),
            Expr::StringLitt(s) => Expr::StringLitt(s),
            Expr::Negate(e1) => Expr::Negate(Box::new(self.apply_expr(*e1))),
            Expr::Name(v) => Expr::Name(v),
            Expr::Binary(op, e1, e2) => Expr::Binary(
                op,
                Box::new(self.apply_expr(*e1)),
                Box::new(self.apply_expr(*e2)),
            ),
            Expr::Apply(e1, e2) => Expr::Apply(
                Box::new(self.apply_expr(*e1)),
                Box::new(self.apply_expr(*e2)),
            ),
            Expr::Lambda(v, t, e) => {
                let scheme: Scheme = self.scheme_for(t);
                for b in &scheme.type_vars {
                    self.bound.insert(*b);
                }
                Expr::Lambda(v, scheme, Box::new(self.apply_expr(*e)))
            }
            Expr::Let(def, e2) => {
                let Definition::Val(v, t, _, e1) = *def;
                let s1 = self.scheme_for(t);
                for b in &s1.type_vars {
                    self.bound.insert(*b);
                }
                let r1 = self.apply_expr(e1);
                let r2 = self.apply_expr(*e2);
                Expr::Let(Box::new(Definition::Val(v, s1, None, r1)), Box::new(r2))
            }
        }
    }

    fn apply(&mut self, ast: AST<Type>) -> AST<Scheme> {
        let mut definitions = Vec::new();
        for Definition::Val(v, t, _, e) in ast.definitions {
            let s = self.scheme_for(t);
            let r = self.apply_expr(e);
            definitions.push(Definition::Val(v, s, None, r))
        }
        AST { definitions }
    }
}

pub fn type_tree(ast: AST, source: &mut IdentSource) -> TypeResult<AST<Scheme>> {
    let mut inferencer = Inferencer::new(source);
    let tree = inferencer.infer(ast);
    let mut assumed_vars = HashSet::new();
    inferencer.assumptions.vars(&mut assumed_vars);
    for v in assumed_vars {
        return Err(TypeError::UnboundVar(v));
    }
    let mut solver = Solver::new(inferencer.constraints, source);
    solver.solve()?;

    let mut typer = Typer::new(solver.substitution);
    Ok(typer.apply(tree))
}
