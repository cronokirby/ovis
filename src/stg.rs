use crate::identifiers::{Ident, IdentSource};
use crate::interner::{Dictionary, DisplayWithDict};
use crate::parser::BinOp;
use crate::simplifier::{Definition, Expr as SExpr, Scheme, AST as SAST};
use std::fmt;

const INDENT_SIZE: u64 = 2;

pub struct AST {
    bindings: Vec<Binding>,
}

impl DisplayWithDict for AST {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        for b in &self.bindings {
            b.fmt(0, f, dict)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

pub struct Binding {
    pub name: Ident,
    pub lf: LambdaForm,
}

impl Binding {
    fn fmt(&self, indent: u64, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        for _ in 0..indent {
            write!(f, " ")?;
        }
        write!(f, "{} = ", dict.get_or_str(self.name))?;
        self.lf.fmt(indent, f, dict)
    }
}

pub enum Updateable {
    Yes,
    No,
}

impl fmt::Display for Updateable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Updateable::Yes => write!(f, "Y"),
            Updateable::No => write!(f, "N"),
        }
    }
}

pub struct LambdaForm {
    pub free: Vec<Ident>,
    pub updateable: Updateable,
    pub bound: Vec<Ident>,
    pub expr: Expr,
}

impl LambdaForm {
    fn fmt(&self, indent: u64, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        write!(f, "\\ {{")?;
        let mut i = 0;
        for name in &self.free {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", dict.get_or_str(*name))?;
            i += 1;
        }
        write!(f, "}} {} {{", self.updateable)?;
        let mut i = 0;
        for name in &self.bound {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", dict.get_or_str(*name))?;
            i += 1;
        }
        write!(f, "}} -> ")?;
        self.expr.fmt(indent, f, dict)
    }
}

pub enum Expr {
    Let(Vec<Binding>, Box<Expr>),
    Atom(Atom),
    ApplyName(Ident, Vec<Atom>),
    ApplyPrim(Primitive, Vec<Atom>),
}

impl Expr {
    fn as_atom(&self) -> Option<Atom> {
        if let Expr::Atom(a) = self {
            Some(a.clone())
        } else {
            None
        }
    }

    fn fmt(&self, mut indent: u64, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        match self {
            Expr::Let(bindings, expr) => {
                indent += INDENT_SIZE;
                writeln!(f)?;
                for _ in 0..indent {
                    write!(f, " ")?;
                }
                writeln!(f, "let")?;
                for b in bindings {
                    b.fmt(indent + INDENT_SIZE, f, dict)?;
                    writeln!(f)?;
                }
                for _ in 0..indent {
                    write!(f, " ")?;
                }
                write!(f, "in ")?;
                expr.fmt(indent, f, dict)
            }
            Expr::Atom(a) => a.fmt(f, dict),
            Expr::ApplyName(name, atoms) => {
                write!(f, "{} {{", dict.get_or_str(*name))?;
                let mut i = 0;
                for a in atoms {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    a.fmt(f, dict)?;
                    i += 1;
                }
                write!(f, "}}")
            }
            Expr::ApplyPrim(prim, atoms) => {
                write!(f, "{} {{", prim)?;
                let mut i = 0;
                for a in atoms {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    a.fmt(f, dict)?;
                    i += 1;
                }
                write!(f, "}}")
            }
        }
    }
}

pub enum Primitive {
    Add,
    Sub,
    Mul,
    Div,
    Negate,
    Concat,
}

impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Primitive::Add => write!(f, "+"),
            Primitive::Sub => write!(f, "-"),
            Primitive::Mul => write!(f, "*"),
            Primitive::Div => write!(f, "/"),
            Primitive::Negate => write!(f, "-"),
            Primitive::Concat => write!(f, "<>"),
        }
    }
}

#[derive(Clone)]
pub enum Litt {
    IntLitt(i64),
    StringLitt(String),
}

#[derive(Clone)]
pub enum Atom {
    Litt(Litt),
    Name(Ident),
}

impl Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        match self {
            Atom::Litt(Litt::IntLitt(i)) => write!(f, "{}", i),
            Atom::Litt(Litt::StringLitt(s)) => write!(f, "{:?}", s),
            Atom::Name(n) => write!(f, "{}", dict.get_or_str(*n)),
        }
    }
}

impl Atom {
    fn as_name(&self) -> Option<Ident> {
        match self {
            Atom::Name(i) => Some(*i),
            _ => None,
        }
    }
}

fn op_to_primitive(op: BinOp) -> Primitive {
    match op {
        BinOp::Add => Primitive::Add,
        BinOp::Sub => Primitive::Sub,
        BinOp::Mul => Primitive::Mul,
        BinOp::Div => Primitive::Div,
        BinOp::Concat => Primitive::Concat,
    }
}

fn compile_expr(
    expr: SExpr<Scheme>,
    bindings: &mut Vec<Binding>,
    source: &mut IdentSource,
) -> Expr {
    match expr {
        SExpr::Lambda(n, _, e) => {
            let mut inner_bindings = Vec::new();
            let r_e = compile_expr(*e, &mut inner_bindings, source);
            let name = source.next();
            let expr = if inner_bindings.is_empty() {
                r_e
            } else {
                Expr::Let(inner_bindings, Box::new(r_e))
            };
            bindings.push(Binding {
                name,
                lf: LambdaForm {
                    free: vec![],
                    updateable: Updateable::Yes,
                    bound: vec![n],
                    expr,
                },
            });
            Expr::Atom(Atom::Name(name))
        }
        SExpr::Let(defs, e) => {
            for def in defs {
                bindings.push(compile_def(def, source));
            }
            compile_expr(*e, bindings, source)
        }
        SExpr::Name(n) => Expr::Atom(Atom::Name(n)),
        SExpr::NumberLitt(i) => Expr::Atom(Atom::Litt(Litt::IntLitt(i))),
        SExpr::StringLitt(s) => Expr::Atom(Atom::Litt(Litt::StringLitt(s))),
        SExpr::Binary(op, l, r) => {
            let r_l = compile_expr(*l, bindings, source).as_atom().unwrap();
            let r_r = compile_expr(*r, bindings, source).as_atom().unwrap();
            let prim = op_to_primitive(op);
            let binary = Expr::ApplyPrim(prim, vec![r_l, r_r]);
            let binary_name = source.next();
            bindings.push(Binding {
                name: binary_name,
                lf: LambdaForm {
                    free: vec![],
                    updateable: Updateable::Yes,
                    bound: vec![],
                    expr: binary,
                },
            });
            Expr::Atom(Atom::Name(binary_name))
        }
        SExpr::Negate(e) => {
            let r_e = compile_expr(*e, bindings, source).as_atom().unwrap();
            let expr = Expr::ApplyPrim(Primitive::Negate, vec![r_e]);
            let expr_name = source.next();
            bindings.push(Binding {
                name: expr_name,
                lf: LambdaForm {
                    free: vec![],
                    updateable: Updateable::Yes,
                    bound: vec![],
                    expr,
                },
            });
            Expr::Atom(Atom::Name(expr_name))
        }
        SExpr::Apply(l, r) => {
            let l = compile_expr(*l, bindings, source)
                .as_atom()
                .and_then(|x| x.as_name())
                .unwrap();
            let r = compile_expr(*r, bindings, source).as_atom().unwrap();
            let expr = Expr::ApplyName(l, vec![r]);
            let expr_name = source.next();
            bindings.push(Binding {
                name: expr_name,
                lf: LambdaForm {
                    free: vec![],
                    updateable: Updateable::Yes,
                    bound: vec![],
                    expr,
                },
            });
            Expr::Atom(Atom::Name(expr_name))
        }
    }
}

fn compile_top(expr: SExpr<Scheme>, source: &mut IdentSource) -> LambdaForm {
    match expr {
        SExpr::Lambda(n, _, e) => {
            let mut inner_bindings = Vec::new();
            let r_e = compile_expr(*e, &mut inner_bindings, source);
            let name = source.next();
            let expr = if inner_bindings.is_empty() {
                r_e
            } else {
                Expr::Let(inner_bindings, Box::new(r_e))
            };
            LambdaForm {
                free: vec![],
                updateable: Updateable::Yes,
                bound: vec![n],
                expr,
            }
        }
        e => {
            let mut bindings = Vec::new();
            let compiled = match e {
                SExpr::Apply(l, r) => {
                    let l = compile_expr(*l, &mut bindings, source)
                        .as_atom()
                        .and_then(|x| x.as_name())
                        .unwrap();
                    let r = compile_expr(*r, &mut bindings, source).as_atom().unwrap();
                    Expr::ApplyName(l, vec![r])
                }
                e => compile_expr(e, &mut bindings, source),
            };
            let expr = if bindings.is_empty() {
                compiled
            } else {
                Expr::Let(bindings, Box::new(compiled))
            };
            LambdaForm {
                free: vec![],
                updateable: Updateable::Yes,
                bound: vec![],
                expr,
            }
        }
    }
}

fn compile_def(def: Definition<Scheme>, source: &mut IdentSource) -> Binding {
    let Definition::Val(name, _, _, e) = def;
    let lf = compile_top(e, source);
    Binding { name, lf }
}

pub fn compile(ast: SAST<Scheme>, source: &mut IdentSource) -> AST {
    let mut bindings = Vec::new();
    for def in ast.definitions {
        bindings.push(compile_def(def, source));
    }
    AST { bindings }
}
