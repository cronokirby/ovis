use crate::identifiers::{Ident, IdentSource};
use crate::interner::{Dictionary, DisplayWithDict, Interner};
use crate::parser;

use std::collections::{HashMap, HashSet};
use std::fmt;

/// We simply reuse the binary operations provided by the parser
pub type BinOp = parser::BinOp;

/// Represents a kind of type with no information whatsoever
#[derive(Clone, Copy, Debug)]
pub struct Unknown;

impl fmt::Display for Unknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "?")
    }
}

/// Represents a single expression in our language
#[derive(Debug, PartialEq)]
pub enum Expr<T = Unknown> {
    /// A lambda abstraction / function litteral
    Lambda(Ident, T, Box<Expr<T>>),
    /// A let expression, where we have a series of mutual declarations before the final expression
    Let(Vec<Definition<T>>, Box<Expr<T>>),
    /// A reference to a variable name or definition
    Name(Ident),
    /// A reference to a positive number
    NumberLitt(i64),
    /// A reference to a string litteral
    StringLitt(String),
    /// A binary operation between expressions
    Binary(BinOp, Box<Expr<T>>, Box<Expr<T>>),
    /// Unary negation of an expression
    Negate(Box<Expr<T>>),
    /// Represents the application of one function to an argument
    Apply(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T: DisplayWithDict> DisplayWithDict for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        match self {
            Expr::Lambda(n, t, e) => {
                write!(f, "(λ {} ", dict.get_or_str(*n))?;
                t.fmt(f, dict)?;
                write!(f, " ")?;
                e.fmt(f, dict)?;
                write!(f, ")")
            }
            Expr::Name(n) => write!(f, "{}", dict.get(*n).unwrap()),
            Expr::NumberLitt(i) => write!(f, "{}", i),
            Expr::StringLitt(s) => write!(f, "\"{}\"", s),
            Expr::Binary(op, e1, e2) => {
                write!(f, "({} ", op)?;
                e1.fmt(f, dict)?;
                write!(f, " ")?;
                e2.fmt(f, dict)?;
                write!(f, ")")
            }
            Expr::Negate(e) => {
                write!(f, "(- ")?;
                e.fmt(f, dict)?;
                write!(f, ")")
            }
            Expr::Apply(e1, e2) => {
                write!(f, "(apply ")?;
                e1.fmt(f, dict)?;
                write!(f, " ")?;
                e2.fmt(f, dict)?;
                write!(f, ")")
            }
            Expr::Let(defs, e) => {
                write!(f, "(let")?;
                for d in defs {
                    write!(f, " ")?;
                    d.fmt(f, dict)?;
                }
                write!(f, " ")?;
                e.fmt(f, dict)?;
                write!(f, ")")
            }
        }
    }
}

/// Represents a type, formed through primitive types, or composition of other types
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A function A -> B
    Function(Box<Type>, Box<Type>),
    /// The primitive integer type
    I64,
    /// The primitive string type
    Strng,
    /// A reference to some identifier, e.g. `a`
    ///
    /// Of course, that type variable has to be quantified in some scope for this
    /// to make any sense.
    TypeVar(Ident),
}

impl DisplayWithDict for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        match self {
            Type::Function(t1, t2) => {
                write!(f, "(-> ")?;
                t1.fmt(f, dict)?;
                write!(f, " ")?;
                t2.fmt(f, dict)?;
                write!(f, ")")
            }
            Type::TypeVar(n) => write!(f, "{}", dict.get_or_str(*n)),
            Type::I64 => write!(f, "I64"),
            Type::Strng => write!(f, "String"),
        }
    }
}

/// Represents an expression of a scheme, i.e. type with quantified polymorphic vars.
///
/// This is used to represent some declaration of a scheme, e.g. `{a} => a -> a`.
#[derive(Clone, Debug, PartialEq)]
pub struct Scheme {
    /// The polymorphic variables being quantified over
    ///
    /// They also have whatever kind of identifier we use for variable names.
    pub type_vars: HashSet<Ident>,
    /// The expression being quantified over
    pub typ: Type,
}

impl DisplayWithDict for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        if !self.type_vars.is_empty() {
            write!(f, "(=> (")?;
            let mut i = 0;
            for v in &self.type_vars {
                if i == 0 {
                    write!(f, "{}", dict.get_or_str(*v))?;
                } else {
                    write!(f, " {}", dict.get_or_str(*v))?;
                }
                i += 1;
            }
            write!(f, ") ")?;
            self.typ.fmt(f, dict)?;
            write!(f, ")")
        } else {
            self.typ.fmt(f, dict)
        }
    }
}

/// Represents a definition or annotation
///
/// A definition assigns a name to an expression, and a type annotation assigns
/// an explicit type to a name. Type annotations are optional in our language.
#[derive(Debug, PartialEq)]
pub enum Definition<T = Unknown> {
    /// Represents the definition of name, with its corresponding expression
    Val(Ident, T, Option<Scheme>, Expr<T>),
}

impl<T: DisplayWithDict> DisplayWithDict for Definition<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        let Definition::Val(n, t, declared, e) = self;
        match declared {
            None => {
                write!(f, "(= {} ", dict.get_or_str(*n))?;
            }
            Some(decl) => {
                write!(f, "(= (: {} ", dict.get_or_str(*n))?;
                decl.fmt(f, dict)?;
                write!(f, ") ")?;
            }
        }
        t.fmt(f, dict)?;
        write!(f, " ")?;
        e.fmt(f, dict)?;
        write!(f, ")")
    }
}

/// Represents a program in our language.
///
/// This is parametrized over the type of identifiers
///
/// A program is just a sequence of value or type annotations
#[derive(Debug, PartialEq)]
pub struct AST<T = Unknown> {
    pub definitions: Vec<Definition<T>>,
}

impl<T: DisplayWithDict> DisplayWithDict for AST<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, dict: &Dictionary) -> fmt::Result {
        writeln!(f, "(ast")?;
        for def in &self.definitions {
            write!(f, "  ")?;
            def.fmt(f, dict)?;
            write!(f, "\n")?;
        }
        writeln!(f, ")")
    }
}

struct Simplifier<'a> {
    interner: Interner<'a>,
}

impl<'a> Simplifier<'a> {
    fn new(source: &'a mut IdentSource) -> Self {
        Simplifier {
            interner: Interner::new(source),
        }
    }

    fn type_expr(&mut self, e: parser::TypeExpr) -> Type {
        match e {
            parser::TypeExpr::Function(t1, t2) => {
                Type::Function(Box::new(self.type_expr(*t1)), Box::new(self.type_expr(*t2)))
            }
            parser::TypeExpr::TypeVar(n) => Type::TypeVar(self.interner.ident(n)),
            parser::TypeExpr::I64 => Type::I64,
            parser::TypeExpr::Strng => Type::Strng,
        }
    }

    fn scheme(&mut self, e: parser::SchemeExpr) -> Scheme {
        let mut type_vars = HashSet::new();
        for name in e.type_vars {
            type_vars.insert(self.interner.ident(name));
        }
        let typ = self.type_expr(e.typ);
        Scheme { type_vars, typ }
    }

    fn expr(&mut self, e: parser::Expr) -> Expr {
        match e {
            parser::Expr::Name(n) => Expr::Name(self.interner.ident(n)),
            parser::Expr::StringLitt(s) => Expr::StringLitt(s),
            parser::Expr::NumberLitt(n) => Expr::NumberLitt(n),
            parser::Expr::Let(defs, body) => {
                Expr::Let(self.definitions(defs), Box::new(self.expr(*body)))
            }
            parser::Expr::Negate(body) => Expr::Negate(Box::new(self.expr(*body))),
            parser::Expr::Binary(op, e1, e2) => {
                Expr::Binary(op, Box::new(self.expr(*e1)), Box::new(self.expr(*e2)))
            }
            parser::Expr::Apply(e1, e2) => {
                Expr::Apply(Box::new(self.expr(*e1)), Box::new(self.expr(*e2)))
            }
            parser::Expr::Lambda(bindings, body) => {
                let mut seed = self.expr(*body);
                for name in bindings.into_iter().rev() {
                    seed = Expr::Lambda(self.interner.ident(name), Unknown, Box::new(seed))
                }
                seed
            }
        }
    }

    fn definitions(&mut self, defs: Vec<parser::Definition>) -> Vec<Definition> {
        let mut map: HashMap<Ident, Scheme> = HashMap::new();
        for def in &defs {
            match def {
                parser::Definition::Type(name, scheme) => {
                    let ident = self.interner.ident(name.to_string());
                    map.insert(ident, self.scheme(scheme.clone()));
                }
                _ => {}
            }
        }
        let mut res = Vec::new();
        for def in defs {
            match def {
                parser::Definition::Val(name, expr) => {
                    let ident = self.interner.ident(name);
                    res.push(Definition::Val(
                        ident,
                        Unknown,
                        map.get(&ident).cloned(),
                        self.expr(expr),
                    ))
                }
                _ => {}
            }
        }
        res
    }

    fn ast(&mut self, parsed: parser::AST) -> AST {
        AST {
            definitions: self.definitions(parsed.definitions),
        }
    }
}

/// Simplify a parsed AST to a representation of an equivalent program.
///
/// We want to simplify to remove so-called "Syntax Sugar", allowing us to
/// work more directly with certain constructs
pub fn simplify(parsed: parser::AST, source: &mut IdentSource) -> (AST, Dictionary) {
    let mut simplifier = Simplifier::new(source);
    let ast = simplifier.ast(parsed);
    (ast, simplifier.interner.dictionary())
}
