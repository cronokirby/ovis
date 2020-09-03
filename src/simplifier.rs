use crate::ast;
use crate::parser;

fn expr(e: parser::Expr) -> ast::Expr<String, ()> {
    match e {
        parser::Expr::Name(n) => ast::Expr::Name(n),
        parser::Expr::StringLitt(s) => ast::Expr::StringLitt(s),
        parser::Expr::NumberLitt(n) => ast::Expr::NumberLitt(n),
        parser::Expr::Let(defs, body) => ast::Expr::Let(definitions(defs), Box::new(expr(*body))),
        parser::Expr::Negate(body) => ast::Expr::Negate(Box::new(expr(*body))),
        parser::Expr::Binary(op, e1, e2) => {
            ast::Expr::Binary(op, Box::new(expr(*e1)), Box::new(expr(*e2)))
        }
        parser::Expr::Apply(e1, e2) => ast::Expr::Apply(Box::new(expr(*e1)), Box::new(expr(*e2))),
        parser::Expr::Lambda(bindings, body) => {
            let mut seed = expr(*body);
            for name in bindings.into_iter().rev() {
                seed = ast::Expr::Lambda(name, (), Box::new(seed))
            }
            seed
        }
    }
}

fn definition(def: parser::Definition) -> ast::Definition<String, ()> {
    match def {
        parser::Definition::Type(name, type_expr) => ast::Definition::Type(name, type_expr),
        parser::Definition::Val(name, e) => ast::Definition::Val(name, (), expr(e)),
    }
}

fn definitions(defs: Vec<parser::Definition>) -> Vec<ast::Definition<String, ()>> {
    defs.into_iter().map(|x| definition(x)).collect()
}

/// Simplify a parsed AST to a representation of an equivalent program.
///
/// We want to simplify to remove so-called "Syntax Sugar", allowing us to
/// work more directly with certain constructs
pub fn simplify(parsed: parser::AST) -> ast::AST<String, ()> {
    ast::AST {
        definitions: definitions(parsed.definitions),
    }
}
