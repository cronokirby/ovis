use crate::identifiers::Ident;

struct Binding {
    name: Ident,
    lf: LambdaForm,
}

enum Updateable {
    Yes,
    No,
}

struct LambdaForm {
    free: Vec<Ident>,
    updateable: Updateable,
    bound: Vec<Ident>,
    expr: Expr,
}

enum Expr {
    Let(Vec<Binding>, Box<Expr>),
    ApplyVar(Ident, Vec<Atom>),
    ApplyPrim(Primitive, Vec<Atom>),
    Litt(Litt),
}

enum Primitive {
    Add,
    Sub,
    Mul,
    Div,
}

enum Litt {
    IntLitt(i64),
    StringLitt(String),
}

enum Atom {
    Litt(Litt),
    Name(Ident),
}
