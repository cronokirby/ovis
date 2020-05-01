# Current Syntax

This represents the currently planned syntax for the language. The syntax describes
the programs that the compiler can parse.

# Definitions

An **Ovis** program is composed of definitions. Definitions bind names to expressions

```
// x is just a constant
x = 3

// y is an expression
y = \x -> x + 2
```

# Type Annotations

Top level definitions can also have *type annotations*, specifying what type a given expression is:

```
x : Int
x = 3

y : Int -> Int
y = \x -> x + 2
```

# Expressions

The usual arithmetic expressions are supported.

We can also define functions, through the lambda syntax:

```
\x -> x + 2
```

Multiple arguments are possible through *currying*:

```
\x -> \y -> x + y
```

# Grammar

As mentioned before, any line starting with `//` is a comment, and ignored by the parser.
Additionally, the lexer currently ignores all whitespace, so there's no inclusion
of these tokens in the description of the grammar.

Here's a full description of the grammar, in a rough BNF format. This doesn't worry
about details like avoiding left-recursion, and what-not. This is mainly to give an overview
of what the syntax rules look like. Concerns like associativity aren't really covered here.
If you want to know *exactly* how the syntax is defined, it's best to read the source code.

```
program := definition program

definition := expr_definition | type_annotation

expr_definition := name "=" expr

expr := lambda_expr
lambda_expr := "\" name "->" add_expr | add_expr
add_expr := mul_expr "+" mul_expr | mul_expr "-" mul_expr | mul_expr
mul_expr := add_expr "*" add_expr | app_expr "/" app_expr | app_expr
app_expr := factor factor | factor
factor := name | number | (expr)

type_annotation := name ":" type

type := type_factor "->" type_factor | type_factor
type_factor := primitive | (type)
primitive := "I64"

name := (a-z)(a-zA-Z0-9)*
number := (0-9)+
```
