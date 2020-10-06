# Current Syntax

This represents the currently planned syntax for the language. The syntax describes
the programs that the compiler can parse.

# Definitions

An **Ovis** program is composed of definitions. Definitions bind names to expressions

```ovis
// x is just a constant
x = 3

// y is an expression
y = \x -> x + 2
```

# Expressions

The usual arithmetic expressions are supported.

We can also define functions, through the lambda syntax:

```ovis
\x -> x + 2
```

Multiple arguments are possible through *currying*:

```ovis
\x -> \y -> x + y
```

# Type Annotations

Top level definitions can also have *type annotations*, specifying what type a given expression is:

```ovis
x : I64
x = 3

y : I64 -> I64
y = \x -> x + 2
```

## Polymorphism

Ovis also supports a standard form of polymorphism. For example, the identity function would be:

```ovis
f : {a} => a -> a
f = \x -> x
```

All new type variables must be explicitly declared with `{a, b} =>`. It's possible to reference
previously introduced type variables, but unlike a language like Haskell, type annotations
like `f : a -> a` won't desugar to `f : {a} => a -> a` automatically.

### Examples

```ovis
first : {a, b} => a -> b -> b
first = \a b -> a
```

# Tokenizer

The tokenizer / lexer takes the string based representation of our program, and converts
it a sequence of tokens that's more easy to parse. The main reason we need a lexer
is to make the parsing of whitespace much simpler.

# Grammar

As mentioned before, any line starting with `//` is a comment, and ignored by the parser.
Additionally, the lexer currently ignores all whitespace, so there's no inclusion
of these tokens in the description of the grammar.

Here's a full description of the grammar, in a rough BNF format. This doesn't worry
about details like avoiding left-recursion, and what-not. This is mainly to give an overview
of what the syntax rules look like. Concerns like associativity aren't really covered here.
If you want to know *exactly* how the syntax is defined, it's best to read the source code.

```ovis
program := definition (";" definition)* | ""

definition := expr_definition | type_annotation

expr_definition := name = expr

expr := lambda_expr | arithmetic_expr

lambda_expr := "\" name+ "->" expr

let_expr := "let" "{" definition (";" definition)* "}" "in" expr

arithmetic_expr := add_expr
add_expr := mul_expr "+" mul_expr | mul_expr "-" mul_expr | mul_expr
mul_expr := add_expr "*" add_expr | app_expr "/" app_expr | app_expr
unary_minus_expr := "-" app_expr | app_expr
app_expr := factor app_expr | factor
factor := name | number | (expr)

type_annotation := name ":" scheme

scheme := "{" name ("," name)* "}" "=>" type | type
type := type_factor "->" type_factor | type_factor
type_factor := name | primitive | "(" type ")"
primitive := "I64" | "String"

name := (a-z)(a-zA-Z0-9!?_)*
number := (0-9)+
```
