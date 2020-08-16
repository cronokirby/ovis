//! This module handles the lexing of strings into tokens for our parser.
//!
//! We mainly need a lexing phase to handle (eliminate) whitespace
use std::fmt;
use std::iter::Peekable;
use std::str::Chars;

/// The position of a token in a line
///
/// We need to be able to distinguish whether or not a token is at the start of a line,
/// with only whitespace before it, or in the middle
#[derive(Debug, PartialEq)]
enum LinePosition {
    Middle,
    Start,
}

/// An item annotated with the column where it appears
///
/// This is useful since we need to be able to keep track of the position
/// where characters, and ultimately tokens appear in order to handle whitespace sensitivity.
#[derive(Debug)]
struct Positioned<T> {
    item: T,
    col: u64,
    line_pos: LinePosition,
}

/// An iterator that will return non-whitespace characters, along with the position they appear at
struct PositionedChars<'a> {
    chars: Peekable<Chars<'a>>,
    col: u64,
    new_line: bool,
}

impl<'a> PositionedChars<'a> {
    /// Construct a lexer given a source of input to tokenize
    fn new(input: &'a str) -> Self {
        PositionedChars {
            chars: input.chars().peekable(),
            col: 0,
            new_line: true,
        }
    }

    fn peek_one(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    // This is useful for the cases where we want to advance without skipping over whitespace,
    // like when parsing a number. In this case we don't care about position either
    fn next_one(&mut self) -> Option<char> {
        self.col += 1;
        self.chars.next()
    }
}

impl<'a> Iterator for PositionedChars<'a> {
    type Item = Positioned<char>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.chars.next() {
            if !c.is_whitespace() {
                let line_pos = if self.new_line {
                    self.new_line = false;
                    LinePosition::Start
                } else {
                    LinePosition::Middle
                };
                self.col += 1;
                return Some(Positioned {
                    item: c,
                    col: self.col,
                    line_pos,
                });
            }
            if c == '\n' || c == '\r' {
                self.new_line = true;
                self.col = 0;
            } else {
                self.col += 1;
            }
        }
        None
    }
}

/// Represents a single token that we distinguish while lexing
///
/// Tokens represent a more useful unit of information while parsing. Using tokens
/// allows us to ignore things like whitespaces, focusing instead on individual
/// atoms like operators, litterals, or names.
///
/// Tokens also represent built-in types. This isn't the most elegant way
/// of doing things, but it does avoid repeating strings later in the program,
/// so I prefer doing it this way for now. Once we have custom types, it's probably
/// a better idea to treat things more uniformly.
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    /// The ":" symbol
    Colon,
    /// The ";" symbol
    Semicolon,
    /// The "=" symbol
    Equal,
    /// The "->" symbol
    RightArrow,
    /// The "+" symbol
    Plus,
    /// This can represent either unary minus, or binary minus, depending on the
    /// context. Figuring out which is the job of the parser.
    Minus,
    /// The "*" symbol
    Asterisk,
    /// The "/" symbol
    FSlash,
    /// The "\" symbol
    BSlash,
    /// Opening "("
    LeftParens,
    /// Closing ")"
    RightParens,
    /// Opening "{"
    LeftBrace,
    /// Opening "}"
    RightBrace,
    /// The keyword "let"
    Let,
    /// The keyword "in"
    In,
    /// The type "I64"
    TypeI64,
    /// The type "String",
    TypeString,
    /// Some positive numeric litteral.
    /// We have to handle unary minus, e.g. "-x" or "-69", when parsing later.
    /// We eventually want positive / negative litterals, hence i64 here.
    NumberLitt(i64),
    /// Represents a single string litteral
    StringLitt(String),
    /// A reference to some name, e.g. "a23"
    Name(String),
}

impl Token {
    /// Try and get the number containing in a numeric litteral token
    pub fn get_number(&self) -> Option<i64> {
        match self {
            Token::NumberLitt(x) => Some(*x),
            _ => None,
        }
    }

    /// Get the name contained in this token, if possible
    pub fn get_name(&self) -> Option<&str> {
        match self {
            Token::Name(s) => Some(s),
            _ => None,
        }
    }

    /// True if this token starts a layout (in the grammar) after it
    fn starts_layout(&self) -> bool {
        match self {
            Token::Let => true,
            _ => false,
        }
    }
}

fn can_continue_identifier(c: char) -> bool {
    c == '_' || c == '?' || c == '!' || c.is_alphanumeric()
}

/// Represents an error that can occurr during lexing.
///
/// The lexing phase will usually try to produce as many errors as possible
#[derive(Debug, PartialEq)]
pub enum LexError {
    /// We weren't expecting this character at this position
    Unexpected(char),
    /// We don't know what this (primitive) type is
    ///
    /// This is an error at this stage, since all valid types are known lexically
    /// in advance, since no user-defined types exist.
    UnknownPrimitiveType(String),
    /// A right brace was encountered will inferring layout that doesn't have
    /// a corresponding explicit opening brace
    UnmatchedRightBrace,
    /// A string litteral was started but never ended
    UnterminatedString,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LexError::*;
        match self {
            Unexpected(c) => writeln!(f, "Unexpected character: '{}'", c),
            UnknownPrimitiveType(s) => writeln!(f, "Type {} is not a primitive type", s),
            UnmatchedRightBrace => writeln!(f, "Unmatched explicit `}}` encountered"),
            UnterminatedString => writeln!(f, "Unterminated string litteral"),
        }
    }
}

/// The tokenizer will spit out tokens along with their position
///
/// Before we can use these tokens, we want to use the positions to infer semicolons
/// and braces.
struct Tokenizer<'a> {
    /// We hold an iterate over the characters, with a bit of lookahead
    chars: PositionedChars<'a>,
}

impl<'a> Tokenizer<'a> {
    /// Construct a lexer given a source of input to tokenize
    fn new(input: &'a str) -> Self {
        Tokenizer {
            chars: PositionedChars::new(input),
        }
    }

    /// Parse out a positive number, given it's first digit.
    /// The character passed here must be a valid digit.
    fn number(&mut self, first_digit: char) -> i64 {
        let mut acc: i64 = first_digit.to_digit(10).unwrap() as i64;
        while let Some(d) = self.chars.peek_one().and_then(|x| x.to_digit(10)) {
            self.chars.next_one();
            acc = 10 * acc + (d as i64);
        }
        acc
    }

    /// This works for both variable and type identifiers, since they only
    /// differ in validity based on their first character
    fn identifier(&mut self, starter: char) -> String {
        let mut acc = String::new();
        acc.push(starter);
        while let Some(c) = self.chars.peek_one() {
            if !can_continue_identifier(*c) {
                break;
            }
            // Fine since we peeked
            acc.push(self.chars.next_one().unwrap());
        }
        acc
    }

    /// Parse a string litteral, assuming that we've already seen a single "
    ///
    /// This will consume the closing " as well
    fn string_litt(&mut self) -> Option<String> {
        let mut acc = String::new();
        while let Some(c) = self.chars.next_one() {
            // If we see the closer, we want things to be ok
            if c == '"' {
                return Some(acc);
            }
            acc.push(c);
        }
        None
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Positioned<Token>, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        use Token::*;
        let next = self.chars.next()?;
        let res = match next.item {
            '(' => Ok(LeftParens),
            ')' => Ok(RightParens),
            '{' => Ok(LeftBrace),
            '}' => Ok(RightBrace),
            '=' => Ok(Equal),
            ':' => Ok(Colon),
            ';' => Ok(Token::Semicolon),
            '+' => Ok(Plus),
            '*' => Ok(Asterisk),
            '/' => Ok(FSlash),
            '\\' => Ok(BSlash),
            '-' => match self.chars.peek_one() {
                Some('>') => {
                    self.chars.next_one();
                    Ok(RightArrow)
                }
                _ => Ok(Minus),
            },
            '"' => self
                .string_litt()
                .map(StringLitt)
                .ok_or(LexError::UnterminatedString),
            a if a.is_digit(10) => Ok(NumberLitt(self.number(a))),
            a if a.is_lowercase() => {
                let id = self.identifier(a);
                let tok = match id.as_ref() {
                    "let" => Let,
                    "in" => In,
                    _ => Name(id),
                };
                Ok(tok)
            }
            a if a.is_uppercase() => {
                let type_ident = self.identifier(a);
                match type_ident.as_ref() {
                    "I64" => Ok(TypeI64),
                    "String" => Ok(TypeString),
                    _ => Err(LexError::UnknownPrimitiveType(type_ident)),
                }
            }
            c => Err(LexError::Unexpected(c)),
        };
        Some(res.map(|t| Positioned {
            item: t,
            line_pos: next.line_pos,
            col: next.col,
        }))
    }
}

/// Represents what kind of layout we're expecting to see
///
/// If we have an explicit layout, that means that the program contains explicit
/// braces and semicolons, and we should thus ignore indentation until that layout ends.
/// Otherwise, we expect new elements in the layout to have a certain indentation,
/// which we record in the IndentedBy branch
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Layout {
    Explicit,
    IndentedBy(u64),
}

/// This holds the state we need while inferring semicolons and braces from our tokens
struct Lexer {
    tokens: Vec<Token>,
    /// The stack of layout contexts we need to respect
    ///
    /// The top represents the current layout, and we pop it off the stack once it finishes
    layouts: Vec<Layout>,
    /// Whether or not we're expecting a layout to start
    ///
    /// This layout we're expecting can either be started by an explicit brace, or
    /// implicitly, by the presence of indentation.
    expecting_layout: bool,
}

impl Lexer {
    fn new() -> Self {
        Lexer {
            tokens: Vec::new(),
            layouts: Vec::new(),
            expecting_layout: true,
        }
    }

    fn lex(mut self, tokenizer: &mut Tokenizer) -> Result<Vec<Token>, Vec<LexError>> {
        let mut errors = Vec::new();
        for res in tokenizer {
            match res {
                Ok(t) => {
                    if let Err(e) = self.handle_token(t) {
                        errors.push(e);
                    }
                }
                Err(e) => errors.push(e),
            }
        }
        if errors.is_empty() {
            self.handle_end();
            Ok(self.tokens)
        } else {
            Err(errors)
        }
    }

    fn current_layout(&self) -> Option<Layout> {
        self.layouts.last().copied()
    }

    fn handle_token(&mut self, token: Positioned<Token>) -> Result<(), LexError> {
        // We only handle indents if the token is at the start, and if it doesn't start
        // a layout. The following branches usually mean that a token will start a layout,
        // but there's one case where it doesn't, hence the mutable variable.
        let mut should_handle_indent = token.line_pos == LinePosition::Start;
        if token.item == Token::RightBrace {
            should_handle_indent = false;
            if let Some(Layout::Explicit) = self.current_layout() {
                self.layouts.pop();
            } else {
                return Err(LexError::UnmatchedRightBrace);
            }
        } else if token.item.starts_layout() {
            should_handle_indent = false;
            self.expecting_layout = true;
        } else if self.expecting_layout {
            self.expecting_layout = false;
            should_handle_indent = false;
            if token.item == Token::LeftBrace {
                self.layouts.push(Layout::Explicit);
            } else {
                let n = Layout::IndentedBy(token.col);
                if n > self.current_layout().unwrap_or(Layout::Explicit) {
                    // A nested layout must be further indented
                    self.layouts.push(Layout::IndentedBy(token.col));
                    self.tokens.push(Token::LeftBrace);
                } else {
                    // We were expecting a layout, but this actually belongs to a previous
                    // layout, so this layout is in fact empty. We also need to handle
                    // the indentation of this token as if it weren't the first token
                    // of a layout
                    self.tokens.push(Token::LeftBrace);
                    self.tokens.push(Token::RightBrace);
                    should_handle_indent = true;
                }
            }
        }
        if should_handle_indent {
            let n = Layout::IndentedBy(token.col);
            while let Some(true) = self.current_layout().map(|l| n < l) {
                self.tokens.push(Token::RightBrace);
                self.layouts.pop();
            }
            if let Some(true) = self.current_layout().map(|l| l == n) {
                self.tokens.push(Token::Semicolon);
            }
        }
        self.tokens.push(token.item);
        Ok(())
    }

    /// At the end of the token stream, we need to insert all of the remaining closing
    /// braces for each layout we started implicitly.
    fn handle_end(&mut self) {
        for layout in &self.layouts {
            if *layout != Layout::Explicit {
                self.tokens.push(Token::RightBrace);
            }
        }
    }
}

/// Tokenize a string of input into its tokens, or output all the errors we found
pub fn lex(input: &str) -> Result<Vec<Token>, Vec<LexError>> {
    let mut tokenizer = Tokenizer::new(input);
    let lexer = Lexer::new();
    lexer.lex(&mut tokenizer)
}

#[cfg(test)]
mod test {
    use super::*;
    use Token::*;

    macro_rules! assert_lex {
        ($input:expr, $t:expr) => {{
            let res = lex($input);
            assert!(res.is_ok());
            assert_eq!(res.unwrap(), $t)
        }};
    }

    #[test]
    fn lexing_identifiers_works() {
        assert_lex!(
            "I64 String a12 a_A_?!",
            vec![
                LeftBrace,
                TypeI64,
                TypeString,
                Name("a12".into()),
                Name("a_A_?!".into()),
                RightBrace
            ]
        );
    }

    #[test]
    fn lexing_operators_works() {
        assert_lex!(
            "= : -> + - * / \\",
            vec![
                LeftBrace, Equal, Colon, RightArrow, Plus, Minus, Asterisk, FSlash, BSlash,
                RightBrace
            ]
        );
    }

    #[test]
    fn lexing_numbers_works() {
        assert_lex!(
            "-69 69",
            vec![LeftBrace, Minus, NumberLitt(69), NumberLitt(69), RightBrace]
        );
    }

    #[test]
    fn lexing_strings_works() {
        assert_lex!(
            "\"foo\" \"bar\"",
            vec![
                LeftBrace,
                StringLitt("foo".into()),
                StringLitt("bar".into()),
                RightBrace
            ]
        )
    }

    #[test]
    fn lexing_for_nested_layouts_works() {
        let input = r#"
            z =
              let
                x = 2
                y =
                  let
                    z = 3
                  in z
              in 4
        "#;
        assert_lex!(
            input,
            vec![
                LeftBrace,
                Name("z".into()),
                Equal,
                Let,
                LeftBrace,
                Name("x".into()),
                Equal,
                NumberLitt(2),
                Semicolon,
                Name("y".into()),
                Equal,
                Let,
                LeftBrace,
                Name("z".into()),
                Equal,
                NumberLitt(3),
                RightBrace,
                In,
                Name("z".into()),
                RightBrace,
                In,
                NumberLitt(4),
                RightBrace
            ]
        )
    }
}
