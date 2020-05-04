//! This module handles the lexing of strings into tokens for our parser.
//!
//! We mainly need a lexing phase to handle (eliminate) whitespace
use std::fmt;
use std::iter::Peekable;
use std::str::Chars;

/// The positioning of a token that we care about when calculating layout rules.
///
/// We want to know whether a lexeme is in the middle of a line, or whether or not it's
/// at the start (only whitespace before it) at a certain column
#[derive(Debug)]
enum Position {
    Middle,
    StartingAt(u64),
}

/// An item annotated with the column where it appears
///
/// This is useful since we need to be able to keep track of the position
/// where characters, and ultimately tokens appear in order to handle whitespace sensitivity.
#[derive(Debug)]
struct Positioned<T> {
    item: T,
    pos: Position,
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
                let pos = if self.new_line {
                    self.new_line = false;
                    Position::StartingAt(self.col)
                } else {
                    Position::Middle
                };
                self.col += 1;
                return Some(Positioned { item: c, pos });
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
    /// Some positive numeric litteral.
    /// We have to handle unary minus, e.g. "-x" or "-69", when parsing later.
    /// We eventually want positive / negative litterals, hence i64 here.
    NumberLitt(i64),
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
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LexError::*;
        match self {
            Unexpected(c) => writeln!(f, "Unexpected character: '{}'", c),
            UnknownPrimitiveType(s) => writeln!(f, "Type {} is not a primitive type", s),
        }
    }
}

/// The Lexer takes in our source program, and will start spitting out tokens.
struct Lexer<'a> {
    /// We hold an iterate over the characters, with a bit of lookahead
    chars: PositionedChars<'a>,
}

impl<'a> Lexer<'a> {
    /// Construct a lexer given a source of input to tokenize
    fn new(input: &'a str) -> Self {
        Lexer {
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
}

impl<'a> Iterator for Lexer<'a> {
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
                    _ => Err(LexError::UnknownPrimitiveType(type_ident)),
                }
            }
            c => Err(LexError::Unexpected(c)),
        };
        Some(res.map(|t| Positioned {
            item: t,
            pos: next.pos,
        }))
    }
}

/// Tokenize a string of input into its tokens, or output all the errors we found
pub fn lex(input: &str) -> Result<Vec<Token>, Vec<LexError>> {
    let lexer = Lexer::new(input);
    let mut errors = Vec::new();
    let mut tokens = Vec::new();
    let mut had_error = false;
    for res in lexer {
        if had_error {
            if let Err(e) = res {
                errors.push(e)
            }
        } else {
            match res {
                Err(e) => {
                    had_error = true;
                    errors.push(e)
                }
                Ok(t) => tokens.push(t.item),
            }
        }
    }
    if had_error {
        Err(errors)
    } else {
        Ok(tokens)
    }
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
    fn parsing_identifiers_works() {
        assert_lex!(
            "I64 a12 a_A_?!",
            vec![TypeI64, Name("a12".into()), Name("a_A_?!".into())]
        );
    }

    #[test]
    fn parsing_operators_works() {
        assert_lex!(
            "= : -> + - * / \\",
            vec![Equal, Colon, RightArrow, Plus, Minus, Asterisk, FSlash, BSlash]
        );
    }

    #[test]
    fn parsing_numbers_works() {
        assert_lex!("-69 69", vec![Minus, NumberLitt(69), NumberLitt(69)]);
    }
}
