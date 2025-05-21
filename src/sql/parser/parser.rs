use std::iter::Peekable;

use super::{Keyword, Lexer, Token, ast};


pub struct Parser<'a> {
    pub lexer: Peekable<Lexer<'a>>,
}