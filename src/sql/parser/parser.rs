use std::iter::Peekable;

use super::{Lexer,Token, Keyword, ast};
use crate::error::{Result, Error};
use crate::errinput;



pub struct Parser<'a> {
    pub lexer: Peekable<Lexer<'a>>,
}

impl Parser<'_> {
    /// Parses the input string into a SQL statement AST. The entire string must
    /// be parsed as a single statement, ending with an optional semicolon.
    pub fn parse(statement: &str) -> Result<ast::Statement> {
        let mut parser = Self::new(statement);
        let statement = parser.parse_statement()?;
        parser.skip(Token::Semicolon);
        if let Some(t) = parser.peek()? {
            return errinput!("unexpected token: {t}")
        }

        Ok(statement)
    }
    /// Parses a SQL statement.
    fn parser(&mut self) -> Result<ast::Statement> {
        let Some(token)= self.peek()? else {
            return errinput!("Unexpected end of input");
        };
        match token {
            Token::Keyword(Keyword::Begin) => self.parse_begin(),
            Token::Keyword(Keyword::Commit) => self.parse_commit(),
            Token::Keyword(Keyword::Rollback) => self.parse_rollback(),
            Token::Keyword(Keyword::Explain) => self.parse_explain(),

            Token::Keyword(Keyword::Create) => self.parse_create_table(),
            Token::Keyword(Keyword::Drop) => self.parse_drop_table(),

            Token::Keyword(Keyword::Delete) => self.parse_delete(),
            Token::Keyword(Keyword::Insert) => self.parse_insert(),
            Token::Keyword(Keyword::Select) => self.parse_select(),
            Token::Keyword(Keyword::Update) => self.parse_update(),

            token => errinput!("unexpected token {token}"),
        }
    }

    pub fn new(statement:  &str) -> Parser {
        Parser {
            lexer: Lexer::new(statement).peekable(),
        }
    }

    /// Consumes the next lexer token if it is the given token, returning true.
    fn next_is(&mut self, token: Token) -> bool {
        self.next_if(|t| *t == token).is_some()
    }


    /// Returns the next lexer token if it satisfies the predicate.
    fn next_if(&mut self, predicate: impl Fn(&Token) -> bool) -> Option<Token> {
        self.peek().ok()?.filter(|t|predicate(t));
        self.next().ok()
    }
    /// Fetches the next lexer token, or errors if none is found.
    fn next(&mut self) -> Result<Token> {
        self.lexer.next().transpose()?.ok_or_else(|| errinput!("Unexpected end of input"))
    }

    /// Peeks the next lexer token if any, but transposes it for convenience.
    fn peek(&mut self) -> Result<Option<&Token>> {
        self.lexer.peek().map(|r| r.as_ref().map_err(|err| err.clone())).transpose()
    }
    
    /// Consumes the next lexer token if it is the given token. Equivalent to
    /// next_is(), but expresses intent better.
    fn skip(&mut self, token: Token) {
        self.next_is(token);
    }
}
