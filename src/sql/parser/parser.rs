use std::iter::Peekable;

use super::{ast, Keyword, Lexer, Token};
use crate::errinput;
use crate::error::{Error, Result};
use crate::sql::types::DataType;

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
        if let Some(t) = parser.lexer.next().transpose()? {
            return errinput!("unexpected token: {t}");
        }

        Ok(statement)
    }
    /// Parses a SQL statement.
    fn parse_statement(&mut self) -> Result<ast::Statement> {
        let Some(token) = self.peek()? else {
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
    fn parse_drop_table(&mut self) -> Result<ast::Statement> {
        unimplemented!("not implemented yet")
    }

    fn parse_delete(&mut self) -> Result<ast::Statement> {
        unimplemented!("not implemented yet")
    }
    fn parse_insert(&mut self) -> Result<ast::Statement> {
        unimplemented!("not implemented yet")
    }
    fn parse_select(&mut self) -> Result<ast::Statement> {
        unimplemented!("not implemented yet")
    }
    fn parse_update(&mut self) -> Result<ast::Statement> {
        unimplemented!("not implemented yet")
    }

    fn parse_explain(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Explain.into())?;
        if self.next_is(Keyword::Explain.into()) {
            return errinput!("nested EXPLAIN statements are not supported");
        }
        Ok(ast::Statement::Explain(Box::new(self.parse_statement()?)))
    }

    fn parse_create_table(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Create.into())?;
        self.expect(Keyword::Table.into())?;

        let name = self.next_ident()?;
        self.expect(Token::OpenParen)?;
        let mut columns = Vec::new();
        loop {
            columns.push(self.parse_create_table_column()?);
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        self.expect(Token::CloseParen)?;
        Ok(ast::Statement::CreateTable { name, columns })
    }

    fn parse_create_table_column(&mut self) -> Result<ast::Column> {
        let name = self.next_ident()?;

        let data_type = match self.next()? {
            Token::Keyword(Keyword::Bool | Keyword::Boolean) => DataType::Boolean,
            Token::Keyword(Keyword::Float | Keyword::Double) => DataType::Float,
            Token::Keyword(Keyword::Int | Keyword::Integer) => DataType::Integer,
            Token::Keyword(Keyword::String | Keyword::Text | Keyword::Varchar) => DataType::String,
            token => return errinput!("unexpected token {token}"),
        };
        let mut column = ast::Column {
            name,
            data_type,
            primary_key: false,
            nullable: None,
            default: None,
            unique: false,
            index: false,
            references: None,
        };

        while let Some(keyword) = self.next_if_keyword() {
            match keyword {
                Keyword::Primary => {
                    self.expect(Keyword::Key.into())?;
                    column.primary_key = true;
                }
                Keyword::Null => {
                    if column.nullable.is_some() {
                        return errinput!("column {} has multiple NULL constraints", column.name);
                    }
                }
                Keyword::Not => {
                    self.expect(Keyword::Null.into())?;
                    if column.nullable.is_some() {
                        return errinput!(
                            "column {} has multiple NOT NULL constraints",
                            column.name
                        );
                    }
                    column.nullable = Some(false);
                }
                Keyword::Default => column.default = Some(self.parse_expression()?),
                Keyword::Unique => column.unique = true,
                Keyword::Index => column.index = true,
                Keyword::References => column.references = Some(self.next_ident()?),
                keyword => return errinput!("unexpected keyword {keyword}"),
            }
        }

        Ok(column)
    }

    fn parse_expression(&mut self) -> Result<ast::Expression> {
        unimplemented!("Expression parsing is not implemented yet");
    }

    fn next_if_keyword(&mut self) -> Option<Keyword> {
        self.next_if_map(|token| match token {
            Token::Keyword(keyword) => Some(*keyword),
            token => None,
        })
    }

    fn next_if_map<T>(&mut self, f: impl Fn(&Token) -> Option<T>) -> Option<T> {
        self.peek().ok()?.map(f)?.inspect(|_| drop(self.next()))
    }

    fn next_ident(&mut self) -> Result<String> {
        match self.next()? {
            Token::Ident(indent) => Ok(indent),
            token => errinput!("unexpected token {token}"),
        }
    }

    fn pare_explain(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Explain.into())?;

        if self.next_is(Keyword::Explain.into()) {
            return errinput!("nested EXPLAIN statements are not supported");
        }
        Ok(ast::Statement::Explain(Box::new(self.parse_statement()?)))
    }

    fn parse_rollback(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Rollback.into())?;
        Ok(ast::Statement::Rollback)
    }

    fn parse_commit(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Commit.into())?;
        Ok(ast::Statement::Commit)
    }

    fn parse_begin(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Begin.into())?;
        self.skip(Keyword::Transaction.into());
        let mut read_only = false;
        if self.next_is(Keyword::Read.into()) {
            match self.next()? {
                Token::Keyword(Keyword::Only) => read_only = true,
                Token::Keyword(Keyword::Write) => {}
                token => return errinput!("unexpected token {token}"),
            }
        }

        let mut as_of = None;
        if self.next_is(Keyword::As.into()) {
            self.expect(Keyword::Of.into())?;
            self.expect(Keyword::System.into())?;
            self.expect(Keyword::Time.into())?;
            match self.next()? {
                Token::Number(n) => as_of = Some(n.parse::<u64>()?),
                token => return errinput!("unexpected token {token}"),
            }
        }

        return Ok(ast::Statement::Begin { read_only, as_of });
    }

    fn expect(&mut self, expect: Token) -> Result<()> {
        let token = self.next()?;
        if token != expect {
            return errinput!("expected {expect}, found {token}");
        }
        Ok(())
    }

    pub fn new(statement: &str) -> Parser {
        Parser { lexer: Lexer::new(statement).peekable() }
    }

    /// Consumes the next lexer token if it is the given token, returning true.
    fn next_is(&mut self, token: Token) -> bool {
        self.next_if(|t| *t == token).is_some()
    }

    /// Returns the next lexer token if it satisfies the predicate.
    fn next_if(&mut self, predicate: impl Fn(&Token) -> bool) -> Option<Token> {
        self.peek().ok()?.filter(|t| predicate(t));
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sql::parser::ast::{Column, Statement};
    use crate::sql::types::DataType;

    #[test]
    fn test_parse_create_table() {
        let sql = "CREATE TABLE users (id INT PRIMARY KEY, name STRING, age INT)";
        let stmt = Parser::parse(sql).expect("Failed to parse SQL statement");
        match stmt {
            Statement::CreateTable { name, columns } => {
                assert_eq!(name, "users");
                assert_eq!(columns.len(), 3);
                assert_eq!(columns[0].name, "id");
                assert_eq!(columns[0].data_type, DataType::Integer);
                assert!(columns[0].primary_key);
                assert_eq!(columns[1].name, "name");
                assert_eq!(columns[1].data_type, DataType::String);
                assert_eq!(columns[2].name, "age");
                assert_eq!(columns[2].data_type, DataType::Integer);
            }
            _ => panic!("Expected CreateTable statement"),
        }
    }
}
