use std::collections::HashMap;
use std::io::Write;

use derive_more::Display;
use thiserror::Error;

mod lexer;
use lexer::{Lexer, Token, TokenDiscriminants, TokenInfo};

#[derive(Clone, Debug)]
pub struct Program {
    statements: Vec<AstStatement>,
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for statement in &self.statements {
            write!(f, "{}", statement)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Display)]
enum AstStatement {
    #[display(fmt = "let {_0} = {_1};")]
    Let(String, AstExpression),
    #[display(fmt = "return {_0};")]
    Return(AstExpression),
    ExpressionStatement(AstExpression),
}

#[derive(Clone, Debug, Display)]
enum AstExpression {
    Identifier(String),
    Integer(u64),
}

#[derive(Error, Debug, Clone)]
#[error("{filename}:{line}:{column} {inner}")]
struct ParserError {
    filename: String,
    line: u32,
    column: u32,
    inner: ParserErrorInner,
}

impl ParserError {
    fn from_token_info_and_inner(token_info: TokenInfo, inner: ParserErrorInner) -> Self {
        Self {
            filename: token_info.filename,
            line: token_info.line,
            column: token_info.column,
            inner,
        }
    }

    fn expected_token(expected: TokenDiscriminants, token_info: TokenInfo) -> Self {
        Self::from_token_info_and_inner(
            token_info.clone(),
            ParserErrorInner::ExpectedToken {
                expected,
                found: token_info.token,
            },
        )
    }

    fn unexpected_token(token_info: TokenInfo) -> Self {
        Self::from_token_info_and_inner(
            token_info.clone(),
            ParserErrorInner::UnexpectedToken(token_info.token),
        )
    }
}

#[derive(Error, Debug, Clone)]
enum ParserErrorInner {
    #[error("expected token {expected:?}, found {found:?}")]
    ExpectedToken {
        expected: TokenDiscriminants,
        found: Token,
    },
    #[error("unexpected token {0:?}")]
    UnexpectedToken(Token),
}

#[derive(Error, Debug, Clone)]
pub struct ParserErrors {
    errors: Vec<ParserError>,
}

impl std::fmt::Display for ParserErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for error in self.errors.iter() {
            writeln!(f, "{error}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

type PrefixFn = fn(&mut Parser) -> Result<AstExpression, ParserError>;
type InfixFn = fn(&mut Parser, AstExpression) -> Result<AstExpression, ParserError>;

pub struct Parser {
    lexer: Lexer,
    current_token_info: TokenInfo,
    peek_token_info: TokenInfo,
    errors: Vec<ParserError>,
    prefix_parse_fns: HashMap<TokenDiscriminants, PrefixFn>,
    infix_parse_fns: HashMap<TokenDiscriminants, InfixFn>,
}

// I can't believe I actually was able to do this
macro_rules! expect_token {
    (@instance $($path:ident)::*) => {
        $($path)::*
    };
    (@instance $($path:ident)::*($args:tt)) => {
        $($path)::*(expect_token!(@args $args))
    };
    (@args $($arg:pat),+) => {
        $({ expect_token!(@ignore $arg); Default::default()}),+
    };
    (@ignore $arg:tt) => {};
    ($self:ident, $($pattern:tt)+) => {
        let $($pattern)+ = $self.peek_token_info.token.clone() else {
            return Err(
                ParserError::expected_token(
                    expect_token!(@instance $($pattern)+).into(),
                    $self.peek_token_info.clone()
                )
            );
        };

        $self.next_token();
    };
}

impl Parser {
    // TODO: Do this with iterators
    pub fn with_lexer(mut lexer: Lexer) -> Self {
        let current = lexer.next_token_info();
        let peek = lexer.next_token_info();
        let mut parser = Self {
            lexer,
            current_token_info: current,
            peek_token_info: peek,
            errors: Vec::new(),
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
        };
        parser.register_operators();
        parser
    }

    pub fn parse_program(&mut self) -> Result<Program, ParserErrors> {
        let mut program = Program {
            statements: Vec::new(),
        };

        loop {
            if let Token::Eof = self.current_token_info.token {
                break;
            }
            match self.parse_statement() {
                Ok(Some(statement)) => program.statements.push(statement),
                Ok(None) => {}
                Err(error) => self.errors.push(error),
            }
            self.next_token();
        }

        if !self.errors.is_empty() {
            Err(ParserErrors {
                errors: self.errors.clone(),
            })
        } else {
            Ok(program)
        }
    }

    fn register_prefix(&mut self, token_discriminant: TokenDiscriminants, prefix_fn: PrefixFn) {
        self.prefix_parse_fns.insert(token_discriminant, prefix_fn);
    }

    fn register_infix(&mut self, token_discriminant: TokenDiscriminants, infix_fn: InfixFn) {
        self.infix_parse_fns.insert(token_discriminant, infix_fn);
    }

    fn parse_statement(&mut self) -> Result<Option<AstStatement>, ParserError> {
        match &self.current_token_info.token {
            Token::Let => self.parse_let_statement().map(|x| Some(x)),
            Token::Return => self.parse_return_statement().map(|x| Some(x)),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_let_statement(&mut self) -> Result<AstStatement, ParserError> {
        expect_token!(self, Token::Identifier(identifier));
        expect_token!(self, Token::Assignment);

        loop {
            // Skip until next semicolon
            self.next_token();
            if let Token::Semicolon = self.current_token_info.token {
                break;
            }
        }

        Ok(AstStatement::Let(identifier, AstExpression::Integer(0)))
    }

    fn parse_return_statement(&mut self) -> Result<AstStatement, ParserError> {
        loop {
            // Skip until next semicolon
            self.next_token();
            if let Token::Semicolon = self.current_token_info.token {
                break;
            }
        }

        Ok(AstStatement::Return(AstExpression::Integer(0)))
    }

    fn parse_expression_statement(&mut self) -> Result<Option<AstStatement>, ParserError> {
        let expression = self.parse_expression(Precedence::Lowest)?;

        if let Token::Semicolon = self.current_token_info.token {
            self.next_token()
        }

        let statement = expression.map(|e| AstStatement::ExpressionStatement(e));
        return Ok(statement);
    }

    fn parse_expression(
        &mut self,
        precedence: Precedence,
    ) -> Result<Option<AstExpression>, ParserError> {
        return self
            .prefix_parse_fns
            .get(&self.current_token_info.token.clone().into())
            .copied()
            .map(|f| f(self))
            .transpose();
    }

    fn register_operators(&mut self) {
        self.register_prefix(TokenDiscriminants::Identifier, |parser| {
            return if
                let Token::Identifier(ident_name) = parser.current_token_info.token.clone() 
            {
                Ok(AstExpression::Identifier(ident_name))
            } else {
                Err(ParserError::expected_token(
                    TokenDiscriminants::Identifier,
                    parser.current_token_info.clone(),
                ))
            };
        });
    }

    fn next_token(&mut self) {
        std::mem::swap(&mut self.current_token_info, &mut self.peek_token_info);
        self.peek_token_info = self.lexer.next_token_info();
    }
}

fn repl() -> anyhow::Result<()> {
    let mut stdout = std::io::stdout();
    let prompt = ">> ";
    print!("{}", prompt);
    stdout.flush()?;

    for line in std::io::stdin().lines() {
        let mut lexer = Lexer::from_code_str(&line?);
        println!(
            "{:#?}",
            lexer
                .tokenize_info()?
                .iter()
                .map(|x| x.token.clone())
                .collect::<Vec<_>>()
        );
        print!("{}", prompt);
        stdout.flush()?;
    }
    println!();
    Ok(())
}

fn main() -> anyhow::Result<()> {
    repl()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn parser_let_statement() -> anyhow::Result<()> {
        let code = "let a = 3; let asdf = 4; let foobar = 1009348;";
        let identifiers = vec!["a", "asdf", "foobar"];
        let lexer = Lexer::from_code_str(code);
        let mut parser = Parser::with_lexer(lexer);
        let program = parser.parse_program()?;

        assert_eq!(program.statements.len(), 3);
        for (statement, expected) in program.statements.into_iter().zip(identifiers.into_iter()) {
            let identifier =
                assert_matches!(statement, AstStatement::Let(identifier, _) => identifier);
            assert_eq!(identifier, expected);
        }

        Ok(())
    }

    #[test]
    fn parser_return_statement() -> anyhow::Result<()> {
        let code = "return 3; return 4; return 35325;";
        let lexer = Lexer::from_code_str(code);
        let mut parser = Parser::with_lexer(lexer);
        let program = parser.parse_program()?;

        assert_eq!(program.statements.len(), 3);
        for statement in program.statements {
            assert_matches!(statement, AstStatement::Return(_));
        }

        Ok(())
    }

    #[test]
    fn parser_display() -> anyhow::Result<()> {
        let code = "let myVar = anotherVar;";
        let program = Program {
            statements: vec![AstStatement::Let(
                "myVar".into(),
                AstExpression::Identifier("anotherVar".into()),
            )],
        };

        assert_eq!(&program.to_string(), code);
        Ok(())
    }

    #[test]
    fn parser_identifier_expression() -> anyhow::Result<()> {
        let code = "foobar;";
        let lexer = Lexer::from_code_str(code);
        let mut parser = Parser::with_lexer(lexer);
        let program = parser.parse_program()?;

        assert_eq!(program.statements.len(), 1);
        let ident_name = assert_matches!(&program.statements[0],
           AstStatement::ExpressionStatement(
               AstExpression::Identifier(ident_name)
           ) => ident_name
        );

        assert_eq!(ident_name, "foobar");

        Ok(())
    }
}
