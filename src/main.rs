use std::io::Write;

use assert_matches::assert_matches;
use thiserror::Error;

mod lexer;
use lexer::{Lexer, Token, TokenDiscriminants, TokenInfo};

#[derive(Clone, Debug)]
pub struct Program {
    statements: Vec<AstStatement>,
}

#[derive(Clone, Debug)]
enum AstStatement {
    Let(String, AstExpression),
    Return(AstExpression),
}

#[derive(Clone, Debug)]
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
            write!(f, "{error}\n")?;
        }
        Ok(())
    }
}

pub struct Parser {
    lexer: Lexer,
    current_token_info: TokenInfo,
    peek_token_info: TokenInfo,
    errors: Vec<ParserError>,
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
        Self {
            lexer,
            current_token_info: current,
            peek_token_info: peek,
            errors: Vec::new(),
        }
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
                Ok(statement) => program.statements.push(statement),
                Err(error) => self.errors.push(error),
            }
            self.next_token();
        }

        if self.errors.len() > 0 {
            Err(ParserErrors {
                errors: self.errors.clone(),
            })
        } else {
            Ok(program)
        }
    }

    fn parse_statement(&mut self) -> Result<AstStatement, ParserError> {
        match &self.current_token_info.token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => Err(ParserError::unexpected_token(
                self.current_token_info.clone(),
            )),
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
}
