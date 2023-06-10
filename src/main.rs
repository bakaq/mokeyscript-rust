use std::io::Write;

mod lexer;
use lexer::{Lexer, Token, TokenInfo};

#[derive(Clone, Debug)]
pub struct Program {
    statements: Vec<AstStatement>,
}

#[derive(Clone, Debug)]
enum AstStatement {
    Let(String, AstExpression),
    Invalid,
}

#[derive(Clone, Debug)]
enum AstExpression {
    Identifier(String),
    Integer(u64),
    Invalid,
}

type ParserError = String;

pub struct Parser {
    lexer: Lexer,
    current_token_info: TokenInfo,
    peek_token_info: TokenInfo,
    errors: Vec<ParserError>,
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

    pub fn parse_program(&mut self) -> Program {
        let mut program = Program { statements: Vec::new() };

        loop {
            if let Token::Eof = self.current_token_info.token {
                break;
            }
            if let Some(statement) = self.parse_statement() {
                program.statements.push(statement);
            }
            self.next_token();
        }

        program
    }

    fn parse_statement(&mut self) -> Option<AstStatement> {
        match &self.current_token_info.token {
            Token::Let => self.parse_let_statement(),
            _ => None,
        }
    }

    fn parse_let_statement(&mut self) -> Option<AstStatement> {
        let Token::Identifier(identifier) = self.peek_token_info.token.clone() else {
            return None;
        };

        self.next_token();
        let Token::Assignment = self.peek_token_info.token else {
            return None;
        };

        self.next_token();
        loop {
            // Skip until next semicolon
            if let Token::Semicolon = self.peek_token_info.token {
                break;
            }
            self.next_token();
        }
        
        Some(AstStatement::Let(identifier, AstExpression::Integer(0)))
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
    fn parser_let_statement() {
        let code = "let a = 3; let asdf = 4; let foobar = 1009348;";
        let identifiers = vec!["a", "asdf", "foobar"];
        let lexer = Lexer::from_code_str(code);
        let mut parser = Parser::with_lexer(lexer);
        let program = parser.parse_program();

        assert_eq!(program.statements.len(), 3);
        for (statement, expected) in
            program.statements.into_iter().zip(identifiers.into_iter())
        {
            if let AstStatement::Let(identifier, _) = statement {
                assert_eq!(identifier, expected);
            } else {
                panic!("Should have been let statement, instead {:?}", statement);
            }
        }
    }
}
