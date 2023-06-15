use std::collections::HashMap;

use derive_more::Display;
use thiserror::Error;

use crate::lexer::{Lexer, Token, TokenDiscriminants, TokenInfo};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Display)]
enum PrefixOperation {
    #[display(fmt = "!")]
    BooleanNegation,
    #[display(fmt = "-")]
    UnaryMinus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Display)]
enum InfixOperation {
    #[display(fmt = "+")]
    Plus,
    #[display(fmt = "-")]
    Minus,
    #[display(fmt = "*")]
    Multiplication,
    #[display(fmt = "/")]
    Division,
    #[display(fmt = ">")]
    GreaterThan,
    #[display(fmt = "<")]
    LessThan,
    #[display(fmt = "==")]
    Equals,
    #[display(fmt = "!=")]
    NotEquals,
}

impl InfixOperation {
    fn get_precedence(&self) -> Precedence {
        use Precedence::*;
        match self {
            InfixOperation::Plus => Sum,
            InfixOperation::Minus => Sum,
            InfixOperation::Multiplication => Product,
            InfixOperation::Division => Product,
            InfixOperation::GreaterThan => LessGreater,
            InfixOperation::LessThan => LessGreater,
            InfixOperation::Equals => Equals,
            InfixOperation::NotEquals => Equals,
        }
    }

    fn get_infix_tokens() -> Vec<TokenDiscriminants> {
        use TokenDiscriminants::*;
        vec![
            Plus,
            Minus,
            Slash,
            Asterisk,
            GreaterThan,
            LessThan,
            Equal,
            NotEqual,
        ]
    }
}

impl TryFrom<Token> for InfixOperation {
    type Error = String;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        use InfixOperation::*;
        Ok(match value {
            Token::Plus => Plus,
            Token::Minus => Minus,
            Token::Slash => Division,
            Token::Asterisk => Multiplication,
            Token::GreaterThan => GreaterThan,
            Token::LessThan => LessThan,
            Token::Equal => Equals,
            Token::NotEqual => NotEquals,
            _ => Err("token is not a infix operator")?,
        })
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
    Integer(i64),
    #[display(fmt = "({_0}{_1})")]
    PrefixExpression(PrefixOperation, Box<AstExpression>),
    #[display(fmt = "({_0} {_1} {_2})")]
    InfixExpression(Box<AstExpression>, InfixOperation, Box<AstExpression>),
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

    fn expected_tokens(expected: &[TokenDiscriminants], token_info: TokenInfo) -> Self {
        Self::from_token_info_and_inner(
            token_info.clone(),
            ParserErrorInner::ExpectedTokens {
                expected: expected.into(),
                found: token_info.token,
            },
        )
    }

    fn invalid_integer(token_info: TokenInfo, value: String) -> Self {
        Self::from_token_info_and_inner(
            token_info,
            ParserErrorInner::InvalidInteger(value),
        )
    }

    fn no_prefix_parse_fn(token_info: TokenInfo) -> Self {
        Self::from_token_info_and_inner(
            token_info.clone(),
            ParserErrorInner::NoPrefixParseFn(token_info.token),
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
    #[error("expected one of the tokens {expected:?}, found {found:?}")]
    ExpectedTokens {
        expected: Vec<TokenDiscriminants>,
        found: Token,
    },
    #[error("invalid integer {0}")]
    InvalidInteger(String),
    #[error("no prefix parse function for token {0:?}")]
    NoPrefixParseFn(Token),
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
    //Call,
}

type PrefixFn = fn(&mut Parser) -> Result<AstExpression, ParserError>;
type InfixFn = fn(&mut Parser, AstExpression) -> Result<AstExpression, ParserError>;

// TODO: Accumulate parsing errors in errors field instead of returning them from functions
// as we can show more errors for the user that way
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
                Ok(statement) => program.statements.push(statement),
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

    fn register_prefix(
        &mut self,
        token_discriminant: TokenDiscriminants,
        prefix_fn: PrefixFn,
    ) {
        self.prefix_parse_fns.insert(token_discriminant, prefix_fn);
    }

    fn register_infix(
        &mut self,
        token_discriminant: TokenDiscriminants,
        infix_fn: InfixFn,
    ) {
        self.infix_parse_fns.insert(token_discriminant, infix_fn);
    }

    fn parse_statement(&mut self) -> Result<AstStatement, ParserError> {
        match &self.current_token_info.token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
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

    fn parse_expression_statement(&mut self) -> Result<AstStatement, ParserError> {
        let expression = self.parse_expression(Precedence::Lowest)?;

        if let Token::Semicolon = self.peek_token_info.token {
            self.next_token();
        }

        Ok(AstStatement::ExpressionStatement(expression))
    }

    fn parse_expression(
        &mut self,
        precedence: Precedence,
    ) -> Result<AstExpression, ParserError> {
        println!("--{:?} {:?}", self.current_token_info, precedence);
        let prefix_parse_fn = self
            .prefix_parse_fns
            .get(&self.current_token_info.token.clone().into())
            .ok_or_else(|| {
                ParserError::no_prefix_parse_fn(self.current_token_info.clone())
            })?;
        let mut left_expression = prefix_parse_fn(self);

        let peek_semicolon = matches!(self.peek_token_info.token, Token::Semicolon);

        while !peek_semicolon && precedence < self.peek_precedence() {
            let infix_parse_fn = self
                .infix_parse_fns
                .get(&self.peek_token_info.token.clone().into())
                .cloned();
            if let Some(infix) = infix_parse_fn {
                self.next_token();
                left_expression = infix(self, left_expression.clone()?);
            } else {
                break;
            }
        }
        left_expression
    }

    fn register_operators(&mut self) {
        self.register_prefix(TokenDiscriminants::Identifier, |parser| {
            if let Token::Identifier(ident_name) = parser.current_token_info.token.clone()
            {
                Ok(AstExpression::Identifier(ident_name))
            } else {
                Err(ParserError::expected_token(
                    TokenDiscriminants::Identifier,
                    parser.current_token_info.clone(),
                ))
            }
        });

        self.register_prefix(TokenDiscriminants::Integer, |parser| {
            if let Token::Integer(value) = parser.current_token_info.token.clone() {
                Ok(AstExpression::Integer(value.parse().map_err(|_| {
                    ParserError::invalid_integer(parser.current_token_info.clone(), value)
                })?))
            } else {
                Err(ParserError::expected_token(
                    TokenDiscriminants::Integer,
                    parser.current_token_info.clone(),
                ))
            }
        });

        let parse_prefix_expr = |parser: &mut Parser| {
            let op = match parser.current_token_info.token {
                Token::Bang => PrefixOperation::BooleanNegation,
                Token::Minus => PrefixOperation::UnaryMinus,
                _ => Err(ParserError::expected_tokens(
                    &[Token::Bang.into(), Token::Minus.into()],
                    parser.current_token_info.clone(),
                ))?,
            };
            parser.next_token();
            let expression = parser.parse_expression(Precedence::Prefix)?;
            Ok(AstExpression::PrefixExpression(op, Box::new(expression)))
        };

        self.register_prefix(TokenDiscriminants::Bang, parse_prefix_expr);
        self.register_prefix(TokenDiscriminants::Minus, parse_prefix_expr);

        let parse_infix_expr = |parser: &mut Parser, left| {
            let precedence = parser.current_precedence();
            let op: InfixOperation = parser
                .current_token_info
                .token
                .clone()
                .try_into()
                .map_err(|_| {
                ParserError::expected_tokens(
                    &InfixOperation::get_infix_tokens(),
                    parser.current_token_info.clone(),
                )
            })?;
            parser.next_token();
            let right = parser.parse_expression(precedence)?;
            Ok(AstExpression::InfixExpression(
                Box::new(left),
                op,
                Box::new(right),
            ))
        };

        for token in InfixOperation::get_infix_tokens() {
            self.register_infix(token, parse_infix_expr);
        }
    }

    fn next_token(&mut self) {
        //println!("Current: {:?}", self.current_token_info);
        std::mem::swap(&mut self.current_token_info, &mut self.peek_token_info);
        self.peek_token_info = self.lexer.next_token_info();
    }

    fn current_precedence(&mut self) -> Precedence {
        self.current_token_info
            .token
            .clone()
            .try_into()
            .map(|op: InfixOperation| op.get_precedence())
            .unwrap_or(Precedence::Lowest)
    }

    fn peek_precedence(&mut self) -> Precedence {
        self.peek_token_info
            .token
            .clone()
            .try_into()
            .map(|op: InfixOperation| op.get_precedence())
            .unwrap_or(Precedence::Lowest)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn let_statement() -> anyhow::Result<()> {
        let code = "let a = 3; let asdf = 4; let foobar = 1009348;";
        let identifiers = vec!["a", "asdf", "foobar"];
        let lexer = Lexer::from_code_str(code);
        let mut parser = Parser::with_lexer(lexer);
        let program = parser.parse_program()?;

        assert_eq!(program.statements.len(), 3);
        for (statement, expected) in
            program.statements.into_iter().zip(identifiers.into_iter())
        {
            let identifier = assert_matches!(statement, AstStatement::Let(identifier, _) => identifier);
            assert_eq!(identifier, expected);
        }

        Ok(())
    }

    #[test]
    fn return_statement() -> anyhow::Result<()> {
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
    fn display() -> anyhow::Result<()> {
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
    fn identifier_expression() -> anyhow::Result<()> {
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

    #[test]
    fn integer_expression() -> anyhow::Result<()> {
        let code = "5;";
        let lexer = Lexer::from_code_str(code);
        let mut parser = Parser::with_lexer(lexer);
        let program = parser.parse_program()?;

        assert_eq!(program.statements.len(), 1);
        let value = assert_matches!(&program.statements[0],
           AstStatement::ExpressionStatement(
               AstExpression::Integer(value)
           ) => value
        );

        assert_eq!(*value, 5);

        Ok(())
    }

    #[test]
    fn prefix_expression() -> anyhow::Result<()> {
        let cases = [
            ("!5;", PrefixOperation::BooleanNegation, 5),
            ("-15;", PrefixOperation::UnaryMinus, 15),
        ];

        for (code, expected_op, expected_expr_int) in cases {
            let lexer = Lexer::from_code_str(code);
            let mut parser = Parser::with_lexer(lexer);
            let program = parser.parse_program()?;

            assert_eq!(program.statements.len(), 1);
            let (op, expr) = assert_matches!(&program.statements[0],
                AstStatement::ExpressionStatement(
                    AstExpression::PrefixExpression(op, expr)
                ) => (op, expr)
            );

            assert_eq!(*op, expected_op);
            let expr_int = assert_matches!(**expr,
                AstExpression::Integer(expr_int) => expr_int
            );
            assert_eq!(expr_int, expected_expr_int);
        }

        Ok(())
    }

    #[test]
    fn infix_expressions() -> anyhow::Result<()> {
        let cases = [
            ("5 + 5;", 5, InfixOperation::Plus, 5),
            ("5 - 5;", 5, InfixOperation::Minus, 5),
            ("5 * 5;", 5, InfixOperation::Multiplication, 5),
            ("5 / 5;", 5, InfixOperation::Division, 5),
            ("5 > 5;", 5, InfixOperation::GreaterThan, 5),
            ("5 < 5;", 5, InfixOperation::LessThan, 5),
            ("5 == 5;", 5, InfixOperation::Equals, 5),
            ("5 != 5;", 5, InfixOperation::NotEquals, 5),
        ];

        for (code, expected_int_left, expected_op, expected_int_right) in cases {
            let lexer = Lexer::from_code_str(code);
            let mut parser = Parser::with_lexer(lexer);
            let program = parser.parse_program()?;

            assert_eq!(program.statements.len(), 1);
            let (expr_left, op, expr_right) = assert_matches!(&program.statements[0],
                AstStatement::ExpressionStatement(
                    AstExpression::InfixExpression(expr_left, op, expr_right)
                ) => (expr_left, op, expr_right)
            );

            assert_eq!(*op, expected_op);

            let int_left = assert_matches!(**expr_left,
                AstExpression::Integer(int_left) => int_left
            );
            assert_eq!(int_left, expected_int_left);

            let int_right = assert_matches!(**expr_right,
                AstExpression::Integer(int_right) => int_right
            );
            assert_eq!(int_right, expected_int_right);
        }

        Ok(())
    }

    #[test]
    fn operator_precedence() -> anyhow::Result<()> {
        let cases = [
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b / c", "(a + (b / c))"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
        ];

        for (code, expected) in cases {
            println!("Case: {}", code);
            let lexer = Lexer::from_code_str(code);
            let mut parser = Parser::with_lexer(lexer);
            let program = parser.parse_program()?;
            assert_eq!(&program.to_string(), expected);
        }
        Ok(())
    }
}
