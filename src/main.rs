use std::io::Write;

#[derive(Clone, Debug)]
pub struct TokenInfo {
    pub token: Token,
    pub filename: String,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Illegal,
    EOF,
    Identifier(String),
    Integer(String),

    Assignment,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    LessThan,
    GreaterThan,
    Equal,
    NotEqual,

    Comma,
    Semicolon,
    LeftParenthesis,
    RightParenthesis,
    LeftBrace,
    RightBrace,

    True,
    False,
    Return,
    If,
    Else,
    Function,
    Let,
}

impl Token {
    fn from_word(word: &str) -> Self {
        use Token::*;
        match word {
            "let" => Let,
            "fn" => Function,
            "return" => Return,
            "if" => If,
            "else" => Else,
            "false" => False,
            "true" => True,
            _ => Identifier(word.into()),
        }
    }
}

pub struct Lexer {
    code: Vec<char>,
    filename: String,
    idx: usize,
    line: u32,
    column: u32,
}

impl Lexer {
    pub fn from_code_str(code: &str) -> Self {
        Self {
            code: code.chars().collect(),
            filename: "<usr>".into(),
            idx: 0,
            line: 1,
            column: 1,
        }
    }

    pub fn tokenize_info(&mut self) -> anyhow::Result<Vec<TokenInfo>> {
        let mut token_infos = Vec::new();
        loop {
            let token_info = self.next_token_info();
            token_infos.push(token_info.clone());
            if let Token::EOF = token_info.token {
                break;
            }
            if let Token::Illegal = token_info.token {
                anyhow::bail!(
                    "Illegal token at {}, line: {}, column: {}",
                    token_info.filename,
                    token_info.line,
                    token_info.column
                );
            }
        }
        Ok(token_infos)
    }

    fn next_char(&mut self) -> Option<char> {
        self.code.get(self.idx).map(|&c| {
            if let '\n' = c {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
            self.idx += 1;
            c
        })
    }

    fn peek_next_char(&self) -> Option<char> {
        self.code.get(self.idx).copied()
    }

    fn next_token(&mut self) -> Token {
        use Token::*;

        let Some(next_char) = self.peek_next_char() else {
            self.next_char();
            return EOF;
        };

        let mut consume_char = true;

        let token = match next_char {
            '=' => {
                self.next_char();
                consume_char = false;
                if let Some('=') = self.peek_next_char() {
                    self.next_char();
                    Equal
                } else {
                    Assignment
                }
            }
            '+' => Plus,
            '-' => Minus,
            '*' => Asterisk,
            '/' => Slash,
            '<' => LessThan,
            '>' => GreaterThan,
            '!' => {
                self.next_char();
                consume_char = false;
                if let Some('=') = self.peek_next_char() {
                    NotEqual
                } else {
                    Bang
                }
            }
            '(' => LeftParenthesis,
            ')' => RightParenthesis,
            '{' => LeftBrace,
            '}' => RightBrace,
            ',' => Comma,
            ';' => Semicolon,
            'a'..='z' | 'A'..='Z' => {
                consume_char = false;
                let word = self.read_word();
                Token::from_word(&word)
            }
            '0'..='9' => {
                consume_char = false;
                let integer_str = self.read_integer();
                Token::Integer(integer_str)
            }
            _ => Illegal,
        };

        if consume_char {
            self.next_char();
        }
        token
    }

    fn read_integer(&mut self) -> String {
        let mut integer_str: String = "".into();
        while let Some(current_digit @ ('0'..='9')) = self.peek_next_char() {
            integer_str.push(current_digit);
            self.next_char();
        }
        integer_str
    }

    fn read_word(&mut self) -> String {
        let mut word: String = "".into();
        while let Some(current_char @ ('a'..='z' | 'A'..='Z' | '_')) = self.peek_next_char() {
            word.push(current_char);
            self.next_char();
        }
        word
    }

    fn skip_whitespace(&mut self) {
        while let Some('\n' | ' ' | '\t') = self.peek_next_char() {
            self.next_char();
        }
    }

    pub fn next_token_info(&mut self) -> TokenInfo {
        self.skip_whitespace();

        let line = self.line;
        let column = self.column;

        let token = self.next_token();

        TokenInfo {
            token,
            filename: self.filename.clone(),
            line,
            column,
        }
    }
}

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

pub struct Parser {
    lexer: Lexer,
    current_token_info: TokenInfo,
    peek_token_info: TokenInfo,
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
        }
    }

    pub fn parse_program(&mut self) -> Program {
        let mut program = Program { statements: Vec::new() };

        loop {
            if let Token::EOF = self.current_token_info.token {
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
    fn lexer_simple_tokens() {
        let code = "+=(){},;";
        let expected_tokens = {
            use Token::*;
            vec![
                Plus,
                Assignment,
                LeftParenthesis,
                RightParenthesis,
                LeftBrace,
                RightBrace,
                Comma,
                Semicolon,
                EOF,
            ]
        };
        let mut lexer = Lexer::from_code_str(code);
        for expected_token in expected_tokens {
            assert_eq!(lexer.next_token_info().token, expected_token);
        }
    }

    #[test]
    fn lexer_basic_code() {
        let code = "let five = 5;
let add = fn(x,y) {
    x + y;
};\n";
        let expected_lines_columns_tokens = {
            use Token::*;
            vec![
                (1, 1, Let),
                (1, 5, Identifier("five".into())),
                (1, 10, Assignment),
                (1, 12, Integer("5".into())),
                (1, 13, Semicolon),
                (2, 1, Let),
                (2, 5, Identifier("add".into())),
                (2, 9, Assignment),
                (2, 11, Function),
                (2, 13, LeftParenthesis),
                (2, 14, Identifier("x".into())),
                (2, 15, Comma),
                (2, 16, Identifier("y".into())),
                (2, 17, RightParenthesis),
                (2, 19, LeftBrace),
                (3, 5, Identifier("x".into())),
                (3, 7, Plus),
                (3, 9, Identifier("y".into())),
                (3, 10, Semicolon),
                (4, 1, RightBrace),
                (4, 2, Semicolon),
            ]
        };
        let mut lexer = Lexer::from_code_str(code);
        for expected in expected_lines_columns_tokens {
            let token_info = lexer.next_token_info();
            assert_eq!(
                (token_info.line, token_info.column, token_info.token),
                expected
            );
        }
    }

    #[test]
    fn lexer_operators() {
        let code = "+-*/<>!";
        let expected_tokens = {
            use Token::*;
            vec![Plus, Minus, Asterisk, Slash, LessThan, GreaterThan, Bang]
        };
        let mut lexer = Lexer::from_code_str(code);
        for expected in expected_tokens {
            let token_info = lexer.next_token_info();
            assert_eq!(token_info.token, expected);
        }
    }

    #[test]
    fn lexer_keywords() {
        let code = "true false fn return if else let";
        let expected_tokens = {
            use Token::*;
            vec![True, False, Function, Return, If, Else, Let]
        };
        let mut lexer = Lexer::from_code_str(code);
        for expected in expected_tokens {
            let token_info = lexer.next_token_info();
            assert_eq!(token_info.token, expected);
        }
    }

    #[test]
    fn lexer_two_character_operators() {
        let code = "== !=";
        let expected_tokens = {
            use Token::*;
            vec![Equal, NotEqual]
        };
        let mut lexer = Lexer::from_code_str(code);
        for expected in expected_tokens {
            let token_info = lexer.next_token_info();
            assert_eq!(token_info.token, expected);
        }
    }

    #[test]
    fn parser_let_statement() {
        let code = "let a = 3; let asdf = 4; let foobar = 1009348;";
        let identifiers = vec!["a", "asdf", "foobar"];
        let mut lexer = Lexer::from_code_str(code);
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
