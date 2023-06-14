use std::io::Write;

mod lexer;
mod parser;

use lexer::Lexer;

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
