//! The `zedc` command: `zedc fmt <file>` writes the file in the formatter's layout to standard
//! output; `zedc run` and `zedc replay` run a program ([`zedc::run::command`]); `zedc test`
//! runs the tests of units ([`zedc::testing::command`]); with no arguments it prints its
//! version.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match &args[..] {
        [] => println!("zedc {}", env!("CARGO_PKG_VERSION")),
        [cmd, file] if cmd == "fmt" => {
            let out = std::fs::read(file)
                .map_err(|e| e.to_string())
                .and_then(|bytes| zedc::format::format_source(&bytes));
            match out {
                Ok(text) => print!("{text}"),
                Err(e) => {
                    eprintln!("{file}:{e}");
                    return ExitCode::FAILURE;
                }
            }
        }
        [cmd, ..] if cmd == "run" || cmd == "replay" => {
            let (mut stdin, mut stdout, mut stderr) =
                (std::io::stdin(), std::io::stdout(), std::io::stderr());
            return ExitCode::from(zedc::run::command(
                &args,
                &mut stdin,
                &mut stdout,
                &mut stderr,
            ));
        }
        [cmd, files @ ..] if cmd == "test" => {
            let (mut stdout, mut stderr) = (std::io::stdout(), std::io::stderr());
            return ExitCode::from(zedc::testing::command(files, &mut stdout, &mut stderr));
        }
        _ => {
            eprintln!(
                "usage: zedc [fmt <file> | run <file> … | replay <file> <record> … | test <file> …]"
            );
            return ExitCode::from(2);
        }
    }
    ExitCode::SUCCESS
}
