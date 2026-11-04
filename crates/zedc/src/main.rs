//! The `zedc` command: `zedc fmt <file>` writes the file in the formatter's layout to standard
//! output; `zedc run` and `zedc replay` run a program ([`zedc::run::command`]); `zedc test`
//! runs the tests of units ([`zedc::testing::command`]); with no arguments it prints its
//! version.

use std::ffi::OsString;
use std::process::ExitCode;

const USAGE: &str =
    "usage: zedc [fmt <file> | run <file> … | replay <file> <record> … | test [--mutate] <file> …]";

fn main() -> ExitCode {
    // The words stay as the system gives them: a `CommandLine` argument need not be UTF-8 to
    // reach `zedc run`, which names the one that is not (step L1.19a).
    let os: Vec<OsString> = std::env::args_os().skip(1).collect();
    if matches!(os.first(), Some(cmd) if cmd == "run" || cmd == "replay") {
        let (mut stdin, mut stdout, mut stderr) =
            (std::io::stdin(), std::io::stdout(), std::io::stderr());
        return ExitCode::from(zedc::run::command(
            &os,
            &mut stdin,
            &mut stdout,
            &mut stderr,
        ));
    }
    let Some(args) = os
        .into_iter()
        .map(OsString::into_string)
        .collect::<Result<Vec<String>, _>>()
        .ok()
    else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
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
        [cmd, files @ ..] if cmd == "test" => {
            let (mut stdout, mut stderr) = (std::io::stdout(), std::io::stderr());
            return ExitCode::from(zedc::testing::command(files, &mut stdout, &mut stderr));
        }
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    }
    ExitCode::SUCCESS
}
