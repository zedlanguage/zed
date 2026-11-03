//! `ref NN INPUT` prints reference program NN's output on INPUT. `ref --write` rewrites the
//! `.out` file of every corpus input from its reference program.

use std::process::ExitCode;

use zed_corpus_ref::run;

fn write_all() -> Result<(), String> {
    let corpus = concat!(env!("CARGO_MANIFEST_DIR"), "/..");
    for entry in std::fs::read_dir(corpus).map_err(|e| format!("{corpus}: {e}"))? {
        let path = entry.map_err(|e| format!("{corpus}: {e}"))?.path();
        let name = path.to_string_lossy();
        let Some(base) = name.strip_suffix(".in") else {
            continue;
        };
        let file = path.file_name().expect("a directory entry has a name");
        let number = &file.to_string_lossy()[..2];
        let (out, result) = run(number, &name);
        result.map_err(|e| format!("{name}: {e}"))?;
        let dest = format!("{base}.out");
        std::fs::write(&dest, out).map_err(|e| format!("{dest}: {e}"))?;
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match &args[..] {
        [flag] if flag == "--write" => write_all(),
        [number, input] => {
            let (out, result) = run(number, input);
            print!("{out}");
            result
        }
        _ => Err("usage: ref NN INPUT, or ref --write".into()),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
