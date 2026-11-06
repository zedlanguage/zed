//! The `zedc` command: `zedc fmt <file>` writes the file in the formatter's layout to standard
//! output; `zedc run` and `zedc replay` run a program ([`zedc::run::command`]); `zedc build`
//! compiles one to an executable ([`zed_native::link::command`]); `zedc test` runs the tests of
//! units ([`zedc::testing::command`]); with no arguments it prints its version. `zedc --report`
//! before any of these runs it and then writes to standard error the instructions and bytes of
//! its work by stage, unit and definition ([`zedc::work`]).
//!
//! It is a target of the package `zed-native`, which `zedc build` needs and which depends on
//! `zedc`.

use std::ffi::OsString;
use std::process::ExitCode;

// The global allocator of `zed-alloc-count` counts the bytes `--report` reports. It is linked
// into this executable only, not into the runtime library `zedc build` links into programs.
use zed_alloc_count as _;

const USAGE: &str = "usage: zedc [--report] [fmt <file> | run <file> … | replay <file> <record> … | \
     build <file> -o <out> … | test [--mutate] [--suppress <address> …] <file> …]";

fn main() -> ExitCode {
    // The words stay as the system gives them: a `CommandLine` argument need not be UTF-8 to
    // reach `zedc run`, which names the one that is not (step L1.19a).
    let mut os: Vec<OsString> = std::env::args_os().skip(1).collect();
    if os.first().is_some_and(|w| w == "--report") {
        os.remove(0);
        let (counter, why) = counter();
        let (status, report) = zedc::work::with(counter, || command(os));
        eprint!("{report}");
        if let Some(why) = why {
            eprintln!("instructions are not counted: {why}");
        }
        return ExitCode::from(status);
    }
    ExitCode::from(command(os))
}

/// Runs the command `os`, the words after `zedc`, and gives its exit status.
fn command(os: Vec<OsString>) -> u8 {
    if matches!(os.first(), Some(cmd) if cmd == "run" || cmd == "replay") {
        let (mut stdin, mut stdout, mut stderr) =
            (std::io::stdin(), std::io::stdout(), std::io::stderr());
        return zedc::run::command(&os, &mut stdin, &mut stdout, &mut stderr);
    }
    let Some(args) = os
        .into_iter()
        .map(OsString::into_string)
        .collect::<Result<Vec<String>, _>>()
        .ok()
    else {
        eprintln!("{USAGE}");
        return 2;
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
                    return 1;
                }
            }
        }
        // The link names the system libraries of Linux; another host waits for PORTABLE-rt.
        #[cfg(target_os = "linux")]
        [cmd, rest @ ..] if cmd == "build" => {
            let tools = zed_native::link::Toolchain::from_env();
            return zed_native::link::command(rest, &tools, &mut std::io::stderr());
        }
        [cmd, files @ ..] if cmd == "test" => {
            let (mut stdout, mut stderr) = (std::io::stdout(), std::io::stderr());
            return zedc::testing::command(files, &mut stdout, &mut stderr);
        }
        _ => {
            eprintln!("{USAGE}");
            return 2;
        }
    }
    0
}

/// The counter `--report` reads: the instructions this thread and the threads and processes it
/// starts retire in user mode, from `perf_event_open`, and the bytes this thread allocates, from
/// `zed-alloc-count`, whose count on the main thread holds no other thread's bytes (`zedc`
/// starts none). Where the instructions cannot be counted, they read 0, with the reason.
#[cfg(target_os = "linux")]
fn counter() -> (zedc::work::Counter, Option<String>) {
    use perf_event::Builder;
    use perf_event::events::Hardware;
    match Builder::new(Hardware::INSTRUCTIONS)
        .inherit(true)
        .enabled(true)
        .build()
    {
        Ok(mut c) => {
            let read = move || zedc::work::Work {
                // A counter that opened is read by a `read` of its 8 bytes, which fails only if
                // the descriptor is closed, and `c` holds it open.
                instructions: c.read().expect("reading the open instructions counter"),
                bytes: zed_alloc_count::allocated(),
            };
            (Box::new(read), None)
        }
        Err(e) => (
            Box::new(bytes_only),
            Some(format!(
                "perf_event_open: {e} (kernel.perf_event_paranoid must be 2 or less)"
            )),
        ),
    }
}

/// The counter `--report` reads off Linux: the bytes `zed-alloc-count` counts, those of the whole
/// process there; instructions read 0.
#[cfg(not(target_os = "linux"))]
fn counter() -> (zedc::work::Counter, Option<String>) {
    (
        Box::new(bytes_only),
        Some("zedc reads the instructions counter on Linux only".to_string()),
    )
}

/// The bytes allocated, with instructions 0.
fn bytes_only() -> zedc::work::Work {
    zedc::work::Work {
        instructions: 0,
        bytes: zed_alloc_count::allocated(),
    }
}
