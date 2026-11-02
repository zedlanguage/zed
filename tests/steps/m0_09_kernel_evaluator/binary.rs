//! The zedc executable, run as a user runs it, on a value deeper than the minimum of 20,000
//! nested calls (DESIGN.md step M0.11). `crates/zedc/Cargo.toml` names this test, since only a
//! test of that package can name the executable.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// The largest stack a run may have for this test to prove anything: the usual 8 MiB. Under a
/// larger limit a native recursion would pass.
const STACK_LIMIT: u64 = 1 << 23;

/// `grow` adds 16 levels per call, so that reaching the depth costs few reads of the accumulator:
/// each read copies it (K21 in COMPLEXITY.md).
const PROGRAM: &str = r#"
grow(positional x) = (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, (1, x))))))))))))))));

build(positional f, positional k, positional acc) =
  if k == 0 { acc } else { f(f, k - 1, grow(acc)) };

main(stdin: Lines) -> (stdout: Lines) {
  x = build(build, 1250, 0);
  stdout <- if x == x { "same" } else { "different" };
}
"#;

/// The soft limit on this process's stack, which a child inherits; `None` when unlimited.
fn stack_limit() -> Option<u64> {
    let limits = fs::read_to_string("/proc/self/limits").expect("Linux reports its limits");
    let line = limits
        .lines()
        .find(|l| l.starts_with("Max stack size"))
        .expect("the stack has a limit line");
    let soft = line.split_whitespace().nth(3).expect("a soft limit");
    soft.parse().ok()
}

#[test]
fn zedc_compares_a_value_20000_deep_on_an_ordinary_stack() {
    let limit = stack_limit();
    assert!(
        limit.is_some_and(|l| l <= STACK_LIMIT),
        "this test needs a stack of at most {STACK_LIMIT} bytes and has {limit:?}: \
         run it after `ulimit -s 8192`"
    );
    let name = format!("deep_value_{}.zed", std::process::id());
    let file = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    fs::write(&file, PROGRAM).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("run")
        .arg(&file)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    fs::remove_file(&file).unwrap();
    assert!(
        out.status.success(),
        "{:?}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "same");
}
