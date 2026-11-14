//! The zedc executable, run as a user runs it, on a value deeper than the minimum of 20,000
//! nested calls (DESIGN.md step M0.11), under the usual 8 MiB stack limit (author P178: an
//! unusual size is a benchmark). `crates/zed-native/Cargo.toml` names this test program, since
//! only a test of that package can name the executable.

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

main(m: MainArgs) {
  x = build(build, 1250, 0);
  m.stdout <- if x == x { "same" } else { "different" };
}
"#;

/// Sets this process's soft stack limit, which a child inherits, to [`STACK_LIMIT`], or to the
/// hard limit where that is lower, so that the test holds whatever limit it was started with
/// (`ulimit -s unlimited` included). The test harness's threads have their own fixed stacks,
/// and its main thread only waits, so the lower limit does not reach the tests themselves.
fn limit_stack() {
    use rustix::process::{Resource, Rlimit, getrlimit, setrlimit};
    let Rlimit { maximum, .. } = getrlimit(Resource::Stack);
    let current = maximum.map_or(STACK_LIMIT, |hard| hard.min(STACK_LIMIT));
    setrlimit(
        Resource::Stack,
        Rlimit {
            current: Some(current),
            maximum,
        },
    )
    .expect("a soft limit at most the hard limit is accepted");
}

#[test]
fn zedc_compares_a_value_20000_deep_on_an_ordinary_stack() {
    limit_stack();
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
