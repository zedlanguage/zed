//! `zedc run --suppress`, run as a user runs it, from a directory of the user's (items
//! DIAG-suppress and DIAG-suppress-rest, DESIGN.md sec:diagnostics): a warning's address names
//! its file by the path from the directory zedc runs in, so a tree moved or copied elsewhere and
//! run from the same place in it prints the same addresses, and an address printed in one copy
//! suppresses the warning in the other. `crates/zed-native/Cargo.toml` names this test, since
//! only a test of that package can name the executable and set the directory it runs in.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// A program whose one warning is at `area`, 4:10.
const AREA: &str = "half(positional x) = x div 2 test { 10 -> 5, 7 -> 3 }\n\
                    main(stdin: Lines) -> (stdout: Lines) {\n  side = 3037000500;\n  \
                    area = side * side;\n  stdout <- String(0);\n}\n";

/// The directory `copy` of this test, holding `src/area.zed`, under the test target's scratch
/// directory; the file is overwritten by each run, never deleted.
fn tree(copy: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("suppress_binary")
        .join(copy);
    std::fs::create_dir_all(d.join("src")).unwrap();
    std::fs::write(d.join("src").join("area.zed"), AREA).unwrap();
    d
}

/// `zedc run <words>` with no input, run in the directory `dir`: status, stdout and stderr.
fn zedc_in(dir: &Path, words: &[&str]) -> (Option<i32>, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("run")
        .args(words)
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    (
        out.status.code(),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

/// The one address printed in `err`.
fn address(err: &str) -> String {
    let all: Vec<&str> = err
        .lines()
        .filter_map(|l| l.strip_prefix("  address: "))
        .collect();
    assert_eq!(all.len(), 1, "{err}");
    all[0].to_string()
}

#[test]
fn a_copied_tree_run_from_the_same_place_prints_the_same_address() {
    let (one, two) = (tree("one"), tree("two"));
    let (status, out, err) = zedc_in(&one, &["src/area.zed"]);
    assert_eq!((status, out.as_str()), (Some(0), "0\n"), "{err}");
    assert!(err.starts_with("src/area.zed:4:10: `area` widens"), "{err}");
    let a = address(&err);
    assert_eq!(address(&zedc_in(&two, &["src/area.zed"]).2), a);
    // The address printed in one copy suppresses the warning in the other.
    assert_eq!(
        zedc_in(&two, &["src/area.zed", "--suppress", &a]),
        (Some(0), "0\n".into(), String::new())
    );
    // Another path to the same file from the same directory gives the same address.
    assert_eq!(address(&zedc_in(&one, &["../one/./src/area.zed"]).2), a);
}

#[test]
fn the_address_depends_on_the_directory_zedc_runs_in() {
    // The rule chosen: the file's part of the address is its path from the current directory,
    // so the same file run from another directory has another address, and that address
    // names nothing when zedc runs from the first.
    let one = tree("elsewhere");
    let a = address(&zedc_in(&one, &["src/area.zed"]).2);
    let inner = address(&zedc_in(&one.join("src"), &["area.zed"]).2);
    assert_ne!(inner, a);
    let (status, _, err) = zedc_in(&one, &["src/area.zed", "--suppress", &inner]);
    assert_eq!(status, Some(0));
    assert!(
        err.ends_with(&format!(
            "src/area.zed: `--suppress {inner}`: no diagnostic has this address\n"
        )),
        "{err}"
    );
}
