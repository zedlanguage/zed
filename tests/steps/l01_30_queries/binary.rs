//! `zedc --report`, run as a user runs it (plan item TIME-report): the command does what it does
//! without the flag, and then writes to standard error its work by stage, unit and definition,
//! whose rows sum to the total. `crates/zed-native/Cargo.toml` names this test, since only a
//! test of that package can name the executable.
#![cfg(target_os = "linux")]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A directory of its own for this test, under the test target's scratch directory; files in
/// it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("time_report_binary");
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn zedc(args: &[&Path]) -> Output {
    let exe = std::env::current_exe().unwrap();
    let runtime =
        zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
            .unwrap_or_else(|e| panic!("{e}"));
    Command::new(env!("CARGO_BIN_EXE_zedc"))
        .args(args)
        .env("ZED_RUNTIME", runtime)
        .env("CC", "cc")
        .output()
        .unwrap()
}

/// A row of the report: stage, unit, definition, instructions, bytes, computed, cached.
#[derive(Debug, PartialEq)]
struct Row {
    stage: String,
    unit: String,
    definition: String,
    numbers: [u64; 4],
}

/// The rows and the total of the report that ends `stderr`, checking its header and that the
/// rows sum to the total, and whether its instructions were counted.
fn report(stderr: &str) -> (Vec<Row>, [u64; 2], bool) {
    let lines: Vec<&str> = stderr.lines().collect();
    let counted = !lines
        .last()
        .is_some_and(|l| l.starts_with("instructions are not counted: "));
    let end = if counted {
        lines.len()
    } else {
        lines.len() - 1
    };
    let start = lines[..end]
        .iter()
        .position(|l| l.starts_with("stage "))
        .unwrap_or_else(|| panic!("no report in\n{stderr}"));
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    assert_eq!(
        head,
        [
            "stage",
            "unit",
            "definition",
            "instructions",
            "bytes",
            "computed",
            "cached"
        ]
    );
    let number = |w: &str| w.parse::<u64>().unwrap_or_else(|e| panic!("{w}: {e}"));
    let rows: Vec<Row> = lines[start + 1..end - 1]
        .iter()
        .map(|l| {
            let w: Vec<&str> = l.split_whitespace().collect();
            assert_eq!(w.len(), 7, "{l}");
            Row {
                stage: w[0].into(),
                unit: w[1].into(),
                definition: w[2].into(),
                numbers: [number(w[3]), number(w[4]), number(w[5]), number(w[6])],
            }
        })
        .collect();
    let total: Vec<&str> = lines[end - 1].split_whitespace().collect();
    assert_eq!(total[0], "total", "{stderr}");
    let total = [number(total[1]), number(total[2])];
    let sum = |i: usize| rows.iter().map(|r| r.numbers[i]).sum::<u64>();
    assert_eq!([sum(0), sum(1)], total, "{stderr}");
    (rows, total, counted)
}

const FAHRENHEIT: &str = "\
fahrenheit(positional celsius: int) = celsius * 9 div 5 + 32
test { 0 -> 32, 100 -> 212, -40 -> -40 }
";

#[test]
fn a_reported_test_shows_the_second_copy_of_a_unit_as_cached() {
    let d = dir();
    let (a, b) = (d.join("a.zed"), d.join("b.zed"));
    std::fs::write(&a, FAHRENHEIT).unwrap();
    std::fs::write(&b, FAHRENHEIT).unwrap();
    let plain = zedc(&[Path::new("test"), &a, &b]);
    let out = zedc(&[Path::new("--report"), Path::new("test"), &a, &b]);
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(out.stdout, plain.stdout);
    assert!(plain.stderr.is_empty(), "{plain:?}");
    let stderr = String::from_utf8(out.stderr).unwrap();
    let (rows, total, counted) = report(&stderr);
    assert!(total[1] > 0, "{stderr}");
    let test = |unit: &Path| -> Vec<[u64; 4]> {
        let unit = unit.to_str().unwrap();
        rows.iter()
            .filter(|r| r.stage == "test" && r.unit == unit && r.definition == "fahrenheit")
            .map(|r| r.numbers)
            .collect()
    };
    let first = test(&a);
    assert_eq!(first.len(), 1, "{stderr}");
    assert_eq!(first[0][2..], [3, 0], "{stderr}");
    assert!(!counted || first[0][0] > 0, "{stderr}");
    assert_eq!(test(&b), [[0, 0, 0, 3]], "{stderr}");
}

#[test]
fn a_reported_build_shows_lowering_code_generation_and_the_link() {
    let d = dir();
    let src = d.join("hello.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- \"Hello!\";\n}\n").unwrap();
    let exe = d.join("hello");
    // An executable left here by an earlier run would be kept, and its link reported as
    // cached rather than computed; an empty file in its place makes this run link again.
    std::fs::write(&exe, b"").unwrap();
    let out = zedc(&[
        Path::new("--report"),
        Path::new("build"),
        &src,
        Path::new("-o"),
        &exe,
    ]);
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    let (rows, _, counted) = report(&stderr);
    for stage in ["load", "parse", "check", "lower", "codegen", "link"] {
        let row = rows.iter().find(|r| r.stage == stage);
        let row = row.unwrap_or_else(|| panic!("no row {stage} in\n{stderr}"));
        assert_eq!(row.numbers[2], 1, "{stderr}");
        assert!(!counted || row.numbers[0] > 0, "{stderr}");
    }
    let ran = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8(ran.stdout).unwrap(), "Hello!\n");
}

#[test]
fn a_reported_command_that_fails_keeps_its_status_and_still_reports() {
    let out = zedc(&[Path::new("--report"), Path::new("fmt")]);
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(
        stderr.starts_with(
            "`zedc fmt` takes one word after it, the file to print in the standard layout, and \
             was given 0 words. Write `zedc fmt <file>`, once for each file.\n\n\
             The commands of zedc are:\n"
        ),
        "{stderr}"
    );
    let (rows, _, _) = report(&stderr);
    assert_eq!(
        rows.len(),
        1,
        "only the work outside every stage:\n{stderr}"
    );
}
