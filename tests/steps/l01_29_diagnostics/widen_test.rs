//! `zedc test` prints the widening warnings of each unit it checks, as `zedc run` prints
//! them: on standard error, each as `file:line:col: why` with its derivation, in order of
//! place, before the unit's outcomes, and only for a unit with no rejection.

use std::path::PathBuf;

use zed_tests::scaling;

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted.
fn dir(name: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l01_29_widen_test")
        .join(name);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Writes the unit `src` as `file` in test directory `name` and gives its path.
pub(super) fn unit(name: &str, file: &str, src: &str) -> String {
    let path = dir(name).join(file);
    std::fs::write(&path, src).unwrap();
    path.display().to_string()
}

/// `zedc test <files>`: its status, standard output and standard error.
fn test(files: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = files.iter().map(|a| a.to_string()).collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::testing::command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// `zedc run <file>` with no input: its status and standard error.
fn run(file: &str) -> (u8, String) {
    let args = vec!["run".to_string(), file.to_string()];
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut "".as_bytes(), &mut out, &mut err);
    (status, String::from_utf8(err).unwrap())
}

/// A unit with a table that passes and a `main` whose body binds `lines` and prints `0`.
pub(super) fn checked_program(lines: &str) -> String {
    format!(
        "half(positional x) = x div 2 test {{ 10 -> 5, 7 -> 3 }}\n\
         main(stdin: Lines) -> (stdout: Lines) {{\n{lines}  stdout <- String(0);\n}}\n"
    )
}

#[test]
fn zedc_test_prints_the_warning_zedc_run_prints() {
    // The area of a square whose side fits in an i64 does not.
    let src = checked_program("  side = 3037000500;\n  area = side * side;\n");
    let file = unit("area", "area.zed", &src);
    let address = zedc::suppress::InFile::of(file.as_ref())
        .unwrap()
        .address(&zedc::run::load(src.as_bytes()).unwrap().warnings()[0]);
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "2 passed, 0 failed, 0 rejection units\n");
    assert_eq!(
        err,
        format!(
            "\
{file}:4:10: `area` widens past a machine word: this `*` of an i64 and an i64 gives a big integer
  [1] 4:10: this `*` gives 9223372037000250000, past i64
      4 |   area = side * side;
        |          ^^^^^^^^^^^
  [2] 4:10: `side` is 3037000500 here
      4 |   area = side * side;
        |          ^^^^
  [3] 3:10: `side` is defined as this expression, 3037000500
      3 |   side = 3037000500;
        |          ^^^^^^^^^^
  [4] 3:10: this literal is 3037000500
  [5] 4:17: `side` is 3037000500 here
      4 |   area = side * side;
        |                 ^^^^
  [6] 4:10: repair: if wrapping arithmetic is meant, reduce the value with `mod 2 ** k`, k at most 64
      4 |   area = side * side;
        |          ^^^^^^^^^^^
  address: {address}
"
        )
    );
    assert_eq!(run(&file), (0, err));
}

#[test]
fn a_unit_with_no_widening_prints_no_warning() {
    let src = checked_program("  side = 3037000499;\n  area = side * side;\n");
    let file = unit("none", "none.zed", &src);
    assert_eq!(
        test(&[&file]),
        (
            0,
            "2 passed, 0 failed, 0 rejection units\n".into(),
            String::new()
        )
    );
    assert_eq!(run(&file), (0, String::new()));
}

#[test]
fn a_unit_without_main_prints_its_warning() {
    // `zedc run` needs a `main`; `zedc test` checks a library unit's warnings all the same.
    let file = unit(
        "library",
        "library.zed",
        "big = 4294967296 * 4294967296;\nsame(positional x) = x test { 1 -> 1 }\n",
    );
    let (status, _, err) = test(&[&file]);
    assert_eq!(status, 0);
    assert_eq!(
        err.lines().next(),
        Some(
            format!(
                "{file}:1:7: `big` widens past a machine word: this `*` of an i64 and an i64 \
                 gives a big integer"
            )
            .as_str()
        )
    );
}

#[test]
fn a_rejected_unit_prints_no_warning() {
    // The widening is not reported when the unit does not compile; its rejection is.
    let file = unit(
        "rejected",
        "rejected.zed",
        "big = 4294967296 * 4294967296;\nsame(positional x) = x test { 1 -> y }\n",
    );
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 1);
    assert!(out.contains("`y`"), "{out}");
    assert_eq!(err, "");
}

/// The first line of each warning in the standard error `err`.
fn firsts(err: &str) -> Vec<&str> {
    err.lines().filter(|l| !l.starts_with(' ')).collect()
}

#[test]
fn several_warnings_keep_their_order() {
    // Prices in cents of three large orders, each past the word.
    let src = checked_program(
        "  units = 4294967296;\n  cents = units * 4294967296;\n  \
         taxed = (units * 3) * 3037000500;\n  total = 3037000500 * 3037000500;\n",
    );
    let file = unit("order", "order.zed", &src);
    let (status, _, err) = test(&[&file]);
    assert_eq!(status, 0);
    assert_eq!(
        firsts(&err),
        [
            format!(
                "{file}:4:11: `cents` widens past a machine word: this `*` of an i64 and an \
                 i64 gives a big integer"
            ),
            format!(
                "{file}:5:11: `taxed` widens past a machine word: this `*` of an i64 and an \
                 i64 gives a big integer"
            ),
            format!(
                "{file}:6:11: `total` widens past a machine word: this `*` of an i64 and an \
                 i64 gives a big integer"
            ),
        ]
    );
    assert_eq!(run(&file), (0, err));
}

#[test]
fn a_batch_prints_what_each_file_prints_alone() {
    let a = unit(
        "batch",
        "a.zed",
        &checked_program("  area = 3037000500 * 3037000500;\n"),
    );
    let b = unit(
        "batch",
        "b.zed",
        &checked_program("  quiet = 3037000499 * 3037000499;\n"),
    );
    let c = unit(
        "batch",
        "c.zed",
        &checked_program("  x = 4294967296;\n  y = x * x;\n  z = x * x * 3;\n"),
    );
    let alone: String = [&a, &b, &c].iter().map(|f| test(&[f]).2).collect();
    assert_eq!(firsts(&alone).len(), 3);
    assert_eq!(test(&[&a, &b, &c]).2, alone);
    // A file given twice is printed twice, from the one compilation the batch keeps.
    let twice = test(&[&c, &c]).2;
    assert_eq!(twice, test(&[&c]).2.repeat(2));
}

/// A unit with a table and a `main` of `n` bindings, each squaring a large literal.
pub(super) fn many_squares(n: usize) -> String {
    let lines: String = (0..n)
        .map(|i| format!("  a{i} = {} * 3037000500;\n", 3037000500 + i))
        .collect();
    checked_program(&lines)
}

/// `zedc test` on a unit of `n` warnings, each written once: the run, compilation and
/// printing together, is within n log n. The files are written before the timing.
#[test]
fn printing_many_warnings_scales() {
    let n = 400;
    let files: Vec<(usize, String)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, unit("scale", &format!("{m}.zed"), &many_squares(m))))
        .collect();
    scaling::check("zedc test on a unit of n warnings", n, |m| {
        let file = &files.iter().find(|(k, _)| *k == m).expect("a size").1;
        let (status, _, err) = test(&[file]);
        assert_eq!(status, 0);
        assert_eq!(firsts(&err).len(), m);
    });
}

/// A unit with a table that passes and a `main` that squares a side past the word and pushes
/// `push`: one widening notice, at 4:10.
fn area_program(push: &str) -> String {
    sized_area(3037000500, push)
}

/// `area_program` with the side `side`.
fn sized_area(side: u64, push: &str) -> String {
    format!(
        "half(positional x) = x div 2 test {{ 10 -> 5, 7 -> 3 }}\n\
         main(stdin: Lines) -> (stdout: Lines) {{\n  side = {side};\n  \
         area = side * side;\n  stdout <- {push};\n}}\n"
    )
}

/// The push that concatenates a number to a string, which is rejected, and its repair.
const REJECTED_PUSH: &str = "\"area: \" ++ area";
const REPAIRED_PUSH: &str = "\"area: \" ++ String(area)";

#[test]
fn a_rejection_is_reported_alone_and_its_repair_reports_the_notice() {
    // Step L1.29a: one rejection and one widening notice in one unit give the rejection
    // alone, from every entry point.
    let src = area_program(REJECTED_PUSH);
    let file = unit("alone", "rejected.zed", &src);
    let why = zedc::run::load(src.as_bytes())
        .err()
        .expect("the concatenation is rejected");
    assert!(why.starts_with("5:13: "), "{why}");
    assert!(!why.contains("widens"), "{why}");
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 1, "{out}");
    assert!(out.contains(&format!("{file}:5:13: ")), "{out}");
    assert!(!out.contains("widens"), "{out}");
    assert_eq!(err, "");
    let (status, err) = run(&file);
    assert_eq!(status, 1);
    assert!(err.contains(&format!("{file}:5:13: ")), "{err}");
    assert!(!err.contains("widens"), "{err}");

    // Repaired, the unit is accepted and the notice is reported.
    let src = area_program(REPAIRED_PUSH);
    let file = unit("alone", "repaired.zed", &src);
    let program = zedc::run::load(src.as_bytes()).expect("the repair is accepted");
    let notices: Vec<(usize, usize)> = program.warnings().iter().map(|w| (w.line, w.col)).collect();
    assert_eq!(notices, [(4, 10)]);
    let notice = format!(
        "{file}:4:10: `area` widens past a machine word: this `*` of an i64 and an i64 gives a \
         big integer"
    );
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 0, "{out}");
    assert_eq!(firsts(&err), [notice.as_str()]);
    assert_eq!(run(&file), (0, err));
}

/// Every corpus and step unit that `zedc test` finds rejected prints no warning.
#[test]
fn no_rejected_unit_of_the_corpus_prints_a_warning() {
    let mut rejected = 0;
    for (name, text) in super::order::units() {
        if zedc::run::load(text.as_bytes()).is_ok() {
            continue;
        }
        rejected += 1;
        let file = unit("corpus", "unit.zed", &text);
        let (_, _, err) = test(&[&file]);
        assert_eq!(err, "", "{name}");
    }
    assert!(rejected >= 5, "{rejected} rejected units");
}

/// `zedc test` on a batch of `n` units, each with its own side, half rejected and half
/// repaired: each rejected unit prints its rejection alone and each repaired one its notice,
/// in work linear in the units. The files are written before the timing.
#[test]
fn a_batch_of_rejected_and_repaired_units_scales() {
    let n = 40;
    let batch = |m: usize| -> Vec<String> {
        (0..m)
            .map(|i| {
                let push = if i % 2 == 0 {
                    REJECTED_PUSH
                } else {
                    REPAIRED_PUSH
                };
                let side = 3037000500 + i as u64;
                unit(
                    &format!("halves{m}"),
                    &format!("{i}.zed"),
                    &sized_area(side, push),
                )
            })
            .collect()
    };
    let batches = [batch(n), batch(scaling::FACTOR * n)];
    scaling::check_order("zedc test on a batch of n units", n, 1, |m| {
        let files = &batches[usize::from(m != n)];
        let args: Vec<&str> = files.iter().map(String::as_str).collect();
        let (status, out, err) = test(&args);
        assert_eq!(status, 1);
        assert_eq!(firsts(&err).len(), m / 2);
        assert_eq!(out.matches(":5:13: ").count(), m / 2);
    });
}

/// A unit whose front end accepts it and whose `main` has a port that `zedc run` refuses is
/// rejected: `zedc test` reports the rejection alone, as `zedc run` does, and no notice.
#[test]
fn a_unit_whose_main_ports_are_rejected_prints_no_warning() {
    let src = "half(positional x) = x div 2 test { 10 -> 5, 7 -> 3 }\n\
               main(stdin: int) -> (stdout: Lines) {\n  side = 3037000500;\n  \
               area = side * side;\n  stdout <- String(area);\n}\n";
    let file = unit("ports", "ports.zed", src);
    let why = zedc::run::load(src.as_bytes())
        .err()
        .expect("the port `stdin: int` is rejected");
    assert!(!why.contains("widens"), "{why}");
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 1, "{out}");
    assert!(
        out.contains(&format!("{file}:2:1: port `stdin` of `main`")),
        "{out}"
    );
    assert_eq!(err, "");
    let (status, err) = run(&file);
    assert_eq!(status, 1);
    assert!(!err.contains("widens"), "{err}");
}
