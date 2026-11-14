//! `zedc test` prints the widening warnings of each unit it checks, as `zedc run` prints
//! them: on standard error, each as `file:line:col: why` with its derivation, in order of
//! place, before the unit's outcomes, and only for a unit with no rejection.

use std::io::Read;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::Relaxed;

/// Writes the unit `src` as `file` in test directory `name`, under this process's scratch
/// directory, and gives its path. The file is the calling test's alone
/// ([`zed_tests::step_helpers::scratch`]); a test may write it again.
///
/// The directory was shared by every process of this test binary, and `std::fs::write`
/// empties a file and then fills it, so a process could check a file another had just
/// emptied: `a_batch_prints_what_each_file_prints_alone` failed so (TEST-l01_29-widen-flake; 5
/// of 50 runs in each of three processes at once, 0 of 50 alone). Commit 4167668eb wrote each
/// text to a file of its own and renamed it over `file`, which still let a second process read
/// the first text of a test that writes one name twice; a directory per process
/// (TEST-fixture-write-race) ends that. The rename stays: a reader holding the file open while
/// its test writes it again, `a_unit_written_again_leaves_a_reader_the_whole_old_text`, keeps
/// the whole old text, as a POSIX `rename` within one directory replaces the name in one step,
/// at the cost of one more file created per write.
pub(super) fn unit(name: &str, file: &str, src: &str) -> String {
    static WRITES: AtomicU64 = AtomicU64::new(0);
    let path = zed_tests::step_helpers::scratch(format!("l01_29_widen_test/{name}/{file}"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    let own = path.with_file_name(format!(".{file}.{}", WRITES.fetch_add(1, Relaxed)));
    std::fs::write(&own, src).unwrap();
    std::fs::rename(&own, &path).unwrap();
    path.display().to_string()
}

/// `zedc test --addresses <files>`: its status, standard output and standard error.
fn test(files: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = std::iter::once(&"--addresses")
        .chain(files)
        .map(|a| a.to_string())
        .collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::testing::command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// `zedc run <file> --addresses` with no input: its status and standard error.
fn run(file: &str) -> (u8, String) {
    let args = ["run", file, "--addresses"];
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut "".as_bytes(), &mut out, &mut err);
    (status, String::from_utf8(err).unwrap())
}

/// A unit with a table that passes and a `main` whose body binds `lines` and prints `0`.
pub(super) fn checked_program(lines: &str) -> String {
    format!(
        "half(positional x) = x div 2 test {{ 10 -> 5, 7 -> 3 }}\n\
         main(m: MainArgs) {{\n{lines}  m.stdout <- String(0);\n}}\n"
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
{file}:4:10: `area` widens past a machine word: this `*` of an i64 and an i64 gives a big integer.
  [1] 4:10: this `*` gives 9223372037000250000, past i64
      4 |   area = side * side;
        |          ^^^^ [2]
        |          ^^^^^^^^^^^ [1, 6]
        |                 ^^^^ [5]
  [2] 4:10: `side` is 3037000500 here
  [3] 3:10: `side` is defined as this expression, 3037000500
      3 |   side = 3037000500;
        |          ^^^^^^^^^^
  [4] 3:10: this literal is 3037000500
  [5] 4:17: `side` is 3037000500 here
  [6] 4:10: repair: if wrapping arithmetic is meant, reduce the value with `mod 2^k`, k at most 64
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
                 gives a big integer."
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
                 i64 gives a big integer."
            ),
            format!(
                "{file}:5:11: `taxed` widens past a machine word: this `*` of an i64 and an \
                 i64 gives a big integer."
            ),
            format!(
                "{file}:6:11: `total` widens past a machine word: this `*` of an i64 and an \
                 i64 gives a big integer."
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

/// The file of a unit of `m` warnings, [`many_squares`], written.
pub(super) fn a_unit_of_warnings(m: usize) -> String {
    unit("scale", &format!("{m}.zed"), &many_squares(m))
}

/// `zedc test` on `file`, a [`a_unit_of_warnings`] of `m`, passes and prints each warning once.
pub(super) fn many_warnings_printed(file: &str, m: usize) {
    let (status, _, err) = test(&[file]);
    assert_eq!(status, 0);
    assert_eq!(firsts(&err).len(), m, "{err}");
}

/// Units of 1, 2 and 5 warnings (`bench::widen_test` times 400 and 3200).
#[test]
fn printing_many_warnings() {
    for m in [1, 2, 5] {
        many_warnings_printed(&a_unit_of_warnings(m), m);
    }
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
         main(m: MainArgs) {{\n  side = {side};\n  \
         area = side * side;\n  m.stdout <- {push};\n}}\n"
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
    assert!(why.starts_with("5:15: "), "{why}");
    assert!(!why.contains("widens"), "{why}");
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 1, "{out}");
    assert!(out.contains(&format!("{file}:5:15: ")), "{out}");
    assert!(!out.contains("widens"), "{out}");
    assert_eq!(err, "");
    let (status, err) = run(&file);
    assert_eq!(status, 1);
    assert!(err.contains(&format!("{file}:5:15: ")), "{err}");
    assert!(!err.contains("widens"), "{err}");

    // Repaired, the unit is accepted and the notice is reported.
    let src = area_program(REPAIRED_PUSH);
    let file = unit("alone", "repaired.zed", &src);
    let program = zedc::run::load(src.as_bytes()).expect("the repair is accepted");
    let notices: Vec<(usize, usize)> = program.warnings().iter().map(|w| (w.line, w.col)).collect();
    assert_eq!(notices, [(4, 10)]);
    let notice = format!(
        "{file}:4:10: `area` widens past a machine word: this `*` of an i64 and an i64 gives a \
         big integer."
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

/// The files of a batch of `m` units, each with its own side, the even ones rejected and the
/// odd ones repaired, written.
pub(super) fn a_batch_of_halves(m: usize) -> Vec<String> {
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
}

/// `zedc test` on `files`, a [`a_batch_of_halves`] of an even `m`: it fails, each rejected unit
/// prints its rejection alone and each repaired one its notice.
pub(super) fn a_batch_of_halves_printed(files: &[String], m: usize) {
    let args: Vec<&str> = files.iter().map(String::as_str).collect();
    let (status, out, err) = test(&args);
    assert_eq!(status, 1);
    assert_eq!(firsts(&err).len(), m / 2, "{err}");
    assert_eq!(out.matches(":5:15: ").count(), m / 2, "{out}");
}

/// Batches of 2 and 4 units (`bench::widen_test` times 40 and 320).
#[test]
fn a_batch_of_rejected_and_repaired_units() {
    for m in [2, 4] {
        a_batch_of_halves_printed(&a_batch_of_halves(m), m);
    }
}

/// A unit whose `main` has a parameter other than `m: MainArgs` is rejected: `zedc test` reports the rejection alone, as `zedc run` does, and no notice.
#[test]
fn a_unit_whose_main_ports_are_rejected_prints_no_warning() {
    let src = "half(positional x) = x div 2 test { 10 -> 5, 7 -> 3 }\n\
               main(stdin: int) {\n  side = 3037000500;\n  \
               area = side * side;\n  m.stdout <- String(area);\n}\n";
    let file = unit("ports", "ports.zed", src);
    let why = zedc::run::load(src.as_bytes())
        .err()
        .expect("the port `stdin: int` is rejected");
    assert!(!why.contains("widens"), "{why}");
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 1, "{out}");
    assert!(
        out.contains(&format!(
            "{file}:2:6: {}",
            zed_tests::main_param_message("stdin", "int")
        )),
        "{out}"
    );
    assert_eq!(err, "");
    let (status, err) = run(&file);
    assert_eq!(status, 1);
    assert!(!err.contains("widens"), "{err}");
}

/// A unit written again leaves a reader of the file as it was with the whole old text, and the
/// name with the whole new one: a program reading the file while its test writes it again
/// reads one text or the other, never an emptied file (see [`unit`]).
#[test]
fn a_unit_written_again_leaves_a_reader_the_whole_old_text() {
    let file = format!("{}.zed", std::process::id());
    let path = unit("rewrite", &file, "main = 1;\n");
    let mut reader = std::fs::File::open(&path).unwrap();
    unit("rewrite", &file, "main = 22;\n");
    let mut read = String::new();
    reader.read_to_string(&mut read).unwrap();
    assert_eq!(read, "main = 1;\n");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "main = 22;\n");
    std::fs::remove_file(&path).unwrap();
}
