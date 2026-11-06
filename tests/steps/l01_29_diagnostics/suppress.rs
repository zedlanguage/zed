//! Item DIAG-suppress (DESIGN.md sec:diagnostics): each diagnostic prints its address, the
//! same on every run of the same source; `--suppress <address>` leaves that warning unprinted
//! and the program unchanged; naming a rejection is an error and the run still fails; an
//! address that names nothing is reported.

use zed_tests::scaling;
use zedc::address::ContentAddress;
use zedc::front::Diagnostic;
use zedc::run::{load, load_file};
use zedc::suppress::Suppress;

use super::widen_test::{checked_program, many_squares, unit};

/// `zedc <words>` through `zedc::run::command`, with no input: status, stdout and stderr.
fn zedc(words: &[&str]) -> (u8, String, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(words, &mut "".as_bytes(), &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// `zedc test <words>`: status, stdout and stderr.
fn zedc_test(words: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = words.iter().map(|w| w.to_string()).collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::testing::command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// The addresses printed in `err`, in order.
fn printed(err: &str) -> Vec<&str> {
    err.lines()
        .filter_map(|l| l.strip_prefix("  address: "))
        .collect()
}

/// A program whose one warning is at `area`, 4:10.
fn area() -> String {
    checked_program("  side = 3037000500;\n  area = side * side;\n")
}

/// The ZIR of the program in `file`, loaded as `zedc run` and `zedc build` load it with the
/// addresses `words` suppressed, printed; and what was written to standard error.
fn zir(file: &str, words: &[&str]) -> (String, String) {
    let (mut suppress, rest) = Suppress::take(words).unwrap();
    assert!(rest.is_empty());
    let mut err = Vec::new();
    let program = load_file(file, &mut suppress, &mut err).unwrap();
    let g = zedc::zir::lower::lower(&program.term()).unwrap();
    (zedc::zir::text::print(&g), String::from_utf8(err).unwrap())
}

#[test]
fn a_warning_prints_the_same_address_on_every_run() {
    let src = area();
    let file = unit("suppress", "same.zed", &src);
    let (status, _, first) = zedc(&["run", &file]);
    assert_eq!(status, 0);
    let want = load(src.as_bytes()).unwrap().warnings()[0]
        .address
        .to_string();
    assert_eq!(printed(&first), [want.as_str()]);
    // The address follows the warning's derivation, on a line of its own.
    assert!(
        first.ends_with(&format!("^^^^^^^^^^^\n  address: {want}\n")),
        "{first}"
    );
    assert_eq!(zedc(&["run", &file]).2, first);
    // A line added above moves the warning to line 5 and leaves its address.
    let moved = unit("suppress", "moved.zed", &format!("// a comment\n{src}"));
    let (_, _, err) = zedc(&["run", &moved]);
    assert!(err.contains(":5:10: `area` widens"), "{err}");
    assert_eq!(printed(&err), [want.as_str()]);
}

#[test]
fn the_warnings_of_a_unit_have_distinct_addresses() {
    let program = load(many_squares(50).as_bytes()).unwrap();
    let addresses: std::collections::HashSet<ContentAddress> =
        program.warnings().iter().map(|w| w.address).collect();
    assert_eq!(addresses.len(), 50);
}

#[test]
fn suppressing_a_warning_removes_it_and_leaves_the_zir_unchanged() {
    let file = unit("suppress", "hidden.zed", &area());
    let (status, out, err) = zedc(&["run", &file]);
    assert_eq!(status, 0);
    let a = printed(&err)[0].to_string();
    assert_eq!(
        zedc(&["run", &file, "--suppress", &a]),
        (0, out.clone(), String::new())
    );
    let (shown, shown_err) = zir(&file, &[]);
    let (hidden, hidden_err) = zir(&file, &["--suppress", &a]);
    assert_eq!(shown_err, err);
    assert_eq!(hidden_err, "");
    assert_eq!(hidden, shown);
    // `zedc test` leaves it unprinted too, and the checks run as before.
    let (status, out, err) = zedc_test(&["--suppress", &a, &file]);
    assert_eq!(
        (status, out.as_str(), err.as_str()),
        (0, "2 passed, 0 failed, 0 rejection units\n", "")
    );
}

#[test]
fn suppressing_one_of_several_warnings_leaves_the_others() {
    let src = checked_program("  x = 4294967296;\n  y = x * x;\n  z = x * x * 3;\n");
    let file = unit("suppress", "several.zed", &src);
    let (_, _, err) = zedc(&["run", &file]);
    let all = printed(&err);
    assert_eq!(all.len(), 2, "{err}");
    let (_, _, rest) = zedc(&["run", &file, "--suppress", all[0]]);
    assert_eq!(printed(&rest), [all[1]]);
    assert!(rest.starts_with(&format!("{file}:5:")), "{rest}");
}

#[test]
fn suppressing_a_rejection_is_an_error_and_the_run_still_fails() {
    let src = checked_program("  y = missing + 1;\n");
    let file = unit("suppress", "rejected.zed", &src);
    let (status, _, err) = zedc(&["run", &file]);
    assert_eq!(status, 1);
    assert!(err.contains("`missing`"), "{err}");
    let a = printed(&err)[0].to_string();
    let (status, _, refused) = zedc(&["run", &file, "--suppress", &a]);
    assert_eq!(status, 1);
    assert_eq!(
        refused,
        format!(
            "{}{file}:3:7: `--suppress {a}` names a rejection, which cannot be suppressed\n",
            err
        )
    );
    // `zedc test` fails the run in the same way.
    let (status, out, _) = zedc_test(&["--suppress", &a, &file]);
    assert_eq!(status, 1);
    assert!(
        out.contains(&format!("`--suppress {a}` names a rejection")),
        "{out}"
    );
}

#[test]
fn an_address_that_names_nothing_is_reported() {
    let file = unit("suppress", "nothing.zed", &area());
    let (_, _, err) = zedc(&["run", &file]);
    let none = "0".repeat(64);
    let (status, _, more) = zedc(&["run", &file, "--suppress", &none]);
    assert_eq!(status, 0);
    assert_eq!(
        more,
        format!("{err}{file}: `--suppress {none}`: no diagnostic has this address\n")
    );
    let (status, _, more) = zedc_test(&["--suppress", &none, &file]);
    assert_eq!(status, 0);
    assert_eq!(
        more,
        format!("{err}`--suppress {none}`: no diagnostic has this address\n")
    );
}

#[test]
fn a_word_after_suppress_that_is_not_an_address_is_a_usage_error() {
    let file = unit("suppress", "usage.zed", &area());
    let (status, _, err) = zedc(&["run", &file, "--suppress", "abc"]);
    assert_eq!(status, 2);
    assert_eq!(
        err,
        "`--suppress abc`: an address is 64 lowercase hex digits\n"
    );
    let (status, _, err) = zedc(&["run", &file, "--suppress"]);
    assert_eq!(status, 2);
    assert_eq!(
        err,
        "`--suppress` needs an address, 64 lowercase hex digits\n"
    );
    assert_eq!(zedc_test(&["--suppress", "abc", &file]).0, 2);
}

/// `zedc run` on a unit of `n` warnings with every one suppressed: compiling, addressing and
/// matching together are within n log n. The files and the words are made before the timing.
#[test]
fn suppressing_every_warning_scales() {
    let n = 400;
    let runs: Vec<(usize, Vec<String>)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let src = many_squares(m);
            let file = unit("suppress", &format!("scale{m}.zed"), &src);
            let mut words = vec!["run".to_string(), file];
            for w in load(src.as_bytes()).unwrap().warnings() {
                words.push("--suppress".into());
                words.push(w.address.to_string());
            }
            (m, words)
        })
        .collect();
    scaling::check("zedc run suppressing each of n warnings", n, |m| {
        let words = &runs.iter().find(|(k, _)| *k == m).expect("a size").1;
        let words: Vec<&str> = words.iter().map(String::as_str).collect();
        assert_eq!(zedc(&words), (0, "0\n".into(), String::new()));
    });
}

/// `n` warnings with distinct addresses, and the words that suppress every one of them.
fn suppressed(n: usize) -> (Vec<Diagnostic>, Vec<String>) {
    let warnings: Vec<Diagnostic> = (0..n)
        .map(|i| Diagnostic {
            line: i + 1,
            col: 1,
            message: "w".into(),
            steps: Vec::new(),
            row: None,
            address: ContentAddress(*blake3::hash(&i.to_le_bytes()).as_bytes()),
        })
        .collect();
    let words = warnings
        .iter()
        .flat_map(|w| ["--suppress".to_string(), w.address.to_string()])
        .collect();
    (warnings, words)
}

/// Matching `n` suppressions against `n` warnings is O(n): each address is found in a set.
#[test]
fn matching_suppressions_scales() {
    let n = 20_000;
    let sizes = [n, scaling::FACTOR * n].map(|m| (m, suppressed(m)));
    scaling::check_order("matching n suppressions against n warnings", n, 1, |m| {
        let (warnings, words) = &sizes.iter().find(|(k, _)| *k == m).expect("a size").1;
        let words: Vec<&str> = words.iter().map(String::as_str).collect();
        let (mut suppress, rest) = Suppress::take(&words).unwrap();
        assert!(rest.is_empty());
        assert!(warnings.iter().all(|w| suppress.hides(w)));
        assert!(suppress.unmatched().is_empty());
    });
}
