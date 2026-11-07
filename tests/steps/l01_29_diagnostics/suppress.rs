//! Items DIAG-suppress and DIAG-suppress-rest (DESIGN.md sec:diagnostics): each diagnostic
//! prints its address, the same on every run of the same file from the same directory and
//! different in each file; `--suppress <address>` leaves that warning unprinted and the program
//! unchanged; naming a rejection is an error and the run still fails; an address that names
//! nothing is reported.

use std::path::{Component, Path, PathBuf};

use zed_tests::scaling;
use zedc::address::ContentAddress;
use zedc::front::Diagnostic;
use zedc::run::{load, load_file};
use zedc::suppress::{InFile, Suppress};

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

/// The address the first warning of the program `src`, read from `file`, prints.
fn address_in(file: &str, src: &str) -> String {
    InFile::of(Path::new(file))
        .unwrap()
        .address(&load(src.as_bytes()).unwrap().warnings()[0])
        .to_string()
}

#[test]
fn a_warning_prints_the_same_address_on_every_run() {
    let src = area();
    let file = unit("suppress", "same.zed", &src);
    let (status, _, first) = zedc(&["run", &file]);
    assert_eq!(status, 0);
    let want = address_in(&file, &src);
    assert_eq!(printed(&first), [want.as_str()]);
    // The address follows the warning's derivation, on a line of its own.
    assert!(
        first.ends_with(&format!("^^^^^^^^^^^\n  address: {want}\n")),
        "{first}"
    );
    assert_eq!(zedc(&["run", &file]).2, first);
    // A line added above, in the same file, moves the warning to line 5 and leaves its address.
    unit("suppress", "same.zed", &format!("// a comment\n{src}"));
    let (_, _, err) = zedc(&["run", &file]);
    assert!(err.contains(":5:10: `area` widens"), "{err}");
    assert_eq!(printed(&err), [want.as_str()]);
    // So does a function added below `main`.
    unit(
        "suppress",
        "same.zed",
        &format!("{src}third(positional x) = x div 3 test {{ 9 -> 3 }}\n"),
    );
    assert_eq!(printed(&zedc(&["run", &file]).2), [want.as_str()]);
}

#[test]
fn the_same_warning_in_two_files_has_two_addresses() {
    // One text in four files: two names in one directory, and one name in two directories.
    let src = area();
    let files = [
        unit("suppress", "first.zed", &src),
        unit("suppress", "second.zed", &src),
        unit("suppress/left", "copy.zed", &src),
        unit("suppress/right", "copy.zed", &src),
    ];
    let names: Vec<&str> = files.iter().map(String::as_str).collect();
    let (status, out, err) = zedc_test(&names);
    assert_eq!(
        (status, out.as_str()),
        (0, "8 passed, 0 failed, 0 rejection units\n")
    );
    let all = printed(&err);
    assert_eq!(all.len(), 4, "{err}");
    assert_eq!(
        all.iter().collect::<std::collections::HashSet<_>>().len(),
        4,
        "{err}"
    );
    for (file, a) in files.iter().zip(&all) {
        // Checking each file alone prints the address checking them together prints.
        assert_eq!(printed(&zedc(&["run", file]).2), [*a]);
        assert_eq!(printed(&zedc_test(&[file]).2), [*a]);
        assert_eq!(*a, address_in(file, &src));
    }
    // Suppressing the third file's warning hides it and no other.
    let mut words = vec!["--suppress", all[2]];
    words.extend(&names);
    let (status, _, rest) = zedc_test(&words);
    assert_eq!(status, 0);
    assert_eq!(printed(&rest), [all[0], all[1], all[3]]);
    assert!(!rest.contains(&files[2]), "{rest}");
    assert!(
        rest.contains(&format!("{}:4:10: `area` widens", files[3])),
        "{rest}"
    );
}

/// The path of `to`, an absolute path, from the current directory, with `..` for each part of
/// the current directory below the parts the two share.
fn relative(to: &Path) -> PathBuf {
    let here = std::env::current_dir().unwrap().canonicalize().unwrap();
    let to = to.canonicalize().unwrap();
    let shared = here
        .components()
        .zip(to.components())
        .take_while(|(a, b)| a == b)
        .count();
    let mut path: PathBuf = here
        .components()
        .skip(shared)
        .map(|_| Component::ParentDir)
        .collect();
    path.extend(to.components().skip(shared));
    path
}

#[test]
fn a_file_named_by_several_paths_has_one_address() {
    // The rule: a file's part of the address is its path from the current directory once
    // every link and every `.` and `..` step is resolved, so any path to it gives the same.
    let src = area();
    let file = unit("suppress/paths", "one.zed", &src);
    let dir = Path::new(&file).parent().unwrap();
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    let link = dir.join("link.zed");
    if std::fs::symlink_metadata(&link).is_err() {
        std::os::unix::fs::symlink("one.zed", &link).unwrap();
    }
    let paths = [
        file.clone(),
        dir.join(".").join("one.zed").display().to_string(),
        dir.join("sub")
            .join("..")
            .join("one.zed")
            .display()
            .to_string(),
        link.display().to_string(),
        relative(Path::new(&file)).display().to_string(),
    ];
    assert!(paths[4].starts_with(".."), "{}", paths[4]);
    let names: Vec<&str> = paths.iter().map(String::as_str).collect();
    let (status, _, err) = zedc_test(&names);
    assert_eq!(status, 0);
    let want = address_in(&file, &src);
    assert_eq!(printed(&err), [want.as_str(); 5]);
    // The one address hides the warning under every path.
    let mut words = vec!["--suppress", &want];
    words.extend(&names);
    assert_eq!(
        zedc_test(&words),
        (
            0,
            "10 passed, 0 failed, 0 rejection units\n".into(),
            String::new()
        )
    );
}

#[test]
fn a_file_whose_name_has_spaces_and_other_characters_round_trips() {
    // The address is hex, whatever the path holds, so it needs no quoting.
    let file = unit("suppress/odd name", "a b, ü & $x 'q'.zed", &area());
    let (status, out, err) = zedc(&["run", &file]);
    assert_eq!(status, 0);
    let a = printed(&err)[0].to_string();
    assert!(err.starts_with(&format!("{file}:4:10:")), "{err}");
    assert_eq!(
        zedc(&["run", &file, "--suppress", &a]),
        (0, out, String::new())
    );
    assert_eq!(zedc_test(&["--suppress", &a, &file]).2, "");
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
            let at = InFile::of(Path::new(&file)).unwrap();
            let mut words = vec!["run".to_string(), file];
            for w in load(src.as_bytes()).unwrap().warnings() {
                words.push("--suppress".into());
                words.push(at.address(w).to_string());
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
        assert!(warnings.iter().all(|w| suppress.hides(w.address)));
        assert!(suppress.unmatched().is_empty());
    });
}
