//! Item DIAG-addr-rest (DESIGN.md sec:diagnostics): every rejection prints its address, the
//! address of the top-level declaration it concerns, in the form every diagnostic prints it:
//! a rejection reported by `zedc test`, a problem of a package (`zedc::unit::Package`), and a
//! `main` that `zedc run` refuses (`zedc::run::program`). Naming any of them with
//! `--suppress` is an error, as naming a front-end rejection is.

use std::path::PathBuf;

use zed_tests::scaling;
use zedc::suppress::{InFile, Suppress};

use super::widen_test::unit;

/// `zedc <words>` through `zedc::run::command`, with no input and `--addresses` after the
/// file: status, stdout and stderr.
fn zedc(words: &[&str]) -> (u8, String, String) {
    let mut words = words.to_vec();
    words.insert(2.min(words.len()), "--addresses");
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&words, &mut "".as_bytes(), &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// `zedc test --addresses <words>`: status, stdout and stderr.
fn zedc_test(words: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = std::iter::once(&"--addresses")
        .chain(words)
        .map(|w| w.to_string())
        .collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::testing::command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// A `Suppress` that suppresses nothing and prints each address, as `--addresses` asks.
fn addressed() -> Suppress {
    Suppress::take(&["--addresses"]).unwrap().0
}

/// The address printed on the line after the line that starts with `place`, in `text`.
fn address_after(text: &str, place: &str) -> String {
    let mut lines = text.lines().skip_while(|l| !l.starts_with(place));
    assert!(
        lines.next().is_some(),
        "no line starts with {place}:\n{text}"
    );
    lines
        .find_map(|l| l.strip_prefix("  address: "))
        .unwrap_or_else(|| panic!("no address after {place}:\n{text}"))
        .to_string()
}

/// The line refusing `--suppress <address>` at `place`, where the error it names is printed.
fn refusal(place: &str, address: &str) -> String {
    format!(
        "{place}: `--suppress {address}` names the error printed above at this place, and an \
         error cannot be suppressed, since the program it rejects cannot be built; only a warning \
         can be. Correct the program as that error describes, or remove `--suppress {address}`."
    )
}

/// The lines of `text` that are addresses.
fn addresses(text: &str) -> Vec<&str> {
    text.lines()
        .filter_map(|l| l.strip_prefix("  address: "))
        .collect()
}

/// A package directory of its own for test `name`, holding `files`, under the test target's
/// scratch directory; files in it are overwritten by each run, never deleted.
fn package(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l01_29_rejection_addresses")
        .join(name);
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// A unit with a table whose `use` names nothing.
const REJECTED: &str = "double(x) = x * 2 test { 1 -> 2 }\nuse(x) = missing + x;\n";

#[test]
fn a_rejection_under_zedc_test_prints_the_address_zedc_run_prints() {
    let file = unit("addresses", "rejected.zed", REJECTED);
    let (status, _, err) = zedc(&["run", &file]);
    assert_eq!(status, 1);
    let place = format!("{file}:2:");
    let a = address_after(&err, &place);
    let (status, out, _) = zedc_test(&[&file]);
    assert_eq!(status, 1, "{out}");
    assert_eq!(address_after(&out, &place), a, "{out}");
    // The row that does not run reports no rejection and so prints no address.
    assert_eq!(addresses(&out), [&a[..]], "{out}");
    // The address names the declaration `use`, not the line: a declaration added above it
    // moves the rejection and leaves its address.
    let moved = unit(
        "addresses",
        "moved.zed",
        &format!("other(y) = y;\n{REJECTED}"),
    );
    let (_, out, _) = zedc_test(&[&moved]);
    // Compared in one file, since the address names its file too.
    std::fs::write(&moved, REJECTED).unwrap();
    let (_, _, same) = zedc(&["run", &moved]);
    assert_eq!(
        address_after(&out, &format!("{moved}:3:")),
        address_after(&same, &format!("{moved}:2:"))
    );
}

/// A unit whose `main` has a parameter other than `m: MainArgs`.
const PORT: &str = "helper(x) = x;\nmain(n: int) {\n  m.stdout <- \"x\";\n}\n";

#[test]
fn a_main_that_zedc_run_refuses_prints_its_place_and_address() {
    let file = unit("addresses", "port.zed", PORT);
    let (status, _, err) = zedc(&["run", &file]);
    assert_eq!(status, 1);
    let head = format!(
        "{file}:2:6: {}\n",
        zed_tests::main_param_message("n", "int")
    );
    let a = address_after(&err, head.trim_end());
    // The headline, its notes, then the address.
    assert!(err.starts_with(&head), "{err}");
    assert!(
        err.contains("`main` takes one argument, of type `MainArgs`"),
        "{err}"
    );
    assert!(err.ends_with(&format!("\n  address: {a}\n")), "{err}");
    // `zedc test` prints it the same way, address and all.
    let tested = PORT.replace("helper(x) = x;", "helper(x) = x test { 1 -> 1 }");
    let tested = unit("addresses", "port_test.zed", &tested);
    let (status, out, _) = zedc_test(&[&tested]);
    assert_eq!(status, 1, "{out}");
    let b = address_after(&out, &format!("{tested}:2:6: Parameter of `main`"));
    let (_, _, run) = zedc(&["run", &tested]);
    assert_eq!(address_after(&run, &format!("{tested}:2:6: ")), b);
    // Naming it is an error, under both commands.
    let (status, _, refused) = zedc(&["run", &file, "--suppress", &a]);
    assert_eq!(status, 1);
    assert_eq!(
        refused,
        format!("{err}{}\n", refusal(&format!("{file}:2:6"), &a))
    );
    let (status, out, err) = zedc_test(&["--suppress", &b, &tested]);
    assert_eq!(status, 1);
    assert!(
        out.contains(&refusal(&format!("{tested}:2:6"), &b)),
        "{out}"
    );
    assert!(
        !err.contains("no warning or error of this run has this address"),
        "{err}"
    );
}

#[test]
fn a_unit_with_no_main_is_refused_at_its_start_with_an_address() {
    let file = unit("addresses", "nomain.zed", "helper = 1;\n");
    let (status, _, err) = zedc(&["run", &file]);
    assert_eq!(status, 1);
    let a = address_after(&err, &format!("{file}:1:1: This file declares no `main`"));
    assert_eq!(
        err,
        format!(
            "{file}:1:1: This file declares no `main` to start the program at. Try adding \
             `main(m: MainArgs) {{ m.stdout <- \"hello\"; }}`.\n  \
             [1] 1:1: `zedc run` runs a program, which starts at the function `main`; a file of \
             definitions to test runs with `zedc test`\n      \
             1 | helper = 1;\n        \
             | ^\n  \
             address: {a}\n"
        )
    );
}

/// A package whose unit `app.main` imports a name `pricing` does not define.
fn shop(name: &str, main: &str) -> PathBuf {
    package(
        name,
        &[
            ("zed.manifest", "// the shop\n"),
            ("app/main.zed", main),
            ("pricing.zed", "net(g: f64) = g / 1.2;\n"),
        ],
    )
}

const SHOP_MAIN: &str = "import pricing.{net, gross};\nmain(m: MainArgs) {}\n";

#[test]
fn a_problem_of_a_package_prints_its_address() {
    let d = shop("shop", SHOP_MAIN);
    let main = d.join("app/main.zed");
    let main = main.to_str().unwrap();
    // The first run writes the import's pin (step L2.8), which changes the import's text, so the
    // runs compared below are those after it.
    zedc(&["run", main]);
    let (status, _, err) = zedc(&["run", main]);
    assert_eq!(status, 1, "{err}");
    let place = format!("{main}:1:1: the unit `pricing` defines no `gross`");
    let a = address_after(&err, &place);
    // Each problem prints one address, after its derivation, and the runs agree.
    let problems = err
        .lines()
        .filter(|l| l.starts_with(&d.display().to_string()));
    assert_eq!(problems.count(), addresses(&err).len(), "{err}");
    assert_eq!(zedc(&["run", main]).2, err);
    // A copy of the package in another directory prints the same address: the file's part is
    // its path from the package root (item DIAG-addr-root).
    let other = shop("shop2", SHOP_MAIN);
    let other = other.join("app/main.zed");
    let other = other.to_str().unwrap();
    zedc(&["run", other]);
    let (_, _, there) = zedc(&["run", other]);
    assert_eq!(
        address_after(
            &there,
            &format!("{other}:1:1: the unit `pricing` defines no `gross`")
        ),
        a
    );
    // Naming it is an error, and the address counts as matched.
    let (status, _, refused) = zedc(&["run", main, "--suppress", &a]);
    assert_eq!(status, 1);
    assert_eq!(
        refused,
        format!("{err}{}\n", refusal(&format!("{main}:1:1"), &a))
    );
}

#[test]
fn a_unit_a_package_names_and_has_no_file_prints_an_address() {
    let d = package(
        "missing",
        &[
            ("zed.manifest", "// the shop\n"),
            ("main.zed", "import nowhere.{x};\nmain(m: MainArgs) {}\n"),
        ],
    );
    let main = d.join("main.zed");
    let (status, _, err) = zedc(&["run", main.to_str().unwrap()]);
    assert_eq!(status, 1, "{err}");
    let problems = err.lines().filter(|l| !l.starts_with("  "));
    assert_eq!(problems.count(), addresses(&err).len(), "{err}");
    for a in addresses(&err) {
        let (status, _, refused) = zedc(&["run", main.to_str().unwrap(), "--suppress", a]);
        assert_eq!(status, 1);
        assert!(
            refused.contains(&format!("`--suppress {a}` names the error printed above")),
            "{refused}"
        );
    }
}

/// `Package::report_on_disk` on a package with problems in `n` files, each a unit that imports
/// `PER` names its import does not define, with every address suppressed: placing, addressing
/// and matching them is within n log n. The package is loaded before the timing. Each problem
/// costs some 60,000 instructions of its own (placing, hashing, writing), so a cost per pair of
/// problems shows only when there are thousands: `PER` = 40 gives 8,400 and 67,200 problems,
/// and a scan of all problems per problem then grows 50 times, not the 24 allowed.
#[test]
fn addressing_the_problems_of_a_package_scales() {
    const PER: usize = 40;
    let n = 200;
    let made: Vec<(usize, PathBuf, zedc::unit::Package, Vec<String>)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let mut files = vec![
                ("zed.manifest".to_string(), String::new()),
                ("base.zed".to_string(), "b = 1;\n".to_string()),
            ];
            let mut main = String::new();
            for i in 0..m {
                main.push_str(&format!("import u{i}.{{here{i}}};\n"));
                files.push((format!("u{i}.zed"), {
                    let names: Vec<String> = (0..PER).map(|j| format!("gone{i}_{j}")).collect();
                    format!("import base.{{{}}};\nhere{i} = {i};\n", names.join(", "))
                }));
            }
            main.push_str("main(m: MainArgs) {}\n");
            files.push(("main.zed".into(), main));
            let files: Vec<(&str, &str)> = files
                .iter()
                .map(|(f, t)| (f.as_str(), t.as_str()))
                .collect();
            let d = package(&format!("scale{m}"), &files);
            let pkg = zedc::unit::load(
                &mut zedc::query::Db::new(),
                &zedc::unit::Dir(d.clone()),
                &["main"],
            );
            let lines = pkg.report_on_disk(&d, &mut addressed());
            assert!(lines.len() >= m, "{}", lines.len());
            let words = lines
                .iter()
                .flat_map(|l| addresses(l))
                .flat_map(|a| ["--suppress".to_string(), a.to_string()])
                .collect();
            (m, d, pkg, words)
        })
        .collect();
    scaling::check("addressing the problems of a package in n files", n, |m| {
        let (_, d, pkg, words) = made.iter().find(|(k, ..)| *k == m).expect("a size");
        let words: Vec<&str> = words.iter().map(String::as_str).collect();
        let (mut suppress, _) = Suppress::take(&words).unwrap();
        let lines = pkg.report_on_disk(d, &mut suppress);
        assert!(suppress.unmatched().is_empty());
        // Each problem, and the line refusing its suppression.
        assert_eq!(lines.len(), words.len());
    });
}

/// `Suppress::refused_at` matches the address it is given, and only that one.
#[test]
fn refused_at_counts_its_address_as_matched() {
    let a = "1".repeat(64);
    let b = "2".repeat(64);
    let (mut s, rest) = Suppress::take(&["--suppress", &a]).unwrap();
    assert!(rest.is_empty());
    let pa = zedc::address::ContentAddress::parse(&a).unwrap();
    let pb = zedc::address::ContentAddress::parse(&b).unwrap();
    assert_eq!(s.refused_at("f.zed", pb), None);
    assert_eq!(
        s.refused_at("f.zed:1:2", pa).as_deref(),
        Some(refusal("f.zed:1:2", &a).as_str())
    );
    assert!(s.unmatched().is_empty());
}

/// A root unit with no file is reported in the file it would have, with an address; that
/// file's part of the address is found from its path under the package root alone (item
/// DIAG-addr-root), so any path to the root gives one, the file once written gives the same
/// part, and two names give two.
#[test]
fn a_root_unit_with_no_file_has_an_address_from_its_name_under_the_root() {
    let d = package("rootless", &[("zed.manifest", ""), ("sub/keep.zed", "")]);
    let gone = d.join("gone.zed");
    assert!(!gone.exists());
    let report = |root: &std::path::Path| {
        zedc::unit::load(
            &mut zedc::query::Db::new(),
            &zedc::unit::Dir(root.to_path_buf()),
            &["gone"],
        )
        .report_on_disk(root, &mut addressed())
    };
    let lines = report(&d);
    assert_eq!(lines.len(), 1, "{lines:?}");
    assert!(
        lines[0].starts_with(&format!("{}: ", gone.display())),
        "{lines:?}"
    );
    let a = addresses(&lines[0]);
    assert_eq!(a.len(), 1, "{lines:?}");
    // Another path to the root prints another file name and the same address.
    assert_eq!(addresses(&report(&d.join("sub/..")).join("\n")), a);
    // The file `gone.zed` of a copy of the package that has it has the part the name gives.
    let full = package("rootful", &[("zed.manifest", ""), ("gone.zed", "")]);
    assert_eq!(
        InFile::of(&full.join("gone.zed")).unwrap(),
        InFile::named("gone.zed")
    );
    assert_ne!(InFile::named("gone2.zed"), InFile::named("gone.zed"));
}

/// The file's part of an address (`InFile::of`) for a file `n` directories deep, with no
/// manifest above it, so every directory up to the file system's root is probed: within n log n
/// in instructions and bytes at n and 8n. The directories are made before the timing. Work in
/// the kernel, which resolves each probe's path, is not counted (`zed_tests::scaling`).
#[test]
fn the_file_part_of_an_address_scales_with_the_depth_of_the_file() {
    let n = 40;
    let files: Vec<(usize, PathBuf)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let mut d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
                .join("l01_29_rejection_addresses")
                .join(format!("deep{m}"));
            for _ in 0..m {
                d.push("d");
            }
            std::fs::create_dir_all(&d).unwrap();
            let file = d.join("deep.zed");
            std::fs::write(&file, "").unwrap();
            (m, file)
        })
        .collect();
    scaling::check("the file part of an address, n directories deep", n, |m| {
        let (_, file) = files.iter().find(|(k, _)| *k == m).expect("a size");
        InFile::of(file).unwrap();
    });
}
