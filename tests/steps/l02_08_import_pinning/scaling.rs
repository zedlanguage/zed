//! Pinning at the rule of low complexity (DESIGN.md Part G): writing and checking the pins of a
//! package is linear, up to a logarithm, in its units, its imports and its pins. Each package's
//! files are built, and its pinned texts found, before timing; the work measured is the
//! loader's, from reading each file to the pins it writes or checks.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::pin::{Edit, Pins, apply};
use zedc::query::Db;
use zedc::unit::{Memory, load};

use super::{files, mistakes};

/// The package of the `(file, text)` pairs `fs`.
fn memory(fs: &[(String, String)]) -> Memory {
    let refs: Vec<(&str, &str)> = fs.iter().map(|(f, t)| (f.as_str(), t.as_str())).collect();
    files(&refs)
}

/// `k` units `u0` … `u{k-1}`, each defining one value, and `main` importing each of them, as
/// the statements `main` holds.
fn fan(k: usize, main: impl Fn(usize) -> String) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = (0..k)
        .map(|i| {
            (
                format!("u{i}.zed"),
                format!("v{i}(x: f64) = x * {i}.0 + 1.0;\n"),
            )
        })
        .collect();
    let imports: String = (0..k).map(&main).collect();
    out.push((
        "main.zed".into(),
        format!("{imports}main() -> (stdout: Lines) {{}}\n"),
    ));
    out
}

/// Checks that loading each package of `pkgs` from `main` is linear in its size, up to a
/// logarithm, and that the build writes a pin for each of the `k` imports of `main` when
/// `writes` holds, and none when it does not.
fn linear(what: &str, n: usize, pkgs: &HashMap<usize, Memory>, writes: bool) {
    for (&k, fs) in pkgs {
        let p = load(&mut Db::new(), fs, &["main"]);
        assert_eq!(mistakes(&p), Vec::<String>::new(), "{what}");
        let written = p.writes.units.iter().map(|(_, e)| e.len()).sum::<usize>();
        assert_eq!(written, if writes { k } else { 0 }, "{what}");
    }
    scaling::check_order(what, n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}

#[test]
fn a_unit_importing_many_units_is_pinned_in_linear_time() {
    let n = 150;
    let pkgs: HashMap<usize, Memory> = [n, 8 * n]
        .into_iter()
        .map(|k| (k, memory(&fan(k, |i| format!("import u{i};\n")))))
        .collect();
    linear("pinning a fan of imports", n, &pkgs, true);
}

#[test]
fn a_unit_importing_many_pinned_units_is_checked_in_linear_time() {
    let n = 150;
    let pkgs: HashMap<usize, Memory> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let fs = fan(k, |i| format!("import u{i};\n"));
            let pinned = load(&mut Db::new(), &memory(&fs), &["main"])
                .pinned("main")
                .unwrap();
            let mut fs = fs;
            fs.last_mut().unwrap().1 = pinned;
            (k, memory(&fs))
        })
        .collect();
    linear("checking a fan of pinned imports", n, &pkgs, false);
}

#[test]
fn many_units_importing_one_unit_are_pinned_in_linear_time() {
    let n = 150;
    let pkgs: HashMap<usize, Memory> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let mut fs: Vec<(String, String)> = (0..k)
                .map(|i| {
                    (
                        format!("w{i}.zed"),
                        format!("import base.{{rate}};\nw{i}(x: f64) = x * rate;\n"),
                    )
                })
                .collect();
            fs.push(("base.zed".into(), "rate = 1.2;\n".into()));
            let imports: String = (0..k).map(|i| format!("import w{i};\n")).collect();
            fs.push((
                "main.zed".into(),
                format!("{imports}main() -> (stdout: Lines) {{}}\n"),
            ));
            (k, memory(&fs))
        })
        .collect();
    for (&k, fs) in &pkgs {
        let p = load(&mut Db::new(), fs, &["main"]);
        assert_eq!(mistakes(&p), Vec::<String>::new());
        // Each `w` gets its pin of `base`; `main`'s imports of the `w`s, which do not compile
        // alone before step L2.4, get none.
        assert_eq!(p.writes.units.len(), k);
    }
    scaling::check_order("pinning many importers of one unit", n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}

#[test]
fn a_pin_file_of_many_pins_is_read_and_written_in_n_log_n_time() {
    let n = 2000;
    let texts: HashMap<usize, String> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            // Written out of order, so the pins are sorted when read.
            let lines: String = (0..k)
                .rev()
                .map(|i| format!("proof {:064x} obligation {i}\n", i * 7919))
                .collect();
            (k, lines)
        })
        .collect();
    for (&k, t) in &texts {
        assert_eq!(Pins::parse(t).unwrap().len(), k);
    }
    scaling::check_order("reading and writing a pin file", n, 1, |k| {
        let pins = Pins::parse(&texts[&k]).unwrap();
        std::hint::black_box(pins.text());
    });
}

#[test]
fn many_pins_are_written_into_one_file_in_n_log_n_time() {
    let n = 2000;
    let cases: HashMap<usize, (String, Vec<Edit>)> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let text: String = (0..k).map(|i| format!("import u{i};\n")).collect();
            let ends: Vec<usize> = text.match_indices(';').map(|(a, _)| a).collect();
            // Given in reverse, so they are sorted before they are made.
            let edits = ends
                .iter()
                .rev()
                .map(|&at| Edit {
                    at,
                    text: " @hash(\"…\")".into(),
                })
                .collect();
            (k, (text, edits))
        })
        .collect();
    scaling::check_order("writing many pins into one file", n, 1, |k| {
        let (text, edits) = &cases[&k];
        std::hint::black_box(apply(text, edits));
    });
}
