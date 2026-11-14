//! Pinning at the rule of low complexity (DESIGN.md Part G): writing and checking the pins of a
//! package is linear, up to a logarithm, in its units, its imports and its pins. Each package's
//! files are built, and its pinned texts found, before timing; the work measured is the
//! loader's, from reading each file to the pins it writes or checks. The benchmarks in
//! `bench.rs` hold the time of each; here each package is pinned at small sizes, with the checks
//! the benchmarks made of their inputs.

use zedc::pin::{Edit, Pins, apply};
use zedc::query::Db;
use zedc::unit::{Memory, load};

use super::{files, mistakes};

/// The package of the `(file, text)` pairs `fs`.
pub(super) fn memory(fs: &[(String, String)]) -> Memory {
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
        format!("{imports}main(m: MainArgs) {{}}\n"),
    ));
    out
}

/// A fan of `k` imports with no pins.
pub(super) fn unpinned_fan(k: usize) -> Memory {
    memory(&fan(k, |i| format!("import u{i};\n")))
}

/// A fan of `k` imports, `main` holding the pins the build writes for it.
pub(super) fn pinned_fan(k: usize) -> Memory {
    let fs = fan(k, |i| format!("import u{i};\n"));
    let pinned = load(&mut Db::new(), &memory(&fs), &["main"])
        .pinned("main")
        .unwrap();
    let mut fs = fs;
    fs.last_mut().unwrap().1 = pinned;
    memory(&fs)
}

/// `k` units `w{i}`, each importing `base`, and `main` importing each of them.
pub(super) fn importers_of_one(k: usize) -> Memory {
    let mut fs: Vec<(String, String)> = (0..k)
        .map(|i| {
            (
                format!("w{i}.zed"),
                format!("import base.{{rate}};\nw{i}(x: f64) = x * rate;\n"),
            )
        })
        .collect();
    fs.push(("base.zed".into(), "rate = 1.2f64;\n".into()));
    let imports: String = (0..k).map(|i| format!("import w{i};\n")).collect();
    fs.push((
        "main.zed".into(),
        format!("{imports}main(m: MainArgs) {{}}\n"),
    ));
    memory(&fs)
}

/// The pins the build writes for the package `fs`, loaded from `main` with no mistake.
fn written(fs: &Memory) -> usize {
    let p = load(&mut Db::new(), fs, &["main"]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    p.writes.units.iter().map(|(_, e)| e.len()).sum()
}

/// A pin file of `k` pins, written out of order, so the pins are sorted when read.
pub(super) fn pin_file(k: usize) -> String {
    (0..k)
        .rev()
        .map(|i| format!("proof {:064x} obligation {i}\n", i * 7919))
        .collect()
}

/// A file of `k` imports and an edit pinning each, given in reverse, so they are sorted before
/// they are made.
pub(super) fn pin_edits(k: usize) -> (String, Vec<Edit>) {
    let text: String = (0..k).map(|i| format!("import u{i};\n")).collect();
    let ends: Vec<usize> = text.match_indices(';').map(|(a, _)| a).collect();
    let edits = ends
        .iter()
        .rev()
        .map(|&at| Edit {
            at,
            text: " @hash(\"…\")".into(),
        })
        .collect();
    (text, edits)
}

/// Each package of the benchmarks in `bench.rs` loads with no mistake and writes the pins its
/// benchmark expected, at small sizes.
#[test]
fn each_package_writes_its_pins_at_small_sizes() {
    for k in [1, 2, 9] {
        assert_eq!(written(&unpinned_fan(k)), k, "pinning a fan of imports");
        assert_eq!(
            written(&pinned_fan(k)),
            0,
            "checking a fan of pinned imports"
        );
        // Each `w` gets its pin of `base`; `main`'s imports of the `w`s, which do not compile
        // alone before step L2.4, get none.
        let p = load(&mut Db::new(), &importers_of_one(k), &["main"]);
        assert_eq!(mistakes(&p), Vec::<String>::new());
        assert_eq!(p.writes.units.len(), k);
    }
}

/// A pin file of a few pins is read and written, and a few pins are written into one file.
#[test]
fn a_few_pins_are_read_and_written() {
    for k in [0, 1, 2, 9] {
        let pins = Pins::parse(&pin_file(k)).unwrap();
        assert_eq!(pins.len(), k);
        pins.text();
        let (text, edits) = pin_edits(k);
        assert_eq!(apply(&text, &edits).matches(" @hash(").count(), k);
    }
}
