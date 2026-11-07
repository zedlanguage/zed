//! Plan row PORT-catalog: the `catalog` tool of `zed-tools`, which lists the routines of the
//! standard library and of dependencies that the compiler's Rust calls, and the committed
//! `zed/compiler/CATALOG.md`. The tests read SCIP indexes built here, byte by byte, since
//! `rust-analyzer scip` takes more than a minute over this repository; the catalog was made with
//! it, and step S.1 regenerates it the same way.

use std::collections::{HashMap, HashSet};

use zed_tests::scaling::{check, inputs};
use zed_tools::catalog::{self, Uses, check_zed, read_catalog, routine, scan, write_catalog};
use zed_tools::layer::WordTable;
use zed_tools::plan::row_ids;
use zed_tools::spec::Spec;

use zed_tests::step_helpers::m0_03_grammar_tools::{Dir, grammar, tool};

fn varint(mut v: u64, out: &mut Vec<u8>) {
    while v >= 0x80 {
        out.push((v as u8) | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn bytes(field: u64, b: &[u8], out: &mut Vec<u8>) {
    varint(field << 3 | 2, out);
    varint(b.len() as u64, out);
    out.extend_from_slice(b);
}

fn number(field: u64, v: u64, out: &mut Vec<u8>) {
    varint(field << 3, out);
    varint(v, out);
}

/// An occurrence of `symbol` at `line` (from 0) with `roles`; its range packed or not.
fn occurrence(symbol: &str, line: u64, roles: u64, packed: bool) -> Vec<u8> {
    let mut o = Vec::new();
    if packed {
        let mut r = Vec::new();
        for v in [line, 4, 9] {
            varint(v, &mut r);
        }
        bytes(1, &r, &mut o);
    } else {
        for v in [line, 4, 9] {
            number(1, v, &mut o);
        }
    }
    bytes(2, symbol.as_bytes(), &mut o);
    if roles != 0 {
        number(3, roles, &mut o);
    }
    number(5, 7, &mut o); // syntax_kind, which the tool skips
    o
}

/// A document at `path` holding `occs`.
fn document(path: &str, occs: &[Vec<u8>]) -> Vec<u8> {
    let mut d = Vec::new();
    bytes(4, b"rust", &mut d); // language, which the tool skips
    bytes(1, path.as_bytes(), &mut d);
    for o in occs {
        bytes(2, o, &mut d);
    }
    d
}

/// An index of `docs`, after a metadata field the tool skips.
fn index(docs: &[Vec<u8>]) -> Vec<u8> {
    let mut i = Vec::new();
    bytes(1, b"metadata", &mut i);
    for d in docs {
        bytes(2, d, &mut i);
    }
    i
}

const PUSH: &str = "rust-analyzer cargo alloc https://github.com/rust-lang/rust/library/alloc vec/impl#[`Vec<T, A>`]push().";
const ADD: &str = "rust-analyzer cargo core https://github.com/rust-lang/rust/library/core ops/arith/impl#[`&u32`][`Add<u32>`]add().";
const ASSERT: &str = "rust-analyzer cargo core https://github.com/rust-lang/rust/library/core macros/builtin/assert!";
const MAP: &str = "rust-analyzer cargo core https://github.com/rust-lang/rust/library/core iter/traits/iterator/Iterator#map().";
const OURS: &str = "rust-analyzer cargo zedc 0.1.0 parse/Parser#new().";
const TYPE: &str =
    "rust-analyzer cargo alloc https://github.com/rust-lang/rust/library/alloc vec/Vec#";

fn ours() -> HashSet<String> {
    ["zedc".to_string()].into()
}

#[test]
fn routine_names_methods_trait_impls_macros_and_functions() {
    let o = ours();
    let cases = [
        (PUSH, Some("alloc::vec::Vec<T, A>::push")),
        (ADD, Some("core::ops::arith::<&u32 as Add<u32>>::add")),
        (ASSERT, Some("core::macros::builtin::assert!")),
        (MAP, Some("core::iter::traits::iterator::Iterator::map")),
        (
            "rust-analyzer cargo cranelift-codegen 0.1 settings/builder().",
            Some("cranelift_codegen::settings::builder"),
        ),
        (
            "rust-analyzer cargo core v slice/impl#[`[T]`]sort_by(+1).",
            Some("core::slice::[T]::sort_by"),
        ),
        (OURS, None),
        (TYPE, None),
        ("local 5", None),
        ("rust-analyzer cargo core v cmp/Ord#", None),
    ];
    for (symbol, want) in cases {
        assert_eq!(routine(symbol, &o).as_deref(), want, "{symbol}");
    }
}

#[test]
fn scan_counts_uses_files_and_the_first_site_and_skips_definitions_and_imports() {
    let docs = [
        document(
            "crates/zedc/src/b.rs",
            &[
                occurrence(PUSH, 9, 0, true),
                occurrence(PUSH, 2, 0, false),
                occurrence(ADD, 0, 0, true),
                occurrence(MAP, 3, 1, true),    // a definition
                occurrence(ASSERT, 3, 2, true), // an import
                occurrence(OURS, 1, 0, true),
                occurrence(TYPE, 1, 0, true),
                occurrence("local 3", 1, 0, true),
            ],
        ),
        document(
            "crates/zed-kernel/src/a.rs",
            &[occurrence(PUSH, 40, 0, true)],
        ),
        document("crates/zed-rt/src/c.rs", &[occurrence(ASSERT, 0, 0, true)]),
        document("tests/steps/x.rs", &[occurrence(MAP, 0, 0, true)]),
    ];
    let found = scan(&index(&docs), &catalog::SOURCES, &ours()).expect("a well-formed index");
    let want: Vec<(&str, usize, usize, (&str, u64))> = vec![
        (
            "alloc::vec::Vec<T, A>::push",
            3,
            2,
            ("crates/zed-kernel/src/a.rs", 41),
        ),
        (
            "core::ops::arith::<&u32 as Add<u32>>::add",
            1,
            1,
            ("crates/zedc/src/b.rs", 1),
        ),
    ];
    let got: Vec<(&str, usize, usize, (&str, u64))> = found
        .iter()
        .map(|(r, u)| {
            let f = u.first.as_ref().expect("a first use");
            (r.as_str(), u.count, u.files.len(), (f.0.as_str(), f.1))
        })
        .collect();
    assert_eq!(got, want);
}

#[test]
fn scan_rejects_a_damaged_index_with_its_own_message() {
    let good = index(&[document(
        "crates/zedc/src/a.rs",
        &[occurrence(PUSH, 0, 0, true)],
    )]);
    let cases: [(&[u8], &str); 4] = [
        (&good[..good.len() - 1], "runs past its end"),
        (&[0x08, 0x80], "ends inside a number"),
        (&[0x0b], "wire type 3"),
        (
            &[
                0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
            ],
            "longer than ten bytes",
        ),
    ];
    for (bytes, want) in cases {
        let e = scan(bytes, &catalog::SOURCES, &ours()).expect_err("a damaged index");
        assert!(e.contains(want), "{e} lacks {want}");
    }
    let mut no_range = Vec::new();
    bytes(2, PUSH.as_bytes(), &mut no_range);
    let doc = document("crates/zedc/src/a.rs", &[no_range]);
    let e = scan(&index(&[doc]), &catalog::SOURCES, &ours()).expect_err("no range");
    assert!(e.contains("no range"), "{e}");
}

/// A spec with the repository's grammars and a table with `len` at L1 and `deep` at L30.
fn spec_dir(name: &str) -> Dir {
    let dir = Dir::new(name);
    dir.write(
        "DESIGN.md",
        &format!(
            "# Test spec\n\n| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
             | L1 | | | `len` |\n| L30 | | | `deep` |\n\n```peg\n{}```\n\n```peg\n{}```\n\n\
             ```peg\n{}```\n",
            grammar("lexical.peg"),
            grammar("syntax.peg"),
            grammar("notation.peg")
        ),
    );
    dir.write("EXAMPLES.md", "");
    dir
}

#[test]
fn check_zed_takes_missing_plan_rows_and_zed_texts_in_zed0_only() {
    let dir = spec_dir("catalog_zed");
    let spec = Spec::open(&dir.root()).expect("the test spec");
    let words = WordTable::read(&spec.design).expect("its table");
    let rows: HashSet<&str> = ["STD-seq", "S.4"].into();
    let ok = [
        "missing",
        "row STD-seq",
        "row STD-seq, S.4",
        "`a + b`",
        "`len(xs) == 0`, `xs[i]`",
    ];
    for cell in ok {
        assert_eq!(check_zed(cell, &spec, &words, &rows), None, "{cell}");
    }
    let bad = [
        ("row NOPE", "no plan row NOPE"),
        ("row S.4, NOPE", "no plan row NOPE"),
        ("`a +`", "not an expression"),
        ("`deep(x)`", "of L30, above Zed₀"),
        ("`a + b", "unclosed backtick"),
        ("none", "neither"),
        ("`a` or `b`", "neither"),
        ("", "neither"),
    ];
    for (cell, want) in bad {
        let p = check_zed(cell, &spec, &words, &rows).unwrap_or_default();
        assert!(p.contains(want), "{cell:?}: {p:?} lacks {want:?}");
    }
}

#[test]
fn write_keeps_the_zed_column_and_check_reports_each_difference() {
    let dir = spec_dir("catalog_run");
    let docs = [document(
        "crates/zedc/src/a.rs",
        &[occurrence(PUSH, 0, 0, true), occurrence(ADD, 1, 0, true)],
    )];
    let idx = dir.root() + "/index.scip";
    std::fs::write(&idx, index(&docs)).expect("writing the index");
    let cat = dir.write(
        "CATALOG.md",
        "# C\n\nprose\n\nCounts: 0 routines, 0 uses.\n\n| Routine | Uses | Files | First use | Zed |\n\
         |---|--:|--:|---|---|\n| `core::ops::arith::<&u32 as Add<u32>>::add` | 9 | 9 | `x:1` | `a + b` |\n\
         | `gone::f` | 1 | 1 | `x:1` | missing |\n\nAfter.\n",
    );
    let (outcome, out) = tool(catalog::run, &[&dir.root(), &cat, "--index", &idx]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("called, not in the catalog: `alloc::vec::Vec<T, A>::push`"),
        "{out}"
    );
    assert!(
        out.contains("in the catalog, not called: `gone::f`"),
        "{out}"
    );

    let (outcome, out) = tool(
        catalog::run,
        &[&dir.root(), &cat, "--index", &idx, "--write"],
    );
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("1 new, 1 no longer called"), "{out}");
    let text = std::fs::read_to_string(&cat).expect("the written catalog");
    assert_eq!(
        text,
        "# C\n\nprose\n\nCounts: 2 routines, 2 uses.\n\n| Routine | Uses | Files | First use | Zed |\n\
         |---|--:|--:|---|---|\n| `alloc::vec::Vec<T, A>::push` | 1 | 1 | `crates/zedc/src/a.rs:1` | missing |\n\
         | `core::ops::arith::<&u32 as Add<u32>>::add` | 1 | 1 | `crates/zedc/src/a.rs:2` | `a + b` |\n\nAfter.\n"
    );
    let (outcome, out) = tool(catalog::run, &[&dir.root(), &cat, "--index", &idx]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(
        out.contains("2 routines, 1 missing in Zed, 0 problems"),
        "{out}"
    );

    std::fs::write(&cat, text.replace("| missing |", "| row NOPE |"))
        .expect("rewriting the catalog");
    let (outcome, out) = tool(catalog::run, &[&dir.root(), &cat, "--index", &idx]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("`alloc::vec::Vec<T, A>::push`: no plan row NOPE"),
        "{out}"
    );

    let (outcome, out) = tool(catalog::run, &[&dir.root(), &cat, "--bogus"]);
    assert_eq!(
        outcome,
        Err("usage: catalog SPEC_DIR CATALOG.md [--index INDEX.scip] [--write]".to_string()),
        "{out}"
    );
}

#[test]
fn a_routine_listed_twice_is_a_problem() {
    let dir = spec_dir("catalog_twice");
    let idx = dir.root() + "/index.scip";
    std::fs::write(&idx, index(&[])).expect("writing the index");
    let row = "| `a::f` | 1 | 1 | `x:1` | missing |\n";
    let cat = dir.write(
        "CATALOG.md",
        &format!(
            "# C\n\n| Routine | Uses | Files | First use | Zed |\n|---|--:|--:|---|---|\n{row}{row}"
        ),
    );
    let (outcome, out) = tool(catalog::run, &[&dir.root(), &cat, "--index", &idx]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("listed twice: `a::f`"), "{out}");
}

/// The committed catalog: rows sorted with no repeat, each Zed column a form the tool takes under
/// the spec's grammars and words table and the plan, and each row surviving a rewrite. Where the
/// spec repository is not read (`ZED_SPEC_DIR=none`), the repository's copies of the grammars and
/// a table of two words stand in for it.
#[test]
fn the_committed_catalog_is_well_formed() {
    let root = zed_tools::impl_root();
    let text = std::fs::read_to_string(format!("{root}/zed/compiler/CATALOG.md"))
        .expect("zed/compiler/CATALOG.md");
    let (_, rows, _) = read_catalog(&text).expect("its table");
    assert!(rows.len() > 1000, "{} rows", rows.len());
    assert!(
        rows.windows(2).all(|w| w[0].routine < w[1].routine),
        "rows sorted and unique"
    );
    let dir = spec_dir("catalog_committed");
    let spec_root = zed_tests::spec::dir("the catalog's Zed texts against the words table")
        .map_or_else(|| dir.root(), |p| p.display().to_string());
    let spec = Spec::open(&spec_root).expect("the spec");
    let words = WordTable::read(&spec.design).expect("its table");
    let plan = std::fs::read_to_string(format!("{root}/docs/plan_dag.md")).expect("the plan");
    let plan_rows: HashSet<&str> = row_ids(&plan).expect("its rows").into_iter().collect();
    let bad: Vec<String> = rows
        .iter()
        .filter_map(|r| {
            check_zed(&r.zed, &spec, &words, &plan_rows).map(|p| format!("{}: {p}", r.routine))
        })
        .collect();
    assert!(bad.is_empty(), "{bad:#?}");
    let found = rows
        .iter()
        .map(|r| (r.routine.clone(), Uses::default()))
        .collect();
    let zed: HashMap<&str, &str> = rows
        .iter()
        .map(|r| (r.routine.as_str(), r.zed.as_str()))
        .collect();
    let again = write_catalog("", &found, &zed, "");
    let (_, rows2, _) = read_catalog(&again).expect("the rewritten table");
    assert_eq!(
        rows2, rows,
        "a routine's name or Zed column does not survive a rewrite"
    );
}

/// The scan of an index of n documents, each with eight uses of routines out of n / 2.
#[test]
fn scan_scales_linearly_with_the_index() {
    let o = ours();
    let built = inputs(2_000, |n| {
        let docs: Vec<Vec<u8>> = (0..n)
            .map(|d| {
                let occs: Vec<Vec<u8>> = (0..8)
                    .map(|k| {
                        let s = format!(
                            "rust-analyzer cargo dep 1.0 m/T#f{}().",
                            (d * 8 + k) % (n / 2)
                        );
                        occurrence(&s, k as u64, 0, true)
                    })
                    .collect();
                document(&format!("crates/zedc/src/f{}.rs", d % 64), &occs)
            })
            .collect();
        index(&docs)
    });
    check("catalog scan of n documents", 2_000, |n| {
        let found = scan(&built[&n], &catalog::SOURCES, &o).expect("a well-formed index");
        assert_eq!(found.len(), n / 2);
    });
}
