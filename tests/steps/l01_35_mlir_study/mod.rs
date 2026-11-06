//! Step L1.35: the MLIR study, `zed/compiler/MLIR.md`. The record decides how ZIR lowers to
//! MLIR's dialects; this step holds it to the node inventory, so an operation or a region
//! kind added later without a lowering fails here. The inventory is read from the text of
//! `crates/zedc/src/zir/mod.rs` (item L1.35-inventory), so no list in this file has to be
//! extended when a variant is added: the new variant needs a row, and that is all.

use std::collections::BTreeSet;
use std::path::PathBuf;

use zed_tests::scaling::check_order;

fn read(path: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
}

fn record() -> String {
    read("../zed/compiler/MLIR.md")
}

fn zir_source() -> String {
    read("../crates/zedc/src/zir/mod.rs")
}

/// The first cells of the rows of the table under heading `##` `title`, without backticks.
fn rows(text: &str, title: &str) -> BTreeSet<String> {
    let start = text
        .find(&format!("\n## {title}\n"))
        .unwrap_or_else(|| panic!("no section `{title}`"));
    let body = &text[start + title.len() + 5..];
    let body = &body[..body.find("\n## ").unwrap_or(body.len())];
    body.lines()
        .filter(|l| l.starts_with("| `"))
        .map(|l| l[2..].split(" |").next().unwrap().replace('`', ""))
        .collect()
}

/// The variant names of `pub enum <name>` in the Rust source `src`, in order. A variant name
/// is the first identifier after the enum's `{` or after a comma, at the enum body's own
/// nesting level; comments are skipped, and so are attributes and the fields of tuple and
/// struct variants, which sit one bracket deeper. One pass over the enum's text.
fn variants(src: &str, name: &str) -> Vec<String> {
    let head = format!("\npub enum {name} {{");
    let start = src
        .find(&head)
        .unwrap_or_else(|| panic!("no `pub enum {name}` in the source"))
        + head.len();
    let mut found = Vec::new();
    let (mut depth, mut expecting) = (0usize, true);
    for line in src[start..].lines() {
        let code = &line[..line.find("//").unwrap_or(line.len())];
        let mut chars = code.char_indices().peekable();
        while let Some((i, c)) = chars.next() {
            match c {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' => depth -= 1,
                '}' if depth == 0 => {
                    assert!(!found.is_empty(), "`pub enum {name}` has no variants");
                    return found;
                }
                '}' => depth -= 1,
                ',' if depth == 0 => expecting = true,
                c if depth == 0 && expecting && (c.is_alphabetic() || c == '_') => {
                    let mut end = i + c.len_utf8();
                    while let Some(&(j, d)) = chars.peek() {
                        if !(d.is_alphanumeric() || d == '_') {
                            break;
                        }
                        end = j + d.len_utf8();
                        chars.next();
                    }
                    found.push(code[i..end].to_string());
                    expecting = false;
                }
                _ => {}
            }
        }
    }
    panic!("`pub enum {name}` has no closing brace")
}

/// The rows of the Operations table that the variants of `Op` call for: the lower-case variant
/// name, as the text form writes it; `port read` and `port push` for the two port operations,
/// which the text form writes under one name with a direction; and for `Op::Derived` one row
/// per variant of `Derived`, since each derived node lowers in its own way.
fn operation_rows(src: &str) -> BTreeSet<String> {
    let mut want = BTreeSet::new();
    for v in variants(src, "Op") {
        match v.as_str() {
            "Read" => want.insert("port read".to_string()),
            "Push" => want.insert("port push".to_string()),
            "Derived" => {
                want.extend(variants(src, "Derived").iter().map(|d| d.to_lowercase()));
                continue;
            }
            _ => want.insert(v.to_lowercase()),
        };
    }
    want
}

/// The rows of the Region kinds table that the variants of `RegionKind` call for.
fn region_rows(src: &str) -> BTreeSet<String> {
    variants(src, "RegionKind")
        .iter()
        .map(|v| v.to_lowercase())
        .collect()
}

#[test]
fn every_operation_has_a_lowering() {
    let src = zir_source();
    let (want, have) = (operation_rows(&src), rows(&record(), "Operations"));
    assert_eq!(
        have,
        want,
        "MLIR.md's Operations table ({} rows) against the operations of zir/mod.rs ({}); \
         missing rows: {:?}; rows with no operation: {:?}",
        have.len(),
        want.len(),
        want.difference(&have).collect::<Vec<_>>(),
        have.difference(&want).collect::<Vec<_>>(),
    );
}

#[test]
fn every_region_kind_has_a_form() {
    let src = zir_source();
    let (want, have) = (region_rows(&src), rows(&record(), "Region kinds"));
    assert_eq!(
        have,
        want,
        "MLIR.md's Region kinds table ({} rows) against the region kinds of zir/mod.rs ({}); \
         missing rows: {:?}; rows with no region kind: {:?}",
        have.len(),
        want.len(),
        want.difference(&have).collect::<Vec<_>>(),
        have.difference(&want).collect::<Vec<_>>(),
    );
}

#[test]
fn the_ports_and_the_derived_nodes_have_their_own_rows() {
    // The two exceptions to the lower-case rule: `Op::Read` and `Op::Push` are written `port`
    // with a direction, and `Op::Derived` stands for the variants of `Derived`.
    let src = zir_source();
    let want = operation_rows(&src);
    for row in ["port read", "port push"] {
        assert!(
            want.contains(row),
            "no row `{row}` from Op::Read or Op::Push"
        );
    }
    for row in ["read", "push", "port", "derived"] {
        assert!(
            !want.contains(row),
            "a row `{row}` that the text form never writes"
        );
    }
    let derived = variants(&src, "Derived");
    assert!(!derived.is_empty());
    for d in &derived {
        assert!(want.contains(&d.to_lowercase()), "Derived::{d} has no row");
    }
}

#[test]
fn the_reader_takes_struct_and_tuple_variants_comments_and_attributes() {
    // A reduced copy of the shapes zir/mod.rs uses: doc comments, a struct variant over several
    // lines whose field names must not count, tuple variants with generic and nested brackets,
    // an attribute on a variant, and a second enum after the first that must not be read.
    let src = "\n/// Doc.\n#[derive(Clone)]\npub enum Op {\n    /// `reindex`, with a comma, here.\n    \
               Reindex(Witness),\n    Fold {\n        /// The depth.\n        depth: usize,\n        \
               ev: Evidence,\n    },\n    #[doc = \"x\"]\n    Match(Vec<(Pattern, [u8; 2])>),\n    \
               Wave\n}\n\npub enum Other {\n    Not,\n}\n";
    assert_eq!(variants(src, "Op"), ["Reindex", "Fold", "Match", "Wave"]);
    assert_eq!(variants(src, "Other"), ["Not"]);
}

#[test]
fn reading_the_variants_is_linear_in_the_source() {
    // An enum of k struct variants, each with a doc comment and two fields; built before timing.
    fn source(k: usize) -> String {
        let mut s = String::from("\npub enum Op {\n");
        for i in 0..k {
            s.push_str(&format!(
                "    /// Variant {i}, with a comma.\n    V{i} {{\n        a: Vec<u8>,\n        b: (u8, u8),\n    }},\n"
            ));
        }
        s.push_str("}\n");
        s
    }
    let n = 20_000;
    let (small, large) = (source(n), source(8 * n));
    check_order("reading the variants of an enum of n variants", n, 1, |k| {
        let found = variants(if k == n { &small } else { &large }, "Op");
        assert_eq!(found.len(), k);
    });
}
