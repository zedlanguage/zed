//! The prelude words and types of later layers (DESIGN.md sec:grammar, "Defined words by
//! layer"): a use of one that no program name shadows is reported with its layer, not as a
//! name that is not defined.

use std::collections::BTreeMap;
use std::path::Path;

use super::errors;
use zedc::resolve::{LATER_TYPES, WORDS, annotation_layer, prelude_layer};

#[test]
fn a_later_word_is_reported_with_its_layer() {
    assert_eq!(
        errors("f(xs) = any(xs);\n"),
        ["`any` is a prelude word of layer L3 [any]"]
    );
    assert_eq!(
        errors("f(n) = upTo(n);\n"),
        ["`upTo` is a prelude word of layer L5 [upTo]"]
    );
    assert_eq!(
        errors("f(a, b) = merge(a, b);\n"),
        ["`merge` is a prelude word of layer L7 [merge]"]
    );
    assert_eq!(
        errors("f(g) = compile(g);\n"),
        ["`compile` is a prelude word of layer L19 [compile]"]
    );
    // A program's own name shadows the word at any layer.
    assert_eq!(errors("find = 0;\nf() = find;\n"), Vec::<String>::new());
}

#[test]
fn a_later_type_is_reported_with_its_layer() {
    assert_eq!(
        errors("f(t: Instant) = t;\n"),
        ["the type `Instant` is a prelude type of layer L7 [Instant]"]
    );
    assert_eq!(
        errors("f(s: Seq(int)) = s;\n"),
        ["the type `Seq` is a prelude type of layer L5 [Seq]"]
    );
    assert_eq!(
        errors("f(z: complex(f64)) = z;\n"),
        ["the type `complex` is a prelude type of layer L14 [complex]"]
    );
    // A struct of the prelude is also named as a value, to build one.
    assert_eq!(
        errors("f() = Facet(1);\n"),
        ["`Facet` is a prelude type of layer L6 [Facet]"]
    );
    assert_eq!(
        errors("f() = Facett(1);\n"),
        ["`Facett` is not defined [Facett]"]
    );
}

/// The names of the table that the resolver does not hold, each with the reason: a name the
/// program declares, a port a program names in `main`'s header, a compiler mode, which is no name
/// in source, and a word of L1 that a later layer extends to more types.
const NOT_PRELUDE_NAMES: &[(&str, &str)] = &[
    ("L1", "main"),
    ("L7", "clock"),
    ("L7", "log"),
    ("L14", "abs"),
    ("L17", "total"),
    ("L18", "preallocated"),
];

/// The words of later layers the table does not list, each a prelude function that enters with the
/// types it takes and returns (the paragraph before the table): `count` takes a family.
const UNLISTED: &[(&str, u32)] = &[("count", 3)];

/// The lower-case names of the table that are types as well as words: the number algebras
/// and float formats of L14, which are applied to build a value as `int(…)` is.
const LOWER_TYPES: &[&str] = &["complex", "quat", "oct", "bf16", "f16"];

/// Each row of the table "Defined words by layer" in `design`: its layer, its annotations and
/// its defined forms, each the text of its code spans.
fn table(design: &str) -> Vec<(u32, Vec<String>, Vec<String>)> {
    let start = design
        .find("**Defined words by layer.**")
        .expect("the table's paragraph");
    let spans = |cell: &str| -> Vec<String> {
        cell.split('`')
            .skip(1)
            .step_by(2)
            .map(str::to_string)
            .collect()
    };
    design[start..]
        .lines()
        .skip_while(|l| !l.starts_with("| L1 "))
        .take_while(|l| l.starts_with("| L"))
        .map(|l| {
            let cells: Vec<&str> = l.split('|').map(str::trim).collect();
            let layer = cells[1][1..].parse().expect("a layer number");
            (layer, spans(cells[2]), spans(cells[4]))
        })
        .collect()
}

#[test]
fn the_resolver_holds_every_word_and_type_of_the_table() {
    let spec = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../zed/DESIGN.md");
    let Ok(design) = std::fs::read_to_string(&spec) else {
        eprintln!(
            "no spec repository at {}: table not checked",
            spec.display()
        );
        return;
    };
    let rows = table(&design);
    assert!(rows.len() > 20, "the table has {} rows", rows.len());
    // The first layer a name is listed at is its layer: `Ast` returns at L11 with members.
    let mut words: BTreeMap<String, u32> = BTreeMap::new();
    let mut types: BTreeMap<String, u32> = BTreeMap::new();
    for (layer, annots, forms) in &rows {
        for a in annots {
            let name = a.strip_prefix('@').expect("an annotation");
            assert_eq!(annotation_layer(name), Some(*layer), "@{name}");
        }
        let names = forms.iter().filter(|f| {
            f.chars().next().is_some_and(char::is_alphabetic)
                && f.chars().all(char::is_alphanumeric)
                && !NOT_PRELUDE_NAMES.contains(&(format!("L{layer}").as_str(), f.as_str()))
        });
        for f in names {
            let upper = f.chars().next().is_some_and(char::is_uppercase);
            if !upper {
                words.entry(f.clone()).or_insert(*layer);
            }
            if upper || LOWER_TYPES.contains(&f.as_str()) {
                types.entry(f.clone()).or_insert(*layer);
            }
        }
    }
    for (w, layer) in &words {
        assert_eq!(prelude_layer(w), Some(*layer), "the word `{w}`");
    }
    for (t, layer) in &types {
        let held = match LATER_TYPES.iter().find(|(n, _)| n == t) {
            Some(&(_, l)) => Some(l),
            None if zedc::resolve::is_prelude_name(t) => Some(1),
            None => None,
        };
        assert_eq!(held, Some(*layer), "the type `{t}`");
    }
    // And the resolver holds no word or type of a later layer that the table does not list.
    let unlisted: Vec<(&str, u32)> = WORDS
        .iter()
        .filter(|&&(w, l)| l > 1 && words.get(w) != Some(&l))
        .copied()
        .collect();
    assert_eq!(
        unlisted, UNLISTED,
        "the words of later layers the table does not list"
    );
    for &(t, layer) in LATER_TYPES {
        assert!(
            types.get(t) == Some(&layer),
            "the type `{t}` of L{layer} is not in the table"
        );
    }
}
