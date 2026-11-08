//! The prelude words, facet words and types of later layers (DESIGN.md sec:grammar, "Defined
//! words by layer"): a use of one that no program name shadows is reported with its layer, not
//! as a name that is not defined.

use std::collections::BTreeMap;

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

/// A facet is a value of the prelude struct `Facet` bound to a name (DESIGN.md
/// sec:checking_in_zed), so a prelude facet named below its layer is reported with the layer.
#[test]
fn a_facet_word_is_reported_with_its_layer() {
    assert_eq!(
        errors("f(x) = order(x);\n"),
        ["`order` is a prelude word of layer L7 [order]"]
    );
    assert_eq!(
        errors("f(s) = units(s);\n"),
        ["`units` is a prelude word of layer L12 [units]"]
    );
    assert_eq!(
        errors("f(n) = retry(n);\n"),
        ["`retry` is a prelude word of layer L21 [retry]"]
    );
    assert_eq!(
        errors("f() = target;\n"),
        ["`target` is a prelude word of layer L24 [target]"]
    );
    // A facet a program defines is its own name: not defined until the program binds it.
    assert_eq!(
        errors("f() = parity;\n"),
        ["`parity` is not defined [parity]"]
    );
    // A parameter or a binding shadows a facet word at any layer.
    assert_eq!(
        errors("area(length, at) = length * at;\nrate = 2;\ng() = rate;\n"),
        Vec::<String>::new()
    );
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

/// `u8 = int[0..=255]` and `i8` to `i64` are the fixed-width aliases of L7 (DESIGN.md
/// sec:domains, step L7.4), and `byte` is no type at any layer (author decision 2026-11-04: the
/// type `byte` is renamed `u8`).
#[test]
fn the_fixed_width_aliases_are_types_of_l7_and_byte_is_none() {
    assert_eq!(
        errors("checksum(b: u8) = b;\n"),
        ["the type `u8` is a prelude type of layer L7 [u8]"]
    );
    assert_eq!(
        errors("status(rc: i32, flags: i8) = rc;\n"),
        [
            "the type `i32` is a prelude type of layer L7 [i32]",
            "the type `i8` is a prelude type of layer L7 [i8]"
        ]
    );
    assert_eq!(
        errors("checksum(b: byte) = b;\n"),
        ["the type `byte` is not defined [byte]"]
    );
    assert_eq!(
        errors("checksum(b: u8 | byte) = b;\n"),
        [
            "the type `u8` is a prelude type of layer L7 [u8]",
            "the type `byte` is not defined [byte]"
        ]
    );
    // The aliases are no value words: `u8(300)` builds nothing, so it is told the layer of the
    // type and not offered as a cast.
    assert_eq!(
        errors("f() = u8(300);\n"),
        ["`u8` is a prelude type of layer L7 [u8]"]
    );
    // A program's own name `byte`, `u8` or `i32` is an ordinary binding.
    assert_eq!(
        errors("f(byte) = byte + 1;\ng(u8) = u8 * 2;\ni32 = 7;\nh() = i32;\n"),
        Vec::<String>::new()
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
/// of L14 and the float formats of L1, which are applied to build a value as `int(…)` is.
const LOWER_TYPES: &[&str] = &["complex", "quat", "oct", "bf16", "f16"];

/// The lower-case names of the table that are types and not words: the fixed-width aliases of L7
/// (DESIGN.md sec:domains), which no program applies to a value.
const ALIASES: &[&str] = &["i8", "i16", "i32", "i64", "u8"];

/// The facets of the table's third column that a program defines, as examples of the rule
/// "every facet a program defines": names of the program, not of the prelude.
const PROGRAM_FACETS: &[(&str, &str)] = &[("L12", "parity"), ("L12", "latency"), ("L12", "dist")];

/// Names of the table whose rows are not built, each with the plan row that builds it: the test
/// holds that each is not yet known, so that row must take it out of this list.
const PENDING: &[(&str, &str)] = &[
    ("failure", "PORT-ack-name"),
    ("fpwarn", "FPWARN"),
    ("fpsafe", "FPWARN"),
    ("approx", "L10.3d"),
    ("f16", "L1.18a"),
    ("bf16", "L1.18a"),
    ("f32Bits", "L1.18a"),
    ("f16Bits", "L1.18a"),
    ("bf16Bits", "L1.18a"),
    ("i128", "INT-128"),
    ("u16", "INT-128"),
    ("u32", "INT-128"),
    ("u64", "INT-128"),
    ("u128", "INT-128"),
    ("csqrt", "MATH-names"),
    ("cexp", "MATH-names"),
    ("clog", "MATH-names"),
    ("cpow", "MATH-names"),
    ("U8String", "STR-types"),
    ("Utf8String", "STR-types"),
    ("Utf16String", "STR-types"),
    ("Utf32String", "STR-types"),
    ("char8", "STR-types"),
    ("char16", "STR-types"),
    ("char32", "STR-types"),
];

/// A row of the table "Defined words by layer": its layer, and its annotations, facet words and
/// defined forms, each the text of its code spans.
struct Row {
    layer: u32,
    annots: Vec<String>,
    facets: Vec<String>,
    forms: Vec<String>,
}

/// Each row of the table "Defined words by layer" in `design`.
fn table(design: &str) -> Vec<Row> {
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
            Row {
                layer: cells[1][1..].parse().expect("a layer number"),
                annots: spans(cells[2]),
                facets: spans(cells[3]),
                forms: spans(cells[4]),
            }
        })
        .collect()
}

#[test]
fn the_resolver_holds_every_word_and_type_of_the_table() {
    let Some(spec) = zed_tests::spec::dir("the table \"Defined words by layer\"") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).unwrap();
    let rows = table(&design);
    assert!(rows.len() > 20, "the table has {} rows", rows.len());
    // The first layer a name is listed at is its layer: `Ast` returns at L11 with members.
    let mut words: BTreeMap<String, u32> = BTreeMap::new();
    let mut types: BTreeMap<String, u32> = BTreeMap::new();
    for Row {
        layer,
        annots,
        facets,
        forms,
    } in &rows
    {
        for a in annots {
            let name = a.strip_prefix('@').expect("an annotation");
            if PENDING.iter().any(|(n, _)| *n == name) {
                assert_eq!(
                    annotation_layer(name),
                    None,
                    "@{name} is built: remove it from PENDING"
                );
                continue;
            }
            assert_eq!(annotation_layer(name), Some(*layer), "@{name}");
        }
        // A facet word is a value word: the prelude binds the `Facet` value to the name.
        let tag = format!("L{layer}");
        for f in facets {
            assert!(
                f.chars().next().is_some_and(char::is_lowercase)
                    && f.chars().all(char::is_alphanumeric),
                "the facet `{f}` of {tag} is not a lower-case name"
            );
            if PENDING.iter().any(|(n, _)| n == f) {
                assert_eq!(
                    prelude_layer(f),
                    None,
                    "`{f}` is built: remove it from PENDING"
                );
                continue;
            }
            if PROGRAM_FACETS.contains(&(tag.as_str(), f.as_str())) {
                assert_eq!(prelude_layer(f), None, "the program's facet `{f}`");
            } else {
                words.entry(f.clone()).or_insert(*layer);
            }
        }
        let names = forms.iter().filter(|f| {
            f.chars().next().is_some_and(char::is_alphabetic)
                && f.chars().all(char::is_alphanumeric)
                && !NOT_PRELUDE_NAMES.contains(&(tag.as_str(), f.as_str()))
        });
        for f in names {
            if PENDING.iter().any(|(n, _)| n == f) {
                assert_eq!(
                    prelude_layer(f),
                    None,
                    "`{f}` is built: remove it from PENDING"
                );
                assert!(
                    !zedc::resolve::is_prelude_name(f),
                    "`{f}` is built: remove it from PENDING"
                );
                continue;
            }
            let upper = f.chars().next().is_some_and(char::is_uppercase);
            let alias = ALIASES.contains(&f.as_str());
            if !upper && !alias {
                words.entry(f.clone()).or_insert(*layer);
            }
            if upper || alias || LOWER_TYPES.contains(&f.as_str()) {
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
