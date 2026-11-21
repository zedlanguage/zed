//! The prelude words, facet words and types of later layers (DESIGN.md sec:grammar, "Defined
//! words by layer"): a use of one that no program name shadows is reported as a word this zedc
//! does not support, not as a name that is not defined.

#[cfg(feature = "spec")]
use std::collections::BTreeMap;

use super::errors;
#[cfg(feature = "spec")]
use zedc::resolve::{ANNOTATIONS, LATER_TYPES, WORDS, annotation_layer, prelude_layer};

#[test]
fn a_later_word_is_reported_as_not_compiled_yet() {
    assert_eq!(
        errors("f(xs) = any(xs);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `any`"),
            " [any]"
        )]
    );
    assert_eq!(
        errors("f(n) = upTo(n);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `upTo`"),
            " [upTo]"
        )]
    );
    assert_eq!(
        errors("f(a, b) = merge(a, b);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `merge`"),
            " [merge]"
        )]
    );
    assert_eq!(
        errors("f(g) = compile(g);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `compile`"),
            " [compile]"
        )]
    );
    // A program's own name shadows the word at any layer.
    assert_eq!(errors("find = 0;\nf() = find;\n"), Vec::<String>::new());
}

/// A facet is a value of the prelude struct `Facet` bound to a name (DESIGN.md
/// sec:checking_in_zed), so a prelude facet named below its layer is reported as not compiled
/// yet.
#[test]
fn a_facet_word_is_reported_as_not_compiled_yet() {
    assert_eq!(
        errors("f(x) = order(x);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `order`"),
            " [order]"
        )]
    );
    assert_eq!(
        errors("f(s) = units(s);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `units`"),
            " [units]"
        )]
    );
    assert_eq!(
        errors("f(n) = retry(n);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `retry`"),
            " [retry]"
        )]
    );
    assert_eq!(
        errors("f() = target;\n"),
        [concat!(
            zed_tests::not_yet!("the prelude word `target`"),
            " [target]"
        )]
    );
    // A facet a program defines is its own name: not defined until the program binds it.
    assert_eq!(
        errors("f() = parity;\n"),
        ["`parity` is not defined. [parity]"]
    );
    // A parameter or a binding shadows a facet word at any layer.
    assert_eq!(
        errors("area(length, at) = length * at;\nrate = 2;\ng() = rate;\n"),
        Vec::<String>::new()
    );
}

#[test]
fn a_later_type_is_reported_as_not_compiled_yet() {
    assert_eq!(
        errors("f(t: Instant) = t;\n"),
        [concat!(
            zed_tests::not_yet!("the prelude type `Instant`"),
            " [Instant]"
        )]
    );
    assert_eq!(
        errors("f(s: Seq(int)) = s;\n"),
        [concat!(
            zed_tests::not_yet!("the prelude type `Seq`"),
            " [Seq]"
        )]
    );
    assert_eq!(
        errors("f(z: complex(f64)) = z;\n"),
        [concat!(
            zed_tests::not_yet!("the prelude type `complex`"),
            " [complex]"
        )]
    );
    // A struct of the prelude is also named as a value, to build one.
    assert_eq!(
        errors("f() = Facet(1);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude type `Facet`"),
            " [Facet]"
        )]
    );
    assert_eq!(
        errors("f() = Facett(1);\n"),
        ["`Facett` is not defined. [Facett]"]
    );
}

/// `u8 = int[0..=255]`, `i8` to `i128` and `u16` to `u128` are the fixed-width aliases, names
/// of their ranges from step L1.12 (DESIGN.md sec:domains; QUESTIONS A72), which stand where a
/// range does; and `byte` is no type at any layer (author decision 2026-11-04: the type `byte`
/// is renamed `u8`).
#[test]
fn the_fixed_width_aliases_are_ranges_of_l1_and_byte_is_none() {
    assert_eq!(errors("checksum(b: u8) = b;\n"), Vec::<String>::new());
    assert_eq!(
        errors("status(rc: i32, flags: i8, big: u128, wide: i128) = rc;\n"),
        Vec::<String>::new()
    );
    assert_eq!(
        errors("checksum(b: byte) = b;\n"),
        ["The type `byte` is not defined. [byte]"]
    );
    // A range stands only as the whole type of a parameter or a key, and so does an alias; the
    // `u8` of a union is refused as a range there is, a form of a later step, which `errors`
    // leaves out (`carrier_names.rs` of l01_29 tests that message).
    assert_eq!(
        errors("checksum(b: u8 | byte) = b;\n"),
        ["The type `byte` is not defined. [byte]"]
    );
    // As a value an alias is the cast `u8(300)` (sec:corner_cases, "Casts are domain
    // proofs"), which waits for plan row INT-128.
    assert_eq!(
        errors("f() = u8(300);\n"),
        [concat!(
            zed_tests::not_yet!("the prelude type `u8` as a value, the cast `u8(x)`"),
            " [u8]"
        )]
    );
    // A program's own name `byte`, `u8` or `i32` is an ordinary binding.
    assert_eq!(
        errors("f(byte) = byte + 1;\ng(u8) = u8 * 2;\ni32 = 7;\nh() = i32;\n"),
        Vec::<String>::new()
    );
}

/// The names of the table that the resolver does not hold, each with the reason: a name the
/// program declares, a port a program names in `main`'s header, a compiler mode, which is no name
/// in source, a word of L1 that a later layer extends to more types, and `files`, which every
/// function reads as `main::files`, a field of `main` (QUESTIONS A68), and which alone names
/// nothing.
#[cfg(feature = "spec")]
const NOT_PRELUDE_NAMES: &[(&str, &str)] = &[
    ("L1", "main"),
    ("L1", "files"),
    ("L7", "clock"),
    ("L7", "log"),
    ("L14", "abs"),
    ("L17", "total"),
    ("L18", "preallocated"),
];

/// The words of later layers the table does not list, each a prelude function that enters with the
/// types it takes and returns (the paragraph before the table): `count` takes a family.
#[cfg(feature = "spec")]
const UNLISTED: &[(&str, u32)] = &[("count", 3)];

/// The lower-case names of the table that are types as well as words: the number algebras
/// of L14 and the float formats of L1, which are applied to build a value as `int(…)` is.
#[cfg(feature = "spec")]
const LOWER_TYPES: &[&str] = &["complex", "quat", "oct", "bf16", "f16"];

/// The lower-case names of the table that are types and not words: the fixed-width aliases of L1
/// (DESIGN.md sec:domains, step L1.12), which no program applies to a value.
#[cfg(feature = "spec")]
const ALIASES: &[&str] = &zedc::fixed_width::NAMES;

/// The facets of the table's third column that a program defines, as examples of the rule
/// "every facet a program defines": names of the program, not of the prelude.
#[cfg(feature = "spec")]
const PROGRAM_FACETS: &[(&str, &str)] = &[("L12", "parity"), ("L12", "latency"), ("L12", "dist")];

/// Names of the table whose rows are not built, each with the plan row that builds it: the test
/// holds that each is not yet known, or, for an annotation, that it is listed at its layer and
/// still refused as not supported, so that row must take it out of this list.
#[cfg(feature = "spec")]
const PENDING: &[(&str, &str)] = &[
    ("failure", "PORT-ack-name"),
    ("Set", "SET-type-check"),
    ("keeps", "L7.4"),
    ("consumes", "L7.4"),
    ("names", "L38.2"),
    ("bitorder", "TERM-1"),
    ("stack", "L18.2c"),
    ("memoizationArena", "L18.2e"),
    // Also the L22 form `equivalent` of the boolean formulas (SYM-bool-formulas): when this
    // entry goes, `zedc::resolve::WORDS` gains `("equivalent", 22)`.
    ("equivalent", "COST-required"),
    ("fpstrict", "FPWARN"),
    ("fpsafe", "FPWARN"),
    ("approx", "L10.3d"),
    ("cryptosafe", "L33.1e"),
    ("ctDivRem", "L33.1e"),
    ("f16", "L1.18a"),
    ("bf16", "L1.18a"),
    ("f32Bits", "L1.18a"),
    ("f16Bits", "L1.18a"),
    ("bf16Bits", "L1.18a"),
    // `i128`, `u16`, `u32`, `u64` and `u128` are names of their ranges from step L1.12
    // (PRINT-int-carrier-names); a cast to one, `x as u32`, waits for INT-128 still.
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
    ("now", "DYN-port"),
    ("clock", "DYN-port"),
    ("randomBytes", "DYN-port"),
    ("spawn", "DYN-port"),
    ("run", "DYN-port"),
    ("Process", "DYN-port"),
    ("connect", "DYN-port"),
    ("listen", "DYN-port"),
    ("kill", "DYN-port"),
    ("limits", "DYN-port"),
    ("wallTime", "DATE-lib"),
    ("systemZone", "DATE-lib"),
    ("via", "CODEC-kind"),
    ("LossyCodec", "CODEC-kind"),
    ("DecodeFailure", "CODEC-kind"),
    ("utf8Text", "CODEC-utf8"),
    ("utf16Text", "CODEC-utf8"),
    ("utf32Text", "CODEC-utf8"),
    ("escaped", "CODEC-utf8"),
    ("rawLines", "CODEC-lines"),
    ("textLines", "CODEC-lines"),
    ("Line", "CODEC-lines"),
    ("RawLine", "CODEC-lines"),
    ("each", "CODEC-frame"),
    ("delimited", "CODEC-frame"),
    ("lengthPrefixed", "CODEC-frame"),
    ("fixedSize", "CODEC-frame"),
    ("Codec", "CODEC-laws"),
    ("CanonicalCodec", "CODEC-laws"),
    ("records", "CODEC-grammar"),
    ("json", "CODEC-json"),
    ("csv", "CODEC-json"),
    ("countedIn", "UNITS-text-lengths"),
    ("normalize", "STR-normalize-layer"),
    ("utf16Units", "STR-normalize-layer"),
];

/// A row of the table "Defined words by layer": its layer, and its annotations, facet words and
/// defined forms, each the text of its code spans.
#[cfg(feature = "spec")]
struct Row {
    layer: u32,
    annots: Vec<String>,
    facets: Vec<String>,
    forms: Vec<String>,
}

/// Each row of the table "Defined words by layer" in `design`, the spec's DESIGN.md.
#[cfg(feature = "spec")]
fn table(design: &str) -> Vec<Row> {
    let spans = |cell: &str| -> Vec<String> {
        cell.split('`')
            .skip(1)
            .step_by(2)
            .map(str::to_string)
            .collect()
    };
    design
        .lines()
        .skip_while(|l| !l.starts_with("| Layer | Annotations | Facet words"))
        .skip(2)
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

#[cfg(feature = "spec")]
#[test]
fn the_resolver_holds_every_word_and_type_of_the_table() {
    let rows = table(zed_tests::spec::design());
    assert!(rows.len() > 20, "the table has {} rows", rows.len());
    // The first layer a name is listed at is its layer: `Ast` returns at L11 with members.
    let mut words: BTreeMap<String, u32> = BTreeMap::new();
    let mut types: BTreeMap<String, u32> = BTreeMap::new();
    let mut listed: BTreeMap<String, u32> = BTreeMap::new();
    for Row {
        layer,
        annots,
        facets,
        forms,
    } in &rows
    {
        for a in annots {
            let name = a.strip_prefix('@').expect("an annotation");
            // A pending annotation is listed at its layer, as every other is, so that it is
            // refused as not supported; what tells it from a built one is that it still is.
            assert_eq!(annotation_layer(name), Some(*layer), "@{name}");
            if PENDING.iter().any(|(n, _)| *n == name) {
                assert!(
                    not_compiled_yet(name),
                    "@{name} is built: remove it from PENDING"
                );
            }
            listed.entry(name.to_string()).or_insert(*layer);
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
    // Nor an annotation the table no longer lists, as `@teardown` after the spec replaced it
    // by a token (zed 32909bd).
    let unlisted: Vec<(&str, u32)> = ANNOTATIONS
        .iter()
        .filter(|&&(a, l)| listed.get(a) != Some(&l))
        .copied()
        .collect();
    assert_eq!(
        unlisted,
        [] as [(&str, u32); 0],
        "the annotations the table does not list"
    );
    for &(t, layer) in LATER_TYPES {
        assert!(
            types.get(t) == Some(&layer),
            "the type `{t}` of L{layer} is not in the table"
        );
    }
}

/// Whether a function annotated `@name` is refused with the message that names the annotation
/// as not supported.
#[cfg(feature = "spec")]
fn not_compiled_yet(name: &str) -> bool {
    let src = format!("@{name} f(x: f64) = x;\nmain(m: MainArgs) = 0;\n");
    zedc::run::load(src.as_bytes())
        .is_err_and(|out| out.contains(&zed_tests::not_yet(&format!("the annotation `@{name}`"))))
}

/// An annotation that DESIGN lists in "Defined words by layer" but whose step is not built yet is
/// reported as not supported, as any later word is, and not as "is not an annotation" (plan
/// row FAIL-pending-annotation-message: `@fpwarn` got that false message on zed-impl 6b74dc09c).
#[test]
fn an_annotation_of_a_later_step_not_yet_built_is_reported_as_not_compiled_yet() {
    for name in [
        "stack",
        "memoizationArena",
        "equivalent",
        "fpstrict",
        "fpsafe",
        "approx",
        "cryptosafe",
    ] {
        let src = format!("@{name} f(x: f64) = x;\nmain(m: MainArgs) = 0;\n");
        let Err(out) = zedc::run::load(src.as_bytes()) else {
            panic!("accepted:\n{src}")
        };
        assert!(!out.contains("is not an annotation"), "@{name}: {out}");
        assert!(
            out.contains(&format!(
                "the annotation `@{name}` is part of the Zed language but is not supported by \
                 this version of zedc."
            )),
            "@{name}: {out}"
        );
    }
}
