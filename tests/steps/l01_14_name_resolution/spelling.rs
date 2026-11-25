//! Step L1.14a: the row "Name that resolves to nothing" (DESIGN.md sec:diagnostics). The error
//! names the scopes searched, and its menu offers the value name visible at the use that is
//! nearest in spelling, then a definition of the name; each entry is offered only when the
//! program then resolves the name.

use zedc::ast::{Stmt, unit};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve_text;

/// The statements of the unit `text`.
pub(super) fn statements(text: &str) -> Vec<Stmt> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    unit(text, &tokens, &tree).unwrap()
}

/// The notes of the error "`name` is not defined." at the first use of `name` in the unit
/// `text`, resolved with its text, so that a repair is the line rewritten.
fn notes(text: &str, name: &str) -> Vec<String> {
    let errors = resolve_text(&statements(text), Some(text))
        .err()
        .unwrap_or_else(|| panic!("{text}: resolves"));
    let message = format!("`{name}` is not defined.");
    let e = (errors.iter())
        .find(|e| e.message == message)
        .unwrap_or_else(|| panic!("{text}: no error `{message}` in {errors:?}"));
    e.notes.iter().map(|n| n.text.to_string()).collect()
}

/// The lines `notes` offers as repairs, each `repair: \`line\``, as written.
fn repairs(notes: &[String]) -> Vec<String> {
    (notes.iter())
        .filter_map(|n| n.strip_prefix("repair: `")?.strip_suffix('`'))
        .map(str::to_string)
        .collect()
}

/// `text` with its line that holds `from`, trimmed, replaced by `to`.
fn rewritten(text: &str, from: &str, to: &str) -> String {
    let line = text
        .lines()
        .find(|l| l.contains(from))
        .unwrap_or_else(|| panic!("no line holds `{from}`"));
    text.replacen(line.trim(), to, 1)
}

/// Each repair line `notes` offers, put in place of the line of `text` that holds `from`,
/// leaves no error of `name`: the entry resolves the name.
fn each_repair_resolves(text: &str, from: &str, notes: &[String], name: &str) {
    let lines = repairs(notes);
    assert!(!lines.is_empty(), "{text}: no repair line in {notes:?}");
    for line in lines {
        let fixed = rewritten(text, from, &line);
        let message = format!("`{name}` is not defined.");
        if let Err(errors) = resolve_text(&statements(&fixed), Some(&fixed)) {
            assert!(
                errors.iter().all(|e| e.message != message),
                "{fixed}: {errors:?}"
            );
        }
    }
}

#[test]
fn a_misspelled_parameter_offers_the_parameter() {
    let text = "area(width, h) = widht * h;\n";
    let n = notes(text, "widht");
    assert_eq!(repairs(&n), ["area(width, h) = width * h;"], "{n:?}");
    assert!(n[0].starts_with("`widht` was looked for in "), "{n:?}");
    assert!(
        n[0].ends_with("the unit's top level, its imports and the prelude"),
        "{n:?}"
    );
    assert_eq!(
        n.last().map(String::as_str),
        Some("repair: define `widht` above its use, as `widht = …;`")
    );
    each_repair_resolves(text, "widht", &n, "widht");
}

#[test]
fn a_name_equal_once_case_and_underscores_are_folded_is_offered() {
    let text = "myCount = 3;\ntotal = my_count + 1;\n";
    let n = notes(text, "my_count");
    assert_eq!(repairs(&n), ["total = myCount + 1;"], "{n:?}");
    each_repair_resolves(text, "my_count", &n, "my_count");
}

#[test]
fn of_two_names_one_slip_away_the_first_in_name_order_is_offered() {
    let text = "width = 1;\nwyth = 2;\nx = wdth + 1;\n";
    let n = notes(text, "wdth");
    assert_eq!(repairs(&n), ["x = width + 1;"], "{n:?}");
    each_repair_resolves(text, "wdth", &n, "wdth");
}

#[test]
fn a_name_with_none_near_offers_only_a_definition() {
    let text = "x = zzz + 1;\n";
    let n = notes(text, "zzz");
    assert!(repairs(&n).is_empty(), "{n:?}");
    assert_eq!(
        n,
        [
            "`zzz` was looked for in the unit's top level, its imports and the prelude",
            "repair: define `zzz` above its use, as `zzz = …;`",
        ]
    );
    // The definition offered, above the use, resolves it.
    let fixed = "zzz = 0;\nx = zzz + 1;\n";
    assert!(resolve_text(&statements(fixed), Some(fixed)).is_ok());
}

#[test]
fn a_name_defined_below_its_use_in_a_block_is_not_offered() {
    // The row "Name used above its definition" (step L1.14), and no spelling entry from below.
    let text = "f(a) = {\n  y = c;\n  c = a;\n  y\n};\n";
    let errors = resolve_text(&statements(text), Some(text)).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].row,
        Some(zedc::rejection::Row::NameAboveDefinition)
    );
    // A near name declared below the use is not offered either.
    let text = "f(a) = {\n  y = cc;\n  c = a;\n  y\n};\n";
    let n = notes(text, "cc");
    assert!(repairs(&n).is_empty(), "{n:?}");
}

#[test]
fn a_name_bound_only_in_a_caller_is_not_offered() {
    // Names resolve where they are written (sec:units): `g` sees no parameter of `f`.
    let text = "g() = wdth;\nf(width) = g();\n";
    let n = notes(text, "wdth");
    assert!(repairs(&n).is_empty(), "{n:?}");
}

#[test]
fn a_name_in_an_inner_block_names_the_blocks_searched() {
    let text = "f(a) = {\n  b = {\n    c = a;\n    cc + c\n  };\n  b\n};\n";
    let n = notes(text, "cc");
    assert!(n[0].starts_with("`cc` was looked for in the "), "{n:?}");
    assert!(
        n[0].contains("blocks around its use, innermost first"),
        "{n:?}"
    );
    // `c`, one letter less, is visible there.
    assert_eq!(repairs(&n), ["c + c"], "{n:?}");
    each_repair_resolves(text, "cc + c", &n, "cc");
}

#[test]
fn a_prelude_word_is_offered() {
    let text = "x = abss(1);\n";
    let n = notes(text, "abss");
    assert_eq!(repairs(&n), ["x = abs(1);"], "{n:?}");
    each_repair_resolves(text, "abss", &n, "abss");
}

#[test]
fn batch_and_single_file_output_agree() {
    let units = [
        "area(width, h) = widht * h;\nmain() = 0;\n",
        "myCount = 3;\ntotal = my_count + 1;\nmain() = 0;\n",
        "width = 1;\nwyth = 2;\nx = wdth + 1;\nmain() = 0;\n",
        "x = zzz + 1;\nmain() = 0;\n",
        "g() = wdth;\nf(width) = g();\nmain() = 0;\n",
    ];
    let answer = |src: &str| zedc::run::load(src.as_bytes()).err();
    let alone: Vec<Option<String>> = (units.iter())
        .map(|src| {
            let src = src.to_string();
            std::thread::spawn(move || zedc::run::load(src.as_bytes()).err())
                .join()
                .unwrap()
        })
        .collect();
    let batch: Vec<Option<String>> = units.iter().map(|s| answer(s)).collect();
    let mut reversed: Vec<Option<String>> = units.iter().rev().map(|s| answer(s)).collect();
    reversed.reverse();
    assert_eq!(alone, batch);
    assert_eq!(alone, reversed);
    let first = alone[0].as_deref().expect("a rejection");
    assert!(first.contains("area(width, h) = width * h;"), "{first}");
}

/// A unit of `n` names and `n` uses, each a name one letter longer than a name defined:
/// `v0 = 0; … u0 = v0x; …`, so that each use resolves to nothing and is near one name.
pub(super) fn misspelled(n: usize) -> Vec<Stmt> {
    let mut text = String::new();
    for i in 0..n {
        text += &format!("v{i} = {i};\n");
    }
    for i in 0..n {
        text += &format!("u{i} = v{i}x;\n");
    }
    statements(&text)
}

#[test]
fn misspelled_uses_among_many_names_offer_each_its_name() {
    // A small instance of the benchmark `bench::spelling::misspelled_uses_scale`.
    let n = 20;
    let errors = zedc::resolve::resolve(&misspelled(n)).unwrap_err();
    assert_eq!(errors.len(), n);
    for (i, e) in errors.iter().enumerate() {
        assert_eq!(e.message, format!("`v{i}x` is not defined."));
        let want = format!("repair: write `v{i}`");
        assert!(e.notes.iter().any(|n| *n.text == *want), "{e:?}");
    }
}
