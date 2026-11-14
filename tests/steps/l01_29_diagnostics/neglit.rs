//! A prefix `-` on a postfix chain whose base is a numeric literal (DESIGN.md sec:diagnostics,
//! row "Prefix `-` on a numeric literal's postfix chain", and tier 3 of the precedence table):
//! `-1.abs` parses as `-(1.abs)`, which is `-1`, so it is rejected after parsing with the
//! chain, the value each grouping gives, and both groupings as repairs.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Lookup;
use zedc::ast::{Error, unit};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;
use zedc::run::load;
use zedc::testing::test;

use super::rejected;

/// The syntax tree of the unit `text`, or its error.
fn built(text: &str) -> Result<(), Error> {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP)
        .unwrap_or_else(|e| panic!("{text:?} does not parse: {e}"));
    unit(text, &tokens, &tree).map(|_| ())
}

/// A program that prints `e`.
fn printing(e: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n  offset = {e};\n  m.stdout <- \"offset: \" ++ String(offset);\n}}\n"
    )
}

#[test]
fn a_negated_literal_made_absolute_shows_both_groupings_with_their_values() {
    let out = rejected(&printing("-1.abs"));
    assert_eq!(
        out,
        "2:12: a prefix `-` stands before a postfix chain whose base is the number `1`, and the \
chain binds tighter than the `-`, so this is `-(1.abs)`, which is -1, not `(-1).abs`, which is 1. \
Write the grouping you mean.
  [1] 2:13: the chain starts at the numeric literal `1`
      2 |   offset = -1.abs;
        |            ^^^^^^ [3, 4, 5]
        |             ^ [1]
        |             ^^^^^ [2]
  [2] 2:13: the postfix chain `1.abs` binds tighter than a prefix `-` (precedence tiers 1 and 3)
  [3] 2:12: so the `-` applies to the whole chain: `-(1.abs)`, which is -1
  [4] 2:12: repair: `(-1).abs`, the chain started at `-1`, which is 1
  [5] 2:12: repair: `-(1.abs)`, the meaning as written, which is -1"
    );
}

#[test]
fn the_rejection_names_its_row_and_a_marked_line_checks_it() {
    let err = built("drift = -1.abs;\n").unwrap_err();
    assert_eq!(err.row, Some(Row::PrefixMinus));
    let text = include_str!("zed/offsets.zed");
    let failures: Vec<String> = test(text)
        .into_iter()
        .filter_map(|o| o.failure.map(|f| format!("{}: {f}", o.line)))
        .collect();
    assert!(failures.is_empty(), "{failures:?}");
}

#[test]
fn each_repair_is_accepted_and_prints_its_value() {
    for (e, want) in [("(-1).abs", "offset: 1"), ("-(1.abs)", "offset: -1")] {
        let p = load(printing(e).as_bytes()).unwrap_or_else(|err| panic!("{e}: {err}"));
        let mut lines = BTreeMap::new();
        lines.insert("stdin".to_string(), Arc::from([]));
        let files = |_: &str| -> Arc<dyn Lookup> { unreachable!("no `Files` port") };
        let wave = p.run(&lines, files).unwrap();
        let (_, bytes) = &wave.writes[0];
        assert_eq!(String::from_utf8_lossy(bytes).trim_end(), want, "{e}");
    }
}

#[test]
fn only_a_chain_on_a_numeric_literal_under_a_prefix_minus_is_rejected() {
    let cases = [
        // The rejected forms: spaced, float, rational, hexadecimal, a longer chain, a call,
        // an index, inside a call's argument, under `^`'s right operand, doubled.
        ("- 1.abs", true),
        ("-2.5.abs", true),
        ("-0.5r.abs", true),
        ("-0x1F.abs", true),
        ("-1.abs.abs", true),
        ("-1.clamp(0, 8)", true),
        ("-1[0]", true),
        ("f(-1.abs)", true),
        ("2^-1.abs", true),
        ("--1.abs", true),
        // Accepted: no chain, a grouped base, a grouped chain, a name as base, binary minus,
        // `!`, and a power, whose `-` applies to `1.abs ^ 2` as `-x ^ 2` is `-(x ^ 2)`.
        ("-1", false),
        ("-(1).abs", false),
        ("-(1.abs)", false),
        ("(-1).abs", false),
        ("-x.abs", false),
        ("x - 1.abs", false),
        ("!1.abs", false),
        ("-1.abs^2", false),
        ("-1 div 4", false),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(e, want)| {
            let got = built(&format!("y = {e};\n"))
                .err()
                .is_some_and(|err| err.row == Some(Row::PrefixMinus));
            (got != want).then(|| format!("{e}: rejected {got}, want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_float_literal_gives_float_values() {
    let out = rejected(&printing("-2.5.abs"));
    assert!(
        out.contains("this is `-(2.5.abs)`, which is -2.5, not `(-2.5).abs`, which is 2.5"),
        "{out}"
    );
}

#[test]
fn a_chain_whose_value_depends_on_what_it_names_shows_the_groupings_without_values() {
    // `clamp` is a function of the unit, so its value is not known when the unit is parsed.
    let out = rejected(&format!(
        "clamp(positional v, positional lo, positional hi) = if v < lo {{ lo }} else if v > hi {{ hi }} else {{ v }};\n{}",
        printing("-1.clamp(0, 8)")
    ));
    assert!(
        out.contains("so this is `-(1.clamp(0, 8))`, not `(-1).clamp(0, 8)`. Write"),
        "{out}"
    );
}

#[test]
fn a_unit_that_binds_the_word_shows_no_values() {
    // The unit's `abs` shadows the prelude word, so the prelude's values would be wrong.
    let out = rejected(&format!(
        "abs(positional x) = x * 2;\n{}",
        printing("-1.abs")
    ));
    assert!(
        out.contains("so this is `-(1.abs)`, not `(-1).abs`. Write"),
        "{out}"
    );
}

/// A unit of `n` definitions, each negating a chain of three words on a literal.
pub(super) fn many(n: usize) -> String {
    (0..n)
        .map(|i| format!("y{i} = -{i}.abs.abs.abs;\n"))
        .collect()
}

/// A unit with one definition negating a chain of `n` words on a literal.
pub(super) fn long(n: usize) -> String {
    format!("y = -1{};\n", ".abs".repeat(n))
}

/// [`many`]`(n)` is rejected by the row.
pub(super) fn many_chains_rejected(src: &str) {
    assert_eq!(built(src).unwrap_err().row, Some(Row::PrefixMinus));
}

/// [`long`]`(n)` is rejected with the value of the chain, -1.
pub(super) fn one_long_chain_rejected(src: &str) {
    let err = built(src).unwrap_err();
    assert!(err.message.contains("which is -1, not"), "{}", err.message);
}

#[test]
fn rejecting_many_chains_and_one_long_chain() {
    for n in [1, 3, 20] {
        many_chains_rejected(&many(n));
        one_long_chain_rejected(&long(n));
    }
}
