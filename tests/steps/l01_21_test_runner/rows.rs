//! A `// ✗` comment that names a row of the rejection table (DESIGN.md sec:diagnostics) is
//! checked against the row of the diagnostic on its line; one that names no row accepts any.

use zedc::rejection::Row;

use super::checks;

const ROWS: &str = include_str!("../../../zed/fences/rejections.txt");

#[test]
fn the_rows_are_those_of_the_spec_table() {
    let names: Vec<&str> = Row::ALL.iter().map(|r| r.name()).collect();
    let spec: Vec<&str> = ROWS.lines().collect();
    assert_eq!(names, spec);
}

#[test]
fn a_comment_names_a_row_by_its_name_and_a_colon() {
    let cases = [
        (
            " Missing argument: name has no default",
            Some(Row::MissingArgument),
        ),
        (
            " Unreachable `match` arm: every Temp already matched",
            Some(Row::UnreachableArm),
        ),
        (" Missing argument has no colon", None),
        (" compile error: unit mismatch", None),
        (" Missing arguments: a plural is another name", None),
        (" missing argument: the case differs", None),
    ];
    for (comment, want) in cases {
        assert_eq!(Row::named_by(comment), want, "{comment}");
    }
}

/// A label printer whose calls break each argument rule L1 checks: each mark names its row.
const LABELS: &str = include_str!("zed/labels.zed");

#[test]
fn each_argument_rule_names_its_row() {
    assert_eq!(
        checks(LABELS),
        ["5:5: ok", "6:17: ok", "7:5: ok", "8:25: ok"]
    );
}

#[test]
fn a_linear_question_outside_the_fragment_names_its_row() {
    // Four variables: a splinter over three is now decided (LIVE3).
    let unit = "ok(x, y, z, w) = 9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= \
                0 && -7 * x - 12 * y - 2 * z + 8 * w - 1 >= 0 && -9 * x + 8 * y + 7 * z >= 0 && \
                -10 * x + 4 * y - 6 * z - 4 * w + 22 >= 0;  // ✗ Linear question outside the \
                polynomial fragment of the linear-relation domain: a splinter\n";
    assert_eq!(checks(unit), ["1:1: ok"]);
}

#[test]
fn a_mark_naming_another_row_fails_with_both_rows() {
    let unit = "\
label(positional name: String, city: String) = name ++ \", \" ++ city;
a = label(city: \"Leeds\");    // ✗ Argument in the wrong form: but the name is left out
";
    assert_eq!(
        checks(unit),
        [
            "2:5: the mark names the row \"Argument in the wrong form\", and the diagnostic is \
             in the row \"Missing argument\": missing argument `name` of `label`"
        ]
    );
}

#[test]
fn a_mark_naming_a_row_fails_on_a_diagnostic_in_no_row() {
    let unit = "total = 3 + \"pounds\";    // ✗ Missing argument: not this one\n";
    let got = checks(unit);
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        got[0].starts_with(
            "1:9: the mark names the row \"Missing argument\", and the diagnostic is in no row \
             of the rejection table: "
        ),
        "{got:?}"
    );
}

#[test]
fn a_mark_naming_no_row_accepts_any_row() {
    let unit = "\
label(positional name: String, city: String) = name ++ \", \" ++ city;
a = label(city: \"Leeds\");    // ✗ the name is left out
";
    assert_eq!(checks(unit), ["2:5: ok"]);
}

/// A fee calculator called with its rate named before its positional base: the grammar takes
/// either order, and the check names the row, the argument, the first named one and the call.
#[test]
fn a_positional_argument_after_a_named_one_names_its_row() {
    let decl = "fee(positional base: int, rate: int) = base * rate;\n";
    let unit = format!(
        "{decl}f = fee(rate: 3, 5);    // ✗ Named argument before a positional one: 5 goes first\n"
    );
    assert_eq!(checks(&unit), ["2:18: ok"]);
    let Err(why) = zedc::run::load(format!("{decl}f = fee(rate: 3, 5);\n").as_bytes()) else {
        panic!("the call is accepted")
    };
    assert_eq!(
        why,
        "\
2:18: a positional argument after the named argument `rate`: a call passes its positional \
arguments first, then its named ones
  [1] 2:9: the first named argument, `rate`
      2 | f = fee(rate: 3, 5);
        |         ^^^^
  [2] 2:5: the call
      2 | f = fee(rate: 3, 5);
        |     ^^^^^^^^^^^^^^^"
    );
}

/// The same rule for an annotation's arguments, and for a call that begins with positional
/// arguments, then names one and passes another by position.
#[test]
fn an_annotation_argument_after_a_named_one_names_its_row() {
    let unit = "@doc(lang: \"en\", \"a fee\")    // ✗ Named argument before a positional one: \
                the text goes first\n\
                fee(positional base: int) = base;\n";
    assert_eq!(checks(unit), ["1:18: ok"]);
    let decl = "fee(positional base: int, positional cap: int, rate: int) = base * rate;\n";
    let unit = format!(
        "{decl}f = fee(7, rate: 3, 5);    // ✗ Named argument before a positional one: 5 too\n"
    );
    assert_eq!(checks(&unit), ["2:21: ok"]);
}

/// A surcharge declared with its positional base after its named rate, and a lambda whose
/// tuple parameter, positional without the keyword, follows a named one.
#[test]
fn a_positional_parameter_after_a_named_one_names_its_row() {
    let unit = "surcharge(rate: int, positional base: int) = base * rate;    // ✗ `positional` \
                parameter after a named one: base goes first\n";
    assert_eq!(checks(unit), ["1:22: ok"]);
    let lambda = "h = (rate, (a, b)) -> a * rate;    // ✗ `positional` parameter after a named \
                  one: the tuple goes first\n";
    assert_eq!(checks(lambda), ["1:12: ok"]);
    let Err(why) = zedc::run::load(b"surcharge(rate: int, positional base: int) = base * rate;\n")
    else {
        panic!("the declaration is accepted")
    };
    assert_eq!(
        why,
        "\
1:22: the positional parameter `base` comes after the named parameter `rate`: a declaration \
lists its positional parameters first
  [1] 1:11: the first named parameter, `rate`
      1 | surcharge(rate: int, positional base: int) = base * rate;
        |           ^^^^^^^^^
  [2] 1:1: the declaration
      1 | surcharge(rate: int, positional base: int) = base * rate;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
    );
}

/// Positional items first, then named ones (named in any order), are accepted and run.
#[test]
fn positional_items_before_named_ones_are_accepted() {
    let unit = "\
fee(positional base: int, positional lo: int, rate: int, cap: int = 9) = base * rate + lo + cap;
f(x) = fee(x, 1, rate: 3) + fee(x, 1, cap: 4, rate: 3) test { 2 -> 27 }
";
    assert_eq!(checks(unit), ["2:63: ok"]);
}
