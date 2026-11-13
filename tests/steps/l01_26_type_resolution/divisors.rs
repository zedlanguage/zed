//! A division, `div` or `mod` whose divisor's type holds no zero adds no `#divByZero`
//! (DESIGN.md step L1.26). At layer L1 a divisor gets such a type from literals that survive
//! an `if` (step L1.26a), as `1 | 9` or `-3 | -1`, directly or through a call; a divisor
//! whose type holds `0` keeps `#divByZero`, and so does an `int`. The types written in a
//! declaration, `d: int[1..=9]`, and a test that narrows, `if d != 0`, are layer L10's, and
//! their cases are kept below, ignored until zedc compiles them.

use super::{sig, type_errors};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// A divisor of one of two literals, neither zero.
const NINE: &str = "nine(positional c: bool) = if c { 1 } else { 9 };\n";

/// A divisor of one of two negative literals.
const NEG: &str = "neg(positional c: bool) = if c { -3 } else { -1 };\n";

/// A divisor that may be zero.
const ZERO: &str = "zero(positional c: bool) = if c { 0 } else { 9 };\n";

/// The rejection of `_` dropping `#divByZero` at the statement `stmt`.
fn drops_div_by_zero(stmt: &str) -> String {
    format!(
        "`_` drops a loose failure this value may be, #divByZero: `_` drops only a failure the \
         program names, as the default of an `else` names it, and this one would be dropped \
         with nothing in the text saying so. [{stmt}]"
    )
}

#[test]
fn a_divisor_of_literals_that_are_not_zero_adds_no_div_by_zero() {
    assert_eq!(sig(NINE, "nine"), "(bool) -> 1 | 9");
    let div = format!("{NINE}f(positional c: bool, x: int) = x div nine(c);\n");
    assert_eq!(sig(&div, "f"), "(bool, x: int) -> int");
    let neg = format!("{NEG}f(positional c: bool, x: int) = x div neg(c);\n");
    assert_eq!(sig(&neg, "f"), "(bool, x: int) -> int");
    let modulo = format!("{NINE}f(positional c: bool, x: int) = x mod nine(c);\n");
    assert_eq!(sig(&modulo, "f"), "(bool, x: int) -> int");
    // Written in place, and bound to a name first.
    assert_eq!(
        sig(
            "f(positional c: bool, x: int) = x div (if c { 2 } else { -3 });\n",
            "f"
        ),
        "(bool, x: int) -> int"
    );
    assert_eq!(
        sig(
            "f(positional c: bool, x: int) = { d = if c { 1 } else { 9 }; x div d };\n",
            "f"
        ),
        "(bool, x: int) -> int"
    );
    // At `rat`, through `/`.
    assert_eq!(
        sig(
            "f(positional c: bool, x: rat) = x / (if c { 2r } else { 3r });\n",
            "f"
        ),
        "(bool, x: rat) -> rat"
    );
    let run = format!("{div}a = f(true, x: 20);\nb = f(false, x: 20);\n");
    assert_eq!(value(&run, "a"), "20");
    assert_eq!(value(&run, "b"), "2");
    // `div` is Euclidean (sec:domains): 20 = -6 * -3 + 2.
    let run = format!("{neg}a = f(true, x: 20);\nb = f(false, x: -7);\n");
    assert_eq!(value(&run, "a"), "-6");
    assert_eq!(value(&run, "b"), "7");
}

#[test]
fn a_divisor_that_may_be_zero_keeps_div_by_zero() {
    let div = format!("{ZERO}f(positional c: bool, x: int) = x div zero(c);\n");
    assert_eq!(sig(&div, "f"), "(bool, x: int) -> int | #divByZero");
    let modulo = format!("{ZERO}f(positional c: bool, x: int) = x mod zero(c);\n");
    assert_eq!(sig(&modulo, "f"), "(bool, x: int) -> int | #divByZero");
    assert_eq!(
        sig(
            "f(positional c: bool, x: rat) = x / (if c { 2r } else { 0r });\n",
            "f"
        ),
        "(bool, x: rat) -> rat | #divByZero"
    );
    assert_eq!(
        sig("f(x: int, d: int) = x div d;\n", "f"),
        "(x: int, d: int) -> int | #divByZero"
    );
    let run = format!("{div}a = f(true, x: 20);\nb = f(false, x: 20);\n");
    assert_eq!(value(&run, "a"), "#divByZero");
    assert_eq!(value(&run, "b"), "2");
}

#[test]
fn underscore_drops_the_quotient_only_where_the_divisor_cannot_be_zero() {
    // With no `#divByZero` in its type, the quotient holds no loose failure, and `_` takes it.
    let nine = format!("{NINE}f(positional c: bool, x: int) = {{ _ = x div nine(c); x }};\n");
    assert_eq!(type_errors(&nine), Vec::<String>::new());
    let zero = format!("{ZERO}f(positional c: bool, x: int) = {{ _ = x div zero(c); x }};\n");
    assert_eq!(
        type_errors(&zero),
        [drops_div_by_zero("_ = x div zero(c);")]
    );
}

#[test]
#[ignore = "open: the refinement `int[1..=9]` in a parameter type is layer L10 (step L10.1), \
            and zedc refuses it at L1"]
fn a_divisor_declared_without_zero_adds_no_div_by_zero() {
    // DESIGN.md step L1.26: "A division, `div` or `mod` whose divisor's type holds no zero
    // adds no `#divByZero`."
    for (d, want) in [
        ("int[1..=9]", "int"),
        ("int[-3..=-1]", "int"),
        ("int[0..=9]", "int | #divByZero"),
    ] {
        let text = format!("f(x: int, d: {d}) = x div d;\n");
        assert_eq!(
            sig(&text, "f"),
            format!("(x: int, d: {d}) -> {want}"),
            "{d}"
        );
    }
}

#[test]
#[ignore = "open: zedc narrows by `==` and `!=` only against an atom, so `d != 0` leaves `d` \
            an `int` and the quotient keeps `#divByZero`; the type `int` without `0` is a \
            refinement of layer L10"]
fn a_divisor_narrowed_by_a_test_adds_no_div_by_zero() {
    // DESIGN.md sec:type_resolution rule 3: "The checker maintains per-node proposition sets
    // (facts learned by tests)", and step L1.26 on a divisor whose type holds no zero.
    assert_eq!(
        sig(
            "f(x: int, d: int) = if d != 0 { x div d } else { 0 };\n",
            "f"
        ),
        "(x: int, d: int) -> int"
    );
}

/// A divisor, or the base of a `^` under a negative exponent, that is an operation on
/// literals alone has the value its text gives, and one that is no zero adds no
/// `#divByZero`: `(2r/3r)^-2` is `9r/4r` and `1r / (2r/3r)` is `3r/2r`, though `rat` holds
/// `0r` (POW-rat-literal-ops). An integer literal as the exponent keeps `int`, so
/// `(3/2)^-2` in a sum with a `rat` is the exact `4r/9r`.
#[test]
fn a_divisor_or_base_that_is_an_operation_on_literals_adds_div_by_zero_only_at_zero() {
    for (body, at_one) in [
        ("x + (2r/3r)^-2", "13r/4r"),
        ("x + 1r / (2r/3r)", "5r/2r"),
        ("x / (2r/3r)", "3r/2r"),
        ("x + (3/2)^-2", "13r/9r"),
        ("x + (3/2)^-2 * 1r", "13r/9r"),
        ("x - (3/2)^-3", "19r/27r"),
        ("x + 1 / (2/3)", "5r/2r"),
        // A power's value is not computed; the range the text gives of it is enough here:
        // `3r^2 + 1r` is at least `1r`, `2r^10 - 1r` at least `3r`, `2r^2 - 3r` at least `1r`,
        // since a power of a value of the text is read as at least its square, `(1r/2r)^3 - 1r`
        // at most `-3r/4r`, and `(-2r)^3 + 1r` at most `-3r`.
        ("x + 1r / (3r^2 + 1r)", "11r/10r"),
        ("x + 1r / (2r^10 - 1r)", "1024r/1023r"),
        ("x + 1r / (2r^2 - 3r)", "2r"),
        ("x + 1r / ((1r/2r)^3 - 1r)", "-1r/7r"),
        ("x + 1r / ((-2r)^3 + 1r)", "6r/7r"),
        ("x + (1r/2r - 1r/3r)^-3", "217r"),
    ] {
        let text = format!("f(x: rat) = {body};\n");
        assert_eq!(sig(&text, "f"), "(x: rat) -> rat", "{body}");
        assert_eq!(
            value(&format!("{text}y = f(x: 1r);\n"), "y"),
            at_one,
            "{body}"
        );
    }
    // A divisor or base whose value is zero, or not known from the text, keeps `#divByZero`.
    for body in [
        "x + (0r)^-1",
        "x + 1r / (1r - 1r)",
        "x + (1 - 1)^-1 * 1r",
        "x / (1 - 1)",
        "x ^ -2",
        "1r / x",
        // Zero, and a range that holds `0r`: `(-2r)^2 - 4r` is `0r`; `2r^3 - 5r`, which is `3r`,
        // is read as at least `-1r`, since `2r^3` is read as at least `2r^2`, and
        // `(2r^2)^2 - 5r`, which is `11r`, too, since the square is taken only of a value of the
        // text, not of the range of `2r^2`.
        "x + 1r / ((-2r)^2 - 4r)",
        "x + (3r^2 - 9r)^-1",
        "x + 1r / (2r^3 - 5r)",
        "x + 1r / ((2r^2)^2 - 5r)",
    ] {
        let text = format!("f(x: rat) = {body};\n");
        assert_eq!(sig(&text, "f"), "(x: rat) -> rat | #divByZero", "{body}");
    }
    assert_eq!(
        value("f(x: rat) = x + (0r)^-1;\ny = f(x: 1r);\n", "y"),
        "#divByZero"
    );
    // Value typing narrows a result inside an arrow `^` has and makes none: `^` has no arrow
    // (rat, rat), so `4r ^ 0.5r` is refused though its value would be `2r`.
    assert_eq!(type_errors("f(x: rat) = x + 4r ^ 0.5r;\n").len(), 1);
}
