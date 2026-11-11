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
         with nothing in the text saying so [{stmt}]"
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
