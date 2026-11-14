//! A division, `div` or `mod` whose divisor's type holds no zero adds no `#divByZero`
//! (DESIGN.md step L1.26). At layer L1 a divisor gets such a type from literals that survive
//! an `if` (step L1.26a), as `1 | 9` or `-3 | -1`, directly or through a call, and an `int`
//! divisor holds no zero in the arm of a test that rules zero out, as `if d != 0` (step
//! L1.24); a divisor whose type holds `0` keeps `#divByZero`, and so does an `int` no test
//! keeps from zero. The types written in a declaration, `d: int[1..=9]`, are layer L10's, and
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
fn a_divisor_narrowed_by_a_test_adds_no_div_by_zero() {
    // DESIGN.md sec:type_resolution rule 3: "The checker maintains per-node proposition sets
    // (facts learned by tests)"; in the arm of a test a name has the interval the test leaves
    // it (step L1.24), and step L1.26 adds no `#divByZero` for a divisor that holds no zero.
    assert_eq!(
        sig(
            "f(x: int, d: int) = if d != 0 { x div d } else { 0 };\n",
            "f"
        ),
        "(x: int, d: int) -> int"
    );
}

/// Each test that keeps `d` from zero in the arm the division is in: `!=` in either order,
/// the `else` of `==`, a disjunction of two sides that each exclude zero, and a test further
/// out than the arm the division is in; at `div` and `mod`.
#[test]
fn every_test_that_rules_zero_out_narrows_the_divisor() {
    for body in [
        "if d != 0 { x div d } else { 0 }",
        "if 0 != d { x div d } else { 0 }",
        "if d == 0 { 0 } else { x div d }",
        "if 0 == d { 0 } else { x mod d }",
        "if d > 0 || d < 0 { x div d } else { 0 }",
        "if d >= 1 { x mod d } else { 0 }",
        "if d != 0 { if x > 0 { x div d } else { x mod d } } else { 0 }",
        "if d != 0 && x != 0 { x div d } else { 0 }",
    ] {
        let text = format!("f(x: int, d: int) = {body};\n");
        assert_eq!(sig(&text, "f"), "(x: int, d: int) -> int", "{body}");
    }
    let run = "f(x: int, d: int) = if d != 0 { x div d } else { 0 };\n\
               a = f(x: 7, d: 2);\nb = f(x: 7, d: 0);\nc = f(x: -7, d: 2);\n";
    assert_eq!(value(run, "a"), "3");
    assert_eq!(value(run, "b"), "0");
    // `div` is Euclidean (sec:domains): -7 = -4 * 2 + 1.
    assert_eq!(value(run, "c"), "-4");
}

/// Where the test leaves zero to the divisor, `#divByZero` stays: a test against another
/// value, a test of another name, a disjunction one side of which holds zero, and a division
/// outside the arm. The test changes no type outside its arm: `d` stays an `int` in the
/// signature.
#[test]
fn a_test_that_leaves_zero_keeps_div_by_zero() {
    for body in [
        "if d != 1 { x div d } else { 0 }",
        "if x != 0 { x div d } else { 0 }",
        "if d >= 0 || d < -1 { x div d } else { 0 }",
        "if d != 0 && x != 0 { 0 } else { x div d }",
        "(if d != 0 { 1 } else { 2 }) + x div d",
        "{ y = if d != 0 { 1 } else { 0 }; y + x mod d }",
    ] {
        let text = format!("f(x: int, d: int) = {body};\n");
        assert_eq!(
            sig(&text, "f"),
            "(x: int, d: int) -> int | #divByZero",
            "{body}"
        );
    }
}

/// A `rat` divisor the tests it is under keep from `0r` adds no `#divByZero`, as an `int` one
/// does (NARROW-ne-rat-divisor): the row's function, the contrasts of the `int` lists above at
/// `rat`, comparisons with a literal that `0r` fails, and literals with no suffix, which take
/// `rat` beside `r`.
#[test]
fn every_test_that_rules_zero_out_narrows_a_rat_divisor() {
    assert_eq!(
        sig(
            "f(x: rat, r: rat) = if r != 0r { x / r } else { 0r };\n",
            "f"
        ),
        "(x: rat, r: rat) -> rat"
    );
    for body in [
        "if 0r != r { x / r } else { 0r }",
        "if r == 0r { 0r } else { x / r }",
        "if 0r == r { 0r } else { x / r }",
        "if !(r == 0r) { x / r } else { 0r }",
        "if r > 0r || r < 0r { x / r } else { 0r }",
        "if r >= 1r { x / r } else { 0r }",
        "if 0r < r { x / r } else { 0r }",
        "if r <= -1r/2r { x / r } else { 0r }",
        "if r < 0r { x / r } else { 0r }",
        "if r != 0r { if x > 0r { x / r } else { x / r + 1r } } else { 0r }",
        "if r != 0r && x != 0r { x / r } else { 0r }",
        "if r == 0r || x == 0r { 0r } else { x / r }",
        "if r != 0 { x / r } else { 0r }",
        "if r == 0 { 1r } else { x / r }",
        "if r > 0 { x / r } else { 0r }",
        "if r > 1/2 { x / r } else { 0r }",
    ] {
        let text = format!("f(x: rat, r: rat) = {body};\n");
        assert_eq!(sig(&text, "f"), "(x: rat, r: rat) -> rat", "{body}");
    }
    let run = "f(x: rat, r: rat) = if r != 0r { x / r } else { 0r };\n\
               a = f(x: 7r, r: 2r);\nb = f(x: 7r, r: 0r);\nc = f(x: -7r, r: -1r/2r);\n";
    assert_eq!(value(run, "a"), "7r/2r");
    assert_eq!(value(run, "b"), "0r");
    assert_eq!(value(run, "c"), "14r");
}

/// Where the test leaves `0r` to the divisor, `#divByZero` stays, at `rat` as at `int`: a test
/// against another value, a test of another name, a disjunction one side of which holds zero,
/// a comparison `0r` passes, the arm where `r` is zero, and a division outside the arm.
#[test]
fn a_test_that_leaves_zero_keeps_div_by_zero_at_rat() {
    for body in [
        "if r != 1r { x / r } else { 0r }",
        "if x != 0r { x / r } else { 0r }",
        "if r >= 0r || r < -1r { x / r } else { 0r }",
        "if r >= 0r { x / r } else { 0r }",
        "if r <= 1r/2r { x / r } else { 0r }",
        "if r > -1r && r < 1r { x / r } else { 0r }",
        "if r > 0r { 0r } else { x / r }",
        "if r == 0r { x / r } else { 0r }",
        "if r != 0r && x != 0r { 0r } else { x / r }",
        "(if r != 0r { 1r } else { 2r }) + x / r",
        "{ y = if r != 0r { 1r } else { 0r }; y + x / r }",
    ] {
        let text = format!("f(x: rat, r: rat) = {body};\n");
        assert_eq!(
            sig(&text, "f"),
            "(x: rat, r: rat) -> rat | #divByZero",
            "{body}"
        );
    }
}

/// A literal with no suffix compared with a `rat` or an `f64` takes that carrier, and the arm
/// where the test holds is reached: `f(x: 1r, r: 0r)` runs `x / r + 1r`. Read as the `int` the
/// literal would be alone, the test emptied `r` in that arm, which was dropped with its
/// `#divByZero`, and `f` was `(x: rat, r: rat) -> 0r` (NARROW-ne-rat-divisor).
#[test]
fn a_test_against_a_literal_with_no_suffix_keeps_the_arm_where_it_holds() {
    for body in [
        "if r == 0 { x / r + 1r } else { 0r }",
        "if r == 1 + 1 { x / (r - 2) } else { 0r }",
        "if r == 0 && x == 0 { x / r + 1r } else { 0r }",
    ] {
        let text = format!("f(x: rat, r: rat) = {body};\n");
        assert_eq!(
            sig(&text, "f"),
            "(x: rat, r: rat) -> rat | #divByZero",
            "{body}"
        );
    }
    let text = "f(x: f64, r: f64) = if r == 0 { x / r + 1.0 } else { 0.0 };\n";
    assert_eq!(sig(text, "f"), "(x: f64, r: f64) -> f64");
    let run = "f(x: rat, r: rat) = if r == 0 { x / r + 1r } else { 0r };\n\
               a = f(x: 1r, r: 0r) else #divByZero -> 5r;\nb = f(x: 1r, r: 2r) else #divByZero -> 5r;\n";
    assert_eq!(value(run, "a"), "5r");
    assert_eq!(value(run, "b"), "0r");
}

/// Through `zedc run`: the quotient under `d != 0` has no loose failure for `_` to drop, and
/// under `d != 1` the rejection names the failure and where it enters.
#[test]
fn zedc_run_drops_the_quotient_only_under_a_test_that_rules_zero_out() {
    use zed_tests::step_helpers::l01_19_whole_file_ports::run as zedc_run;
    let program = |test: &str| {
        format!(
            "f(x: int, d: int) = {{ _ = if {test} {{ x div d }} else {{ 0 }}; x }};\n\
             main(m: MainArgs) {{\n  m.stdout <- \"${{f(x: 7, d: 0)}}\";\n}}\n"
        )
    };
    let out = zedc_run("ne_divisor_zero", &program("d != 0"), "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "7\n"),
        "{}",
        out.stderr
    );
    let out = zedc_run("ne_divisor_one", &program("d != 1"), "", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{}", out.stderr);
    let (_, message) = out
        .stderr
        .split_once("prog.zed:")
        .expect("a located message");
    assert_eq!(
        message,
        "1:23: `_` drops a loose failure this value may be, #divByZero: `_` drops only a \
         failure the program names, as the default of an `else` names it, and this one would \
         be dropped with nothing in the text saying so.
  [1]  1:39: the loose failure #divByZero enters here
       1 | f(x: int, d: int) = { _ = if d != 1 { x div d } else { 0 }; x };
         |   ^^^^^^ [10]         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [14, 15, 16]
         |           ^^^^^^ [5]      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]
         |                              ^ [4]  ^^^^^^^^^^^ [7]
         |                              ^^^^^^ [3]     ^ [11]
         |                                   ^ [6]              ^^^^^ [12]
         |                                       ^ [9]            ^ [13]
         |                                       ^^^^^^^ [1, 8]
  [2]  1:27: this `if` gives int | #divByZero
  [3]  1:30: this `!=` gives bool
  [4]  1:30: `d` is int here
  [5]  1:11: `d` is declared `int`
  [6]  1:35: this literal, 1, is 1
  [7]  1:37: this block gives int | #divByZero
  [8]  1:39: this `div` gives int | #divByZero
  [9]  1:39: `x` is int here
  [10] 1:3: `x` is declared `int`
  [11] 1:45: `d` is int here
  [12] 1:54: this block gives 0
  [13] 1:56: this literal, 0, is 0
  [14] 1:23: repair: write a default for the value, as `_ = … else #ok;`, so the text names what it drops
  [15] 1:23: repair: handle each failure with a `match` on the value
  [16] 1:23: repair: bind the value to a name, and use the name
"
    );
}

/// `f(x: int, d: int) = { a1 = if d != 0 { x div d } else { 0 }; a2 = if d != 0 { a1 div d }
/// else { a1 }; …; an }`: `n` tests, each with a division in its arm.
pub(super) fn chained_tests(n: usize) -> String {
    let mut s = String::from("f(x: int, d: int) = { a0 = x; ");
    for i in 1..=n {
        let p = i - 1;
        s += &format!("a{i} = if d != 0 {{ a{p} div d }} else {{ a{p} }}; ");
    }
    s += &format!("a{n} }};\n");
    s
}

/// `f(x: rat, r: rat) = { a0 = x; a1 = if r != 0r { a0 / r } else { a0 }; …; an }`, the tests
/// taking in turn `r != 0r`, `r >= 1r` and `r != 0`: `n` tests, each with a division by a
/// `rat` in its arm.
pub(super) fn chained_rat_tests(n: usize) -> String {
    let mut s = String::from("f(x: rat, r: rat) = { a0 = x; ");
    for i in 1..=n {
        let p = i - 1;
        let test = ["r != 0r", "r >= 1r", "r != 0"][i % 3];
        s += &format!("a{i} = if {test} {{ a{p} / r }} else {{ a{p} }}; ");
    }
    s += &format!("a{n} }};\n");
    s
}

#[test]
fn chained_tests_each_with_a_division_in_its_arm_add_no_div_by_zero() {
    // A small instance of the benchmarks
    // `bench::divisors::chained_tests_and_divisions_check_in_linear_time` and
    // `bench::divisors::chained_rat_tests_and_divisions_check_in_linear_time`.
    assert_eq!(sig(&chained_tests(3), "f"), "(x: int, d: int) -> int");
    assert_eq!(sig(&chained_rat_tests(3), "f"), "(x: rat, r: rat) -> rat");
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
