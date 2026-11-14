//! Generic literals at the rule of low complexity (DESIGN.md Part G): each joins its class
//! once, and each takes its carrier at run time by one `match` on the other operand.
//!
//! The texts the benchmarks in `bench/scaling.rs` measure, and a small instance of each check
//! they make besides the ratio (TEST-bench-move-l0126).

use zed_tests::step_helpers::l01_16_elaboration::{checked, elab, value};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

/// A function of `n` untyped parameters, each added with a generic literal: `n` class
/// merges and `n` generic literals, nested `2n` deep.
pub(super) fn sum(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional x{i}")).collect();
    let body: Vec<String> = (0..n).map(|i| format!("x{i} + {}", i + 1)).collect();
    format!("f({}) = {};\n", ps.join(", "), body.join(" + "))
}

#[test]
fn a_body_of_generic_literals_joins_one_class() {
    assert_eq!(
        sig(&sum(2), "f"),
        "(T, T) -> T for T in int | f32 | f64 | rat"
    );
    let u = checked(&sum(3));
    assert_eq!(u.info.follows.len(), 3);
    assert_eq!(u.elab(), elab(&sum(3)).unwrap());
}

/// A function of one parameter multiplied by `n` decimal literals of 19 significant digits,
/// each its own number: each is read and fitted at `f64` and `rat` once (DESIGN.md L1.26b).
pub(super) fn decimals(n: usize) -> String {
    let body: Vec<String> = (0..n)
        .map(|i| format!("x * 0.{:019}", 1_234_567_890_123_456_789u64 - i as u64))
        .collect();
    format!("f(positional x) = {};\n", body.join(" + "))
}

#[test]
fn a_body_of_decimal_literals_of_19_digits_checks() {
    assert_eq!(type_errors(&decimals(2)), Vec::<String>::new());
}

/// One decimal literal of `n` digits at a parameter of type `f64`, read at `f64` alone
/// (DESIGN.md L1.26b). Read at `rat`, as in a class that holds `rat`, its digits cost
/// O(n^1.47) (COMPLEXITY.md K41).
pub(super) fn long(n: usize) -> String {
    format!("id(positional v: f64) = v;\nx = id(0.{});\n", "3".repeat(n))
}

#[test]
fn one_decimal_literal_of_many_digits_checks() {
    assert_eq!(type_errors(&long(40)), Vec::<String>::new());
}

/// A function that calls a generic `mul` `n` times, each with a generic literal argument:
/// `n` literals that each take the carrier of the caller's parameter.
pub(super) fn calls(n: usize) -> String {
    let body: Vec<String> = (0..n).map(|i| format!("mul(x, {})", i + 1)).collect();
    format!(
        "mul(positional x, positional k) = x * k;\nf(positional x) = {};\n",
        body.join(" + ")
    )
}

#[test]
fn generic_literal_arguments_take_the_carrier_of_the_callers_parameter() {
    assert_eq!(sig(&calls(2), "f"), "T -> T for T in int | f32 | f64 | rat");
    let u = checked(&calls(3));
    assert_eq!(u.info.witness.len(), 3);
    assert_eq!(u.info.follows.len(), 3);
    assert_eq!(u.elab(), elab(&calls(3)).unwrap());
}

/// A value bound outside a function, `y = (1 + 0) /* … */ * (1 + 0) /* … */ * … * d`, of `n`
/// parenthesized sums of integer literals and the decimal `d`. Each sum is an operation on
/// literals alone, and so is their product, which takes the carrier of what it meets
/// (DESIGN.md sec:diagnostics, "A `/` of integer literals"). The comments make the line long
/// beside the checker's work on each sum.
pub(super) fn product(n: usize, d: &str) -> String {
    format!(
        "y = {} * {d};\n",
        vec!["(1 + 0) /* a comment the fixes keep, which makes the line long */"; n].join(" * ")
    )
}

/// With `d = 0.5` nothing gives the literals a carrier, and each fix writes the decimal with
/// one, on one line of length of order n, and names the value of `y`, folded over the `2n`
/// operations (MSG-literal-fixes).
#[test]
fn a_menu_of_a_long_line_writes_each_fix_on_the_whole_line() {
    let c = "/* a comment the fixes keep, which makes the line long */";
    let one = format!(
        "  fixes, each checked here:\n    y = (1 + 0) {c} * 0.5f64;    y is 0.5\n    \
         y = (1 + 0) {c} * 0.5r;      y is 1r/2r"
    );
    let [m] = &type_errors(&product(1, "0.5"))[..] else {
        panic!("one rejection")
    };
    assert!(m.ends_with(&format!("{one} [0.5]")), "{m}");
    let [e] = &Resolved::new(&product(3, "0.5")).type_errors()[..] else {
        panic!("one rejection")
    };
    assert_eq!(e.matches("(1 + 0)").count(), 3 * 3, "{e}");
    assert!(e.contains("* 0.5f64;    y is 0.5\n"), "{e}");
}

/// With `d = 0.5f64` the product of the `n` sums meets an `f64`, and each of its `2n`
/// literals takes it (`Ck::lit_op_meets`).
#[test]
fn an_operation_on_literals_takes_the_carrier_it_meets() {
    assert_eq!(type_errors(&product(3, "0.5f64")), Vec::<String>::new());
}

/// `y = (1 / 1) * (1 / 1) * … * (1 / 1)`, of `n` divisions of integer literals: a `/` of
/// literals takes the carrier of what it meets, so each fix writes the first literal of the
/// value alone, and the `*` carry its carrier to every `/` (DESIGN.md sec:diagnostics, "A `/`
/// of integer literals": "the menu writes the carrier at the first literal of the value").
pub(super) fn quotients(n: usize) -> String {
    format!("y = {};\n", vec!["(1 / 1)"; n].join(" * "))
}

#[test]
fn a_menu_writes_one_literal_for_many_divisions() {
    let [e] = &Resolved::new(&quotients(3)).type_errors()[..] else {
        panic!("one rejection")
    };
    // The first fix is also the headline's repair.
    for (fix, k) in [
        ("y = (1.0f64 / 1) * (1 / 1)", 2),
        ("y = (1r / 1) * (1 / 1)", 1),
    ] {
        assert_eq!(e.matches(fix).count(), k, "{e}");
    }
    assert!(e.contains(" * (1 / 1);") && e.contains(" y is 1r\n"), "{e}");
}

/// `y = 1 / 1 / … / 1`, `n` divisions nested to depth `n`: only the innermost divides two
/// literals, and each fix writes its first literal alone, whose carrier reaches each `/`.
pub(super) fn nested_quotients(n: usize) -> String {
    format!("y = 1{};\n", " / 1".repeat(n))
}

#[test]
fn a_menu_of_nested_divisions_writes_the_first_literal() {
    let [e] = &Resolved::new(&nested_quotients(3)).type_errors()[..] else {
        panic!("one rejection")
    };
    assert!(e.contains("    y = 1r / 1 / 1 / 1;"), "{e}");
    assert_eq!(e.matches("1.0f64").count(), 2, "{e}");
}

/// `y = (1 / 2 + 1 / 2 + … + 1 / 2) + 1.0f64`, a sum of `n` divisions of integer literals, each
/// on a line of its own, that meets an `f64` (`Ck::lit_takes`, `Ck::drop_met`).
pub(super) fn sum_of_divisions(n: usize) -> String {
    format!("y = ({}) + 1.0f64;\n", vec!["1 / 2"; n].join("\n  + "))
}

#[test]
fn a_sum_of_divisions_of_literals_takes_its_carrier() {
    assert_eq!(type_errors(&sum_of_divisions(3)), Vec::<String>::new());
}

/// `y = ((…((1 + 1) / 1 + 1) / 1 …) + 1) / 1 + 1.0f64`, `n` divisions of literals nested
/// `2n` deep, each level on a line of its own, that meets an `f64` (`Ck::lit_open_within`,
/// `Ck::lit_takes`).
pub(super) fn nested_divisions(n: usize) -> String {
    format!(
        "y = {}1{} + 1.0f64;\n",
        "(".repeat(n),
        "\n  + 1) / 1".repeat(n)
    )
}

#[test]
fn divisions_of_literals_nested_deep_take_their_carrier() {
    assert_eq!(type_errors(&nested_divisions(3)), Vec::<String>::new());
    assert_eq!(value(&nested_divisions(3), "y"), "5.0");
}

/// `y = (1 + 1, 1 + 1, …) == (2.0f64, 2.0f64, …)`, two tuples of `n` components (`Ck::lit_pairs`,
/// `retyped`).
pub(super) fn pairs(n: usize) -> String {
    format!(
        "y = ({}) == ({});\n",
        vec!["1 + 1"; n].join(", "),
        vec!["2.0f64"; n].join(", ")
    )
}

#[test]
fn a_comparison_of_tuples_of_operations_checks() {
    assert_eq!(type_errors(&pairs(3)), Vec::<String>::new());
}

/// `n` calls of `f(x: f64)`, each given a `/` of literals on a line of its own
/// (`Ck::lit_args_take`).
pub(super) fn calls_of_divisions(n: usize) -> String {
    let ys: String = (0..n)
        .map(|i| format!("y{i} = f(x: ({i} + 1) / 2);\n"))
        .collect();
    format!("f(x: f64) = x;\n{ys}")
}

#[test]
fn calls_given_divisions_of_literals_take_their_carriers() {
    assert_eq!(type_errors(&calls_of_divisions(3)), Vec::<String>::new());
    assert_eq!(value(&calls_of_divisions(3), "y2"), "1.5");
}

/// `n` calls of `f(x: f64)`, each given `(i + 1) / divisor`.
pub(super) fn calls_with_divisor(n: usize, divisor: &str) -> String {
    let ys: String = (0..n)
        .map(|i| format!("y{i} = f(x: ({i} + 1) / {divisor});\n"))
        .collect();
    format!("f(x: f64) = x;\n{ys}")
}

#[test]
fn a_division_of_literals_that_a_call_gives_a_carrier_is_accepted() {
    for divisor in ["2", "2.0f64"] {
        assert_eq!(
            type_errors(&calls_with_divisor(3, divisor)),
            Vec::<String>::new(),
            "{divisor}"
        );
    }
}

/// `y = f(x: ((…((1 + 1) / 1 + 1) / 1 …) + 1) / 1)` at `f(x: f64)`, `n` divisions of literals
/// nested `2n` deep, each level on a line of its own (`Ck::lit_takes`).
pub(super) fn nested_argument(n: usize) -> String {
    format!(
        "f(x: f64) = x;\ny = f(x: {}1{});\n",
        "(".repeat(n),
        "\n  + 1) / 1".repeat(n)
    )
}

#[test]
fn an_argument_of_divisions_of_literals_nested_deep_takes_its_carrier() {
    assert_eq!(type_errors(&nested_argument(3)), Vec::<String>::new());
    assert_eq!(value(&nested_argument(3), "y"), "4.0");
}

/// `(…((base)^-1)^-1 …)^-1`, `n` powers nested `n` deep, each level on a line of its own.
fn nest_powers(base: &str, n: usize) -> String {
    format!("{}({base}){}", "(".repeat(n), ")\n^-1".repeat(n))
}

/// The powers of `3/2` in a body beside `x: rat`.
pub(super) fn powers_in_a_body(n: usize) -> String {
    format!(
        "f(x: rat) = x + {};\ny = f(x: 0r);\n",
        nest_powers("3/2", n)
    )
}

/// The powers of the base `2` in a body beside `x: rat`.
pub(super) fn powers_of_two(n: usize) -> String {
    format!("f(x: rat) = x + {};\ny = f(x: 0r);\n", nest_powers("2", n))
}

/// The powers of `3/2` at the top level, times `1r`.
pub(super) fn powers_at_the_top(n: usize) -> String {
    format!("y = {} * 1r;\n", nest_powers("3/2", n))
}

/// `x / (2r/3r) * (2r/3r) …`, `n` divisors that are operations on literals.
pub(super) fn divisor_chain(n: usize) -> String {
    let ops: String = (0..n)
        .map(|i| match i % 2 {
            0 => "\n  / (2r/3r)",
            _ => "\n  * (2r/3r)",
        })
        .collect();
    format!("f(x: rat) = x{ops};\ny = f(x: 1r);\n")
}

/// One divisor whose power has an exponent of 200 n: its range, at least `1r`, is read from the
/// base and the exponent, and the power, of about 95 n digits, is not computed.
pub(super) fn power_divisor(n: usize) -> String {
    format!("f(x: rat) = x / (3r^{} + 1r);\n", 200 * n)
}

/// A divisor of n nested squares `((3r^2)^2 …)^2 + 1r`: the square is taken of the base `3r`, a
/// value of the text, and not of the range of a power, so the ends stay `9r` and do not double
/// in size at each level.
pub(super) fn squares_divisor(n: usize) -> String {
    format!(
        "f(x: rat) = x / ({}3r{} + 1r);\n",
        "(".repeat(n),
        ")^2".repeat(n)
    )
}

/// The value or range of each base or divisor is a lookup of the one kept for the operation
/// inside it (`Ck::rat_folded`), and the integer exponents keep `int` (POW-rat-literal-ops).
#[test]
fn operations_on_literals_are_typed_by_their_value() {
    assert_eq!(sig(&powers_in_a_body(3), "f"), "(x: rat) -> rat");
    assert_eq!(value(&powers_in_a_body(3), "y"), "2r/3r");
    assert_eq!(value(&powers_in_a_body(4), "y"), "3r/2r");
    assert_eq!(sig(&powers_of_two(3), "f"), "(x: rat) -> rat");
    assert_eq!(value(&powers_of_two(3), "y"), "1r/2r");
    assert_eq!(value(&powers_at_the_top(3), "y"), "2r/3r");
    assert_eq!(sig(&divisor_chain(3), "f"), "(x: rat) -> rat");
    assert_eq!(value(&divisor_chain(3), "y"), "3r/2r");
    assert_eq!(sig(&power_divisor(3), "f"), "(x: rat) -> rat");
    assert_eq!(sig(&squares_divisor(3), "f"), "(x: rat) -> rat");
    for make in [
        powers_in_a_body,
        powers_of_two,
        powers_at_the_top,
        divisor_chain,
        power_divisor,
        squares_divisor,
    ] {
        assert_eq!(type_errors(&make(3)), Vec::<String>::new(), "{}", make(3));
    }
}

/// `x = 3^(200 n) / 2`, rejected.
pub(super) fn half_of_a_power(n: usize) -> String {
    format!("x = 3^{} / 2;\n", 200 * n)
}

/// `y = (3^(200 n) + 0.5, 1) == (1, 2)`, rejected.
pub(super) fn pair_of_a_power(n: usize) -> String {
    format!("y = (3^{} + 0.5, 1) == (1, 2);\n", 200 * n)
}

/// `y = (3^(200 n) + 1, 0.5) == (2, 2)`, rejected, the power at `int`.
pub(super) fn int_pair_of_a_power(n: usize) -> String {
    format!("y = (3^{} + 1, 0.5) == (2, 2);\n", 200 * n)
}

/// The fixes of a rejected binding name the value a power of literals gives at `rat` by the
/// operation as the fix writes it, `x is 3r^200 / 2`, and do not compute it (DESIGN.md
/// sec:diagnostics, "The value a fix names").
#[test]
fn a_fix_names_a_power_of_literals() {
    for make in [half_of_a_power, pair_of_a_power, int_pair_of_a_power] {
        assert_eq!(type_errors(&make(1)).len(), 1, "{}", make(1));
    }
}

/// `f(b: bool) = if b { 3^(200 n) } else { 2 };`.
pub(super) fn if_of_a_power(n: usize) -> String {
    format!("f(b: bool) = if b {{ 3^{} }} else {{ 2 }};\n", 200 * n)
}

/// [`if_of_a_power`] and `main() = f(b: true) > 1;`, rejected.
pub(super) fn main_of_an_if_of_a_power(n: usize) -> String {
    format!("{}main() = f(b: true) > 1;\n", if_of_a_power(n))
}

/// `f(b: bool) = if b { 3^(200 n) + 1 } else { 2 };` and `main() = f(b: true) > 1;`, rejected.
pub(super) fn main_of_an_if_of_a_sum(n: usize) -> String {
    format!(
        "f(b: bool) = if b {{ 3^{} + 1 }} else {{ 2 }};\nmain() = f(b: true) > 1;\n",
        200 * n
    )
}

/// The type of an `if` whose branch is a power of literals keeps the power, held as its prime
/// exponents, and prints it as the program wrote it (DESIGN.md step L1.26a and sec:diagnostics,
/// "Types in a message"; LIT-power-values); a branch that adds to the power prints its digits.
#[test]
fn the_type_of_an_if_holding_a_power_of_literals_prints_the_power() {
    assert_eq!(sig(&if_of_a_power(1), "f"), "(b: bool) -> 2 | 3^200");
    assert_eq!(type_errors(&if_of_a_power(1)), Vec::<String>::new());
    let out = run("l01_26a_power_small", &main_of_an_if_of_a_power(1), "", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains("`(b: bool) -> 2 | 3^200`"),
        "{}",
        out.stderr
    );
    let out = run("l01_26a_power_small", &main_of_an_if_of_a_sum(1), "", &[]);
    assert_eq!(out.status, 1);
    assert!(out.stderr.contains("(b: bool) -> 2 | "), "{}", out.stderr);
}

/// `y = 2r * 2^(1 - 1 + … + 1 - 1 + e)`, an exponent of `2n` terms.
pub(super) fn flat_exponent(n: usize, e: &str) -> String {
    format!("y = 2r * 2^({}{e});\n", "1 - 1 + ".repeat(n))
}

/// `y = 2r * 2^(1^(1^(… ^ e)))`, an exponent of `n` powers nested.
pub(super) fn deep_exponent(n: usize, e: &str) -> String {
    format!("y = 2r * 2^({}{e}{});\n", "1^(".repeat(n), ")".repeat(n))
}

/// With `e` a decimal, `0.5`, the power is no `rat` and the line is rejected; with `e = 2` it
/// is a `rat`. At `rat` the text of each exponent is read once and the exponent folded once at
/// `int` (`int_exponent`, `Ck::lit_fit`; plan row LIT-rat-decimal-exponent).
#[test]
fn a_power_at_rat_with_a_long_or_deep_exponent_checks() {
    for shape in [flat_exponent, deep_exponent] {
        assert!(!type_errors(&shape(3, "0.5")).is_empty());
        assert_eq!(type_errors(&shape(3, "2")), Vec::<String>::new());
    }
}
