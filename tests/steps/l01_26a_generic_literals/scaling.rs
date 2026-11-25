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
/// parenthesized sums of integer literals and the operand `d`. Each sum is an operation on
/// literals alone, and so is their product, which takes the carrier of what it meets
/// (DESIGN.md sec:diagnostics, "A `/` of integer literals"). The comments make the line long
/// beside the checker's work on each sum.
pub(super) fn product(n: usize, d: &str) -> String {
    format!(
        "y = {} * {d};\n",
        vec!["(1 + 0) /* a comment the fixes keep, which makes the line long */"; n].join(" * ")
    )
}

/// With `d = (1 / 2)` nothing gives the literals a carrier, and each fix writes the first literal
/// of the value with one, on one line of length of order n, and names the value of `y`, folded
/// over the `2n` operations (MSG-literal-fixes). (Written with `d = 0.5` before a decimal that
/// nothing fixes took `f64`, author decision 2026-11-12; that product is now accepted, at
/// `f64`.)
#[test]
fn a_menu_of_a_long_line_writes_each_fix_on_the_whole_line() {
    let c = "/* a comment the fixes keep, which makes the line long */";
    let one = format!(
        "  fixes, each checked here:\n    y = (1r + 0) {c} * (1 / 2);        y is 1r/2r\n    \
         y = (1.0 + 0) {c} * (1 / 2);       y is 0.5\n    \
         y = (f64(1) + 0) {c} * (1 / 2);    y is 0.5"
    );
    let [m] = &type_errors(&product(1, "(1 / 2)"))[..] else {
        panic!("one rejection")
    };
    assert!(m.ends_with(&format!("{one} [(1 / 2)]")), "{m}");
    let [e] = &Resolved::new(&product(3, "(1 / 2)")).type_errors()[..] else {
        panic!("one rejection")
    };
    // Each fix writes the whole line: the line quoted, the headline's repair and three fixes,
    // each of which writes the first sum with its carrier.
    assert_eq!(e.matches("(1 + 0)").count(), 5 * 3 - 4, "{e}");
    assert!(e.contains("* (1 / 2);       y is 0.5\n"), "{e}");
    // The decimal the test once used is an `f64`.
    assert_eq!(value(&product(3, "0.5"), "y"), "0.5");
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
        ("y = (1r / 1) * (1 / 1)", 2),
        ("y = (1.0 / 1) * (1 / 1)", 1),
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
    assert_eq!(e.matches("y = 1r / 1 / 1 / 1").count(), 2, "{e}");
    assert_eq!(e.matches("y = 1.0 / 1 / 1 / 1;").count(), 1, "{e}");
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

/// `((1 + 1 / 1) / 1 + 1 / 1) / 1 …`, `n` levels at an `f64` parameter, each on a line of its
/// own: as [`nested_argument`], with a division of literals in the second operand of each `+`
/// as well, so two arguments of each `+` carry fixes.
pub(super) fn nested_argument_two_sides(n: usize) -> String {
    format!(
        "f(x: f64) = x;\ny = f(x: {}1{});\n",
        "(".repeat(n),
        "\n  + 1 / 1) / 1".repeat(n)
    )
}

#[test]
fn an_argument_of_divisions_of_literals_on_both_sides_nested_deep_takes_its_carrier() {
    assert_eq!(
        type_errors(&nested_argument_two_sides(3)),
        Vec::<String>::new()
    );
    assert_eq!(value(&nested_argument_two_sides(3), "y"), "4.0");
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
/// in size at each level. The text fixes the power, `3r^(2^n)`, kept as one prime power
/// (DESIGN.md step L1.17b), and the sum writes it out in full, `2^n log2 3` bits: from n = 67
/// past the address space, 2^67 bits, and, beside a `main` with no memory limit, from n = 33
/// past the default limit of 1 GiB (`nested_squares_are_sized_at_the_sum`).
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

/// The sum `3r^(2^n) + 1r` writes out `2^n log2 3` bits (DESIGN.md sec:diagnostics, "Number too
/// large for any memory of the target", whether or not its branch is taken). A unit without
/// `main` is judged against the address space alone, 2^67 bits on Linux x86_64 (`Ck::
/// powers_over_main_limit`): n = 66 builds 1.17e20 bits, within it, and n = 67, 2.34e20, past
/// it. Beside a `main` that declares no memory limit, the bound is the default of 1 GiB: n = 32
/// builds 851 MB, within it, and n = 33, 1.70 GB, past it. Corner cases on each side of each
/// bound; the benchmark `bench::scaling::operations_on_literals_typed_by_their_value_check_in_
/// linear_time_squares` times n = 2000.
#[test]
fn nested_squares_are_sized_at_the_sum() {
    let with_main = |n| format!("{}main(m: MainArgs) = 0;\n", squares_divisor(n));
    for (src, bound) in [
        (squares_divisor(33), None),
        (squares_divisor(66), None),
        (squares_divisor(67), Some("any memory of the target")),
        (with_main(32), None),
        (with_main(33), Some("the default memory limit")),
    ] {
        let errors = type_errors(&src);
        match bound {
            None => assert_eq!(errors, Vec::<String>::new(), "{src}"),
            Some(bound) => {
                let [e] = &errors[..] else {
                    panic!("one rejection:\n{src}\n{errors:?}")
                };
                assert!(
                    e.starts_with(&format!("Number too large for {bound}")),
                    "{e}"
                );
            }
        }
    }
}

/// `x = 3^(200 n) / 2`, rejected.
pub(super) fn half_of_a_power(n: usize) -> String {
    format!("x = 3^{} / 2;\n", 200 * n)
}

/// `y = (3^(200 n) / 2, 1)`, rejected, its fixes naming the pair `y[0]`.
pub(super) fn tuple_of_a_power(n: usize) -> String {
    format!("y = (3^{} / 2, 1);\n", 200 * n)
}

/// `y = (3^(200 n) / 2, 1) == (1, 2)`, rejected (DESIGN.md sec:diagnostics, "The value a fix
/// names", at the exponent 20). Written with `+ 0.5` before a decimal that nothing fixes took
/// `f64` (author decision 2026-11-12).
pub(super) fn pair_of_a_power(n: usize) -> String {
    format!("y = (3^{} / 2, 1) == (1, 2);\n", 200 * n)
}

/// `y = (3^(200 n) + 1, 1 / 2) == (2, 1 / 2)`, rejected, the power at `int` (DESIGN.md
/// sec:diagnostics, "The value a fix names", `y = (3^2 + 1, 1 / 2) == (10, 1 / 2);`). Written with
/// `0.5` before a decimal that nothing fixes took `f64` (author decision 2026-11-12).
pub(super) fn int_pair_of_a_power(n: usize) -> String {
    format!("y = (3^{} + 1, 1 / 2) == (2, 1 / 2);\n", 200 * n)
}

/// The fixes of a rejected binding name the value a power of literals gives at `rat` by the
/// operation as the fix writes it, `x is 3r^200 / 2`, and do not compute it (DESIGN.md
/// sec:diagnostics, "The value a fix names").
#[test]
fn a_fix_names_a_power_of_literals() {
    // One rejection, each of whose fixes names the binder or its pair, the `rat` power by the
    // operation as written.
    for (make, rat_fix, named) in [
        (
            half_of_a_power as fn(usize) -> String,
            ("x = 3r^200 / 2;", "x is 3r^200 / 2"),
            "x is ",
        ),
        (
            tuple_of_a_power,
            ("y = (3r^200 / 2, 1);", "y[0] is 3r^200 / 2"),
            "y[0] is ",
        ),
    ] {
        let src = make(1);
        let fixes = super::fixes::fixes(&src);
        assert!(
            fixes.iter().all(|(_, holds)| holds.starts_with(named)),
            "{src}{fixes:?}"
        );
        assert!(
            fixes
                .iter()
                .any(|(line, holds)| (line.as_str(), holds.as_str()) == rat_fix),
            "{src}{fixes:?}"
        );
    }
    // DESIGN.md names the comparison too, `y is (3r^20 / 2, 1) == (1, 2)`, and the comparison
    // whose pair at `int` holds the power, in one rejection each (rows
    // LIT-tuple-compare-power-menu and LIT-tuple-compare-names-literal).
    for (src, rat_fix) in [
        (pair_of_a_power(1), "y = (3r^200 / 2, 1) == (1, 2);"),
        (
            int_pair_of_a_power(1),
            "y = (3^200 + 1, 1r / 2) == (2, 1 / 2);",
        ),
    ] {
        let fixes = super::fixes::fixes(&src);
        let named = format!("y is {}", &rat_fix[4..rat_fix.len() - 1]);
        assert_eq!(
            fixes.first().map(|(l, h)| (l.as_str(), h.as_str())),
            Some((rat_fix, named.as_str())),
            "{src}{fixes:?}"
        );
        assert!(
            fixes.iter().all(|(_, h)| h.starts_with("y is ")),
            "{src}{fixes:?}"
        );
    }
}

/// `f(b: bool) = if b { 3^(200 n) } else { 2 };`.
pub(super) fn if_of_a_power(n: usize) -> String {
    format!("f(b: bool) = if b {{ 3^{} }} else {{ 2 }};\n", 200 * n)
}

/// `f(b: bool) = if b { (2^64 + 13)^(200 n) } else { 2 };`, a base wider than 64 bits.
pub(super) fn if_of_a_wide_power(n: usize) -> String {
    format!(
        "f(b: bool) = if b {{ (2^64 + 13)^{} }} else {{ 2 }};\n",
        200 * n
    )
}

/// A power of a base wider than 64 bits is kept as the base, unfactored, with its exponent
/// (plan row LIT-power-wide-base; DESIGN.md sec:domains "Kept powers"), so the type of an `if`
/// holding one prints the power, as for a base of a word; before, `Rat::pow` built its digits,
/// 13 million bits at the exponent 200,000. `2^64 + 13` holds no prime below 2^8 and is no
/// perfect power, so it is one atom (`l01_17_value_representation::powers::
/// a_power_of_a_wide_base_is_kept`). The cost: `bench::scaling::
/// the_type_of_an_if_holding_a_power_of_a_wide_base_prints_the_power_when_checked`.
#[test]
fn the_type_of_an_if_holding_a_power_of_a_wide_base_prints_the_power() {
    let src = if_of_a_wide_power(1);
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(b: bool) -> 2 | 18446744073709551629^200");
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

/// `y = add(x: b^(1^(1^(… ^ 1))), y: 1.0f32)`, a base `b` raised to an exponent of `n` powers
/// of `int` literals nested: the one shape in which a derivation's step at `rat` folds a long
/// exponent at `int` (`int_exponent_noting`: the exponent holds no decimal, so the `^` that
/// does holds it in its base).
pub(super) fn int_tower_on_a_base(n: usize, b: &str) -> String {
    format!(
        "add(x, y) = x + y;\ny = add(x: {b}^({}1{}), y: 1.0f32);\n",
        "1^(".repeat(n),
        ")".repeat(n)
    )
}

/// With the base `1e40`, which no `f32` holds, the call is rejected; with `1.0` it checks.
#[test]
fn an_int_tower_on_a_decimal_base_checks() {
    assert!(!type_errors(&int_tower_on_a_base(3, "1e40")).is_empty());
    assert_eq!(
        type_errors(&int_tower_on_a_base(3, "1.0")),
        Vec::<String>::new()
    );
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

/// A call whose fixes are carried in its first argument alone, `1 / 2`, beside a second argument
/// that `f`'s `T` does not take with it, or takes only at another carrier: the table of types
/// lent across arguments is not made then (04555ad8b), and the verdicts are those of 76705768a,
/// which made it at every call (checked with the table made always, PERF-carried-lent-two-args).
/// Beside `"s"` the call is rejected and the literal offered one conversion per carrier, `rat`
/// first in the menu's order, since no carrier makes the call checked (QUESTIONS A60);
/// beside `1.0f64` the literal takes `f64` and the program runs; beside `#a` it is offered `rat`,
/// and the program with `1r` checks.
#[test]
fn carries_in_one_argument_beside_one_that_fails_keep_their_verdicts() {
    let decl = "f(positional p0, positional p1) = p0 < p1;\n";
    let check = |call: &str| -> Vec<String> {
        let errors = type_errors(&format!("{decl}{call}\n"));
        (errors.iter())
            .map(|e| e.lines().next().unwrap_or_default().to_string())
            .collect()
    };
    assert_eq!(
        check("y = f(1 / 2, \"s\");"),
        [
            // The `/` has no carrier, so it is shown by the carriers it can take (A60).
            "`f` does not take (f64 | rat, \"s\"): no arrow of `f` takes these types. Try \
             `f(String(1 / 2), \"s\")` instead. [f(1 / 2, \"s\")]",
            "Nothing gives the literal `1` a carrier. Try `y = f(1r / 2, \"s\")` instead.",
        ]
    );
    let all = type_errors(&format!("{decl}y = f(1 / 2, \"s\");\n")).join("\n");
    for fix in ["    y = f(1r / 2, \"s\");", "    y = f(1.0f64 / 2, \"s\");"] {
        assert!(all.contains(fix), "{fix} is not offered:\n{all}");
    }
    let src = format!("{decl}y = f(1 / 2, 1.0f64);\n");
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(value(&src, "y"), "true");
    assert_eq!(
        check("y = f(1 / 2, #a);"),
        ["Nothing gives the literal `1` a carrier. Try `y = f(1r / 2, #a)` instead."]
    );
    assert_eq!(check("y = f(1r / 2, #a);"), Vec::<String>::new());
}
