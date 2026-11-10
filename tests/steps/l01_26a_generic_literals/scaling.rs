//! Generic literals at the rule of low complexity (DESIGN.md Part G): each joins its class
//! once, and each takes its carrier at run time by one `match` on the other operand.
//!
//! Each test times elaboration alone, from the checker's findings made before timing: parsing
//! and checking cost about 430,000 to 460,000 instructions per term and elaboration about 4%
//! of the whole, so a quadratic in elaboration that allocates nothing passes a test that times
//! them all (COMPLEXITY.md F85, F86). The checker's own cost on these bodies is timed in
//! `l01_26_type_resolution::scaling`.

use zed_tests::scaling;

use zed_tests::step_helpers::l01_16_elaboration::{checked, elab};
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

/// A function of `n` untyped parameters, each added with a generic literal: `n` class
/// merges and `n` generic literals, nested `2n` deep.
fn sum(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional x{i}")).collect();
    let body: Vec<String> = (0..n).map(|i| format!("x{i} + {}", i + 1)).collect();
    format!("f({}) = {};\n", ps.join(", "), body.join(" + "))
}

#[test]
fn a_body_of_many_generic_literals_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&sum(2), "f"), "(T, T) -> T for T in int | f64 | rat");
            let n = 1000;
            let units = [checked(&sum(n)), checked(&sum(scaling::FACTOR * n))];
            for (u, m) in units.iter().zip([n, scaling::FACTOR * n]) {
                assert_eq!(u.info.follows.len(), m);
            }
            assert_eq!(units[0].elab(), elab(&sum(n)).unwrap());
            scaling::check("elaborating a body of n generic literals", n, |m| {
                units[usize::from(m != n)].elab();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A function of one parameter multiplied by `n` decimal literals of 19 significant digits,
/// each its own number: each is read and fitted at `f64` and `rat` once (DESIGN.md L1.26b).
fn decimals(n: usize) -> String {
    let body: Vec<String> = (0..n)
        .map(|i| format!("x * 0.{:019}", 1_234_567_890_123_456_789u64 - i as u64))
        .collect();
    format!("f(positional x) = {};\n", body.join(" + "))
}

#[test]
fn a_body_of_many_decimal_literals_of_19_digits_checks_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&decimals(2)), Vec::<String>::new());
            let n = 500;
            let srcs = [decimals(n), decimals(scaling::FACTOR * n)];
            scaling::check(
                "checking a body of n decimal literals of 19 digits",
                n,
                |m| {
                    checked(&srcs[usize::from(m != n)]);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// One decimal literal of `n` digits at a parameter of type `f64`, read at `f64` alone
/// (DESIGN.md L1.26b). Read at `rat`, as in a class that holds `rat`, its digits cost
/// O(n^1.47) (COMPLEXITY.md K41).
fn long(n: usize) -> String {
    format!("id(positional v: f64) = v;\nx = id(0.{});\n", "3".repeat(n))
}

#[test]
fn one_decimal_literal_of_many_digits_checks_in_linear_time() {
    assert_eq!(type_errors(&long(40)), Vec::<String>::new());
    let n = 65_536;
    let srcs = [long(n), long(scaling::FACTOR * n)];
    scaling::check("checking one decimal literal of n digits", n, |m| {
        checked(&srcs[usize::from(m != n)]);
    });
}

/// A function that calls a generic `mul` `n` times, each with a generic literal argument:
/// `n` literals that each take the carrier of the caller's parameter.
fn calls(n: usize) -> String {
    let body: Vec<String> = (0..n).map(|i| format!("mul(x, {})", i + 1)).collect();
    format!(
        "mul(positional x, positional k) = x * k;\nf(positional x) = {};\n",
        body.join(" + ")
    )
}

#[test]
fn a_body_of_many_generic_literal_arguments_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&calls(2), "f"), "(T) -> T for T in int | f64 | rat");
            let n = 1000;
            let units = [checked(&calls(n)), checked(&calls(scaling::FACTOR * n))];
            for (u, m) in units.iter().zip([n, scaling::FACTOR * n]) {
                assert_eq!(u.info.witness.len(), m);
                assert_eq!(u.info.follows.len(), m);
            }
            assert_eq!(units[0].elab(), elab(&calls(n)).unwrap());
            scaling::check(
                "elaborating a body of n generic literal arguments",
                n,
                |m| {
                    units[usize::from(m != n)].elab();
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A value bound outside a function, `y = (1 + 0) /* … */ * (1 + 0) /* … */ * … * 0.5`, of `n`
/// parenthesized sums of integer literals and a decimal: nothing gives its literals a carrier,
/// and each sum is typed on its own, so each fix writes the first literal of every sum with a
/// carrier, on one line of length of order n, and names the value of `y`, folded over the `2n`
/// operations (MSG-literal-fixes). The comments make the line long beside the checker's work
/// on each sum. Negative controls (each run once, not committed), at n = 500 and 4,000:
/// `Rewrite::line` building a new line for each edit failed at 33.0 times the bytes;
/// applying each edit in place by `String::replace_range`, which moves the rest of the line
/// each time, passed at 8.2 times the work, since `memmove` costs a small fraction of an
/// instruction per byte against the checker's work on each sum, so this test does not see
/// that form.
fn product(n: usize) -> String {
    format!(
        "y = {} * 0.5;\n",
        vec!["(1 + 0) /* a comment the fixes keep, which makes the line long */"; n].join(" * ")
    )
}

#[test]
fn a_menu_of_many_edits_scales() {
    scaling::on_a_thread(1 << 29, || {
        let c = "/* a comment the fixes keep, which makes the line long */";
        let one = format!(
            "  fixes, each checked here:\n    y = (1.0f64 + 0) {c} * 0.5;    y is 0.5\n    \
             y = (1r + 0) {c} * 0.5;        y is 1r/2r"
        );
        let [m] = &type_errors(&product(1))[..] else {
            panic!("one rejection")
        };
        assert!(m.ends_with(&format!("{one} [0.5]")), "{m}");
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&product(m)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert_eq!(e.matches("1.0f64 + 0").count(), *m, "{e}");
            assert!(e.contains("y is 0.5\n"), "{e}");
        }
        scaling::check("rejecting a value of n sums with a menu", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}
