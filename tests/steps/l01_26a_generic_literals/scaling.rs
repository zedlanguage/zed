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
use zed_tests::step_helpers::l01_26_type_resolution::sig;

/// A function of `n` untyped parameters, each added with a generic literal: `n` class
/// merges and `n` generic literals, nested `2n` deep.
fn sum(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional x{i}")).collect();
    let body: Vec<String> = (0..n).map(|i| format!("x{i} + {}n", i + 1)).collect();
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

/// A function that calls a generic `mul` `n` times, each with a generic literal argument:
/// `n` literals that each take the carrier of the caller's parameter.
fn calls(n: usize) -> String {
    let body: Vec<String> = (0..n).map(|i| format!("mul(x, {}n)", i + 1)).collect();
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
