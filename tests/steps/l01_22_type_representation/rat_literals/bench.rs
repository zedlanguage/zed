//! The benchmarks of `rat_literals.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `rat_literals.rs`.

use super::*;

#[test]
fn a_rat_literal_costs_its_exponent_and_not_its_digits() {
    // The exponent `N` at `2^20` and `2^23`: the value has `N` digits, the text `log10 N`.
    let ns = [1usize << 20, 1 << 23];
    let texts = programs(&ns.map(|n| n.to_string()));
    check_order(
        "the types of 1eNr, 10eNr, 1.0eNr and 1e-Nr checked, compared and printed",
        ns[0],
        0,
        |n| {
            let i = usize::from(n != ns[0]);
            check_program(&texts[&i], &ns[i].to_string());
        },
    );
}

#[test]
fn a_rat_literal_costs_the_length_of_its_text() {
    // The exponent written with `n` and `8n` digits: no form of the value could be built.
    let digits = [200usize, 1600];
    let ns = digits.map(|d| format!("1{}", "0".repeat(d - 1)));
    let texts = programs(&ns);
    check(
        "the types of 1eNr, 10eNr, 1.0eNr and 1e-Nr, N of n digits",
        digits[0],
        |n| {
            let i = usize::from(n != digits[0]);
            check_program(&texts[&i], &ns[i]);
        },
    );
}
