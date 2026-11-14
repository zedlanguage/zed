//! The benchmarks of steps L1.26a and L1.26b, run by `tools/run_tests.sh --bench` and left out
//! of its default run (TEST-bench-split). Each check they make besides the ratio has a small
//! instance among the correctness tests.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// A body of `n` comparisons of the parameter `x` with operations on literals alone:
/// `g(positional x) = { c0 = x == 0 + 1; …; c0 };` (plan row LIT-generic-class-follows; the
/// correctness tests are in `param_follows.rs`).
fn comparisons(n: usize) -> String {
    let lines: String = (0..n)
        .map(|i| format!("c{i} = x == {i} + {}; ", i % 7))
        .collect();
    format!("g(positional x) = {{ {lines}c0 }};\n")
}

#[test]
fn comparisons_with_a_parameter_are_checked_in_linear_time() {
    zed_tests::deep::on_small_stack(|| {
        assert_eq!(type_errors(&comparisons(4)), Vec::<String>::new());
        let n = 5000;
        let srcs = [comparisons(n), comparisons(scaling::FACTOR * n)];
        scaling::check(
            "checking a body of n comparisons of a parameter with operations on literals",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}

#[test]
fn nested_int_operation_exponents_are_read_in_linear_time() {
    // Each `^` reads its exponent as an `int` (plan row LIT-rat-int-op-exponent): read anew
    // at each of the n powers, as the text walk does, that is O(n^2); kept by operation, and
    // not entered again at the top level, O(n). The correctness test is in
    // `top_body_agree.rs`.
    use super::top_body_agree::nested_int_exponents;
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let n = 300;
            let srcs = [
                nested_int_exponents(n),
                nested_int_exponents(scaling::FACTOR * n),
            ];
            scaling::check("checking n nested int exponents", n, |m| {
                type_errors(&srcs[usize::from(m != n)]);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
