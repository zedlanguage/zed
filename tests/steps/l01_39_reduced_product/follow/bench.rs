//! Benchmarks of `follow`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The arms of the two chains are compared at depths 1 to 12 by
/// `a_chain_of_following_comparisons_reads_as_the_plain_chain`; here only their costs.
#[test]
fn a_chain_of_following_comparisons_costs_what_the_plain_chain_costs() {
    let d = 48;
    let (ps, follow) = function(&chain(d, false));
    let (_, plain) = function(&chain(d, true));
    let scope = ints(&ps);
    // Finding each compared value again for each test around it cost 2^d; finding it once
    // per test, d times the plain chain. The terms differ by the match of each level only.
    scaling::compare_costs(
        "the arms of a chain of 48 following comparisons against the plain chain",
        "the value compared is found once, as in the plain chain",
        3.0,
        || _ = arms(&plain, &scope),
        || _ = arms(&follow, &scope),
    );
}

#[test]
fn following_tests_scale() {
    for (what, n, src) in [
        (
            "a conjunction of following tests of a name",
            256,
            excluded as fn(usize) -> String,
        ),
        ("a chain of bindings of following tests", 1024, bound),
        (
            "a conjunction of following tests of a difference",
            32,
            differences,
        ),
    ] {
        let (scope, terms) = sizes(n, src);
        scaling::check(what, n, |k| _ = arms(at(&terms, k), &scope));
    }
}

/// The arms of `d` nested tests of sums cost `O(d)`: each `if` is summarized once, as a
/// function of `n` affine on each of a few intervals, where the sum `n + n` had no summary
/// and each test fell to the linear stage, `O(d^3)` (16 to 128 levels: 12 ms to 1.53 s). A
/// sum with an `if` adds its line by one tag, and a sum of `d` ramps adds each ramp by a
/// split of the larger summary at two cuts, `O(d log d)` (16 to 128: 2.2 ms to 10.7 ms and
/// 1.3 ms to 7.0 ms, where the projection and the linear stage took 24 ms to 195 ms and 11 ms
/// to 126 ms and read every `n`).
#[test]
fn nested_sums_of_one_input_scale() {
    for (what, n, src) in [
        (
            "the arms of nested tests of n + n",
            128,
            twice as fn(usize) -> String,
        ),
        (
            "the arms of nested tests of n + n, following",
            128,
            following,
        ),
        ("the arms of nested tests of n - 3 * n + 4", 128, line),
        ("the arms of nested tests of n + m", 64, two),
        (
            "the arms of nested tests of n + (if n > 0 { n } else { 0 })",
            128,
            with_an_if,
        ),
        ("the arms of a test of a sum of d ramps", 256, ramps),
    ] {
        let (scope, terms) = sizes(n, src);
        scaling::check(what, n, |k| _ = arms(at(&terms, k), &scope));
    }
}

/// A block of `d` bindings `y_k = y_(k-1) + ramp_k; x_k = x_(k-1) + y_k` and a test of `x_d`
/// ([`let_chain`]) costs `O(d log d)`: each binding is summarized once, as the sum of the
/// summaries it adds kept unsummed, and the test forms the sum of `x_d` once. Before, each
/// test in a ramp reduced every name bound since the last reduction, `Θ(d²)` (32 to 256: 27.6
/// times the instructions), and the final test read every `n` (repair of PA-let-block). A
/// block of 512 overflowed the stack of a run, since the walk of the arms recursed on the bound
/// terms; it keeps them on the heap now (item PA-let-stack, `deep_let`).
#[test]
fn a_block_of_sums_of_ramps_scales() {
    let (scope, terms) = sizes(256, let_chain);
    scaling::check("the arms of a block of d sums of ramps", 256, |k| {
        _ = arms(at(&terms, k), &scope)
    });
}

/// Forming the summary of `x_d` in a chain of `d` bindings costs `O(d)`: one sum per binding,
/// each a constant added to a line.
#[test]
fn a_deep_chain_of_summaries_scales() {
    scaling::check("forming a chain of d summaries", 160_000, |d| {
        _ = deep_chain(d)
    });
}
