//! Benchmarks of `follow`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// A chain of summaries of 40 000 bindings is formed (`LetPa::sum`) and dropped (`Drop for
/// LetNode`) on explicit stacks, with no overflow, and reads `n = 5`. It runs on a thread with
/// the default stack of a test thread, 2 MiB, so that it is the same when libtest runs a test
/// on the main thread. The depth is about a fifth above the larger of the two overflows of that
/// stack without the explicit stacks, measured 2026-11-14 with each replaced by recursion:
/// forming overflows from 32 616 bindings, dropping from 18 750.
#[test]
fn a_deep_chain_of_summaries_is_formed_and_dropped() {
    let got = zed_tests::scaling::on_a_stack(2 << 20, || deep_chain(40_000)["n"].to_string());
    assert_eq!(got, "[5..=5]");
}

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

/// Compiling a conjunction of following tests of a name costs `O(k log k)` for `k` tests: an
/// enumeration no longer gathers again the constraints blocked on `slot`, which lists no
/// members, each time `slot` narrows (BENCH-l0139-follow-over-cap; 256 to 2048 tests took
/// 132 ms to 9.3 s before).
#[test]
fn compiling_following_tests_of_a_name_scales() {
    scaling::check(
        "compiling a conjunction of following tests of a name",
        256,
        |k| _ = function(&excluded(k)),
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
        arms_scale(what, n, src);
    }
}

/// The readings of `nested_sums_keep_their_arms` at depths 6 to 12, which that test leaves out
/// for its time.
#[test]
fn nested_sums_keep_their_arms_at_depths_6_to_12() {
    nested_sums_read(6..=12);
}

/// The arms of `d` nested tests of sums cost `O(d)`: each `if` is summarized once, as a
/// function of `n` affine on each of a few intervals, where the sum `n + n` had no summary
/// and each test fell to the linear stage, `O(d^3)` (16 to 128 levels: 12 ms to 1.53 s). A
/// sum with an `if` adds its line by one tag, and a sum of `d` ramps adds each ramp by a
/// split of the larger summary at two cuts, `O(d log d)` (16 to 128: 2.2 ms to 10.7 ms and
/// 1.3 ms to 7.0 ms, where the projection and the linear stage took 24 ms to 195 ms and 11 ms
/// to 126 ms and read every `n`).
///
/// The checks are in five tests: the run at `8 n` of a check is in a new process that builds
/// the terms of every earlier check of its test again (`scaling::compare_by`), so six checks
/// in one test built `c + 1` sets of terms for check `c`, 21 in all, and the test took 21.7 s
/// at load 56 though its runs took about 2.7 s at `n` (BENCH-l0139-follow-over-cap). This one
/// keeps `n + m` and the sum of ramps, which comments elsewhere cite by this name; the sums of
/// one name are [`nested_sums_of_n_plus_n_scale`] and the three after it.
#[test]
fn nested_sums_of_one_input_scale() {
    for (what, n, src) in [
        (
            "the arms of nested tests of n + m",
            64,
            two as fn(usize) -> String,
        ),
        ("the arms of a test of a sum of d ramps", 256, ramps),
    ] {
        arms_scale(what, n, src);
    }
}

/// The arms of the term `src` gives, at sizes `n` and `8 n`. Each process compiles the term
/// only at the sizes it runs (`scaling::check_inputs`, BENCH-follow-group-near-60s), where both
/// sizes were compiled in every process of the check and of each later check of its test.
fn arms_scale(what: &str, n: usize, src: fn(usize) -> String) {
    let built = |k: usize| {
        let (ps, term) = function(&src(k));
        (ints(&ps), term)
    };
    scaling::check_inputs(what, n, built, |(scope, term)| _ = arms(term, scope));
}

/// One of the checks of [`nested_sums_of_one_input_scale`].
#[test]
fn nested_sums_of_n_plus_n_scale() {
    arms_scale("the arms of nested tests of n + n", 128, twice);
}

/// One of the checks of [`nested_sums_of_one_input_scale`].
#[test]
fn nested_following_sums_of_n_plus_n_scale() {
    arms_scale(
        "the arms of nested tests of n + n, following",
        128,
        following,
    );
}

/// One of the checks of [`nested_sums_of_one_input_scale`].
#[test]
fn nested_sums_of_n_minus_3_n_plus_4_scale() {
    arms_scale("the arms of nested tests of n - 3 * n + 4", 128, line);
}

/// One of the checks of [`nested_sums_of_one_input_scale`].
#[test]
fn nested_sums_with_an_if_scale() {
    arms_scale(
        "the arms of nested tests of n + (if n > 0 { n } else { 0 })",
        128,
        with_an_if,
    );
}

/// A block of `d` bindings `y_k = y_(k-1) + ramp_k; x_k = x_(k-1) + y_k` and a test of `x_d`
/// ([`let_chain`]) costs `O(d log d)`: each binding is summarized once, as the sum of the
/// summaries it adds kept unsummed, and the test forms the sum of `x_d` once. Before, each
/// test in a ramp reduced every name bound since the last reduction, `Θ(d²)` (32 to 256: 27.6
/// times the instructions), and the final test read every `n` (repair of PA-let-block). A
/// block of 512 overflowed the stack of a run, since the walk of the arms recursed on the bound
/// terms; it keeps them on the heap now (item PA-let-stack, `deep_let`).
///
/// Size (BENCH-l0139-follow-over-cap): 128, was 256, at which the test took 15.0 s at load 27
/// though its runs took 87 ms and 658 ms (ratio 8.83): the rest was compiling the block of
/// 2048 twice, in this process and in the new one of the run at `8 n` (`scaling::compare_by`),
/// 24.9 billion instructions each against 7.9 at 1024. The checker forms the summary of every
/// `x_k`, `Θ(d²)` pieces in all, which no two share (`LetPa::sum`, COMPLEXITY.md row
/// PA-let-block); this test times only the arms.
#[test]
fn a_block_of_sums_of_ramps_scales() {
    arms_scale("the arms of a block of d sums of ramps", 128, let_chain);
}

/// Forming the summary of `x_d` in a chain of `d` bindings costs `O(d)`: one sum per binding,
/// each a constant added to a line.
#[test]
fn a_deep_chain_of_summaries_scales() {
    scaling::check("forming a chain of d summaries", 160_000, |d| {
        _ = deep_chain(d)
    });
}
