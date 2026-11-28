//! Benchmarks of `arm_test_through_call`: each times the work at a size and at 8 times it, run
//! apart from the correctness tests (`tools/run_tests.sh --bench`).

use super::*;
use zed_tests::instances::Rng;
use zed_tests::scaling;

/// The body of a callee of `k` nested arms: `0` below 0, `x + j` at `x = j - 1` for `j` in
/// `1..k`, and `x + k` from `k - 1`, so `2 * x + 1` on `0..k`, rising.
fn body(k: usize) -> String {
    let mut f = String::from("if x < 0 { 0 }");
    for j in 1..k {
        f.push_str(&format!(" else if x < {j} {{ x + {j} }}"));
    }
    f.push_str(&format!(" else {{ x + {k} }}"));
    f
}

/// The least `x` with `2 * x + 1 > c`, for `c >= 0`.
fn least(c: i64) -> i64 {
    (c + 1) / 2
}

/// A callee `f` of `k` nested arms ([`body`]) and `k` tests `f(x) > c` at random `c` in
/// `0..2k - 1`, each of whose arms reads `x - least(c) - past`, not negative where the test
/// narrows `x` exactly when `past` is 0.
fn stairs(rng: &mut Rng, k: usize, past: i64) -> String {
    let tests: Vec<String> = (0..k)
        .map(|_| {
            let c = rng.int(0, 2 * k as i64 - 2);
            format!(
                "(if f(x) > {c} {{ popCount(x - {}) }} else {{ 0 }})",
                least(c) + past
            )
        })
        .collect();
    format!(
        "f(positional x: int) = {};\ng(positional x: int) = {};\n",
        body(k),
        tests.join(" + ")
    )
}

/// `k` tests calling one callee of `k` nested arms cost `O(k)` together, not `k` times the
/// callee (CHECK-spine-tests-per-body). Each size has its own random tests, from a seed new
/// each run; the programs are made before the timing, and their verdicts checked at the
/// smaller size.
///
/// The verdicts are checked after the timing and the programs made by `check_inputs`, only at
/// the sizes this process runs: a run at 8n in a new process of the test runs the test up to
/// its check and ends there, so the two checks of the verdicts at 512, made before the timing,
/// ran again in that process, in the phase of the run at 8n, whose limit of 20 s they and that
/// run passed (rc 124 at 32.0 s on l43, b22-tests8 job f2,
/// FAIL-bench-pieces-past-limit-on-main).
#[test]
fn tests_calling_one_deep_callee_scale() {
    let k = 512;
    let (mut rng, seed) = Rng::fresh("tests_calling_one_deep_callee_scale");
    scaling::check_inputs(
        "k tests calling one callee of k nested arms",
        k,
        |n| stairs(&mut Rng::new(seed ^ n as u64), n, 0),
        |src| _ = check(src),
    );
    let src = stairs(&mut rng, k, 0);
    assert!(check(&src).is_none(), "seed {seed}: rejected\n{src}");
    let src = stairs(&mut rng, k, 1);
    assert!(check(&src).is_some(), "seed {seed}: accepted\n{src}");
}

/// A callee of `k` nested arms each giving a literal: `0` below 0, `j` at `x = j - 1` for `j`
/// in `1..k`, and `k` from `k - 1`. Its result type is the union of `k + 1` literals.
fn literal_body(k: usize) -> String {
    spaced_body(k, 1)
}

/// A callee of `k` nested arms each giving a literal `step` apart: `0` below 0, `step * j` at
/// `x = j - 1` for `j` in `1..k`, and `step * k` from `k - 1`. For `step` above 1 no two of its
/// literals are adjacent, so the interval of its result has a piece for each.
fn spaced_body(k: usize, step: usize) -> String {
    let mut f = String::from("if x < 0 { 0 }");
    for j in 1..k {
        f.push_str(&format!(" else if x < {j} {{ {} }}", step * j));
    }
    f.push_str(&format!(" else {{ {} }}", step * k));
    f
}

/// The callee of [`literal_body`] and `k` tests `f(x) > c` at random `c` in `0..k`, each of
/// whose arms reads `x - c - past`. On `0..k - 1`, `f(x)` is `x + 1`, so the test holds exactly
/// for `x >= c`, and the read is not negative where the test narrows `x` exactly when `past` is
/// 0.
fn literal_tests(rng: &mut Rng, k: usize, past: i64) -> String {
    spaced_tests(rng, k, 1, past)
}

/// The callee of [`spaced_body`] and `k` tests `f(x) > step * c` at random `c` in `0..k`, each
/// of whose arms reads `x - c - past`. On `0..k - 1`, `f(x)` is `step * (x + 1)`, so the test
/// holds exactly for `x >= c`, and the read is not negative where the test narrows `x` exactly
/// when `past` is 0.
fn spaced_tests(rng: &mut Rng, k: usize, step: usize, past: i64) -> String {
    let tests: Vec<String> = (0..k)
        .map(|_| {
            let c = rng.int(0, k as i64 - 1);
            format!(
                "(if f(x) > {} {{ popCount(x - {}) }} else {{ 0 }})",
                step as i64 * c,
                c + past
            )
        })
        .collect();
    format!(
        "f(positional x: int) = {};\ng(positional x: int) = {};\n",
        spaced_body(k, step),
        tests.join(" + ")
    )
}

/// `k` tests on a callee whose result is a union of `k + 1` literals cost `O(k log k)`
/// together (CHECK-literal-union-cost): each test narrows the union to the literals above `c`,
/// about `k / 2` of them, which must share the callee's set rather than copy it. Each size has
/// its own random tests, from a seed new each run; the verdicts are checked at the smaller
/// size.
#[test]
fn tests_on_a_callee_of_k_literal_arms_scale() {
    let k = 64;
    let (mut rng, seed) = Rng::fresh("tests_on_a_callee_of_k_literal_arms_scale");
    let src = literal_tests(&mut rng, k, 0);
    assert!(check(&src).is_none(), "seed {seed}: rejected\n{src}");
    let src = literal_tests(&mut rng, k, 1);
    assert!(check(&src).is_some(), "seed {seed}: accepted\n{src}");
    let srcs = scaling::inputs(k, |n| literal_tests(&mut Rng::new(seed ^ n as u64), n, 0));
    scaling::check("k tests on a callee of k literal arms", k, |n| {
        _ = check(&srcs[&n]);
    });
}

/// As [`tests_on_a_callee_of_k_literal_arms_scale`], with the callee's literals 3 apart
/// ([`spaced_tests`]), so that the interval of its result is `k + 1` pieces rather than one,
/// and each test's narrowing cuts a set of many members against an interval of many pieces.
#[test]
fn tests_on_a_callee_of_k_spaced_literal_arms_scale() {
    let k = 64;
    let (mut rng, seed) = Rng::fresh("tests_on_a_callee_of_k_spaced_literal_arms_scale");
    let src = spaced_tests(&mut rng, k, 3, 0);
    assert!(check(&src).is_none(), "seed {seed}: rejected\n{src}");
    let src = spaced_tests(&mut rng, k, 3, 1);
    assert!(check(&src).is_some(), "seed {seed}: accepted\n{src}");
    let srcs = scaling::inputs(k, |n| spaced_tests(&mut Rng::new(seed ^ n as u64), n, 3, 0));
    scaling::check("k tests on a callee of k literal arms 3 apart", k, |n| {
        _ = check(&srcs[&n]);
    });
}

/// The union of `k` literals that `k` nested arms give costs `O(k log k)` to type
/// (CHECK-literal-union-cost).
#[test]
fn a_callee_of_k_literal_arms_scales() {
    let k = 512;
    let srcs = scaling::inputs(k, |n| {
        format!("f(positional x: int) = {};\n", literal_body(n))
    });
    assert!(check(&srcs[&k]).is_none(), "rejected\n{}", srcs[&k]);
    scaling::check("a callee of k nested arms each giving a literal", k, |n| {
        _ = check(&srcs[&n]);
    });
}

/// The test of a sum of `d` names, each bound to an `if` and so summarized once, costs O(d)
/// (CHECK-sum-of-summarized-names; the program is [`summed_names`]). The row was filed at
/// 46 times at 8 times `d` (156 ms, 512 ms, 2.2 s and 7.15 s at d = 32, 64, 128 and 256, debug,
/// load about 40), but this program does not show it: on c95bec442, where the row was found,
/// it measured 7.418 (32 ms at 32, 239 ms at 256), and 8.150 and 8.931 on main 60267344b
/// (b22-checkwalk10, 2026-11-24). Each process makes the program only at the sizes it runs
/// (`check_inputs`).
#[test]
fn a_test_of_a_sum_of_summarized_names_scales() {
    scaling::check_inputs(
        "a test of a sum of d summarized names",
        32,
        |d| summed_names(d, 0),
        |src| _ = check(src),
    );
}

/// `k` tests `g(x + j) >= 1` on a callee with no summary, `g(n) = n * n - 3`, each at its own
/// argument, whose arms read `popCount(g(x + j) - 1 - past)`: not negative exactly when `past`
/// is 0, at `x + j = 2` where `g` is 1.
fn unsummed_tests(k: usize, past: i64) -> String {
    let tests: Vec<String> = (0..k)
        .map(|j| {
            format!(
                "(if g(x + {j}) >= 1 {{ popCount(g(x + {j}) - {}) }} else {{ 0 }})",
                1 + past
            )
        })
        .collect();
    format!(
        "g(positional n: int) = n * n - 3;\nh(positional x: int) = {};\n",
        tests.join(" + ")
    )
}

/// `k` tests and arms that call a callee with no summary at `k` distinct arguments cost
/// `O(k)`: each argument is one name shared by its test and its arm, its value read once at
/// the root, and each test narrows twice, through the call and through the name
/// (CHECK-implicit-call-limits, `Ck::shared_term`). The verdicts are checked at the smaller
/// size, after the timing.
#[test]
fn tests_and_arms_calling_an_unsummed_callee_scale() {
    let k = 128;
    scaling::check_inputs(
        "k tests and arms calling a callee with no summary at k arguments",
        k,
        |n| unsummed_tests(n, 0),
        |src| _ = check(src),
    );
    let src = unsummed_tests(k, 0);
    assert!(check(&src).is_none(), "rejected\n{src}");
    let src = unsummed_tests(k, 1);
    assert!(check(&src).is_some(), "accepted\n{src}");
}
