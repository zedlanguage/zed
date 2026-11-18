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
#[test]
fn tests_calling_one_deep_callee_scale() {
    let k = 512;
    let (mut rng, seed) = Rng::fresh("tests_calling_one_deep_callee_scale");
    let src = stairs(&mut rng, k, 0);
    assert!(check(&src).is_none(), "seed {seed}: rejected\n{src}");
    let src = stairs(&mut rng, k, 1);
    assert!(check(&src).is_some(), "seed {seed}: accepted\n{src}");
    let srcs = scaling::inputs(k, |n| stairs(&mut Rng::new(seed ^ n as u64), n, 0));
    scaling::check("k tests calling one callee of k nested arms", k, |n| {
        _ = check(&srcs[&n]);
    });
}

/// A callee of `k` nested arms each giving a literal: `0` below 0, `j` at `x = j - 1` for `j`
/// in `1..k`, and `k` from `k - 1`. Its result type is the union of `k + 1` literals.
fn literal_body(k: usize) -> String {
    let mut f = String::from("if x < 0 { 0 }");
    for j in 1..k {
        f.push_str(&format!(" else if x < {j} {{ {j} }}"));
    }
    f.push_str(&format!(" else {{ {k} }}"));
    f
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
