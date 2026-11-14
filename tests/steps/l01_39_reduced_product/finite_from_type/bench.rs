//! Benchmarks of `finite_from_type`: each times the work at a size and at 8 times it, run
//! apart from the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn keeping_a_finite_set_against_its_type_scales_with_the_set() {
    // A set of `n` pairs `(i, i)` against the square of `0..n`, which has `n²` values: one
    // membership test per member, of order `n log n` with the set's own order. Listing the
    // type's values is of order `n²`.
    let built: std::collections::HashMap<usize, (Type, BTreeSet<Value>)> = [20_000, 160_000]
        .into_iter()
        .map(|n| (n, (square(n), (0..n).map(|i| pair(i, i)).collect())))
        .collect();
    scaling::check_order(
        "a finite set of n pairs against a square of n literals",
        20_000,
        1,
        |n| {
            let (ty, members) = &built[&n];
            assert_eq!(finite(&bound(ty, members)).map(|s| s.len()), Some(n));
        },
    );
}

#[test]
fn a_named_finite_type_reduces_in_time_linear_in_its_form() {
    // `t(d)` is written as `d + 1` types; the reduction reads each once. Listing its values,
    // `2^(2^d)` of them, does not end for `d` past 5.
    let built = scaling::inputs(20_000, t);
    scaling::check(
        "the reduction of a name of type t(d), d + 1 types written",
        20_000,
        |d| {
            assert_eq!(finite(&Product::of_type(built[&d].clone())), None);
        },
    );
}

#[test]
fn the_values_of_a_type_written_as_a_list_become_its_set_in_their_number() {
    // `(0, 0) | (1, 0) | … | (n - 1, 0)`: `n` tuples written, all of which the set holds. At
    // 10,000: at 20,000 the run, with the types built before the timing, took 15 s, near the
    // 20 s piece limit (0.35 and 3.95 s timed).
    let built = scaling::inputs(10_000, |n| {
        Type::union_all((0..n).map(|i| lit(&pair(i, 0))))
    });
    scaling::check(
        "the n values of n written tuples made a finite set",
        10_000,
        |n| {
            let p = Product::of_type(built[&n].clone());
            assert_eq!(finite(&p).map(|s| s.len()), Some(n));
        },
    );
}
