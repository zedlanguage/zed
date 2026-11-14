//! Benchmarks of `exact`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn a_point_inside_a_huge_range_is_excluded_without_listing_the_range() {
    // Over `0..=10^12` the exact set of `n * n mod 10 == 9` has 4·10^11 members; excluding
    // 4 assumes `n == 4`, a box of one point, and a witness for the whole range is found by
    // halving toward the first point.
    let t = product_mod_10("n", "n", 9);
    let s = written(within(&[("n", 0, 1_000_000_000_000)], true), &[t]);
    assert!(!s.bottom);
    let t0 = zed_tests::scaling::cpu_time();
    assert!(s.assume(&is("n", 4), true, &none()).bottom);
    assert!(!s.assume(&is("n", 999_999_999_997), true, &none()).bottom);
    let took = zed_tests::scaling::cpu_time() - t0;
    assert!(took.as_secs() < 5, "took {took:?}");
}
