//! The benchmarks of `surface.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `surface.rs`.

use super::*;

#[test]
fn the_text_of_a_type_shared_n_deep_scales() {
    // A pair of the level below, n deep, has 2^n paths: the text names each level once.
    // TEST-bench-move-l0123 (author P169): n was 1,000, now 24,000; 1x measured 269 ms
    // (ns=269485405) at load 25.22 on 2026-11-14.
    scaling::check("the text of a pair type shared n deep", 24000, |n| {
        let s = shared(n).surface();
        assert_eq!(s.defs.len(), n - 1);
    });
}

// The text of a type written by name is linear in the text. The three checks were one test,
// `the_text_of_a_type_written_by_name_scales`, until TEST-bench-move-l0123 (author P169) split
// it so that each runs within the time of one test.

#[test]
fn the_text_of_a_nested_tuple_written_by_name_scales() {
    // A tuple nested n deep.
    // TEST-bench-move-l0123 (author P169): n was 1,000, now 18,000; 1x measured 258 ms
    // (ns=258259072) at load 25.22 on 2026-11-14.
    let nested = scaling::inputs(18000, |n| {
        (0..n as i64).fold(lit(-1), |t, i| tuple(&[lit(i), t]))
    });
    scaling::check(
        "the text of a tuple nested n deep, written by name",
        18000,
        |n| {
            let s = nested[&n].surface_by_name(TextPlace::Any);
            assert!(s.defs.is_empty());
        },
    );
}

#[test]
fn the_text_of_a_list_type_of_lists_written_by_name_scales() {
    // A recursive type whose argument is another, n deep.
    // TEST-bench-move-l0123 (author P169): n was 100, now 57,344; 1x measured 276 ms (ns=275904224)
    // at load 25.36 on 2026-11-14.
    let lists = scaling::inputs(57344, |n| (0..n).fold(Type::int(), |t, _| list_of(t)));
    scaling::check(
        "the text of a list type of lists n deep, written by name",
        57344,
        |n| {
            let s = lists[&n].surface_by_name(TextPlace::Any);
            assert_eq!(s.root.matches("L(").count(), n);
        },
    );
}

#[test]
fn the_text_of_a_pair_type_shared_n_deep_written_by_name_scales() {
    // A pair of the level below, n deep, shares a part at each level: each level is defined
    // once, so the text grows as n log n (the names' digits), not as the 2^n leaves the
    // pair has when each part is written out at each use.
    // TEST-bench-move-l0123 (author P169): n was 1,000, now 24,000; 1x measured 166 ms
    // (ns=166472218) at load 25.36 on 2026-11-14.
    let n = 24000;
    let pairs = scaling::inputs(n, shared);
    let bytes = |n: usize| pairs[&n].surface_by_name(TextPlace::Any).to_string().len();
    scaling::hold(
        &format!(
            "the text of a pair type shared n deep, written by name: n = {n} and {}",
            scaling::FACTOR * n
        ),
        "bytes of text",
        bytes(n) as u64,
        bytes(scaling::FACTOR * n) as u64,
        1,
    );
    scaling::check(
        "the text of a pair type shared n deep, written by name",
        n,
        |n| {
            let s = pairs[&n].surface_by_name(TextPlace::Any);
            assert_eq!(s.defs.len(), n - 1);
        },
    );
}

#[test]
fn the_text_of_a_meet_with_a_long_list_scales() {
    // TEST-bench-move-l0123 (author P169): n was 256, now 20,480; 1x measured 167 ms (ns=166582881)
    // at load 25.36 on 2026-11-14.
    let inputs = scaling::inputs(20480, less_a_long_list);
    scaling::check("a meet with a decision list of n points", 20480, |n| {
        let s = inputs[&n].surface().to_string();
        assert!(!s.contains('_'), "{s}");
        assert_eq!(s.matches(" \\ ").count() + s.matches(" | ").count(), n + 2);
    });
}

#[test]
fn the_text_of_meets_n_deep_scales() {
    // Each meet asks whether its operands hold values outside every point; each node's answer
    // is kept, so the n meets read each node once and not each node below them again.
    // TEST-bench-move-l0123 (author P169): n was 128, now 4,096; 1x measured 291 ms (ns=291470748)
    // at load 25.97 on 2026-11-14.
    let inputs = scaling::inputs(4096, meets_n_deep);
    scaling::check("n meets inside each other", 4096, |n| {
        let s = inputs[&n].surface().to_string();
        assert!(!s.contains('_'), "{s}");
        assert_eq!(s.matches(" \\ ").count(), n);
    });
}

/// Moved here from `surface.rs` as it stood, 400 seeds (TEST-bench-move-l0123, author P178:
/// many cases make a benchmark); its small instance, the first 50 seeds, is
/// `a_few_unions_differences_and_intersections_of_rows_read_back_as_the_same_type`.
#[test]
fn unions_differences_and_intersections_of_rows_read_back_as_the_same_type() {
    formulas_read_back(400);
}
