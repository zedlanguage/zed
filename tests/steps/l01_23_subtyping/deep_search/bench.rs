//! The benchmarks of `deep_search.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_search.rs`.

use super::*;
use zed_tests::scaling;

/// Which of the three measures a test takes.
#[derive(Clone, Copy)]
enum Measure {
    Deciding,
    Verdict,
    Comparing,
}

/// Deciding, the verdict or the subtype of types nested `n` and `8n` deep in `shape`.
/// TEST-bench-move-l0123, author P169: moved here from `deep_search.rs` with `n` (500 for all
/// nine checks before) and the measure as parameters, so that each check is a test of its own.
fn scales(what: &str, shape: fn(usize, Type) -> Type, n: usize, measure: Measure) {
    zed_tests::deep::on_small_stack(|| {
        let built = |k: usize| (shape(k, lit(0)), shape(k, lit(1)), shape(k, Type::int()));
        let (small, large) = (built(n), built(8 * n));
        let at = |k: usize| if k == n { &small } else { &large };
        // Each run is on a thread of its own, so it finds no answer kept by another.
        match measure {
            Measure::Deciding => scaling::check(&format!("deciding {what}"), n, |k| {
                assert!(!at(k).0.is_empty());
            }),
            Measure::Verdict => scaling::check(&format!("the verdict on {what}"), n, |k| {
                assert_eq!(at(k).0.verdict(), Verdict::Inhabited);
            }),
            Measure::Comparing => scaling::check(&format!("comparing {what}"), n, |k| {
                let (t, u, int) = at(k);
                assert!(!t.subtype(u) && t.subtype(int));
            }),
        }
    });
}

// The nine tests below were three, one per shape, each making the three checks at n = 500
// (TEST-bench-move-l0123, author P169).

/// TEST-bench-move-l0123, author P169: n was 500, now 18_000; 1x 0.31 s at load 31.
#[test]
fn deciding_deep_tuple_types_scales_with_depth() {
    scales("tuples", tuples, 18_000, Measure::Deciding);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 18_000; 1x 0.25 s at load 30.
#[test]
fn the_verdict_on_deep_tuple_types_scales_with_depth() {
    scales("tuples", tuples, 18_000, Measure::Verdict);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 6000; 1x 0.37 s at load 25.
#[test]
fn comparing_deep_tuple_types_scales_with_depth() {
    scales("tuples", tuples, 6000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 25_000; 1x 0.32 s at load 30.
#[test]
fn deciding_deep_atom_types_scales_with_depth() {
    scales("atoms", atoms, 25_000, Measure::Deciding);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 22_000; 1x 0.33 s at load 30.
#[test]
fn the_verdict_on_deep_atom_types_scales_with_depth() {
    scales("atoms", atoms, 22_000, Measure::Verdict);
}

/// TEST-bench-move-l0123, author P169: left at n = 500, its old size; 1x 6.6 ms at load 9. FINDING:
/// at larger n it fails the limit. At 8000 it measured 214 ms and 2393 ms, 8.33 times the work
/// and 8.0 times the bytes, 7.5 s wall; at 12,000, 406 ms and 6357 ms, 12.19 times the work and
/// 14.3 times the bytes, over 10.5, 18.4 s wall and 1.73 GB, at load 25 to 30 (2026-11-14); a
/// second run at 12,000 gave 12.19 again. A flat `perf` profile of that run (no call graphs)
/// shows `Type::cmp` 8.5%, `hashbrown` `usize` key compares 5.5%, `Type::name_digest` 5.1%,
/// `memmove` 2.9% and the drop of a `BTreeMap<(Type, Type), usize>` 1.9%: the time is spread
/// over the search's tables, with no one hot spot; the growth past n is not yet explained.
#[test]
fn comparing_deep_atom_types_scales_with_depth() {
    scales("atoms", atoms, 500, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 24_000; 1x 0.34 s at load 29.
#[test]
fn deciding_deep_morphism_types_scales_with_depth() {
    scales("morphisms", morphisms, 24_000, Measure::Deciding);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 25_000; 1x 0.34 s at load 28.
#[test]
fn the_verdict_on_deep_morphism_types_scales_with_depth() {
    scales("morphisms", morphisms, 25_000, Measure::Verdict);
}

/// TEST-bench-move-l0123, author P169: n was 500, now 4000; 1x 0.48 s at load 27.
#[test]
fn comparing_deep_morphism_types_scales_with_depth() {
    scales("morphisms", morphisms, 4000, Measure::Comparing);
}

// The seven tests below were regular tests of `deep_search.rs`, moved here as they were
// (TEST-bench-move-l0123, author P178: a test that needs an unusual depth is a benchmark);
// each has a small instance there, at depth `DEPTH` on the default test thread, of the same
// name with "nested" for "deep" or "far deeper than the stack".

/// The search overflowed a 2 MiB stack some thousands of levels down when it recursed; here it
/// goes 10,000, past that depth and no deeper, so that each test stays short (author P169: the
/// smallest depth that overflows a default stack). It went 100,000 until TEST-bench-move-l0123.
/// Moved here from `deep_search.rs` at the same depth (TEST-bench-move-l0123, author P178).
const DEEP: usize = 10_000;

/// `t` nested `DEEP` deep around `0` is inhabited, by `is_empty` and by `verdict`.
fn decides_deep(shape: fn(usize, Type) -> Type) {
    zed_tests::deep::on_small_stack(move || {
        let t = shape(DEEP, lit(0));
        assert!(!t.is_empty());
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn a_tuple_type_far_deeper_than_the_stack_is_decided() {
    decides_deep(tuples);
}

#[test]
fn an_atom_type_far_deeper_than_the_stack_is_decided() {
    decides_deep(atoms);
}

#[test]
fn a_morphism_type_far_deeper_than_the_stack_is_decided() {
    decides_deep(morphisms);
}

/// Two types nested `DEEP` deep that differ only at the bottom: the one around `0` is not under
/// the one around `1`, which the search decides on their difference, and, in a test of its own,
/// is under the one around `int`, which the simulation of rows shows. Tuples split the box on
/// their way down and morphisms meet and subtract their fields at each level; atoms do neither,
/// and theirs are compared in a test of their own and in the benchmarks. A morphism comparison
/// 100,000 levels deep took 9.1 s in the optimized test build at load 22 (EMPTY-morphism-next,
/// 2026-11-07).
fn compares_deep(shape: fn(usize, Type) -> Type, bottom: Type, under: bool) {
    zed_tests::deep::on_small_stack(move || {
        let t = shape(DEEP, lit(0));
        assert_eq!(t.subtype(&shape(DEEP, bottom)), under);
    });
}

#[test]
fn a_deep_tuple_type_is_not_under_one_that_differs_at_the_bottom() {
    compares_deep(tuples, lit(1), false);
}

#[test]
fn a_deep_tuple_type_is_under_one_wider_at_the_bottom() {
    compares_deep(tuples, Type::int(), true);
}

#[test]
fn a_deep_morphism_type_is_not_under_one_that_differs_at_the_bottom() {
    compares_deep(morphisms, lit(1), false);
}

#[test]
fn a_deep_morphism_type_is_under_one_wider_at_the_bottom() {
    compares_deep(morphisms, Type::int(), true);
}

/// Atoms, nested `DEEP` deep, compared both ways: a small instance of the comparison of
/// `comparing_deep_atom_types_scales_with_depth`.
#[test]
fn a_deep_atom_type_is_compared_by_its_bottom() {
    compares_deep(atoms, lit(1), false);
    compares_deep(atoms, Type::int(), true);
}
