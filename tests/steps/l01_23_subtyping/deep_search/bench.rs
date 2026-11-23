//! The benchmarks of `deep_search.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_search.rs`.

use super::*;
use zed_kernel::types::Universe;
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
        let (small, large) = (built(n), built(scaling::FACTOR * n));
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

/// Size (PERF-deep-atom-compare): n 500 before, now 5000. At TEST-bench-move-l0123 (2026-11-14,
/// processor time at load 25 to 30) the ratio was 8.33 at 8000 and 12.19 at 12,000, twice, with
/// the bytes 14.3 times. On main at de376d336, with no change of this row to the kernel, the
/// instructions under DynamoRIO grew 8.14 times from 2000 (350M to 2,845M), 8.15 from 8000
/// (1,415M to 11,532M) and 8.15 from 12,000 (2,103M to 17,139M), bytes 8.0 times at each, on a
/// Colab VM (2026-11-22): the growth past n no longer reproduces, so an earlier row fixed it.
/// 1x at 8000 took 1.42 s by `ns`, so the 1 s size is about 5000.
#[test]
fn comparing_deep_atom_types_scales_with_depth() {
    scales("atoms", atoms, 5000, Measure::Comparing);
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

/// `levels` levels around `bottom`, five operations in turn: a pair `(t, 1)`, a union with `0`,
/// a meet with the tuples (which takes the `0` away again), a union with `#nil` less `#nil`, and
/// the morphism `{int: t}`. The meet and the difference give back the type they were given, so
/// the chain is the type [`shallow`] builds with only the pairs and the morphisms.
fn chain(levels: usize, bottom: Type) -> Type {
    let (zero, nil) = (lit(0), Type::atom("nil"));
    let tuples = Type::universe(Universe::Tuple);
    (0..levels).fold(bottom, |t, k| match k % 5 {
        0 => Type::tuple(vec![t, lit(1)]),
        1 => &t | &zero,
        2 => &t & &tuples,
        3 => (&t | &nil) - &nil,
        _ => Type::exact(Type::int(), t),
    })
}

/// The type [`chain`] is, built with only its pairs and morphisms.
fn shallow(levels: usize, bottom: Type) -> Type {
    (0..levels / 5).fold(bottom, |t, _| {
        Type::exact(Type::int(), Type::tuple(vec![t, lit(1)]))
    })
}

/// Runs `f` on a 2 MiB stack, whatever `RUST_MIN_STACK` says, and prints its time.
fn timed(what: &str, f: impl FnOnce() + Send) {
    zed_tests::deep::on_small_stack(|| {
        let start = std::time::Instant::now();
        f();
        eprintln!("{what} in {:.2?}", start.elapsed());
    });
}

/// The levels of the chain STACK-big-tests (a44c82a2) probed on a 2 MiB stack and did not
/// commit (TESTS-STACK-big-tests-deep-ops, test audit 2026-11-08 row 15).
const CHAIN: usize = 50_000;

/// The chain of union, meet, difference, pair and morphism `CHAIN` levels deep is built and
/// decided on a 2 MiB stack, and is the type its pairs and morphisms alone build, in both
/// directions. Each of these steps took time linear in the depth: 28 ms to build 16,000
/// levels, 40 ms for the verdict, microseconds for each comparison, since the chain is built
/// equal to its shallow composition (2026-11-22, five depths from 1000 to 16,000 run at once).
/// The whole test took 343 ms on an 8-thread VM (2026-11-22).
#[test]
fn a_chain_of_the_five_operations_50_000_levels_deep_is_the_shallow_composition() {
    timed(&format!("a chain of {CHAIN} levels"), || {
        let t = chain(CHAIN, lit(0));
        let same = shallow(CHAIN, lit(0));
        assert!(t.subtype(&same), "the chain under its shallow composition");
        assert!(same.subtype(&t), "the shallow composition under the chain");
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

/// The levels of [`a_chain_of_the_five_operations_4000_levels_deep_is_not_under_another_bottoms`]:
/// 800 morphisms and 800 pairs in turn, past the depth at which a search by recursion
/// overflowed a 2 MiB stack.
// FINDING (2026-11-22, not yet fixed): the comparison below takes time quadratic in the depth.
// At 1000, 2000, 4000, 8000 and 16,000 levels of `chain` it took 0.25 s, 0.99 s, 3.18 s,
// 11.80 s and 48.20 s, about 4 times a doubling (five depths run at once on an 8-thread VM);
// at 50,000 levels the whole test took 600 s. Pure tuple and pure morphism types compare within
// the ratio limit (`comparing_deep_tuple_types_scales_with_depth`,
// `comparing_deep_morphism_types_scales_with_depth`); a morphism of a pair does not. The
// simulation fails at the top (`Simulation::rows`: the two morphism parts differ), and the
// time is in `is_empty` of `a - b`: a probe (not committed) nested `a` and `b` 200, 400, 800
// and 1600 deep around `0` and `1` and timed the two steps apart. Building `a - b` took 13 to
// 85 µs at every depth. Deciding it took 10.4, 19.7, 39.7 and 76.4 ms for `{int: t}` and 9.6,
// 18.3, 36.0 and 77.5 ms for `(t, 1)`, linear, but 0.24, 0.90, 3.27 and 11.28 s for
// `{int: (t,)}` and 0.25, 0.94, 3.21 and 11.92 s for `{int: (t, 1)}`, about 3.6 times a
// doubling: the search is quadratic where a morphism's value is a tuple. Not yet located
// within the search (no profiler on the VM). No ratio is checked here until it is fixed.
const UNEQUAL: usize = 4000;

/// The chain `UNEQUAL` levels deep is not under the shallow composition around another bottom,
/// on a 2 MiB stack.
#[test]
fn a_chain_of_the_five_operations_4000_levels_deep_is_not_under_another_bottoms() {
    timed(&format!("a chain of {UNEQUAL} levels compared"), || {
        let t = chain(UNEQUAL, lit(0));
        assert!(!t.subtype(&shallow(UNEQUAL, lit(1))));
    });
}
