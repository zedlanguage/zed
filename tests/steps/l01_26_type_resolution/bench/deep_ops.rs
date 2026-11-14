//! The operations on types nested deep: each runs on a type [`DEEP`] levels deep on a stack of
//! [`SHALLOW_STACK`] bytes, and each costs time linear in the depth. Their results on types a
//! few levels deep are checked in `deep_ops`.

use std::collections::BTreeMap;

use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zedc::check::ty;

use super::super::deep_ops::{
    self, functions, levels, shared, shared_value, sig, tuples, value, y, z,
};

/// The depth of the deep checks here. They ran 100,000 deep on a 2 MiB stack (T2-ty), and the
/// two slowest 20,000 deep on a fifth of it, after taking 73 s and over 80 s alone at load 42
/// (TESTS-l01_29-split); their time is linear in the depth, and they need no more stack at
/// 20,000 levels than at 100. Each now runs 13,000 deep, about an eighth of 100,000, on the
/// same fraction of 2 MiB; 13,000 and 100,000 leave the same remainder by 6, so the outermost
/// level of [`levels`] and the parity of the depth are as they were
/// (TEST-bench-move-l0126).
pub(super) const DEEP: usize = 13_000;

/// A 2 MiB stack scaled by [`DEEP`] / 100,000, so a check that takes stack a level overflows it
/// as it would overflow 2 MiB at 100,000 levels: a walk of two tuples that recurses once a
/// level, about 30 bytes a level, overflows both.
const SHALLOW_STACK: usize = (2 << 20) * DEEP / 100_000;

/// Runs `f` on a thread with a stack of [`SHALLOW_STACK`] bytes.
pub(super) fn on_shallow_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    scaling::on_a_thread(SHALLOW_STACK, f)
}

/// Besides running on a shallow stack: the checks of `deep_ops::clone_hash_and_drop`, run at a few
/// levels by `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn clone_hash_and_drop_of_a_deep_type_run_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::clone_hash_and_drop(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::display_and_debug`, run at a few
/// levels by `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn display_and_debug_of_a_deep_type_run_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::display_and_debug(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::union`, run at a few levels by
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn union_of_deep_types_runs_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::union(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::meet_meets_and_contains`, run at a
/// few levels by `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn meet_meets_and_contains_of_deep_tuples_run_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::meet_meets_and_contains(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::subtype_of_types`, run at a few
/// levels by `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn subtype_of_deep_types_runs_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::subtype_of_types(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::subtype_of_data`, run at a few
/// levels by `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn subtype_of_deep_data_runs_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::subtype_of_data(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::diff`, run at a few levels by
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn diff_of_deep_types_runs_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::diff(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::kernel`, run at a few levels by
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn kernel_of_deep_tuples_runs_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::kernel(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::variables`, run at a few levels by
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn variables_of_a_deep_type_run_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::variables(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::signatures`, run at a few levels by
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn signatures_of_deep_types_run_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::signatures(DEEP));
}

/// Besides running on a shallow stack: the checks of `deep_ops::signatures_that_differ`, run at a
/// few levels by `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn signatures_of_deep_tuples_that_differ_run_on_a_shallow_stack() {
    on_shallow_stack(|| deep_ops::signatures_that_differ(DEEP));
}

/// Checks that `op` on what `build` makes for each size takes time linear in the size, on a
/// 2 MiB stack; what is built is not measured.
fn linear<T: Sync>(what: &str, n: usize, build: impl Fn(usize) -> T, op: impl Fn(&T) + Sync) {
    let made: BTreeMap<usize, T> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|k| (k, build(k)))
        .collect();
    on_small_stack(|| scaling::check_order(what, n, 1, |k| op(&made[&k])));
}

/// Besides its ratio: the meet of equal tuples is not empty. Small instance:
/// `deep_ops::meet_meets_and_contains_of_shallow_tuples_are_as_built`.
#[test]
fn meet_takes_linear_time_in_the_depth() {
    linear(
        "meet of two tuples n deep",
        10_000,
        |k| (tuples(k, z()), tuples(k, z())),
        |(a, b)| assert!(!a.meet(b).is_empty()),
    );
}

/// Besides its ratio: tuples that differ at the bottom do not meet. Small instance:
/// `deep_ops::meet_meets_and_contains_of_shallow_tuples_are_as_built`.
#[test]
fn meets_takes_linear_time_in_the_depth() {
    linear(
        "meets of two tuples n deep",
        40_000,
        |k| (tuples(k, z()), tuples(k, y())),
        |(a, b)| assert!(!a.meets(b)),
    );
}

/// Besides its ratio: the tuples contain the value built alike. Small instance:
/// `deep_ops::meet_meets_and_contains_of_shallow_tuples_are_as_built`.
#[test]
fn contains_takes_linear_time_in_the_depth() {
    linear(
        "contains of a tuple n deep",
        50_000,
        |k| (tuples(k, z()), value(k, "z")),
        |(a, v)| assert!(a.contains(v)),
    );
}

// Each side of the three checks below holds `2^n` paths through `n` tuples, and no tuple is
// shared between the sides: a walk that followed the paths took `2^n` time.

/// Besides its ratio: the meet of shared tuples with a wider bottom is not empty. Small instance:
/// `deep_ops::meet_meets_and_contains_of_shallow_tuples_are_as_built`.
#[test]
fn meet_of_shared_tuples_takes_linear_time() {
    linear(
        "meet of two shared tuples n deep",
        10_000,
        |k| (shared(k, z()), shared(k, ty::Ty::union(&z(), &y()))),
        |(a, b)| assert!(!a.meet(b).is_empty()),
    );
}

/// Besides its ratio: shared tuples that differ at the bottom do not meet. Small instance:
/// `deep_ops::meet_meets_and_contains_of_shallow_tuples_are_as_built`.
#[test]
fn meets_of_shared_tuples_takes_linear_time() {
    linear(
        "meets of two shared tuples n deep",
        64_000,
        |k| (shared(k, z()), shared(k, y())),
        |(a, b)| assert!(!a.meets(b)),
    );
}

/// Besides its ratio: shared tuples contain the shared value. Small instance:
/// `deep_ops::meet_meets_and_contains_of_shallow_tuples_are_as_built`.
#[test]
fn contains_of_a_shared_value_takes_linear_time() {
    linear(
        "contains of a shared value in a shared tuple n deep",
        64_000,
        |k| (shared(k, z()), shared_value(k)),
        |(a, v)| assert!(a.contains(v)),
    );
}

#[test]
fn printing_a_type_with_a_function_at_every_place_takes_linear_time_in_the_depth() {
    // The printer decides each part's parentheses from where it stands, once per part.
    linear(
        "printing a type n deep with a function at every place",
        64_000,
        functions,
        |t| assert!(!t.to_string().is_empty()),
    );
}

/// Besides its ratio: `Debug` writes something. Small instance: `deep_ops::display_and_debug` in
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn debug_of_a_type_takes_linear_time_in_the_depth() {
    linear(
        "Debug of a type n deep",
        10_000,
        |k| levels(k, z()),
        |t| assert!(!format!("{t:?}").is_empty()),
    );
}

/// Besides its ratio: tuples that differ at the bottom are no subtype. Small instance:
/// `deep_ops::subtype_of_data` in
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn subtype_of_tuples_takes_linear_time_in_the_depth() {
    linear(
        "subtype of two tuples n deep",
        2000,
        |k| (tuples(k, z()), tuples(k, y())),
        |(a, b)| assert!(!a.subtype(b)),
    );
}

/// Besides its ratio: equal types are subtypes. Small instance: `deep_ops::subtype_of_types` in
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn subtype_of_types_takes_linear_time_in_the_depth() {
    linear(
        "subtype of two types n deep",
        32_000,
        |k| (levels(k, z()), levels(k, z())),
        |(a, b)| assert!(a.subtype(b)),
    );
}

/// Besides its ratio: the difference of tuples that differ at the bottom is not empty. Small
/// instance: `deep_ops::diff` in
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn diff_takes_linear_time_in_the_depth() {
    linear(
        "diff of two tuples n deep",
        2000,
        |k| (tuples(k, z()), tuples(k, y())),
        |(a, b)| assert!(!a.diff(b).is_empty()),
    );
}

/// Besides its ratio: equal signatures fit. Small instance: `deep_ops::signatures` in
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn fits_sig_takes_linear_time_in_the_depth() {
    linear(
        "fits_sig of two signatures n deep",
        20_000,
        |k| {
            (
                sig(levels(k, z()), levels(k, z())),
                sig(levels(k, z()), levels(k, z())),
            )
        },
        |(s, q)| assert!(ty::fits_sig(s, q)),
    );
}

/// The instructions a level of `op` on what `build` makes: the least of two runs at `2n` less
/// the least of two at `n`, over `n`, so the work done once, as starting the thread, cancels.
/// What is built is not measured. `None` where the meter counts no instructions: processor
/// time moves with the load.
fn per_level<T: Sync>(n: usize, build: impl Fn(usize) -> T, op: impl Fn(&T) + Sync) -> Option<u64> {
    let mut meter = scaling::Meter::new();
    if !meter.unit().starts_with("instructions") {
        return None;
    }
    let mut least = |k: usize| {
        let made = build(k);
        (0..2)
            .map(|_| meter.work(|| on_shallow_stack(|| op(&made))).units)
            .min()
            .expect("two runs")
    };
    let (small, large) = (least(n), least(2 * n));
    Some(large.saturating_sub(small) / n as u64)
}

/// The instructions a level of a subtype verdict, `fits_sig`, `why_unfit` and a difference on
/// tuples nested `n` deep stay bounded (PERF-deep-ops-slow): a change that costs more a level
/// fails here, where the linear checks above pass it. Each bound is about 10% over the count of
/// this test when it was set (2026-11-12), and below the count on main before
/// PERF-deep-ops-slow, given beside it. The counts include the test allocator's counting.
///
/// Besides its bounds: the difference of tuples that differ at the bottom is the first, and the
/// signatures do not fit. Small instances: `deep_ops::diff`, `deep_ops::subtype_of_data` (the
/// verdict) and `deep_ops::signatures_that_differ` (`why_unfit`), in
/// `deep_ops::the_operations_on_a_type_a_few_levels_deep_are_as_built`.
#[test]
fn subtype_fits_why_and_diff_cost_a_bounded_number_of_instructions_a_level() {
    let n = 2000;
    let pairs = |k: usize| (tuples(k, z()), tuples(k, y()));
    let sigs = |k: usize| {
        (
            sig(tuples(k, z()), tuples(k, z())),
            sig(tuples(k, y()), tuples(k, z())),
        )
    };
    // (what, measured, bound, before PERF-deep-ops-slow), in instructions a level.
    let checks = [
        (
            "verdict of two tuples n deep",
            per_level(n, pairs, |(a, c)| {
                std::hint::black_box(a.verdict(c));
            }),
            286_000,
            315_516,
        ),
        (
            "diff of two tuples n deep",
            per_level(n, pairs, |(a, c)| assert_eq!(&a.diff(c), a)),
            245_000,
            570_672,
        ),
        (
            "fits_sig of two signatures n deep",
            per_level(n, sigs, |(s, r)| assert!(!ty::fits_sig(s, r))),
            537_000,
            714_888,
        ),
        (
            "why_unfit of two signatures n deep",
            per_level(n, sigs, |(s, r)| {
                std::hint::black_box(ty::why_unfit(s, r));
            }),
            930_000,
            1_083_786,
        ),
    ];
    let over: Vec<String> = checks
        .iter()
        .filter_map(|(what, measured, bound, before)| {
            let Some(measured) = measured else {
                eprintln!("{what}: no counter of instructions, not checked");
                return None;
            };
            eprintln!("{what}: {measured} instructions a level, bound {bound}, before {before}");
            (measured > bound).then(|| format!("{what}: {measured} over {bound}"))
        })
        .collect();
    assert!(
        over.is_empty(),
        "instructions a level over the bound: {over:?}"
    );
}
