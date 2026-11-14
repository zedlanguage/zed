use std::collections::BTreeMap;

use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zedc::check::ty;

use super::super::deep_ops::{
    functions, levels, on_shallow_stack, shared, shared_value, sig, tuples, value, y, z,
};

/// Checks that `op` on what `build` makes for each size takes time linear in the size, on a
/// 2 MiB stack; what is built is not measured.
fn linear<T: Sync>(what: &str, n: usize, build: impl Fn(usize) -> T, op: impl Fn(&T) + Sync) {
    let made: BTreeMap<usize, T> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|k| (k, build(k)))
        .collect();
    on_small_stack(|| scaling::check_order(what, n, 1, |k| op(&made[&k])));
}

#[test]
fn meet_takes_linear_time_in_the_depth() {
    linear(
        "meet of two tuples n deep",
        10_000,
        |k| (tuples(k, z()), tuples(k, z())),
        |(a, b)| assert!(!a.meet(b).is_empty()),
    );
}

#[test]
fn meets_takes_linear_time_in_the_depth() {
    linear(
        "meets of two tuples n deep",
        10_000,
        |k| (tuples(k, z()), tuples(k, y())),
        |(a, b)| assert!(!a.meets(b)),
    );
}

#[test]
fn contains_takes_linear_time_in_the_depth() {
    linear(
        "contains of a tuple n deep",
        10_000,
        |k| (tuples(k, z()), value(k, "z")),
        |(a, v)| assert!(a.contains(v)),
    );
}

// Each side of the three checks below holds `2^n` paths through `n` tuples, and no tuple is
// shared between the sides: a walk that followed the paths took `2^n` time.

#[test]
fn meet_of_shared_tuples_takes_linear_time() {
    linear(
        "meet of two shared tuples n deep",
        2000,
        |k| (shared(k, z()), shared(k, ty::Ty::union(&z(), &y()))),
        |(a, b)| assert!(!a.meet(b).is_empty()),
    );
}

#[test]
fn meets_of_shared_tuples_takes_linear_time() {
    linear(
        "meets of two shared tuples n deep",
        2000,
        |k| (shared(k, z()), shared(k, y())),
        |(a, b)| assert!(!a.meets(b)),
    );
}

#[test]
fn contains_of_a_shared_value_takes_linear_time() {
    linear(
        "contains of a shared value in a shared tuple n deep",
        2000,
        |k| (shared(k, z()), shared_value(k)),
        |(a, v)| assert!(a.contains(v)),
    );
}

#[test]
fn printing_a_type_with_a_function_at_every_place_takes_linear_time_in_the_depth() {
    // The printer decides each part's parentheses from where it stands, once per part.
    linear(
        "printing a type n deep with a function at every place",
        2000,
        functions,
        |t| assert!(!t.to_string().is_empty()),
    );
}

#[test]
fn debug_of_a_type_takes_linear_time_in_the_depth() {
    linear(
        "Debug of a type n deep",
        10_000,
        |k| levels(k, z()),
        |t| assert!(!format!("{t:?}").is_empty()),
    );
}

#[test]
fn subtype_of_tuples_takes_linear_time_in_the_depth() {
    linear(
        "subtype of two tuples n deep",
        2000,
        |k| (tuples(k, z()), tuples(k, y())),
        |(a, b)| assert!(!a.subtype(b)),
    );
}

#[test]
fn subtype_of_types_takes_linear_time_in_the_depth() {
    linear(
        "subtype of two types n deep",
        2000,
        |k| (levels(k, z()), levels(k, z())),
        |(a, b)| assert!(a.subtype(b)),
    );
}

#[test]
fn diff_takes_linear_time_in_the_depth() {
    linear(
        "diff of two tuples n deep",
        2000,
        |k| (tuples(k, z()), tuples(k, y())),
        |(a, b)| assert!(!a.diff(b).is_empty()),
    );
}

#[test]
fn fits_sig_takes_linear_time_in_the_depth() {
    linear(
        "fits_sig of two signatures n deep",
        2000,
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
