//! The benchmarks of `cells.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::cells::*;
use zed_tests::scaling;
use zedc::store::presburger::decide;

/// The chain with no point at 80 levels (`c = 2`) and 10, in work linear in the levels. Control
/// (once, not kept): with the probe over the disjunctions in place of the cells, this test fails,
/// 82.6 times the bytes from 10 to 80 levels (122,171,546 to 10,094,059,976), against 16.75.
#[test]
fn guarded_chains_with_no_point_scale() {
    assert!(!reaches_zero(80, false), "80 levels have no point");
    let fs = scaling::inputs(770, |n| chain(n, false));
    scaling::check_order("decision of a guarded chain with no point", 770, 1, |n| {
        assert_eq!(
            decide(&fs[&n]).expect("decided"),
            reaches_zero(n, false),
            "{n}"
        );
    });
}

/// Each family with no point, at 12 levels and 96, in work linear in the levels: the wide ones
/// over about 6 and 48 cells, the cells decided together. Control (once, not kept): before M5
/// (C55), with each cell's conjunction solved alone, the wide family took 34.4 M and 694 M
/// instructions, 20.2 times the work, and the test failed. On M5 it still passes with
/// `has_point`'s three cell methods turned off (3.0 s against 1.4 s): the later methods
/// decide these chains in linear work too, so the test now holds the whole decision to it.
#[test]
fn wide_nested_and_joined_guards_with_no_point_scale() {
    for name in ["wide", "nest", "or", "and"] {
        let guard = family(name);
        let fs = scaling::inputs(190, |n| {
            let r = family_range(name, n);
            let target = missed(&guarded_run(n, r, guard));
            guarded(n, r, guard, target)
        });
        let what = format!("decision of a {name} chain with no point");
        scaling::check_order(&what, 190, 1, |n| {
            assert!(!decide(&fs[&n]).expect("decided"), "{name} {n}");
        });
    }
}

/// Every guarded chain from 1 to 96 levels, with either constant, decided as running it decides:
/// a long run (author P178); `cells::guarded_chains_are_decided_as_run` takes those up to 35.
#[test]
fn guarded_chains_up_to_96_levels_are_decided_as_run() {
    guarded_chains_up_to(96);
}

/// The chains of each guarded family from 1 to 40 levels: a long run (author P178);
/// `cells::wide_nested_and_joined_guards_are_decided_as_run` takes those up to 12.
#[test]
fn wide_nested_and_joined_guards_up_to_40_levels_are_decided_as_run() {
    guarded_families_up_to(40);
}

/// The chain with one guard of `n` points copied into all `n` levels, at `n` = 250 and 707 (about
/// 67 000 and 514 000 atoms), in work linear in the formula's size. Control (once, not kept): with
/// the merge over all runs in place of `cells_without`, this test fails, 11.4 times the work.
#[test]
fn one_guard_copied_into_every_level_scales_with_the_formula() {
    let fs = scaling::inputs(250 * 250, |m| shared_guard(m.isqrt()));
    scaling::check_order(
        "decision of a chain with one guard in every level",
        250 * 250,
        1,
        |m| {
            assert!(!decide(&fs[&m]).expect("decided"), "{m}");
        },
    );
}
