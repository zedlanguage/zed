//! Benchmarks of `families`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn star_scales() {
    scales("star", 8, 1);
}

#[test]
fn star_mixed_scales() {
    scales("star_mixed", 8, 1);
}

#[test]
fn starjoin_scales() {
    scales("starjoin", 8, 1);
}

#[test]
fn hubs_scale() {
    scales("hubs", 8, 1);
}

#[test]
fn coordmix_scales() {
    scales("coordmix", 8, 1);
}

#[test]
fn coordmix_shift_scales() {
    scales("coordmix_shift", 8, 1);
}

#[test]
fn coordmix_unmatched_scales() {
    scales("coordmix_unmatched", 8, 1);
}

#[test]
fn hole_end1_pad_scales() {
    scales("hole_end1_pad", 8, 1);
}

#[test]
fn hole_end2_pad_scales() {
    scales("hole_end2_pad", 8, 1);
}

#[test]
fn rows_one_pair_scales() {
    scales("rows_one_pair", 8, 1);
}

#[test]
fn wide_pairs_scale() {
    scales("wide_pairs", 8, 1);
}

#[test]
fn drop_ends_scale() {
    scales("drop_ends", 8, 1);
}

#[test]
fn unary_arms_scale() {
    scales("unary_arms", 8, 1);
}

/// 10.7 times the instructions at 8n while each side of a hull over two names was searched;
/// 7.1 since those sides are read off the envelopes of their rows (XR-l139-family).
#[test]
fn cuts_scale() {
    scales("cuts", 4, 1);
}

/// Each of wide's `k + 1` tests holds a sum of `k` names, so its input has `k^2` terms: order
/// `k^2` is linear in the input.
#[test]
fn wide_scales() {
    scales("wide", 8, 2);
}

/// 12.0 times the instructions at 8n while each part of a test was certified idle again at
/// each of its cases; 10.3 since the least part of each chain of disjunctions stands for the
/// parts above it (XR-l139-family, `Scope::idle_by_chain`).
#[test]
fn coordmix_floor_scales() {
    scales("coordmix_floor", 4, 1);
}

/// About `k^1.6` to `k^2` on main; about `k^1.1` to `k^1.25` since the threshold aggregate
/// reads the upper disjunctions (LAZY-hub-unsolved).
#[test]
fn coordkk_y_scales() {
    scales("coordkk_y", 8, 1);
}

/// About `k^1.8` to `k^2.1` on main; about `k^1.05` to `k^1.1` since the threshold aggregate
/// reads the upper disjunctions and every ray of a group (LAZY-hub-unsolved).
#[test]
fn coordmix_slopes_scales() {
    scales("coordmix_slopes", 4, 1);
}

/// About `k^1.2` to `k^1.8` from `k = 8` to 128 on main; with the threshold aggregate's
/// upper disjunctions (LAZY-hub-unsolved), about `k^1.2` to `k^1.4`, 15.6 times the work from
/// `k = 16` to 128 against the limit 15.4. Each of the `k` tests took one constraint on two
/// names out of a block of near `k` such constraints, and the work after it read every
/// conjunct of that block: the names of each (`Scope::due`) and a search through it
/// (`Blocks::peel`). Now the names of a block and its constraints on two names are counted as
/// they come and go (`Blocks::names_of`, `Blocks::cut`), and the blocks a block went to are
/// read from the difference of its persistent sets (`Blocks::now_of`): 9.6 times the work
/// (106M and 1,017M instructions; 113.6M and 1,768M, 15.6 times, before) and 8.4 times the
/// bytes (PERF-l139-family, COMPLEXITY.md PERF-l139-due).
#[test]
fn coordkk_scales() {
    scales("coordkk", 16, 1);
}

/// About `k^1.75` to `k^1.96`, 14.8 times the instructions at 8n, while each part of a test
/// was certified idle again at each of its cases; 10.1 since the least part of each chain of
/// disjunctions stands for the parts above it (XR-l139-family, `Scope::idle_by_chain`).
#[test]
fn star_extra_scales() {
    scales("star_extra", 4, 1);
}

/// About `k^1.7` from `k = 8` to 32. At `n = 2` the limit's log factor is 4, and main
/// passes (31.9 times the work against 35.2); at `n = 4` each run of `k = 32` takes over 30 s,
/// so the test would not finish in 60 s. 10.9 times the instructions at 8n while each part of
/// a test was certified idle again at each of its cases; 10.2 since the least part of each
/// chain of disjunctions stands for the parts above it (XR-l139-family, `Scope::idle_by_chain`).
#[test]
fn chain_scales() {
    scales("chain", 2, 1);
}

/// About `k^2.1` while each side of a hull over two names was searched; 8.8 times the
/// instructions at 8n since those sides are read off the envelopes of their rows
/// (XR-l139-family).
#[test]
fn boxstar_scales() {
    scales("boxstar", 2, 1);
}

/// About `k^2.7` to `k^2.8` on stair_holes and stair_holes_mix, and `k^2` on
/// stair_holes_late.
#[test]
fn stair_holes_scale() {
    scales("stair_holes", 4, 1);
}

#[test]
fn stair_holes_mix_scales() {
    scales("stair_holes_mix", 4, 1);
}

#[test]
fn stair_holes_late_scales() {
    scales("stair_holes_late", 8, 1);
}

/// About `k^2`.
#[test]
fn stair_cover_scales() {
    scales("stair_cover", 8, 1);
}

#[test]
fn stair_cover_free_scales() {
    scales("stair_cover_free", 8, 1);
}

/// About `k^2` from `k = 8` to 16, each run of `k = 16` some 60 billion instructions.
#[test]
fn hop_scales() {
    scales("hop", 2, 1);
}

#[test]
fn hopon_scales() {
    scales("hopon", 2, 1);
}
