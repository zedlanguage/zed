//! Benchmarks of `families`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`). The sizes were set on 2026-11-14 so
//! that the run at `n` takes about 0.3 to 0.5 s and the run at `8n` about 3 to 4 s, at load
//! 20 to 30 on 32 cores (TEST-bench-move-l0139); where a larger size went over the limit of
//! 10.5 times the work at `8n`, the size is the largest that passed and the comment gives the
//! numbers, as instructions at `8n` over those at `n`, measured on the first runs.

use super::*;

#[test]
fn star_scales() {
    scales("star", 192, 1);
}

/// 7.97 times the work at 8, 10.2 at 64, 11.7 at 112.
#[test]
fn star_mixed_scales() {
    scales("star_mixed", 64, 1);
}

#[test]
fn starjoin_scales() {
    scales("starjoin", 160, 1);
}

#[test]
fn hubs_scale() {
    scales("hubs", 224, 1);
}

#[test]
fn coordmix_scales() {
    scales("coordmix", 120, 1);
}

#[test]
fn coordmix_shift_scales() {
    scales("coordmix_shift", 128, 1);
}

/// 8.8 times the work at 8, 9.6 at 32, 10.1 at 48, 12.1 at 128; 64 is over the limit.
#[test]
fn coordmix_unmatched_scales() {
    scales("coordmix_unmatched", 48, 1);
}

#[test]
fn hole_end1_pad_scales() {
    scales("hole_end1_pad", 144, 1);
}

#[test]
fn hole_end2_pad_scales() {
    scales("hole_end2_pad", 160, 1);
}

#[test]
fn rows_one_pair_scales() {
    scales("rows_one_pair", 512, 1);
}

#[test]
fn wide_pairs_scale() {
    scales("wide_pairs", 512, 1);
}

#[test]
fn drop_ends_scale() {
    scales("drop_ends", 8, 1);
}

#[test]
fn unary_arms_scale() {
    scales("unary_arms", 1536, 1);
}

/// 10.7 times the instructions at 8n while each side of a hull over two names was searched;
/// 7.1 since those sides are read off the envelopes of their rows (XR-l139-family).
#[test]
fn cuts_scale() {
    scales("cuts", 96, 1);
}

/// Each of wide's `k + 1` tests holds a sum of `k` names, so its input has `k^2` terms: order
/// `k^2` is linear in the input.
#[test]
fn wide_scales() {
    scales("wide", 16, 2);
}

/// 12.0 times the instructions at 8n while each part of a test was certified idle again at
/// each of its cases; 10.3 since the least part of each chain of disjunctions stands for the
/// parts above it (XR-l139-family, `Scope::idle_by_chain`). 10.3 at 4 and 26.1 at 32 on
/// 2026-11-14, so it stays at 4.
#[test]
fn coordmix_floor_scales() {
    scales("coordmix_floor", 4, 1);
}

/// About `k^1.6` to `k^2` on main; about `k^1.1` to `k^1.25` since the threshold aggregate
/// reads the upper disjunctions (LAZY-hub-unsolved). 10.0 times the work at 128.
#[test]
fn coordkk_y_scales() {
    scales("coordkk_y", 128, 1);
}

/// About `k^1.8` to `k^2.1` on main; about `k^1.05` to `k^1.1` since the threshold aggregate
/// reads the upper disjunctions and every ray of a group (LAZY-hub-unsolved). 8.4 times the
/// work at 4, 9.6 at 32, 10.1 at 48, 10.48 at 64 (too near the limit to keep), 11.3 at 96.
#[test]
fn coordmix_slopes_scales() {
    scales("coordmix_slopes", 48, 1);
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
/// bytes (PERF-l139-family, COMPLEXITY.md PERF-l139-due). 10.1 times at 128, 10.3 at 160.
#[test]
fn coordkk_scales() {
    scales("coordkk", 160, 1);
}

/// About `k^1.75` to `k^1.96`, 14.8 times the instructions at 8n, while each part of a test
/// was certified idle again at each of its cases; 10.1 since the least part of each chain of
/// disjunctions stands for the parts above it (XR-l139-family, `Scope::idle_by_chain`). On
/// 2026-11-14, 11.3 times at 4 (99.9M and 1,130M instructions), over the limit; 10.0 at 3,
/// 27.6 at 16.
#[test]
fn star_extra_scales() {
    scales("star_extra", 3, 1);
}

/// About `k^1.7` from `k = 8` to 32 on the code of that time, when a run of `k = 32` took over
/// 30 s. 10.9 times the instructions at 8n while each part of a test was certified idle again
/// at each of its cases; 10.2 since the least part of each chain of disjunctions stands for the
/// parts above it (XR-l139-family, `Scope::idle_by_chain`). On 2026-11-14, 9.8 times at 2, 9.0
/// at 3, 8.7 at 4, 8.8 at 6, 9.6 at 8 and 10.8 at 12.
#[test]
fn chain_scales() {
    scales("chain", 8, 1);
}

/// About `k^2.1` while each side of a hull over two names was searched; 8.8 times the
/// instructions at 8n since those sides are read off the envelopes of their rows
/// (XR-l139-family). 7.9 at 2, 9.5 at 4, 10.2 at 5, 10.9 at 6.
#[test]
fn boxstar_scales() {
    scales("boxstar", 5, 1);
}

/// About `k^2.7` to `k^2.8` on stair_holes and stair_holes_mix, and `k^2` on
/// stair_holes_late.
#[test]
fn stair_holes_scale() {
    scales("stair_holes", 2048, 1);
}

#[test]
fn stair_holes_mix_scales() {
    scales("stair_holes_mix", 2048, 1);
}

#[test]
fn stair_holes_late_scales() {
    scales("stair_holes_late", 2048, 1);
}

/// About `k^2`. 9.1 times the work at 64 and 9.2 at 112; at 128, 41.8 times the bytes (16.3 MB
/// and 683 MB), over the limit, so the run at `8n` stays short (0.2 s).
#[test]
fn stair_cover_scales() {
    scales("stair_cover", 112, 1);
}

#[test]
fn stair_cover_free_scales() {
    scales("stair_cover_free", 2048, 1);
}

/// About `k^2` from `k = 8` to 16, each run of `k = 16` some 60 billion instructions, on the code
/// of that time. 8.9 times the work at 2, 9.5 at 3, 10.1 at 4, 11.5 at 6; 5 is over the limit.
#[test]
fn hop_scales() {
    scales("hop", 4, 1);
}

/// 9.5 times the work at 2, 9.9 at 3, 10.48 at 4 (too near the limit to keep), 11.8 at 6.
#[test]
fn hopon_scales() {
    scales("hopon", 3, 1);
}
