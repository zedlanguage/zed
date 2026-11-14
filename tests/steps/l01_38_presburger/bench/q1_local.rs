//! The benchmarks of `q1_local.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::q1_local::*;
use zedc::store::presburger::Refusal;

#[test]
fn growth_of_the_hub_family() {
    // 9.39x. The hub variable joins the blocks; the first block of four is refused.
    grows(
        "the hub family",
        64,
        Err(Refusal::Growth),
        crate::scaling::blocks_with_a_hub,
    );
}

#[test]
fn sliding_windows_of_four_are_decided() {
    // 9.3x the instructions and 8.4x the bytes from 64 to 512 (load 8 to 12, 2026-11-08). Refused
    // with Growth at every size until the exact eliminations were also taken by the terms they
    // write (`System::shrink`): `Sides::fill` counted each opposite pair of windows as growing.
    grows("sliding windows of four", 64, Ok(true), |n| windows(n).0);
}

#[test]
fn growth_of_weighted_sliding_windows() {
    // 9.25x to the refusal.
    grows("weighted sliding windows", 64, Err(Refusal::Growth), |n| {
        weighted_windows(n).0
    });
}

#[test]
fn growth_of_offsets_laid_end_to_end() {
    // 9.3x the instructions and 8.0x the bytes from 256 to 2048, 2.09x, 2.15x and 2.08x per
    // doubling (load 14, 2026-11-08); from 64 to 512, 9.3x and 8.0x. Before, `Omega::flush`
    // resolved every definition of the chain in full (1, 2, ..., n terms) and
    // `System::refresh` read the sum of the n lengths once for each of them, both O(n^2):
    // 16.8x and 16.2x from 64 to 512 (2.37x, 2.53x, 2.81x per doubling), and 34.2x and 30.4x
    // from 256 to 2048 (2.88x, 3.28x, 3.63x), which fails here; so the sizes start at 256.
    // Before that, 23.4x and 32.4x from 64 to 512 until the pivot of an equality was taken
    // among the variables no other equality holds (`pivots`): the chain
    // `o[i+1] == o[i] + l[i]` wrote rows of 3 to n + 1 terms.
    grows("offsets laid end to end", 256, Ok(true), offsets);
}

#[test]
fn growth_of_a_convex_valley() {
    // 9.4x the instructions and 8.1x the bytes from 64 to 512 (load 27, 2026-11-08). Without
    // `System::dominated`, once the stage of `System::shrink` was added, 38.1x the bytes: each
    // step carried one more row `k·x - (k - 1)·y >= -N` implied by the next.
    grows("a convex valley", 64, Ok(true), convex);
}

#[test]
fn growth_of_sums_over_grid_squares() {
    // 10.25x to the refusal.
    grows("sums over grid squares", 144, Err(Refusal::Growth), |n| {
        grid_squares(side(n)).0
    });
}

#[test]
fn growth_of_a_band_of_four() {
    // 10.03x to the refusal.
    grows("a band of four", 64, Err(Refusal::Growth), |n| band(n).0);
}

#[test]
fn growth_of_sparse_random_rows() {
    // 9.46x to the refusal.
    grows("sparse random rows", 64, Err(Refusal::Growth), |n| {
        sparse_random(n).0
    });
}

#[test]
fn growth_of_chained_blocks_of_five() {
    // 9.40x to the refusal.
    grows("chained blocks of five", 32, Err(Refusal::Growth), |n| {
        chained_blocks(n).0
    });
}

#[test]
fn growth_of_a_tree_of_blocks_of_five() {
    // 9.29x to the refusal.
    grows("a tree of blocks of five", 32, Err(Refusal::Growth), |n| {
        tree_blocks(n).0
    });
}

#[test]
fn growth_of_chained_blocks_with_a_far_contradiction() {
    // 9.42x.
    grows(
        "chained blocks, far contradiction",
        32,
        Ok(false),
        chained_blocks_empty,
    );
}
