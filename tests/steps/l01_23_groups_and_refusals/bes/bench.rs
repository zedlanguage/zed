//! The benchmarks of `bes.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `bes.rs`.

use super::*;

// The tests below were two: `the_families_scale`, deciding each of `FAMILIES` at n = 512, and
// `the_widened_families_scale`, deciding each of `WIDENED` at n = 4096. Each family is now a
// test of its own, sized so that its run at 8n takes about 3 s, since the 41 checks at that
// size do not fit one test of 15 s (TEST-bench-move-l0123, author P169).

/// TEST-bench-move-l0123, author P169: n was 512, now 440000; 1x 0.30 s at load 26.
#[test]
fn deciding_chain_scales() {
    scales("chain", 440000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 280000; 1x 0.37 s at load 26.
#[test]
fn deciding_ladder_scales() {
    scales("ladder", 280000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 160000; 1x 0.40 s at load 26.
#[test]
fn deciding_bigladder_scales() {
    scales("bigladder", 160000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 135000; 1x 0.28 s at load 8.
#[test]
fn deciding_flip_scales() {
    scales("flip", 135000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 150000; 1x 0.40 s at load 25.
#[test]
fn deciding_flipand_scales() {
    scales("flipand", 150000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 210000; 1x 0.57 s at load 25.
#[test]
fn deciding_hardladder_scales() {
    scales("hardladder", 210000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 120000; 1x 0.50 s at load 25.
#[test]
fn deciding_hardflip_scales() {
    scales("hardflip", 120000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 320000; 1x 0.23 s at load 9.
#[test]
fn deciding_g_chain_scales() {
    scales("g_chain", 320000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 210000; 1x 0.27 s at load 9.
#[test]
fn deciding_g_ladder_scales() {
    scales("g_ladder", 210000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 115000; 1x 0.26 s at load 8.
#[test]
fn deciding_g_bigladder_scales() {
    scales("g_bigladder", 115000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 110000; 1x 0.22 s at load 9.
#[test]
fn deciding_adv_bigladder_mor_scales() {
    scales("adv_bigladder_mor", 110000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 130000; 1x 0.23 s at load 10.
#[test]
fn deciding_reanchor_ring_scales() {
    scales("reanchor_ring", 130000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 130000; 1x 0.23 s at load 10.
#[test]
fn deciding_reanchor_cut_ring_scales() {
    scales("reanchor_cut_ring", 130000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 140000; 1x 0.50 s at load 29.
#[test]
fn deciding_bidir_trap_scales() {
    scales("bidir_trap", 140000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 380000; 1x 0.44 s at load 29.
#[test]
fn deciding_c_chain_scales() {
    scales("c_chain", 380000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 230000; 1x 0.30 s at load 30.
#[test]
fn deciding_c_ladder_scales() {
    scales("c_ladder", 230000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 120000; 1x 0.27 s at load 29.
#[test]
fn deciding_c_bigladder_scales() {
    scales("c_bigladder", 120000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 110000; 1x 0.27 s at load 29.
#[test]
fn deciding_c_adversary_scales() {
    scales("c_adversary", 110000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 190000; 1x 0.31 s at load 29.
#[test]
fn deciding_exring_scales() {
    scales("exring", 190000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 280000; 1x 0.29 s at load 28.
#[test]
fn deciding_unring_scales() {
    scales("unring", 280000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 230000; 1x 0.32 s at load 28.
#[test]
fn deciding_defeat_d_scales() {
    scales("defeatD", 230000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 81000; 1x 0.28 s at load 28.
#[test]
fn deciding_defeatgsr_scales() {
    scales("defeatgsr", 81000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 100000; 1x 0.23 s at load 28.
#[test]
fn deciding_codex_adversary_scales() {
    scales("codex_adversary", 100000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 130000; 1x 0.27 s at load 27.
#[test]
fn deciding_mu_bidir_scales() {
    scales("mu_bidir", 130000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 55000; 1x 0.25 s at load 27.
#[test]
fn deciding_guarded_mu_bidir_scales() {
    scales("guarded_mu_bidir", 55000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 130000; 1x 0.10 s at load 27.
#[test]
fn deciding_random_scales() {
    scales("random", 130000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 240000; 1x 0.25 s at load 27.
#[test]
fn deciding_tiles_scales() {
    scales("tiles", 240000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 46000; 1x 0.32 s at load 25.
#[test]
fn deciding_cut_tiles_scales() {
    scales("cut_tiles", 46000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 210000; 1x 0.28 s at load 25.
#[test]
fn deciding_cyclic_ladder_scales() {
    scales("cyclic_ladder", 210000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 130000; 1x 0.25 s at load 25.
#[test]
fn deciding_claude_flip_scales() {
    scales("claude_flip", 130000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 120000; 1x 0.26 s at load 25.
#[test]
fn deciding_claude_flipand_scales() {
    scales("claude_flipand", 120000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 140000; 1x 0.57 s at load 25.
#[test]
fn deciding_g_codex_adversary_scales() {
    scales("g_codex_adversary", 140000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 160000; 1x 0.56 s at load 25.
#[test]
fn deciding_claude_hardladder_scales() {
    scales("claude_hardladder", 160000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 110000; 1x 0.74 s at load 24.
#[test]
fn deciding_claude_hardflip_scales() {
    scales("claude_hardflip", 110000);
}

/// TEST-bench-move-l0123, author P169: n was 512, now 84000; 1x 0.42 s at load 24.
#[test]
fn deciding_indirect_alt_ladder_scales() {
    scales("indirect_alt_ladder", 84000);
}

/// `exring:6:1` of `WIDENED`. TEST-bench-move-l0123, author P169: n was 4096, now 750000; 1x 0.43 s at load 28.
#[test]
fn deciding_widened_exring_scales() {
    scales(WIDENED[0], 750000);
}

/// `defeatgsr:6:42:and` of `WIDENED`. TEST-bench-move-l0123, author P169: n was 4096, now 650000; 1x 0.57 s at load 28.
#[test]
fn deciding_widened_defeatgsr_scales() {
    scales(WIDENED[1], 650000);
}

/// `indirect_alt_ladder:6:7` of `WIDENED`. TEST-bench-move-l0123, author P169: n was 4096, now 560000; 1x 0.46 s at load 28.
#[test]
fn deciding_widened_indirect_alt_ladder_scales() {
    scales(WIDENED[2], 560000);
}

/// `g_codex_adversary:6:24:mor` of `WIDENED`. TEST-bench-move-l0123, author P169: n was 4096, now 610000; 1x 0.37 s at load 27.
#[test]
fn deciding_widened_g_codex_adversary_scales() {
    scales(WIDENED[3], 610000);
}

/// `tiles:6:0:mor` of `WIDENED`. TEST-bench-move-l0123, author P169: n was 4096, now 580000; 1x 0.51 s at load 26.
#[test]
fn deciding_widened_tiles_scales() {
    scales(WIDENED[4], 580000);
}

/// Deciding [`long_run`] of `n` and `8n` unions: the test of union edges reads each edge once,
/// with the run of unions after each node counted once (`bes::one_cycle_but_union_chords`),
/// where walking each edge along the cycle would take `n` steps an edge.
/// TEST-bench-move-l0123, author P169: n was 4096, now 700_000; 1x 0.45 s at load 26.
#[test]
fn a_long_run_of_union_edges_scales() {
    let n = 700_000;
    let small = long_run(n).bes();
    let large = long_run(scaling::FACTOR * n).bes();
    scaling::check_order("deciding a run of n unions with union edges", n, 1, |m| {
        let g = if m == n { &small } else { &large };
        std::hint::black_box(decide(std::hint::black_box(g)));
    });
}
