//! The scaling half of `ref_memo.rs` (plan item PERF-ref-memo-quadratic): each of the 48
//! families of the item's benchmark, the one-input shapes of PROOF-preimage-ref-chain-cost,
//! the two-input threshold chains of PERF-ref-memo-multi-input, and the two-input chains of
//! remainders of PERF-ref-memo-moduli-tables (also over the modulus),
//! at n and 8n, held to the plan's limit
//! (`scaling::LIMIT`) in instructions and bytes, with no wider limit for any family; each
//! answer grows at most 8 times (`output_grid` demands four values, 4n pieces). The answers
//! of every family at small sizes are checked against the interpreter in `ref_memo.rs`.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage_ref::{Demand, Domains, preimage};

use crate::bench::s22::on_big_stack;
use crate::ref_memo::{
    MIN_GAP_B_NODES, alternating_moduli, answer_pieces, family, i_and_m, min_gap_if_tree_nodes,
    output_grid, round_down_most,
};

/// [`scaling::compare`] on the reference preimage of the family `name` at `n` and `8n` links: a
/// pass of order n, held to [`scaling::LIMIT`] with the note from [`scaling::PREFERRED`]. Every
/// family's answer grows at most 8 times from `n` to `8n`; the work of writing out a larger
/// answer is held by [`output_grid_work_grows_with_its_answer`], at one `n`.
fn scales(name: &str, n: usize) {
    on_big_stack(|| {
        let large_n = n * scaling::FACTOR;
        let (small, large) = (family(name, n), family(name, large_n));
        let run = |cases: &[(Term, Domains, Demand)]| {
            for (t, ds, d) in cases {
                std::hint::black_box(preimage(t, ds, d));
            }
        };
        let what = format!("the reference preimage of the family {name}, sizes {n} and {large_n}");
        scaling::compare(&what, 1, || run(&small), || run(&large));
    });
}

/// One test a family, each at the first size the item's scorer used, except where a note says.
macro_rules! scaling_tests {
    ($($(#[$meta:meta])* $test:ident: $name:literal at $n:literal;)*) => {
        $(
            $(#[$meta])*
            #[test]
            fn $test() {
                scales($name, $n);
            }
        )*
    };
}

scaling_tests! {
    const2_narrow_scales: "const2_narrow" at 64;
    const2_wide_scales: "const2_wide" at 64;
    const_base_wide_scales: "const_base_wide" at 64;
    cross_2in_scales: "cross_2in" at 16;
    div_base_i_le_j_scales: "div_base_i_le_j" at 64;
    guarded_holes_narrow_scales: "guarded_holes_narrow" at 256;
    guarded_holes_wide_scales: "guarded_holes_wide" at 64;
    i_le_j_narrow_scales: "i_le_j_narrow" at 64;
    i_le_j_wide_scales: "i_le_j_wide" at 64;
    indep_const2_scales: "indep_const2" at 64;
    indep_small_scales: "indep_small" at 6;
    interleaved_wide_scales: "interleaved_wide" at 64;
    jmod5_mega_scales: "jmod5_mega" at 64;
    jmod5_narrow_scales: "jmod5_narrow" at 64;
    jmod5_ne100_scales: "jmod5_ne100" at 64;
    jmod5_top_scales: "jmod5_top" at 64;
    jmod5_wide_scales: "jmod5_wide" at 64;
    lambda_chain_scales: "lambda_chain" at 64;
    let_chain_scales: "let_chain" at 64;
    ne_guard_wide_scales: "ne_guard_wide" at 64;
    nested_moduli_946_eq_scales: "nested_moduli_946_eq" at 2;
    nested_moduli_eq_scales: "nested_moduli_eq" at 2;
    // At n = 0 mod 10, so both sizes put the same constants next to the root (they repeat every
    // 10 links); at 32 and 256 the answer went from 5 pieces to 772, a different question.
    nested_moduli_eq_4096_scales: "nested_moduli_eq_4096" at 160;
    nested_moduli_eq_long_scales: "nested_moduli_eq" at 128;
    nested_moduli_mod7_scales: "nested_moduli_mod7" at 2;
    normal_add_base_scales: "normal_add_base" at 16;
    normal_div_chain_scales: "normal_div_chain" at 16;
    normal_holey_guards_scales: "normal_holey_guards" at 16;
    normal_incompatible_moduli_16_scales: "normal_incompatible_moduli" at 16;
    normal_incompatible_moduli_scales: "normal_incompatible_moduli" at 4;
    // At 1024 (BENCH-ref-memo-normal-min-gap-bytes), as `normal_round_down` below: the first run
    // allocates a + b log2 n bytes per link, b near 4,500 (a rise of 4,065 to 4,947 at each
    // doubling from 128 to 8192: 58.6k, 62.8k, 67.3k, 72.3k, 76.8k, 80.9k, 85.3k per link, with
    // no growth in the rise, which a term c n per link would double), the path copies of the
    // persistent labels, whose largest has n / 2 pieces (`counts::inverse_most`). At 16 the
    // ratio of such work is 8 (a + 7b) / (a + 4b), over 10.5 when a < 5.6 b: it read 10.40 to
    // 10.73 as a fell; at 1024 the ratio is at most 8 log(8n) / log n = 10.4 for any a (P300),
    // and reads 9.45 by the per-link bytes above. Byte counts do not depend on load. Proof of
    // the log factor: row PROOF-min-gap-log-per-link.
    normal_min_gap_scales: "normal_min_gap" at 1024;
    normal_mixed_moduli_scales: "normal_mixed_moduli" at 16;
    normal_mod_chain_scales: "normal_mod_chain" at 16;
    normal_mul_base_scales: "normal_mul_base" at 16;
    normal_mul_chain_scales: "normal_mul_chain" at 16;
    normal_named_scales: "normal_named" at 16;
    normal_named_modguard_scales: "normal_named_modguard" at 16;
    normal_named_reflection_scales: "normal_named_reflection" at 16;
    normal_rel_guard_scales: "normal_rel_guard" at 16;
    // At 1024 (FAIL-ref-memo-round-down-ratio, COMPLEXITY.md K124): each link costs a + b log2 n
    // instructions (a near 190,000, b near 32,500), proved in K124 and at `Tx::inverse_states`:
    // every tree operation at a link follows one path of the persistent partition tree, which
    // has at most n nodes. For any a >= 0 the ratio at n and 8n, 8 (a + b log 8n) / (a + b log n),
    // is at most 8 log(8n) / log n: 10.4 at 1024, 14.0 at 16. At 16 the test passed or failed on
    // a alone (10.74 on 28fe3807f, 10.21 on ea99d8093 with a larger a) and let a walk of the
    // whole tree at every link through (10.22); at 1024 it reads 9.59 and that walk fails it
    // (10.61).
    normal_round_down_scales: "normal_round_down" at 1024;
    normal_round_trip_scales: "normal_round_trip" at 16;
    // Four values demanded: 4n pieces. At 8 the answer-free work was 84% of the run.
    output_grid_scales: "output_grid" at 64;
    pathological_2var_scales: "pathological_2var" at 16;
    pathological_abs_scales: "pathological_abs" at 16;
    pow2_small_scales: "pow2_small" at 8;
    pow2_wide_scales: "pow2_wide" at 64;
    random_chains_scales: "random_chains" at 64;
    // PROOF-preimage-ref-chain-cost: the step shapes `Tx::back_doubt` named as possibly
    // quadratic. `coef2_guard` read 14.8 here and 31.1 at 32 before `x + x` became a product
    // by 2 in `Tx::step_1d_at`; 7.9 to 8.0 at 16, 32 and 64 after.
    coef2_guard_scales: "coef2_guard" at 16;
    normal_mul3_chain_scales: "normal_mul3_chain" at 16;
    // At 128: it read 11.81 at 16 and 8.34 at 128 (load 52), the ratio falling as n grows. No
    // bound on the pieces the product's inverse visits per link is proved (`Tx::back_doubt`);
    // the cost is measured only.
    normal_div_neg2_chain_scales: "normal_div_neg2_chain" at 128;
    // PERF-ref-memo-multi-input: two-input threshold chains, answered by
    // `Tx::affine_threshold_pair` in O(n log n) (Theorem 1 at `threshold_box`). On the memo
    // `alternating_2var` read 13.2 at 16, 16.2 at 32 and 25.2 at 64. `alt2var_m` at 20 puts
    // n ≡ 0 (mod 20) at both sizes; the round-3 cover that the stage replaced declined at
    // n ≡ 18..21 (mod 20).
    alternating_2var_scales: "alternating_2var" at 64;
    alt2var_m_scales: "alt2var_m" at 20;
    // PERF-ref-memo-multi-input part (b): guards on distinct inputs, answered by
    // `Tx::independent_affine` in O(n). On the memo it read 20.9 at 6, 12.1 at 12 and 183 at
    // 24; 7.99 here (instructions 7.99, bytes 8.01, load 46).
    indep_varying_scales: "indep_varying" at 24;
    // PERF-ref-memo-moduli-tables: two-input chains of modular links, answered by
    // `Tx::mod_chain_pair` in O(K n (log n + k)), K = min(M_1, W) classes, no table sized by a
    // modulus. On the memo `alternating_moduli` read 12.1 at 4 and 101 at 8; the cross-review's
    // tables aborted at moduli near 2^40, which `alternating_moduli_big` uses.
    alternating_moduli_scales: "alternating_moduli" at 64;
    alternating_moduli_big_scales: "alternating_moduli_big" at 64;
}

/// PERF-ref-memo-moduli-tables, the scaling over the modulus: `alternating_moduli` at 64 links
/// with moduli `ms` and 8 times `ms`, held to [`scaling::LIMIT`] like a pass at n and 8n.
fn modulus_scales(ms: [i64; 2]) {
    on_big_stack(|| {
        let at = |ms: [i64; 2]| {
            let d = Demand::Bool(true);
            let t = zed_kernel::Term::Prim(
                zed_kernel::Prim::Ne,
                vec![
                    alternating_moduli(64, ms),
                    Term::Lit(zed_kernel::Value::Int(0)),
                ],
            );
            (t, i_and_m(), d)
        };
        let (small, large) = (at(ms), at(ms.map(|m| m * 8)));
        let run = |(t, ds, d): &(Term, Domains, Demand)| {
            std::hint::black_box(preimage(t, ds, d));
        };
        let what = format!("alternating_moduli at 64 links, moduli {ms:?} and 8 times");
        scaling::compare(&what, 1, || run(&small), || run(&large));
    });
}

/// From (7, 64) to (56, 512) the classes `K = min(M_1, W)` grow 8 times (`W` = 2001), so the
/// work grows about 8 times: this holds the cost to linear in the classes.
#[test]
fn mod_chain_modulus_scales() {
    modulus_scales([7, 64]);
}

/// Near `2^37` and `2^59`, 8 times to near `2^40` and `2^62`: the classes stay `W`, so the work
/// should not grow; the cross-review's tables were sized by the modulus.
#[test]
fn mod_chain_big_modulus_scales() {
    modulus_scales([(1 << 37) + 3, (1 << 59) - 55]);
}

/// PROOF-round-down-piece-bound at the sizes the benchmark above times, which need a large
/// stack: the forward image of a node has at most 3 pieces and every label one, as the proof at
/// `Tx::inverse_states` derives for every n;
/// `ref_memo::the_round_down_chain_keeps_three_pieces_and_one_piece_labels` reads every n to 128.
#[test]
fn normal_round_down_keeps_its_pieces_at_large_sizes() {
    on_big_stack(|| {
        for n in [1024, 2048, 4096, 8192] {
            assert_eq!(round_down_most(n), [3, 1], "normal_round_down at {n}");
        }
    });
}

/// COMPLEXITY.md K138 (C) at the 1024 links `normal_min_gap_scales` times, which need a large
/// stack: B_j's tree reaches its bound of [`MIN_GAP_B_NODES`] nodes and no more.
#[test]
fn normal_min_gap_keeps_its_b_nodes_at_1024() {
    on_big_stack(|| {
        assert_eq!(
            min_gap_if_tree_nodes(1024),
            MIN_GAP_B_NODES,
            "normal_min_gap at 1024"
        );
    });
}

/// The work of writing out an answer 8 times larger, the term unchanged: [`output_grid`] at 1024
/// links with 64 and 512 values demanded, `64 n` and `512 n` pieces by the hand count, held to
/// [`scaling::LIMIT`] as a pass of order n in the pieces. An earlier test held `output_grid`'s
/// work at `n` and `8n` with all `n / 2` odd values demanded to the limit times the growth of
/// the answer counted from the code under test (64 times): work quadratic in `n` passed it, and
/// an answer split into more pieces raised its own limit.
#[test]
fn output_grid_work_grows_with_its_answer() {
    on_big_stack(|| {
        let n = 1024;
        let (small, large) = (output_grid(n, 64), output_grid(n, 512));
        let run = |(t, ds, d): &(Term, Domains, Demand)| {
            std::hint::black_box(preimage(t, ds, d));
        };
        scaling::compare(
            "the reference preimage of output_grid at 1024 links, 64 and 512 values demanded",
            1,
            || run(&small),
            || run(&large),
        );
        assert_eq!(answer_pieces(&small), 64 * n);
        assert_eq!(answer_pieces(&large), 512 * n);
    });
}

/// [`scales`] on `nested_moduli_eq_4096` with the constants of n = 6 mod 10 next to the root at
/// every n, an answer of about 760 pieces at both sizes (REF-nested-moduli-state).
///
/// At 64, not 16: the state reaching the chain's input holds a few input pieces per residue
/// for every residue of 4096 only after the first links (3,511 of the 4,096 residues at n =
/// 16), so from 16 to 128 the state itself grows 12.1 times (8,192 to 99,474 label pieces) and
/// any pass that builds it does at least that much more work: 12.07 times the instructions,
/// 2026-11-21. From 64 to 512 the state grows 8.84 times (46,813 to 413,696 label pieces) and
/// the pass 8.12 times (11.47 times before the waiting masks of `Parts1d` in `preimage_ref.rs`).
#[test]
fn nested_moduli_eq_4096_at_6_scales() {
    scales("nested_moduli_eq_4096_at_6", 64);
}
