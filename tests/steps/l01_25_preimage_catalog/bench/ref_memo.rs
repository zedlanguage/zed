//! The scaling half of `ref_memo.rs` (plan item PERF-ref-memo-quadratic): each of the 48
//! families of the item's benchmark, and the one-input shapes of PROOF-preimage-ref-chain-cost,
//! at n and 8n, held to the plan's limit
//! (`scaling::LIMIT`) in instructions and bytes, with no wider limit for any family; each
//! answer grows at most 8 times (`output_grid` demands four values, 4n pieces). The answers
//! of every family at small sizes are checked against the interpreter in `ref_memo.rs`.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage_ref::{Demand, Domains, preimage};

use crate::bench::s22::on_big_stack;
use crate::ref_memo::{
    MIN_GAP_B_NODES, answer_pieces, family, min_gap_if_tree_nodes, output_grid, round_down_most,
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
