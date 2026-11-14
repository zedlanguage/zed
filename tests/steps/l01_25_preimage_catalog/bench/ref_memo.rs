//! The scaling half of `ref_memo.rs` (plan item PERF-ref-memo-quadratic): each of the 48
//! families of the item's benchmark at n and 8n, held to the plan's limit
//! (`scaling::LIMIT`) in instructions and bytes, with no wider limit for any family; each
//! answer grows at most 8 times (`output_grid` demands four values, 4n pieces). The answers
//! of every family at small sizes are checked against the interpreter in `ref_memo.rs`.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage_ref::{Demand, Domains, preimage};

use crate::ref_memo::{answer_pieces, family, output_grid};
use crate::s22::on_big_stack;

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
    normal_min_gap_scales: "normal_min_gap" at 16;
    normal_mixed_moduli_scales: "normal_mixed_moduli" at 16;
    normal_mod_chain_scales: "normal_mod_chain" at 16;
    normal_mul_base_scales: "normal_mul_base" at 16;
    normal_mul_chain_scales: "normal_mul_chain" at 16;
    normal_named_scales: "normal_named" at 16;
    normal_named_modguard_scales: "normal_named_modguard" at 16;
    normal_named_reflection_scales: "normal_named_reflection" at 16;
    normal_rel_guard_scales: "normal_rel_guard" at 16;
    normal_round_down_scales: "normal_round_down" at 16;
    normal_round_trip_scales: "normal_round_trip" at 16;
    // Four values demanded: 4n pieces. At 8 the answer-free work was 84% of the run.
    output_grid_scales: "output_grid" at 64;
    pathological_2var_scales: "pathological_2var" at 16;
    pathological_abs_scales: "pathological_abs" at 16;
    pow2_small_scales: "pow2_small" at 8;
    pow2_wide_scales: "pow2_wide" at 64;
    random_chains_scales: "random_chains" at 64;
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
