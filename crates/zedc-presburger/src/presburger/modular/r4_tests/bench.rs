//! The benchmarks of `r4_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//!
//! The graph-coloring benchmarks stay at n = 32, the size they had (1x a few milliseconds),
//! and do not reach the 1 s size the other benchmarks have: their witness is one integer
//! built by `combine_crt_tree` from one prime modulus per vertex, O(M(N) log k) for `k`
//! moduli of `N` bits in all, with `N` about `k log k`, and that grows faster than the limit
//! of 10.5 at 8n allows once the integers are wide. Measured 2026-11-14 (instructions at 8n):
//! 8.4 to 8.9 at n = 32, 8.9 to 10.7 at 256, 11.8 to 14.9 at 4000, 12.3 to 13.2 at 24,000 to
//! 80,000; most of the work is in big-integer multiplication, not in the coloring.
//! The other benchmarks are sized (2026-11-14) so the 1x case takes about 0.3 to 1 s, or less
//! where building the inputs takes most of the piece, and a piece stays under 20 s.

use super::*;

#[test]
fn pncx_pure_bounds_scale() {
    let inputs = scaling::inputs(64_000, |n| pure_constraints(n, false));
    scaling::check_order("pure bounds with separate holes", 64_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

#[test]
fn pncx_pure_residues_scale() {
    let inputs = scaling::inputs(64_000, |n| pure_constraints(n, true));
    scaling::check_order(
        "pure residue constraints with separate holes",
        64_000,
        1,
        |n| {
            assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
        },
    );
}

#[test]
fn pncx_domain_membership_scale() {
    let inputs = scaling::inputs(2_048_000, |n| {
        Domain::from_pieces(
            (0..n)
                .map(|i| (Some(Int::from(3 * i as i64)), Some(Int::from(3 * i as i64))))
                .collect(),
        )
    });
    scaling::check_instructions_only(
        "membership in disjoint bound intervals",
        2_048_000,
        1,
        |n| {
            for i in 0..n {
                let yes = Some(Int::from(3 * i as i64));
                let no = Some(Int::from(3 * i as i64 + 1));
                assert!(inputs[&n].contains_span(&yes, &yes));
                assert!(!inputs[&n].contains_span(&no, &no));
            }
        },
    );
}

#[test]
fn pncx_kept_prefix_scale() {
    let inputs = scaling::inputs(32_000, prefix_formula);
    scaling::check_order("kept conjunction prefixes", 32_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

#[test]
fn pncx_connected_colors_scale() {
    let inputs = scaling::inputs(32, connected_color_system);
    scaling::check_order("color connected triangles by removal order", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_independent_components_scale() {
    let inputs = scaling::inputs(32, color_system);
    scaling::check_order("independent residue components", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        // Keep the measured assertion weak so the old path's slower
        // Undecided result is caught by the cost check itself.
        assert!(!matches!(
            solve_coprime_system(&None, &None, info, allowed.clone(), clauses.clone(), true),
            RegimeOut::Empty
        ));
    });
}

#[test]
fn pncx_lower_witness_scale() {
    let inputs = scaling::inputs(2_048_000, |n| {
        (2..n + 2)
            .map(|m| (Int::from(m), vec![(Int::ONE, Int::from(m - 1))]))
            .collect::<BTreeMap<_, _>>()
    });
    // This routine allocates no bytes on word-sized inputs.
    scaling::check_instructions_only(
        "one candidate from residue lower bounds",
        2_048_000,
        1,
        |n| {
            std::hint::black_box(lower_witness(&Int::from(1000003), &None, &inputs[&n], &[]));
        },
    );
}

#[test]
fn pncx_bound_merge_formula_scale() {
    let inputs = scaling::inputs(30_000, bound_merge_formula);
    scaling::check_order("bound merging in a modular formula", 30_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

#[test]
fn pncx_bound_partition_scale() {
    let inputs = scaling::inputs(1_536_000, bound_partition_input);
    scaling::check_order("partition disjoint global bounds", 1_536_000, 1, |n| {
        let (global, clauses) = &inputs[&n];
        let out = partition_into_regimes(global, clauses);
        assert_eq!(out.len(), 2 * n);
        std::hint::black_box(out);
    });
}
