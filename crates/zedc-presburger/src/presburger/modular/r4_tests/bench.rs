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

#[test]
fn pncx_common_factor_scale() {
    let inputs = scaling::inputs(512, shared_moduli);
    scaling::check_order("common factor with coprime cofactors", 512, 1, |n| {
        std::hint::black_box(coprime_factorization(&inputs[&n]));
    });
}

/// The first n odd primes: no shared factor, and every modulus is its own base. On the table
/// side of `shares_a_factor` at both sizes (asserted on the inputs).
#[test]
fn pncx_coprime_dense_scale() {
    let inputs = scaling::inputs(32_000, |n| {
        let primes = odd_primes(n);
        assert!(dense_values(&primes.iter().cloned().collect::<Vec<_>>()).is_some());
        primes
    });
    scaling::check_order(
        "coprime moduli from a table of least prime factors",
        32_000,
        1,
        |n| {
            let facs = coprime_factorization(&inputs[&n]).expect("factored");
            assert_eq!(facs.len(), n);
        },
    );
}

/// Both methods of `shares_a_factor` on both sides of the table method's condition (author
/// decision A96): k values `1 + i * stride`, the largest about `k * stride`, so the condition
/// (largest value at most the bits of all the values) holds only for the small strides.
/// Prints the instructions and bytes of each method and holds their answers equal. The switch
/// is set by the proved bound, not by these numbers; they show the table is also the cheaper
/// method on its own side, and for how far beyond it. Run again for each target platform and
/// after a change to code generation.
#[test]
fn pncx_shared_factor_crossover_axis() {
    let mut meter = scaling::Meter::new();
    for k in [16u32, 128, 1024, 4096] {
        for stride in [1u32, 4, 16, 64, 256, 1024] {
            let small: Vec<u32> = (0..k).map(|i| 1 + i * stride).collect();
            let vals: Vec<Int> = small.iter().map(|&v| Int::from(i64::from(v))).collect();
            let top = 1 + (k - 1) * stride;
            let bits: u64 = vals.iter().map(Int::bits).sum();
            let (mut by_table, mut by_tree) = (Vec::new(), Vec::new());
            let table = meter.work(|| by_table = shares_a_factor_by_table(&small, top));
            let tree = meter.work(|| by_tree = shares_a_factor_by_tree(&vals));
            assert_eq!(by_table, by_tree);
            println!(
                "bench SHARED_FACTOR k={k} stride={stride} largest={top} bits={bits} table_side={} table={}/{} tree={}/{}",
                dense_values(&vals).is_some(),
                table.units,
                table.bytes,
                tree.units,
                tree.bytes
            );
        }
    }
}
