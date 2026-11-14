//! The benchmarks of `r6_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness tests that keep a small instance of
//! what each checks besides the ratio are `the_benchmark_inputs_have_their_answers_at_small_sizes`, and
//! for the graph cores `pncx_bipartite_core`, `pncx_prism_models` and `pncx_wheel_models`.
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
fn pncx_bipartite_core_scale() {
    let inputs = scaling::inputs(32, bipartite_core);
    scaling::check_order("color a bipartite three-core", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_bound_matching_scale() {
    let inputs = scaling::inputs(640_000, |n| {
        (0..n)
            .map(|i| FlatClause {
                bounds: Domain::ge(Int::from(100)),
                mods: BTreeMap::from([
                    (
                        Int::from(100_003),
                        vec![(Int::from(i % 2), Int::from(i % 2))],
                    ),
                    (Int::from(100_019), vec![(Int::from(i), Int::from(i))]),
                ]),
            })
            .collect::<Vec<_>>()
    });
    scaling::check_order("three-pair implication by matching", 640_000, 1, |n| {
        assert_eq!(forced_pair_bounds(&inputs[&n]), Domain::all());
    });
}

/// At 160 million input bits (1x 0.3 s). Between 8 and 20 million bits the bytes at 8n are 11.1
/// to 13.0 times those at n, since the 8n run passes the size where multiplication changes
/// method and the n run does not; at 4 million and at 160 million both runs sit on one side,
/// and the bytes are under 10.5 times (9.0 at 160 million, measured 2026-11-14).
#[test]
fn pncx_power_propagation_scale() {
    let inputs = scaling::inputs(160_000_000, power_inputs);
    scaling::check_order(
        "propagate the highest fixed residue once",
        160_000_000,
        1,
        |n| {
            let (sets, max) = &inputs[&n];
            let ConsolidateOut::Ok(info, _) = consolidate_prime_powers(sets, max) else {
                panic!("fixed residue");
            };
            assert_eq!(info.u, max - &Int::ONE);
        },
    );
}

#[test]
fn pncx_prism_core_scale() {
    let inputs = scaling::inputs(32, prism_core);
    scaling::check_order("Brooks coloring on odd prism cores", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_wheel_core_scale() {
    let inputs = scaling::inputs(32, wheel_core);
    scaling::check_order("a universal vertex and a bipartite remainder", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_empty_pair_bound_scale() {
    let inputs = scaling::inputs(640_000, |n| {
        (0..n)
            .map(|i| FlatClause {
                bounds: Domain::empty(),
                mods: BTreeMap::from([
                    (
                        Int::from(100003),
                        vec![(Int::from(i % 2), Int::from(i % 2))],
                    ),
                    (Int::from(100019), vec![(Int::from(i), Int::from(i))]),
                ]),
            })
            .collect::<Vec<_>>()
    });
    scaling::check_order("empty shared bounds tested by matching", 640_000, 1, |n| {
        assert_eq!(forced_pair_bounds(&inputs[&n]), Domain::all());
    });
}

#[test]
fn pncx_alias_chain_axis() {
    let mut meter = scaling::Meter::new();
    for n in [256, 512, 1024, 2048] {
        let (uf, atoms, f) = alias_chain(n);
        assert_eq!(uf.get(&atoms[0]), (atoms[n].clone(), 1, Int::from(n)));
        let work = meter.work(|| {
            for a in &atoms {
                std::hint::black_box(uf.get(a));
            }
        });
        let printed = f.to_string().len();
        let mut witness = Model::new();
        for (i, a) in atoms.iter().enumerate() {
            witness.insert(a.clone(), Int::from(2i64 - i as i64));
        }
        witness.insert(Atom::Aux(0), Int::ZERO);
        witness.insert(Atom::Aux(1), Int::from(2));
        assert!(f.holds(&witness));
        println!(
            "ALIAS_GET n={n} input_bytes={printed} work={} bytes={}",
            work.units, work.bytes
        );
        let mut result = None;
        let work = meter.work(|| result = solve_modular(&f, false));
        assert!(matches!(result, Some(Some(_))));
        println!(
            "ALIAS_FORMULA n={n} input_bytes={printed} work={} bytes={}",
            work.units, work.bytes
        );
        let mut d = None;
        let work = meter.work(|| d = Some(crate::presburger::decide(&f)));
        assert_eq!(d, Some(Ok(true)));
        println!(
            "ALIAS_DECIDE n={n} input_bytes={printed} work={} bytes={}",
            work.units, work.bytes
        );
    }
}

#[test]
fn pncx_affine_alias_chain_scale() {
    let inputs = scaling::inputs(40_000, |n| alias_chain(n).2);
    scaling::check_order("affine aliases before one remainder", 40_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}
