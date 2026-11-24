//! The benchmarks of `r6_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness tests that keep a small instance of
//! what each checks besides the ratio are `the_benchmark_inputs_have_their_answers_at_small_sizes`,
//! and for the graph cores `pncx_bipartite_core`, `pncx_prism_models` and `pncx_wheel_models`.
//!
//! The graph-coloring benchmarks scale the coloring without the CRT that joins its witness,
//! and measure the whole question against its coloring and its CRT (`coloring_scales`; the
//! reason and the measurements are in `r4_tests::bench`, PNCX-coloring-crt-scale).
//! The other benchmarks are sized (2026-11-14) so the 1x case takes about 0.3 to 1 s, or less
//! where building the inputs takes most of the piece, and a piece stays under 20 s.
//! The two matching benchmarks went from n = 640,000 to 160,000 (b22-presburger3, 2026-11-22):
//! at 640,000 each piece took 49 to 52 s at load 49, most of it building and dropping 5.12
//! million clauses at 8n; at 160,000 they take 11 to 15 s at the same load, 1x 0.3 G
//! instructions, ratio 8.63 and 8.65 (8.86 and 8.88 at 640,000).

use super::super::r4_tests::{COLORS, Coloring, against_its_crt};
use super::*;

/// The coloring of a core family scales at [`COLORS`] and 8 times it without the CRT that
/// joins its witness, and the whole question costs a bounded multiple of its coloring and that
/// CRT ([`against_its_crt`], PNCX-coloring-crt-scale).
fn coloring_scales(what: &str, make: fn(usize) -> Coloring) {
    let n = COLORS;
    let inputs = scaling::inputs(n, make);
    scaling::check_order(what, n, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_choices(info, allowed, clauses).is_some());
    });
    let system = &inputs[&n];
    let (info, allowed, clauses) = system;
    against_its_crt(what, system, || {
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_bipartite_core_scale() {
    coloring_scales("color a bipartite three-core", bipartite_core);
}

#[test]
fn pncx_bound_matching_scale() {
    let inputs = scaling::inputs(160_000, |n| {
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
    scaling::check_order("three-pair implication by matching", 160_000, 1, |n| {
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
    coloring_scales("Brooks coloring on odd prism cores", prism_core);
}

#[test]
fn pncx_wheel_core_scale() {
    coloring_scales("a universal vertex and a bipartite remainder", wheel_core);
}

#[test]
fn pncx_empty_pair_bound_scale() {
    let inputs = scaling::inputs(160_000, |n| {
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
    scaling::check_order("empty shared bounds tested by matching", 160_000, 1, |n| {
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

/// `x - m_i q_i = 1` over the first `n` primes above `2^47`, each `q_i` private: the private
/// quotients over distinct primes past `FACTOR_BITS` (44), where `coprime_factorization` used
/// to take zed-kernel's `by_halves` (R2 Gemini seat, `ADV_WIDE48_UNIT`: 14.11 then 19.78 times
/// the instructions at 8 times the rows from 64). From 256 moduli that are all prime words the
/// kernel's prime-word path answers (PERF-private-quotient-wide-moduli, 2026-11-21, load 40:
/// 61,348,567 and 516,268,910 instructions at 4096 and 32,768 rows, 8.42 times, and 8.0 times
/// the bytes; with the path turned off, 182,982,981 and 2,203,550,057, 12.04 times, a
/// failure).
#[test]
fn pncx_private_quotients_wide_primes_scale() {
    let inputs = scaling::inputs(4096, |n| {
        let x = Lin::atom(Atom::Sym("x".into()));
        let mut parts = Vec::with_capacity(n);
        let mut p = (1u64 << 47) + 1;
        while parts.len() < n {
            if zed_numtheory::is_prime(p) {
                let q = Lin::atom(Atom::Aux(parts.len() as u32));
                let m = Int::from(i128::from(p));
                parts.push(Formula::Con(Con::eq(
                    &x.minus(&q.times(m)),
                    &Lin::constant(1),
                )));
            }
            p += 2;
        }
        Formula::and(parts)
    });
    scaling::check_order(
        "private quotients over distinct wide primes",
        4096,
        1,
        |n| {
            assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
        },
    );
}

/// Moved here from `r6_tests` (BENCH-meters-outside-bench); its answers at small sizes are
/// `pncx_wide_affine_alias_is_satisfiable_at_small_sizes`.
#[test]
fn pncx_wide_affine_alias_scale() {
    let inputs = scaling::inputs(128, wide_alias_chain);
    scaling::check_order("affine aliases with one wide written offset", 128, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

/// The adversarial middle-wide-edge-first unbounded alternating-sign chain, from part 3 of
/// `r6_tests::pncx_wide_affine_alias_adversarial_shapes`, which checks it at small sizes
/// (BENCH-meters-outside-bench).
#[test]
fn pncx_wide_affine_alias_adversarial_scale() {
    let inputs = scaling::inputs(128, wide_middle_first_chain);
    scaling::check_order("middle wide offset placed first", 128, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}
