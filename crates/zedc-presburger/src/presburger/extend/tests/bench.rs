//! The benchmarks of `extend::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness tests that keep a small instance of
//! what each checks besides the ratio are `the_benchmark_inputs_have_their_answers_at_small_sizes`
//! and `a_merge_of_fewer_than_two_pieces_returns_them`. The `_measurement` tests check no
//! ratio; they print the work at two sizes for the record.
//! Sizes are set (2026-11-14) so a piece stays under 20 s, with the 1x case at about 0.3 to 1 s;
//! where building the inputs takes most of the piece (the unbalanced unions, the unequal
//! frontiers, the functional keys and the wide questions), the 1x case is 0.05 to 0.15 s.

use super::*;

#[test]
fn r5_frontier_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for (name, depth, shared) in [
        ("leaves", 1, false),
        ("private-chains", 4, false),
        ("shared-prefix", 20, true),
    ] {
        for n in [100, 800] {
            let (mut sums, defs, reads) = r5_frontier_fixture(n, depth, shared);
            let def = |n: u32| defs[n as usize].clone();
            let own = BTreeSet::new();
            // Warm only the requested summaries, never the decomposition. Both cold and
            // warm local calls are measured; the cost counter concerns one warm call.
            let mut cold_calls = 0;
            let cold = meter.work(|| cold_calls = local_when_warmed(&mut sums, &reads, &def));
            FRONTIER_VISITS.with(|v| v.set(0));
            let work = meter.work(|| {
                assert!(matches!(
                    sums.local(&reads, &own, None, &[], &def),
                    Local::Ready(_, _)
                ));
            });
            let visits = FRONTIER_VISITS.with(|v| v.get());
            eprintln!(
                "R5 local {name} n={n} depth={depth} cold_calls={cold_calls} cold_instr={} warm_instr={} visits={visits}",
                cold.units, work.units
            );
        }
    }
}

#[test]
fn r5_parabola_rests_measurement() {
    let mut meter = crate::scaling::Meter::new();
    let sizes: Vec<i64> = std::env::var("R5_PARABOLA_SIZES")
        .unwrap_or("8,64".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    for n in sizes {
        let ps = parabola_rays(n);
        REST_ROW_VISITS.with(|v| v.set(0));
        let mut out = Vec::new();
        let w = meter.work(|| out = merge_pieces(ps));
        let visits = REST_ROW_VISITS.with(|v| v.get());
        assert_eq!(out.len(), 1);
        eprintln!(
            "R5 parabola n={n} instr={} rows={} rest_visits={visits}",
            w.units,
            out[0].len()
        );
        // All tangents are necessary in the old representation. Every integer vertex
        // must retain its original height; a row deleted blindly would admit i²-1.
        parabola_rays_kept(&out, n);
    }
}

#[test]
fn r5_folding_chain_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for n in [100u32, 800] {
        let rows = folding_chain_rows(n);
        FOLD_ROW_VISITS.with(|v| v.set(0));
        let mut out = Vec::new();
        let w = meter.work(|| out = fold_free_unit_pairs(rows, &HashSet::new()));
        let visits = FOLD_ROW_VISITS.with(|v| v.get());
        eprintln!(
            "R5 folding-chain n={n} instr={} visits={visits} rows={}",
            w.units,
            out.len()
        );
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], con(&[(0, 1)], 0, Rel::Ge));
    }
}

#[test]
fn r5_shared_prefix_symbol_unions_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for n in [100u32, 800] {
        let defs = r5_diamond_defs(n);
        let def = |n: u32| defs[n as usize].clone();
        let root = defs.last().unwrap().clone();
        let id = Id::any(&root);
        let mut sums = Summaries::default();
        let w = meter.work(|| sums.syms(root, &def));
        assert_eq!(sums.syms[&id].len(), 2 * n as usize + 1);
        assert_eq!(sums.cone[&id].len(), 3 * n as usize);
        eprintln!(
            "R5 diamond n={n} instr={} bytes={} symbols={} cone={}",
            w.units,
            w.bytes,
            sums.syms[&id].len(),
            sums.cone[&id].len()
        );
    }
}

#[test]
fn r5_diamond_unions_scale() {
    let inputs = crate::scaling::inputs(10_000, |n| r5_diamond_defs(n as u32));
    crate::scaling::check_order(
        "symbol/cone unions through overlapping diamonds",
        10_000,
        1,
        |n| {
            let defs = &inputs[&n];
            let def = |n: u32| defs[n as usize].clone();
            let root = defs.last().unwrap().clone();
            let id = Id::any(&root);
            let mut sums = Summaries::default();
            sums.syms(root, &def);
            assert_eq!(sums.syms[&id].len(), 2 * n + 1);
            assert_eq!(sums.cone[&id].len(), 3 * n);
        },
    );
}

#[test]
fn r5_independent_leaf_frontiers_scale() {
    let inputs = crate::scaling::inputs(100_000, |n| r5_frontier_fixture(n as u32, 1, false));
    crate::scaling::check_order("wide independent leaf frontier", 100_000, 1, |n| {
        let (sums, defs, reads) = &inputs[&n];
        let def = |n: u32| defs[n as usize].clone();
        assert!(matches!(
            sums.local(reads, &BTreeSet::new(), None, &[], &def),
            Local::Ready(_, _)
        ));
    });
}

#[test]
fn r5_convex_vertical_rays_scale() {
    let inputs = crate::scaling::inputs(96_000, |n| parabola_rays(n as i64));
    crate::scaling::check_order(
        "batch join of convex integer vertical rays",
        96_000,
        1,
        |n| {
            let out = merge_pieces(inputs[&n].clone());
            assert_eq!(out.len(), 1);
        },
    );
}

#[test]
fn r5_actual_wide_questions_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for (name, depth, prefix) in [
        ("leaves", 1, 0),
        ("private", 4, 0),
        ("shared-prefix", 4, 200),
    ] {
        for n in [100, 800] {
            let (defs, q) = r5_actual_frontier_defs(n, depth, prefix);
            let def = |n: u32| defs[n as usize].clone();
            let mut ext = Extending::new();
            let mut answer = None;
            let w = meter.work(|| answer = Some(ext.defined(&q, &def)));
            assert_eq!(
                answer,
                Some(Answers {
                    holds: Ok(true),
                    fails: Ok(true)
                })
            );
            eprintln!(
                "R5 actual-frontier {name} width={n} depth={depth} prefix={prefix} nodes={} instr={} bytes={}",
                defs.len(),
                w.units,
                w.bytes
            );
        }
    }
}

#[test]
fn r5_actual_wide_questions_scale() {
    let inputs = crate::scaling::inputs(2000, |n| r5_actual_frontier_defs(n as u32, 4, 0));
    crate::scaling::check_order(
        "cold questions over independent four-link chains",
        2000,
        1,
        |n| {
            let (defs, q) = &inputs[&n];
            let def = |n: u32| defs[n as usize].clone();
            assert_eq!(
                Extending::new().defined(q, &def),
                Answers {
                    holds: Ok(true),
                    fails: Ok(true)
                }
            );
        },
    );
}

#[test]
fn r5_second_adversaries_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for n in [100, 800] {
        let defs = r5_unbalanced_union_defs(n);
        let def = |n: u32| defs[n as usize].clone();
        let mut sums = Summaries::default();
        let work = meter.work(|| sums.syms(defs.last().unwrap().clone(), &def));
        let id = Id::any(defs.last().unwrap());
        assert_eq!(sums.syms[&id].len(), 2 * n as usize);
        eprintln!(
            "R5 unbalanced-union n={n} nodes={} instr={} bytes={}",
            defs.len(),
            work.units,
            work.bytes
        );
        let (sums, defs, reads) = r5_unequal_shared_frontier(n);
        let def = |n: u32| defs[n as usize].clone();
        FRONTIER_VISITS.with(|v| v.set(0));
        let work = meter.work(|| {
            assert!(matches!(
                sums.local(&reads, &BTreeSet::new(), None, &[], &def),
                Local::Ready(_, _)
            ))
        });
        eprintln!(
            "R5 unequal-shared-frontier n={n} nodes={} instr={} bytes={} visits={}",
            defs.len(),
            work.units,
            work.bytes,
            FRONTIER_VISITS.with(|v| v.get())
        );
    }
}

#[test]
fn r5_unbalanced_unions_scale() {
    let inputs = crate::scaling::inputs(3000, |n| r5_unbalanced_union_defs(n as u32));
    crate::scaling::check_order(
        "one large persistent set beside independent singleton inputs",
        3000,
        1,
        |n| {
            let defs = &inputs[&n];
            let def = |n: u32| defs[n as usize].clone();
            let mut sums = Summaries::default();
            sums.syms(defs.last().unwrap().clone(), &def);
        },
    );
}

#[test]
fn r5_unequal_shared_frontiers_scale() {
    let inputs = crate::scaling::inputs(6000, |n| r5_unequal_shared_frontier(n as u32));
    crate::scaling::check_order(
        "unequal-height frontiers above a shared prefix",
        6000,
        1,
        |n| {
            let (sums, defs, reads) = &inputs[&n];
            let def = |n: u32| defs[n as usize].clone();
            assert!(matches!(
                sums.local(reads, &BTreeSet::new(), None, &[], &def),
                Local::Ready(_, _)
            ));
        },
    );
}

#[test]
fn r5_a_merge_with_no_pair_does_no_quadratic_index_work() {
    let inputs = crate::scaling::inputs(200_000, singleton_union);
    crate::scaling::check_order(
        "a singleton union with many distinct row forms",
        200_000,
        1,
        |n| {
            let before = inputs[&n].clone();
            let expected: Vec<_> = before.iter().cloned().collect();
            assert_eq!(merge_pieces(before), expected);
        },
    );
}

#[test]
fn convex_runs_with_a_concave_last_slice_scale() {
    let inputs = crate::scaling::inputs(96_000, r6_almost_convex_rays);
    crate::scaling::check_order("convex runs with a concave last slice", 96_000, 1, |n| {
        let out = merge_pieces(inputs[&n].clone());
        almost_convex_rays_kept(&out, n as i64);
    });
}

#[test]
fn independent_twin_unions_measurement() {
    let mut meter = crate::scaling::Meter::new();
    let sizes: Vec<usize> = std::env::var("LMD_SIZES")
        .unwrap_or("100,800".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    for n in sizes {
        let defs = twin_union_defs(n);
        let def = |n: u32| defs[n as usize].clone();
        let mut sums = Summaries::default();
        let w = meter.work(|| {
            for i in 0..n {
                sums.syms(defs[3 * i + 2].clone(), &def);
            }
        });
        let id = Id::any(defs.last().unwrap());
        assert_eq!(sums.syms[&id].len(), n + 1);
        assert_eq!(sums.cone[&id].len(), 2 * n + 1);
        eprintln!("twin unions n={n} instr={} bytes={}", w.units, w.bytes);
    }
}

#[test]
fn functional_leaf_and_product_key_buckets_scale() {
    let inputs = crate::scaling::inputs(5000, functional_leaf_key_fixture);
    crate::scaling::check_order("functional leaf and product key buckets", 5000, 1, |n| {
        let (sums, defs, rs) = &inputs[&n];
        let def = |n: u32| defs[n as usize].clone();
        assert!(matches!(
            sums.local(rs, &BTreeSet::new(), None, &[], &def),
            Local::Ready(_, _)
        ));
    });
}

#[test]
fn functional_key_buckets_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for n in [100usize, 800] {
        let (sums, defs, rs) = functional_leaf_key_fixture(n);
        let def = |n: u32| defs[n as usize].clone();
        let w = meter.work(|| {
            assert!(matches!(
                sums.local(&rs, &BTreeSet::new(), None, &[], &def),
                Local::Ready(_, _)
            ))
        });
        eprintln!("functional keys n={n} instr={} bytes={}", w.units, w.bytes);
    }
}

#[test]
fn bounded_row_totals_scale() {
    let inputs = crate::scaling::inputs(750_000, r6_bounded_row);
    crate::scaling::check_order("incremental totals of one bounded row", 750_000, 1, |n| {
        let (row, mut bounds) = inputs[&n].clone();
        assert!(tighten_bounded_row(&row, &mut bounds));
    });
}

#[test]
fn bounded_row_totals_measurement() {
    let mut meter = crate::scaling::Meter::new();
    for n in [100, 800] {
        let (row, bounds) = r6_bounded_row(n);
        for old in [true, false] {
            let mut b = bounds.clone();
            let counted = meter.work(|| {
                assert!(if old {
                    tighten_bounded_row_slow(&row, &mut b)
                } else {
                    tighten_bounded_row(&row, &mut b)
                });
            });
            eprintln!(
                "bounded-row n={n} old={old} instr={} bytes={}",
                counted.units, counted.bytes
            );
        }
    }
}

#[test]
fn product_only_input_metadata_keeps_every_factor_and_product_in_linear_work() {
    let inputs = crate::scaling::inputs(20_000, product_input_defs);
    crate::scaling::check_order("metadata of fresh product inputs", 20_000, 1, |n| {
        let defs = &inputs[&n];
        let def = |j: u32| defs[j as usize].clone();
        let root = defs[n].clone();
        let id = Id::any(&root);
        let mut sums = Summaries::default();
        sums.syms(root, &def);
        assert_eq!(sums.syms[&id].len(), 2 * n + 1);
        assert_eq!(sums.cone[&id].len(), n + 1);
    });
}
