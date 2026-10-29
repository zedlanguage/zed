//! Laws 1–10 of the catalog: the reindex, discard and fold equations, the join and packing
//! rules, the fold permissions, scan, and rank.

use zed_kernel::term::build::{app, if_, lit, prim};
use zed_kernel::{Family, KernelError, Pattern, Prim, Term, Value, eval};
use zed_tests::check::{holds, property, property_refuted, refuted};
use zed_tests::instances::{Rng, bmc_floats, partial_maps, shortlex};
use zed_tests::kernel::*;

use super::{IntMap, family, int_maps, ints, seq};

fn plus() -> Term {
    Term::PrimFn(Prim::Add)
}

/// The two-argument function `(p, v) -> body(p, v)` a reindex or discard takes.
fn kv(body: impl FnOnce(Term, Term) -> Term) -> Term {
    func(|[p, v]| body(p, v))
}

/// Applies a two-argument function to a key and a value.
fn call(f: &Term, p: Term, v: Term) -> Term {
    app(f.clone(), vec![p, v])
}

// Law 1: composed reindexes.

#[test]
fn law_01_composed_reindex_reads_the_value_the_first_stage_produced() {
    // Move each account to a new id, triple its balance, then file it under its new balance.
    let kg = kv(|p, _| path(vec![add(key(p, 0), lit(10))]));
    let vg = kv(|_, v| mul(v, lit(3)));
    let kf = kv(|p, v| path(vec![v, key(p, 0)]));
    let vf = kv(|_, v| add(v, lit(1)));
    let two_stage = |m: &IntMap| {
        reindex(
            reindex(ints(m), kg.clone(), vg.clone()),
            kf.clone(),
            vf.clone(),
        )
    };
    let fused_with = |first_value: bool| {
        let (kg2, vg2) = (kg.clone(), vg.clone());
        let (kg, vg, kf, vf) = (kg.clone(), vg.clone(), kf.clone(), vf.clone());
        let k = kv(move |p, v| {
            let v1 = if first_value {
                call(&vg, p.clone(), v.clone())
            } else {
                v.clone()
            };
            call(&kf, call(&kg, p, v), v1)
        });
        let w = kv(|p, v| call(&vf, call(&kg2, p.clone(), v.clone()), call(&vg2, p, v)));
        (k, w)
    };
    let (k, w) = fused_with(true);
    let n = holds(int_maps(1), |m| {
        (two_stage(m), reindex(ints(m), k.clone(), w.clone()))
    });
    assert!(n >= 1_800);
    // The counterexample: the fused key map reads the value from before the first stage.
    let (k, w) = fused_with(false);
    let (m, _, _) = refuted(int_maps(1), |m| {
        (two_stage(m), reindex(ints(m), k.clone(), w.clone()))
    });
    assert!(m.iter().any(|&(_, v)| v != 0));
}

#[test]
fn law_01_identity_reindex_is_the_identity_on_levels_that_are_not_empty() {
    let id_k = kv(|p, _| p);
    let id_v = kv(|_, v| v);
    let n = holds(int_maps(2), |m| {
        (reindex(ints(m), id_k.clone(), id_v.clone()), ints(m))
    });
    assert!(n >= 1_800);
    // The nonempty-level condition has no counterexample among kernel values: a key over
    // an empty level has no keypath, so a value never holds one (sec:values_morphisms). It
    // constrains a guaranteed domain, which may claim a key whose level turns out empty;
    // the `card` facts that discharge it are checked at steps L1.24 and L3.6.
    let warehouses = |east: bool| {
        let mut rows = vec![(
            Value::str("west"),
            Value::Family(Family::of([("bolts", 40i64)])),
        )];
        if east {
            rows.push((Value::str("east"), Value::Family(Family::new())));
        }
        eval(&family(rows)).unwrap()
    };
    assert_eq!(warehouses(true), warehouses(false));
}

// Law 2: a discard moves below a reindex as the composed predicate.

#[test]
fn law_02_filter_after_reindex_moves_below_it() {
    // Negate each key and square each value, then keep the entries whose new key is below
    // the new value.
    let kf = kv(|p, _| path(vec![sub(lit(0), key(p, 0))]));
    let vf = kv(|_, v| mul(v.clone(), v));
    let sel = kv(|p, e| lt(key(p, 0), e));
    let lhs = |m: &IntMap| discard(reindex(ints(m), kf.clone(), vf.clone()), sel.clone());
    let pushed =
        |composed: Term, m: &IntMap| reindex(discard(ints(m), composed), kf.clone(), vf.clone());
    let composed = kv(|p, v| call(&sel, call(&kf, p.clone(), v.clone()), call(&vf, p, v)));
    let n = holds(int_maps(3), |m| (lhs(m), pushed(composed.clone(), m)));
    assert!(n >= 1_800);
    // Composing with the key map only, so the predicate reads the old value, is wrong.
    let key_only = kv(|p, v| call(&sel, call(&kf, p.clone(), v.clone()), v));
    let _ = refuted(int_maps(3), |m| (lhs(m), pushed(key_only.clone(), m)));
}

#[test]
fn law_02_right_to_left_needs_the_reindex_collision_free_on_all_of_f() {
    // File readings under their value: two equal readings collide, unless the filter that
    // was pushed below drops both.
    let kf = kv(|_, v| path(vec![v]));
    let vf = kv(|_, v| v);
    let sel = kv(|_, e| not(eq(e, lit(1))));
    let composed = kv(|p, v| call(&sel, call(&kf, p.clone(), v.clone()), call(&vf, p, v)));
    let (m, a, b) = refuted(int_maps(4), |m| {
        (
            discard(reindex(ints(m), kf.clone(), vf.clone()), sel.clone()),
            reindex(discard(ints(m), composed.clone()), kf.clone(), vf.clone()),
        )
    });
    assert!(matches!(a, Err(KernelError::Collision { .. })) && b.is_ok());
    assert_eq!(m.iter().filter(|&&(_, v)| v == 1).count(), 2);
}

// Law 3: a fold of a map is the fused fold.

#[test]
fn law_03_fold_of_map_is_the_fused_fold_on_integers() {
    let sides = |m: &IntMap| {
        let f = |v: Term| add(mul(v.clone(), v), lit(1));
        (
            fold(map(ints(m), f), plus(), Some(lit(0))),
            fold(
                fam_with(ints(m), |k| f(get(ints(m), k))),
                plus(),
                Some(lit(0)),
            ),
        )
    };
    assert!(holds(int_maps(5), sides) >= 1_800);
}

#[test]
fn law_03_fold_of_map_is_the_fused_fold_on_floats() {
    // A float `+` fold is the exact sum rounded once on both sides.
    let floats: Vec<Vec<Value>> = shortlex(&bmc_floats(), 3);
    let shift = |v: Term| add(v, lit(Value::float(0.1)));
    let n = holds(floats, |xs| {
        (
            fold(map(seq(xs), shift), plus(), None),
            fold(fam_with(seq(xs), |k| shift(get(seq(xs), k))), plus(), None),
        )
    });
    assert_eq!(n, 1 + 9 + 81 + 729);
}

// Law 4: a fold of a group is reduce-by-key.

/// Reduce-by-key written directly: for each class `j`, the fold of the entries `f` sends to
/// `j`.
fn reduce_by_key(m: Term, f: &dyn Fn(Term) -> Term, op: Term) -> Term {
    let classes = keyset(group_by(m.clone(), f));
    fam_with(classes, |j| {
        fold(discard_with(m, |_, e| eq(f(e), j)), op, None)
    })
}

#[test]
fn law_04_fold_of_group_is_reduce_by_key() {
    let by_residue = |v: Term| modulo(v, lit(3));
    for op in [plus(), Term::PrimFn(Prim::Min), Term::PrimFn(Prim::Sub)] {
        let n = holds(int_maps(6), |m| {
            (
                fold_at(group_by(ints(m), by_residue), 2, op.clone(), None),
                reduce_by_key(ints(m), &by_residue, op.clone()),
            )
        });
        assert!(n >= 1_800);
    }
    // `-` holds too: both sides fold each class in key order. The Boom-row condition is for
    // the implementations that do not, such as a fold split across workers (law 8).
}

// Law 5: the entrywise forms distribute over a disjoint union.

/// Every split of the maps over the keys `0..3` into two domain-disjoint parts.
fn splits() -> Vec<(IntMap, IntMap)> {
    let mut out = Vec::new();
    for m in partial_maps(&[0, 1, 2], &[-2, -1, 0, 1, 2]) {
        for mask in 0..(1u32 << m.len()) {
            let (a, b): (Vec<_>, Vec<_>) = m
                .iter()
                .enumerate()
                .partition(|(i, _)| mask & (1 << i) != 0);
            out.push((
                a.into_iter().map(|(_, e)| *e).collect(),
                b.into_iter().map(|(_, e)| *e).collect(),
            ));
        }
    }
    out
}

#[test]
fn law_05_group_map_and_filter_distribute_over_disjoint_union() {
    let du = |a: &IntMap, b: &IntMap| disjoint_union(ints(a), ints(b), 1);
    let parity = |v: Term| modulo(v, lit(2));
    let n = holds(splits(), |(a, b)| {
        (
            group_by(du(a, b), parity),
            disjoint_union(group_by(ints(a), parity), group_by(ints(b), parity), 2),
        )
    });
    // Each map over three keys splits in 2^|m| ways: (1 + 5 * 2)^3 instances.
    assert_eq!(n, 1_331);
    let tripled = |v: Term| mul(v, lit(3));
    holds(splits(), |(a, b)| {
        (
            map(du(a, b), tripled),
            disjoint_union(map(ints(a), tripled), map(ints(b), tripled), 1),
        )
    });
    let positive = |_: Term, e: Term| lt(lit(0), e);
    holds(splits(), |(a, b)| {
        (
            discard_with(du(a, b), positive),
            disjoint_union(
                discard_with(ints(a), positive),
                discard_with(ints(b), positive),
                1,
            ),
        )
    });
    // A key map that collides across `a` and `b` is rejected on both sides.
    let by_value = kv(|_, v| path(vec![v]));
    let id_v = kv(|_, v| v);
    let collide = |(a, b): &(IntMap, IntMap)| {
        (
            reindex(du(a, b), by_value.clone(), id_v.clone()),
            disjoint_union(
                reindex(ints(a), by_value.clone(), id_v.clone()),
                reindex(ints(b), by_value.clone(), id_v.clone()),
                1,
            ),
        )
    };
    let pair = (vec![(0, 5)], vec![(1, 5)]);
    assert!(matches!(
        eval(&collide(&pair).0),
        Err(KernelError::Collision { .. })
    ));
    holds([pair], collide);
}

#[test]
fn law_05_a_filter_that_reads_rank_is_not_linear() {
    // `take(1)`: keep the entry with the least key, which reads the entry's rank in its
    // family, so it differs on the parts and on the whole.
    let take_first = |f: Term| {
        let whole = f.clone();
        discard_with(f, move |p, _| {
            eq(
                count(discard_with(whole, |q, _| lt(key(q, 0), key(p, 0)))),
                lit(0),
            )
        })
    };
    let (_, a, b) = refuted(splits(), |(a, b)| {
        (
            take_first(disjoint_union(ints(a), ints(b), 1)),
            disjoint_union(take_first(ints(a)), take_first(ints(b)), 1),
        )
    });
    assert_ne!(a, b);
}

// Law 6: a join is the disjoint union of its per-region discards.

#[derive(Clone, Copy, Debug, PartialEq)]
enum Region {
    Keep,
    Drop,
    AssertEmpty,
}
use Region::*;

/// `true` unless `e` is the atom `#name`.
fn not_atom(e: Term, name: &str) -> Term {
    Term::Match(
        rc(e),
        vec![
            (Pattern::Atom(name.into(), vec![]), lit(false)),
            (Pattern::Wild, lit(true)),
        ],
    )
}

/// `joinR(t)(a, b)` by its definition: each key of either operand is classified by region and
/// kept with its value pair, dropped, or, in an asserted-empty region, reported as
/// `#assertEmpty`, the failure the assertion stands for.
fn join_by_definition(t: [Region; 3], a: Term, b: Term) -> Term {
    let cell = |r: Region, pair: Term| match r {
        Keep => pair,
        Drop => atom("drop"),
        AssertEmpty => atom("assertEmpty"),
    };
    let both = prim(Prim::Union, vec![keyset(a.clone()), keyset(b.clone())]);
    let classified = fam_with(both, |k| {
        let (in_a, in_b) = (
            found(get(a.clone(), k.clone())),
            found(get(b.clone(), k.clone())),
        );
        let none = || atom("none");
        let pair = |x: Term, y: Term| prim(Prim::Tuple, vec![x, y]);
        if_(
            and(in_a.clone(), in_b.clone()),
            cell(
                t[1],
                pair(get(a.clone(), k.clone()), get(b.clone(), k.clone())),
            ),
            if_(
                in_a,
                cell(t[0], pair(get(a.clone(), k.clone()), none())),
                cell(t[2], pair(none(), get(b.clone(), k))),
            ),
        )
    });
    discard_with(classified, |_, e| not_atom(e, "drop"))
}

/// `joinR(t)(a, b)` as the disjoint union of the kept regions, each a discard of one operand.
fn join_by_regions(t: [Region; 3], a: Term, b: Term) -> Term {
    let pair = |x: Term, y: Term| prim(Prim::Tuple, vec![x, y]);
    let only = |x: Term, y: Term, left: bool| {
        let region = discard_with(x.clone(), |p, _| not(found(get(y, key(p, 0)))));
        fam_with(region, |k| {
            if left {
                pair(get(x, k), atom("none"))
            } else {
                pair(atom("none"), get(x, k))
            }
        })
    };
    let inner = fam_with(
        discard_with(a.clone(), {
            let b = b.clone();
            |p, _| found(get(b, key(p, 0)))
        }),
        |k| pair(get(a.clone(), k.clone()), get(b.clone(), k)),
    );
    let regions = [only(a.clone(), b.clone(), true), inner, only(b, a, false)];
    let mut out = lit(Value::Family(Family::new()));
    for (r, f) in t.iter().zip(regions) {
        if *r == Keep {
            out = disjoint_union(out, f, 1);
        }
    }
    out
}

#[test]
fn law_06_join_is_the_union_of_its_regions() {
    let pairs: Vec<(IntMap, IntMap)> = {
        let ms = partial_maps(&[0, 1, 2], &[1, 2]);
        ms.iter()
            .flat_map(|a| ms.iter().map(move |b| (a.clone(), b.clone())))
            .collect()
    };
    let keys = |m: &IntMap| m.iter().map(|e| e.0).collect::<Vec<_>>();
    let regions_empty = |t: [Region; 3], (a, b): &(IntMap, IntMap)| {
        let (ka, kb) = (keys(a), keys(b));
        let left = ka.iter().any(|k| !kb.contains(k));
        let mid = ka.iter().any(|k| kb.contains(k));
        let right = kb.iter().any(|k| !ka.contains(k));
        [left, mid, right]
            .iter()
            .zip(t)
            .all(|(nonempty, r)| r != AssertEmpty || !nonempty)
    };
    let triples = [
        [Drop, Keep, Drop],               // inner
        [Keep, Keep, Drop],               // left outer
        [Keep, Keep, Keep],               // full outer
        [Keep, Drop, Keep],               // symmetric difference
        [Keep, Drop, Drop],               // difference
        [Keep, AssertEmpty, Keep],        // disjoint union
        [AssertEmpty, Keep, AssertEmpty], // equality join (zip)
        [AssertEmpty, Keep, Drop],        // foreign key
    ];
    for t in triples {
        let ok: Vec<_> = pairs
            .iter()
            .filter(|p| regions_empty(t, p))
            .cloned()
            .collect();
        let n = holds(ok, |(a, b)| {
            (
                join_by_definition(t, ints(a), ints(b)),
                join_by_regions(t, ints(a), ints(b)),
            )
        });
        assert!(n >= 8, "{t:?} ran on {n} instances");
        if t.contains(&AssertEmpty) {
            // The side condition: on operands where an asserted region is not empty, the
            // regions' union silently loses its keys.
            let bad: Vec<_> = pairs
                .iter()
                .filter(|p| !regions_empty(t, p))
                .cloned()
                .collect();
            let (_, a, _) = refuted(bad, |(a, b)| {
                (
                    join_by_definition(t, ints(a), ints(b)),
                    join_by_regions(t, ints(a), ints(b)),
                )
            });
            assert!(a.unwrap().to_string().contains("#assertEmpty"));
        }
    }
}

// Law 7: a catalog-bijective reindex and its inverse cancel.

const W: i64 = 3;

/// `(i, j) -> i * W + j`, packing a two-level family into one level.
fn pack() -> Term {
    kv(|p, _| path(vec![add(mul(key(p.clone(), 0), lit(W)), key(p, 1))]))
}

/// `k -> (k div W, k mod W)`, Euclidean, or truncated toward zero when `truncated`.
fn unpack(truncated: bool) -> Term {
    kv(move |p, _| {
        let k = key(p, 0);
        let q = if truncated {
            // Truncated division rounds a negative quotient up.
            let floor = idiv(k.clone(), lit(W));
            let inexact = not(eq(modulo(k.clone(), lit(W)), lit(0)));
            if_(
                and(lt(k.clone(), lit(0)), inexact),
                add(floor.clone(), lit(1)),
                floor,
            )
        } else {
            idiv(k.clone(), lit(W))
        };
        path(vec![q.clone(), sub(k, mul(q, lit(W)))])
    })
}

/// Grids `row -> column -> v` with rows `-2..=1`, columns `0..W` and every cell present
/// with probability one half.
fn grids() -> Vec<Vec<(i64, i64, i64)>> {
    let mut rng = Rng::new(7);
    (0..512)
        .map(|_| {
            let mut g = Vec::new();
            for i in -2..=1 {
                for j in 0..W {
                    if rng.below(2) == 0 {
                        g.push((i, j, rng.int(-8, 8)));
                    }
                }
            }
            g
        })
        .collect()
}

fn grid(g: &[(i64, i64, i64)]) -> Term {
    let leaves: Vec<_> = g
        .iter()
        .map(|&(i, j, v)| (vec![Value::Int(i), Value::Int(j)], Value::Int(v)))
        .collect();
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

#[test]
fn law_07_affine_packing_round_trips_with_euclidean_division() {
    let id_v = kv(|_, v| v);
    let round_trip = |truncated: bool, g: &Vec<(i64, i64, i64)>| {
        let packed = reindex(grid(g), pack(), id_v.clone());
        (reindex(packed, unpack(truncated), id_v.clone()), grid(g))
    };
    assert_eq!(holds(grids(), |g| round_trip(false, g)), 512);
    // The other direction, on one level over the packed keys `-8..=8`.
    let n = holds(int_maps(8), |m| {
        let m: IntMap = m.iter().map(|&(k, v)| (k - 2, v)).collect();
        let unpacked = reindex(ints(&m), unpack(false), id_v.clone());
        (reindex(unpacked, pack(), id_v.clone()), ints(&m))
    });
    assert!(n >= 1_800);
    // Truncated division sends a negative row's cells to the wrong row.
    let (g, _, _) = refuted(grids(), |g| round_trip(true, g));
    assert!(g.iter().any(|&(i, j, _)| i < 0 && j != 0));
}

// Law 8: a fold may regroup, reorder and dedup, given the Boom row.

/// The map's values in chunks of two by key rank: `(rank div 2) -> rank -> v`.
fn chunked(m: &IntMap) -> Term {
    let leaves: Vec<_> = m
        .iter()
        .enumerate()
        .map(|(r, &(_, v))| {
            (
                vec![Value::Int(r as i64 / 2), Value::Int(r as i64)],
                Value::Int(v),
            )
        })
        .collect();
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

#[test]
fn law_08_an_associative_fold_regroups() {
    for op in [plus(), Term::PrimFn(Prim::Max)] {
        let n = holds(int_maps(9), |m| {
            (
                fold(fold_at(chunked(m), 2, op.clone(), None), op.clone(), None),
                fold(ints(m), op.clone(), None),
            )
        });
        assert!(n >= 1_800);
    }
    // `-` is not associative.
    let (m, _, _) = refuted(int_maps(9), |m| {
        let minus = Term::PrimFn(Prim::Sub);
        (
            fold(
                fold_at(chunked(m), 2, minus.clone(), None),
                minus.clone(),
                None,
            ),
            fold(ints(m), minus, None),
        )
    });
    assert!(m.len() >= 3);
}

#[test]
fn law_08_regrouping_a_float_sum_rounds_more_than_once() {
    // A float `+` fold is the exact sum rounded once; partial sums round each chunk.
    let xs = [0.1, 0.2, 0.3].map(Value::float);
    let chunks = lit(Value::Family(
        Family::from_leaves(vec![
            (vec![Value::Int(0), Value::Int(0)], xs[0].clone()),
            (vec![Value::Int(0), Value::Int(1)], xs[1].clone()),
            (vec![Value::Int(1), Value::Int(2)], xs[2].clone()),
        ])
        .unwrap(),
    ));
    let (_, a, b) = refuted([()], |_| {
        (
            fold(fold_at(chunks.clone(), 2, plus(), None), plus(), None),
            fold(seq(&xs), plus(), None),
        )
    });
    assert_eq!(
        (a.unwrap(), b.unwrap()),
        (Value::float(0.1 + 0.2 + 0.3), Value::float(0.6))
    );
}

#[test]
fn law_08_a_commutative_fold_reorders() {
    let reversed = |m: &IntMap| {
        reindex(
            ints(m),
            kv(|p, _| path(vec![sub(lit(0), key(p, 0))])),
            kv(|_, v| v),
        )
    };
    holds(int_maps(10), |m| {
        (fold(reversed(m), plus(), None), fold(ints(m), plus(), None))
    });
    // `first` is associative but not commutative.
    let first = func(|[x, _]| x);
    let _ = refuted(int_maps(10), |m| {
        (
            fold(reversed(m), first.clone(), None),
            fold(ints(m), first.clone(), None),
        )
    });
}

#[test]
fn law_08_an_idempotent_fold_dedups() {
    let distinct = |m: &IntMap| keyset(group_by(ints(m), |v| v));
    let max = Term::PrimFn(Prim::Max);
    holds(int_maps(11), |m| {
        (
            fold(keyset(distinct(m)), max.clone(), None),
            fold(ints(m), max.clone(), None),
        )
    });
    // `+` is not idempotent: a repeated value counts twice.
    let (m, _, _) = refuted(int_maps(11), |m| {
        (
            fold(keyset(distinct(m)), plus(), None),
            fold(ints(m), plus(), None),
        )
    });
    let vs: Vec<i64> = m.iter().map(|e| e.1).collect();
    assert!(vs.iter().any(|v| vs.iter().filter(|w| *w == v).count() > 1));
}

// Law 9: scan is the prefix-fold family.

/// The scan as the sequential recurrence `acc[0] = xs[0]`, `acc[i] = op(acc[i-1], xs[i])`.
fn scan_sequential(xs: Term, op: Term) -> Term {
    fix_defined(xs.clone(), |this, i| {
        if_(
            eq(i.clone(), lit(0)),
            get(xs.clone(), lit(0)),
            app(op, vec![get(this, sub(i.clone(), lit(1))), get(xs, i)]),
        )
    })
}

#[test]
fn law_09_scan_is_the_prefix_fold_family() {
    let seqs: Vec<Vec<i64>> = shortlex(&[-2, -1, 0, 1, 2, 5], 4);
    for op in [plus(), Term::PrimFn(Prim::Max)] {
        let n = holds(seqs.clone(), |xs| {
            (
                scan(seq(xs), op.clone()),
                scan_sequential(seq(xs), op.clone()),
            )
        });
        assert_eq!(n, 1 + 6 + 36 + 216 + 1_296);
    }
    // `-` is not associative, so the prefix folds' trees disagree with the recurrence.
    let minus = Term::PrimFn(Prim::Sub);
    let (xs, _, _) = refuted(seqs, |xs| {
        (
            scan(seq(xs), minus.clone()),
            scan_sequential(seq(xs), minus.clone()),
        )
    });
    assert!(xs.len() >= 3);
}

// Law 10: rank is a widen.

/// The dense rank each entry's class gets, read off the evaluated widen: `key -> rank`.
fn ranks_of(ranked: &Value) -> Vec<(i64, i64)> {
    let f = ranked.as_family().unwrap();
    let mut out: Vec<(i64, i64)> = f
        .leaves()
        .into_iter()
        .map(|(kp, _)| (kp[1].as_int().unwrap(), kp[0].as_int().unwrap()))
        .collect();
    out.sort();
    out
}

/// A sort key and a comparator on it, in Rust.
type SortKey = (fn(i64) -> i64, fn(i64, i64) -> bool);

/// Checks that the widen by sort key `f` and comparator `less` ranks a map as a total
/// preorder does: one entry per key, dense ranks from 0, equal ranks exactly for entries whose
/// keys tie, and a lower rank exactly for a smaller key. `f_rs` and `less_rs` are `f` and
/// `less` in Rust.
fn ranked_as_a_preorder(
    m: &IntMap,
    (f_rs, less_rs): SortKey,
    f: &dyn Fn(Term) -> Term,
    less: &dyn Fn(Term, Term) -> Term,
) -> Result<(), String> {
    let out = eval(&rank_widen(ints(m), f, less)).map_err(|e| format!("{e:?}"))?;
    let ranks = ranks_of(&out);
    if ranks.len() != m.len() {
        return Err(format!("{} entries ranked, {} given", ranks.len(), m.len()));
    }
    let mut used: Vec<i64> = ranks.iter().map(|r| r.1).collect();
    used.sort();
    used.dedup();
    if used != (0..used.len() as i64).collect::<Vec<_>>() {
        return Err(format!("ranks {used:?} are not dense"));
    }
    for (&(_, x), &(_, rx)) in m.iter().zip(&ranks) {
        for (&(_, y), &(_, ry)) in m.iter().zip(&ranks) {
            let (fx, fy) = (f_rs(x), f_rs(y));
            let tied = !less_rs(fx, fy) && !less_rs(fy, fx);
            if (rx == ry) != tied || (rx < ry) != less_rs(fx, fy) {
                return Err(format!("{x} at rank {rx} and {y} at rank {ry}"));
            }
        }
    }
    Ok(())
}

#[test]
fn law_10_rank_groups_tied_entries_under_a_dense_rank() {
    let by_value: SortKey = (|x| x, |x, y| x < y);
    let n = property(int_maps(12), |m| {
        ranked_as_a_preorder(m, by_value, &|v| v, &lt)
    });
    assert!(n >= 1_800);
    // By absolute value: `-2` and `2` tie, and share a rank.
    let abs = |v: Term| if_(lt(v.clone(), lit(0)), sub(lit(0), v.clone()), v);
    let by_abs: SortKey = (|x: i64| x.abs(), |x, y| x < y);
    property(int_maps(12), |m| ranked_as_a_preorder(m, by_abs, &abs, &lt));
    // A near-tie relation, `y - x >= 2`, is not a preorder whose ties are an equivalence:
    // 0 ties 1 and 1 ties 2, but 0 is below 2.
    let (m, _) = property_refuted(int_maps(12), |m| {
        let near: SortKey = (|x| x, |x, y| y - x >= 2);
        ranked_as_a_preorder(m, near, &|v| v, &|x, y| le(lit(2), sub(y, x)))
    });
    assert!(m.len() >= 2);
}
