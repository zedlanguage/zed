//! Laws 11–20 of the catalog: dead-structure deletion, distribution and promotion of folds,
//! prefix differences, step powers, semi-naive fixpoints, refinement hoisting, rollup,
//! contraction, and naturality.

use zed_kernel::term::build::{app, if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, GuardPos, Pattern, Prim, Term, Value, World, eval};
use zed_tests::check::{holds, refuted};
use zed_tests::instances::{Rng, bmc_floats, bmc_ints, shortlex};
use zed_tests::kernel::*;

use super::{IntMap, int_maps, ints, seq};

fn plus() -> Term {
    Term::PrimFn(Prim::Add)
}

pub(super) fn pf(p: Prim) -> Term {
    Term::PrimFn(p)
}

fn empty() -> Term {
    lit(Value::Family(Family::new()))
}

/// The maps of `int_maps` that have at least one entry.
fn nonempty_maps(seed: u64) -> Vec<IntMap> {
    int_maps(seed)
        .into_iter()
        .filter(|m| !m.is_empty())
        .collect()
}

/// A term built from an instance.
type Builder = Box<dyn Fn(&IntMap) -> Term>;

// Law 11: unconsumed structure deletes.

#[test]
fn law_11_a_binding_no_demand_reaches_deletes() {
    // A report that computes a sorted copy, a per-class total and a ratio, then returns only
    // the grand total: the three dead bindings delete.
    let total = |m: &IntMap| fold(ints(m), plus(), Some(lit(0)));
    let dead: Vec<Builder> = vec![
        Box::new(|m| rank_widen(ints(m), &|v| v, &lt)),
        Box::new(|m| fold_at(group_by(ints(m), |v| modulo(v, lit(3))), 2, plus(), None)),
        Box::new(|m| map(ints(m), |v| idiv(lit(12), v))),
    ];
    for d in &dead {
        let n = holds(int_maps(13), |m| {
            (let_(&fresh("unused"), d(m), total(m)), total(m))
        });
        assert!(n >= 1_800);
    }
    // A dead binding past the 64-bit range is an unread number: `int` is unbounded
    // (reference semantics (b); widened by step L1.17).
    let big = let_("unused", mul(lit(i64::MAX), lit(2)), lit(1));
    assert_eq!(eval(&big), Ok(Value::Int(1)));
}

#[test]
fn law_11_a_push_is_demanded_even_when_its_acknowledgment_is_not() {
    // The demand roots include the ports: deleting an unread push to `log` loses the line.
    let run = |t: &Term| {
        let mut ev = Evaluator::new(World::new().output("log"));
        let out = ev.run(t);
        (out, ev.world.log("log").to_vec())
    };
    let with_push = let_(
        "ack",
        Term::Push("log".into(), rc(lit(Value::str("checkpoint")))),
        lit(1),
    );
    let deleted = lit(1);
    let (a, b) = (run(&with_push), run(&deleted));
    assert_eq!(a.0, b.0);
    assert_eq!(a.1, vec![Value::str("checkpoint")]);
    assert!(b.1.is_empty());
}

// Law 12: a distributing constant hoists out of a fold.

/// `fold(⊕)(map(v -> c ⊗ v)(m))` and `c ⊗ fold(⊕)(m)`.
fn hoisted(m: &IntMap, c: i64, sum: Prim, times: Prim, identity: Option<Term>) -> (Term, Term) {
    (
        fold(
            map(ints(m), |v| bin(times, lit(c), v)),
            pf(sum),
            identity.clone(),
        ),
        bin(times, lit(c), fold(ints(m), pf(sum), identity)),
    )
}

#[test]
fn law_12_a_constant_factor_leaves_the_sum() {
    // Prices in cents times a quantity of 3: the total of the line items is 3 times the
    // total. `*` distributes over `+`, and 0 absorbs, so the empty order is covered too.
    for c in [-2, 0, 3] {
        let n = holds(int_maps(14), |m| {
            hoisted(m, c, Prim::Add, Prim::Mul, Some(lit(0)))
        });
        assert!(n >= 1_800);
    }
}

#[test]
fn law_12_on_a_possibly_empty_level_the_identity_must_absorb() {
    // `+` distributes over `max`, but the identity of `max`, here -100, does not absorb
    // under `+`: on an empty level the hoisted side adds the constant to it.
    let n = holds(nonempty_maps(15), |m| {
        hoisted(m, 5, Prim::Max, Prim::Add, Some(lit(-100)))
    });
    assert!(n >= 1_800);
    let (m, a, b) = refuted(int_maps(15), |m| {
        hoisted(m, 5, Prim::Max, Prim::Add, Some(lit(-100)))
    });
    assert!(m.is_empty());
    assert_eq!((a, b), (Ok(Value::Int(-100)), Ok(Value::Int(-95))));
}

#[test]
fn law_12_a_factor_that_does_not_distribute_stays_inside() {
    // `max` does not distribute over `+`: `max(c, a + b) != max(c, a) + max(c, b)`. The
    // instances are nonempty, so the refutation is not the identity's.
    let (m, _, _) = refuted(nonempty_maps(16), |m| {
        hoisted(m, 1, Prim::Add, Prim::Max, Some(lit(0)))
    });
    assert!(m.len() >= 2);
}

// Law 13: a range fold is a prefix difference in a group.

/// A permutation of `0..3` as the tuple of its images.
fn perm(p: [i64; 3]) -> Value {
    Value::Tuple(p.iter().map(|&x| Value::Int(x)).collect())
}

fn s3() -> Vec<Value> {
    [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ]
    .map(perm)
    .to_vec()
}

/// `p ⊕ q`: apply `p`, then `q`, so `(p ⊕ q)[i] = q[p[i]]`.
fn then() -> Term {
    func(|[p, q]| {
        let image = |i| prim(Prim::TupleGet, vec![q.clone(), nth(p.clone(), i)]);
        prim(Prim::Tuple, (0..3).map(image).collect())
    })
}

/// The inverse permutation: the `j` with `p[j] == i`, for each `i`.
fn inverse(p: Term) -> Term {
    let image = |i: i64| {
        if_(
            eq(nth(p.clone(), 0), lit(i)),
            lit(0),
            if_(eq(nth(p.clone(), 1), lit(i)), lit(1), lit(2)),
        )
    };
    prim(Prim::Tuple, (0..3).map(image).collect())
}

/// Each sequence of at most three permutations, with each range `i..=j` in it.
fn ranges() -> Vec<(Vec<Value>, i64, i64)> {
    let mut out = Vec::new();
    for xs in shortlex(&s3(), 3) {
        for j in 0..xs.len() as i64 {
            for i in 0..=j {
                out.push((xs.clone(), i, j));
            }
        }
    }
    out
}

/// The range fold, and the prefix difference with the inverse on the left or the right.
fn range_sides(xs: &[Value], i: i64, j: i64, inverse_left: bool) -> (Term, Term) {
    let range = fold(
        discard_with(seq(xs), |p, _| {
            and(le(lit(i), key(p.clone(), 0)), le(key(p, 0), lit(j)))
        }),
        then(),
        None,
    );
    let prefix = scan(seq(xs), then());
    let before = if i == 0 {
        lit(perm([0, 1, 2]))
    } else {
        get(prefix.clone(), lit(i - 1))
    };
    let upto = get(prefix, lit(j));
    let diff = if inverse_left {
        app(then(), vec![inverse(before), upto])
    } else {
        app(then(), vec![upto, inverse(before)])
    };
    (range, diff)
}

#[test]
fn law_13_a_range_of_a_group_fold_is_a_prefix_difference() {
    // Composing the shuffles applied to a deck between two steps of a log, from the
    // running compositions: the permutations of three cards are a group that is not
    // abelian.
    let n = holds(ranges(), |(xs, i, j)| range_sides(xs, *i, *j, true));
    assert_eq!(n, 6 + 36 * 3 + 216 * 6);
    // The other orientation, the inverse on the right, holds only on abelian carriers.
    let ((xs, i, _), _, _) = refuted(ranges(), |(xs, i, j)| range_sides(xs, *i, *j, false));
    assert!(i > 0 && xs.len() >= 2);
}

// Law 14: a counted run of a step is the step's power, by repeated squaring.

/// The affine map `x -> a * x + b` as the tuple `(a, b)`, and its composition: `(f ; g)`
/// applies `f` first.
fn affine_then(f: Term, g: Term) -> Term {
    // g(f(x)) = ga * (fa * x + fb) + gb
    prim(
        Prim::Tuple,
        vec![
            mul(nth(g.clone(), 0), nth(f.clone(), 0)),
            add(mul(nth(g.clone(), 0), nth(f, 1)), nth(g, 1)),
        ],
    )
}

/// `step^n` by repeated squaring, built for the static `n`.
fn power(step: Term, n: u32) -> Term {
    let mut acc = lit(Value::Tuple(vec![Value::Int(1), Value::Int(0)]));
    let mut square = step;
    let mut k = n;
    while k > 0 {
        if k & 1 == 1 {
            acc = affine_then(acc, square.clone());
        }
        square = affine_then(square.clone(), square);
        k >>= 1;
    }
    acc
}

/// The loop `gen` from `(0, x0)`, stepping `(t, x) -> (t + 1, next(t, x))` while `t < n`, and
/// the state at generation `n`.
fn counted(x0: i64, n: u32, next: impl Fn(Term, Term) -> Term) -> Term {
    let step = func(|[f]| {
        prim(
            Prim::Tuple,
            vec![
                add(nth(f.clone(), 0), lit(1)),
                next(nth(f.clone(), 0), nth(f, 1)),
            ],
        )
    });
    let frames = Term::Gen {
        init: rc(lit(Value::Tuple(vec![Value::Int(0), Value::Int(x0)]))),
        step: rc(step),
        guard: rc(func(|[f]| lt(nth(f, 0), lit(n as i64)))),
        pos: GuardPos::Before,
    };
    nth(get(frames, lit(n as i64)), 1)
}

fn affine_cases() -> Vec<(i64, i64, i64, u32)> {
    let mut out = Vec::new();
    for a in -2..=2 {
        for b in -2..=2 {
            for x0 in -2..=2 {
                for n in 0..=10 {
                    out.push((a, b, x0, n));
                }
            }
        }
    }
    out
}

#[test]
fn law_14_a_counted_affine_loop_is_one_power_of_its_step() {
    // Compound interest with a fee, `x -> a * x + b`, run for n periods.
    let n = holds(affine_cases(), |&(a, b, x0, n)| {
        let step = lit(Value::Tuple(vec![Value::Int(a), Value::Int(b)]));
        let p = power(step, n);
        (
            counted(x0, n, |_, x| add(mul(lit(a), x), lit(b))),
            add(mul(nth(p.clone(), 0), lit(x0)), nth(p, 1)),
        )
    });
    assert_eq!(n, 5 * 5 * 5 * 11);
    // A step that reads the step index, `x -> x + t`, applies a different action each step,
    // so no single action has a power: the power of its first action, the identity, misses
    // every later one.
    let (_, a, b) = refuted(affine_cases(), |&(_, _, x0, n)| {
        let first_action = lit(Value::Tuple(vec![Value::Int(1), Value::Int(0)]));
        let p = power(first_action, n);
        (
            counted(x0, n, add),
            add(mul(nth(p.clone(), 0), lit(x0)), nth(p, 1)),
        )
    });
    assert_ne!(a, b);
}

// Law 15: fix runs semi-naive.

/// A relation on the nodes `0..N` as the two-level family `u -> v -> true`.
pub(super) const N: i64 = 4;

pub(super) fn nodes() -> Term {
    lit(Value::Family(Family::set(0..N)))
}

pub(super) fn relation(pairs: &[(i64, i64)]) -> Term {
    let leaves: Vec<_> = pairs
        .iter()
        .map(|&(u, v)| (vec![Value::Int(u), Value::Int(v)], Value::Bool(true)))
        .collect();
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

/// `r · s`: the pairs `(u, w)` with some `v` such that `(u, v)` is in `r` and `(v, w)` in `s`.
pub(super) fn compose(r: Term, s: Term) -> Term {
    fam_with(nodes(), |u| {
        let row = fam_with(nodes(), |w| {
            let via = discard_with(nodes(), |p, _| {
                let v = key(p, 0);
                and(
                    found(get(get(r.clone(), u.clone()), v.clone())),
                    found(get(get(s.clone(), v), w.clone())),
                )
            });
            lt(lit(0), count(via))
        });
        discard_with(row, |_, e| e)
    })
}

pub(super) fn union(a: Term, b: Term) -> Term {
    prim(Prim::Union, vec![a, b])
}

/// `a` less the pairs of `b`.
fn minus(a: Term, b: Term) -> Term {
    discard_with(a, |p, _| {
        not(and(
            eq(prim(Prim::PathLen, vec![p.clone()]), lit(2)),
            found(get(get(b, key(p.clone(), 0)), key(p, 1))),
        ))
    })
}

/// The relation the frontier loop reaches: frames `(old, delta)` from `({}, e)`, each round's
/// candidates `cand(delta, old, old ∪ delta)` less what is known, until the delta is empty.
fn semi_naive(e: Term, cand: impl Fn(Term, Term, Term) -> Term) -> Term {
    let step = func(|[f]| {
        let (old, delta) = (nth(f.clone(), 0), nth(f, 1));
        let new = union(old.clone(), delta.clone());
        let fresh_pairs = minus(cand(delta, old, new.clone()), new.clone());
        prim(Prim::Tuple, vec![new, fresh_pairs])
    });
    let frames = Term::Gen {
        init: rc(prim(Prim::Tuple, vec![empty(), e])),
        step: rc(step),
        guard: rc(func(|[f]| lt(lit(0), count(nth(f, 1))))),
        pos: GuardPos::Before,
    };
    let g = fresh("g");
    let last = get(var(&g), sub(count(var(&g)), lit(1)));
    let_(&g, frames, union(nth(last.clone(), 0), nth(last, 1)))
}

/// Every relation on three of the nodes, then random ones on all four.
pub(super) fn relations() -> Vec<Vec<(i64, i64)>> {
    let pairs3: Vec<(i64, i64)> = (0..3).flat_map(|u| (0..3).map(move |v| (u, v))).collect();
    let mut out: Vec<Vec<(i64, i64)>> = (0..1u32 << pairs3.len())
        .map(|mask| {
            pairs3
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, &p)| p)
                .collect()
        })
        .collect();
    let mut rng = Rng::new(15);
    for _ in 0..256 {
        let r = (0..N)
            .flat_map(|u| (0..N).map(move |v| (u, v)))
            .filter(|_| rng.below(4) == 0)
            .collect();
        out.push(r);
    }
    out
}

#[test]
fn law_15_a_linear_step_runs_on_the_frontier() {
    // Every station reachable along a rail network: `r -> r · e` is linear over union.
    let n = holds(relations(), |pairs| {
        let e = relation(pairs);
        let step = {
            let e = e.clone();
            func(move |[r]| compose(r, e))
        };
        (
            fix_lattice(e.clone(), step, pf(Prim::Union)),
            semi_naive(e.clone(), |delta, _, _| compose(delta, e.clone())),
        )
    });
    assert_eq!(n, 512 + 256);
}

#[test]
fn law_15_a_quadratic_step_reads_the_old_and_new_values_around_the_delta() {
    // Transitive closure by path doubling, `r -> r · r`: semi-naive in a distributive dioid
    // steps by `Δ · r_old ⊔ r_new · Δ`.
    let lattice = |pairs: &Vec<(i64, i64)>| {
        fix_lattice(
            relation(pairs),
            func(|[r]| compose(r.clone(), r)),
            pf(Prim::Union),
        )
    };
    let n = holds(relations(), |pairs| {
        (
            lattice(pairs),
            semi_naive(relation(pairs), |delta, old, new| {
                union(compose(delta.clone(), old), compose(new, delta))
            }),
        )
    });
    assert_eq!(n, 512 + 256);
    // The delta alone, `Δ · Δ`, misses a path whose halves were found in different rounds.
    let (pairs, _, _) = refuted(relations(), |pairs| {
        (
            lattice(pairs),
            semi_naive(relation(pairs), |delta, _, _| compose(delta.clone(), delta)),
        )
    });
    assert!(pairs.len() >= 3);
}

// Law 16: a refinement hoists backward through an operation.

/// The values a refinement is tried on: the rung 6 integers and a failure atom.
fn refine_inputs() -> Vec<Term> {
    let mut xs: Vec<Term> = bmc_ints().into_iter().map(lit).collect();
    xs.push(atom("badRecord"));
    xs
}

/// `op(x).refine(p)` and `x.refine(p ∘ op)`.
fn hoist(op: &dyn Fn(Term) -> Term, p: &Term, x: &Term) -> (Term, Term) {
    let composed = {
        let p = p.clone();
        func(|[y]| app(p, vec![op(y)]))
    };
    (
        refine(op(x.clone()), p.clone()),
        op(refine(x.clone(), composed)),
    )
}

#[test]
fn law_16_a_check_on_the_output_is_a_check_on_the_input() {
    // A dosage check, `0 < v`, on a computed dose, moved to the input it is computed from.
    let positive = func(|[v]| lt(lit(0), v));
    let ops: Vec<Box<dyn Fn(Term) -> Term>> = vec![
        Box::new(|x| add(mul(lit(2), x), lit(1))),
        Box::new(|x| idiv(lit(12), x)),
        Box::new(|x| modulo(x, lit(3))),
        Box::new(|x| mul(x.clone(), x)),
        // Along the first argument of `x - y`, with `y` held at 4.
        Box::new(|x| sub(x, lit(4))),
    ];
    for op in &ops {
        let n = holds(refine_inputs(), |x| hoist(op.as_ref(), &positive, x));
        assert_eq!(n, 18);
    }
    // A predicate that narrows a failure, here sending `#divByZero` to `false`, sees the
    // failure only on the hoisted side, where it is the input's preimage.
    let narrowing = func(|[v]| {
        Term::Match(
            rc(v.clone()),
            vec![
                (Pattern::Atom("divByZero".into(), vec![]), lit(false)),
                (Pattern::Wild, lt(lit(0), v)),
            ],
        )
    });
    let div = |x: Term| idiv(lit(12), x);
    let (x, a, b) = refuted(refine_inputs(), |x| hoist(&div, &narrowing, x));
    assert_eq!(eval(&x), Ok(Value::Int(0)));
    assert_eq!(
        (a, b),
        (Ok(Value::atom("divByZero")), Ok(Value::atom("invalid")))
    );
}

// Law 17: fold promotion.

/// `h(fold(⊕)(m))` and `fold(⊗)(map(h)(m))`.
fn promoted(
    m: Term,
    h: &dyn Fn(Term) -> Term,
    sum: Prim,
    sum_id: Option<Term>,
    times: Prim,
    times_id: Option<Term>,
) -> (Term, Term) {
    (
        h(fold(m.clone(), pf(sum), sum_id)),
        fold(map(m, h), pf(times), times_id),
    )
}

#[test]
fn law_17_a_monotone_map_moves_inside_a_max() {
    // The best score after a curve `2v + 1` is the curve of the best score.
    let curve = |v: Term| add(mul(lit(2), v), lit(1));
    let n = holds(int_maps(17), |m| {
        promoted(ints(m), &curve, Prim::Max, None, Prim::Max, None)
    });
    assert!(n >= 1_800);
    // `v * v` is not monotone on the negative scores.
    let square = |v: Term| mul(v.clone(), v);
    let (m, _, _) = refuted(int_maps(17), |m| {
        promoted(ints(m), &square, Prim::Max, None, Prim::Max, None)
    });
    assert!(m.iter().any(|e| e.1 < 0));
}

#[test]
fn law_17_on_an_empty_level_the_map_must_carry_identity_to_identity() {
    // `v + 1` is monotone, but sends the identity -100 to -99.
    let next = |v: Term| add(v, lit(1));
    let sides = |m: &IntMap| {
        promoted(
            ints(m),
            &next,
            Prim::Max,
            Some(lit(-100)),
            Prim::Max,
            Some(lit(-100)),
        )
    };
    assert!(holds(nonempty_maps(18), sides) >= 1_800);
    let (m, a, b) = refuted(int_maps(18), sides);
    assert!(m.is_empty());
    assert_eq!((a, b), (Ok(Value::Int(-99)), Ok(Value::Int(-100))));
}

#[test]
fn law_17_a_float_sum_premise_is_the_n_ary_equation_bitwise() {
    // Negation is a homomorphism of binary `+` up to the sign of zero, and the n-ary
    // equation fails bitwise there: the exact sum of `0.0` and `-0.0` is `+0.0`, and so is
    // the exact sum of their negations.
    let neg = |v: Term| prim(Prim::Neg, vec![v]);
    let floats: Vec<Vec<Value>> = shortlex(&bmc_floats(), 2);
    let (xs, a, b) = refuted(floats, |xs| {
        promoted(seq(xs), &neg, Prim::Add, None, Prim::Add, None)
    });
    assert_eq!(
        xs.iter()
            .filter(|x| matches!(x, Value::Float(f) if f.get() == 0.0))
            .count(),
        2
    );
    assert_eq!((a, b), (Ok(Value::float(-0.0)), Ok(Value::float(0.0))));
}

// Law 18: rollup.

/// Reduce-by-key along the key map `f`: entry `k -> v` goes to class `f(k)`.
fn rollup_by(m: Term, f: &dyn Fn(Term) -> Term, op: Term) -> Term {
    let kf = func(|[p, _]| path(vec![f(key(p.clone(), 0)), key(p, 0)]));
    fold_at(reindex(m, kf, func(|[_, v]| v)), 2, op, None)
}

/// The aggregate along `g ∘ f`, and the one along `g` of the aggregate along `f`.
fn rolled(
    m: &IntMap,
    f: &dyn Fn(Term) -> Term,
    g: &dyn Fn(Term) -> Term,
    op: &Term,
) -> (Term, Term) {
    let gf = |k: Term| g(f(k));
    (
        rollup_by(ints(m), &gf, op.clone()),
        rollup_by(rollup_by(ints(m), f, op.clone()), g, op.clone()),
    )
}

#[test]
fn law_18_a_coarse_total_comes_from_the_fine_totals() {
    // Sales by day `k`, rolled up to weeks `k div 2`, then to the parity of the week.
    let week = |k: Term| idiv(k, lit(2));
    let parity = |w: Term| modulo(w, lit(2));
    let n = holds(int_maps(19), |m| rolled(m, &week, &parity, &plus()));
    assert!(n >= 1_800);
}

#[test]
fn law_18_a_fold_that_does_not_commute_needs_a_monotone_fine_map() {
    // `first`: the earliest sale of each class. With the fine map monotone, the earliest
    // fine class holds the earliest entry; the coarse map is unconstrained.
    let first = func(|[x, _]| x);
    let week = |k: Term| idiv(k, lit(2));
    let third = |w: Term| modulo(w, lit(3));
    assert!(holds(int_maps(20), |m| rolled(m, &week, &third, &first)) >= 1_800);
    // A fine map that reverses the order picks the latest entry of each coarse class.
    let reversed = |k: Term| sub(lit(0), k);
    let parity = |w: Term| modulo(w, lit(2));
    let (m, _, _) = refuted(int_maps(20), |m| rolled(m, &reversed, &parity, &first));
    assert!(m.len() >= 2);
}

// Law 19: contraction is associative.

const D: i64 = 2;

fn dims() -> Term {
    lit(Value::Family(Family::set(0..D)))
}

/// A `D × D` matrix with some cells absent, as `i -> j -> v`.
fn matrix(cells: &[(i64, i64, Value)]) -> Term {
    let leaves: Vec<_> = cells
        .iter()
        .map(|(i, j, v)| (vec![Value::Int(*i), Value::Int(*j)], v.clone()))
        .collect();
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

fn present(m: &Term, i: Term, j: Term) -> Term {
    found(get(get(m.clone(), i), j))
}

/// `(a · b)[i][k]`: the `⊕`-fold over `j` of `a[i][j] ⊗ b[j][k]`, over the `j` where both
/// cells are present.
fn contract(a: Term, b: Term, sum: &Term, times: &Term) -> Term {
    let joined = fam_with(dims(), |i| {
        fam_with(dims(), |k| {
            let shared = discard_with(dims(), |p, _| {
                and(
                    present(&a, i.clone(), key(p.clone(), 0)),
                    present(&b, key(p, 0), k.clone()),
                )
            });
            fam_with(shared, |j| {
                app(
                    times.clone(),
                    vec![
                        get(get(a.clone(), i.clone()), j.clone()),
                        get(get(b.clone(), j), k.clone()),
                    ],
                )
            })
        })
    });
    fold_at(joined, 3, sum.clone(), None)
}

/// Random triples of matrices over `values`, each cell absent with probability 1/4.
fn triples(seed: u64, values: &[Value]) -> Vec<[Vec<(i64, i64, Value)>; 3]> {
    let mut rng = Rng::new(seed);
    let one = |rng: &mut Rng| {
        let mut cells = Vec::new();
        for i in 0..D {
            for j in 0..D {
                if rng.below(4) != 0 {
                    cells.push((i, j, rng.pick(values)));
                }
            }
        }
        cells
    };
    (0..512)
        .map(|_| [one(&mut rng), one(&mut rng), one(&mut rng)])
        .collect()
}

fn chain_sides(t: &[Vec<(i64, i64, Value)>; 3], sum: &Term, times: &Term) -> (Term, Term) {
    let [a, b, c] = t.clone().map(|m| matrix(&m));
    (
        contract(
            contract(a.clone(), b.clone(), sum, times),
            c.clone(),
            sum,
            times,
        ),
        contract(a, contract(b, c, sum, times), sum, times),
    )
}

#[test]
fn law_19_a_chain_of_contractions_reorders_in_every_semiring() {
    let ints: Vec<Value> = (-3..=3).map(Value::Int).collect();
    let bools = vec![Value::Bool(false), Value::Bool(true)];
    let semirings = [
        (pf(Prim::Add), pf(Prim::Mul), &ints), // counting
        (pf(Prim::Min), pf(Prim::Add), &ints), // shortest paths
        (pf(Prim::Max), pf(Prim::Min), &ints), // widest paths
        (pf(Prim::Or), pf(Prim::And), &bools), // reachability
    ];
    for (k, (sum, times, values)) in semirings.iter().enumerate() {
        let n = holds(triples(19 + k as u64, values), |t| {
            chain_sides(t, sum, times)
        });
        assert_eq!(n, 512);
    }
}

#[test]
fn law_19_contraction_needs_distribution_and_a_commutative_sum() {
    let ints: Vec<Value> = (-3..=3).map(Value::Int).collect();
    // `max` does not distribute over `+`.
    let _ = refuted(triples(23, &ints), |t| {
        chain_sides(t, &pf(Prim::Add), &pf(Prim::Max))
    });
    // `first` is associative and `*` distributes over it, but it does not commute: the two
    // orders take the first `k` of the first `j` and the first `j` of the first `k`.
    let first = func(|[x, _]| x);
    let _ = refuted(triples(24, &ints), |t| {
        chain_sides(t, &first, &pf(Prim::Mul))
    });
}

#[test]
fn law_19_a_star_join_folds_each_arm_before_the_join() {
    // Orders `a[i][j]` of customer i for product j, with the product's prices `b[j][k]` and
    // discounts `c[j][l]` per variant: the sum over all triples is the sum over `j` of the
    // order times the arms' totals. A product with no prices or no discounts drops out.
    let ints: Vec<Value> = (-3..=3).map(Value::Int).collect();
    let n = holds(triples(25, &ints), |t| {
        let [a, b, c] = t.clone().map(|m| matrix(&m));
        let cell = |i: Term, j: Term, k: Term, l: Term| {
            if_(
                and(
                    and(
                        present(&a, i.clone(), j.clone()),
                        present(&b, j.clone(), k.clone()),
                    ),
                    present(&c, j.clone(), l.clone()),
                ),
                mul(
                    mul(
                        get(get(a.clone(), i), j.clone()),
                        get(get(b.clone(), j.clone()), k),
                    ),
                    get(get(c.clone(), j), l),
                ),
                atom("drop"),
            )
        };
        let all = fam_with(dims(), |i| {
            fam_with(dims(), |j| {
                fam_with(dims(), |k| {
                    discard_with(
                        fam_with(dims(), |l| cell(i.clone(), j.clone(), k.clone(), l)),
                        |_, e| not_atom_named(e, "drop"),
                    )
                })
            })
        });
        let lhs = fold_at(
            fold_at(fold_at(all, 4, plus(), None), 3, plus(), None),
            2,
            plus(),
            None,
        );
        let rhs = fam_with(dims(), |i| {
            let js = discard_with(dims(), |p, _| {
                let j = key(p, 0);
                and(
                    present(&a, i.clone(), j.clone()),
                    and(
                        some(|q| present(&b, j.clone(), q)),
                        some(|q| present(&c, j, q)),
                    ),
                )
            });
            fold(
                fam_with(js, |j| {
                    mul(
                        mul(
                            get(get(a.clone(), i.clone()), j.clone()),
                            fold(get(b.clone(), j.clone()), plus(), None),
                        ),
                        fold(get(c.clone(), j), plus(), None),
                    )
                }),
                plus(),
                None,
            )
        });
        (lhs, discard_with(rhs, |_, e| not_atom_named(e, "empty")))
    });
    assert_eq!(n, 512);
}

/// `false` on the atom `#name`, `true` on anything else.
fn not_atom_named(e: Term, name: &str) -> Term {
    Term::Match(
        rc(e),
        vec![
            (Pattern::Atom(name.into(), vec![]), lit(false)),
            (Pattern::Wild, lit(true)),
        ],
    )
}

/// Whether some `q` in `0..D` has `pred(q)`.
fn some(pred: impl FnOnce(Term) -> Term) -> Term {
    lt(lit(0), count(discard_with(dims(), |p, _| pred(key(p, 0)))))
}

// Law 20: naturality.

#[test]
fn law_20_a_map_moves_past_a_function_that_ignores_values() {
    let g = |v: Term| mul(v.clone(), v);
    // `first`: the entry with the least key.
    let first = func(|[x, _]| x);
    let n = holds(int_maps(26), |m| {
        (
            g(fold(ints(m), first.clone(), None)),
            fold(map(ints(m), g), first.clone(), None),
        )
    });
    assert!(n >= 1_800);
    // A key restriction: the readings before the cutoff.
    let early = |f: Term| discard_with(f, |p, _| lt(key(p, 0), lit(2)));
    holds(int_maps(26), |m| {
        (map(early(ints(m)), g), early(map(ints(m), g)))
    });
}

#[test]
fn law_20_past_an_equality_test_the_map_must_preserve_and_reflect_it() {
    // The number of distinct readings, an `int`, which the map leaves alone.
    let distinct = |f: Term| count(keyset(group_by(f, |v| v)));
    let injective = |v: Term| add(mul(lit(2), v), lit(1));
    holds(int_maps(27), |m| {
        (distinct(map(ints(m), injective)), distinct(ints(m)))
    });
    // `v * v` merges `-1` and `1`.
    let square = |v: Term| mul(v.clone(), v);
    let (m, _, _) = refuted(int_maps(27), |m| {
        (distinct(map(ints(m), square)), distinct(ints(m)))
    });
    let vs: Vec<i64> = m.iter().map(|e| e.1).collect();
    assert!(vs.iter().any(|v| vs.contains(&-v) && *v != 0));
}

#[test]
fn law_20_past_an_order_the_map_must_preserve_and_reflect_it() {
    // Ranking scores, then rescaling them, against rescaling first.
    let sides = |m: &IntMap, g: &dyn Fn(Term) -> Term| {
        (
            rank_widen(map(ints(m), g), &|v| v, &lt),
            map(rank_widen(ints(m), &|v| v, &lt), g),
        )
    };
    let rescale = |v: Term| add(mul(lit(2), v), lit(1));
    assert!(holds(int_maps(28), |m| sides(m, &rescale)) >= 1_800);
    // `v div 2` is monotone but merges `2` and `3` into one tie, so their ranks merge.
    let halve = |v: Term| idiv(v, lit(2));
    let (m, _, _) = refuted(int_maps(28), |m| sides(m, &halve));
    assert!(m.len() >= 2);
}
