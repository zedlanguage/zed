//! Laws 21–28 of the catalog: folds over a recursive union, bisection, tupling, lookup
//! through reduce-by-key, fix fusion, generation fusion, the update laws of `with`, and
//! reversal.

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Family, GuardPos, KernelError, Prim, Term, Value};
use zed_tests::check::{holds, refuted};
use zed_tests::instances::{Rng, bmc_floats, partial_maps, shortlex};
use zed_tests::kernel::*;

use super::laws_11_20::{N, compose, or_else, pf, relation, relations, row_of, set_image, union};
use super::{ints, seq};

fn plus() -> Term {
    pf(Prim::Add)
}

fn tuple(items: Vec<Term>) -> Term {
    prim(Prim::Tuple, items)
}

/// `first`: the entry with the least key.
fn first() -> Term {
    func(|[x, _]| x)
}

/// The last frame of a `gen` result.
fn last_frame(frames: Term, then: impl FnOnce(Term) -> Term) -> Term {
    let g = fresh("g");
    let last = get(var(&g), sub(count(var(&g)), lit(1)));
    let_(&g, frames, then(last))
}

// Law 21: fold uniqueness and fusion over a recursive union.

/// A binary tree as a node table `i -> (v, left, right)` with the root at 0 and -1 for an
/// absent child: the recursive union `Node(v, l, r) | Empty` with each node named by its
/// preorder number.
type Tree = Vec<(i64, i64, i64)>;

/// Every shape of `n` nodes numbered in preorder from `o`, as each node's children.
fn shapes(n: i64, o: i64) -> Vec<Vec<(i64, i64)>> {
    if n == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for a in 0..n {
        for l in shapes(a, o + 1) {
            for r in shapes(n - 1 - a, o + 1 + a) {
                let left = if a > 0 { o + 1 } else { -1 };
                let right = if n - 1 - a > 0 { o + 1 + a } else { -1 };
                let mut t = vec![(left, right)];
                t.extend(l.iter().copied());
                t.extend(r);
                out.push(t);
            }
        }
    }
    out
}

/// Every tree of one to three nodes with values in `-2..=2`, then random trees of up to
/// eight nodes with values in `-8..=8`.
fn trees() -> Vec<Tree> {
    let mut out = Vec::new();
    for n in 1..=3 {
        for shape in shapes(n, 0) {
            for vs in shortlex(&[-2i64, -1, 0, 1, 2], n as usize)
                .into_iter()
                .filter(|vs| vs.len() == n as usize)
            {
                out.push(shape.iter().zip(vs).map(|(&(l, r), v)| (v, l, r)).collect());
            }
        }
    }
    let mut rng = Rng::new(21);
    let by_size: Vec<_> = (0..=8).map(|n| shapes(n, 0)).collect();
    for _ in 0..256 {
        let n = rng.int(1, 8) as usize;
        let shape = rng.pick(&by_size[n]);
        out.push(shape.iter().map(|&(l, r)| (rng.int(-8, 8), l, r)).collect());
    }
    out
}

fn tree(t: &Tree) -> Term {
    let entries = t.iter().enumerate().map(|(i, &(v, l, r))| {
        (
            i as i64,
            Value::tuple(vec![Value::Int(v), Value::Int(l), Value::Int(r)]),
        )
    });
    lit(Value::Family(Family::of(entries)))
}

/// `t.fold(alg)` at the root: `empty` at an absent child, `node(v, l, r)` with the children's
/// results at a node, as the definedness fix over the node table.
fn tree_fold(t: Term, empty: Term, node: impl Fn(Term, Term, Term) -> Term) -> Term {
    let table = t.clone();
    let all = fix_defined(t, |this, k| {
        let n = get(table, k);
        let child = |c: Term| if_(eq(c.clone(), lit(-1)), empty.clone(), get(this.clone(), c));
        node(
            nth(n.clone(), 0),
            child(nth(n.clone(), 1)),
            child(nth(n, 2)),
        )
    });
    get(all, lit(0))
}

fn tree_sum(t: Term) -> Term {
    tree_fold(t, lit(0), |v, l, r| add(add(v, l), r))
}

#[test]
fn law_21_two_functions_that_satisfy_one_fold_equation_are_equal() {
    // The number of employees under a manager in an org chart: the table's count satisfies
    // `size(Node(v, l, r)) = 1 + size(l) + size(r)` and `size(Empty) = 0`, so it is the fold.
    let n = holds(trees(), |t| {
        (
            count(tree(t)),
            tree_fold(tree(t), lit(0), |_, l, r| add(add(lit(1), l), r)),
        )
    });
    assert_eq!(n, 5 + 2 * 25 + 5 * 125 + 256);
}

#[test]
fn law_21_a_function_of_a_fold_is_a_fold_when_it_commutes_with_one_layer() {
    // Converting a cost tree's total to another unit, `h(x) = 3x`, is the fold that converts
    // each node's own cost: `h(v + l + r) = 3v + h(l) + h(r)` and `h(0) = 0`.
    let n = holds(trees(), |t| {
        (
            mul(lit(3), tree_sum(tree(t))),
            tree_fold(tree(t), lit(0), |v, l, r| add(add(mul(lit(3), v), l), r)),
        )
    });
    assert!(n > 900);
    // `x * x` does not commute with the layer: the square of a sum is not the sum of squares.
    let (t, _, _) = refuted(trees(), |t| {
        let square = |x: Term| mul(x.clone(), x);
        (
            square(tree_sum(tree(t))),
            tree_fold(tree(t), lit(0), |v, l, r| add(add(square(v), l), r)),
        )
    });
    assert!(t.len() >= 2);
}

#[test]
fn law_21_over_a_mutual_recursion_the_equations_hold_componentwise() {
    // Two mutually recursive functions over the levels of a tree: `even(n)` sums the values
    // at even depth below and at `n`, `odd(n)` those at odd depth, as one fold at the pair.
    // Their difference, the alternating sum, is the fold `v - h(l) - h(r)`.
    let n = holds(trees(), |t| {
        let pair = tree_fold(tree(t), tuple(vec![lit(0), lit(0)]), |v, l, r| {
            tuple(vec![
                add(add(v, nth(l.clone(), 1)), nth(r.clone(), 1)),
                add(nth(l, 0), nth(r, 0)),
            ])
        });
        let p = fresh("p");
        (
            let_(&p, pair, sub(nth(var(&p), 0), nth(var(&p), 1))),
            tree_fold(tree(t), lit(0), |v, l, r| sub(sub(v, l), r)),
        )
    });
    assert!(n > 900);
}

/// The heap-shaped tree over a sequence: node `i` holds `xs[i]` with children `2i + 1` and
/// `2i + 2` where those are in range.
fn heap_build(xs: Term) -> Term {
    let n = count(xs.clone());
    fam_with(xs.clone(), |i| {
        let child = |c: Term| if_(lt(c.clone(), n.clone()), c, lit(-1));
        tuple(vec![
            get(xs, i.clone()),
            child(add(mul(lit(2), i.clone()), lit(1))),
            child(add(mul(lit(2), i), lit(2))),
        ])
    })
}

#[test]
fn law_21_a_fold_of_a_build_is_the_recursion_on_seeds() {
    // The height of a binary heap built from an array, computed without the heap: `go(i)`
    // recurses on the array indices the build would make children of.
    let height = |_: Term, l: Term, r: Term| add(lit(1), prim(Prim::Max, vec![l, r]));
    let n = holds(shortlex(&[-2i64, -1, 0, 1, 2], 4), |xs| {
        let xs = seq(xs);
        let n = count(xs.clone());
        let go = fix_defined(xs.clone(), |this, i| {
            let at = |c: Term| if_(lt(c.clone(), n.clone()), get(this.clone(), c), lit(0));
            add(
                lit(1),
                prim(
                    Prim::Max,
                    vec![
                        at(add(mul(lit(2), i.clone()), lit(1))),
                        at(add(mul(lit(2), i), lit(2))),
                    ],
                ),
            )
        });
        (tree_fold(heap_build(xs), lit(0), height), get(go, lit(0)))
    });
    assert_eq!(n, 1 + 5 + 25 + 125 + 625);
}

/// `x else d`: `d` in place of any atom.
fn or(x: Term, d: i64) -> Term {
    or_else(x, None, lit(d))
}

/// The layer `a(Node(v, l, r)) = l + r + 12 div v`: a tree of shares, each node splitting 12
/// into `v` parts, which fails with `#divByZero` at a node of 0 parts.
fn shares(v: Term, l: Term, r: Term) -> Term {
    add(add(l, r), idiv(lit(12), v))
}

/// Each layer `(v, l, r)` with `v` in `-2..=2` and children in `-3..=3`, or `#divByZero` as
/// well when `failures` is set.
fn layers(failures: bool) -> Vec<(i64, Value, Value)> {
    let mut children: Vec<Value> = (-3..=3).map(Value::Int).collect();
    if failures {
        children.push(Value::atom("divByZero"));
    }
    let mut out = Vec::new();
    for v in -2..=2 {
        for l in &children {
            for r in &children {
                out.push((v, l.clone(), r.clone()));
            }
        }
    }
    out
}

#[test]
fn law_21_fusion_needs_h_strict_on_the_failure_channel() {
    // `h(x) = 3x` is strict: three times an atom is the atom. It commutes with every layer,
    // a failing child included, and fuses.
    let strict = |v: Term, l: Term, r: Term| add(add(l, r), mul(lit(3), idiv(lit(12), v)));
    let n = holds(layers(true), |(v, l, r)| {
        let (v, l, r) = (lit(*v), lit(l.clone()), lit(r.clone()));
        (
            mul(lit(3), shares(v.clone(), l.clone(), r.clone())),
            strict(v, mul(lit(3), l), mul(lit(3), r)),
        )
    });
    assert_eq!(n, 5 * 8 * 8);
    let n = holds(trees(), |t| {
        (
            mul(lit(3), tree_fold(tree(t), lit(0), shares)),
            tree_fold(tree(t), lit(0), strict),
        )
    });
    assert!(n > 900);
    // `h(x) = x else 0` is not strict. With `b(v, L, R) = (L + R + 12 div v) else 0` the
    // premise `h(a(n)) == b(F(h)(n))` holds on every layer whose children are numbers, so a
    // check of the premise on the success members alone passes,
    let lazy = |v: Term, l: Term, r: Term| or(shares(v, l, r), 0);
    let n = holds(layers(false), |(v, l, r)| {
        let (v, l, r) = (lit(*v), lit(l.clone()), lit(r.clone()));
        (
            or(shares(v.clone(), l.clone(), r.clone()), 0),
            lazy(v, or(l, 0), or(r, 0)),
        )
    });
    assert_eq!(n, 5 * 7 * 7);
    // but not on a layer with a failing child: `h` turns the child's atom into 0 before `b`
    // sees it, where `a` would have passed it up.
    let ((_, l, r), a, b) = refuted(layers(true), |(v, l, r)| {
        let (v, l, r) = (lit(*v), lit(l.clone()), lit(r.clone()));
        (
            or(shares(v.clone(), l.clone(), r.clone()), 0),
            lazy(v, or(l, 0), or(r, 0)),
        )
    });
    assert!(matches!(l, Value::Atom(_)) || matches!(r, Value::Atom(_)));
    assert_ne!(a, b);
    // And fusion fails: at `Node(1, Empty, Node(0, Empty, Empty))` the child fails, `a` passes
    // the failure to the root and `h` makes it 0, while `b` makes the child 0 and the root 12.
    let named: Tree = vec![(1, -1, 1), (0, -1, -1)];
    let (_, a, b) = refuted(vec![named], |t| {
        (
            or(tree_fold(tree(t), lit(0), shares), 0),
            tree_fold(tree(t), lit(0), lazy),
        )
    });
    assert_eq!((a, b), (Ok(Value::Int(0)), Ok(Value::Int(12))));
}

/// A table of seeds `k -> c(k)`: the layer `(v, sl, sr)`, with -1 for no child seed, or the
/// failure member `#notFound` (`None`).
type Seeds = Vec<Option<(i64, i64, i64)>>;

fn seed_table(s: &Seeds) -> Term {
    let entries = s.iter().enumerate().map(|(k, c)| {
        let c = match *c {
            Some((v, l, r)) => Value::tuple(vec![Value::Int(v), Value::Int(l), Value::Int(r)]),
            None => Value::atom("notFound"),
        };
        (k as i64, c)
    });
    lit(Value::Family(Family::of(entries)))
}

/// Seed tables with values in `0..=2` whose child seeds are greater than their parent, so
/// that every build terminates: each table of three seeds, then 256 random tables of five.
/// With `failures` set, a seed may be the failure member.
fn seed_tables(failures: bool) -> Vec<Seeds> {
    fn layers_at(k: i64, n: i64, failures: bool) -> Vec<Option<(i64, i64, i64)>> {
        let children: Vec<i64> = std::iter::once(-1).chain(k + 1..n).collect();
        let mut out = Vec::new();
        for v in 0..=2 {
            for &l in &children {
                for &r in &children {
                    out.push(Some((v, l, r)));
                }
            }
        }
        if failures {
            out.push(None);
        }
        out
    }
    let mut out = vec![vec![]];
    for k in 0..3 {
        out = out
            .into_iter()
            .flat_map(|s: Seeds| {
                layers_at(k, 3, failures).into_iter().map(move |c| {
                    let mut s = s.clone();
                    s.push(c);
                    s
                })
            })
            .collect();
    }
    let mut rng = Rng::new(2121);
    for _ in 0..256 {
        out.push(
            (0..5)
                .map(|k| rng.pick(&layers_at(k, 5, failures)))
                .collect(),
        );
    }
    out
}

/// `b(0)`, the tree a build unfolds from seed 0, as a node table in preorder; a seed reached
/// twice is unfolded twice. `None` when the build reaches the failure member, so that `b(0)`
/// is the failure.
fn build(s: &Seeds) -> Option<Tree> {
    fn unfold(s: &Seeds, k: i64, out: &mut Tree) -> Option<i64> {
        let (v, sl, sr) = s[k as usize]?;
        let at = out.len();
        out.push((v, -1, -1));
        if sl >= 0 {
            out[at].1 = unfold(s, sl, out)?;
        }
        if sr >= 0 {
            out[at].2 = unfold(s, sr, out)?;
        }
        Some(at as i64)
    }
    let mut out = Vec::new();
    unfold(s, 0, &mut out).map(|_| out)
}

/// `b(0).fold(alg)`: the fold of the built tree, or the failure itself, since `.fold` passes
/// a failure of its subject through.
fn fold_of_build(s: &Seeds, alg: fn(Term, Term, Term) -> Term) -> Term {
    match build(s) {
        Some(t) => tree_fold(tree(&t), lit(0), alg),
        None => atom("notFound"),
    }
}

/// `go(0)` with `go(s) = alg(F(go)(c(s)))`, as the definedness fix over the seeds: the
/// failure member has no recursive position, so `F(go)` passes it through, and `alg` sees a
/// child's failure as data.
fn on_seeds(s: Term, alg: fn(Term, Term, Term) -> Term) -> Term {
    let table = s.clone();
    let all = fix_defined(s, |this, k| {
        let c = get(table, k);
        let child = |x: Term| if_(eq(x.clone(), lit(-1)), lit(0), get(this.clone(), x));
        unless_atom(
            c.clone(),
            alg(
                nth(c.clone(), 0),
                child(nth(c.clone(), 1)),
                child(nth(c, 2)),
            ),
        )
    });
    get(all, lit(0))
}

/// `alg` that reads past a failing child: `(l else 0) + (r else 0) + 12 div v`.
fn lazy_alg(v: Term, l: Term, r: Term) -> Term {
    add(add(or(l, 0), or(r, 0)), idiv(lit(12), v))
}

#[test]
fn law_21_the_build_clause_needs_alg_strict_only_with_a_failure_member() {
    // Seeds are the parts of an assembly, each with its weight `v` and up to two sub-parts;
    // `go` totals a part's weight without building the assembly tree.
    let strict = |v: Term, l: Term, r: Term| add(add(v, l), r);
    // With a failure member (a part missing from the catalog), a strict `alg` passes the
    // failure up exactly as the build does.
    let n = holds(seed_tables(true), |s| {
        (fold_of_build(s, strict), on_seeds(seed_table(s), strict))
    });
    assert_eq!(n, 28 * 13 * 4 + 256);
    // A non-strict one does not: the build fails as a whole, while `go` reads past the
    // failing child, to a number or to a failure of its own (`12 div 0`).
    let (s, a, b) = refuted(seed_tables(true), |s| {
        (
            fold_of_build(s, lazy_alg),
            on_seeds(seed_table(s), lazy_alg),
        )
    });
    assert!(build(&s).is_none());
    assert_eq!(a, Ok(Value::atom("notFound")));
    assert_ne!(b, a);
    // Without a failure member the build clause holds for that same non-strict `alg`, a
    // failure `alg` itself makes (`12 div 0`) included: the build gives no atom, and `alg`
    // sees the same children on both sides. The strictness of `alg` matters only when the
    // result type of `b` has a failure member, which the build clause (sec:type_language) excludes.
    let n = holds(seed_tables(false), |s| {
        (
            fold_of_build(s, lazy_alg),
            on_seeds(seed_table(s), lazy_alg),
        )
    });
    assert_eq!(n, 27 * 12 * 3 + 256);
}

#[test]
fn law_21_the_build_clause_needs_termination_evidence() {
    // A part listed as its own sub-part: the build never finishes, so the definedness fix that
    // builds the assembly stalls, while `go` with an `alg` that reads no child gives a value.
    let cyclic: Seeds = vec![Some((1, 0, -1))];
    let (_, a, b) = refuted(vec![cyclic], |s| {
        let table = seed_table(s);
        let built = {
            let t = table.clone();
            fix_defined(table.clone(), |this, k| {
                let c = get(t, k);
                let child = |x: Term| if_(eq(x.clone(), lit(-1)), lit(true), get(this.clone(), x));
                unless_atom(c.clone(), and(child(nth(c.clone(), 1)), child(nth(c, 2))))
            })
        };
        let weight = |v: Term, _: Term, _: Term| v;
        (
            unless_atom(get(built, lit(0)), tree_fold(table.clone(), lit(0), weight)),
            on_seeds(table, weight),
        )
    });
    assert!(matches!(a, Err(KernelError::Stalled { .. })));
    assert_eq!(b, Ok(Value::Int(1)));
}

// Law 22: bisection.

/// The least `xs[i]` with `p(xs[i])`, found by halving the range of ranks `lo..hi`.
fn bisect(xs: Term, p: impl Fn(Term) -> Term) -> Term {
    let n = count(xs.clone());
    let step = func(|[f]| {
        let (lo, hi) = (nth(f.clone(), 0), nth(f, 1));
        let mid = idiv(add(lo.clone(), hi.clone()), lit(2));
        if_(
            p(get(xs.clone(), mid.clone())),
            tuple(vec![lo, mid.clone()]),
            tuple(vec![add(mid, lit(1)), hi]),
        )
    });
    let frames = Term::Gen {
        init: rc(tuple(vec![lit(0), n.clone()])),
        step: rc(step),
        guard: rc(func(|[f]| lt(nth(f.clone(), 0), nth(f, 1)))),
        pos: GuardPos::Before,
    };
    last_frame(frames, |last| {
        let lo = nth(last, 0);
        if_(lt(lo.clone(), n), get(xs.clone(), lo), atom("empty"))
    })
}

/// Each ascending sequence of at most four values in `-3..=3`, with each threshold in
/// `-4..=4`.
fn sorted_with_thresholds() -> Vec<(Vec<i64>, i64)> {
    let values: Vec<i64> = (-3..=3).collect();
    let mut out = Vec::new();
    for xs in shortlex(&values, 4) {
        if xs.windows(2).all(|w| w[0] <= w[1]) {
            for t in -4..=4 {
                out.push((xs.clone(), t));
            }
        }
    }
    out
}

#[test]
fn law_22_a_monotone_predicate_on_a_sorted_level_bisects() {
    // The first delivery slot at or after a requested time, in a sorted timetable.
    let n = holds(sorted_with_thresholds(), |(xs, t)| {
        let at_least = |v: Term| le(lit(*t), v);
        (
            fold(discard_with(seq(xs), |_, v| at_least(v)), first(), None),
            bisect(seq(xs), at_least),
        )
    });
    assert_eq!(n, 330 * 9);
    // `v == t` is not monotone along the order: bisection skips past an equal entry.
    let ((xs, t), _, _) = refuted(sorted_with_thresholds(), |(xs, t)| {
        let equal = |v: Term| eq(v, lit(*t));
        (
            fold(discard_with(seq(xs), |_, v| equal(v)), first(), None),
            bisect(seq(xs), equal),
        )
    });
    assert!(xs.contains(&t));
}

/// `last`: the entry with the greatest key.
fn last() -> Term {
    func(|[_, y]| y)
}

/// The greatest `xs[i]` with `p(xs[i])`, for a `p` that holds on a prefix of the order, found
/// by halving the range of ranks `lo..hi` from the other end: `lo` ends at the first rank
/// where `p` fails.
fn bisect_last(xs: Term, p: impl Fn(Term) -> Term) -> Term {
    let n = count(xs.clone());
    let step = func(|[f]| {
        let (lo, hi) = (nth(f.clone(), 0), nth(f, 1));
        let mid = idiv(add(lo.clone(), hi.clone()), lit(2));
        if_(
            p(get(xs.clone(), mid.clone())),
            tuple(vec![add(mid.clone(), lit(1)), hi]),
            tuple(vec![lo, mid]),
        )
    });
    let frames = Term::Gen {
        init: rc(tuple(vec![lit(0), n])),
        step: rc(step),
        guard: rc(func(|[f]| lt(nth(f.clone(), 0), nth(f, 1)))),
        pos: GuardPos::Before,
    };
    last_frame(frames, |last| {
        let lo = nth(last, 0);
        if_(
            lt(lit(0), lo.clone()),
            get(xs.clone(), sub(lo, lit(1))),
            atom("empty"),
        )
    })
}

#[test]
fn law_22_last_bisects_from_the_other_end_for_a_falling_predicate() {
    // The dearest item within a budget, in a price list sorted by price: `v <= t` holds on a
    // prefix and then fails (↓ along the order).
    let n = holds(sorted_with_thresholds(), |(xs, t)| {
        let at_most = |v: Term| le(v, lit(*t));
        (
            fold(discard_with(seq(xs), |_, v| at_most(v)), last(), None),
            bisect_last(seq(xs), at_most),
        )
    });
    assert_eq!(n, 330 * 9);
    // `v == t` is not monotone along the order: the halving skips past an equal entry.
    let ((xs, t), _, _) = refuted(sorted_with_thresholds(), |(xs, t)| {
        let equal = |v: Term| eq(v, lit(*t));
        (
            fold(discard_with(seq(xs), |_, v| equal(v)), last(), None),
            bisect_last(seq(xs), equal),
        )
    });
    assert!(xs.contains(&t));
}

// Law 23: tupling.

/// The two folds of a level, and the one fold at the pair.
fn tupled(m: Term, sum_id: Option<Term>, max_id: Option<Term>) -> (Term, Term) {
    let pair_id = match (&sum_id, &max_id) {
        (Some(a), Some(b)) => Some(tuple(vec![a.clone(), b.clone()])),
        _ => None,
    };
    let both = func(|[a, b]| {
        tuple(vec![
            add(nth(a.clone(), 0), nth(b.clone(), 0)),
            prim(Prim::Max, vec![nth(a, 1), nth(b, 1)]),
        ])
    });
    let square = |v: Term| mul(v.clone(), v);
    (
        tuple(vec![
            fold(map(m.clone(), square), plus(), sum_id),
            fold(map(m.clone(), |v| sub(lit(0), v)), pf(Prim::Max), max_id),
        ]),
        fold(
            map(m, |v| tuple(vec![square(v.clone()), sub(lit(0), v)])),
            both,
            pair_id,
        ),
    )
}

#[test]
fn law_23_two_folds_of_one_level_are_one_pass() {
    // The sum of squared errors and the largest negative error of a batch, in one pass.
    let nonempty: Vec<_> = super::int_maps(23)
        .into_iter()
        .filter(|m| !m.is_empty())
        .collect();
    assert!(holds(nonempty, |m| tupled(ints(m), None, None)) >= 1_800);
    // On an empty level, the fused fold gives one `#empty` where the pair has two.
    let (m, a, _) = refuted(super::int_maps(23), |m| tupled(ints(m), None, None));
    assert!(m.is_empty());
    assert_eq!(
        a,
        Ok(Value::tuple(vec![
            Value::atom("empty"),
            Value::atom("empty")
        ]))
    );
    // With identities, the empty case is the pair of the two identities.
    let n = holds(super::int_maps(23), |m| {
        tupled(ints(m), Some(lit(0)), Some(lit(-100)))
    });
    assert!(n >= 1_800);
}

#[test]
fn law_23_a_float_component_keeps_its_own_exact_accumulator() {
    // The exact float sum of `fold(+)` is not the canonical-tree sum a fused fold with a
    // pairing operator computes; the fusion keeps the accumulator per component.
    let nonempty = shortlex(&bmc_floats(), 3)
        .into_iter()
        .filter(|xs| !xs.is_empty());
    let (xs, _, _) = refuted(nonempty, |xs| {
        let both = func(|[a, b]| {
            tuple(vec![
                add(nth(a.clone(), 0), nth(b.clone(), 0)),
                add(nth(a, 1), nth(b, 1)),
            ])
        });
        (
            tuple(vec![
                fold(seq(xs), plus(), None),
                fold(seq(xs), plus(), None),
            ]),
            fold(map(seq(xs), |v| tuple(vec![v.clone(), v])), both, None),
        )
    });
    assert_eq!(xs.len(), 3);
}

#[test]
fn law_23_over_a_recursive_union_two_folds_are_one_fold_at_the_pair() {
    // A cost tree's node count and total cost in one traversal.
    let n = holds(trees(), |t| {
        (
            tuple(vec![
                tree_fold(tree(t), lit(0), |_, l, r| add(add(lit(1), l), r)),
                tree_sum(tree(t)),
            ]),
            tree_fold(tree(t), tuple(vec![lit(0), lit(0)]), |v, l, r| {
                tuple(vec![
                    add(add(lit(1), nth(l.clone(), 0)), nth(r.clone(), 0)),
                    add(add(v, nth(l, 1)), nth(r, 1)),
                ])
            }),
        )
    });
    assert!(n > 900);
}

#[test]
fn law_23_a_fold_that_reads_another_fold_is_one_fold_at_the_pair() {
    // The longest chain of reports in an org chart, in nodes, reads each subtree's height:
    // computed against a separate table of heights, and as one fold at (height, longest).
    let n = holds(trees(), |t| {
        let table = tree(t);
        let at = |all: Term, c: Term| if_(eq(c.clone(), lit(-1)), lit(0), get(all, c));
        let max = |a: Term, b: Term| prim(Prim::Max, vec![a, b]);
        let heights = {
            let table = table.clone();
            fix_defined(table.clone(), |this, k| {
                let n = get(table, k);
                add(
                    lit(1),
                    max(at(this.clone(), nth(n.clone(), 1)), at(this, nth(n, 2))),
                )
            })
        };
        let h = fresh("h");
        let longest = {
            let table = table.clone();
            fix_defined(table.clone(), |this, k| {
                let n = get(table, k);
                let (l, r) = (nth(n.clone(), 1), nth(n, 2));
                max(
                    max(at(this.clone(), l.clone()), at(this, r.clone())),
                    add(add(lit(1), at(var(&h), l)), at(var(&h), r)),
                )
            })
        };
        let pair = tree_fold(table, tuple(vec![lit(0), lit(0)]), |_, l, r| {
            let (hl, hr) = (nth(l.clone(), 0), nth(r.clone(), 0));
            tuple(vec![
                add(lit(1), max(hl.clone(), hr.clone())),
                max(max(nth(l, 1), nth(r, 1)), add(add(lit(1), hl), hr)),
            ])
        });
        (let_(&h, heights, get(longest, lit(0))), nth(pair, 1))
    });
    assert!(n > 900);
}

// Law 24: lookup through reduce-by-key.

#[test]
fn law_24_one_class_of_a_reduce_by_key_is_the_fold_of_its_fiber() {
    // Total sales in one region, `v mod 3`, without computing the other regions.
    let region = |v: Term| modulo(v, lit(3));
    let cases: Vec<(Vec<(i64, i64)>, i64)> = partial_maps(&[0, 1, 2, 3], &[-2, -1, 0, 1, 2])
        .into_iter()
        .flat_map(|m| (0..3).map(move |j| (m.clone(), j)))
        .collect();
    let sides = |(m, j): &(Vec<(i64, i64)>, i64)| {
        (
            get(fold_at(group_by(ints(m), region), 2, plus(), None), lit(*j)),
            fold(
                discard_with(ints(m), |_, v| eq(region(v), lit(*j))),
                plus(),
                None,
            ),
        )
    };
    let in_image = |(m, j): &(Vec<(i64, i64)>, i64)| m.iter().any(|e| e.1.rem_euclid(3) == *j);
    let n = holds(cases.iter().filter(|c| in_image(c)).cloned(), sides);
    assert!(n > 2_000);
    // Outside the image the class is absent, while the fiber is an empty level.
    let (_, a, b) = refuted(cases, sides);
    assert_eq!(
        (a, b),
        (Ok(Value::atom("notFound")), Ok(Value::atom("empty")))
    );
}

// Law 25: fix fusion.

/// The row `s` of a relation, as a set of nodes.
fn row(r: Term, s: i64) -> Term {
    row_of(r, lit(s))
}

/// `v · E` for a set of nodes `v`: the successors of the nodes of `v`.
fn successors(v: Term, e: Term) -> Term {
    set_image(v, e)
}

#[test]
fn row_and_successors_give_the_sets_computed_here() {
    // Both sides of law 25 read rows with `row` and step with `successors`: each is checked
    // against the set computed in Rust, on every relation, a missing row 0 included.
    let n = holds(relations(), |pairs| {
        let r0: Vec<i64> = pairs.iter().filter(|p| p.0 == 0).map(|p| p.1).collect();
        let succ: Vec<i64> = (0..N)
            .filter(|&w| pairs.iter().any(|&(v, x)| x == w && r0.contains(&v)))
            .collect();
        let set = |xs: Vec<i64>| lit(Value::Family(Family::of(xs.into_iter().map(|w| (w, true)))));
        let e = relation(pairs);
        (
            prim(
                Prim::Tuple,
                vec![row(e.clone(), 0), successors(row(e.clone(), 0), e)],
            ),
            prim(Prim::Tuple, vec![set(r0), set(succ)]),
        )
    });
    assert_eq!(n, 512 + 256);
}

#[test]
fn law_25_one_row_of_a_closure_is_a_search_from_its_source() {
    // The stations reachable from station 0, without the whole reachability table.
    let n = holds(relations(), |pairs| {
        let e = relation(pairs);
        let step = {
            let e = e.clone();
            func(move |[r]| compose(r, e))
        };
        let search_step = {
            let e = e.clone();
            func(move |[v]| successors(v, e))
        };
        (
            row(fix_lattice(e.clone(), step, pf(Prim::Union)), 0),
            fix_lattice(row(e, 0), search_step, pf(Prim::Union)),
        )
    });
    assert_eq!(n, 512 + 256);
}

/// The sides of the invariant form for the relation `pairs`: on the iterates of
/// `x -> x ∪ E · x` from `E`, `E · x = x · E` holds, and with it the one identity the
/// invariant form needs.
pub(super) fn left_multiplied_invariant(pairs: &[(i64, i64)]) -> (Term, Term) {
    let e = relation(pairs);
    let mut checks = Vec::new();
    let mut binds = Vec::new();
    // Each iterate, `E · x` and the row `x[0]` are bound to names and read by them: written out
    // in place, the checks evaluated `next` once per node of its row and `E · x` twice, and the
    // test took 9.4 ms a relation (TEST-law25-time).
    let mut bind = |stem: &str, t: Term| {
        let name = fresh(stem);
        binds.push((name.clone(), t));
        var(&name)
    };
    let mut xv = bind("x", e.clone());
    for _ in 0..N {
        let ex = bind("ex", compose(e.clone(), xv.clone()));
        let next = bind("x", union(xv.clone(), ex.clone()));
        let commutes = eq(ex, compose(xv.clone(), e.clone()));
        let row0 = bind("row", row(xv, 0));
        let fused = eq(
            row(next.clone(), 0),
            union(row0.clone(), successors(row0, e.clone())),
        );
        checks.push(and(commutes, fused));
        xv = next;
    }
    let all = checks.into_iter().reduce(and).unwrap();
    let term = binds
        .into_iter()
        .rev()
        .fold(all, |body, (name, value)| let_(&name, value, body));
    (term, lit(true))
}

/// The invariant form on every relation on three points, 512 of them (TEST-law25-time), and on
/// the 5 on four points whose index among all 768 is a multiple of 48, which the test checked when
/// it took every 48th; `bench/laws.rs` checks all 768.
#[test]
fn law_25_a_left_multiplied_step_takes_the_invariant_form() {
    // `r[s]` does not commute with `r -> E · r` on every relation.
    let rs = relations();
    let pairs: Vec<_> = (0..rs.len())
        .map(|i| (rs[i].clone(), rs[(i * 7 + 3) % rs.len()].clone()))
        .collect();
    let _ = refuted(pairs, |(e, r)| {
        let (e, r) = (relation(e), relation(r));
        (
            row(compose(e.clone(), r.clone()), 0),
            successors(row(r, 0), e),
        )
    });
    let some: Vec<_> = (relations().into_iter().enumerate())
        .filter(|&(i, _)| i < 512 || i % 48 == 0)
        .map(|(_, r)| r)
        .collect();
    let n = holds(some, |pairs| left_multiplied_invariant(pairs));
    assert_eq!(n, 512 + 5);
}

/// `x · e` for a set `x` and a relation `e` into `0..n`: the image of `x`, as a family of
/// `w -> true`.
fn image(x: Term, e: Term, n: i64) -> Term {
    discard_with(
        fam_with(lit(Value::Family(Family::set(0..n))), |w| {
            let via = discard_with(x, |p, _| found(get(get(e, key(p, 0)), w)));
            lt(lit(0), count(via))
        }),
        |_, b| b,
    )
}

/// The set of the bits of `mask`, as a family of `w -> true`.
fn set_of(mask: u32) -> Term {
    let keys = (0..32).filter(|w| mask & (1 << w) != 0);
    lit(Value::Family(Family::of(keys.map(|w| (w as i64, true)))))
}

/// The relation whose row `u` is the set of the bits of `rows[u]`.
fn relation_of(rows: &[u32]) -> Term {
    let pairs: Vec<(i64, i64)> = rows
        .iter()
        .enumerate()
        .flat_map(|(u, &m)| {
            (0..32)
                .filter(move |w| m & (1 << w) != 0)
                .map(move |w| (u as i64, w))
        })
        .collect();
    relation(&pairs)
}

/// A finite model of fix fusion: `h(x) = x · H` from sets of `0..5` to sets of `0..4`, which
/// preserves unions; the steps `s1(x) = x · E1` on `0..5` and `s2(y) = y · E2` on `0..4`; and
/// a seed `x0`. Rows are bit masks.
#[derive(Clone, Debug)]
struct FixFusion {
    h: [u32; 5],
    e1: [u32; 5],
    e2: [u32; 4],
    x0: u32,
}

/// `x · M` for a set of bits `x` and the rows `m`.
fn image_bits(x: u32, m: &[u32]) -> u32 {
    (0..m.len())
        .filter(|u| x & (1 << u) != 0)
        .fold(0, |a, u| a | m[u])
}

/// 256 random models with `E1 · H = H · E2`, so that `h ∘ s1 = s2 ∘ h`: `H` and `E2` are
/// drawn, and each row `i` of `E1` is the set of `j` with `H[j]` inside row `i` of `H · E2`,
/// kept only when those `H[j]` cover the row.
fn fix_fusions() -> Vec<FixFusion> {
    let mut rng = Rng::new(25);
    let mut out = Vec::new();
    while out.len() < 256 {
        let h: [u32; 5] = std::array::from_fn(|_| rng.below(16) as u32);
        let e2: [u32; 4] = std::array::from_fn(|_| rng.below(16) as u32);
        let e1: [u32; 5] = std::array::from_fn(|i| {
            (0..5)
                .filter(|&j| h[j] & !image_bits(h[i], &e2) == 0)
                .fold(0, |a, j| a | 1 << j)
        });
        if (0..5).all(|i| image_bits(e1[i], &h) == image_bits(h[i], &e2)) {
            out.push(FixFusion {
                h,
                e1,
                e2,
                x0: rng.below(32) as u32,
            });
        }
    }
    out
}

/// The two sides of fix fusion: `h(fix(x0, s1, ∪))` and `fix(h(x0), s2, ∪)`.
fn fix_fusion_sides(m: &FixFusion) -> (Term, Term) {
    let (h, e1, e2) = (relation_of(&m.h), relation_of(&m.e1), relation_of(&m.e2));
    let s1 = func(|[x]| image(x, e1, 5));
    let s2 = func(|[y]| image(y, e2, 4));
    (
        image(fix_lattice(set_of(m.x0), s1, pf(Prim::Union)), h.clone(), 4),
        fix_lattice(image(set_of(m.x0), h, 4), s2, pf(Prim::Union)),
    )
}

#[test]
fn law_25_a_join_homomorphism_that_commutes_with_the_steps_fuses() {
    // The zones a set of stations can reach: `h` maps stations to their fare zones, and a
    // station step maps onto a zone step, so the reachable zones need no station search.
    let n = holds(fix_fusions(), fix_fusion_sides);
    assert_eq!(n, 256);
    // Without `h ∘ s1 = s2 ∘ h` it fails: one more zone link breaks the commuting square.
    let broken = fix_fusions().into_iter().map(|mut m| {
        m.e2[0] |= 1 << 3;
        m
    });
    let (m, _, _) = refuted(broken, fix_fusion_sides);
    assert!((0..5).any(|i| image_bits(m.e1[i], &m.h) != image_bits(m.h[i], &m.e2)));
}

#[test]
fn law_25_a_function_that_commutes_with_the_steps_but_not_the_join_does_not_fuse() {
    // The number of stations reached on a ring line from station 0, with `h = count`, the join
    // `max` on counts and `s2` the identity: a shift round the ring keeps the count, so
    // `h ∘ s1 = s2 ∘ h`, but a count of a union is not the larger count.
    let ring = relation(&[(0, 1), (1, 2), (2, 3), (3, 0)]);
    let shift = |x: Term| image(x, ring.clone(), 4);
    let n = holds(0..16u32, |&x| (count(shift(set_of(x))), count(set_of(x))));
    assert_eq!(n, 16);
    let pairs = (0..16u32).flat_map(|a| (0..16u32).map(move |b| (a, b)));
    let _ = refuted(pairs, |&(a, b)| {
        (
            count(union(set_of(a), set_of(b))),
            prim(Prim::Max, vec![count(set_of(a)), count(set_of(b))]),
        )
    });
    let (_, a, b) = refuted(vec![1u32], |&x0| {
        (
            count(fix_lattice(
                set_of(x0),
                func(|[x]| shift(x)),
                pf(Prim::Union),
            )),
            fix_lattice(count(set_of(x0)), func(|[y]| y), pf(Prim::Max)),
        )
    });
    assert_eq!((a, b), (Ok(Value::Int(4)), Ok(Value::Int(1))));
}

// Law 26: generation fusion.

/// A loan simulation: frames `(month, balance, audit)` from `(0, x0, y0)`, each month adding
/// the month number to the balance and doubling the audit counter; and the projection `h`
/// onto `(month, balance)`.
fn loan(x0: i64, y0: i64, guard: Term) -> Term {
    let step = func(|[f]| {
        tuple(vec![
            add(nth(f.clone(), 0), lit(1)),
            add(nth(f.clone(), 1), nth(f.clone(), 0)),
            mul(nth(f, 2), lit(2)),
        ])
    });
    Term::Gen {
        init: rc(lit(Value::tuple(vec![
            Value::Int(0),
            Value::Int(x0),
            Value::Int(y0),
        ]))),
        step: rc(step),
        guard: rc(guard),
        pos: GuardPos::Before,
    }
}

fn abstract_loan(x0: i64) -> Term {
    let step = func(|[f]| {
        tuple(vec![
            add(nth(f.clone(), 0), lit(1)),
            add(nth(f.clone(), 1), nth(f, 0)),
        ])
    });
    Term::Gen {
        init: rc(lit(Value::tuple(vec![Value::Int(0), Value::Int(x0)]))),
        step: rc(step),
        guard: rc(func(|[f]| lt(nth(f, 0), lit(4)))),
        pos: GuardPos::Before,
    }
}

fn seeds() -> Vec<(i64, i64)> {
    (-2..=2)
        .flat_map(|x| (1..=4).map(move |y| (x, y)))
        .collect()
}

#[test]
fn law_26_a_loop_runs_on_an_abstraction_of_its_state() {
    let h = |f: Term| tuple(vec![nth(f.clone(), 0), nth(f, 1)]);
    let by_month = func(|[f]| lt(nth(f, 0), lit(4)));
    let n = holds(seeds(), |&(x0, y0)| {
        (map(loan(x0, y0, by_month.clone()), h), abstract_loan(x0))
    });
    assert_eq!(n, 20);
    // A guard on the audit counter, which `h` drops, agrees with the month guard only when
    // the counter starts at 1.
    let by_audit = func(|[f]| lt(nth(f, 2), lit(16)));
    let ((_, y0), _, _) = refuted(seeds(), |&(x0, y0)| {
        (map(loan(x0, y0, by_audit.clone()), h), abstract_loan(x0))
    });
    assert_eq!(y0, 2);
}

// Law 27: the update laws of `with`.

/// An inventory record `{"price" -> {item -> n}, "stock" -> {item -> n}}`, as its two maps.
type Record = (Vec<(i64, i64)>, Vec<(i64, i64)>);

/// A `with` path: a field step, then an optional key step.
type UpdatePath = (&'static str, Option<i64>);

fn records() -> Vec<Record> {
    let maps = partial_maps(&[0, 1], &[1, 2]);
    let mut out = Vec::new();
    for p in &maps {
        for s in &maps {
            out.push((p.clone(), s.clone()));
        }
    }
    out
}

fn record(r: &Record) -> Term {
    let mut leaves = Vec::new();
    for (field, m) in [("price", &r.0), ("stock", &r.1)] {
        for &(k, v) in m {
            leaves.push((vec![Value::str(field), Value::Int(k)], Value::Int(v)));
        }
    }
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

fn paths() -> Vec<UpdatePath> {
    let mut out = Vec::new();
    for field in ["price", "stock"] {
        out.push((field, None));
        for k in 0..3 {
            out.push((field, Some(k)));
        }
    }
    out
}

fn steps(p: &UpdatePath) -> Vec<Term> {
    let mut out = vec![lit(Value::str(p.0))];
    out.extend(p.1.map(lit));
    out
}

/// Whether every key step of `p` is present in `r`; a field is present while its map is
/// nonempty, since `record` writes no leaf for an empty map.
fn present(r: &Record, p: &UpdatePath) -> bool {
    let m = if p.0 == "price" { &r.0 } else { &r.1 };
    !m.is_empty() && p.1.is_none_or(|k| m.iter().any(|e| e.0 == k))
}

fn prefix_related(p: &UpdatePath, q: &UpdatePath) -> bool {
    p.0 == q.0 && (p.1.is_none() || q.1.is_none() || p.1 == q.1)
}

/// The value a test writes at `p`: a price list at a field path, a number at a key path.
fn written(p: &UpdatePath, n: i64) -> Term {
    match p.1 {
        Some(_) => lit(n),
        None => lit(Value::Family(Family::of([(0i64, n)]))),
    }
}

fn read(v: Term, p: &[Term]) -> Term {
    p.iter().fold(v, |v, k| get(v, k.clone()))
}

/// `v with { p = a }`: a key step rebuilds its level with the key's entry updated, and is
/// `#missing` where the key is absent. A failure in `v` flows out unchanged.
fn update(v: Term, p: &[Term], a: Term) -> Term {
    let Some((k, rest)) = p.split_first() else {
        return a;
    };
    let inner = update(get(v.clone(), k.clone()), rest, a);
    let level = fam_with(v.clone(), |j| {
        if_(eq(j.clone(), k.clone()), inner, get(v.clone(), j))
    });
    unless_atom(
        v.clone(),
        if_(found(get(v, k.clone())), level, atom("missing")),
    )
}

fn with_paths() -> Vec<(Record, UpdatePath)> {
    records()
        .into_iter()
        .flat_map(|r| paths().into_iter().map(move |p| (r.clone(), p)))
        .collect()
}

fn with_path_pairs() -> Vec<(Record, UpdatePath, UpdatePath)> {
    let mut out = Vec::new();
    for r in records() {
        for p in paths() {
            for q in paths() {
                out.push((r.clone(), p, q));
            }
        }
    }
    out
}

#[test]
fn law_27_reading_back_and_writing_back() {
    let ok = |(r, p): &(Record, UpdatePath)| present(r, p);
    let back = |(r, p): &(Record, UpdatePath)| {
        let a = written(p, 7);
        (read(update(record(r), &steps(p), a.clone()), &steps(p)), a)
    };
    let n = holds(with_paths().into_iter().filter(ok), back);
    assert!(n > 300);
    let write_back = |(r, p): &(Record, UpdatePath)| {
        let v = record(r);
        (update(v.clone(), &steps(p), read(v.clone(), &steps(p))), v)
    };
    holds(with_paths().into_iter().filter(ok), write_back);
    let overwrite = |(r, p): &(Record, UpdatePath)| {
        let v = record(r);
        (
            update(
                update(v.clone(), &steps(p), written(p, 7)),
                &steps(p),
                written(p, 9),
            ),
            update(v, &steps(p), written(p, 9)),
        )
    };
    // Overwriting holds on absent keys too, where both sides are `#missing`.
    assert_eq!(holds(with_paths(), overwrite), 81 * 8);
    // An absent key gives `#missing` there, so neither reading back nor writing back holds.
    let (_, a, _) = refuted(with_paths(), back);
    assert_eq!(a, Ok(Value::atom("missing")));
    let ((r, p), _, _) = refuted(with_paths(), write_back);
    assert!(!present(&r, &p));
}

#[test]
fn law_27_reading_elsewhere_and_commuting_updates() {
    let elsewhere = |(r, p, q): &(Record, UpdatePath, UpdatePath)| {
        let v = record(r);
        (
            read(update(v.clone(), &steps(p), written(p, 7)), &steps(q)),
            read(v, &steps(q)),
        )
    };
    let apart = |(r, p, q): &(Record, UpdatePath, UpdatePath)| {
        present(r, p) && present(r, q) && !prefix_related(p, q)
    };
    let n = holds(with_path_pairs().into_iter().filter(apart), elsewhere);
    assert!(n > 500);
    let commute = |(r, p, q): &(Record, UpdatePath, UpdatePath)| {
        let v = record(r);
        let (a, b) = (written(p, 7), written(q, 9));
        (
            update(
                update(v.clone(), &steps(p), a.clone()),
                &steps(q),
                b.clone(),
            ),
            update(update(v, &steps(q), b), &steps(p), a),
        )
    };
    assert_eq!(
        holds(with_path_pairs().into_iter().filter(apart), commute),
        n
    );
    // Paths that are equal or prefix-related once their keys are evaluated overwrite one
    // another, the outer the inner.
    let related = |(r, p, q): &(Record, UpdatePath, UpdatePath)| {
        present(r, p) && present(r, q) && prefix_related(p, q)
    };
    let ((_, p, q), _, _) = refuted(with_path_pairs().into_iter().filter(related), commute);
    assert!(prefix_related(&p, &q));
}

// Law 28: reversal.

/// `xs` read in the reverse of its order, as the sequence `i -> xs[n - 1 - i]`.
fn rev(xs: Term) -> Term {
    let n = count(xs.clone());
    reindex(
        xs,
        func(|[p, _]| path(vec![sub(sub(n, lit(1)), key(p, 0))])),
        func(|[_, v]| v),
    )
}

#[test]
fn law_28_a_fold_in_sequence_reads_either_direction_with_its_operator_flipped() {
    // A bank balance from a ledger written newest first.
    let minus = pf(Prim::Sub);
    let ledgers = shortlex(&[-2i64, -1, 0, 1, 2], 4);
    let n = holds(ledgers.clone(), |xs| {
        (
            foldl(rev(seq(xs)), lit(100), minus.clone()),
            foldr(seq(xs), flip(minus.clone()), lit(100)),
        )
    });
    assert_eq!(n, 781);
    holds(ledgers.clone(), |xs| {
        (
            foldr(rev(seq(xs)), minus.clone(), lit(0)),
            foldl(seq(xs), lit(0), flip(minus.clone())),
        )
    });
    // `fold` with an associative operator that does not commute: the earliest entry of the
    // reversed ledger is the latest of the ledger.
    holds(ledgers.clone(), |xs| {
        (
            fold(rev(seq(xs)), first(), None),
            fold(seq(xs), flip(first()), None),
        )
    });
    // A tree fold runs on the mirror image of its tree in the other direction, which only
    // associativity makes equal: `-` is not associative.
    let (xs, _, _) = refuted(ledgers, |xs| {
        (
            fold(rev(seq(xs)), minus.clone(), None),
            fold(seq(xs), flip(minus.clone()), None),
        )
    });
    assert!(xs.len() >= 3);
}

#[test]
fn law_28_a_float_canonical_tree_fold_is_not_moved() {
    // A float `+` given as a function, not the primitive, folds on the canonical tree, whose
    // mirror rounds differently.
    let float_add = func(|[x, y]| add(x, y));
    let (xs, _, _) = refuted(shortlex(&bmc_floats(), 3), |xs| {
        (
            fold(rev(seq(xs)), float_add.clone(), None),
            fold(seq(xs), flip(float_add.clone()), None),
        )
    });
    assert_eq!(xs.len(), 3);
}
