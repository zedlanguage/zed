//! Laws 21–28 of the catalog: folds over a recursive union, bisection, tupling, lookup
//! through reduce-by-key, fix fusion, generation fusion, the update laws of `with`, and
//! reversal.

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Family, GuardPos, Prim, Term, Value};
use zed_tests::check::{holds, refuted};
use zed_tests::instances::{Rng, bmc_floats, partial_maps, shortlex};
use zed_tests::kernel::*;

use super::laws_11_20::{N, compose, nodes, pf, relation, relations, union};
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
            Value::Tuple(vec![Value::Int(v), Value::Int(l), Value::Int(r)]),
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
        Ok(Value::Tuple(vec![
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
    discard_with(
        fam_with(nodes(), |w| found(get(get(r, lit(s)), w))),
        |_, e| e,
    )
}

/// `v · E` for a set of nodes `v`: the successors of the nodes of `v`.
fn successors(v: Term, e: Term) -> Term {
    discard_with(
        fam_with(nodes(), |w| {
            let via = discard_with(v, |p, _| found(get(get(e, key(p, 0)), w)));
            lt(lit(0), count(via))
        }),
        |_, x| x,
    )
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
    // On the iterates of `x -> x ∪ E · x` from `E`, `E · x = x · E` holds, and with it the
    // one identity the invariant form needs.
    let n = holds(relations(), |pairs| {
        let e = relation(pairs);
        let mut checks = Vec::new();
        let mut x = e.clone();
        let mut binds = Vec::new();
        for _ in 0..N {
            let name = fresh("x");
            binds.push((name.clone(), x));
            let xv = var(&name);
            let next = union(xv.clone(), compose(e.clone(), xv.clone()));
            let commutes = eq(
                compose(e.clone(), xv.clone()),
                compose(xv.clone(), e.clone()),
            );
            let fused = eq(
                row(next.clone(), 0),
                union(row(xv.clone(), 0), successors(row(xv, 0), e.clone())),
            );
            checks.push(and(commutes, fused));
            x = next;
        }
        let all = checks.into_iter().reduce(and).unwrap();
        let term = binds
            .into_iter()
            .rev()
            .fold(all, |body, (name, value)| let_(&name, value, body));
        (term, lit(true))
    });
    assert_eq!(n, 512 + 256);
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
        init: rc(lit(Value::Tuple(vec![
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
        init: rc(lit(Value::Tuple(vec![Value::Int(0), Value::Int(x0)]))),
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
/// nonempty, since an empty level drops its key.
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
