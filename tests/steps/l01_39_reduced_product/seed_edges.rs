//! The projection by shortest paths reads, at each seed, only the edges of the conjuncts added
//! and, at a seed whose product changed since the last projection or that a block of another
//! tree moved, the edges into it; its search starts only from those seeds and the ones it
//! lowered (`Scope::bound_pass`, item NARROW-hub-seed-edges). Every other edge held at the
//! fixed point the last projection left. Each test here takes one way a bound can come to
//! move after that fixed point, and checks the scope against the same steps projected from
//! scratch (`Scope::forget_projections`), block by block, which reads every edge.

use std::sync::Arc;

use zed_kernel::{Prim, Shared, Term};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::interval::End;
use zedc::store::product::{Product, Scope};

use super::ints;
use super::linked::stars_by_definition;
use super::nests::{diff_ge, int, names, prim, var};

/// `a - b == c`.
fn diff_eq(a: &str, b: &str, c: i64) -> Term {
    prim(Prim::Eq, prim(Prim::Sub, var(a), var(b)), int(c))
}

fn ge(a: &str, c: i64) -> Term {
    prim(Prim::Ge, var(a), int(c))
}

fn le(a: &str, c: i64) -> Term {
    prim(Prim::Le, var(a), int(c))
}

/// The ends of `n`'s integers in `s`, settled (`Scope::settled`), `None` for an end that is infinite; `None` for a scope
/// no state reaches.
fn ends(s: &Scope, n: &str) -> Option<(Option<i64>, Option<i64>)> {
    if s.bottom {
        return None;
    }
    let p = s.settled(&Arc::from(n));
    let (lo, hi) = p.ints().bounds()?;
    let fin = |e: &End| match e {
        End::Fin(v) => v.to_i64(),
        _ => None,
    };
    Some((fin(lo), fin(hi)))
}

/// The integers of every name in `ns`, settled, or `None` when no state reaches `s`.
fn intervals(s: &Scope, ns: &[Arc<str>]) -> Option<Vec<String>> {
    if s.bottom {
        return None;
    }
    Some(
        ns.iter()
            .map(|n| format!("{n}: {:?}", s.settled(n).ints()))
            .collect(),
    )
}

/// `step` on `s` as it is, and on `s` with its projections forgotten, projected again from
/// scratch: the two must agree at every name of `ns`. The scope `step` gives.
fn agrees(s: &Scope, ns: &[Arc<str>], what: &str, step: impl Fn(&Scope) -> Scope) -> Scope {
    let got = step(s);
    let mut fresh = s.clone();
    fresh.forget_projections();
    let mut want = step(&fresh);
    want.forget_projections();
    want.reduce();
    assert_eq!(
        intervals(&got, ns),
        intervals(&want, ns),
        "{what}: incremental against from scratch"
    );
    got
}

/// The integers `ns`, each in `0..=10`.
fn within(ns: &[&str]) -> Scope {
    let p = Premises::new();
    let mut s = ints(&names(ns));
    for n in ns {
        s = s.assume(&ge(n, 0), true, &p).assume(&le(n, 10), true, &p);
    }
    s
}

#[test]
fn a_conjunct_added_beside_an_older_one_moves_its_names() {
    // x and y in 0..=10, z in 0..=4, and the older conjunct y <= z, which held at the last
    // projection: y in 0..=4. The test y - x >= 3 moves x to 0..=1 and y to 3..=4. Its atom
    // narrows both names by preimage before the projection, so they are changed seeds, and
    // the projection reads its edges both as a conjunct added and as edges into those seeds.
    let p = Premises::new();
    let ns = names(&["x", "y", "z"]);
    let s = within(&["x", "y", "z"]).assume(&le("z", 4), true, &p);
    let s = s.assume(&diff_ge("z", "y", 0), true, &p);
    assert_eq!(ends(&s, "y"), Some((Some(0), Some(4))));
    let s = agrees(&s, &ns, "y - x >= 3", |s| {
        s.assume(&diff_ge("y", "x", 3), true, &p)
    });
    assert_eq!(ends(&s, "x"), Some((Some(0), Some(1))));
    assert_eq!(ends(&s, "y"), Some((Some(3), Some(4))));
}

#[test]
fn an_equality_added_moves_both_its_names_on_both_sides() {
    // An equality is two edges, one each way. With x in 3..=10 and y in 0..=6, x == y + 1
    // moves x down by the edge from y and y up by the edge from x: x in 3..=7, y in 2..=6.
    // Written the other way round, y + 1 == x, the two edges swap roles. As with any atom,
    // preimage narrows both names first; the projection must agree with it.
    let p = Premises::new();
    let ns = names(&["x", "y"]);
    let base = within(&["x", "y"])
        .assume(&ge("x", 3), true, &p)
        .assume(&le("y", 6), true, &p);
    for (what, t) in [
        ("x - y == 1", diff_eq("x", "y", 1)),
        ("y - x == -1", diff_eq("y", "x", -1)),
    ] {
        let s = agrees(&base, &ns, what, |s| s.assume(&t, true, &p));
        assert_eq!(ends(&s, "x"), Some((Some(3), Some(7))), "{what}");
        assert_eq!(ends(&s, "y"), Some((Some(2), Some(6))), "{what}");
    }
}

#[test]
fn a_bound_moved_at_one_reading_reaches_the_others_through_older_equalities() {
    // k readings each equal to the hub n: the hub has 2k edges, none of them added by the test
    // a0 <= 5, which changes a0 alone. n and every other reading are reached only through the
    // older equalities' edges from a0, along the search from the changed name.
    let p = Premises::new();
    let k = 6;
    let reads: Vec<String> = (0..k).map(|i| format!("a{i}")).collect();
    let mut all: Vec<&str> = vec!["n"];
    all.extend(reads.iter().map(String::as_str));
    let ns = names(&all);
    let mut s = within(&all);
    for a in &reads {
        s = agrees(&s, &ns, &format!("{a} == n"), |s| {
            s.assume(&diff_eq(a, "n", 0), true, &p)
        });
    }
    let s = agrees(&s, &ns, "a0 <= 5", |s| s.assume(&le("a0", 5), true, &p));
    let s = agrees(&s, &ns, "a3 >= 2", |s| s.assume(&ge("a3", 2), true, &p));
    for n in &all {
        assert_eq!(ends(&s, n), Some((Some(2), Some(5))), "{n}");
    }
    // A new reading equal to the hub, a name not changed, takes the hub's bounds through the
    // equality's own edges.
    let mut wider = all.clone();
    wider.push("b");
    let ns = names(&wider);
    let mut s = s;
    let b: Arc<str> = "b".into();
    let _ = s.bind(
        &b,
        Product::of_type(zed_kernel::types::Type::int()),
        &Shared::new(Term::Var("b".into())),
    );
    let s = agrees(&s, &ns, "b == n", |s| {
        s.assume(&diff_eq("b", "n", 0), true, &p)
    });
    assert_eq!(ends(&s, "b"), Some((Some(2), Some(5))));
}

#[test]
fn a_cycle_closed_by_a_conjunct_added_through_older_edges_is_empty() {
    // x <= y - 1 and y <= z - 1 are older conjuncts; z <= x closes a cycle of weight -2
    // through them, found only by following the older edges from the names it changes.
    let p = Premises::new();
    let ns = names(&["x", "y", "z"]);
    let s = within(&["x", "y", "z"])
        .assume(&diff_ge("y", "x", 1), true, &p)
        .assume(&diff_ge("z", "y", 1), true, &p);
    assert_eq!(ends(&s, "y"), Some((Some(1), Some(9))));
    let s = agrees(&s, &ns, "x - z >= 0", |s| {
        s.assume(&diff_ge("x", "z", 0), true, &p)
    });
    assert!(s.bottom, "{s}");
    // Unbounded names: only the cycle's weight, not the bounds, says the scope is empty.
    let s =
        ints(&ns)
            .assume(&diff_ge("y", "x", 1), true, &p)
            .assume(&diff_ge("z", "y", 1), true, &p);
    let s = agrees(&s, &ns, "x - z >= 0 unbounded", |s| {
        s.assume(&diff_ge("x", "z", 0), true, &p)
    });
    assert!(s.bottom, "{s}");
}

#[test]
fn a_join_that_raises_a_bound_keeps_what_the_edges_into_it_give() {
    // x <= y + 0 holds on both sides of an `if` on x; the join raises x from 0..=3 (the side
    // taken) to the join of both sides, which the edge from y still bounds. Then y <= 6 moves
    // x again through that older edge.
    let p = Premises::new();
    let ns = names(&["x", "y", "w"]);
    let s = within(&["x", "y", "w"])
        .assume(&le("y", 8), true, &p)
        .assume(&diff_ge("y", "x", 0), true, &p)
        .assume(&diff_ge("w", "y", 0), true, &p);
    let t = le("x", 3);
    let s = agrees(&s, &ns, "join on x <= 3", |s| {
        let mut j = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
        j.reduce();
        j
    });
    assert_eq!(ends(&s, "x"), Some((Some(0), Some(8))));
    let s = agrees(&s, &ns, "y <= 6", |s| s.assume(&le("y", 6), true, &p));
    assert_eq!(ends(&s, "x"), Some((Some(0), Some(6))));
    assert_eq!(ends(&s, "w"), Some((Some(0), Some(10))));
}

#[test]
fn a_conjunct_removed_by_a_join_leaves_its_names_to_the_edges_left() {
    // x <= y holds on one side of an `if` only, so the join keeps a disjunction in its place
    // and the tree is no longer of difference constraints alone at x and y; a later test on
    // y must not move x through the edge that went, and must move z through the one left.
    let p = Premises::new();
    let ns = names(&["x", "y", "z"]);
    let s = within(&["x", "y", "z"]).assume(&diff_ge("z", "y", 0), true, &p);
    let t = diff_ge("y", "x", 0);
    let s = agrees(&s, &ns, "join on y - x >= 0", |s| {
        let mut j = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
        j.reduce();
        j
    });
    let s = agrees(&s, &ns, "y >= 7", |s| s.assume(&ge("y", 7), true, &p));
    assert_eq!(ends(&s, "x"), Some((Some(0), Some(10))));
    assert_eq!(ends(&s, "z"), Some((Some(7), Some(10))));
}

#[test]
fn a_star_that_goes_puts_its_conjuncts_edges_into_the_tree() {
    // In a lazy scope the leaf a of the star a >= n (b >= n gives the hub n more conjuncts
    // than a) is left unsettled when n >= 4 moves the hub. A written constraint on a pins it,
    // so the star goes and its conjunct joins the forest's tree. Writing narrows no product:
    // only that conjunct's edge, made due by the star's going, carries n's bound 4 to a.
    let p = Premises::new();
    let ns = names(&["a", "b", "n"]);
    let narrowed = |s: Scope| {
        s.assume(&diff_ge("a", "n", 0), true, &p)
            .assume(&diff_ge("b", "n", 0), true, &p)
            .assume(&ge("n", 4), true, &p)
    };
    let (eager, lazy) = (narrowed(ints(&ns)), narrowed(ints(&ns).lazy()));
    assert!(
        !stars_by_definition(&lazy.relation).is_empty(),
        "no star: {}",
        lazy.relation
    );
    assert_eq!(ends(&eager, "a"), Some((Some(4), None)));
    // The leaf is stale before the write.
    assert_eq!(
        lazy.get("a").ints().bounds().map(|(lo, _)| lo.clone()),
        Some(End::NegInf)
    );
    let write = |s: &Scope| {
        let mut s = s.clone();
        s.write(ge("a", -100));
        s.reduce();
        s
    };
    for (what, s) in [("eager", &eager), ("lazy", &lazy)] {
        let s = agrees(s, &ns, &format!("{what}: write a >= -100"), write);
        assert_eq!(ends(&s, "a"), Some((Some(4), None)), "{what}");
        assert_eq!(ends(&s, "b"), Some((Some(4), None)), "{what}");
    }
}

#[test]
fn a_hub_moved_by_a_star_moves_its_tree() {
    // The leaf a of the star a <= n, bounded above by 3, moves its hub n through the star's
    // block; n's equality with m in the forest's tree then moves m.
    let p = Premises::new();
    let ns = names(&["a", "n", "m"]);
    let s = ints(&ns)
        .assume(&diff_eq("n", "m", 0), true, &p)
        .assume(&le("n", 10), true, &p)
        .assume(&diff_ge("n", "a", 0), true, &p);
    let s = agrees(&s, &ns, "a >= 3", |s| s.assume(&ge("a", 3), true, &p));
    assert_eq!(ends(&s, "m"), Some((Some(3), Some(10))));
}

/// Random sequences of tests on readings related to one hub by `==`, `<=` and `>=` with an
/// offset, bounds on readings and the hub, ties between readings, `if`s joined and names
/// bound by `let`, each step compared with the projection from scratch.
#[test]
fn random_tests_around_a_hub_give_the_projection_from_scratch() {
    let p = Premises::new();
    let mut r = Rng::new(0x5eed_ed9e);
    let (mut moved, mut empty, mut joined) = (0, 0, 0);
    for case in 0..200 {
        let k = 2 + r.below(6);
        let reads: Vec<String> = (0..k).map(|i| format!("a{i}")).collect();
        let mut all: Vec<String> = vec!["n".into()];
        all.extend(reads.iter().cloned());
        let mut ns: Vec<Arc<str>> = all.iter().map(|n| Arc::from(n.as_str())).collect();
        let mut s = ints(&ns);
        let mut bound = 0;
        let mut trace: Vec<String> = Vec::new();
        for step in 0..3 * k + r.below(3 * k) {
            let a = reads[r.below(k)].clone();
            let b = reads[r.below(k)].clone();
            let c = r.int(-2, 2);
            let t = match r.below(10) {
                0..3 => diff_eq(&a, "n", c),
                3 => diff_ge(&a, "n", c),
                4 => diff_ge("n", &a, c),
                5 => ge(&a, r.int(-8, 8)),
                6 => le(&a, r.int(-8, 8)),
                7 => prim(
                    if r.below(2) == 0 { Prim::Ge } else { Prim::Le },
                    var("n"),
                    int(r.int(-8, 8)),
                ),
                8 if a != b => diff_ge(&a, &b, c),
                9 => {
                    // A `let` of a fresh name, then its equality with the hub.
                    let x = format!("b{bound}");
                    bound += 1;
                    let xa: Arc<str> = x.as_str().into();
                    let q = Product::of_type(zed_kernel::types::Type::int());
                    let _ = s.bind(&xa, q, &Shared::new(Term::Var(xa.clone())));
                    ns.push(xa);
                    diff_eq(&x, "n", c)
                }
                _ => continue,
            };
            let join = r.below(6) == 0;
            let holds = r.below(5) != 0;
            trace.push(format!("{t:?} holds {holds} join {join}"));
            let before = intervals(&s, &ns);
            let got = agrees(
                &s,
                &ns,
                &format!("case {case} step {step}: {trace:#?}"),
                |s| {
                    if join {
                        let mut j = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
                        j.reduce();
                        j
                    } else {
                        s.assume(&t, holds, &p)
                    }
                },
            );
            joined += usize::from(join);
            moved += usize::from(intervals(&got, &ns) != before);
            if got.bottom {
                // The step is dropped, and the sequence goes on from the scope before it.
                empty += 1;
                continue;
            }
            s = got;
        }
    }
    assert!(moved > 1500, "{moved} steps moved an interval");
    assert!(empty > 500, "{empty} steps left no state");
    assert!(joined > 500, "{joined} steps joined both arms");
}
