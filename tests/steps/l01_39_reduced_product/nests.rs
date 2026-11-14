//! Tests nested in tests: disjunctions, conjunctions, negations and `if`s inside one another,
//! as a scope is narrowed by them (DESIGN.md sec:constraints).
//!
//! - Two tests that together leave no value give an empty scope, whichever comes first.
//! - Grouping and ordering the sides of a disjunction change nothing.
//! - Every point that meets a random nested test is in the narrowed scope (the interpreter is
//!   the oracle), and a scope narrowed by the opposite outcome misses such points, so the
//!   check can fail.
//! - Narrowing is near linear in the number of nested tests; the one family that is not is
//!   stated as hard in COMPLEXITY.md.

use std::collections::BTreeMap;
use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use super::ints;

pub(super) fn var(x: &str) -> Term {
    Term::Var(x.into())
}

pub(super) fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

pub(super) fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn tt(b: bool) -> Term {
    Term::Lit(Value::Bool(b))
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

pub(super) fn and(a: Term, b: Term) -> Term {
    prim(Prim::And, a, b)
}

pub(super) fn or(a: Term, b: Term) -> Term {
    prim(Prim::Or, a, b)
}

/// `a - b >= c`.
pub(super) fn diff_ge(a: &str, b: &str, c: i64) -> Term {
    prim(Prim::Ge, prim(Prim::Sub, var(a), var(b)), int(c))
}

pub(super) fn names(ns: &[&str]) -> Vec<Arc<str>> {
    ns.iter().map(|n| Arc::from(*n)).collect()
}

/// The integers `ns`, each in `-b..=b`.
pub(super) fn boxed(ns: &[&str], b: i64) -> Scope {
    let t = ns
        .iter()
        .map(|n| {
            and(
                prim(Prim::Ge, var(n), int(-b)),
                prim(Prim::Le, var(n), int(b)),
            )
        })
        .reduce(and)
        .expect("one name");
    ints(&names(ns)).assume(&t, true, &Premises::new())
}

fn point(xs: &[(&str, i64)]) -> BTreeMap<Arc<str>, Value> {
    xs.iter()
        .map(|(n, v)| (Arc::from(*n), Value::Int(*v)))
        .collect()
}

/// The values of `x` in `-b..=b` that the scope holds.
fn xs(s: &Scope, b: i64) -> Vec<i64> {
    (-b..=b)
        .filter(|v| !s.bottom && s.get("x").contains(&Value::Int(*v)))
        .collect()
}

#[test]
fn two_tests_that_leave_no_value_give_an_empty_scope_in_either_order() {
    let p = Premises::new();
    // `x != y` then `x == y`: the part of `x != y` is projected again once `x == y` joins it.
    let ne = prim(Prim::Ne, var("x"), var("y"));
    let eq = prim(Prim::Eq, var("x"), var("y"));
    for s in [ints(&names(&["x", "y"])), boxed(&["x", "y"], 20)] {
        assert!(s.assume(&ne, true, &p).assume(&eq, true, &p).bottom);
        assert!(s.assume(&eq, true, &p).assume(&ne, true, &p).bottom);
    }
}

#[test]
fn a_disjunction_then_an_equality_narrows_each_name() {
    // `x - y >= 5 || y - x >= 5`, then `x + y == 0`: `|2x| >= 5`, so `x` is at least 3 away
    // from 0, in either order.
    let p = Premises::new();
    let s = boxed(&["x", "y"], 20);
    let d = or(diff_ge("x", "y", 5), diff_ge("y", "x", 5));
    let e = prim(Prim::Eq, prim(Prim::Add, var("x"), var("y")), int(0));
    let want: Vec<i64> = (-20..=20).filter(|v: &i64| v.abs() >= 3).collect();
    for r in [
        s.assume(&d, true, &p).assume(&e, true, &p),
        s.assume(&e, true, &p).assume(&d, true, &p),
    ] {
        assert!(!r.bottom, "{r}");
        assert_eq!(xs(&r, 20), want, "{r}");
        assert_eq!(r.get("x"), r.get("y"), "{r}");
    }
}

#[test]
fn every_grouping_of_three_sides_gives_the_same_scope() {
    let p = Premises::new();
    let s = ints(&names(&["x", "y", "z"]));
    let a = and(diff_ge("z", "x", -3), {
        prim(Prim::Eq, prim(Prim::Add, var("y"), var("z")), int(-2))
    });
    let b = and(
        prim(Prim::Eq, var("x"), int(0)),
        prim(Prim::Eq, var("y"), int(-2)),
    );
    let c = and(
        prim(Prim::Eq, var("x"), int(3)),
        prim(Prim::Eq, var("y"), int(-3)),
    );
    let (a, b, c) = (&a, &b, &c);
    let forms = [
        or(a.clone(), or(b.clone(), c.clone())),
        or(or(a.clone(), b.clone()), c.clone()),
        or(b.clone(), or(c.clone(), a.clone())),
        or(or(b.clone(), c.clone()), a.clone()),
        or(c.clone(), or(a.clone(), b.clone())),
        or(or(c.clone(), a.clone()), b.clone()),
        or(c.clone(), or(b.clone(), a.clone())),
        or(a.clone(), or(c.clone(), b.clone())),
    ];
    let held = |t: &Term| -> Vec<bool> {
        let r = s.assume(t, true, &p);
        let g = -6..=6;
        g.clone()
            .flat_map(|x| {
                g.clone()
                    .flat_map(move |y| (-6..=6).map(move |z| (x, y, z)))
            })
            .map(|(x, y, z)| r.contains(&point(&[("x", x), ("y", y), ("z", z)])))
            .collect()
    };
    let first = held(&forms[0]);
    for f in &forms[1..] {
        assert!(held(f) == first, "{f}");
    }
    // A point in no side is in no scope: the join states the bounds of each side.
    let r = s.assume(&forms[0], true, &p);
    assert!(
        !r.contains(&point(&[("x", -5), ("y", -5), ("z", -5)])),
        "{r}"
    );
}

/// A random test over `x`, `y`, `z`: comparisons, sums, differences and remainders, under
/// `||`, `&&`, `!` and `if`, with `if`s inside disjunctions.
fn random_nest(rnd: &mut Rng, depth: usize) -> Term {
    let ns = ["x", "y", "z"];
    let (a, b) = (var(ns[rnd.below(3)]), var(ns[rnd.below(3)]));
    let c = int(rnd.int(-3, 3));
    if depth == 0 || rnd.below(4) == 0 {
        return match rnd.below(5) {
            0 => prim(Prim::Eq, a, c),
            1 => prim(Prim::Ge, a, c),
            2 => prim(Prim::Ge, prim(Prim::Sub, a, b), c),
            3 => prim(Prim::Eq, prim(Prim::Add, a, b), c),
            _ => prim(
                Prim::Eq,
                prim(Prim::Mod, a, int(rnd.int(2, 4))),
                int(rnd.int(0, 1)),
            ),
        };
    }
    let (l, r) = (random_nest(rnd, depth - 1), random_nest(rnd, depth - 1));
    match rnd.below(5) {
        0 | 1 => or(l, r),
        2 => and(l, r),
        3 => Term::Prim(Prim::Not, vec![l]),
        _ => {
            let c = random_nest(rnd, depth - 1);
            let then = if rnd.below(2) == 0 { tt(true) } else { l };
            or(if_(c, then, r), random_nest(rnd, 0))
        }
    }
}

/// The value of the test `t` at `env`, by the interpreter.
fn at(t: &Term, env: &BTreeMap<Arc<str>, Value>) -> Option<bool> {
    let t = env.iter().fold(t.clone(), |b, (n, v)| {
        Term::Let(n.clone(), Shared::new(Term::Lit(v.clone())), Shared::new(b))
    });
    match Evaluator::new(World::new()).run(&t) {
        Ok(Value::Bool(b)) => Some(b),
        _ => None,
    }
}

/// The points of the cube `-b..=b` at which `t` has the outcome `o`.
fn meeting(t: &Term, o: bool, b: i64) -> Vec<BTreeMap<Arc<str>, Value>> {
    let mut pts = Vec::new();
    for x in -b..=b {
        for y in -b..=b {
            for z in -b..=b {
                let e = point(&[("x", x), ("y", y), ("z", z)]);
                if at(t, &e) == Some(o) {
                    pts.push(e);
                }
            }
        }
    }
    pts
}

#[test]
fn every_point_that_meets_a_nested_test_is_in_its_scope() {
    const B: i64 = 3;
    let p = Premises::new();
    let base = boxed(&["x", "y", "z"], B);
    let mut rnd = Rng::new(0x57);
    let (mut checked, mut caught, mut empty) = (0, 0, 0);
    for _ in 0..200 {
        let depth = rnd.int(1, 4) as usize;
        let t = random_nest(&mut rnd, depth);
        let o = rnd.below(2) == 0;
        let pts = meeting(&t, o, B);
        let r = base.assume(&t, o, &p);
        for e in &pts {
            assert!(r.contains(e), "{t} is {o} at {e:?}, outside\n{r}");
        }
        checked += pts.len();
        empty += usize::from(r.bottom);
        // Negative control: the scope of the opposite outcome misses some point that
        // meets the test, unless the test has one outcome over the whole cube.
        let q = base.assume(&t, !o, &p);
        caught += usize::from(pts.iter().any(|e| !q.contains(e)));
    }
    assert!(checked > 10_000, "{checked} points checked");
    assert!(
        caught > 100,
        "the opposite outcome missed points in {caught} tests"
    );
    assert!(empty > 5, "{empty} empty scopes");
}

#[test]
fn the_order_of_the_sides_of_a_disjunction_changes_nothing() {
    let p = Premises::new();
    let s = ints(&names(&["x", "y", "z"]));
    let mut rnd = Rng::new(0x58);
    let right = |v: &[Term]| {
        v.iter()
            .cloned()
            .rev()
            .reduce(|a, c| or(c, a))
            .expect("sides")
    };
    let left = |v: &[Term]| v.iter().cloned().reduce(or).expect("sides");
    let same = |a: &Scope, b: &Scope| {
        a.bottom == b.bottom && ["x", "y", "z"].iter().all(|n| a.get(n) == b.get(n))
    };
    for _ in 0..100 {
        let sides: Vec<Term> = (0..4).map(|_| random_nest(&mut rnd, 1)).collect();
        let first = s.assume(&right(&sides), true, &p);
        assert!(same(&first, &s.assume(&left(&sides), true, &p)));
        for _ in 0..6 {
            let mut v = sides.clone();
            for i in (1..v.len()).rev() {
                v.swap(i, rnd.below(i + 1));
            }
            let q = s.assume(&right(&v), true, &p);
            assert!(same(&first, &q), "{}\n{first}\n{q}", right(&v));
        }
    }
}

/// `x0 == 0 || x0 == 1 || … || x0 == k-1`, grouped to the right.
fn or_nest(k: usize) -> Term {
    (0..k as i64 - 1)
        .rev()
        .fold(prim(Prim::Eq, var("x0"), int(k as i64 - 1)), |t, i| {
            or(prim(Prim::Eq, var("x0"), int(i)), t)
        })
}

/// `if x0 - y >= k-1 { true } else if … else { x0 - y >= 0 }`.
fn if_chain(k: usize) -> Term {
    (1..k as i64).fold(diff_ge("x0", "y", 0), |t, i| {
        if_(diff_ge("x0", "y", i), tt(true), t)
    })
}

/// `if x0 >= 0 { if x0 >= 2 { … } else { true } } else { false }`: thresholds with
/// alternating outcomes.
fn thresholds(k: usize) -> Term {
    (0..k as i64).rev().fold(tt(false), |t, i| {
        if_(prim(Prim::Ge, var("x0"), int(2 * i)), t, tt(i % 2 == 0))
    })
}

/// `k` differences over `k/4 + 2` names, unrelated directions, in one disjunction.
fn pairs(k: usize) -> (Term, Vec<Arc<str>>) {
    let m = k / 4 + 2;
    let ns: Vec<String> = (0..m).map(|i| format!("n{i}")).collect();
    let t = (1..k).fold(diff_ge(&ns[0], &ns[1], 0), |t, i| {
        let (a, b) = (i % m, (i * 7 + 1) % m);
        let b = if a == b { (b + 1) % m } else { b };
        or(t, diff_ge(&ns[a], &ns[b], (i % 5) as i64))
    });
    (t, ns.iter().map(|n| Arc::from(n.as_str())).collect())
}

/// Times the narrowing of each scope by its test, the two built before the timing.
fn check_built(what: &str, n: usize, build: impl Fn(usize) -> (Scope, Term)) {
    let built: BTreeMap<usize, (Scope, Term)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|k| (k, build(k)))
        .collect();
    scaling::check(what, n, |k| {
        let (s, t) = &built[&k];
        s.assume(t, true, &Premises::new());
    });
}

#[test]
fn a_test_no_value_meets_gives_an_empty_scope_however_it_is_written() {
    // `x != x` is `!(0 == 0)` once `x - x` is taken as 0: a conjunct of no names, which no
    // projection reads, so it is decided when it joins the relation.
    let p = Premises::new();
    let s = boxed(&["x", "y"], 6);
    let never = [
        prim(Prim::Ne, var("x"), var("x")),
        prim(Prim::Lt, var("y"), var("y")),
        and(
            Term::Prim(Prim::Not, vec![prim(Prim::Eq, var("y"), var("y"))]),
            prim(Prim::Lt, var("x"), var("y")),
        ),
    ];
    for t in &never {
        assert!(s.assume(t, true, &p).bottom, "{t}");
    }
    // `x == x` holds everywhere and narrows nothing.
    let always = s.assume(&prim(Prim::Eq, var("x"), var("x")), true, &p);
    assert!(!always.bottom);
    assert_eq!(xs(&always, 6), (-6..=6).collect::<Vec<_>>());
}

/// `t` with `x` and `y` renamed `u` and `v`.
fn renamed(t: &Term) -> Term {
    match t {
        Term::Var(x) if &**x == "x" => var("u"),
        Term::Var(x) if &**x == "y" => var("v"),
        Term::Prim(p, a) => Term::Prim(*p, a.iter().map(renamed).collect()),
        Term::If(c, a, b) => if_(renamed(c), renamed(a), renamed(b)),
        t => t.clone(),
    }
}

/// The values in `-6..=6` that the scope holds for each name; none when it is empty.
fn shown(s: &Scope) -> Vec<Vec<i64>> {
    ["x", "y", "u", "v"]
        .iter()
        .map(|n| {
            (-6..=6)
                .filter(|v| !s.bottom && s.get(n).contains(&Value::Int(*v)))
                .collect()
        })
        .collect()
}

#[test]
fn a_conjunction_of_tests_on_names_apart_narrows_as_the_tests_one_after_the_other() {
    // `a && b`, with `a` on `x` and `y` and `b` on `u` and `v`, says no more than `a` and `b`
    // apart, so it narrows as `a` then `b` do. `a && b` once lost one side: a side whose test
    // has a `mod` or an `if` of integers has no linear relation of the whole test, and the
    // side with cases then kept only the join of its cases.
    let p = Premises::new();
    let s = boxed(&["x", "y", "u", "v"], 6);
    let one = (
        Term::Prim(
            Prim::Ne,
            vec![
                Term::Prim(Prim::Mod, vec![var("y"), int(2)]),
                Term::Prim(
                    Prim::Neg,
                    vec![Term::Prim(Prim::Add, vec![var("x"), var("x")])],
                ),
            ],
        ),
        Term::Prim(
            Prim::Not,
            vec![if_(
                prim(Prim::Ne, var("u"), var("u")),
                prim(Prim::Ge, var("u"), var("v")),
                prim(Prim::Eq, var("u"), var("u")),
            )],
        ),
    );
    let mut r = Rng::new(0xd15);
    let mut cases = vec![one];
    for _ in 0..400 {
        let a = zed_tests::step_helpers::l01_38_presburger::bool_term(&mut r, 2);
        let b = renamed(&zed_tests::step_helpers::l01_38_presburger::bool_term(
            &mut r, 2,
        ));
        cases.push((a, b));
    }
    let mut narrowed = 0;
    let mut same = 0;
    for (a, b) in &cases {
        let both = s.assume(&and(a.clone(), b.clone()), true, &p);
        let apart = s.assume(a, true, &p).assume(b, true, &p);
        // Never wider; it may be narrower, since inside the conjunction a test such as `y != 3`
        // joins the relation, which cuts the hole that the test alone does not.
        let (w, n) = (shown(&both), shown(&apart));
        assert!(
            w.iter()
                .zip(&n)
                .all(|(w, n)| w.iter().all(|v| n.contains(v))),
            "{a} && {b}: {w:?} is wider than {n:?}"
        );
        same += usize::from(w == n);
        narrowed += usize::from(shown(&both) != shown(&s));
    }
    assert!(
        cases[0..1]
            .iter()
            .all(|(a, b)| s.assume(&and(a.clone(), b.clone()), true, &p).bottom)
    );
    assert!(narrowed > 200, "{narrowed} of {} narrow", cases.len());
    assert!(same > 350, "{same} of {} are the same", cases.len());
}

mod bench;
