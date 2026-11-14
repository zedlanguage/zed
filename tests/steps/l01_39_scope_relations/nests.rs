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
    let (mut rnd, seed) = Rng::fresh("every_point_that_meets_a_nested_test_is_in_its_scope");
    let (mut checked, mut caught, mut empty) = (0, 0, 0);
    for _ in 0..POINT_NESTS {
        let depth = rnd.int(1, 4) as usize;
        let t = random_nest(&mut rnd, depth);
        let o = rnd.below(2) == 0;
        let pts = meeting(&t, o, B);
        let r = base.assume(&t, o, &p);
        for e in &pts {
            assert!(
                r.contains(e),
                "seed {seed}: {t} is {o} at {e:?}, outside\n{r}"
            );
        }
        checked += pts.len();
        empty += usize::from(r.bottom);
        // Negative control: the scope of the opposite outcome misses some point that
        // meets the test, unless the test has one outcome over the whole cube.
        let q = base.assume(&t, !o, &p);
        caught += usize::from(pts.iter().any(|e| !q.contains(e)));
    }
    eprintln!(
        "seed {seed}: {checked} points, {caught} caught, {empty} empty, of {POINT_NESTS} nests"
    );
    // Ten seeds at 40 nests gave 5,268 to 7,299 points and 26 to 34 caught.
    assert!(checked > 3_000, "seed {seed}: {checked} points checked");
    assert!(
        caught > POINT_NESTS / 4,
        "seed {seed}: the opposite outcome missed points in {caught} tests"
    );
    // Empty scopes, about 1 in 12 nests, are too rare for a floor at this count;
    // `a_random_nest_no_point_meets_gives_an_empty_scope` checks one.
}

#[test]
fn the_order_of_the_sides_of_a_disjunction_changes_nothing() {
    let p = Premises::new();
    let s = ints(&names(&["x", "y", "z"]));
    let (mut rnd, seed) = Rng::fresh("the_order_of_the_sides_of_a_disjunction_changes_nothing");
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
    for _ in 0..ORDERS {
        let sides: Vec<Term> = (0..4).map(|_| random_nest(&mut rnd, 1)).collect();
        let first = s.assume(&right(&sides), true, &p);
        assert!(
            same(&first, &s.assume(&left(&sides), true, &p)),
            "seed {seed}: {}",
            left(&sides)
        );
        for _ in 0..6 {
            let mut v = sides.clone();
            for i in (1..v.len()).rev() {
                v.swap(i, rnd.below(i + 1));
            }
            let q = s.assume(&right(&v), true, &p);
            assert!(same(&first, &q), "seed {seed}: {}\n{first}\n{q}", right(&v));
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
    let (mut r, seed) = Rng::fresh("a_conjunction_of_tests_on_names_apart");
    let mut cases = vec![one];
    for _ in 0..CONJUNCTIONS {
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
            "seed {seed}: {a} && {b}: {w:?} is wider than {n:?}"
        );
        same += usize::from(w == n);
        narrowed += usize::from(shown(&both) != shown(&s));
    }
    assert!(
        cases[0..1]
            .iter()
            .all(|(a, b)| s.assume(&and(a.clone(), b.clone()), true, &p).bottom)
    );
    eprintln!(
        "seed {seed}: {narrowed} narrow, {same} the same, of {}",
        cases.len()
    );
    // Ten seeds at 50 pairs gave 41 to 48 narrowed of 51, and all 51 the same.
    assert!(
        narrowed > CONJUNCTIONS / 2,
        "seed {seed}: {narrowed} of {} narrow",
        cases.len()
    );
    assert!(
        same > CONJUNCTIONS * 7 / 8,
        "seed {seed}: {same} of {} are the same",
        cases.len()
    );
}

/// The random nests [`every_point_that_meets_a_nested_test_is_in_its_scope`] draws in a run
/// (was 200 of the seed 0x57, 1.3 s at load 30), the disjunctions whose sides
/// [`the_order_of_the_sides_of_a_disjunction_changes_nothing`] reorders (was 100 of 0x58,
/// 2.1 s), and the pairs of tests
/// [`a_conjunction_of_tests_on_names_apart_narrows_as_the_tests_one_after_the_other`] joins
/// (was 400 of 0xd15, 3.3 s). Each run draws a new seed (author P169).
const POINT_NESTS: usize = 40;
const ORDERS: usize = 15;
const CONJUNCTIONS: usize = 50;

/// The sides of a disjunction grouped to the left, last side first.
fn sides(mut t: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    while let Term::Prim(Prim::Or, v) = t {
        out.push(v[1].clone());
        t = &v[0];
    }
    out.push(t.clone());
    out
}

/// The points of the cube `-b..=b` over `ns`.
fn cube(ns: &[Arc<str>], b: i64) -> Vec<BTreeMap<Arc<str>, Value>> {
    let mut pts = vec![BTreeMap::new()];
    for n in ns {
        pts = pts
            .into_iter()
            .flat_map(|e| {
                (-b..=b).map(move |v| {
                    let mut e = e.clone();
                    e.insert(n.clone(), Value::Int(v));
                    e
                })
            })
            .collect();
    }
    pts
}

/// The nests the benchmarks time, at 4 tests, narrow soundly: every point of the cube
/// `-3..=3` at which the nest is true, by the interpreter, is in the narrowed scope; and the
/// three of one or two names leave out some point at which the nest is false, so the check
/// can fail. (The disjunction of differences of [`pairs`] narrows no name, as
/// [`excluded_sides_change_only_their_names`] checks.)
#[test]
fn the_built_nests_narrow_soundly() {
    const B: i64 = 3;
    let p = Premises::new();
    let (pt, pn) = pairs(4);
    let pn: Vec<&str> = pn.iter().map(|n| &**n).collect();
    let nests = [
        ("or_nest", vec!["x0"], or_nest(4), true),
        ("if_chain", vec!["x0", "y"], if_chain(4), true),
        ("thresholds", vec!["x0"], thresholds(4), true),
        ("pairs", pn, pt, false),
    ];
    for (what, ns, t, cuts) in nests {
        let r = boxed(&ns, B).assume(&t, true, &p);
        let (yes, no): (Vec<_>, Vec<_>) = cube(&names(&ns), B)
            .into_iter()
            .partition(|e| at(&t, e) == Some(true));
        assert!(!yes.is_empty(), "{what}: {t} is never true in the cube");
        for e in &yes {
            assert!(r.contains(e), "{what}: {t} is true at {e:?}, outside\n{r}");
        }
        if cuts {
            assert!(
                no.iter().any(|e| !r.contains(e)),
                "{what}: {t} leaves out no point at which it is false\n{r}"
            );
        }
    }
}

/// The nest of [`pairs`] at k = 8 and 16 narrows no name, and the nest written in the
/// reverse order gives the same scope (the answer the benchmark
/// `excluded_sides_cost_the_names_they_change` checks at 400).
#[test]
fn excluded_sides_change_only_their_names() {
    let p = Premises::new();
    for k in [8, 16] {
        let (t, ns) = pairs(k);
        let s = ints(&ns);
        let q = s.assume(&t, true, &p);
        let reversed = sides(&t).into_iter().reduce(or).expect("sides");
        let r = s.assume(&reversed, true, &p);
        assert!(!q.bottom && !r.bottom, "k = {k}");
        for n in &ns {
            assert_eq!(q.get(n), r.get(n), "k = {k}, {n}");
            assert_eq!(q.get(n), s.get(n), "k = {k}: {n} is narrowed");
        }
    }
}

/// `x - y >= 1 || z - w >= 1` and `y - x >= 1 || w - z >= 1` in `-n..=n`.
fn back_and_forth(n: i64) -> Scope {
    let c = and(
        or(diff_ge("x", "y", 1), diff_ge("z", "w", 1)),
        or(diff_ge("y", "x", 1), diff_ge("w", "z", 1)),
    );
    boxed(&["x", "y", "z", "w"], n).assume(&c, true, &Premises::new())
}

/// The scope of [`back_and_forth`], then `z == w`: the two parts pass a bound back and forth
/// until the box is empty, in one projection of both. Without `z == w` the scope is not
/// empty.
#[test]
fn two_parts_that_pass_a_bound_back_and_forth_reach_the_empty_scope() {
    let zw = prim(Prim::Eq, var("z"), var("w"));
    for n in [10, 100, 1000] {
        let s = back_and_forth(n);
        assert!(!s.bottom, "n = {n}");
        assert!(s.assume(&zw, true, &Premises::new()).bottom, "n = {n}");
    }
}

/// `v_i + w <= 0 || v_(i+1) - w >= 1` for each `i < n - 1`, with `w` in `0..=1` and each
/// `v_i` in `0..=3`: the scope of the bounds, the clauses in order and in reverse, and the
/// last name.
fn walk(n: usize) -> (Scope, Term, Term, String) {
    let p = Premises::new();
    let vs: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
    let mut all: Vec<&str> = vs.iter().map(|s| s.as_str()).collect();
    all.push("w");
    let bounds = all.iter().fold(
        and(
            prim(Prim::Ge, var("w"), int(0)),
            prim(Prim::Le, var("w"), int(1)),
        ),
        |a, v| {
            if *v == "w" {
                a
            } else {
                let b = and(
                    prim(Prim::Ge, var(v), int(0)),
                    prim(Prim::Le, var(v), int(3)),
                );
                and(a, b)
            }
        },
    );
    let s = ints(&names(&all)).assume(&bounds, true, &p);
    let each: Vec<Term> = (0..n - 1)
        .map(|i| {
            or(
                prim(Prim::Le, prim(Prim::Add, var(&vs[i]), var("w")), int(0)),
                diff_ge(&vs[i + 1], "w", 1),
            )
        })
        .collect();
    let clauses = each.iter().cloned().reduce(and).expect("two names");
    let reversed = each.into_iter().rev().reduce(and).expect("two names");
    (s, clauses, reversed, vs[n - 1].clone())
}

/// The clauses of [`walk`], then `v_0 - w >= 1`. Each case of a clause fixes `w`, and every
/// earlier part mentions `w`. The scope reaches the fixed point, which a scope with its
/// projections forgotten and reduced again also reaches, in either order of the clauses and
/// with the start first or last; the last name loses 0.
#[test]
fn a_walk_through_a_shared_name_reaches_the_fixed_point() {
    let p = Premises::new();
    let start = diff_ge("v0", "w", 1);
    for n in [3, 8, 20] {
        let (s, clauses, reversed, last) = walk(n);
        let r = s.assume(&clauses, true, &p).assume(&start, true, &p);
        let mut f = r.clone();
        f.forget_projections();
        f.reduce();
        assert_eq!(r.get(&last), f.get(&last), "n = {n}");
        let back = s.assume(&reversed, true, &p).assume(&start, true, &p);
        assert_eq!(back.get(&last), f.get(&last), "n = {n}, reversed");
        let first = s.assume(&start, true, &p).assume(&clauses, true, &p);
        assert_eq!(first.get(&last), f.get(&last), "n = {n}, start first");
        assert!(
            !r.bottom && !r.get(&last).contains(&Value::Int(0)),
            "n = {n}: {r}"
        );
    }
}

/// A random nest of the seed 0x57 (the seed of
/// [`every_point_that_meets_a_nested_test_is_in_its_scope`] until TEST-bench-move-l0139) that
/// gives an empty scope: no point of the cube meets it, so the empty scope loses none, and
/// the opposite outcome keeps the whole cube's points that meet it.
#[test]
fn a_random_nest_no_point_meets_gives_an_empty_scope() {
    const B: i64 = 3;
    let p = Premises::new();
    let base = boxed(&["x", "y", "z"], B);
    let mut rnd = Rng::new(0x57);
    let found = (0..200).find_map(|_| {
        let depth = rnd.int(1, 4) as usize;
        let t = random_nest(&mut rnd, depth);
        let o = rnd.below(2) == 0;
        base.assume(&t, o, &p).bottom.then_some((t, o))
    });
    let (t, o) = found.expect("an empty scope among 200 nests of the seed 0x57");
    assert!(meeting(&t, o, B).is_empty(), "{t} is {o} at a point");
    let q = base.assume(&t, !o, &p);
    for e in meeting(&t, !o, B) {
        assert!(q.contains(&e), "{t} is {} at {e:?}, outside\n{q}", !o);
    }
}

mod bench;
