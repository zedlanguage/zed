//! The reduced product's time against the size of the test (the rule of low complexity,
//! DESIGN.md Part G): a conjunction of disjunctions narrows a scope in time near linear in
//! its length.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::images::{self, TermRead};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, LetIn, Lets, let_narrowing, let_summary};
use zedc::store::product::Scope;

use super::ints;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

/// `(x + y >= 0 || x - y >= 0) && (x + y >= 1 || x - y >= 1) && …`, `k` disjunctions.
fn clauses(k: usize) -> Term {
    let clause = |j: i64| {
        let sum = prim(Prim::Add, var("x"), var("y"));
        let diff = prim(Prim::Sub, var("x"), var("y"));
        prim(
            Prim::Or,
            prim(Prim::Ge, sum, int(j)),
            prim(Prim::Ge, diff, int(j)),
        )
    };
    (1..k as i64).fold(clause(0), |a, j| prim(Prim::And, a, clause(j)))
}

#[test]
fn a_scope_keeps_every_clause_of_a_relation() {
    let s = ints(&["x".into(), "y".into()]);
    for k in [1, 4, 40] {
        let r = s.assume(&clauses(k), true, &Premises::new());
        // The two sides of the last clause once each: the relation of the whole test, taken
        // before the scope is narrowed, holds no copy of a side that a case of the split adds
        // again, and no clause that a stronger one on the same two sides implies (clause `j`
        // follows from clause `k - 1`).
        let n = r.relation.cons().len();
        assert!(n == 2, "{k} clauses: {n} constraints in {}", r.relation);
        let mut got: Vec<String> = r.relation.cons().iter().map(|c| c.to_string()).collect();
        got.sort();
        let j = k - 1;
        let diff = if j == 0 {
            "x >= y".to_string()
        } else {
            format!("x >= y + {j}")
        };
        let mut want = vec![format!("x + y >= {j}"), diff];
        want.sort();
        assert_eq!(got, want, "{k} clauses");
        // Every point that meets the test is in the scope.
        for (x, y) in [(40, 0), (0, -40), (39, 0)] {
            let env = [("x".into(), Value::Int(x)), ("y".into(), Value::Int(y))].into();
            let holds = (0..k as i64).all(|j| x + y >= j || x - y >= j);
            assert!(
                !holds || r.contains(&env),
                "{k} clauses: ({x}, {y}) left out"
            );
        }
    }
}

fn arc(t: Term) -> zed_kernel::Shared {
    zed_kernel::Shared::new(t)
}

/// `let x1 = x0 + 1 in … let xk = x(k-1) + 1 in if xk >= 0 { 1 } else { 2 }`.
fn lets(k: usize) -> Term {
    let last = format!("x{k}");
    let mut t = Term::If(
        arc(prim(Prim::Ge, var(&last), int(0))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (1..=k).rev() {
        let prev = format!("x{}", i - 1);
        t = Term::Let(
            format!("x{i}").into(),
            arc(prim(Prim::Add, var(&prev), int(1))),
            arc(t),
        );
    }
    t
}

/// `if x0 >= 0 { if x0 >= 1 { … } else { 0 } } else { 0 }`, `k` deep.
fn ifs(k: usize) -> Term {
    (0..k).rev().fold(int(1), |t, i| {
        Term::If(
            arc(prim(Prim::Ge, var("x0"), int(i as i64))),
            arc(t),
            arc(int(0)),
        )
    })
}

/// `if x >= 0 { let x = x - 100 in if x >= 0 { 1 } else { 2 } } else { 3 }`: the inner `x`
/// is the outer one less 100, so the inner false arm is reached at `x = -100`. What held of
/// the outer `x` does not hold of the inner one.
#[test]
fn a_binding_forgets_what_held_of_the_name_it_shadows() {
    let test = || prim(Prim::Ge, var("x"), int(0));
    let inner = Term::If(arc(test()), arc(int(1)), arc(int(2)));
    let body = Term::Let(
        "x".into(),
        arc(prim(Prim::Sub, var("x"), int(100))),
        arc(inner),
    );
    let t = Term::If(arc(test()), arc(body), arc(int(3)));
    let a = super::arms(&t, &ints(&["x".into()]));
    let shown: Vec<String> = a
        .iter()
        .map(|a| format!("{} {}: {}", a.guard, a.outcome, a.scope))
        .collect();
    assert_eq!(a.len(), 4, "{shown:#?}");
    let reached = &a[2];
    assert!(!reached.outcome, "{shown:#?}");
    assert!(!reached.scope.bottom, "{shown:#?}");
    let at = std::collections::BTreeMap::from([("x".into(), zed_kernel::Value::Int(-100))]);
    assert!(reached.scope.contains(&at), "{shown:#?}");
}

/// `(x1 == 0 && … && xk == 0) || (x1 == 1 && … && xk == 1)`.
fn all_zero_or_all_one(k: usize) -> Term {
    let all = |v: i64| {
        (2..=k).fold(prim(Prim::Eq, var("x1"), int(v)), |a, i| {
            prim(Prim::And, a, prim(Prim::Eq, var(&format!("x{i}")), int(v)))
        })
    };
    prim(Prim::Or, all(0), all(1))
}

/// A random conjunction over `x1`..`x5`: bounds, differences and sums of two names, and
/// disjunctions of two of these, so that the blocks form chains, trees and cycles.
fn random_conjunction(rnd: &mut Rng) -> Term {
    let name = |rnd: &mut Rng| var(&format!("x{}", rnd.int(1, 5)));
    let atom = |rnd: &mut Rng| {
        let rel = rnd.pick(&[Prim::Lt, Prim::Le, Prim::Eq]);
        let (a, b) = (name(rnd), name(rnd));
        match rnd.below(3) {
            0 => prim(rel, a, int(rnd.int(-3, 3))),
            1 => prim(rel, a, prim(Prim::Add, b, int(rnd.int(-2, 2)))),
            _ => prim(rel, prim(Prim::Add, a, b), int(rnd.int(-4, 4))),
        }
    };
    let conjunct = |rnd: &mut Rng| {
        if rnd.below(3) == 0 {
            prim(Prim::Or, atom(rnd), atom(rnd))
        } else {
            atom(rnd)
        }
    };
    let n = rnd.int(2, 7);
    (1..n).fold(conjunct(rnd), |t, _| prim(Prim::And, t, conjunct(rnd)))
}

#[test]
fn projecting_by_blocks_keeps_what_projecting_whole_trees_keeps() {
    let names: Vec<std::sync::Arc<str>> = (1..=5).map(|i| format!("x{i}").into()).collect();
    let s = ints(&names);
    let mut rnd = Rng::new(39);
    let mut empty = 0;
    for _ in 0..zed_tests::instances::RANDOM_INSTANCES {
        let t = random_conjunction(&mut rnd);
        let a = s.assume(&t, true, &Premises::new());
        let (mut blocks, mut whole) = (a.clone(), a);
        blocks.reduce();
        whole.reduce_whole();
        assert_eq!(blocks.bottom, whole.bottom, "{t:?}");
        if blocks.bottom {
            empty += 1;
            continue;
        }
        for x in &names {
            assert_eq!(blocks.get(x), whole.get(x), "{x} in {t:?}");
        }
    }
    // Both kinds of case occur.
    assert!(
        0 < empty && empty < zed_tests::instances::RANDOM_INSTANCES,
        "{empty} empty"
    );
}

#[test]
fn a_cycle_of_strict_orders_is_empty() {
    // x < y and y < x: each bound raises the other without end unless the cycle is seen.
    let s = ints(&["x".into(), "y".into()]);
    let t = prim(
        Prim::And,
        prim(Prim::Lt, var("x"), var("y")),
        prim(Prim::Lt, var("y"), var("x")),
    );
    let mut a = s.assume(&t, true, &Premises::new());
    a.reduce();
    assert!(a.bottom, "{a}");
}

#[test]
fn an_even_number_that_is_odd_is_empty() {
    // c == 2a, c == 2b + 1, c >= 0: no bound is ever tight, only the parity is.
    let s = ints(&["a".into(), "b".into(), "c".into()]);
    let two = |x: &str| prim(Prim::Mul, int(2), var(x));
    let t = prim(
        Prim::And,
        prim(
            Prim::And,
            prim(Prim::Eq, var("c"), two("a")),
            prim(Prim::Eq, var("c"), prim(Prim::Add, two("b"), int(1))),
        ),
        prim(Prim::Le, int(0), var("c")),
    );
    let mut a = s.assume(&t, true, &Premises::new());
    a.reduce();
    assert!(a.bottom, "{a}");
}

/// `let h = (y) -> 2 * y + 1 in if h(x) >= k { k } else if h(x) >= k - 1 { k - 1 } … else { 0 }`:
/// an `else if` chain of `k` tests, each read through the function it calls.
fn helper_chain(k: usize) -> Term {
    let call = || Term::App(arc(var("h")), vec![var("x")]);
    let chain = (1..=k).fold(int(0), |t, i| {
        Term::If(
            arc(prim(Prim::Ge, call(), int(i as i64))),
            arc(int(i as i64)),
            arc(t),
        )
    });
    let h = Term::Lam(
        vec!["y".into()],
        arc(prim(Prim::Add, prim(Prim::Mul, int(2), var("y")), int(1))),
    );
    Term::Let("h".into(), arc(h), arc(chain))
}

/// `let h0 = (y) -> y + 1 in let h1 = (y) -> h0(y) + 1 in let h2 = (y) -> h1(y) + h0(y) in …
/// if hk(x) >= 0 { 1 } else { 2 }`: one test read through `k + 1` functions, each calling the
/// two before it, so a function is reached along many paths.
fn nested_helpers(k: usize) -> Term {
    let name = |i: usize| -> std::sync::Arc<str> { format!("h{i}").into() };
    let call = |f: std::sync::Arc<str>, a: Term| Term::App(arc(Term::Var(f)), vec![a]);
    let mut t = Term::If(
        arc(prim(Prim::Ge, call(name(k), var("x")), int(0))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (0..=k).rev() {
        let body = match i {
            0 => prim(Prim::Add, var("y"), int(1)),
            1 => prim(Prim::Add, call(name(0), var("y")), int(1)),
            _ => prim(
                Prim::Add,
                call(name(i - 1), var("y")),
                call(name(i - 2), var("y")),
            ),
        };
        let f = Term::Lam(vec!["y".into()], arc(body));
        t = Term::Let(name(i), arc(f), arc(t));
    }
    t
}

/// Runs `f` on a thread with a stack deep enough for the nests above (item T2-mid).
fn on_big_stack<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(1 << 28);
        thread.spawn_scoped(s, f).unwrap().join().unwrap()
    })
}

/// `xi - yi >= 1`, or with `or` the test `xi - yi >= 1 || yi - xi >= 1`, for `i` below `k`:
/// tests on names that no other test mentions.
fn apart(k: usize, or: bool) -> (Vec<std::sync::Arc<str>>, Vec<Term>) {
    let ge = |a: &str, b: &str| prim(Prim::Ge, prim(Prim::Sub, var(a), var(b)), int(1));
    let mut names = Vec::new();
    let mut tests = Vec::new();
    for i in 0..k {
        let (x, y) = (format!("x{i}"), format!("y{i}"));
        tests.push(if or {
            prim(Prim::Or, ge(&x, &y), ge(&y, &x))
        } else {
            ge(&x, &y)
        });
        names.push(x.into());
        names.push(y.into());
    }
    (names, tests)
}

/// `let x1 = x0 in let x1 = x1 + 1 in … let xk = x0 in let xk = xk + 1 in if xk >= 1 { 1 }
/// else { 2 }`: each name is bound and then shadowed, so every second binding saves the
/// scope, which then holds up to `k` names.
fn shadows(k: usize) -> Term {
    let last = format!("x{k}");
    let mut t = Term::If(
        arc(prim(Prim::Ge, var(&last), int(1))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (1..=k).rev() {
        let x = format!("x{i}");
        t = Term::Let(
            x.as_str().into(),
            arc(var("x0")),
            arc(Term::Let(
                x.as_str().into(),
                arc(prim(Prim::Add, var(&x), int(1))),
                arc(t),
            )),
        );
    }
    t
}

/// `if x >= 0 { let x = x + 1 in let x = x + 1 in if x >= 2 { 1 } else { 2 } } else { 3 }`:
/// each binding reads the `x` it shadows, so the innermost `x` is at least 2 and the inner
/// false arm is never reached.
#[test]
fn a_binding_that_reads_the_name_it_shadows_keeps_what_held_of_it() {
    let inner = Term::If(
        arc(prim(Prim::Ge, var("x"), int(2))),
        arc(int(1)),
        arc(int(2)),
    );
    let step = |body: Term| {
        Term::Let(
            "x".into(),
            arc(prim(Prim::Add, var("x"), int(1))),
            arc(body),
        )
    };
    let t = Term::If(
        arc(prim(Prim::Ge, var("x"), int(0))),
        arc(step(step(inner))),
        arc(int(3)),
    );
    let a = super::arms(&t, &ints(&["x".into()]));
    let shown: Vec<String> = a
        .iter()
        .map(|a| format!("{} {}: {}", a.guard, a.outcome, a.scope))
        .collect();
    assert_eq!(a.len(), 4, "{shown:#?}");
    assert!(a[1].outcome && !a[1].scope.bottom, "{shown:#?}");
    assert!(!a[2].outcome && a[2].scope.bottom, "{shown:#?}");
}

/// `n{i}`.
fn n(i: usize) -> String {
    format!("n{i}")
}

/// `a * b mod 10 == r`.
fn ends_in(a: &str, b: &str, r: i64) -> Term {
    let ab = prim(Prim::Mul, var(a), var(b));
    prim(Prim::Eq, prim(Prim::Mod, ab, int(10)), int(r))
}

/// The scope under `@exact` of the integers `n0` to `n{k - 1}`, each within `0..=30`.
fn exact_within(k: usize) -> Scope {
    let names: Vec<std::sync::Arc<str>> = (0..k).map(|i| n(i).into()).collect();
    let int_ty = || zedc::store::product::Product::of_type(zed_kernel::types::Type::int());
    let mut s = Scope::exact(names.iter().map(|x| (x.clone(), int_ty())));
    let p = Premises::new();
    for x in &names {
        let from = prim(Prim::Ge, var(x), int(0));
        let to = prim(Prim::Le, var(x), int(30));
        s = s.assume(&prim(Prim::And, from, to), true, &p);
    }
    s
}

/// `scope` with each of `written` written and the scope reduced after each, as a body's
/// constraints are met one by one.
fn reduced_one_by_one(scope: &Scope, written: &[Term]) -> Scope {
    let mut s = scope.clone();
    for c in written {
        s.write(c.clone());
        s.reduce();
    }
    s
}

/// `n{i} * n{i} mod 10 == 9` for `i` below `k`: constraints on names apart.
fn squares_apart(k: usize) -> Vec<Term> {
    (0..k).map(|i| ends_in(&n(i), &n(i), 9)).collect()
}

/// `n{i} * n{i + 1} mod 10 == 1` for `i` below `k`: one group of constraints, linked in a chain.
fn products_in_a_chain(k: usize) -> Vec<Term> {
    (0..k).map(|i| ends_in(&n(i), &n(i + 1), 1)).collect()
}

/// What a scaling test calls a family of constraints, and its constraints by their count.
type Family = (&'static str, fn(usize) -> Vec<Term>);

/// An eager scope of `n`, `m` and `a0`..`a(k-1)` under `n >= -1 && m >= -1` and `k` tests
/// `ai >= n && ai >= m`: `k` stars of the two hubs, each leaf `int[-1..]`.
fn stars_of_two_hubs(k: usize) -> Scope {
    let mut all: Vec<std::sync::Arc<str>> = vec!["n".into(), "m".into()];
    all.extend((0..k).map(|i| format!("a{i}").into()));
    let p = Premises::new();
    let bounds = prim(
        Prim::And,
        prim(Prim::Ge, var("n"), int(-1)),
        prim(Prim::Ge, var("m"), int(-1)),
    );
    (0..k).fold(ints(&all).assume(&bounds, true, &p), |s, i| {
        let a = format!("a{i}");
        let star = prim(
            Prim::And,
            prim(Prim::Ge, var(&a), var("n")),
            prim(Prim::Ge, var(&a), var("m")),
        );
        s.assume(&star, true, &p)
    })
}

/// `n - m <= c`, a test among the hubs of the stars of [`stars_of_two_hubs`].
fn hubs_within(c: i64) -> Term {
    prim(Prim::Le, prim(Prim::Sub, var("n"), var("m")), int(c))
}

/// An eager scope of `n`, `m` and `a0`..`a(k-1)` under `n >= -1 && m >= -1` and, for each
/// `i`, `ai >= 5000` and the star `ai >= n && ai >= m`, or `ai >= n` alone with `one`: `k`
/// stars of the hubs, each leaf `int[5000..]`, above every value the tests below give a hub.
fn stars_above_the_hubs(k: usize, one: bool) -> Scope {
    let mut all: Vec<std::sync::Arc<str>> = vec!["n".into(), "m".into()];
    all.extend((0..k).map(|i| format!("a{i}").into()));
    let p = Premises::new();
    let bounds = prim(
        Prim::And,
        prim(Prim::Ge, var("n"), int(-1)),
        prim(Prim::Ge, var("m"), int(-1)),
    );
    (0..k).fold(ints(&all).assume(&bounds, true, &p), |s, i| {
        let a = format!("a{i}");
        let s = s.assume(&prim(Prim::Ge, var(&a), int(5000)), true, &p);
        let star = if one {
            prim(Prim::Ge, var(&a), var("n"))
        } else {
            prim(
                Prim::And,
                prim(Prim::Ge, var(&a), var("n")),
                prim(Prim::Ge, var(&a), var("m")),
            )
        };
        s.assume(&star, true, &p)
    })
}

/// `k` tests `n <= 1000 + k`, …, `n <= 1001` on `start` in turn, and the nest of `k` `if`s on
/// them: down by each true arm, then each level's false arm joined on the way up.
fn tests_on_a_hub(start: &Scope, k: usize) -> (Scope, Scope) {
    let p = Premises::new();
    let test = |i: usize| prim(Prim::Le, var("n"), int(1000 + (k - i) as i64));
    let one_after_another = (0..k).fold(start.clone(), |s, i| s.assume(&test(i), true, &p));
    let mut levels = vec![start.clone()];
    for i in 0..k {
        let next = levels[i].assume(&test(i), true, &p);
        levels.push(next);
    }
    let mut nest = levels.pop().expect("the innermost level");
    for i in (0..k).rev() {
        nest = nest.join(&levels[i].assume(&test(i), false, &p));
    }
    (one_after_another, nest)
}

/// The tests of [`a_lazy_scope_settles_the_hubs_of_a_class_of_stars_in_linear_time`] at size
/// `k`: `n + m >= 1 || n - m >= 30`, then `k` stars `ai >= n + m - i`, then `k` tests
/// `n >= m - (k - i)` among the hubs, each stronger than the last.
fn a_class_of_stars(k: usize) -> (Scope, Vec<Term>) {
    let sum = || prim(Prim::Add, var("n"), var("m"));
    let diff = || prim(Prim::Sub, var("n"), var("m"));
    let mut tests = vec![prim(
        Prim::Or,
        prim(Prim::Ge, sum(), int(1)),
        prim(Prim::Ge, diff(), int(30)),
    )];
    let star = |i: usize| {
        let leaf = var(&format!("a{i}"));
        prim(Prim::Ge, leaf, prim(Prim::Sub, sum(), int(i as i64)))
    };
    let hub = |i: usize| {
        let bound = prim(Prim::Sub, var("m"), int((k - i) as i64));
        prim(Prim::Ge, var("n"), bound)
    };
    tests.extend((0..k).map(star));
    tests.extend((0..k).map(hub));
    let names: Vec<Arc<str>> = ["n", "m"]
        .into_iter()
        .map(Arc::from)
        .chain((0..k).map(|i| Arc::from(format!("a{i}"))))
        .collect();
    (ints(&names), tests)
}

/// The tests of [`a_lazy_scope_with_many_disjunctions_among_the_hubs_of_a_star_scales`] at
/// size `k`: the star `a >= x + y`, then `k` tests `x + y >= j || x - y >= j` among its hubs.
fn disjunctions_among_the_hubs_of_a_star(k: usize) -> (Scope, Vec<Term>) {
    let sum = || prim(Prim::Add, var("x"), var("y"));
    let diff = || prim(Prim::Sub, var("x"), var("y"));
    let mut tests = vec![prim(Prim::Ge, var("a"), sum())];
    tests.extend((0..k as i64).map(|j| {
        prim(
            Prim::Or,
            prim(Prim::Ge, sum(), int(j)),
            prim(Prim::Ge, diff(), int(j)),
        )
    }));
    let names: Vec<Arc<str>> = ["a", "x", "y"].into_iter().map(Arc::from).collect();
    (ints(&names), tests)
}

/// Assumes the tests of [`disjunctions_among_the_hubs_of_a_star`] at size `k`, in a lazy scope
/// with `lazy`, under [`scaling::check`].
fn disjunctions_scale(what: &str, lazy: bool) {
    let inputs = scaling::inputs(16, |k| {
        let (start, tests) = disjunctions_among_the_hubs_of_a_star(k);
        (if lazy { start.lazy() } else { start }, tests)
    });
    scaling::check(what, 16, |k| {
        let (start, tests) = &inputs[&k];
        let p = Premises::new();
        tests
            .iter()
            .fold(start.clone(), |s, t| s.assume(t, true, &p));
    });
}

/// The star `a >= x + y`, then `k` tests `x + j * y >= 1 || x - j * y >= 1` among its hubs,
/// `j` = 1 to `k`, of which none implies another.
fn distinct_disjunctions_among_the_hubs_of_a_star(k: usize) -> (Scope, Vec<Term>) {
    let mut tests = vec![prim(
        Prim::Ge,
        var("a"),
        prim(Prim::Add, var("x"), var("y")),
    )];
    tests.extend((1..=k as i64).map(|j| {
        let jy = || prim(Prim::Mul, int(j), var("y"));
        prim(
            Prim::Or,
            prim(Prim::Ge, prim(Prim::Add, var("x"), jy()), int(1)),
            prim(Prim::Ge, prim(Prim::Sub, var("x"), jy()), int(1)),
        )
    }));
    let names: Vec<Arc<str>> = ["a", "x", "y"].into_iter().map(Arc::from).collect();
    (ints(&names), tests)
}

/// The scope of `a` and `b` within `0..=100000`, with `a + b <= 150000` and the disjunction
/// `a < 3 || b > 7`, and the `k` tests of [`changes_of_one_block_hold_bounded_memory`]: each
/// tightens `a - b <= c`, and every fourth is followed by an `if a + 2 * b == c` whose arms
/// are joined, its first arm with one more equality in the block.
fn changes_of_one_block(k: usize) -> (Scope, Vec<(Term, bool)>) {
    let p = Premises::new();
    let (a, b) = (|| var("a"), || var("b"));
    let s = ["a", "b"]
        .iter()
        .fold(ints(&["a".into(), "b".into()]), |s: Scope, n| {
            s.assume(&prim(Prim::Ge, var(n), int(0)), true, &p).assume(
                &prim(Prim::Le, var(n), int(100_000)),
                true,
                &p,
            )
        });
    let s = s
        .assume(
            &prim(Prim::Le, prim(Prim::Add, a(), b()), int(150_000)),
            true,
            &p,
        )
        .assume(
            &prim(
                Prim::Or,
                prim(Prim::Lt, a(), int(3)),
                prim(Prim::Gt, b(), int(7)),
            ),
            true,
            &p,
        );
    let mut tests = Vec::new();
    for i in 0..k as i64 {
        let diff = prim(Prim::Sub, a(), b());
        tests.push((prim(Prim::Le, diff, int(100_000 - i)), false));
        if i % 4 == 0 {
            let sum = prim(Prim::Add, a(), prim(Prim::Mul, int(2), b()));
            tests.push((prim(Prim::Eq, sum, int(1000 + i)), true));
        }
    }
    (s, tests)
}

/// Assumes each test of [`changes_of_one_block`] on `s`, joining both arms of those marked.
fn change_one_block(s: &Scope, tests: &[(Term, bool)]) -> Scope {
    let p = Premises::new();
    tests.iter().fold(s.clone(), |s, (t, joined)| {
        if *joined {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        } else {
            s.assume(t, true, &p)
        }
    })
}

/// `a || b`.
fn or(a: Term, b: Term) -> Term {
    prim(Prim::Or, a, b)
}

/// `k` disjunctions on `n`, `m` and `v_i` (`d(v_i)`), each `v_i` in 0..=10 and `n`, `m` in
/// -10^6..=10^6, then `k` tests `t(j)` that move no interval, each tightening the one
/// constraint on a term of `n` and `m`.
fn tightenings_beside_disjunctions(
    k: usize,
    d: impl Fn(&str) -> Term,
    t: impl Fn(i64) -> Term,
) -> (Scope, Vec<(Term, bool)>) {
    const W: i64 = 1_000_000;
    let p = Premises::new();
    let vs: Vec<String> = (0..k).map(|i| format!("v{i}")).collect();
    let mut all: Vec<Arc<str>> = vs.iter().map(|v| Arc::from(v.as_str())).collect();
    all.extend([Arc::from("n"), Arc::from("m")]);
    let within = |s: Scope, x: &str, lo: i64, hi: i64| {
        s.assume(&prim(Prim::Ge, var(x), int(lo)), true, &p).assume(
            &prim(Prim::Le, var(x), int(hi)),
            true,
            &p,
        )
    };
    let mut s = within(within(ints(&all), "n", -W, W), "m", -W, W);
    for v in &vs {
        s = within(s, v, 0, 10).assume(&d(v), true, &p);
    }
    let tests = (1..=k as i64).map(|j| (t(W - 10 - j), false)).collect();
    (s, tests)
}

/// `let z = x1 + … + xk in if x1 >= 0 { let w1 = z + 1 in if x2 >= 0 { let w2 = z + 2 in … } }`,
/// ending in `if wk >= 0 { 1 } else { 2 }`: each binding reads the summary of `z`, over `k`
/// inputs, one more of them narrowed since the last read.
fn sums_read_as_inputs_narrow(k: usize) -> (Vec<Arc<str>>, Term) {
    let names: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
    let mut t = Term::If(
        arc(prim(Prim::Ge, var(&format!("w{k}")), int(0))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (1..=k).rev() {
        let x = format!("x{i}");
        let on_z = Term::Let(
            format!("w{i}").into(),
            arc(prim(Prim::Add, var("z"), int(i as i64))),
            arc(t),
        );
        t = Term::If(arc(prim(Prim::Ge, var(&x), int(0))), arc(on_z), arc(int(0)));
    }
    let sum = (2..=k).fold(var("x1"), |s, i| prim(Prim::Add, s, var(&format!("x{i}"))));
    (names, Term::Let("z".into(), arc(sum), arc(t)))
}

/// `if x1 >= 0 { if x1 <= 1 { … t … } else { -1 } } else { -1 }`: each `xi` of `1..=k` in
/// `0..=1` around `t`.
fn in_bits(k: usize, mut t: Term) -> Term {
    for i in (1..=k).rev() {
        let x = format!("x{i}");
        t = Term::If(
            arc(prim(Prim::Ge, var(&x), int(0))),
            arc(Term::If(
                arc(prim(Prim::Le, var(&x), int(1))),
                arc(t),
                arc(int(-1)),
            )),
            arc(int(-1)),
        );
    }
    t
}

/// `if test(1) { if test(2) { … if test(k) { 0 } else { k } … } else { 2 } } else { 1 }`.
fn nested(k: usize, test: impl Fn(usize) -> Term) -> Term {
    (1..=k).rev().fold(int(0), |t, i| {
        Term::If(arc(test(i)), arc(t), arc(int(i as i64)))
    })
}

/// `x1 + … + xk`.
fn sum_of(k: usize) -> Term {
    (2..=k).fold(var("x1"), |s, i| prim(Prim::Add, s, var(&format!("x{i}"))))
}

/// `if x1 >= 0 { if x1 <= 1 { … let z = x1 + … + xk in if z >= 1 { if z >= 2 { … if z >= k
/// { 0 } else { k } … } else { 2 } } else { 1 } … } else { -1 } } else { -1 }`: each `xi` in
/// `0..=1`, then `k` tests of `z`, a name over `k` inputs, each arm reachable.
fn tests_of_one_sum(k: usize) -> (Vec<Arc<str>>, Term) {
    let names: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
    let tests = nested(k, |i| prim(Prim::Ge, var("z"), int(i as i64)));
    let t = Term::Let("z".into(), arc(sum_of(k)), arc(tests));
    (names, in_bits(k, t))
}

/// The scope of `z0 + … + z(k-1) >= 0` and the `k` tests `a_i_u + a_i_v + a_i_w >= 0` that
/// follow it, each on three inputs of its own, written so that each test's conjunct comes
/// after every earlier one in the order of the parts' keys and before the sum.
fn parts_beside_a_wide_part(k: usize) -> (Scope, Vec<Term>) {
    let p = Premises::new();
    let wide: Vec<Arc<str>> = (0..k).map(|j| format!("z{j}").into()).collect();
    let small: Vec<[Arc<str>; 3]> = (0..k)
        .map(|i| ["u", "v", "w"].map(|x| format!("a{i:06}_{x}").into()))
        .collect();
    let names: Vec<Arc<str>> = wide
        .iter()
        .cloned()
        .chain(small.iter().flatten().cloned())
        .collect();
    let sum = |xs: &[Arc<str>]| {
        xs[1..]
            .iter()
            .fold(var(&xs[0]), |t, x| prim(Prim::Add, t, var(x)))
    };
    let s = ints(&names).assume(&prim(Prim::Ge, sum(&wide), int(0)), true, &p);
    let tests = small
        .iter()
        .map(|xs| prim(Prim::Ge, sum(xs), int(0)))
        .collect();
    (s, tests)
}

/// `t0 && t1 && …` as a balanced tree, so its depth is that of a binary tree of the tests.
fn all_of(tests: &[Term]) -> Term {
    match tests {
        [t] => t.clone(),
        _ => {
            let (a, b) = tests.split_at(tests.len() / 2);
            prim(Prim::And, all_of(a), all_of(b))
        }
    }
}

/// The names `z0` to `z(k-1)`, the sum `z0 + … + z(k-1)`, and the tests `0 <= zj <= 3` and
/// `z0 + … + z(k-1) >= 3·k - 1`.
fn wide_sum(k: usize) -> (Vec<Arc<str>>, Term, Term) {
    let names: Vec<Arc<str>> = (0..k).map(|j| format!("z{j}").into()).collect();
    let sum = (names[1..].iter()).fold(var(&names[0]), |t, x| prim(Prim::Add, t, var(x)));
    let mut tests: Vec<Term> = Vec::with_capacity(2 * k + 1);
    for x in &names {
        tests.push(prim(Prim::Ge, var(x), int(0)));
        tests.push(prim(Prim::Le, var(x), int(3)));
    }
    tests.push(prim(Prim::Ge, sum.clone(), int(3 * k as i64 - 1)));
    (names, sum, all_of(&tests))
}

/// The scope of `z0 + … + z(k-1) + h >= 0 || g <= -1` and the `k` tests
/// `a_i + h >= 0 || a_i + g <= -5` that follow it: each test shares `h` and `g` with the first
/// disjunction, so all are one block, and `a_i` has both signs, so it is the leaf of no star.
fn disjunctions_beside_a_wide_disjunction(k: usize) -> (Scope, Vec<Term>) {
    let p = Premises::new();
    let wide: Vec<Arc<str>> = (0..k).map(|j| format!("z{j:06}").into()).collect();
    let small: Vec<Arc<str>> = (0..k).map(|i| format!("a{i:06}").into()).collect();
    let names: Vec<Arc<str>> = ["g".into(), "h".into()]
        .into_iter()
        .chain(wide.iter().cloned())
        .chain(small.iter().cloned())
        .collect();
    let sum = wide
        .iter()
        .fold(var("h"), |t, x| prim(Prim::Add, t, var(x)));
    let first = prim(
        Prim::Or,
        prim(Prim::Ge, sum, int(0)),
        prim(Prim::Le, var("g"), int(-1)),
    );
    let s = ints(&names).assume(&first, true, &p);
    let tests = small
        .iter()
        .map(|a| {
            prim(
                Prim::Or,
                prim(Prim::Ge, prim(Prim::Add, var(a), var("h")), int(0)),
                prim(Prim::Le, prim(Prim::Add, var(a), var("g")), int(-5)),
            )
        })
        .collect();
    (s, tests)
}

/// The `k` stars of [`stars_of_two_hubs`] with the hubs at most `100000` and the disjunction
/// `n + m <= -1 || n + m >= 2`, lazy or eager.
fn stars_under_a_disjunction(k: usize, lazy: bool) -> Scope {
    let p = Premises::new();
    let s = stars_of_two_hubs(k);
    let s = if lazy { s.lazy() } else { s };
    let sum = || prim(Prim::Add, var("n"), var("m"));
    let tests = [
        prim(Prim::Le, var("n"), int(100_000)),
        prim(Prim::Le, var("m"), int(100_000)),
        prim(
            Prim::Or,
            prim(Prim::Le, sum(), int(-1)),
            prim(Prim::Ge, sum(), int(2)),
        ),
    ];
    tests.iter().fold(s, |s, t| s.assume(t, true, &p))
}

mod bench;
