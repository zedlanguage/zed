//! Benchmarks of `nests`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn narrowing_by_a_nest_of_disjunctions_scales() {
    let x0 = || ints(&names(&["x0"]));
    check_built("a disjunction of k equalities", 64, |k| (x0(), or_nest(k)));
    check_built("a chain of k `if`s on a difference", 40, |k| {
        (ints(&names(&["x0", "y"])), if_chain(k))
    });
    check_built("k nested thresholds", 50, |k| (x0(), thresholds(k)));
    check_built("k differences over k/4 names", 400, |k| {
        let (t, ns) = pairs(k);
        (ints(&ns), t)
    });
}

/// The nest of [`pairs`] at k = 400 and 3200: each case starts with the sides before it
/// excluded, which change no name, and the cases are joined as a balanced tree, each join
/// putting a disjunction of up to k differences in place of the half it begins with. A case
/// costs the names its sides change and a join the size of what it adds, so the narrowing is
/// O(k log² k) (COMPLEXITY.md C51). The work per side of [`pairs`] is uneven in k (each name
/// `a` is paired with `7a + 1` modulo the `k/4 + 2` names, a graph whose shape changes with
/// that number): measured, k = 400 and 1600 cost more per side than 200, 800 and 3200, so
/// these two sizes favor the larger; the old method still took 18.2 times the work at them,
/// against a limit of 11.9, and fails. The answer is that of the nest written in the reverse
/// order: every name is still unbounded and the scope is not empty.
#[test]
fn excluded_sides_cost_the_names_they_change() {
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Term, Vec<Arc<str>>)> = [400, scaling::FACTOR * 400]
        .into_iter()
        .map(|k| {
            let (t, ns) = pairs(k);
            (k, (ints(&ns), t, ns))
        })
        .collect();
    let (s, t, ns) = &built[&400];
    let q = s.assume(t, true, &p);
    let sides = |mut t: &Term| -> Vec<Term> {
        let mut out = Vec::new();
        while let Term::Prim(Prim::Or, v) = t {
            out.push(v[1].clone());
            t = &v[0];
        }
        out.push(t.clone());
        out
    };
    let reversed = sides(t).into_iter().reduce(or).expect("sides");
    let r = s.assume(&reversed, true, &p);
    assert!(!q.bottom && !r.bottom);
    for n in ns {
        assert_eq!(q.get(n), r.get(n), "{n}");
        assert_eq!(
            q.get(n),
            s.get(n),
            "{n} is narrowed by a disjunction of differences"
        );
    }
    scaling::check_order("k differences over k/4 names", 400, 1, |k| {
        let (s, t, _) = &built[&k];
        s.assume(t, true, &p);
    });
}

/// `x - y >= 1 || z - w >= 1` and `y - x >= 1 || w - z >= 1` in `-n..=n`, then `z == w`:
/// the two parts pass a bound back and forth until the box is empty, in one projection of
/// both.
#[test]
fn two_parts_that_pass_a_bound_back_and_forth_reach_the_empty_scope_and_scale() {
    let p = Premises::new();
    let first = |n: i64| {
        let c = and(
            or(diff_ge("x", "y", 1), diff_ge("z", "w", 1)),
            or(diff_ge("y", "x", 1), diff_ge("w", "z", 1)),
        );
        boxed(&["x", "y", "z", "w"], n).assume(&c, true, &p)
    };
    let zw = prim(Prim::Eq, var("z"), var("w"));
    for n in [10, 100, 1000] {
        assert!(first(n).assume(&zw, true, &p).bottom, "n = {n}");
    }
    let built: BTreeMap<usize, Scope> = [50, 400]
        .into_iter()
        .map(|n| (n, first(n as i64)))
        .collect();
    scaling::check(
        "a bound passed between two parts in a box of width n",
        50,
        |n| {
            built[&n].assume(&zw, true, &p);
        },
    );
}

/// `v_i + w <= 0 || v_(i+1) - w >= 1` for each `i`, with `w` in `0..=1` and each `v_i` in
/// `0..=3`, then `v_0 - w >= 1`. Each case of a clause fixes `w`, and every earlier part
/// mentions `w`, so each case projects O(i) parts: quadratic, stated as hard in
/// COMPLEXITY.md. The scope reaches the fixed point.
#[test]
fn a_walk_through_a_shared_name_reaches_the_fixed_point_in_quadratic_time() {
    let p = Premises::new();
    let build = |n: usize| {
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
    };
    let start = diff_ge("v0", "w", 1);
    for n in [3, 8, 20] {
        let (s, clauses, reversed, last) = build(n);
        let r = s.assume(&clauses, true, &p).assume(&start, true, &p);
        let mut f = r.clone();
        f.forget_projections();
        f.reduce();
        assert_eq!(r.get(&last), f.get(&last), "n = {n}");
        // The clauses in the other order, and the start before them, give the same scope.
        let back = s.assume(&reversed, true, &p).assume(&start, true, &p);
        assert_eq!(back.get(&last), f.get(&last), "n = {n}, reversed");
        let first = s.assume(&start, true, &p).assume(&clauses, true, &p);
        assert_eq!(first.get(&last), f.get(&last), "n = {n}, start first");
        assert!(
            !r.bottom && !r.get(&last).contains(&Value::Int(0)),
            "n = {n}: {r}"
        );
    }
    let built: BTreeMap<usize, (Scope, Term, Term, String)> =
        [5, 40].into_iter().map(|n| (n, build(n))).collect();
    scaling::check_order("a walk of n clauses through a shared name", 5, 2, |n| {
        let (s, clauses, _, _) = &built[&n];
        s.assume(clauses, true, &p).assume(&start, true, &p);
    });
}
