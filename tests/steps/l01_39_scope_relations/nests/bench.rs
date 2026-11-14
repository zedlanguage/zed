//! Benchmarks of `nests`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn narrowing_by_a_nest_of_disjunctions_scales() {
    let x0 = || ints(&names(&["x0"]));
    check_built("a disjunction of k equalities", 1_024, |k| {
        (x0(), or_nest(k))
    });
    check_built("a chain of k `if`s on a difference", 400, |k| {
        (ints(&names(&["x0", "y"])), if_chain(k))
    });
    check_built("k nested thresholds", 500, |k| (x0(), thresholds(k)));
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

/// The scope of [`back_and_forth`], then `z == w`, in a box of width n: the two parts pass a
/// bound back and forth until the box is empty, in one projection of both. The empty scope is
/// checked by `two_parts_that_pass_a_bound_back_and_forth_reach_the_empty_scope`.
#[test]
fn two_parts_that_pass_a_bound_back_and_forth_reach_the_empty_scope_and_scale() {
    let p = Premises::new();
    let zw = prim(Prim::Eq, var("z"), var("w"));
    let built = scaling::inputs(N_PARTS, |n| back_and_forth(n as i64));
    scaling::check(
        "a bound passed between two parts in a box of width n",
        N_PARTS,
        |n| {
            built[&n].assume(&zw, true, &p);
        },
    );
}

/// The clauses of [`walk`], then `v_0 - w >= 1`. Each case of a clause fixes `w`, and every
/// earlier part mentions `w`, so each case projects O(i) parts: quadratic, stated as hard in
/// COMPLEXITY.md. The fixed point is checked by
/// `a_walk_through_a_shared_name_reaches_the_fixed_point`.
#[test]
fn a_walk_through_a_shared_name_reaches_the_fixed_point_in_quadratic_time() {
    let p = Premises::new();
    let start = diff_ge("v0", "w", 1);
    let built = scaling::inputs(N_WALK, walk);
    scaling::check_order(
        "a walk of n clauses through a shared name",
        N_WALK,
        2,
        |n| {
            let (s, clauses, _, _) = &built[&n];
            s.assume(clauses, true, &p).assume(&start, true, &p);
        },
    );
}

/// The sizes of the last two benchmarks.
const N_PARTS: usize = 50;
const N_WALK: usize = 20;

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
