//! The lazy scope ([`Scope::lazy`]) against the eager one: under random sequences of tests,
//! joins and bindings on names related to two hubs, the lazy scope settles every name to
//! the product the eager scope holds, and is empty exactly when the eager one is. One run
//! relates each leaf to one hub at a time, within bounded names; the other relates leaves to
//! both hubs at once (`ai - n - m >= c`), with leaves unbounded, so that stars of two hubs
//! come and go, beside tests of a hub against the other and bounds on either side.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Prim, Shared, Term};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::conjuncts::names as mentioned;
use zedc::store::product::Scope;

use super::ints;
use super::linked::stars_by_definition;
use super::nests::{and, boxed, diff_ge, int, names, or, prim, var};

const LEAVES: [&str; 5] = ["a0", "a1", "a2", "a3", "a4"];
const HUBS: [&str; 2] = ["n", "m"];

/// A random test of nesting `depth` at most: a spoke `ai - n >= c` or `n - ai >= c`, a bound
/// on a hub or on a leaf, or a disjunction or a conjunction of two tests.
fn test(rng: &mut Rng, depth: usize) -> Term {
    let (leaf, hub) = (rng.pick(&LEAVES), rng.pick(&HUBS));
    match rng.below(if depth == 0 { 4 } else { 6 }) {
        0 => diff_ge(leaf, hub, rng.int(-3, 3)),
        1 => diff_ge(hub, leaf, rng.int(-3, 3)),
        2 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(hub),
            int(rng.int(-15, 15)),
        ),
        3 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(leaf),
            int(rng.int(-15, 15)),
        ),
        4 => or(test(rng, depth - 1), test(rng, depth - 1)),
        _ => and(test(rng, depth - 1), test(rng, depth - 1)),
    }
}

/// `a - b - c >= k`, or with `sum` the other way round: `b + c - a >= k`.
fn sum3(a: &str, b: &str, c: &str, k: i64, sum: bool) -> Term {
    let (l, r) = (var(a), prim(Prim::Add, var(b), var(c)));
    let (l, r) = if sum { (r, l) } else { (l, r) };
    prim(Prim::Ge, prim(Prim::Sub, l, r), int(k))
}

/// A random test of nesting `depth` at most, most often of the shape of a star of two hubs:
/// `ai - n - m >= c` or `ai - n >= c`, a lower bound on a leaf or a bound on a hub; now and
/// then one that undoes such a star: `n + m - ai >= c` or an upper bound on a leaf; or a test
/// among the hubs, `n - m >= c` or `n + m >= c`, which a star of the two hubs is projected
/// with.
fn wide(rng: &mut Rng, depth: usize) -> Term {
    let (leaf, hub) = (rng.pick(&LEAVES), rng.pick(&HUBS));
    match rng.below(if depth == 0 { 12 } else { 14 }) {
        0..4 => sum3(leaf, "n", "m", rng.int(-3, 3), false),
        4 => sum3(leaf, "n", "m", rng.int(-3, 3), true),
        5 | 6 => diff_ge(leaf, hub, rng.int(-3, 3)),
        7 if rng.below(2) == 0 => diff_ge(hub, if hub == "n" { "m" } else { "n" }, rng.int(-3, 3)),
        7 => prim(
            Prim::Ge,
            prim(Prim::Add, var("n"), var("m")),
            int(rng.int(-3, 3)),
        ),
        8 => prim(Prim::Ge, var(leaf), int(rng.int(-15, 15))),
        9 => prim(Prim::Le, var(leaf), int(rng.int(-15, 15))),
        10 | 11 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(hub),
            int(rng.int(-15, 15)),
        ),
        12 => or(wide(rng, depth - 1), wide(rng, depth - 1)),
        _ => and(wide(rng, depth - 1), wide(rng, depth - 1)),
    }
}

/// Checks that `lazy` settles every name to what `eager` holds, and that the two are empty
/// together. Returns the number of names the lazy scope held unsettled.
fn same(eager: &Scope, lazy: &Scope, all: &[Arc<str>], trace: &[String]) -> usize {
    assert_eq!(eager.bottom, lazy.bottom, "{}", trace.join("\n"));
    if eager.bottom {
        return 0;
    }
    let mut stale = 0;
    for x in all {
        let settled = lazy.settled(x);
        assert_eq!(eager.get(x), settled, "{x} after\n{}", trace.join("\n"));
        stale += usize::from(lazy.get(x) != settled);
    }
    stale
}

/// Runs `seeds` random sequences of tests drawn by `test`, joins and bindings from `start`,
/// eagerly and lazily, and checks them the same after each step. Returns the number of names
/// the lazy scope held unsettled, the number of states with a star of two hubs, and of those
/// the number with a conjunct of the two hubs.
fn run(start: &Scope, seeds: u64, test: fn(&mut Rng, usize) -> Term) -> (usize, usize, usize) {
    let p = Premises::new();
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let (mut stale, mut two, mut related) = (0, 0, 0);
    for seed in 0..seeds {
        let mut rng = Rng::new(seed);
        let (mut eager, mut lazy) = (start.clone(), start.clone().lazy());
        let mut trace = vec![format!("seed {seed}")];
        for _ in 0..12 {
            match rng.below(8) {
                0..6 => {
                    let (t, outcome) = (test(&mut rng, 2), rng.below(4) != 0);
                    trace.push(format!("assume {t:?} is {outcome}"));
                    eager = eager.assume(&t, outcome, &p);
                    lazy = lazy.assume(&t, outcome, &p);
                }
                6 => {
                    // The two outcomes of a test, each narrowed further, then joined.
                    let (t, u, v) = (test(&mut rng, 1), test(&mut rng, 1), test(&mut rng, 1));
                    trace.push(format!("join {t:?} and {u:?} with not it and {v:?}"));
                    let arms = |s: &Scope| {
                        let yes = s.assume(&t, true, &p).assume(&u, true, &p);
                        let no = s.assume(&t, false, &p).assume(&v, true, &p);
                        yes.join(&no)
                    };
                    (eager, lazy) = (arms(&eager), arms(&lazy));
                }
                _ => {
                    // A name bound again, to what another name holds: a hub rebound drops
                    // its spokes.
                    let (x, y) = (rng.pick(&all), rng.pick(&all));
                    trace.push(format!("bind {x} to the product of {y}"));
                    let e = Shared::new(Term::Var(y.clone()));
                    let (pe, pl) = (eager.get(&y), lazy.settled(&y));
                    eager.bind(&x, pe, &e);
                    lazy.bind(&x, pl, &e);
                }
            }
            stale += same(&eager, &lazy, &all, &trace);
            let multi = stars_by_definition(&lazy.relation).values().any(|gs| {
                gs.iter()
                    .flat_map(|g| mentioned(g))
                    .collect::<BTreeSet<_>>()
                    .len()
                    > 2
            });
            two += usize::from(multi);
            related += usize::from(
                multi
                    && lazy.relation.set().iter().any(|g| {
                        let ns = mentioned(g);
                        ns.len() == 2 && ns.iter().all(|n| &**n == "n" || &**n == "m")
                    }),
            );
            if eager.bottom {
                break;
            }
        }
    }
    (stale, two, related)
}

#[test]
fn a_lazy_scope_settles_each_name_to_the_eager_product() {
    let start = boxed(&["n", "m", "a0", "a1", "a2", "a3", "a4"], 20);
    let (stale, _, _) = run(&start, 300, test);
    // The lazy scope did leave names unsettled, so the comparison is not of two eager scopes.
    assert!(stale > 0, "the lazy scope settled every name at once");
}

#[test]
fn a_lazy_scope_with_stars_of_two_hubs_settles_each_name_to_the_eager_product() {
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let hubs = HUBS
        .iter()
        .map(|h| {
            and(
                prim(Prim::Ge, var(h), int(-20)),
                prim(Prim::Le, var(h), int(20)),
            )
        })
        .reduce(and)
        .expect("two hubs");
    let start = ints(&all).assume(&hubs, true, &Premises::new());
    let (stale, two, related) = run(&start, 100, wide);
    println!(
        "{stale} unsettled names, {two} states with a star of two hubs, {related} with a \
         conjunct of the two"
    );
    assert!(stale > 0, "the lazy scope settled every name at once");
    assert!(two > 0, "no state held a star of two hubs");
    assert!(related > 0, "no state held a star of two related hubs");
}
