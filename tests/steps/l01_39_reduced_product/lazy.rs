//! The lazy scope ([`Scope::lazy`]) against the eager one: under random sequences of tests,
//! joins and bindings on names related to two hubs, the lazy scope settles every name to
//! the product the eager scope holds, and is empty exactly when the eager one is. One run
//! relates each leaf to one hub at a time, within bounded names; the other relates leaves to
//! both hubs at once (`ai - n - m >= c`), with leaves unbounded, so that stars of two hubs
//! come and go, beside tests of a hub against the other and bounds on either side.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::conjuncts::names as mentioned;
use zedc::store::interval::IntervalSet;
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

/// Runs, for each seed of `seeds`, a random sequence of tests drawn by `test`, joins and
/// bindings from `start`, eagerly and lazily, and checks them the same after each step.
/// Returns the number of names the lazy scope held unsettled, the number of states with a
/// star of two hubs, and of those the number with a conjunct of the two hubs, and the number
/// with a satellite of the hubs of such a star ([`satellite_kept`]).
fn run(
    start: &Scope,
    seeds: impl IntoIterator<Item = u64>,
    test: fn(&mut Rng, usize) -> Term,
) -> (usize, usize, usize, usize) {
    let p = Premises::new();
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let (mut stale, mut two, mut related, mut kept) = (0, 0, 0, 0);
    for seed in seeds {
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
            kept += usize::from(multi && satellite_kept(&lazy));
            if eager.bottom {
                break;
            }
        }
    }
    (stale, two, related, kept)
}

// The seed loops below ran 100 to 1,200 fixed seeds each, 16 to 42 s alone at load 30, split
// into tests of 20 to 100 seeds (TEST-lazy-split). Each is now one test of a few seeds new at
// each run ([`fresh_seeds`]), well under a second, which checks the lazy scope against the
// eager one and leaves out the counts of rare events, and one test of a fixed seed at which
// each event the loop counted occurs, so that the random runs are known to reach it
// (TEST-bench-move-l0139; seeds found 2026-11-14 over the first 30 to 200 seeds of each).

/// `count` seeds in a row from a new one each run, which [`Rng::fresh`] prints and `ZED_TEST_SEED`
/// repeats. Each check names the seed it failed at.
fn fresh_seeds(what: &str, count: u64) -> std::ops::Range<u64> {
    let (_, seed) = Rng::fresh(what);
    let first = seed.min(u64::MAX - count);
    first..first + count
}

/// Random seeds of [`test`]; seed 19 leaves names unsettled, so that the comparison is not of
/// two eager scopes (in 6 of seeds 0 to 199).
mod a_lazy_scope_settles_each_name_to_the_eager_product {
    use super::*;

    fn start() -> Scope {
        boxed(&["n", "m", "a0", "a1", "a2", "a3", "a4"], 20)
    }

    #[test]
    fn random_seeds() {
        run(
            &start(),
            fresh_seeds("lazy scope against the eager product", 10),
            test,
        );
    }

    #[test]
    fn seed_19_leaves_a_name_unsettled() {
        let (stale, _, _, _) = run(&start(), [19], test);
        assert!(stale > 0, "the lazy scope settled every name at once");
    }
}

/// Every name unbounded but the two hubs, each within [-20, 20].
fn bounded_hubs() -> Scope {
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
    ints(&all).assume(&hubs, true, &Premises::new())
}

/// Random seeds of [`wide`]; seed 2 leaves names unsettled and holds a star of two hubs, and
/// one beside a conjunct of the two (all three in 18 of seeds 0 to 199).
mod a_lazy_scope_with_stars_of_two_hubs_settles_each_name_to_the_eager_product {
    use super::*;

    #[test]
    fn random_seeds() {
        let seeds = fresh_seeds("lazy scope with stars of two hubs", 8);
        run(&bounded_hubs(), seeds, wide);
    }

    #[test]
    fn seed_2_holds_a_star_of_two_related_hubs() {
        let (stale, two, related, _) = run(&bounded_hubs(), [2], wide);
        assert!(stale > 0, "the lazy scope settled every name at once");
        assert!(two > 0, "no state held a star of two hubs");
        assert!(related > 0, "no state held a star of two related hubs");
    }
}

#[test]
fn a_test_between_the_hubs_of_a_star_settles_them_as_the_eager_scope_does() {
    // Seed 1109 of the run above, past its default seeds: a disjunction of tests on `m + n`
    // and a star `ai >= n + m - c` over both hubs, then `n >= m`. The eager scope gave n
    // int[1..=20] and the lazy one int[0..=20]: the disjunction was a part of the star's block
    // and of the hubs' block under one key, so each block found the other's snapshot there and
    // projected it again, with `n >= m` in the eager scope, which projects the star at once.
    // Each block now keys its parts apart (item NARROW-lazy-settle). `run` panics on the first
    // name the two scopes settle apart.
    let (_, two, _, _) = run(&bounded_hubs(), 1109..1110, wide);
    assert!(two > 0, "seed 1109 no longer makes a star of two hubs");
}

#[test]
fn seed_3011_a_new_star_settles_its_leaf_as_the_eager_scope_does() {
    // Seed 3011 of `wide`, past its default seeds: `m + n >= -2` holds (`m <= 8` rules out the
    // other side of a disjunction), then `a0 >= n + m - 2`, then `a0 >= n + m + 1`. The eager
    // scope kept `a0 >= -4` from the first where the lazy scope, settling `a0`, found
    // `a0 >= -1`, on main before item NARROW-lazy-settle too; with the parts of a star's block
    // keyed apart from the hubs' block, the two agree.
    let (_, two, _, _) = run(&bounded_hubs(), 3011..3012, wide);
    assert!(two > 0, "seed 3011 no longer makes a star of two hubs");
}

/// Whether a star of two hubs or more stands beside a satellite of its hubs: a conjunct of a
/// hub of the star and one other name, neither a leaf of a star nor a hub of that one.
fn satellite_kept(s: &Scope) -> bool {
    let stars = stars_by_definition(&s.relation);
    stars.iter().any(|(leaf, gs)| {
        let hubs: BTreeSet<Arc<str>> = gs
            .iter()
            .flat_map(|g| mentioned(g))
            .filter(|n| n != leaf)
            .collect();
        hubs.len() > 1
            && s.relation.set().iter().any(|g| {
                let ns = mentioned(g);
                ns.len() == 2
                    && ns.iter().any(|n| hubs.contains(n))
                    && ns
                        .iter()
                        .any(|n| !hubs.contains(n) && !stars.contains_key(n))
            })
    })
}

/// As [`wide`], and now and then a hub above a leaf, `n - ai >= c`, so that a leaf between the
/// two hubs (`ai >= n`, `m - ai >= c`) is a satellite of them and leaves the stars of the two
/// hubs in place.
fn satellites(rng: &mut Rng, depth: usize) -> Term {
    if rng.below(4) == 0 {
        diff_ge(rng.pick(&HUBS), rng.pick(&LEAVES), rng.int(-3, 3))
    } else {
        wide(rng, depth)
    }
}

/// Random seeds of [`satellites`]. A star of two hubs stood beside a satellite of them at
/// seeds 18, 59, 75 and 99 of 0 to 99 only (2026-11-09; 9 of seeds 0 to 199), so seed 18 is
/// checked on its own.
mod a_lazy_scope_with_satellites_of_two_hubs_settles_each_name_to_the_eager_product {
    use super::*;

    #[test]
    fn random_seeds() {
        let seeds = fresh_seeds("lazy scope with satellites of two hubs", 8);
        run(&bounded_hubs(), seeds, satellites);
    }

    #[test]
    fn seed_18_holds_a_star_beside_a_satellite_of_its_hubs() {
        let (stale, _, _, kept) = run(&bounded_hubs(), [18], satellites);
        assert!(stale > 0, "the lazy scope settled every name at once");
        assert!(
            kept > 0,
            "no star of two hubs stood beside a satellite of them"
        );
    }
}

/// For each name of `all`, the values in `-3..=13` the scope holds of it.
fn held(s: &Scope, all: &[Arc<str>], lazy: bool) -> Vec<Vec<i64>> {
    all.iter()
        .map(|x| {
            let p = if lazy { s.settled(x) } else { s.get(x) };
            (-3..=13).filter(|v| p.contains(&Value::Int(*v))).collect()
        })
        .collect()
}

/// For each name, the values in `-3..=13` it takes at the integer points, with `n` and `m` in
/// `0..=5` and the leaves in `-3..=13`, that meet `a0 >= n + m`, `a0 <= 3`, `n <= a2 <= m - 1`
/// and, with `sandwich`, `n + m <= a1 <= n + m + 1`.
fn points(sandwich: bool) -> Vec<Vec<i64>> {
    let mut out = vec![BTreeSet::new(); 5];
    let w = -3..=13i64;
    for n in 0..=5i64 {
        for m in 0..=5i64 {
            for a0 in w.clone().filter(|a0| *a0 >= n + m && *a0 <= 3) {
                for a2 in w.clone().filter(|a2| *a2 >= n && *a2 < m) {
                    for a1 in w.clone() {
                        if sandwich && !(n + m..=n + m + 1).contains(&a1) {
                            continue;
                        }
                        for (i, v) in [n, m, a0, a1, a2].into_iter().enumerate() {
                            out[i].insert(v);
                        }
                    }
                }
            }
        }
    }
    out.into_iter().map(|s| s.into_iter().collect()).collect()
}

#[test]
fn stars_beside_a_satellite_or_a_sandwich_project_exactly() {
    // A star's core is closed: its conjuncts and the free conjuncts at its hubs, so that
    // projecting the core gives each of its names exactly. With hubs `n` and `m`, the star
    // `a0 >= n + m` and the satellite `n <= a2 <= m - 1`, whose conjuncts each relate it to
    // one hub: the hubs admit `a0` (each relates `a2` to the other hub, which is a hub of
    // `a0`), and the satellite's conjuncts are free at the hubs, so they are in the core;
    // projecting the core with `a0 <= 3` meets `n + m <= 3` with `n <= m - 1` and gives `n`
    // in 0..=1, where the star alone would give 0..=3. Any other conjunct at a name of the
    // core is of the name alone or another leaf's, which only bounds a hub, so nothing outside
    // the core relates its names. The sandwich `n + m <= a1 <= n + m + 1` relates `a1` to the
    // two hubs at once: `a1` is no satellite and no leaf (its sign differs), so the hubs admit
    // no star of `n` and `m`, `a0` is no star, and the whole block is projected together, as
    // before satellites.
    let all = names(&["n", "m", "a0", "a1", "a2"]);
    let p = Premises::new();
    for sandwich in [false, true] {
        let mut t = vec![
            prim(Prim::Ge, var("n"), int(0)),
            prim(Prim::Le, var("n"), int(5)),
            prim(Prim::Ge, var("m"), int(0)),
            prim(Prim::Le, var("m"), int(5)),
            sum3("a0", "n", "m", 0, false),
            diff_ge("a2", "n", 0),
            diff_ge("m", "a2", 1),
        ];
        if sandwich {
            t.push(sum3("a1", "n", "m", 0, false));
            t.push(sum3("a1", "n", "m", -1, true));
        }
        let (mut eager, mut lazy) = (ints(&all), ints(&all).lazy());
        for t in &t {
            eager = eager.assume(t, true, &p);
            lazy = lazy.assume(t, true, &p);
        }
        let star = stars_by_definition(&lazy.relation).contains_key("a0");
        assert_eq!(star, !sandwich, "a0 a star with sandwich {sandwich}");
        assert_eq!(
            lazy.relation.star("a0").is_some(),
            star,
            "the kept stars and the definition disagree on a0"
        );
        let cap = prim(Prim::Le, var("a0"), int(3));
        let (eager, lazy) = (eager.assume(&cap, true, &p), lazy.assume(&cap, true, &p));
        let want = points(sandwich);
        assert_eq!(want[0], vec![0, 1], "the points give n in 0..=1");
        // Without the sandwich `a1` is unbounded, and so held at each value of the window.
        assert_eq!(
            held(&eager, &all, false),
            want,
            "eager, sandwich {sandwich}"
        );
        assert_eq!(held(&lazy, &all, true), want, "lazy, sandwich {sandwich}");
    }
}

/// `Scope::settle` gives a leaf of a class the projection of an earlier leaf of the class
/// when the other names and the leaf's own interval and class are as the earlier leaf's
/// were. Against settling each leaf alone, which reuses nothing: leaves named before,
/// between and after the hubs, so that the solver orders their names differently; the class
/// one conjunct of the two hubs, of coefficient one or two at the leaf, or two conjuncts of
/// one hub each; each leaf's own lower bound and hole drawn from two of each, so that some
/// leaves share them and some do not; and the hubs with bounds, holes and a class. The last
/// test moves a hub, so that every star is due at once. Each leaf is settled to the product
/// it gets alone, and to the eager scope's. The leaves were in one class in 15 of the 28 runs
/// of seeds 0 to 29 (seeds 12 and 17 give an empty scope; 2026-11-09 and 2026-11-14): random
/// seeds, and seed 1, whose leaves are in one class, with seed 12, whose scope is empty.
mod leaves_of_one_class_settled_together_get_what_each_gets_alone {
    use super::*;

    #[test]
    fn random_seeds() {
        part(fresh_seeds("leaves of one class settled together", 2));
    }

    #[test]
    fn seed_1_has_leaves_of_one_class_and_seed_12_an_empty_scope() {
        assert_eq!(
            part([1, 12]),
            (1, 1),
            "(runs, runs with the leaves in one class)"
        );
    }

    fn part(seeds: impl IntoIterator<Item = u64>) -> (usize, usize) {
        const LEAVES: [&str; 6] = ["a0", "a1", "mm0", "mm1", "z0", "z1"];
        let all = names(&["m", "n", "a0", "a1", "mm0", "mm1", "z0", "z1"]);
        let leaves = names(&LEAVES);
        let p = Premises::new();
        let (mut reused, mut runs) = (0, 0);
        for seed in seeds {
            let mut rng = Rng::new(seed);
            let form = rng.below(3);
            let c = rng.int(-3, 3);
            let star = |x: &str| -> Vec<Term> {
                match form {
                    0 => vec![sum3(x, "n", "m", c, false)],
                    1 => vec![prim(
                        Prim::Ge,
                        prim(
                            Prim::Sub,
                            prim(Prim::Add, var(x), var(x)),
                            prim(Prim::Add, var("n"), var("m")),
                        ),
                        int(c),
                    )],
                    _ => vec![diff_ge(x, "n", c), diff_ge(x, "m", -c)],
                }
            };
            let mut t: Vec<Term> = Vec::new();
            for h in ["n", "m"] {
                t.push(prim(Prim::Ge, var(h), int(rng.int(-12, -2))));
                t.push(prim(Prim::Le, var(h), int(rng.int(2, 12))));
                t.push(prim(Prim::Ne, var(h), int(rng.int(-3, 3))));
            }
            if rng.below(2) == 0 {
                // `n` even.
                t.push(prim(Prim::Eq, prim(Prim::Mod, var("n"), int(2)), int(0)));
            }
            let lows = [rng.int(-20, 0), rng.int(-20, 0)];
            let holes = [rng.int(-3, 6), rng.int(-3, 6)];
            for x in LEAVES {
                t.extend(star(x));
                t.push(prim(Prim::Ge, var(x), int(rng.pick(&lows))));
                t.push(prim(Prim::Ne, var(x), int(rng.pick(&holes))));
            }
            let (mut eager, mut lazy) = (ints(&all), ints(&all).lazy());
            for t in &t {
                eager = eager.assume(t, true, &p);
                lazy = lazy.assume(t, true, &p);
            }
            let hub = prim(Prim::Ge, var("n"), int(rng.int(-4, 4)));
            eager = eager.assume(&hub, true, &p);
            lazy = lazy.assume(&hub, true, &p);
            if eager.bottom {
                assert!(
                    lazy.bottom,
                    "seed {seed}: the eager scope is empty, the lazy one not"
                );
                continue;
            }
            let classes: BTreeSet<_> = leaves
                .iter()
                .filter_map(|x| lazy.relation.class_of(x))
                .collect();
            let stars = leaves
                .iter()
                .filter(|x| lazy.relation.star(x).is_some())
                .count();
            let mut together = lazy.clone();
            together.settle(&leaves);
            for x in &leaves {
                let mut alone = lazy.clone();
                alone.settle([x]);
                assert_eq!(together.get(x), alone.get(x), "seed {seed}: {x} with {t:?}");
                assert_eq!(
                    together.get(x),
                    eager.get(x),
                    "seed {seed}: {x} eagerly, with {t:?}"
                );
            }
            for h in names(&["m", "n"]) {
                assert_eq!(together.get(&h), eager.get(&h), "seed {seed}: {h}");
            }
            runs += 1;
            reused += usize::from(stars >= 2 && classes.len() == 1);
        }
        println!("{runs} runs, {reused} with two stars or more, all of one class");
        (runs, reused)
    }
}

/// `Scope::join` settles on each side the leaves of the stars whose core may differ
/// between the sides: those at a name the sides hold differently, at a name a written
/// constraint of one side alone mentions, or at a name whose free conjuncts differ
/// ([`zedc::store::conjuncts::Conjuncts::core`]). A leaf of a star whose core and product
/// are one on both sides stays as it is. Against the join of the two sides with every name
/// settled first, and against the eager join: leaves `a0` to `a3` of one class of two hubs
/// (`ai >= n + c` and `ai >= m + c`, or `ai - n + m >= c`), each with its own lower bound
/// and hole, hubs with bounds and holes, then a test that moves a hub, so that the stars
/// are stale, then two joins in a row of the two outcomes of a test, each narrowed
/// further: a test of a hub, of the two hubs (`n - m >= c`, a free conjunct at both, which
/// moves neither), of a leaf, or `b >= n && b >= m` on a further name `b`, whose negation
/// splits in two. Every name is then settled to the product of both. Random seeds, and seed
/// 1, at which a join leaves a leaf stale (7 of seeds 0 to 39; seeds 0 to 199 took 33 s at
/// load 24 to 35, item SPLIT-l01_39-slow).
mod a_join_settles_the_leaves_whose_core_differs_as_settling_every_name_does {
    use super::*;

    const LEAVES: [&str; 4] = ["a0", "a1", "a2", "a3"];

    /// A test on the two hubs, a leaf, or `b`, at nesting `depth` at most.
    fn branch(rng: &mut Rng, depth: usize) -> Term {
        let hub = rng.pick(&HUBS);
        match rng.below(if depth == 0 { 5 } else { 7 }) {
            0 => prim(
                rng.pick(&[Prim::Ge, Prim::Le]),
                var(hub),
                int(rng.int(-12, 12)),
            ),
            1 => diff_ge("n", "m", rng.int(-3, 3)),
            2 => prim(
                rng.pick(&[Prim::Ge, Prim::Le]),
                var(rng.pick(&LEAVES)),
                int(rng.int(-20, 20)),
            ),
            3 | 4 => and(diff_ge("b", "n", 0), diff_ge("b", "m", 0)),
            5 => or(branch(rng, depth - 1), branch(rng, depth - 1)),
            _ => and(branch(rng, depth - 1), branch(rng, depth - 1)),
        }
    }

    fn part(seeds: impl IntoIterator<Item = u64>) -> usize {
        let all = names(&["n", "m", "a0", "a1", "a2", "a3", "b"]);
        let p = Premises::new();
        let (mut runs, mut kept) = (0, 0);
        for seed in seeds {
            let mut rng = Rng::new(seed);
            let (form, c) = (rng.below(2), rng.int(-3, 3));
            let mut t: Vec<Term> = Vec::new();
            for h in HUBS {
                t.push(prim(Prim::Ge, var(h), int(rng.int(-20, -2))));
                t.push(prim(Prim::Le, var(h), int(rng.int(2, 20))));
                t.push(prim(Prim::Ne, var(h), int(rng.int(-3, 3))));
            }
            let lows = [rng.int(-30, 0), rng.int(-30, 0)];
            for x in LEAVES {
                if form == 0 {
                    t.push(diff_ge(x, "n", c));
                    t.push(diff_ge(x, "m", c));
                } else {
                    let d = prim(Prim::Sub, var(x), var("n"));
                    t.push(prim(Prim::Ge, prim(Prim::Add, d, var("m")), int(c)));
                }
                t.push(prim(Prim::Ge, var(x), int(rng.pick(&lows))));
                t.push(prim(Prim::Ne, var(x), int(rng.int(-3, 6))));
            }
            t.push(prim(
                rng.pick(&[Prim::Ge, Prim::Le]),
                var(rng.pick(&HUBS)),
                int(rng.int(-6, 6)),
            ));
            let (mut eager, mut lazy) = (ints(&all), ints(&all).lazy());
            for t in &t {
                eager = eager.assume(t, true, &p);
                lazy = lazy.assume(t, true, &p);
            }
            let mut trace = vec![format!("seed {seed}: {t:?}")];
            for _ in 0..2 {
                if eager.bottom {
                    break;
                }
                let (t, u, v) = (
                    branch(&mut rng, 1),
                    branch(&mut rng, 0),
                    branch(&mut rng, 0),
                );
                trace.push(format!("join {t:?} and {u:?} with not it and {v:?}"));
                let arms = |s: &Scope| {
                    let yes = s.assume(&t, true, &p).assume(&u, true, &p);
                    let no = s.assume(&t, false, &p).assume(&v, true, &p);
                    (yes, no)
                };
                let (ey, en) = arms(&eager);
                let (ly, ln) = arms(&lazy);
                let (mut sy, mut sn) = (ly.clone(), ln.clone());
                sy.settle(&all);
                sn.settle(&all);
                let (every, joined) = (sy.join(&sn), ly.join(&ln));
                eager = ey.join(&en);
                assert_eq!(eager.bottom, joined.bottom, "{}", trace.join("\n"));
                if !eager.bottom {
                    for x in &all {
                        let s = joined.settled(x);
                        assert_eq!(s, every.settled(x), "{x} after\n{}", trace.join("\n"));
                        assert_eq!(s, eager.get(x), "{x} eagerly after\n{}", trace.join("\n"));
                        kept += usize::from(LEAVES.contains(&&**x) && joined.get(x) != s);
                    }
                }
                lazy = joined;
                runs += 1;
            }
        }
        println!("{runs} joins, {kept} leaves left stale by a join");
        kept
    }

    #[test]
    fn random_seeds() {
        part(fresh_seeds(
            "a join settles the leaves whose core differs",
            3,
        ));
    }

    #[test]
    fn seed_1_leaves_a_leaf_stale_after_a_join() {
        assert!(part([1]) > 0, "no join left a leaf stale");
    }
}

/// Joins whose two cases keep the values of each hub, so that the stars at the hubs, stale
/// from a move of both hubs, stay stale through the join unless the join settles them. Each
/// leaf `ai` is above `n` and above `m` (or `-m`), and the hubs meet a disjunction of tests
/// on them. Two ways the join's own star can differ from the cases': a case that is a test
/// on another name, `z`, joined with a test on the hubs makes a disjunction that mentions `z`
/// and both hubs, so the hubs no longer admit the star and the join holds none; and two cases
/// that test the hubs alone make a second disjunction among the hubs, which the projection of
/// the star (one disjunction at a time) reads less tightly than each case's one disjunction.
/// In both, the leaf settles to the least value of the leaf over the union of the cases.
mod a_join_settles_a_star_it_drops_or_whose_core_gains_a_disjunction {
    use super::*;

    /// `kn·n + km·m >= k`, each coefficient -1, 0 or 1.
    #[derive(Clone, Copy, Debug)]
    struct HubTest(i64, i64, i64);

    impl HubTest {
        fn holds(self, n: i64, m: i64) -> bool {
            self.0 * n + self.1 * m >= self.2
        }

        /// The test as a program writes it, with sums and differences only: a coefficient
        /// other than one or minus one would make it a written constraint, whose names the
        /// join settles at once.
        fn term(self) -> Term {
            let mut sum: Option<Term> = None;
            for (k, x) in [(self.0, "n"), (self.1, "m")] {
                sum = match (sum, k) {
                    (s, 0) => s,
                    (None, 1) => Some(var(x)),
                    (None, _) => Some(prim(Prim::Sub, int(0), var(x))),
                    (Some(s), 1) => Some(prim(Prim::Add, s, var(x))),
                    (Some(s), _) => Some(prim(Prim::Sub, s, var(x))),
                };
            }
            prim(Prim::Ge, sum.expect("a hub"), int(self.2))
        }
    }

    fn all(ts: &[HubTest], n: i64, m: i64) -> bool {
        ts.iter().all(|t| t.holds(n, m))
    }

    fn conj(ts: &[HubTest]) -> Term {
        ts.iter().map(|t| t.term()).reduce(and).expect("a test")
    }

    /// The hubs' values after the move.
    const LO: i64 = -10;
    const HI: i64 = 10;

    /// A case of the join: leaves `ai >= n` and `ai >= sign·m`, the disjunction `d1`, then
    /// `z >= 0` and `yes`, or `z < 0` and `no`, tested together when `with_z` and one after
    /// the other otherwise.
    struct Case {
        sign: i64,
        d1: Vec<HubTest>,
        yes: Vec<HubTest>,
        no: Vec<HubTest>,
        with_z: bool,
    }

    impl Case {
        /// The random case of `seed`: `d1` of two or three tests, each arm of one or two. A
        /// test of one hub narrows it, and so does a test of two whose bound is above 0 on
        /// this box, so the arms draw tests of two hubs with bounds at or below 0.
        fn of(seed: u64) -> Case {
            let shapes = [
                (1, 0),
                (-1, 0),
                (0, 1),
                (0, -1),
                (1, 1),
                (-1, -1),
                (1, -1),
                (-1, 1),
            ];
            let mut rng = Rng::new(seed);
            let test = |rng: &mut Rng, arm: bool| {
                if arm {
                    let (a, b) = rng.pick(&shapes[4..]);
                    HubTest(a, b, rng.int(-20, 0))
                } else {
                    let (a, b) = rng.pick(&shapes);
                    HubTest(a, b, rng.int(-14, 14))
                }
            };
            let d1: Vec<HubTest> = (0..2 + rng.below(2))
                .map(|_| test(&mut rng, false))
                .collect();
            let yes: Vec<HubTest> = (0..1 + rng.below(2))
                .map(|_| test(&mut rng, true))
                .collect();
            let no: Vec<HubTest> = (0..1 + rng.below(2))
                .map(|_| test(&mut rng, true))
                .collect();
            let (sign, with_z) = (rng.pick(&[1, -1]), rng.below(2) == 0);
            Case {
                sign,
                d1,
                yes,
                no,
                with_z,
            }
        }

        fn trace(&self, seed: u64) -> String {
            let Case {
                sign,
                d1,
                yes,
                no,
                with_z,
            } = self;
            format!("seed {seed}: sign {sign} d1 {d1:?} yes {yes:?} no {no:?} z {with_z}")
        }

        fn d1_holds(&self, n: i64, m: i64) -> bool {
            self.d1.iter().any(|g| g.holds(n, m))
        }

        /// The hubs' values in `LO..=HI` that `d1` and `arm` admit.
        fn points(&self, arm: &[HubTest]) -> Vec<(i64, i64)> {
            (LO..=HI)
                .flat_map(|n| (LO..=HI).map(move |m| (n, m)))
                .filter(|&(n, m)| self.d1_holds(n, m) && all(arm, n, m))
                .collect()
        }

        /// Whether neither arm narrows a hub on the box (otherwise the lazy join settles the
        /// stars at it at once).
        fn keeps(&self) -> bool {
            [&self.yes, &self.no].iter().all(|arm| {
                let points = self.points(arm);
                let ns: BTreeSet<i64> = points.iter().map(|p| p.0).collect();
                let ms: BTreeSet<i64> = points.iter().map(|p| p.1).collect();
                ns.len() == ms.len() && ns.len() == (HI - LO + 1) as usize
            })
        }

        /// The tests before the arms: hubs in `LO - 1..=HI`, the leaves, `d1`, and the move of
        /// both hubs to `LO`.
        fn before(&self) -> Vec<Term> {
            let mut t: Vec<Term> = Vec::new();
            for h in HUBS {
                t.push(prim(Prim::Ge, var(h), int(LO - 1)));
                t.push(prim(Prim::Le, var(h), int(HI)));
            }
            for x in ["a0", "a1", "a2"] {
                t.push(diff_ge(x, "n", 0));
                t.push(if self.sign == 1 {
                    diff_ge(x, "m", 0)
                } else {
                    prim(Prim::Ge, prim(Prim::Add, var(x), var("m")), int(0))
                });
            }
            t.push(self.d1.iter().map(|g| g.term()).reduce(or).expect("a test"));
            for h in HUBS {
                t.push(prim(Prim::Ge, var(h), int(LO)));
            }
            t
        }

        /// The scope after the tests before the arms, lazy or eager.
        fn scope(&self, lazy: bool, p: &Premises) -> Scope {
            let s = ints(&names(&["n", "m", "z", "a0", "a1", "a2"]));
            let s = if lazy { s.lazy() } else { s };
            self.before().iter().fold(s, |s, t| s.assume(t, true, p))
        }

        fn arms(&self, s: &Scope, p: &Premises) -> (Scope, Scope) {
            let z = prim(Prim::Ge, var("z"), int(0));
            if self.with_z {
                let not_z = prim(Prim::Lt, var("z"), int(0));
                (
                    s.assume(&and(z, conj(&self.yes)), true, p),
                    s.assume(&and(not_z, conj(&self.no)), true, p),
                )
            } else {
                (
                    s.assume(&z, true, p).assume(&conj(&self.yes), true, p),
                    s.assume(&z, false, p).assume(&conj(&self.no), true, p),
                )
            }
        }

        /// The least value of a leaf in either arm, by the enumeration of the hubs.
        fn least(&self) -> Option<i64> {
            (self.points(&self.yes).into_iter())
                .chain(self.points(&self.no))
                .map(|(n, m)| n.max(self.sign * m))
                .min()
        }

        /// The join of the eager arms, checked against the enumeration of the hubs and the
        /// lazy join: empty exactly when no point is left; each leaf's least value that of the
        /// enumeration; each hub holding every value a point gives it; and each name no
        /// coarser than in the lazy join, so a hub is exact wherever the lazy join's is. Each
        /// hub, eager and lazy, has the enumeration's least and greatest values as its ends
        /// (item LAZY-hub-coarse); a hole between them may be lost.
        fn eager_join(&self, trace: &str) -> Scope {
            let p = Premises::new();
            let (ey, en) = self.arms(&self.scope(false, &p), &p);
            let joined = ey.join(&en);
            let least = self.least();
            assert_eq!(joined.bottom, least.is_none(), "eagerly after {trace}");
            let Some(least) = least else {
                return joined;
            };
            let (ly, ln) = self.arms(&self.scope(true, &p), &p);
            let lazy = ly.join(&ln);
            for x in &names(&["n", "m", "z", "a0", "a1", "a2"]) {
                let (e, l) = (joined.get(x), lazy.settled(x));
                assert!(
                    e.ints().is_subset(l.ints()),
                    "{x} is {}, lazily {}, eagerly after {trace}",
                    e.ints(),
                    l.ints()
                );
            }
            let points: Vec<(i64, i64)> = (self.points(&self.yes).into_iter())
                .chain(self.points(&self.no))
                .collect();
            for (h, at) in [("n", 0), ("m", 1)] {
                let values: BTreeSet<i64> = points
                    .iter()
                    .map(|p| if at == 0 { p.0 } else { p.1 })
                    .collect();
                let (lo, hi) = (values.first(), values.last());
                let ends = IntervalSet::of(*lo.expect("a point"), *hi.expect("a point"));
                let h: Arc<str> = Arc::from(h);
                for (how, ints) in [
                    ("eagerly", joined.get(&h).ints().clone()),
                    ("lazily", lazy.settled(&h).ints().clone()),
                ] {
                    for &v in &values {
                        assert!(
                            ints.contains(v),
                            "{h} is {ints}, holds no {v}, {how} after {trace}"
                        );
                    }
                    assert!(
                        ints.hull() == ends,
                        "{h} is {ints}, the enumeration's ends are {ends}, {how} after {trace}"
                    );
                }
            }
            for x in ["a0", "a1", "a2"] {
                let ints = joined.get(&Arc::from(x)).ints().clone();
                assert!(
                    ints.contains(least) && !ints.contains(least - 1),
                    "{x} is {ints}, least {least}, eagerly after {trace}"
                );
            }
            joined
        }

        /// Checks each name of the lazy join against settling every name first, and against
        /// the eager join, and each leaf's least value against the enumeration of the hubs;
        /// returns how many leaves one arm or the other holds stale before the join.
        fn run(&self, trace: &str) -> usize {
            let all_names = names(&["n", "m", "z", "a0", "a1", "a2"]);
            let p = Premises::new();
            let (ly, ln) = self.arms(&self.scope(true, &p), &p);
            let (mut sy, mut sn) = (ly.clone(), ln.clone());
            sy.settle(&all_names);
            sn.settle(&all_names);
            let (every, joined) = (sy.join(&sn), ly.join(&ln));
            let eager = self.eager_join(trace);
            let least = self.least();
            assert_eq!(joined.bottom, least.is_none(), "{trace}");
            let Some(least) = least else {
                return 0;
            };
            let mut stale = 0;
            for x in &all_names {
                let s = joined.settled(x);
                assert_eq!(s, every.settled(x), "{x} after {trace}");
                assert_eq!(s, eager.get(x), "{x} eagerly after {trace}");
                if x.starts_with('a') {
                    let ints = s.ints();
                    assert!(
                        ints.contains(least) && !ints.contains(least - 1),
                        "{x} is {ints}, least {least}, after {trace}"
                    );
                    stale += usize::from(ly.get(x) != ly.settled(x) || ln.get(x) != ln.settled(x));
                }
            }
            stale
        }
    }

    /// The case that tests `z` with a test on the hubs: the join's disjunction
    /// `(z >= 0 && n + m <= -7) || (z < 0 && n - m >= -30)` mentions `z`, which no hub relates
    /// to, so the join holds no star, and the leaves, at `-11` from before the move, read as
    /// they are unless the join settles them first.
    #[test]
    fn a_case_that_tests_another_name_drops_the_star() {
        let case = Case {
            sign: 1,
            d1: vec![HubTest(-1, -1, 10)],
            yes: vec![HubTest(-1, -1, 7)],
            no: vec![HubTest(1, -1, -30)],
            with_z: true,
        };
        assert!(case.run("n + m <= -10; z >= 0 && n + m <= -7, or z < 0 && n - m >= -30") > 0);
    }

    /// Cases that test the hubs alone: the join's core holds `n - m >= -6 || n <= -8` and
    /// `n - m >= -8 || n - m >= -6`, two disjunctions, and is projected one disjunction at a
    /// time, which gives `ai >= -4`; each case's core holds one disjunction and gives the
    /// least value `-3` (at `n = -3`, `m = 3`).
    #[test]
    fn a_join_that_adds_a_second_disjunction_to_the_core() {
        let case = Case {
            sign: -1,
            d1: vec![HubTest(1, -1, -6), HubTest(-1, 0, 8)],
            yes: vec![HubTest(1, -1, -8)],
            no: vec![HubTest(1, -1, -6)],
            with_z: false,
        };
        assert!(case.run("n - m >= -6 || n <= -8; n - m >= -8, or n - m >= -6") > 0);
    }

    /// Seeds at which the eager join was coarser than the lazy one: an arm's test on a term of
    /// the hubs that `d1` does not compare left the projection of `d1` with the leaves as it
    /// was, so each eager arm read a leaf or a hub below the enumeration, and the join took the
    /// union (at seed 22671 `m <= n + 5` under `m + n <= -7 || m + n >= 2` gave `a0 >= -2`,
    /// least `-1`; at seed 272 `m` reached `1`, greatest `0`). The eager join projects those
    /// stars again (`Scope::refresh`). Seeds 116 and 237, reported with them, show no
    /// difference from cc9b8f5b on, and are kept here as checks.
    #[test]
    fn the_eager_join_is_as_tight_as_the_lazy_one_at_these_seeds() {
        for seed in [116, 237, 272, 2_220, 22_490, 22_671] {
            let case = Case::of(seed);
            let trace = case.trace(seed);
            if case.keeps() {
                case.run(&trace);
            } else {
                case.eager_join(&trace);
            }
        }
    }

    /// Seeds reported with a lazy join's hub coarser than the enumeration (item
    /// LAZY-hub-coarse). At 781, 1515 and 1820 the ends were past the enumeration's: a test
    /// on `n + m` or `m - n` after `d1` made no part of `d1` due, since it is on neither of
    /// `d1`'s terms, so `d1`'s part kept the projection made without it. With that rule the
    /// eager join, checked first, had `n` in `[-10..=3]` at 781 (ends `[-10..=0]`), `m` in
    /// `[-5..=10]` at 1515 (ends `[1..=10]`) and `n` in `[-10..=10]` at 1820 (ends
    /// `[-10..=4]`). A part is now projected again when a group of linked constraints that
    /// holds two of its variables changes ([`Scope::lazy`]). At 397 and 550 the ends were
    /// already exact; a hole between them is lost (`n` is `[-10..=4]` at 397, the enumeration
    /// `[-10..=-9] ∪ [-5..=4]`), which is left open.
    #[test]
    fn the_lazy_join_has_the_enumeration_s_ends_at_these_seeds() {
        for seed in [397, 550, 781, 1_515, 1_820] {
            let case = Case::of(seed);
            let trace = case.trace(seed);
            if case.keeps() {
                case.run(&trace);
            } else {
                case.eager_join(&trace);
            }
        }
    }

    /// Random cases of both kinds. Each case's eager join is checked against the enumeration;
    /// a case where neither arm narrows a hub (`Case::keeps`) is also checked by
    /// `Case::run`.
    fn part(seeds: impl IntoIterator<Item = u64>) -> (usize, usize) {
        let (mut joins, mut kept) = (0, 0);
        for seed in seeds {
            let case = Case::of(seed);
            let trace = case.trace(seed);
            if !case.keeps() {
                case.eager_join(&trace);
                continue;
            }
            kept += case.run(&trace);
            joins += 1;
        }
        println!("{joins} joins, {kept} leaves stale before a join");
        (joins, kept)
    }

    /// Seeds 0 to 1,199 made 100 cases a test; a run now draws a few, of both kinds.
    #[test]
    fn random_seeds() {
        part(fresh_seeds("a join settles a star it drops", 8));
    }

    /// A leaf stale before a join that keeps the hubs (72 of seeds 0 to 199).
    #[test]
    fn seed_1_joins_with_a_leaf_stale() {
        let (joins, kept) = part([1]);
        assert!(joins > 0 && kept > 0, "{joins} joins, {kept} stale");
    }
}

/// The program of seed 1820 made small (item LAZY-hub-coarse): within `-10 <= n, m <= 10`,
/// `m >= 10 || n <= -9` and `n + m <= 14` leave `n` at most `4` (`m == 10` gives `n <= 4`,
/// `n <= -9` gives less). The bound `n + m <= 14` is on neither term of the disjunction, and
/// was assumed after it, so the disjunction's part was not projected again and `n` kept
/// `10`; with the other order, or both tests at once, it was `4`. Each order, eager and lazy,
/// now gives `n` in `[-10..=4]` and `m` in `[-10..=10]`.
#[test]
fn a_bound_on_two_names_of_a_disjunction_assumed_after_it_bounds_its_points() {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let sum = || prim(Prim::Add, var("n"), var("m"));
    let dif = || prim(Prim::Sub, var("m"), var("n"));
    let either = || or(ge(var("m"), 10), le(var("n"), -9));
    let orders: [(&str, Vec<Term>); 4] = [
        ("after", vec![either(), le(sum(), 14)]),
        (
            "after another bound",
            vec![either(), ge(dif(), -14), le(sum(), 14)],
        ),
        ("before", vec![le(sum(), 14), either()]),
        ("at once", vec![and(either(), le(sum(), 14))]),
    ];
    let p = Premises::new();
    for (how, tests) in orders {
        for lazy in [false, true] {
            let s = ints(&names(&["n", "m"]));
            let s = if lazy { s.lazy() } else { s };
            let s = ["n", "m"]
                .into_iter()
                .flat_map(|h| [ge(var(h), -10), le(var(h), 10)])
                .chain(tests.iter().cloned())
                .fold(s, |s, t| s.assume(&t, true, &p));
            for (h, lo, hi) in [("n", -10, 4), ("m", -10, 10)] {
                let ints = s.settled(&Arc::from(h)).ints().clone();
                assert_eq!(
                    ints,
                    IntervalSet::of(lo, hi),
                    "{h} with the bound {how}, lazy {lazy}"
                );
            }
        }
    }
}
