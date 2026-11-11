//! A star whose core holds two disjunctions of tests on its hubs (PROJECT-two-disj-lazy).
//!
//! `a >= n + 2 && a >= m + 2` with `n, m` in `[-12, 7]` makes `a` a star at the hubs `n` and
//! `m`. The eager scope projects the star in each case of a disjunction, where the cases
//! that are bottom drop out; the lazy scope settles it later, from the core, where the
//! projection takes one disjunction at a time (S16) and does not see that a side of one is
//! empty where the other holds. So a narrowing by a disjunction keeps the relation of its
//! live sides alone (`Scope::narrow_linear` in zedc-preimage), and both scopes settle `a` to the exact
//! least value. The tests compare the lazy and the eager answers with an enumeration of
//! the hubs.

use std::sync::Arc;

use zed_kernel::{Prim, Term};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use super::ints;
use super::nests::{diff_ge, int, names, or, prim, var};

/// The test `c0 * n + c1 * m >= c2`, with `c0` and `c1` in `{-1, 0, 1}`.
#[derive(Clone, Copy, Debug)]
struct HubTest(i64, i64, i64);

impl HubTest {
    fn holds(self, n: i64, m: i64) -> bool {
        self.0 * n + self.1 * m >= self.2
    }

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

/// The hubs' bounds.
const LO: i64 = -12;
const HI: i64 = 7;

/// The least value of `a` under the hubs' bounds, `a >= n + k1`, `a >= m + k2` and the
/// disjunctions `d1` and `d2`: by enumeration, from the eager scope, and from the lazy
/// scope settled. `None` where no state is left. Asserts that the scopes agree on bottom.
fn least(d1: &[HubTest], d2: &[HubTest], k1: i64, k2: i64) -> [Option<i64>; 3] {
    let all: Vec<Arc<str>> = names(&["n", "m", "a"]);
    let p = Premises::new();
    let mut tests = vec![
        prim(Prim::Ge, var("n"), int(LO)),
        prim(Prim::Le, var("n"), int(HI)),
        prim(Prim::Ge, var("m"), int(LO)),
        prim(Prim::Le, var("m"), int(HI)),
        diff_ge("a", "n", k1),
        diff_ge("a", "m", k2),
    ];
    for d in [d1, d2] {
        tests.push(d.iter().map(|g| g.term()).reduce(or).expect("a test"));
    }
    let (mut eager, mut lazy): (Scope, Scope) = (ints(&all), ints(&all).lazy());
    for t in &tests {
        eager = eager.assume(t, true, &p);
        lazy = lazy.assume(t, true, &p);
    }
    assert_eq!(eager.bottom, lazy.bottom, "{d1:?} {d2:?} {k1} {k2}");
    let exact = (LO..=HI)
        .flat_map(|n| (LO..=HI).map(move |m| (n, m)))
        .filter(|&(n, m)| d1.iter().any(|g| g.holds(n, m)) && d2.iter().any(|g| g.holds(n, m)))
        .map(|(n, m)| (n + k1).max(m + k2))
        .min();
    let a: Arc<str> = "a".into();
    let low = |s: &Scope, p: zedc::store::product::Product| {
        if s.bottom {
            None
        } else {
            p.ints().bounds().and_then(|(l, _)| l.to_i64())
        }
    };
    [
        exact,
        low(&eager, eager.get(&a)),
        low(&lazy, lazy.settled(&a)),
    ]
}

/// The case of the report: `n + m >= -1 || m - n >= 15`, where the hubs' bounds after the
/// first disjunction leave `m - n <= 11`, holds only as `n + m >= -1`, so `a >= 4`. Before
/// the fix the lazy scope settled `a` to `[2..]`.
#[test]
fn a_dead_side_of_the_second_disjunction_drops_out_of_the_lazy_core() {
    let d1 = [HubTest(1, -1, 6), HubTest(1, 1, 3), HubTest(0, -1, 10)];
    let d2 = [HubTest(1, 1, -1), HubTest(-1, 1, 15)];
    assert_eq!(least(&d1, &d2, 2, 2), [Some(4); 3]);
}

/// Seeds `seeds` of random cores: two disjunctions of two or three hub tests, and offsets
/// `k1, k2` in `[-3, 3]`. The lazy and the eager answers are each the enumerated one. A
/// piece of 400 seeds takes about 10 s.
fn random(seeds: std::ops::Range<u64>) {
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
    for seed in seeds {
        let mut rng = Rng::new(seed);
        let test = |rng: &mut Rng| {
            let (a, b) = rng.pick(&shapes);
            HubTest(a, b, rng.int(-14, 14))
        };
        let d1: Vec<HubTest> = (0..2 + rng.below(2)).map(|_| test(&mut rng)).collect();
        let d2: Vec<HubTest> = (0..2 + rng.below(2)).map(|_| test(&mut rng)).collect();
        let (k1, k2) = (rng.int(-3, 3), rng.int(-3, 3));
        let [exact, eager, lazy] = least(&d1, &d2, k1, k2);
        if exact.is_none() {
            // No state: the scopes may still keep one, since a disjunction is joined.
            continue;
        }
        assert_eq!(
            (eager, lazy),
            (exact, exact),
            "seed {seed}: {d1:?} {d2:?} k {k1} {k2}: eager, lazy, exact"
        );
    }
}

#[test]
fn random_cores_0() {
    random(0..400);
}

#[test]
fn random_cores_1() {
    random(400..800);
}

#[test]
fn random_cores_2() {
    random(800..1200);
}

#[test]
fn random_cores_3() {
    random(1200..1600);
}

#[test]
fn random_cores_4() {
    random(1600..2000);
}

#[test]
fn random_cores_5() {
    random(2000..2400);
}

#[test]
fn random_cores_6() {
    random(2400..2800);
}

#[test]
fn random_cores_7() {
    random(2800..3200);
}

/// `n + m >= 0 || n >= w + 1 || ... || n >= w + k - 1`, one disjunction: in the box `[-w, w]`
/// of [`star`] every side but the first is dead.
fn dead_sides(k: usize, w: i64) -> Term {
    (1..k as i64)
        .map(|i| HubTest(1, 0, w + i).term())
        .fold(HubTest(1, 1, 0).term(), or)
}

/// The hubs `n` and `m` in `[-w, w]` and the star `a >= n + 2 && a >= m + 2`.
fn star(lazy: bool, w: i64) -> Scope {
    let all: Vec<Arc<str>> = names(&["n", "m", "a"]);
    let p = Premises::new();
    let s = ints(&all);
    let mut s = if lazy { s.lazy() } else { s };
    for t in [
        prim(Prim::Ge, var("n"), int(-w)),
        prim(Prim::Le, var("n"), int(w)),
        prim(Prim::Ge, var("m"), int(-w)),
        prim(Prim::Le, var("m"), int(w)),
        diff_ge("a", "n", 2),
        diff_ge("a", "m", 2),
    ] {
        s = s.assume(&t, true, &p);
    }
    s
}

/// The narrowing by a disjunction of `k` sides, all dead but one, keeps the relation of the
/// live side in O(k log k): the sides' liveness comes from the cases, and one more relation
/// is taken, of the live side. (For many live sides, [`a_disjunction_of_live_sides_scales`].)
#[test]
fn a_disjunction_with_dead_sides_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let built = scaling::inputs(64, |k| (star(lazy, 4096), dead_sides(k, 4096)));
        let what = format!("a disjunction of k sides, all dead but one, lazy {lazy}");
        scaling::check_order(&what, 64, 1, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &p);
        });
    }
    // The live side gives `n + m >= 0`, so `max(n, m) >= 0` and `a >= 2`.
    let s = star(true, 5).assume(&dead_sides(5, 5), true, &p);
    let a: Arc<str> = "a".into();
    assert_eq!(
        s.settled(&a).ints().bounds().and_then(|(l, _)| l.to_i64()),
        Some(2)
    );
}

/// `n + m >= 0 || n + m >= -1 || ... || n + m >= -(k - 1)`, one disjunction: in the box
/// `[-w, w]` of [`star`], with `k <= 2w`, every side is live.
fn live_sides(k: usize) -> Term {
    (1..k as i64)
        .map(|i| HubTest(1, 1, -i).term())
        .fold(HubTest(1, 1, 0).term(), or)
}

/// The narrowing by a disjunction of `k` live sides over the two hubs is O(k log k): each
/// case is reduced once and the joins of the cases are not reduced (`join_cases` in
/// zedc-preimage, NARROW-many-relational-sides). Before, each join that was joined again was
/// reduced, projecting each of its sides again at each of the `log k` levels: 14.3 times
/// the bytes from 32 to 256 sides, above the limit of 14.1.
#[test]
fn a_disjunction_of_live_sides_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let built = scaling::inputs(32, |k| (star(lazy, 4096), live_sides(k)));
        let what = format!("a disjunction of k live sides, lazy {lazy}");
        scaling::check_order(&what, 32, 1, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &p);
        });
    }
    // The sides give `n + m >= -4`, so `max(n, m) >= -2` and `a >= 0`, eager and lazy.
    let a: Arc<str> = "a".into();
    for lazy in [false, true] {
        let s = star(lazy, 5).assume(&live_sides(5), true, &p);
        assert_eq!(
            s.settled(&a).ints().bounds().and_then(|(l, _)| l.to_i64()),
            Some(0),
            "lazy {lazy}"
        );
    }
}
