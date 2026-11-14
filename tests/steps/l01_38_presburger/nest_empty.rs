//! A nest of shared tests whose every path holds a contradiction on one variable
//! (PRES-nest-empty).

use std::sync::Arc;

use zed_tests::scaling::{self, Meter};
use zedc::store::presburger::extend::Extending;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide, project_each, satisfiable};

pub(super) fn v(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

/// `Σ c·a + k >= 0`.
fn ge(t: &[(&str, i64)], k: i64) -> Formula {
    let l = (t.iter()).fold(Lin::constant(k), |l, (a, c)| {
        l.plus(&Lin::atom(v(a)).times(*c))
    });
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

/// `a == k`.
fn is(a: &str, k: i64) -> Formula {
    Formula::Con(Con::eq(&Lin::atom(v(a)), &Lin::constant(k)))
}

/// `f[i] = (x[i] >= i + 1 && f[i-1]) || (x[i] <= -2i - 3 && f[i-1])`, `f[-1] = z >= 1`:
/// `k` levels, `2^k` paths, one shared part per level.
fn nest(k: usize) -> Formula {
    let mut f = ge(&[("z", 1)], -1);
    for i in 0..k as i64 {
        let x = format!("x{i}");
        f = Formula::or(vec![
            Formula::and(vec![ge(&[(&x, 1)], -i - 1), f.clone()]),
            Formula::and(vec![ge(&[(&x, -1)], -2 * i - 3), f.clone()]),
        ]);
    }
    f
}

/// The nest with `z <= 0` beside it: every path holds `z >= 1 && z <= 0`.
pub(super) fn empty(k: usize) -> Formula {
    Formula::and(vec![nest(k), ge(&[("z", -1)], 0)])
}

/// The nest with `z <= 0 || (z == 1 && x[i] == i + 1 for each i)` beside it: one path, that of
/// the first disjunct at every level, has a point, `z == 1 && x[i] == i + 1`.
pub(super) fn near(k: usize) -> Formula {
    let point = (0..k as i64).map(|i| is(&format!("x{i}"), i + 1));
    let point = Formula::and(std::iter::once(is("z", 1)).chain(point).collect());
    Formula::and(vec![nest(k), Formula::or(vec![ge(&[("z", -1)], 0), point])])
}

#[test]
fn a_nest_whose_every_path_is_empty_is_not_refused() {
    // Before PRES-nest-empty the implied rows of a disjunction were read from each disjunct's
    // own rows only, so `z >= 1` at the bottom of the nest never met `z <= 0` beside it, and
    // eight levels were refused for their 256 paths (`Err(Disjuncts)`).
    let f = empty(8);
    assert_eq!(decide(&f), Ok(false), "{f}");
    assert_eq!(satisfiable(&f), Ok(None), "{f}");
}

#[test]
fn a_nest_whose_every_path_is_empty_is_answered_false_at_every_depth() {
    for k in [1, 8, 64, 512] {
        let f = empty(k);
        assert_eq!(decide(&f), Ok(false), "depth {k}");
        assert_eq!(satisfiable(&f), Ok(None), "depth {k}");
        let a = Extending::new().answers(&f);
        assert_eq!((a.holds, a.fails), (Ok(false), Ok(true)), "depth {k}");
        // Each projection of an empty formula is empty.
        let (each, left_out) = project_each(&f, &[v("x0"), v("z")]).expect("answered");
        assert!(left_out.is_empty(), "depth {k}: {left_out:?}");
        assert!(
            each.iter().all(|p| p.as_ref().is_ok_and(|s| s.is_empty())),
            "depth {k}: {each:?}"
        );
    }
}

#[test]
fn a_nest_with_one_path_that_has_a_point_is_projected_onto_it() {
    // The answers of `bench::nest_empty::a_nest_is_projected_in_a_stack_its_depth_does_not_grow`,
    // which runs depth 512 on a 256 KiB stack (author P178), at ordinary depths on the default
    // stack.
    let one = |n: i64| zedc::store::interval::IntervalSet::of(n, n);
    for k in [1, 8, 64] {
        let (each, left_out) = project_each(&near(k), &[v("x0"), v("z")]).expect("answered");
        assert!(left_out.is_empty(), "depth {k}: {left_out:?}");
        assert_eq!(each, vec![Ok(one(1)), Ok(one(1))], "depth {k}");
    }
}

#[test]
fn a_nest_with_one_path_that_has_a_point_is_answered_with_it() {
    for k in [1, 8, 64, 512] {
        let f = near(k);
        assert_eq!(decide(&f), Ok(true), "depth {k}");
        let m = satisfiable(&f).expect("answered").expect("a point");
        assert!(f.holds(&m), "depth {k}: {m:?}");
        assert_eq!(m[&v("z")], 1.into(), "depth {k}");
        for i in 0..k {
            assert_eq!(m[&v(&format!("x{i}"))], (i as i64 + 1).into(), "depth {k}");
        }
    }
}

/// `f[i] = (y[i] >= i && f[i-1]) || (y[i] <= -i && g[i-1])` and
/// `g[i] = (y[i] >= 2i && g[i-1]) || (y[i] <= -2i && f[i-1])`, from `f[-1] = z >= 1` and
/// `g[-1] = z >= 2`, with `z <= 0` beside: two shared tests at each level, each held by both
/// at the level above, every path empty.
pub(super) fn chain(k: usize) -> Formula {
    chain_of(k, [(1, 1), (-1, 1), (1, 2), (-1, 2)])
}

/// [`chain`] with every disjunct bounding `y[i]` from below, at `i`, `2i`, `3i` and `4i`: the
/// hulls of `f` and `g` keep a bound on each `y[i]`, and differ in it.
pub(super) fn chain_one_side(k: usize) -> Formula {
    chain_of(k, [(1, 1), (1, 2), (1, 3), (1, 4)])
}

/// [`chain`] with the disjuncts bounding `y[i]` as `sign·y[i] >= times·i`, in the order
/// `f` from `f`, `f` from `g`, `g` from `g`, `g` from `f`.
fn chain_of(k: usize, bounds: [(i64, i64); 4]) -> Formula {
    let (mut f, mut g) = (ge(&[("z", 1)], -1), ge(&[("z", 1)], -2));
    for i in 0..k as i64 {
        let y = format!("y{i}");
        let at = |(sign, times): (i64, i64), h: &Formula| {
            Formula::and(vec![ge(&[(&y, sign)], -times * i), h.clone()])
        };
        let [ff, fg, gg, gf] = bounds;
        (f, g) = (
            Formula::or(vec![at(ff, &f), at(fg, &g)]),
            Formula::or(vec![at(gg, &g), at(gf, &f)]),
        );
    }
    Formula::and(vec![f, ge(&[("z", -1)], 0)])
}

/// [`chain`] with `g`'s disjuncts bounding `w[i]` where `f`'s bound `y[i]`: the two tests at
/// each level have atoms of their own that the other lacks.
pub(super) fn chain_two_atoms(k: usize) -> Formula {
    let (mut f, mut g) = (ge(&[("z", 1)], -1), ge(&[("z", 1)], -2));
    for i in 0..k as i64 {
        let (y, w) = (format!("y{i}"), format!("w{i}"));
        let at =
            |a: &str, sign: i64, h: &Formula| Formula::and(vec![ge(&[(a, sign)], -i), h.clone()]);
        (f, g) = (
            Formula::or(vec![at(&y, 1, &f), at(&y, -1, &g)]),
            Formula::or(vec![at(&w, 1, &g), at(&w, -1, &f)]),
        );
    }
    Formula::and(vec![f, ge(&[("z", -1)], 0)])
}

/// `a[i] = (u[i] >= i && a[i-1] && b[i-1]) || (u[i] <= -i && a[i-1] && b[i-1])` and `b[i]`
/// likewise with `v[i]`, from `a[-1] = z >= 1` and `b[-1] = z >= 2`, with `z <= 0` beside:
/// two shared tests at each level, both held by each disjunct of both at the level above,
/// each with an atom of its own; every path empty.
pub(super) fn pair(k: usize) -> Formula {
    let (mut a, mut b) = (ge(&[("z", 1)], -1), ge(&[("z", 1)], -2));
    for i in 0..k as i64 {
        let (u, w) = (format!("u{i}"), format!("v{i}"));
        let at =
            |x: &str, sign: i64| Formula::and(vec![ge(&[(x, sign)], -i), a.clone(), b.clone()]);
        (a, b) = (
            Formula::or(vec![at(&u, 1), at(&u, -1)]),
            Formula::or(vec![at(&w, 1), at(&w, -1)]),
        );
    }
    Formula::and(vec![a, ge(&[("z", -1)], 0)])
}

#[test]
fn tests_with_atoms_of_their_own_held_by_both_are_answered_false() {
    for k in [1, 8, 64, 512] {
        for (what, f) in [("two atoms", chain_two_atoms(k)), ("pair", pair(k))] {
            assert_eq!(decide(&f), Ok(false), "{what}, depth {k}");
            assert_eq!(satisfiable(&f), Ok(None), "{what}, depth {k}");
        }
    }
}

/// The formula with a copy of each part at each place that holds it.
fn written_out(f: &Formula) -> Formula {
    match f {
        Formula::Con(c) => Formula::Con(c.clone()),
        Formula::Not(g) => Formula::Not(Shared::new(written_out(g))),
        Formula::And(gs) => Formula::And(Shared::new(gs.iter().map(written_out).collect())),
        Formula::Or(gs) => Formula::Or(Shared::new(gs.iter().map(written_out).collect())),
    }
}

#[test]
fn chains_of_two_tests_held_by_both_are_answered_false() {
    for k in [1, 8, 64, 512] {
        for (what, f) in [("chain", chain(k)), ("one side", chain_one_side(k))] {
            assert_eq!(decide(&f), Ok(false), "{what}, depth {k}");
            assert_eq!(satisfiable(&f), Ok(None), "{what}, depth {k}");
        }
    }
}

#[test]
fn the_answers_are_those_of_the_formulas_written_out() {
    // The hulls are kept by the ids of the parts, but are those of the rows alone: the formula
    // written out, with no part held twice, has the same answers (COMPLEXITY.md S31).
    for k in 1..=6 {
        let families = [
            ("nest", nest(k)),
            ("empty", empty(k)),
            ("near", near(k)),
            ("chain", chain(k)),
            ("one side", chain_one_side(k)),
            ("two atoms", chain_two_atoms(k)),
        ];
        // Written out, `pair` at depth `k` has `2^(2^k - 1)` paths: depths 1 to 3 only.
        let pairs = (k <= 3).then(|| ("pair", pair(k)));
        for (what, f) in families.into_iter().chain(pairs) {
            let w = written_out(&f);
            assert_eq!(decide(&f), decide(&w), "{what}, depth {k}");
            assert_eq!(satisfiable(&f), satisfiable(&w), "{what}, depth {k}");
            let syms = [v("z"), v("x0"), v("y0"), v("w0"), v("u0")];
            let (a, b) = (project_each(&f, &syms), project_each(&w, &syms));
            assert_eq!(format!("{a:?}"), format!("{b:?}"), "{what}, depth {k}");
        }
    }
}

/// The least instructions of three runs of `decide` on each family member at depths 32 to 512,
/// printed with the exponent of each step; then [`scaling::check_order`] at `n` and `8n`.
pub(super) fn costs(what: &str, n: usize, family: fn(usize) -> Formula) {
    let mut meter = Meter::new();
    let sizes = [32, 64, 128, 256, 512];
    let built: Vec<Formula> = sizes.iter().map(|&k| family(k)).collect();
    let cost: Vec<u64> = (built.iter())
        .map(|f| {
            (0..3)
                .map(|_| meter.work(|| assert_eq!(decide(f), Ok(false))).units)
                .min()
        })
        .map(|c| c.expect("runs"))
        .collect();
    for i in 1..sizes.len() {
        let e = (cost[i] as f64 / cost[i - 1] as f64).log2();
        println!(
            "{what}, depth {}: {} {}, exponent {e:.2}",
            sizes[i],
            cost[i],
            meter.unit()
        );
    }
    let built = scaling::inputs(n, family);
    scaling::check_order(&format!("{what}, decided"), n, 1, |n| {
        std::hint::black_box(decide(&built[&n]).is_ok());
    });
    scaling::check_order(&format!("{what}, its point sought"), n, 1, |n| {
        std::hint::black_box(satisfiable(&built[&n]).is_ok());
    });
}
