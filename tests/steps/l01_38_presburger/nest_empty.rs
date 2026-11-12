//! A nest of shared tests whose every path holds a contradiction on one variable
//! (PRES-nest-empty).

use std::sync::Arc;

use zed_tests::scaling::{self, Meter};
use zedc::store::presburger::extend::Extending;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide, project_each, satisfiable};

fn v(s: &str) -> Atom {
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
fn empty(k: usize) -> Formula {
    Formula::and(vec![nest(k), ge(&[("z", -1)], 0)])
}

/// The nest with `z <= 0 || (z == 1 && x[i] == i + 1 for each i)` beside it: one path, that of
/// the first disjunct at every level, has a point, `z == 1 && x[i] == i + 1`.
fn near(k: usize) -> Formula {
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
fn a_nest_is_projected_in_a_stack_its_depth_does_not_grow() {
    // The projection read each level of the nest by a recursive call, about 3.9 kB of stack
    // for each, so the nest of 512 levels overflowed a test thread's 2 MiB stack under some
    // builds, and a 256 KiB stack at about 60 levels. The levels are now kept on an explicit
    // stack (item MAIN-l01_38-failures). The answers are those of the test above, and of the
    // point's own values for the nest that has one.
    let run = || {
        for k in [64, 512] {
            let (each, left_out) = project_each(&empty(k), &[v("x0"), v("z")]).expect("answered");
            assert!(left_out.is_empty(), "depth {k}: {left_out:?}");
            assert!(
                each.iter().all(|p| p.as_ref().is_ok_and(|s| s.is_empty())),
                "depth {k}: {each:?}"
            );
        }
        let (each, left_out) = project_each(&near(512), &[v("x0"), v("z")]).expect("answered");
        assert!(left_out.is_empty(), "{left_out:?}");
        let one = |n: i64| zedc::store::interval::IntervalSet::of(n, n);
        assert_eq!(each, vec![Ok(one(1)), Ok(one(1))]);
    };
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(run)
        .expect("a thread")
        .join()
        .expect("answered in a 256 KiB stack");
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
fn chain(k: usize) -> Formula {
    chain_of(k, [(1, 1), (-1, 1), (1, 2), (-1, 2)])
}

/// [`chain`] with every disjunct bounding `y[i]` from below, at `i`, `2i`, `3i` and `4i`: the
/// hulls of `f` and `g` keep a bound on each `y[i]`, and differ in it.
fn chain_one_side(k: usize) -> Formula {
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
fn chain_two_atoms(k: usize) -> Formula {
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
fn pair(k: usize) -> Formula {
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
/// printed with the exponent of each step; then [`scaling::check_order`] at 64 and 512.
fn costs(what: &str, family: fn(usize) -> Formula) {
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
    let built = scaling::inputs(64, family);
    scaling::check_order(&format!("{what}, decided"), 64, 1, |n| {
        std::hint::black_box(decide(&built[&n]).is_ok());
    });
    scaling::check_order(&format!("{what}, its point sought"), 64, 1, |n| {
        std::hint::black_box(satisfiable(&built[&n]).is_ok());
    });
}

#[test]
fn a_nest_whose_every_path_is_empty_costs_its_depth() {
    // Each part is read once, and each hull is the one it is made from with a few forms
    // changed, O(log n) each (COMPLEXITY.md PRES-nest-empty).
    costs("a nest every path of which is empty", empty);
    let built = scaling::inputs(64, near);
    scaling::check_order(
        "a nest with one path that has a point, its point found",
        64,
        1,
        |n| {
            std::hint::black_box(satisfiable(&built[&n]).is_ok());
        },
    );
}

#[test]
fn a_chain_of_two_tests_held_by_both_costs_its_depth() {
    costs("a chain of two tests held by both", chain);
}

#[test]
fn a_chain_of_two_tests_held_by_both_bounding_one_side_costs_its_depth() {
    costs(
        "a chain of two tests held by both, bounding one side",
        chain_one_side,
    );
}

#[test]
fn a_chain_of_two_tests_with_atoms_of_their_own_costs_its_depth() {
    costs(
        "a chain of two tests with atoms of their own",
        chain_two_atoms,
    );
}

#[test]
fn two_tests_each_held_by_both_at_the_level_above_cost_their_depth() {
    costs("two tests held by both disjuncts of both", pair);
}
