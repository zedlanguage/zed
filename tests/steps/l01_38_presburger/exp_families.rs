//! The families of formulas PRES-exp-audit built (2026-11-09) to reach the paths of the
//! Presburger solver that could grow exponentially in the size of the formula: subset sum,
//! nests of shared disjunctions with and without a point, a nest linked by sums, a chain of
//! inexact eliminations, a chain of three-term rows, and random systems of rows on windows of
//! consecutive variables. For each family and each entry point (`decide`, `satisfiable`,
//! `project_each`, `Extending::answers`) there is a test of its answers against an answer found
//! another way (a search of every point of a small box, a closed form, or a dynamic program over
//! the chain), and a test of its instructions at sizes each twice the last, held to the bound
//! COMPLEXITY.md states for the path (row PRES-exp-families). `nest_empty.rs` and
//! `linked_nest.rs` test the nests and the linked sums in other ways.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling::{self, Meter, Work};
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::extend::Extending;
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, Model, ROW_SUMS_OFF, Refusal, decide, project_each, satisfiable,
};

/// The stack of the thread each measured run takes.
const STACK: usize = 1 << 26;

fn v(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

fn lin(t: &[(&str, i64)], k: i64) -> Lin {
    (t.iter()).fold(Lin::constant(k), |l, (a, c)| {
        l.plus(&Lin::atom(v(a)).times(*c))
    })
}

/// `Σ c·a + k >= 0`.
fn ge(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::ge(&lin(t, k), &Lin::constant(0)))
}

/// `Σ c·a + k == 0`.
fn eq(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::eq(&lin(t, k), &Lin::constant(0)))
}

/// The weights of [`subset_sum`]: `1000 + 37 i² mod 991`, between 1000 and 1990.
fn weights(k: usize) -> Vec<i64> {
    (0..k)
        .map(|i| 1000 + 37 * i as i64 * i as i64 % 991)
        .collect()
}

/// The least number from half the sum of `w` up that no subset of `w` sums to, found by the
/// table of the sums of subsets.
fn target(w: &[i64]) -> i64 {
    let mut sums = vec![false; w.iter().sum::<i64>() as usize + 1];
    sums[0] = true;
    for &x in w {
        for s in (x as usize..sums.len()).rev() {
            if sums[s - x as usize] {
                sums[s] = true;
            }
        }
    }
    let half = sums.len() / 2;
    (half..sums.len()).find(|&s| !sums[s]).expect("a gap") as i64
}

/// `y[i] == 0 || y[i] == w[i]` for each i, and `Σ y[i] == t`, t no subset sum of the weights:
/// k separate disjunctions and one row over all of them, no point.
pub(super) fn subset_sum(k: usize) -> Formula {
    subset_sum_by(&weights(k))
}

/// [`subset_sum`] over the weights `1000 + 37 i² mod 3203`, between 1000 and 4202 and distinct
/// to k = 1602 (`slack_scale::squares_mod`): the weights of [`subset_sum`] repeat from i = 496.
pub(super) fn subset_sum_untied(k: usize) -> Formula {
    subset_sum_by(&crate::slack_scale::squares_mod(k, 1000, 3203))
}

/// [`subset_sum`] over the weights `w`.
fn subset_sum_by(w: &[i64]) -> Formula {
    let k = w.len();
    let names: Vec<String> = (0..k).map(|i| format!("y{i}")).collect();
    let mut fs: Vec<Formula> = (names.iter().zip(w))
        .map(|(y, &w)| Formula::or(vec![eq(&[(y, 1)], 0), eq(&[(y, 1)], -w)]))
        .collect();
    let terms: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    fs.push(eq(&terms, -target(w)));
    Formula::and(fs)
}

/// `f[i] = (x[i] >= 0 && f[i-1]) || (x[i] <= -1 && f[i-1])` from `f[-1] = z >= 1`, with
/// `z <= 0` beside it: k shared parts, 2^k paths, every one holding `z >= 1 && z <= 0`.
pub(super) fn shared_nest(k: usize) -> Formula {
    let mut f = ge(&[("z", 1)], -1);
    for i in 0..k {
        let x = format!("x{i}");
        f = Formula::or(vec![
            Formula::and(vec![ge(&[(&x, 1)], 0), f.clone()]),
            Formula::and(vec![ge(&[(&x, -1)], -1), f.clone()]),
        ]);
    }
    Formula::and(vec![f, ge(&[("z", -1)], 0)])
}

/// `f[i] = (x[i] == x[i-1] && f[i-1]) || (x[i] == x[i-1] + 2^i && f[i-1])` for i in 1..=k from
/// `f[0] = x0 == 0`, with `x[k] == 2h + 1` beside it: k shared parts linked by rows, 2^k sums,
/// every one even, so no point.
pub(super) fn shared_sums(k: usize) -> Formula {
    let mut f = eq(&[("x0", 1)], 0);
    for i in 1..=k {
        let (a, b) = (format!("x{i}"), format!("x{}", i - 1));
        let w = 2i64.pow(i.min(40) as u32);
        f = Formula::or(vec![
            Formula::and(vec![eq(&[(&a, 1), (&b, -1)], 0), f.clone()]),
            Formula::and(vec![eq(&[(&a, 1), (&b, -1)], -w), f.clone()]),
        ]);
    }
    let top = format!("x{k}");
    Formula::and(vec![f, eq(&[(&top, 1), ("h", -2)], -1)])
}

/// `0 <= 2 x[i+1] - 3 x[i] <= 1` for i in 0..k, with `1 <= x0 <= 9`: every elimination inexact,
/// one connected chain.
pub(super) fn dark_chain(k: usize) -> Formula {
    let mut fs = vec![ge(&[("x0", 1)], -1), ge(&[("x0", -1)], 9)];
    for i in 0..k {
        let (a, b) = (format!("x{}", i + 1), format!("x{i}"));
        fs.push(ge(&[(&a, 2), (&b, -3)], 0));
        fs.push(ge(&[(&a, -2), (&b, 3)], 1));
    }
    Formula::and(fs)
}

/// `0 <= 3 a[i] + 5 a[i+1] - 7 b[i] <= 2` and `-1 <= 7 a[i+1] - 3 b[i] <= 4` for i in 0..k, with
/// `5 <= a0 <= 50`: three-term rows with coefficients 3, 5 and 7, chained, which reach the
/// splinters of dark eliminations.
pub(super) fn skew_block(k: usize) -> Formula {
    let mut fs = Vec::new();
    for i in 0..k {
        let (a, b, c) = (format!("a{i}"), format!("a{}", i + 1), format!("b{i}"));
        fs.push(ge(&[(&a, 3), (&b, 5), (&c, -7)], 0));
        fs.push(ge(&[(&a, -3), (&b, -5), (&c, 7)], 2));
        fs.push(ge(&[(&b, 7), (&c, -3)], 1));
        fs.push(ge(&[(&b, -7), (&c, 3)], 4));
    }
    fs.push(ge(&[("a0", 1)], -5));
    fs.push(ge(&[("a0", -1)], 50));
    Formula::and(fs)
}

/// `f[i] = (x[i] >= i + 1 && f[i-1]) || (x[i] <= -2i - 3 && f[i-1])` from `f[-1] = z >= 1`:
/// k shared parts and 2^k paths, each with a point.
pub(super) fn nest_point(k: usize) -> Formula {
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

/// [`nest_point`] with `z <= 0` beside it: no path has a point.
pub(super) fn nest_empty(k: usize) -> Formula {
    Formula::and(vec![nest_point(k), ge(&[("z", -1)], 0)])
}

/// One row of a random window system: `Σ c[j] x[start + j] + k >= 0`.
struct Row {
    start: usize,
    c: Vec<i64>,
    k: i64,
}

/// The rows of a random system over `x0 .. x(n-1)`: `per` rows on each window of `width`
/// consecutive variables, coefficients in ±1..=11 (never 0), constants in -6..=6; each
/// variable also lies in [-12, 12] (the box [`windows`] adds).
fn window_rows(n: usize, seed: u64, width: usize, per: usize) -> Vec<Row> {
    let mut r = Rng::new(seed * 7919 + n as u64);
    let mut rows = Vec::new();
    for start in 0..n + 1 - width {
        for _ in 0..per {
            let c = (0..width)
                .map(|_| r.int(1, 11) * if r.below(2) == 0 { 1 } else { -1 })
                .collect();
            rows.push(Row {
                start,
                c,
                k: r.int(-6, 6),
            });
        }
    }
    rows
}

/// The bound of each variable of a window system: `x[i]` lies in `-BOX..=BOX`.
const BOX: i64 = 12;

/// The formula of [`window_rows`], with the box.
fn windows(n: usize, seed: u64, width: usize, per: usize) -> Formula {
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let mut fs = Vec::new();
    for x in &names {
        fs.push(ge(&[(x, 1)], BOX));
        fs.push(ge(&[(x, -1)], BOX));
    }
    for row in window_rows(n, seed, width, per) {
        let t: Vec<(&str, i64)> = (row.c.iter().enumerate())
            .map(|(j, &c)| (names[row.start + j].as_str(), c))
            .collect();
        fs.push(ge(&t, row.k));
    }
    Formula::and(fs)
}

/// The values of `x0` at the points of the window system, by a dynamic program from the last
/// window back: a state is the values of `width - 1` consecutive variables, and a state at
/// window i is kept when some value of the next variable meets that window's rows and leads to
/// a state kept at window i + 1. O(n · 25^width · rows per window).
fn windows_x0(n: usize, seed: u64, width: usize, per: usize) -> BTreeSet<i64> {
    let rows = window_rows(n, seed, width, per);
    let side = (2 * BOX + 1) as usize;
    let states = side.pow(width as u32 - 1);
    let last = n + 1 - width;
    let mut kept = vec![true; states];
    for i in (0..last).rev() {
        let mine: Vec<&Row> = rows.iter().filter(|r| r.start == i).collect();
        let mut before = vec![false; states];
        for (s, keep) in before.iter_mut().enumerate() {
            let mut vals: Vec<i64> = (0..width - 1)
                .map(|j| (s / side.pow(j as u32) % side) as i64 - BOX)
                .collect();
            vals.push(0);
            *keep = (-BOX..=BOX).any(|x| {
                vals[width - 1] = x;
                let next = s / side + (x + BOX) as usize * side.pow(width as u32 - 2);
                kept[next]
                    && (mine.iter()).all(|r| {
                        (r.c.iter().zip(&vals)).map(|(c, x)| c * x).sum::<i64>() + r.k >= 0
                    })
            });
        }
        kept = before;
    }
    (kept.iter().enumerate())
        .filter(|(_, k)| **k)
        .map(|(s, _)| (s % side) as i64 - BOX)
        .collect()
}

/// The values of `a0` at the points of [`skew_block`], by following each `a0` in 5..=50 along
/// the chain. With `d = 7 a[i+1] - 3 b[i]` in -1..=4, three times the first pair of rows reads
/// `0 <= 9 a[i] + 15 a[i+1] - 7 (7 a[i+1] - d) <= 6`, that is `34 a[i+1]` in
/// `9 a[i] + 7 d - 6 ..= 9 a[i] + 7 d`, inside `9 a[i] - 13 ..= 9 a[i] + 28`: each `a[i+1]` in that
/// range is tried with each `b[i] = (7 a[i+1] - d) / 3` that is whole, on the rows themselves.
fn skew_a0(k: usize) -> BTreeSet<i64> {
    let next = |a: i64| -> BTreeSet<i64> {
        let lo = (9 * a - 13).div_euclid(34);
        let hi = (9 * a + 28).div_euclid(34);
        (lo..=hi + 1)
            .filter(|&n| {
                (-1..=4).any(|d: i64| {
                    let b3 = 7 * n - d;
                    let b = b3.div_euclid(3);
                    b3.rem_euclid(3) == 0 && (0..=2).contains(&(3 * a + 5 * n - 7 * b))
                })
            })
            .collect()
    };
    (5..=50)
        .filter(|&a0| {
            let mut at = BTreeSet::from([a0]);
            for _ in 0..k {
                at = at.iter().flat_map(|&a| next(a)).collect();
            }
            !at.is_empty()
        })
        .collect()
}

/// The values of `on` at the points of `f` with every atom in `lo..=hi`, each point tried with
/// [`Formula::holds`]: (the number of points, the values).
fn brute(f: &Formula, on: &str, (lo, hi): (i64, i64)) -> (u64, BTreeSet<i64>) {
    let atoms: Vec<Atom> = f.atoms().into_iter().collect();
    let at = atoms.iter().position(|a| *a == v(on));
    let mut point = vec![lo; atoms.len()];
    let (mut count, mut values) = (0, BTreeSet::new());
    loop {
        let m: Model = (atoms.iter().cloned())
            .zip(point.iter().map(|&x| x.into()))
            .collect();
        if f.holds(&m) {
            count += 1;
            values.insert(at.map_or(0, |i| point[i]));
        }
        let Some(i) = point.iter().position(|&x| x < hi) else {
            return (count, values);
        };
        point[i] += 1;
        point[..i].fill(lo);
    }
}

/// The answer, found another way, that each entry point's answer on a formula is held to.
struct Truth<'a> {
    /// Whether the formula has a point.
    point: bool,
    /// The atom whose projection is asked for.
    on: &'a str,
    /// Whether a value of `on` is that of a point.
    member: &'a dyn Fn(i64) -> bool,
    /// The values of `on` the projection is compared on.
    near: (i64, i64),
}

/// The projection of `f` onto `on`, a refusal of the whole or of `on` alike.
fn projection(f: &Formula, on: &str) -> Result<IntervalSet, Refusal> {
    let (mut each, _) = project_each(f, &[v(on)])?;
    each.remove(0)
}

/// The value of `a` in `m`, zero when it is absent (as [`Formula::holds`] reads it).
fn value(m: &Model, a: &str) -> Option<i64> {
    let x = m.get(&v(a)).map_or(Some(0), |x| x.to_i128());
    x.and_then(|x| i64::try_from(x).ok())
}

/// Checks every entry point on `f` against `truth`. The entry points named in `answered` must
/// answer: 'd' `decide`, 's' `satisfiable`, 'a' `Extending::answers`, 'p' `project_each`
/// exactly on `truth.near`, 'h' `project_each` with a set that holds every value of a point.
/// The others may refuse, and where they answer they must agree. Every family has a point
/// outside it (zero, or `x0 = 13` for the window systems), so `answers` must find it can fail.
fn agrees(what: &str, f: &Formula, truth: &Truth, answered: &str) {
    match decide(f) {
        Ok(b) => assert_eq!(b, truth.point, "{what}: decide"),
        Err(e) => assert!(!answered.contains('d'), "{what}: decide refused, {e:?}"),
    }
    match satisfiable(f) {
        Ok(Some(m)) => {
            assert!(truth.point, "{what}: satisfiable gave {m:?} for no point");
            assert!(f.holds(&m), "{what}: satisfiable gave {m:?}, not a point");
            let x = value(&m, truth.on);
            assert!(
                x.is_some_and(truth.member),
                "{what}: satisfiable gave {} = {x:?}",
                truth.on
            );
        }
        Ok(None) => assert!(!truth.point, "{what}: satisfiable found no point"),
        Err(e) => assert!(
            !answered.contains('s'),
            "{what}: satisfiable refused, {e:?}"
        ),
    }
    let a = Extending::new().answers(f);
    match a.holds {
        Ok(b) => assert_eq!(b, truth.point, "{what}: answers, holds"),
        Err(e) => assert!(!answered.contains('a'), "{what}: answers refused, {e:?}"),
    }
    assert_eq!(a.fails, Ok(true), "{what}: answers, fails");
    match projection(f, truth.on) {
        Ok(s) => {
            let (lo, hi) = truth.near;
            for x in lo..=hi {
                if (truth.member)(x) {
                    assert!(s.contains(x), "{what}: {x} is missing from {s:?}");
                } else if answered.contains('p') {
                    assert!(!s.contains(x), "{what}: {x} is in {s:?}");
                }
            }
        }
        Err(e) => assert!(
            !answered.contains('p') && !answered.contains('h'),
            "{what}: project_each refused, {e:?}"
        ),
    }
}

#[test]
fn subset_sum_has_no_point() {
    for k in 1..=12 {
        let w = weights(k);
        let t = target(&w);
        // Each of the 2^k subsets, summed apart from the table `target` reads.
        for mask in 0..1u32 << k {
            let s: i64 = (0..k).filter(|i| mask >> i & 1 == 1).map(|i| w[i]).sum();
            assert_ne!(s, t, "k = {k}, subset {mask:b}");
        }
        if k <= 6 {
            let f = subset_sum(k);
            for mask in 0..1u32 << k {
                let m: Model = (0..k)
                    .map(|i| (v(&format!("y{i}")), (w[i] * (mask >> i & 1) as i64).into()))
                    .collect();
                assert!(!f.holds(&m), "k = {k}, subset {mask:b}");
            }
        }
    }
    let none = |_: i64| false;
    let truth = Truth {
        point: false,
        on: "y0",
        member: &none,
        near: (-10, 2010),
    };
    for (k, alone) in (1..=6).flat_map(|k| [(k, false), (k, true)]) {
        // The method of PRES-overlap-fast (module `row_sums`) answers every entry point
        // exactly. The solver alone, from k = 5 on, refuses `decide`, `satisfiable` and
        // `answers` (`Disjuncts`), and its projection is wider than the empty set:
        // COMPLEXITY.md PRES-exp-families, A87.
        let answered = if k <= 4 || !alone { "dsap" } else { "h" };
        let f = subset_sum(k);
        ROW_SUMS_OFF.with(|o| o.set(alone));
        agrees(
            &format!("subset sum, k = {k}, solver alone: {alone}"),
            &f,
            &truth,
            answered,
        );
        if let Ok(s) = projection(&f, "y0") {
            let w0 = weights(1)[0];
            assert!(s.is_subset(&IntervalSet::of(0, w0)), "k = {k}: {s:?}");
        }
        ROW_SUMS_OFF.with(|o| o.set(false));
    }
}

#[test]
fn a_shared_nest_with_tied_names_has_no_point() {
    for k in 1..=3 {
        assert_eq!(brute(&shared_nest(k), "z", (-3, 3)).0, 0, "k = {k}");
    }
    let none = |_: i64| false;
    let truth = Truth {
        point: false,
        on: "z",
        member: &none,
        near: (-20, 20),
    };
    for k in [1, 2, 8, 64] {
        agrees(
            &format!("shared nest, k = {k}"),
            &shared_nest(k),
            &truth,
            "dsap",
        );
    }
}

#[test]
fn a_nest_linked_by_sums_has_no_point() {
    // Each value of x[k] is a sum of distinct powers 2^i, i >= 1: even, never 2h + 1.
    for k in 1..=2 {
        assert_eq!(brute(&shared_sums(k), "x0", (-1, 7)).0, 0, "k = {k}");
    }
    let none = |_: i64| false;
    let truth = Truth {
        point: false,
        on: "x0",
        member: &none,
        near: (-20, 20),
    };
    for k in [1, 2, 8, 64] {
        // `decide`, `satisfiable` and `answers` refuse (`Disjuncts`) where the projection
        // shows the formula empty: COMPLEXITY.md PRES-exp-families.
        let answered = if k <= 2 { "dsap" } else { "p" };
        agrees(
            &format!("linked sums, k = {k}"),
            &shared_sums(k),
            &truth,
            answered,
        );
    }
}

#[test]
fn a_chain_of_inexact_eliminations_has_one_point_per_start() {
    // `0 <= 2 x[i+1] - 3 x[i] <= 1` holds for one x[i+1] only, `ceil(3 x[i] / 2)`: nine points,
    // one for each x0 in [1, 9].
    for k in 1..=2 {
        let (count, x0) = brute(&dark_chain(k), "x0", (-1, 21));
        assert_eq!(count, 9, "k = {k}");
        assert_eq!(x0, (1..=9).collect(), "k = {k}");
    }
    let start = |x: i64| (1..=9).contains(&x);
    let truth = Truth {
        point: true,
        on: "x0",
        member: &start,
        near: (-20, 20),
    };
    for k in [1, 2, 16, 64] {
        let f = dark_chain(k);
        // `project_each` refuses (`Shadows`) where `decide` answers: COMPLEXITY.md
        // PRES-exp-families.
        agrees(&format!("dark chain, k = {k}"), &f, &truth, "dsa");
        let m = satisfiable(&f).expect("answered").expect("a point");
        let x = |i: usize| value(&m, &format!("x{i}"));
        for i in 0..k.min(30) {
            let a = x(i).expect("small");
            assert_eq!(
                x(i + 1),
                Some((3 * a + 1i64).div_euclid(2)),
                "k = {k}, x{}",
                i + 1
            );
        }
    }
}

#[test]
fn a_chain_of_three_term_rows_is_answered_as_by_following_the_chain() {
    let (_, x0) = brute(&skew_block(1), "a0", (-2, 50));
    assert_eq!(x0, skew_a0(1), "k = 1");
    for k in [1, 2, 4, 16, 64] {
        let a0 = skew_a0(k);
        assert!(!a0.is_empty(), "k = {k}");
        let member = |x: i64| a0.contains(&x);
        let truth = Truth {
            point: true,
            on: "a0",
            member: &member,
            near: (-5, 60),
        };
        // Main refuses (`Shadows`) on every entry point from k = 16 on: COMPLEXITY.md
        // PRES-exp-families.
        agrees(&format!("skew block, k = {k}"), &skew_block(k), &truth, "");
    }
}

#[test]
fn a_nest_whose_every_path_has_a_point_is_answered_with_it() {
    let start = |x: i64| x >= 1 || x <= -3;
    for k in 1..=3 {
        let (_, x0) = brute(&nest_point(k), "x0", (-8, 8));
        assert_eq!(x0, (-8..=8).filter(|&x| start(x)).collect(), "k = {k}");
    }
    let truth = Truth {
        point: true,
        on: "x0",
        member: &start,
        near: (-50, 50),
    };
    for k in [1, 2, 8, 64] {
        agrees(
            &format!("nest with points, k = {k}"),
            &nest_point(k),
            &truth,
            "dsap",
        );
    }
}

#[test]
fn a_nest_whose_every_path_is_empty_has_no_point() {
    for k in 1..=3 {
        assert_eq!(brute(&nest_empty(k), "x0", (-6, 6)).0, 0, "k = {k}");
    }
    let none = |_: i64| false;
    let truth = Truth {
        point: false,
        on: "x0",
        member: &none,
        near: (-50, 50),
    };
    for k in [1, 2, 8, 64] {
        agrees(
            &format!("empty nest, k = {k}"),
            &nest_empty(k),
            &truth,
            "dsap",
        );
    }
}

/// The window program's values of `x0` are those of every point of the box, counted one by one:
/// over 3 variables for both shapes and three seeds, where windows of two chain a state across
/// two windows and windows of three have one window; and over 4 variables for windows of three,
/// which chain a state of two variables. Over 4 variables for both shapes and three seeds
/// (2.7 s at load 25, 25^4 points each) is in `bench::exp_families`.
#[test]
fn the_window_program_finds_the_points_of_the_box() {
    for (width, per) in [(3, 2), (2, 3)] {
        for seed in 0..3 {
            window_program_finds_the_points_of_the_box(3, width, per, seed);
        }
    }
    window_program_finds_the_points_of_the_box(4, 3, 2, 0);
}

/// [`windows_x0`] over `n` variables is the values of `x0` at the points of [`windows`],
/// counted one by one over the box.
pub(super) fn window_program_finds_the_points_of_the_box(
    n: usize,
    width: usize,
    per: usize,
    seed: u64,
) {
    let (_, x0) = brute(&windows(n, seed, width, per), "x0", (-BOX, BOX));
    assert_eq!(
        x0,
        windows_x0(n, seed, width, per),
        "n = {n}, {width}, {per}, {seed}"
    );
}

/// [`random_window_systems_answer`] at four seeds drawn from a new seed each run, below 2^40 so
/// that [`windows`]' `seed * 7919 + n` fits. Seeds 0 to 19 (0.65 s at load 14, 1.06 s at load
/// 38) are in `bench::exp_families`.
#[test]
fn random_window_systems_are_answered_as_the_window_program_answers() {
    let (mut rng, seed) = Rng::fresh("exp_families random windows");
    let seeds: Vec<u64> = (0..4).map(|_| rng.next_u64() >> 24).collect();
    random_window_systems_answer(&seeds, &format!("fresh seed {seed}"));
}

/// The four seeds [`random_window_systems_are_answered_as_the_window_program_answers`] drew
/// from fresh seed 13014466797380974686, at which it took 11 to 21 s where it takes 0.66 s
/// (FAIL-window-seed-13014466797380974686): the projection onto `x0` of the windows of 3, 2
/// rows each, n = 12, seed 1096302828291 built two shadows of 6,425,279 terms, uncharged,
/// before its work limit refused them. The case, cut to its first 8 windows, is
/// `exact::projection::tests::a_shadow_past_the_limit_is_refused_while_it_is_made`.
#[test]
fn random_window_systems_at_the_seeds_of_a_slow_run() {
    random_window_systems_answer(
        &[421299115613, 713586870135, 1096302828291, 316746888211],
        "fresh seed 13014466797380974686",
    );
}

/// [`windows`] of 3 variables and 2 rows and of 2 variables and 3 rows, over 6, 12 and 24
/// variables, at each of `seeds`, answered as the window program answers; `at` is named on
/// failure.
pub(super) fn random_window_systems_answer(seeds: &[u64], at: &str) {
    for (width, per) in [(3, 2), (2, 3)] {
        for n in [6, 12, 24] {
            for &seed in seeds {
                let x0 = windows_x0(n, seed, width, per);
                let member = |x: i64| x0.contains(&x);
                let truth = Truth {
                    point: !x0.is_empty(),
                    on: "x0",
                    member: &member,
                    near: (-BOX - 2, BOX + 2),
                };
                let what =
                    format!("{at}: windows of {width}, {per} rows each, n = {n}, seed {seed}");
                let f = windows(n, seed, width, per);
                // Main refuses (`Growth`) on most systems of windows of three from n = 12 on.
                // On windows of two it answers, except where a point could lie only in a
                // splinter that would have to be split again with as many live variables left:
                // DESIGN.md sec:diagnostics allows that refusal, `Shadows`, and no other (22 of
                // window seeds 0..4000 at n = 6, 1 at n = 12, none at n = 24; COMPLEXITY.md
                // PRES-exp-families).
                let answered = match decide(&f) {
                    _ if width == 3 => "",
                    Err(Refusal::Shadows) => {
                        splinter_refusals_only(&what, &f);
                        ""
                    }
                    _ => "dsa",
                };
                agrees(&what, &f, &truth, answered);
            }
        }
    }
}

/// Checks that `decide`, `satisfiable` and `Extending::answers` each answer `f` or refuse it
/// with `Shadows`, the one refusal DESIGN.md sec:diagnostics allows on a window system of two:
/// a point that could lie only in a splinter split again with as many live variables left.
fn splinter_refusals_only(what: &str, f: &Formula) {
    let shadows = |r: Result<(), Refusal>, op: &str| {
        if let Err(e) = r {
            assert_eq!(e, Refusal::Shadows, "{what}: {op} refused");
        }
    };
    shadows(decide(f).map(drop), "decide");
    shadows(satisfiable(f).map(drop), "satisfiable");
    shadows(Extending::new().answers(f).holds.map(drop), "answers");
}

/// Runs entry point `op` ('d', 's', 'p' onto `on`, 'a') on `f`.
fn entry(op: char, f: &Formula, on: &str) {
    match op {
        'd' => drop(std::hint::black_box(decide(f))),
        's' => drop(std::hint::black_box(satisfiable(f))),
        'p' => drop(std::hint::black_box(project_each(f, &[v(on)]))),
        _ => drop(std::hint::black_box(Extending::new().answers(f))),
    }
}

/// The work of `op` on `f`, on a thread of its own so that every memo starts empty.
fn work(op: char, f: &Formula, on: &str) -> Work {
    Meter::new().work(|| scaling::on_a_thread(STACK, || entry(op, f, on)))
}

/// The least work of `runs` runs of `op` on `family(k)`, each on a member built anew before it.
pub(super) fn least(
    runs: usize,
    family: fn(usize) -> Formula,
    op: char,
    on: &str,
    k: usize,
) -> Work {
    let built: Vec<Formula> = (0..runs).map(|_| family(k)).collect();
    (built.iter().map(|f| work(op, f, on)))
        .min_by_key(|w| w.units)
        .expect("a run")
}

/// The work of `op` on the window systems of seeds 0..20 at size `n`, added up.
pub(super) fn seeds(width: usize, per: usize, op: char, n: usize) -> Work {
    let built: Vec<Formula> = (0..20).map(|s| windows(n, s, width, per)).collect();
    (built.iter().map(|f| work(op, f, "x0"))).fold(Work { units: 0, bytes: 0 }, |a, w| Work {
        units: a.units + w.units,
        bytes: a.bytes + w.bytes,
    })
}

/// Measures `cost` at each size, printing the exponent of each doubling, and holds the
/// instructions and the bytes at the last size, 8 times the first, to those at the first by
/// [`scaling::hold`]: under [`scaling::limit`]`(power)`.
pub(super) fn doubling(what: &str, sizes: &[usize], power: u32, cost: impl Fn(usize) -> Work) {
    let (first, last) = (sizes[0], sizes[sizes.len() - 1]);
    assert_eq!(
        last,
        scaling::FACTOR * first,
        "{what}: the sizes run from n to 8n"
    );
    let start = cost(first);
    println!("{what}, k = {first}: {} instructions", start.units);
    let mut before = start;
    for pair in sizes.windows(2) {
        let (small, large) = (pair[0], pair[1]);
        let now = cost(large);
        let (units, bytes) = (
            now.units as f64 / before.units as f64,
            now.bytes as f64 / before.bytes as f64,
        );
        println!(
            "{what}, k = {large}: {} instructions, {units:.2} times, exponent {:.2}; {bytes:.2} \
             times the bytes",
            now.units,
            units.log2() / (large as f64 / small as f64).log2()
        );
        before = now;
    }
    let what = format!("{what}: k = {first} and {last} (COMPLEXITY.md PRES-exp-families)");
    scaling::hold(&what, "instructions", start.units, before.units, power);
    scaling::hold(&what, "bytes", start.bytes, before.bytes, power);
}

/// The size in bits of `f` and of the point `satisfiable` gives it: 8 bits for each byte of `f`
/// as printed, and for each value of the point its binary digits and one for its sign.
fn input_and_output_bits(f: &Formula) -> u64 {
    let point = satisfiable(f).expect("answered").expect("a point");
    let output: u64 = point.values().map(|v| 1 + v.bits()).sum();
    8 * format!("{f}").len() as u64 + output
}

/// Measures `satisfiable` on `family(k)` at each size, the least of `runs` runs, and holds its
/// instructions and bytes per bit of input and output (`input_and_output_bits`) at the last
/// size, 8 times the first, to those at the first, by [`scaling::hold`] with power 0 (a count
/// per bit of order 1, under [`scaling::limit`]`(0)`, 1.3125 times): a cost O(m) in the m bits
/// of the formula and its point, whatever the share of each. For a family
/// whose point has Θ(k²) bits, such as [`dark_chain`], the answer is the bulk of that size, and
/// no method that writes it out costs less (PRES-dark-chain-forced-bits); `decide` and
/// `Extending::answers`, which do not write it, are held to the size of the formula alone.
pub(super) fn output_sensitive(
    what: &str,
    sizes: &[usize],
    family: fn(usize) -> Formula,
    runs: usize,
) {
    let (first, last) = (sizes[0], sizes[sizes.len() - 1]);
    assert_eq!(
        last,
        scaling::FACTOR * first,
        "{what}: the sizes run from n to 8n"
    );
    // Each count per bit, times 2^16 so that it stays a whole number.
    let per_bit = |k: usize| {
        let m = input_and_output_bits(&family(k));
        let w = least(runs, family, 's', "x0", k);
        let per = |x: u64| (u128::from(x) << 16) / u128::from(m);
        println!(
            "{what}, k = {k}: {} instructions, {} bytes, {m} bits in and out, {:.2} instructions \
             and {:.2} bytes a bit",
            w.units,
            w.bytes,
            w.units as f64 / m as f64,
            w.bytes as f64 / m as f64
        );
        (per(w.units), per(w.bytes))
    };
    let start = per_bit(first);
    let mut end = start;
    for &k in &sizes[1..] {
        end = per_bit(k);
    }
    let what = format!(
        "{what}: k = {first} and {last}, per bit of the formula and its point (COMPLEXITY.md \
         PRES-dark-chain-forced-bits)"
    );
    let fit = |x: u128| u64::try_from(x).expect("a count per bit that fits in 64 bits");
    let measure = "instructions per bit, times 2^16";
    scaling::hold(&what, measure, fit(start.0), fit(end.0), 0);
    scaling::hold(
        &what,
        "bytes per bit, times 2^16",
        fit(start.1),
        fit(end.1),
        0,
    );
}

/// Window seed 628126726154 is answered as the window program answers it, or refused for a
/// splinter where DESIGN.md allows that (FAIL-window-two-shadows-seed).
#[test]
fn the_window_systems_of_seed_628126726154_are_answered() {
    random_window_systems_answer(&[628126726154], "seed 628126726154");
}

/// The seed of FAIL-window-two-shadows-seed and the first windows of two that `decide` refused
/// among seeds 0..4000 (the one at n = 12 among them). Since `decide` writes each row divided by
/// the common factor of its coefficients (FAIL-rewrite-growth-both), three of them are answered,
/// as the window program answers them; the other two are refused for a splinter that would have
/// to be split again with as many live variables left, the cause DESIGN.md sec:diagnostics
/// names, and by `satisfiable` and `answers` for no other cause. The refusal can stand where
/// there is a point: seed 398 has points with `x0` in 0..=2, by the window program.
#[test]
fn the_refused_windows_of_two_are_answered_or_refused_for_a_splinter() {
    /// `n`, the seed, the window program's `x0`, and the answer of `decide`.
    type Case = (usize, u64, &'static [i64], Result<bool, Refusal>);
    let cases: [Case; 5] = [
        (6, 628126726154, &[], Ok(false)),
        (6, 398, &[0, 1, 2], Ok(true)),
        (6, 409, &[], Err(Refusal::Shadows)),
        (6, 650, &[], Ok(false)),
        (12, 2591, &[], Err(Refusal::Shadows)),
    ];
    for (n, seed, x0, answer) in cases {
        let what = format!("windows of 2, 3 rows each, n = {n}, seed {seed}");
        let f = windows(n, seed, 2, 3);
        assert_eq!(decide(&f), answer, "{what}: decide");
        let program: Vec<i64> = windows_x0(n, seed, 2, 3).into_iter().collect();
        assert_eq!(program, x0, "{what}: the window program");
        if let Ok(holds) = answer {
            assert_eq!(
                holds,
                !x0.is_empty(),
                "{what}: the answer of the window program"
            );
            let found = satisfiable(&f).map(|m| m.is_some());
            assert_eq!(found, Ok(holds), "{what}: satisfiable");
        }
        splinter_refusals_only(&what, &f);
    }
}

/// The window system of `seed` at `n` with an equation `x0 + 2·x1 == x2 + 1` added, written
/// in one of five ways: 0 as is, 1 with each row times 1, 2 or 3 (by its place) and the
/// equation as one row, 2 with the equation as the two rows `>=` and `<=`, 3 with the equation
/// times 3 and its sides swapped, and 4 with the rows in reverse order.
fn windows_written(n: usize, seed: u64, how: usize) -> Formula {
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let mut fs = Vec::new();
    for x in &names {
        fs.push(ge(&[(x, 1)], BOX));
        fs.push(ge(&[(x, -1)], BOX));
    }
    for (j, row) in window_rows(n, seed, 2, 3).into_iter().enumerate() {
        let times = if how == 1 { 1 + j as i64 % 3 } else { 1 };
        let t: Vec<(&str, i64)> = (row.c.iter().enumerate())
            .map(|(i, &c)| (names[row.start + i].as_str(), c * times))
            .collect();
        fs.push(ge(&t, row.k * times));
    }
    let e = [("x0", 1), ("x1", 2), ("x2", -1)];
    let minus = e.map(|(a, c)| (a, -c));
    match how {
        2 => fs.extend([ge(&e, -1), ge(&minus, 1)]),
        3 => fs.push(eq(&minus.map(|(a, c)| (a, 3 * c)), 3)),
        _ => fs.push(eq(&e, -1)),
    }
    if how == 4 {
        fs.reverse();
    }
    Formula::and(fs)
}

/// `decide` and `satisfiable` give each window system of two, seeds 0..200 at n = 6, the same
/// verdict however it is written ([`windows_written`]): a row times a factor, an equation as
/// one row or two, or with its sides swapped, or the rows in another order. Before both wrote
/// each formula one way first (FAIL-rewrite-growth-both), the solver's elimination order read
/// the factors and the signs of the rows, and 17 of these seeds had a writing refused where
/// another was answered.
#[test]
fn the_verdict_of_a_window_system_does_not_depend_on_its_writing() {
    let mut wrong = Vec::new();
    for seed in 0..200 {
        let verdict = |how: usize| {
            let f = windows_written(6, seed, how);
            (decide(&f), satisfiable(&f).map(|m| m.is_some()))
        };
        let want = verdict(0);
        assert_eq!(want.0, want.1, "seed {seed}: decide and satisfiable");
        for how in 1..5 {
            let got = verdict(how);
            if got != want {
                wrong.push(format!(
                    "seed {seed} writing {how}: {got:?}, as is {want:?}"
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
