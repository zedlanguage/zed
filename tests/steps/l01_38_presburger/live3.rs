//! Rows over three variables, decided completely (plan item LIVE3): `live3::point` against
//! enumeration on random systems that are feasible, empty, flat, unbounded, or equalities; on
//! Reeve's tetrahedra, which are thin, hold a real point and no integer point, under random
//! unimodular changes of variable; on the corner cases; on the systems of the removed `hull3`
//! tests, rows with a term in one variable everywhere (HULL3-subsumed); and its work at `m` and
//! `8m` rows and at `B` and `8B` bits.

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::live3::{self, Row3, point};
use zedc::store::presburger::{Con, Formula, Lin, decide, satisfiable};

pub(super) fn int(n: i64) -> Int {
    Int::from(n)
}

pub(super) fn row(a: [i64; 3], k: i64) -> Row3 {
    (a.map(int), int(k))
}

fn holds(rows: &[Row3], x: &[Int; 3]) -> bool {
    rows.iter().all(|(a, k)| {
        let s = (0..3).fold(k.clone(), |s, i| &s + &(&a[i] * &x[i]));
        !s.is_negative()
    })
}

/// Whether some point of the cube `[-h, h]^3` meets every row.
fn enumerate(rows: &[Row3], h: i64) -> bool {
    (-h..=h).any(|a| (-h..=h).any(|b| (-h..=h).any(|c| holds(rows, &[a, b, c].map(int)))))
}

/// The rows `±x_i + h >= 0`.
pub(super) fn cube(h: i64) -> Vec<Row3> {
    (0..3)
        .flat_map(|i| {
            [1, -1].map(|s| {
                let mut a = [0; 3];
                a[i] = s;
                row(a, h)
            })
        })
        .collect()
}

/// The answer, checked: a point holds every row.
fn solve(rows: &[Row3]) -> Option<[Int; 3]> {
    let x = point(rows);
    if let Some(x) = &x {
        assert!(holds(rows, x), "the point {x:?} misses a row of {rows:?}");
    }
    x
}

fn random_rows(rng: &mut Rng, n: usize, c: i64, k: i64) -> Vec<Row3> {
    (0..n)
        .map(|_| row([0; 3].map(|_| rng.int(-c, c)), rng.int(-k, k)))
        .collect()
}

/// 600 random systems in the cube `[-3, 3]^3` of a new seed each run, against enumeration; both
/// answers occur. The 3000 systems of seed 0x13a01 (1.5 s at load 25) are in `bench::live3`.
#[test]
fn random_bounded_systems_match_enumeration() {
    let (mut rng, seed) = Rng::fresh("live3 bounded systems");
    let (sat, unsat) = bounded_systems_match_enumeration(&mut rng, 600);
    // Both answers occur, so neither check passes by never being asked.
    assert!(
        sat > 60 && unsat > 60,
        "seed {seed}: {sat} with a point, {unsat} without"
    );
}

/// `count` random systems of 1 to 6 rows in the cube `[-3, 3]^3`, each answered as enumeration
/// answers; the counts with and without a point.
pub(super) fn bounded_systems_match_enumeration(rng: &mut Rng, count: usize) -> (usize, usize) {
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..count {
        let n = 1 + rng.below(6);
        let mut rows = random_rows(rng, n, 6, 12);
        rows.extend(cube(3));
        let truth = enumerate(&rows, 3);
        assert_eq!(solve(&rows).is_some(), truth, "{rows:?}");
        if truth {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    (sat, unsat)
}

/// 400 unbounded systems of [`unbounded_systems_match_enumeration`] of a new seed each run;
/// each outcome occurs: a point in the window, one only outside it, and none. The 1500 of seed
/// 0x13a02 (0.78 s at load 14, 1.2 s at load 38) are in `bench::live3`.
#[test]
fn random_unbounded_systems_match_enumeration_in_a_window() {
    let (mut rng, seed) = Rng::fresh("live3 unbounded systems");
    let (inside, outside, none) = unbounded_systems_match_enumeration(&mut rng, 400);
    assert!(
        inside > 100 && outside > 0 && none > 8,
        "seed {seed}: {inside}, {outside}, {none}"
    );
}

/// `count` systems of one to five rows with no bound: a point of the window `[-8, 8]^3` is a
/// point of the rows, and the rows have a point when the window holds one; with none in the
/// window the rows may still have one outside. The counts with a point inside the window, with
/// one only outside it, and with none.
pub(super) fn unbounded_systems_match_enumeration(
    rng: &mut Rng,
    count: usize,
) -> (usize, usize, usize) {
    let (mut inside, mut outside, mut none) = (0, 0, 0);
    for _ in 0..count {
        let n = 1 + rng.below(5);
        let rows = random_rows(rng, n, 5, 10);
        let seen = enumerate(&rows, 8);
        match (solve(&rows), seen) {
            (Some(_), true) => inside += 1,
            (Some(_), false) => outside += 1,
            (None, false) => none += 1,
            (None, true) => panic!("no point found in rows with one: {rows:?}"),
        }
    }
    (inside, outside, none)
}

/// 600 equalities in the cube `[-3, 3]^3` of a new seed each run, against enumeration; both
/// answers occur. The 2000 of seed 0x13a03 (1.25 s at load 25) are in `bench::live3`.
#[test]
fn flat_and_equality_systems_match_enumeration() {
    let (mut rng, seed) = Rng::fresh("live3 flat and equality systems");
    let (sat, unsat) = flat_and_equality_systems_match(&mut rng, 600);
    assert!(
        sat > 60 && unsat > 60,
        "seed {seed}: {sat} with a point, {unsat} without"
    );
}

/// `count` equalities with up to two other rows in the cube `[-3, 3]^3`, each answered as
/// enumeration answers; the counts with and without a point.
pub(super) fn flat_and_equality_systems_match(rng: &mut Rng, count: usize) -> (usize, usize) {
    // An equality `a·x + k = 0` as two rows, with a bound; `a` with a common factor half of
    // the time, so that some have real points and no integer point.
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..count {
        let g = rng.pick(&[1, 2, 3]);
        let a = [0; 3].map(|_| g * rng.int(-4, 4));
        let k = rng.int(-15, 15);
        let mut rows = vec![row(a, k), row(a.map(|c| -c), -k)];
        let extra = rng.below(3);
        rows.extend(random_rows(rng, extra, 4, 8));
        rows.extend(cube(3));
        let truth = enumerate(&rows, 3);
        assert_eq!(solve(&rows).is_some(), truth, "{rows:?}");
        if truth {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    (sat, unsat)
}

#[test]
fn rationally_empty_systems_have_no_point() {
    let mut rng = Rng::new(0x1_3a04);
    for _ in 0..500 {
        // `a·x >= k` and `a·x <= k - 1 - s`, with other rows.
        let a = [0; 3].map(|_| rng.int(-6, 6));
        let k = rng.int(-20, 20);
        let mut rows = vec![row(a, -k), row(a.map(|c| -c), k - 1 - rng.int(0, 3))];
        if a == [0; 3] {
            continue;
        }
        let extra = rng.below(4);
        rows.extend(random_rows(&mut rng, extra, 6, 12));
        assert_eq!(solve(&rows), None, "{rows:?}");
    }
}

/// A random unimodular matrix, as rows: products of elementary column operations.
fn unimodular(rng: &mut Rng) -> [[i64; 3]; 3] {
    let mut u = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
    for _ in 0..6 {
        let (i, j) = (rng.below(3), rng.below(3));
        if i == j {
            continue;
        }
        let c = rng.int(-3, 3);
        for r in &mut u {
            r[j] += c * r[i];
        }
    }
    u
}

/// The rows with `x = U·y`: each `a·x` becomes `(a·U)·y`.
fn change(rows: &[([i64; 3], i64)], u: &[[i64; 3]; 3]) -> Vec<Row3> {
    rows.iter()
        .map(|(a, k)| {
            let b = [0, 1, 2].map(|j| (0..3).map(|i| a[i] * u[i][j]).sum::<i64>());
            row(b, *k)
        })
        .collect()
}

/// Reeve's tetrahedron of height `r`, the hull of `(0,0,0)`, `(1,0,0)`, `(0,1,0)` and `(1,1,r)`,
/// each facet moved inward by `s / 4`. Its only integer points are its four vertices, each on
/// three facets, so with `s = 1` it has none, and it holds `(1/2, 1/2, r/4)` for `r >= 1`.
fn reeve(r: i64, s: i64) -> Vec<([i64; 3], i64)> {
    vec![
        ([0, 0, 4], -s),
        ([0, 4 * r, -4], -s),
        ([4 * r, 0, -4], -s),
        ([-4 * r, -4 * r, 4], 4 * r - s),
    ]
}

#[test]
fn reeve_tetrahedra_under_unimodular_maps_are_decided() {
    let mut rng = Rng::new(0x1_3a05);
    for r in 1..=12 {
        for _ in 0..20 {
            let u = unimodular(&mut rng);
            // Shrunk: a real point, no integer point.
            assert_eq!(solve(&change(&reeve(r, 1), &u)), None, "r = {r}, U = {u:?}");
            // Not shrunk: the vertices.
            assert!(
                solve(&change(&reeve(r, 0), &u)).is_some(),
                "r = {r}, U = {u:?}"
            );
        }
    }
}

#[test]
fn corner_cases() {
    // No row, a row of zeros, and one row.
    assert!(solve(&[]).is_some());
    assert!(solve(&[row([0, 0, 0], 0)]).is_some());
    assert_eq!(solve(&[row([0, 0, 0], -1)]), None);
    assert!(solve(&[row([3, -5, 7], -1_000_000)]).is_some());
    // Parallel rows: `1 <= 6x + 10y + 15z <= 1` has a point; `1 <= 6x + 10y + 14z <= 1` has
    // none, since 2 divides every coefficient.
    assert!(solve(&[row([6, 10, 15], -1), row([-6, -10, -15], 1)]).is_some());
    assert_eq!(solve(&[row([6, 10, 14], -1), row([-6, -10, -14], 1)]), None);
    // Parallel rows with a direction of common factor 2 and a gap below one value of it.
    assert_eq!(
        solve(&[row([2, 4, 6], -5), row([-2, -4, -6], 5), row([1, 0, 0], 0)]),
        None
    );
    assert!(solve(&[row([2, 4, 6], -4), row([-2, -4, -6], 5)]).is_some());
    // Huge coefficients: 10^30 times Pugh's rows in `x` and `y`, a slab in `z`.
    let big = (0..30).fold(int(1), |p, _| &p * &int(10));
    let scaled = |a: [i64; 3], k: i64| (a.map(|c| &big * &int(c)), &big * &int(k));
    let pugh = [
        scaled([11, 13, 0], -27),
        scaled([-11, -13, 0], 45),
        scaled([7, -9, 0], 10),
        scaled([-7, 9, 0], 4),
        scaled([0, 0, 1], 5),
    ];
    assert_eq!(solve(&pugh), None);
    // A point with 40-digit coordinates.
    let p = [&big * &int(123_456_789), -&(&big * &int(98_765)), int(7)];
    let near: Vec<Row3> = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [3, 5, -1], [-2, 1, 4]]
        .iter()
        .flat_map(|a| {
            let v = (0..3).fold(int(0), |s, i| &s + &(&int(a[i]) * &p[i]));
            [(a.map(int), -&v), (a.map(|c| int(-c)), &v + &int(1))]
        })
        .collect();
    let x = solve(&near).expect("a point next to p");
    assert!(x.iter().zip(&p).all(|(x, p)| (x - p).abs() <= int(1)));
}

/// Random systems of a new seed each run, under each order of the variables and with the rows
/// reversed: 30 unbounded, most of which have a point, and 30 in the cube `[-3, 3]^3`, about 40%
/// of which have none (fewer than 2 on either side about 5 times in a million), so both answers
/// are moved. The 400 unbounded systems of seed 0x13a06 (2.5 s at load 25) are in
/// `bench::live3`.
#[test]
fn the_answer_does_not_depend_on_the_order_of_variables_or_rows() {
    let (mut rng, seed) = Rng::fresh("live3 order of variables and rows");
    let free = order_does_not_change_the_answer(&mut rng, 30, false);
    let (sat, unsat) = order_does_not_change_the_answer(&mut rng, 30, true);
    assert!(
        sat >= 2 && unsat >= 2,
        "seed {seed}: in the cube, {sat} with a point, {unsat} without; unbounded {free:?}"
    );
}

/// `count` random systems of 2 to 6 rows, in the cube `[-3, 3]^3` when `bounded`, each with
/// the same answer under every order of the variables and with its rows reversed; the counts
/// with and without a point.
pub(super) fn order_does_not_change_the_answer(
    rng: &mut Rng,
    count: usize,
    bounded: bool,
) -> (usize, usize) {
    let perms = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..count {
        let n = 2 + rng.below(5);
        let mut rows = random_rows(rng, n, 7, 15);
        if bounded {
            rows.extend(cube(3));
        }
        let first = solve(&rows).is_some();
        for p in perms {
            let moved: Vec<Row3> = rows
                .iter()
                .map(|(a, k)| ([0, 1, 2].map(|i| a[p[i]].clone()), k.clone()))
                .collect();
            assert_eq!(solve(&moved).is_some(), first, "{rows:?} under {p:?}");
        }
        rows.reverse();
        assert_eq!(solve(&rows).is_some(), first, "{rows:?} reversed");
        if first {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    (sat, unsat)
}

#[test]
fn the_omega_test_decides_three_variables() {
    // The rows of the refusal of a splinter of a splinter before LIVE3: decided, with a point.
    let v = |n: &str| Lin::atom(zedc::store::presburger::Atom::Sym(n.into()));
    let ge = |t: &[(&str, i64)], k: i64| {
        let l = t
            .iter()
            .fold(Lin::constant(k), |l, (n, c)| l.plus(&v(n).times(*c)));
        Formula::Con(Con::ge(&l, &Lin::constant(0)))
    };
    let f = Formula::and(vec![
        ge(&[("x", -2), ("y", -3), ("z", -6)], 4),
        ge(&[("x", -4), ("z", -6)], -22),
        ge(&[("x", 1), ("y", -1), ("z", 4)], 36),
        ge(&[("x", 2), ("y", 3), ("z", 3)], -24),
    ]);
    let m = satisfiable(&f).expect("decided").expect("a point");
    assert!(f.holds(&m), "{m:?}");
    // Reeve's tetrahedron of height 7, shrunk: no point.
    let rows = reeve(7, 1);
    let f = Formula::and(
        rows.iter()
            .map(|(a, k)| ge(&[("x", a[0]), ("y", a[1]), ("z", a[2])], *k))
            .collect(),
    );
    assert_eq!(satisfiable(&f), Ok(None));
}

/// Reeve's tetrahedron of height 7, shrunk so it holds no integer point, and `m` rows more of
/// coefficients drawn by `coefficient`, each holding the whole unshrunk tetrahedron with slack 0 to 5.
/// No elimination, box point or rounding center decides it, so every stage runs: the linear
/// programs, the rounding, LLL, and `twovar` on each of the planes of the flat direction, all
/// over every row.
pub(super) fn thin(m: usize, seed: u64, coefficient: impl Fn(&mut Rng) -> Int) -> Vec<Row3> {
    let mut rng = Rng::new(seed);
    let r = 7;
    let mut rows: Vec<Row3> = reeve(r, 1).iter().map(|(a, k)| row(*a, *k)).collect();
    let corners = [[0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, r]].map(|v| v.map(int));
    for _ in 0..m {
        let a = [0; 3].map(|_| coefficient(&mut rng));
        let least = corners
            .iter()
            .map(|v| (0..3).fold(int(0), |s, i| &s + &(&a[i] * &v[i])))
            .min()
            .expect("four corners");
        rows.push((a, &int(rng.int(0, 5)) - &least));
    }
    rows
}

/// Checks that the work of `point` on `small` and `large`, sizes `n` and `8n`, is of order
/// `n^power`, measuring each once.
pub(super) fn scales(what: &str, n: usize, power: u32, small: &[Row3], large: &[Row3]) {
    assert_eq!(solve(small), None);
    assert_eq!(solve(large), None);
    scaling::check_order(what, n, power, |m| {
        let rows = if m == n { small } else { large };
        std::hint::black_box(point(rows));
    });
}

// Plan item LIVE3-TESTS (from the XR3 round 3 synthesis): the systems the cross-review named,
// each with its answer found here by hand and by enumeration, and the slab family at `n` and
// `8n` rows.

/// The rows `a <= c·x <= a + w`.
pub(super) fn slab(c: [i64; 3], a: i64, w: i64) -> Vec<Row3> {
    vec![row(c, -a), row(c.map(|c| -c), a + w)]
}

/// The rows `-h <= x_i <= h` for each `i` in `which`.
fn bounds(which: &[usize], h: i64) -> Vec<Row3> {
    cube(h)
        .into_iter()
        .enumerate()
        .filter(|(j, _)| which.contains(&(j / 2)))
        .map(|(_, r)| r)
        .collect()
}

/// The rows as a formula over `x`, `y` and `z`, for the path through `satisfiable`.
pub(super) fn formula(rows: &[Row3]) -> Formula {
    let v = |n: &str| Lin::atom(zedc::store::presburger::Atom::Sym(n.into()));
    Formula::and(
        rows.iter()
            .map(|(a, k)| {
                let l = ["x", "y", "z"]
                    .iter()
                    .zip(a)
                    .fold(Lin::constant(k.clone()), |l, (n, c)| {
                        l.plus(&v(n).times(c.clone()))
                    });
                Formula::Con(Con::ge(&l, &Lin::constant(0)))
            })
            .collect(),
    )
}

/// Both paths, `point` and `satisfiable`, give `expected` (whether a point exists), and a point
/// either finds holds every row.
fn decided(rows: &[Row3], expected: bool) {
    assert_eq!(solve(rows).is_some(), expected, "point: {rows:?}");
    let f = formula(rows);
    let m = satisfiable(&f).expect("decided, not refused");
    assert_eq!(m.is_some(), expected, "satisfiable: {rows:?}");
    if let Some(m) = &m {
        assert!(f.holds(m), "{m:?}");
    }
}

/// The integer points of `a <= c·x <= a + w` with `|x_0|, |x_1| <= h` and `x_2` free, counted
/// exactly in `i128`, apart from `Int` and the solver: for each `(x_0, x_1)` the values of `x_2`
/// lie between two quotients by `c_2 > 0`.
fn slab_points(c: [i64; 3], a: i64, w: i64, h: i64) -> i128 {
    let (c, a, w) = (c.map(i128::from), i128::from(a), i128::from(w));
    assert!(c[2] > 0);
    let mut n = 0;
    for x0 in -h..=h {
        for x1 in -h..=h {
            let s = c[0] * i128::from(x0) + c[1] * i128::from(x1);
            // c_2 x_2 >= a - s and c_2 x_2 <= a + w - s.
            let lo = (a - s).div_euclid(c[2]) + i128::from((a - s).rem_euclid(c[2]) != 0);
            let hi = (a + w - s).div_euclid(c[2]);
            n += (hi - lo + 1).max(0);
        }
    }
    n
}

#[test]
fn a_slab_of_million_coefficients_is_decided() {
    // c = (10^6, 10^6 + 1, 10^6 + 3) over the cube |x_i| <= 5: c·x = 10^6 S + t with
    // S = x_0 + x_1 + x_2 and t = x_1 + 3 x_2, |t| <= 20. So 500,000 <= c·x <= 500,001 has no
    // integer point, since |10^6 S - 500,000| >= 500,000 > 20 + 1, though it has real points
    // (x = (1/2, 0, 0)). 2,000,007 <= c·x <= 2,000,008 has one: S = 2 and t = 7 at
    // (-1, 1, 2), where c·x = -10^6 + 1,000,001 + 2,000,006 = 2,000,007.
    let c = [1_000_000, 1_000_001, 1_000_003];
    let empty: Vec<Row3> = [slab(c, 500_000, 1), cube(5)].concat();
    assert!(!enumerate(&empty, 5));
    decided(&empty, false);
    let held: Vec<Row3> = [slab(c, 2_000_007, 1), cube(5)].concat();
    assert!(holds(&held, &[-1, 1, 2].map(int)));
    decided(&held, true);
    // Every value of `a` that the cube reaches and the gaps between them, against enumeration
    // of the 11^3 points: c·x lies within 20 of a multiple of 10^6, so a slab at
    // 10^6 S + 19 .. 10^6 S + 22 is held exactly when t can be 19 to 21.
    for s in -3..=3 {
        for t in [-22, -21, -20, -1, 0, 19, 20, 21, 22, 500] {
            let a = 1_000_000 * s + t;
            let rows: Vec<Row3> = [slab(c, a, 1), cube(5)].concat();
            assert_eq!(solve(&rows).is_some(), enumerate(&rows, 5), "a = {a}");
        }
    }
}

#[test]
fn the_cross_reviews_slab_of_million_coefficients_is_decided() {
    // Cross-review XR3 (Gemini's probe): c = (1,000,003, 1,400,005, 1,800,014), |x_0|, |x_1| <= 5,
    // x_2 free. c·(1, 1, 1) = 4,200,022, so c·x = 4,200,022 holds there; the slab one wide above
    // it too. For each value of `a` the exact count of points over the 121 pairs (x_0, x_1)
    // decides; a random `a` misses, since each pair hits 2 values of `a` in 1,800,014.
    let c = [1_000_003, 1_400_005, 1_800_014];
    let free = bounds(&[0, 1], 5);
    let rows: Vec<Row3> = [slab(c, 4_200_022, 0), free.clone()].concat();
    assert_eq!(slab_points(c, 4_200_022, 0, 5), 1);
    assert!(holds(&rows, &[1, 1, 1].map(int)));
    decided(&rows, true);
    assert_eq!(solve(&rows), Some([1, 1, 1].map(int)), "the only point");
    let mut rng = Rng::new(0x1_3a07);
    let (mut sat, mut unsat) = (0, 0);
    for i in 0..200 {
        let a = if i % 2 == 0 {
            // At or one below the value of a point of the box, so held.
            let p = [rng.int(-5, 5), rng.int(-5, 5), rng.int(-9, 9)];
            (0..3).map(|j| c[j] * p[j]).sum::<i64>() - rng.int(0, 1)
        } else {
            rng.int(-20_000_000, 20_000_000)
        };
        let rows: Vec<Row3> = [slab(c, a, 1), free.clone()].concat();
        let truth = slab_points(c, a, 1, 5) > 0;
        assert_eq!(solve(&rows).is_some(), truth, "a = {a}");
        if truth {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    assert!(
        sat >= 100 && unsat > 50,
        "{sat} with a point, {unsat} without"
    );
}

#[test]
fn the_checkers_three_variable_question_has_a_point() {
    // The rows of `checker.rs` `a_question_whose_point_lies_past_one_splinter_is_rejected`
    // before LIVE3, refused then (a splinter of a splinter). (5, 12, -7) holds them:
    // 4 - 10 - 36 + 42 = 0, -20 + 42 - 22 = 0, 5 - 12 - 28 + 36 = 1, 10 + 36 - 21 - 24 = 1.
    // Enumeration of [-15, 15]^3 finds points, so the answer is a point.
    let rows = [
        row([-2, -3, -6], 4),
        row([-4, 0, -6], -22),
        row([1, -1, 4], 36),
        row([2, 3, 3], -24),
    ];
    assert!(holds(&rows, &[5, 12, -7].map(int)));
    assert!(enumerate(&rows, 15));
    decided(&rows, true);
    // Raised by one in the second row (-4x - 6z >= 23): no integer point, though real ones.
    // The first row less the fourth gives 3z <= -20, so z <= -7. 4x + 6z is even, so
    // 4x + 6z <= -23 means 2x + 3z <= -12. The third and fourth give
    // 24 - 2x - 3z <= 3y <= 3x + 12z + 108, so 5x + 15z >= -84 and x + 3z >= -16. Then
    // 2(-16 - 3z) <= 2x <= -12 - 3z gives z >= -6, against z <= -7. Over the reals the
    // same steps give only -7.37 <= z <= -6.67. Enumeration of [-15, 15]^3 agrees.
    let raised = [
        row([-2, -3, -6], 4),
        row([-4, 0, -6], -23),
        row([1, -1, 4], 36),
        row([2, 3, 3], -24),
    ];
    assert!(!enumerate(&raised, 15));
    decided(&raised, false);
}

#[test]
fn a_point_on_a_tight_plane_with_large_coefficients_is_found() {
    // From the xt round 2 review (wt/xt2/gemini/R2_ZED_IMPL.patch). The last four rows are the
    // equalities 2x + 3y - z = 2 and x - 2y + 3z = 1, so z = 2x + 3y - 2, then 7x + 7y = 7:
    // y = 1 - x and z = 1 - x. The first two rows become 97x >= 0 and -89x >= 0, so x = 0,
    // and (0, 1, 1) is the one integer point, on the plane 97x + 37y - 37z = 0.
    let rows = [
        row([97, 37, -37], 0),
        row([-89, -34, 34], 0),
        row([2, 3, -1], -2),
        row([-2, -3, 1], 2),
        row([1, -2, 3], -1),
        row([-1, 2, -3], 1),
    ];
    let witness = [0, 1, 1].map(int);
    assert!(holds(&rows, &witness));
    decided(&rows, true);
    assert_eq!(solve(&rows), Some(witness.clone()));
    let f = formula(&rows);
    assert_eq!(zedc::store::presburger::decide(&f), Ok(true));
    let m = satisfiable(&f).expect("decided").expect("a point");
    let v = |n: &str| {
        m.get(&zedc::store::presburger::Atom::Sym(n.into()))
            .cloned()
            .unwrap_or(Int::ZERO)
    };
    assert_eq!([v("x"), v("y"), v("z")], witness);
}

#[test]
fn parity_slabs_are_decided() {
    // Cross-review XR3 (Gemini's control): 2z - 2x = 1 has real points and no integer point,
    // since the left side is even. Each row alone settles it, its coefficients having the
    // common factor 2.
    let gemini: Vec<Row3> = [
        vec![row([-2, 0, 2], -1), row([2, 0, -2], 1)],
        bounds(&[0, 1], 5),
    ]
    .concat();
    decided(&gemini, false);
    // Rows with no common factor: x + y - 2z = 1 and x - y + 2z = 0 add to 2x = 1, so no
    // integer point, while x = 1/2, y = 1/2 + 2z is a line of real points. Only the sum shows
    // it.
    let parity = |k: i64| -> Vec<Row3> {
        [slab([1, 1, -2], 1, 0), slab([1, -1, 2], k, 0), cube(6)].concat()
    };
    assert!(!enumerate(&parity(0), 6));
    decided(&parity(0), false);
    // With x - y + 2z = 1 instead, 2x = 2: (1, 0, 0) holds.
    assert!(holds(&parity(1), &[1, 0, 0].map(int)));
    decided(&parity(1), true);
    // Coefficients near 10^6: c = (10^6 + 1, 10^6 + 3, 10^6 + 5) gives
    // c·x = (10^6 + 1) S + 2 t with S = x_0 + x_1 + x_2 and t = x_1 + 2 x_2. Over the cube
    // |x_i| <= 5, |t| <= 15, so c·x = 1 needs S = 0 (else |c·x| >= 10^6 + 1 - 30), and then
    // c·x = 2t is even: no point, though (-1/2, 1/2, 0) is a real point (S = 0, t = 1/2).
    // 1 <= c·x <= 2 has one: S = 0, t = 1 at (-1, 1, 0), where
    // c·x = -(10^6 + 1) + 10^6 + 3 = 2.
    let c = [1_000_001, 1_000_003, 1_000_005];
    let empty: Vec<Row3> = [slab(c, 1, 0), cube(5)].concat();
    assert!(!enumerate(&empty, 5));
    decided(&empty, false);
    let held: Vec<Row3> = [slab(c, 1, 1), cube(5)].concat();
    assert!(holds(&held, &[-1, 1, 0].map(int)));
    decided(&held, true);
    // The same thin slab under random unimodular changes of variable, which keep the integer
    // points: still none, and with the other constant still some.
    let mut rng = Rng::new(0x1_3a08);
    let plain = |k: i64| {
        vec![
            ([1, 1, -2], -1),
            ([-1, -1, 2], 1),
            ([1, -1, 2], -k),
            ([-1, 1, -2], k),
        ]
    };
    for _ in 0..100 {
        let u = unimodular(&mut rng);
        assert_eq!(solve(&change(&plain(0), &u)), None, "U = {u:?}");
        assert!(solve(&change(&plain(1), &u)).is_some(), "U = {u:?}");
    }
}

// The systems of the removed `hull3` tests (plan item HULL3-subsumed): rows `z·Z + x·X + y·Y +
// k >= 0` with `z != 0` in every row, the unit-side class the `hull3` stage once projected on
// `(X, Y)` before the box. `live3` decides them now, checked against enumeration.

/// `z·Z + x·X + y·Y + k >= 0`, as `[z, x, y, k]`, over the variables `(X, Y, Z)`.
fn zxy(rows: &[[i64; 4]]) -> Vec<Row3> {
    rows.iter().map(|r| row([r[1], r[2], r[0]], r[3])).collect()
}

/// Checks `point` on `rows` and on `rows` cut to the cube `|x_i| <= 5`: every point found holds
/// every row (`solve`), the rows have a point when the cube holds one, and on the cut rows the
/// answer is enumeration's. Returns whether the rows, uncut, have a point.
fn agrees(rows: &[Row3]) -> bool {
    let found = solve(rows).is_some();
    assert!(
        found || !enumerate(rows, 5),
        "no point found in rows with one: {rows:?}"
    );
    let mut cut = rows.to_vec();
    cut.extend(cube(5));
    assert_eq!(solve(&cut).is_some(), enumerate(&cut, 5), "{cut:?}");
    found
}

/// `m` rows with `Z`'s coefficient in `±(1..=zc)`, `X`'s and `Y`'s in `-c..=c`, `k` in `-k..=k`.
fn rows_with_z(rng: &mut Rng, m: usize, c: i64, k: i64, zc: i64) -> Vec<Row3> {
    (0..m)
        .map(|_| {
            let z = rng.int(1, zc) * if rng.below(2) == 0 { 1 } else { -1 };
            row([rng.int(-c, c), rng.int(-c, c), z], rng.int(-k, k))
        })
        .collect()
}

#[test]
fn rows_with_a_term_in_one_variable_everywhere_match_enumeration() {
    let mut rng = Rng::new(0x4_3333);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..400 {
        let m = 1 + rng.below(12);
        if agrees(&rows_with_z(&mut rng, m, 5, 12, 3)) {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    assert!(
        sat > 40 && unsat > 40,
        "{sat} with a point, {unsat} without"
    );
}

#[test]
fn rows_whose_planes_coincide_match_enumeration() {
    // Coefficients in -1..1: many planes parallel, equal, or meeting in one line or point.
    let mut rng = Rng::new(0x4_3334);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..400 {
        let m = 1 + rng.below(14);
        if agrees(&rows_with_z(&mut rng, m, 1, 2, 2)) {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    assert!(
        sat > 40 && unsat > 40,
        "{sat} with a point, {unsat} without"
    );
}

#[test]
fn planes_through_one_line_or_one_point() {
    // All through the line X = Y = Z: the integer points are that line's.
    let line = zxy(&[
        [1, -1, 0, 0],
        [1, 0, -1, 0],
        [2, -1, -1, 0],
        [-1, 1, 0, 0],
        [-1, 0, 1, 0],
        [-3, 1, 2, 0],
    ]);
    assert!(agrees(&line));
    let x = solve(&line).expect("a point on the line");
    assert!(x[0] == x[1] && x[1] == x[2], "{x:?}");
    let pin = |rows: &[Row3], i: usize, v: i64| {
        let mut a = [0; 3];
        a[i] = 1;
        let mut r = rows.to_vec();
        r.extend([row(a, -v), row(a.map(|c| -c), v)]);
        r
    };
    assert_eq!(solve(&pin(&line, 0, 5)), Some([5, 5, 5].map(int)));
    assert_eq!(solve(&pin(&pin(&line, 0, 5), 1, 6)), None);
    // A cone with its apex at the origin, Z >= |X| + |Y| and Z <= 0: a single point.
    let point = zxy(&[
        [1, 1, 1, 0],
        [1, -1, 1, 0],
        [1, 1, -1, 0],
        [1, -1, -1, 0],
        [-1, 0, 0, 0],
    ]);
    assert!(agrees(&point));
    assert_eq!(solve(&point), Some([0, 0, 0].map(int)));
    // The same plane many times over, on both sides: a slab of width zero over everything,
    // which holds integer points since Z's coefficient is 1.
    let same = zxy(&[
        [1, 2, 3, 4],
        [1, 2, 3, 4],
        [-1, -2, -3, -4],
        [-2, -4, -6, -8],
    ]);
    assert!(agrees(&same));
}

#[test]
fn normals_in_one_plane_unbounded_and_empty_systems() {
    // No Y anywhere: a strip in X.
    assert!(agrees(&zxy(&[
        [1, 1, 0, 3],
        [1, -2, 0, 1],
        [-1, 1, 0, 4],
        [-2, 0, 0, 5]
    ])));
    // One side only: unbounded in Z.
    assert!(agrees(&zxy(&[[1, 1, 2, 3], [2, -1, 0, 1]])));
    assert!(agrees(&zxy(&[[-1, 1, 2, 3]])));
    // A half-space, and an unbounded wedge.
    assert!(agrees(&zxy(&[[1, 0, 0, 0], [-1, 1, 1, 0]])));
    assert!(agrees(&zxy(&[[1, 1, 0, 0], [1, 0, 1, 0], [-1, 0, 0, 5]])));
    // Parallel bounds that do not meet.
    assert!(!agrees(&zxy(&[
        [1, 1, 1, -1],
        [-1, -1, -1, 0],
        [1, 0, 0, 7]
    ])));
    // Bounds that meet nowhere though no two are parallel: Z >= |X| and Z <= -1.
    assert!(!agrees(&zxy(&[
        [1, -1, 0, 0],
        [1, 1, 0, 0],
        [1, 0, 1, 0],
        [-1, 0, 0, -1]
    ])));
}

/// `n` planes tangent to `Z = (X - p)² + (Y - p)²` from below and `n` to `Z = C - (X - p)² -
/// (Y - p)²` from above, at random points: the body between them is near a lens over `(p, p)`,
/// with many planes on its boundary.
pub(super) fn tangents(n: usize, p: i64) -> Vec<Row3> {
    let mut rng = Rng::new(0x4_3335);
    let c = 2_000_000i64;
    (0..2 * n)
        .map(|i| {
            let (a, b) = (rng.int(-1000, 1000), rng.int(-1000, 1000));
            let s = a * a + b * b + 2 * (a + b) * p;
            if i % 2 == 0 {
                // Z >= 2a(X - p) + 2b(Y - p) - a² - b².
                row([-2 * a, -2 * b, 1], s)
            } else {
                // Z <= -2a(X - p) - 2b(Y - p) + a² + b² + C.
                row([-2 * a, -2 * b, -1], s + c)
            }
        })
        .collect()
}

#[test]
fn a_lens_of_tangent_planes_has_a_point() {
    assert!(solve(&tangents(128, 0)).is_some());
    assert!(solve(&tangents(128, 5_000)).is_some());
}

/// The lens of [`tangents`] over the origin cut by the slab `10^6 + 1/4 <= Z <= 10^6 + 1/2`,
/// which holds real points of the lens and no integer `Z`.
pub(super) fn lens_in_a_thin_slab(n: usize) -> Vec<Row3> {
    let mut rows = tangents(n, 0);
    rows.push(row([0, 0, 4], -4_000_001));
    rows.push(row([0, 0, -4], 4_000_002));
    rows
}

#[test]
fn a_lens_in_a_thin_slab_has_no_point() {
    assert_eq!(solve(&lens_in_a_thin_slab(64)), None);
}

/// The calls of `Lin2::minus` that `point` makes on `rows`.
pub(super) fn minus_calls(rows: &[Row3]) -> u64 {
    let before = live3::counts::minus();
    std::hint::black_box(point(rows));
    live3::counts::minus() - before
}

/// [`thin`] with seed 7 and coefficients up to 50, the family of the benchmark of many rows.
pub(super) fn thin_with_coefficients_to_fifty(m: usize) -> Vec<Row3> {
    thin(m, 7, |rng| int(rng.int(-50, 50)))
}

/// The empty slab `c·x = 1` of `parity_slabs_are_decided`, `c = (10^6 + 1, 10^6 + 3, 10^6 + 5)`,
/// over the cube `|x_i| <= 5`, and `m` rows more with coefficients up to 50, each holding the
/// whole cube with slack 0 to 5, so that no row bound settles it.
pub(super) fn million_slab_with_rows(m: usize) -> Vec<Row3> {
    let c = [1_000_001, 1_000_003, 1_000_005];
    let mut rng = Rng::new(11);
    let mut rows: Vec<Row3> = [slab(c, 1, 0), cube(5)].concat();
    for _ in 0..m {
        let a = [0; 3].map(|_| rng.int(-50, 50));
        // The least of a·x over the cube is -5 Σ|a_i|.
        let least = -5 * a.iter().map(|c| c.abs()).sum::<i64>();
        rows.push(row(a, rng.int(0, 5) - least));
    }
    rows
}

/// The rows of [`tangents`]`(n, 5_000)` as a formula: a lens away from the origin, over which no
/// point of the box stage holds, so that `satisfiable` reaches `live3`.
pub(super) fn lens_away_from_the_origin(n: usize) -> Formula {
    formula(&tangents(n, 5_000))
}

/// The check the benchmarks make of the rows they time in `point`: `point` finds none.
pub(super) fn assert_no_point(rows: &[Row3]) {
    assert_eq!(solve(rows), None);
}

/// The checks of the benchmarks of `bench/live3.rs` at small sizes: no point in the thin
/// tetrahedron or the slab with rows added, `Lin2::minus` called on the slab, and a point of the
/// lens away from the origin found, holding, and decided.
#[test]
fn the_families_of_the_benchmarks_are_answered_at_small_sizes() {
    for m in [0, 1, 8, 30] {
        assert_no_point(&thin_with_coefficients_to_fifty(m));
        let slab = million_slab_with_rows(m);
        assert_no_point(&slab);
        assert!(minus_calls(&slab) > 0, "m = {m}");
    }
    for n in [1, 4, 16] {
        let f = lens_away_from_the_origin(n);
        let m = satisfiable(&f).expect("answered").expect("a point");
        assert!(f.holds(&m), "{m:?}");
        assert_eq!(decide(&f), Ok(true), "n = {n}");
    }
}
