//! Rows over three variables, decided completely (plan item LIVE3): `live3::point` against
//! enumeration on random systems that are feasible, empty, flat, unbounded, or equalities; on
//! Reeve's tetrahedra, which are thin, hold a real point and no integer point, under random
//! unimodular changes of variable; on the corner cases; and its work at `m` and `8m` rows and
//! at `B` and `8B` bits.

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::live3::{Row3, point};
use zedc::store::presburger::{Con, Formula, Lin, satisfiable};

fn int(n: i64) -> Int {
    Int::from(n)
}

fn row(a: [i64; 3], k: i64) -> Row3 {
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
fn cube(h: i64) -> Vec<Row3> {
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

#[test]
fn random_bounded_systems_match_enumeration() {
    let mut rng = Rng::new(0x1_3a01);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..3000 {
        let n = 1 + rng.below(6);
        let mut rows = random_rows(&mut rng, n, 6, 12);
        rows.extend(cube(3));
        let truth = enumerate(&rows, 3);
        assert_eq!(solve(&rows).is_some(), truth, "{rows:?}");
        if truth {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    // Both answers occur, so neither check passes by never being asked.
    assert!(
        sat > 300 && unsat > 300,
        "{sat} with a point, {unsat} without"
    );
}

#[test]
fn random_unbounded_systems_match_enumeration_in_a_window() {
    // No bound: a point of the window is a point of the rows, and the rows have a point when
    // the window holds one; with none in the window the rows may still have one outside.
    let mut rng = Rng::new(0x1_3a02);
    let (mut inside, mut outside, mut none) = (0, 0, 0);
    for _ in 0..1500 {
        let n = 1 + rng.below(5);
        let rows = random_rows(&mut rng, n, 5, 10);
        let seen = enumerate(&rows, 8);
        match (solve(&rows), seen) {
            (Some(_), true) => inside += 1,
            (Some(_), false) => outside += 1,
            (None, false) => none += 1,
            (None, true) => panic!("no point found in rows with one: {rows:?}"),
        }
    }
    assert!(inside > 100 && none > 20, "{inside}, {outside}, {none}");
}

#[test]
fn flat_and_equality_systems_match_enumeration() {
    // An equality `a·x + k = 0` as two rows, with a bound; `a` with a common factor half of
    // the time, so that some have real points and no integer point.
    let mut rng = Rng::new(0x1_3a03);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..2000 {
        let g = rng.pick(&[1, 2, 3]);
        let a = [0; 3].map(|_| g * rng.int(-4, 4));
        let k = rng.int(-15, 15);
        let mut rows = vec![row(a, k), row(a.map(|c| -c), -k)];
        let extra = rng.below(3);
        rows.extend(random_rows(&mut rng, extra, 4, 8));
        rows.extend(cube(3));
        let truth = enumerate(&rows, 3);
        assert_eq!(solve(&rows).is_some(), truth, "{rows:?}");
        if truth {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    assert!(
        sat > 200 && unsat > 200,
        "{sat} with a point, {unsat} without"
    );
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

#[test]
fn the_answer_does_not_depend_on_the_order_of_variables_or_rows() {
    let mut rng = Rng::new(0x1_3a06);
    let perms = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    for _ in 0..400 {
        let n = 2 + rng.below(5);
        let mut rows = random_rows(&mut rng, n, 7, 15);
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
    }
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

/// A random integer of `bits` bits or fewer, either sign, for `bits` a multiple of 16.
fn wide(rng: &mut Rng, bits: u32) -> Int {
    let mut c = int(rng.int(-1 << 16, 1 << 16));
    for _ in 1..bits / 16 {
        c = &(&c * &int(1 << 16)) + &int(rng.int(0, 1 << 16));
    }
    c
}

/// Reeve's tetrahedron of height 7, shrunk so it holds no integer point, and `m` rows more of
/// coefficients drawn by `coefficient`, each holding the whole unshrunk tetrahedron with slack 0 to 5.
/// No elimination, box point or rounding center decides it, so every stage runs: the linear
/// programs, the rounding, LLL, and `twovar` on each of the planes of the flat direction, all
/// over every row.
fn thin(m: usize, seed: u64, coefficient: impl Fn(&mut Rng) -> Int) -> Vec<Row3> {
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
fn scales(what: &str, n: usize, power: u32, small: &[Row3], large: &[Row3]) {
    assert_eq!(solve(small), None);
    assert_eq!(solve(large), None);
    scaling::check_order(what, n, power, |m| {
        let rows = if m == n { small } else { large };
        std::hint::black_box(point(rows));
    });
}

#[test]
fn many_rows_scale_linearly() {
    // Coefficients up to 50; the work is O(m log m), from `twovar::point` on each plane.
    let fifty = |rng: &mut Rng| int(rng.int(-50, 50));
    let (small, large) = (thin(256, 7, fifty), thin(256 * scaling::FACTOR, 7, fifty));
    scales("rows over three variables", 256, 1, &small, &large);
}

#[test]
fn wide_coefficients_scale() {
    // From 64 bits, past the `i128` fast path of `Int`, so both sizes measure big integers. A
    // product of two `B`-bit integers is `B^2` by schoolbook, but at these sizes the sums and
    // the products by small numbers cost more; power 1 catches an extra factor of `B`.
    // Measured: see COMPLEXITY.md.
    let bits = |b: u32| move |rng: &mut Rng| wide(rng, b);
    let (small, large) = (
        thin(8, 9, bits(64)),
        thin(8, 9, bits(64 * scaling::FACTOR as u32)),
    );
    scales("rows of wide coefficients, in bits", 64, 1, &small, &large);
}

// Plan item LIVE3-TESTS (from the XR3 round 3 synthesis): the systems the cross-review named,
// each with its answer found here by hand and by enumeration, and the slab family at `n` and
// `8n` rows.

/// The rows `a <= c·x <= a + w`.
fn slab(c: [i64; 3], a: i64, w: i64) -> Vec<Row3> {
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
fn formula(rows: &[Row3]) -> Formula {
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

#[test]
fn slabs_of_million_coefficients_scale() {
    // The empty slab c·x = 1 of `parity_slabs_are_decided`, c = (10^6 + 1, 10^6 + 3, 10^6 + 5),
    // over the cube |x_i| <= 5, and m rows more with coefficients up to 50, each holding the
    // whole cube with slack 0 to 5, so no row bound settles it. Every stage runs over all the
    // rows: the linear programs, the rounding, LLL (the flat direction is c) and `twovar` on the
    // one plane c·x = 1, which has no point in the cube. The work is O(m log m). From 512 rows,
    // since at 256 an all-pairs pass of `Lin2::minus` in each round of `solve2` stays under the
    // limit (COMPLEXITY.md S18).
    let c = [1_000_001, 1_000_003, 1_000_005];
    let family = |m: usize| -> Vec<Row3> {
        let mut rng = Rng::new(11);
        let mut rows: Vec<Row3> = [slab(c, 1, 0), cube(5)].concat();
        for _ in 0..m {
            let a = [0; 3].map(|_| rng.int(-50, 50));
            // The least of a·x over the cube is -5 Σ|a_i|.
            let least = -5 * a.iter().map(|c| c.abs()).sum::<i64>();
            rows.push(row(a, rng.int(0, 5) - least));
        }
        rows
    };
    let (small, large) = (family(512), family(512 * scaling::FACTOR));
    scales(
        "rows over a slab of million coefficients",
        512,
        1,
        &small,
        &large,
    );
}
