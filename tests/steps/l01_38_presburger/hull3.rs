//! The shadow of a polyhedron in three variables (`zedc::store::hull3`, XT3 B4): the pairs it
//! chooses cut out the same set as all pairs of a lower and an upper bound (Fourier–Motzkin),
//! checked at every half-integer point of a window, on random systems and on degenerate ones
//! (planes through one line or one point, normals in one plane, unbounded, empty, a single
//! point), and its work at n and 8n planes.

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::hull3::{Plane, shadow};
use zedc::store::int::Int;

/// `z·Z + x·X + y·Y + k >= 0`, as `[z, x, y, k]`.
type Row = [i64; 4];

fn planes(rows: &[Row]) -> Vec<Plane> {
    rows.iter()
        .map(|r| Plane {
            z: Int::from(r[0]),
            x: Int::from(r[1]),
            y: Int::from(r[2]),
            k: Int::from(r[3]),
        })
        .collect()
}

/// The combination `α·X + β·Y + γ >= 0` of a lower bound `p` and an upper bound `q` on `Z`.
fn combine(p: &Row, q: &Row) -> [i128; 3] {
    let (a, b) = (i128::from(-q[0]), i128::from(p[0]));
    [1, 2, 3].map(|i| a * i128::from(p[i]) + b * i128::from(q[i]))
}

/// The half-integer points `(X/2, Y/2)`, `|X|, |Y| <= 24`, where every combination holds.
fn points(rows: &[[i128; 3]]) -> Vec<(i128, i128)> {
    let mut v = Vec::new();
    for xx in -24..=24 {
        for yy in -24..=24 {
            if rows.iter().all(|r| r[0] * xx + r[1] * yy + 2 * r[2] >= 0) {
                v.push((xx, yy));
            }
        }
    }
    v
}

/// The shadow's pairs are each a lower and an upper bound, and cut out the same points of
/// the window as all pairs.
fn agrees(rows: &[Row]) -> Vec<(usize, usize)> {
    let pairs = shadow(&planes(rows));
    for &(p, q) in &pairs {
        assert!(
            rows[p][0] > 0 && rows[q][0] < 0,
            "{rows:?}: pair ({p}, {q})"
        );
    }
    let chosen: Vec<[i128; 3]> = pairs
        .iter()
        .map(|&(p, q)| combine(&rows[p], &rows[q]))
        .collect();
    let mut all = Vec::new();
    for p in rows.iter().filter(|r| r[0] > 0) {
        for q in rows.iter().filter(|r| r[0] < 0) {
            all.push(combine(p, q));
        }
    }
    assert_eq!(points(&chosen), points(&all), "{rows:?}: pairs {pairs:?}");
    pairs
}

fn random_rows(g: &mut Rng, m: usize, c: i64, k: i64, zc: i64) -> Vec<Row> {
    (0..m)
        .map(|_| {
            let z = g.int(1, zc) * if g.below(2) == 0 { 1 } else { -1 };
            [z, g.int(-c, c), g.int(-c, c), g.int(-k, k)]
        })
        .collect()
}

#[test]
fn the_shadow_agrees_with_all_pairs_on_random_systems() {
    let mut g = Rng::new(0x4_3333);
    for _ in 0..400 {
        let m = 1 + g.below(12);
        agrees(&random_rows(&mut g, m, 5, 12, 3));
    }
}

#[test]
fn the_shadow_agrees_with_all_pairs_when_planes_coincide() {
    // Coefficients in -1..1: many planes parallel, equal, or meeting in one line or point.
    let mut g = Rng::new(0x4_3334);
    for _ in 0..400 {
        let m = 1 + g.below(14);
        agrees(&random_rows(&mut g, m, 1, 2, 2));
    }
}

#[test]
fn planes_through_one_line_or_one_point() {
    // All through the line X = Y = Z: the shadow is that line's shadow, the diagonal.
    let line: Vec<Row> = vec![
        [1, -1, 0, 0],
        [1, 0, -1, 0],
        [2, -1, -1, 0],
        [-1, 1, 0, 0],
        [-1, 0, 1, 0],
        [-3, 1, 2, 0],
    ];
    agrees(&line);
    let on: Vec<(i128, i128)> = (-24..=24).map(|v| (v, v)).collect();
    let pairs = shadow(&planes(&line));
    let rows: Vec<[i128; 3]> = pairs
        .iter()
        .map(|&(p, q)| combine(&line[p], &line[q]))
        .collect();
    assert_eq!(points(&rows), on);
    // A cone with its apex at the origin, Z >= |X| + |Y| and Z <= 0: a single point.
    let point: Vec<Row> = vec![
        [1, 1, 1, 0],
        [1, -1, 1, 0],
        [1, 1, -1, 0],
        [1, -1, -1, 0],
        [-1, 0, 0, 0],
    ];
    let pairs = agrees(&point);
    let rows: Vec<[i128; 3]> = pairs
        .iter()
        .map(|&(p, q)| combine(&point[p], &point[q]))
        .collect();
    assert_eq!(points(&rows), vec![(0, 0)]);
    // The same plane many times over, on both sides: a slab of width zero over everything.
    let same: Vec<Row> = vec![
        [1, 2, 3, 4],
        [1, 2, 3, 4],
        [-1, -2, -3, -4],
        [-2, -4, -6, -8],
    ];
    let pairs = agrees(&same);
    assert!(pairs.iter().all(|&(p, q)| {
        let r = combine(&same[p], &same[q]);
        r[0] == 0 && r[1] == 0 && r[2] >= 0
    }));
}

#[test]
fn normals_in_one_plane_unbounded_and_empty_shadows() {
    // No Y anywhere: a strip in X.
    agrees(&[[1, 1, 0, 3], [1, -2, 0, 1], [-1, 1, 0, 4], [-2, 0, 0, 5]]);
    // One side only: no pair, no bound.
    assert!(agrees(&[[1, 1, 2, 3], [2, -1, 0, 1]]).is_empty());
    assert!(agrees(&[[-1, 1, 2, 3]]).is_empty());
    // A half-plane, and an unbounded wedge.
    agrees(&[[1, 0, 0, 0], [-1, 1, 1, 0]]);
    agrees(&[[1, 1, 0, 0], [1, 0, 1, 0], [-1, 0, 0, 5]]);
    // Parallel bounds that do not meet: one false pair.
    let gap: Vec<Row> = vec![[1, 1, 1, -1], [-1, -1, -1, 0], [1, 0, 0, 7]];
    let pairs = agrees(&gap);
    assert_eq!(pairs.len(), 1);
    let r = combine(&gap[pairs[0].0], &gap[pairs[0].1]);
    assert!(r[0] == 0 && r[1] == 0 && r[2] < 0, "{r:?}");
    // Bounds that meet nowhere though no two are parallel.
    let none: Vec<Row> = vec![[1, -1, 0, 0], [1, 1, 0, 0], [1, 0, 1, 0], [-1, 0, 0, -1]];
    let pairs = agrees(&none);
    let rows: Vec<[i128; 3]> = pairs
        .iter()
        .map(|&(p, q)| combine(&none[p], &none[q]))
        .collect();
    assert!(points(&rows).is_empty());
}

/// `n` planes tangent to `Z = X² + Y²` from below and `n` to `Z = C - X² - Y²` from above,
/// at random points: the shadow is a polygon near a circle with an edge for many pairs.
fn tangents(n: usize) -> Vec<Plane> {
    let mut g = Rng::new(0x4_3335);
    let c = 2_000_000i64;
    let mut v = Vec::with_capacity(2 * n);
    for i in 0..2 * n {
        let (a, b) = (g.int(-1000, 1000), g.int(-1000, 1000));
        let r = if i % 2 == 0 {
            // Z >= 2aX + 2bY - a² - b².
            [1, -2 * a, -2 * b, a * a + b * b]
        } else {
            // Z <= -2aX - 2bY + a² + b² + C.
            [-1, -2 * a, -2 * b, a * a + b * b + c]
        };
        v.push(Plane {
            z: Int::from(r[0]),
            x: Int::from(r[1]),
            y: Int::from(r[2]),
            k: Int::from(r[3]),
        });
    }
    v
}

#[test]
fn the_shadow_scales() {
    let (small, large) = (tangents(128), tangents(128 * scaling::FACTOR));
    assert!(shadow(&small).len() >= 16, "the polygon has many edges");
    scaling::check("the shadow of tangent planes", 128, |m| {
        let p = if m == 128 { &small } else { &large };
        std::hint::black_box(shadow(p));
    });
}
