//! The unit checks of the affine hull and its join.

use std::collections::BTreeMap;

use zed_tests::scaling;
use zedc::store::hull::Hull;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Lin};

/// `sum of c * name` plus `k`.
fn lin(terms: &[(&str, i128)], k: i128) -> Lin {
    Lin {
        terms: terms
            .iter()
            .filter(|(_, c)| *c != 0)
            .map(|(s, c)| (Atom::Sym((*s).into()), Int::from(*c)))
            .collect(),
        constant: Int::from(k),
    }
}

/// The hull of one point.
fn point(names: &[String], v: &[i128]) -> Hull {
    let rows: Vec<Lin> = names
        .iter()
        .zip(v)
        .map(|(s, x)| lin(&[(s, 1)], -x))
        .collect();
    Hull::of(&rows)
}

/// The value of `t` at `m`.
fn eval(t: &Lin, m: &BTreeMap<Atom, i128>) -> i128 {
    t.terms
        .iter()
        .map(|(a, c)| c.to_i128().expect("small") * m[a])
        .sum::<i128>()
        + t.constant.to_i128().expect("small")
}

/// The rank of the integer vectors, by fraction-free elimination.
fn rank(vs: &[Vec<i128>]) -> usize {
    let mut rows = vs.to_vec();
    let mut r = 0;
    let width = rows.first().map_or(0, Vec::len);
    for col in 0..width {
        let Some(p) = (r..rows.len()).find(|&i| rows[i][col] != 0) else {
            continue;
        };
        rows.swap(p, r);
        let t = rows[r].clone();
        for row in rows.iter_mut().skip(r + 1) {
            let c = row[col];
            if c != 0 {
                *row = (0..width).map(|j| row[j] * t[col] - t[j] * c).collect();
                let g = row.iter().fold(0i128, |g, &x| gcd(g, x));
                if g > 1 {
                    row.iter_mut().for_each(|x| *x /= g);
                }
            }
        }
        r += 1;
    }
    r
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Checks that `h` is the affine hull of `points`: each row is zero at each point, and the
/// rows number the dimension less the dimension the points span.
fn is_hull_of(h: &Hull, names: &[String], points: &[Vec<i128>]) {
    for p in points {
        let m: BTreeMap<Atom, i128> = names
            .iter()
            .zip(p)
            .map(|(s, x)| (Atom::Sym(s.as_str().into()), *x))
            .collect();
        for t in h.rows() {
            assert_eq!(eval(t, &m), 0, "{t} at {p:?}");
        }
    }
    let diffs: Vec<Vec<i128>> = points[1..]
        .iter()
        .map(|p| p.iter().zip(&points[0]).map(|(x, y)| x - y).collect())
        .collect();
    assert_eq!(h.rows().count(), names.len() - rank(&diffs), "{h}");
}

/// A small linear congruential generator, so the test needs no crate.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> i128 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) % n) as i128
    }
}

/// The points `x0 + M t` for random small `M`, `x0` and `t`, of dimension at most `k`.
fn on_plane(rnd: &mut Rng, d: usize, k: usize, n: usize) -> Vec<Vec<i128>> {
    let x0: Vec<i128> = (0..d).map(|_| rnd.below(7) - 3).collect();
    let m: Vec<Vec<i128>> = (0..d)
        .map(|_| {
            (0..k)
                .map(|_| {
                    if rnd.below(3) == 0 {
                        rnd.below(5) - 2
                    } else {
                        0
                    }
                })
                .collect()
        })
        .collect();
    (0..n)
        .map(|_| {
            let t: Vec<i128> = (0..k).map(|_| rnd.below(9) - 4).collect();
            (0..d)
                .map(|i| x0[i] + (0..k).map(|j| m[i][j] * t[j]).sum::<i128>())
                .collect()
        })
        .collect()
}

/// A hull of `n` rows.
fn rows_of(n: usize) -> Hull {
    let rows: Vec<Lin> = (0..n)
        .map(|i| lin(&[(&format!("y{i}"), 1), (&format!("z{i}"), -1)], 0))
        .collect();
    Hull::of(&rows)
}

/// `n` joins as at a loop head, each of the hull `h` of `n` rows with itself and one more row,
/// `name(i) == i` at the `i`th.
fn loop_joins(h: &Hull, n: usize, name: impl Fn(usize) -> String) {
    let mut h = h.clone();
    for i in 0..n {
        let b = h.clone().and(&lin(&[(&name(i), 1)], -(i as i128)));
        h = h.join(&b);
    }
    assert_eq!(h.rows().count(), n);
}

#[test]
fn the_textbook_join_keeps_exactly_i_plus_j_minus_n() {
    // {i == 0, j == n} and {i == 1, j == n - 1} both hold i + j == n, and nothing else.
    let a = Hull::of(&[lin(&[("i", 1)], 0), lin(&[("j", 1), ("n", -1)], 0)]);
    let b = Hull::of(&[lin(&[("i", 1)], -1), lin(&[("j", 1), ("n", -1)], 1)]);
    assert_eq!(a.clone().join(&b).to_string(), "i + j - n == 0");
    assert_eq!(b.join(&a).to_string(), "i + j - n == 0");
}

#[test]
fn a_contradiction_is_the_empty_hull_and_the_identity_of_join() {
    let e = Hull::of(&[lin(&[("x", 1)], 0), lin(&[("x", 1)], -1)]);
    assert!(e.is_empty);
    let a = Hull::of(&[lin(&[("x", 2), ("y", -4)], 6)]);
    assert_eq!(a.to_string(), "x - 2 * y + 3 == 0");
    let shown = a.to_string();
    assert_eq!(e.clone().join(&a).to_string(), shown);
    assert_eq!(a.join(&e).to_string(), shown);
}

#[test]
fn the_join_of_point_hulls_is_the_hull_of_the_points() {
    // Random points on random planes; the hulls of the points are joined one at a time, in
    // either order of the names, so the rows that differ lie first or last.
    let mut rnd = Rng(7);
    for _ in 0..200 {
        let d = 1 + rnd.below(7) as usize;
        let k = rnd.below(d as u64 + 1) as usize;
        let n = 1 + rnd.below(6) as usize;
        let names: Vec<String> = (0..d).map(|i| format!("x{i}")).collect();
        let pts = on_plane(&mut rnd, d, k, n);
        for rev in [false, true] {
            let cols: Vec<usize> = if rev {
                (0..d).rev().collect()
            } else {
                (0..d).collect()
            };
            let order: Vec<String> = cols.iter().map(|&c| names[c].clone()).collect();
            let ps: Vec<Vec<i128>> = pts
                .iter()
                .map(|p| cols.iter().map(|&c| p[c]).collect())
                .collect();
            let h = ps
                .iter()
                .map(|p| point(&order, p))
                .reduce(|x, y| x.join(&y))
                .expect("a point");
            is_hull_of(&h, &order, &ps);
        }
    }
}

#[test]
fn a_join_of_hulls_that_differ_in_a_few_names_is_exact() {
    // As at a loop head: the second side is the first with a few names moved by one, and the
    // join is the hull of both sides' points.
    let mut rnd = Rng(11);
    for _ in 0..100 {
        let d = 4 + rnd.below(8) as usize;
        let k = 1 + rnd.below(3) as usize;
        let names: Vec<String> = (0..d).map(|i| format!("x{i}")).collect();
        let a = on_plane(&mut rnd, d, k, k + 2);
        let moved: Vec<usize> = (0..2).map(|_| rnd.below(d as u64) as usize).collect();
        let b: Vec<Vec<i128>> = a
            .iter()
            .map(|p| {
                (0..d)
                    .map(|i| p[i] + i128::from(moved.contains(&i)))
                    .collect()
            })
            .collect();
        let of = |ps: &[Vec<i128>]| {
            ps.iter()
                .map(|p| point(&names, p))
                .reduce(|x, y| x.join(&y))
                .expect("a point")
        };
        let all: Vec<Vec<i128>> = a.iter().chain(&b).cloned().collect();
        is_hull_of(&of(&a).join(&of(&b)), &names, &all);
    }
}

#[test]
fn a_join_costs_near_the_rows_that_differ() {
    // n joins of hulls of n rows differing in one, whose pivot sorts before every other: near
    // n log n in all.
    let hulls: BTreeMap<usize, Hull> = [256, scaling::FACTOR * 256]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    scaling::check("the join of hulls", 256, |m| {
        loop_joins(&hulls[&m], m, |i| format!("x{i}"))
    });
}

#[test]
fn a_join_costs_near_the_rows_that_differ_wherever_they_sort() {
    // As above, with the new row's pivot among the rows' pivots `y…` (`y12a` sorts between
    // `y12` and `y120`) and after all of them.
    let hulls: BTreeMap<usize, Hull> = [256, scaling::FACTOR * 256]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    scaling::check("the join of hulls, a row among the others", 256, |m| {
        loop_joins(&hulls[&m], m, |i| format!("y{i}a"))
    });
    scaling::check("the join of hulls, a row after the others", 256, |m| {
        loop_joins(&hulls[&m], m, |i| format!("zz{i}"))
    });
}

#[test]
fn a_join_with_a_hull_narrowed_from_it_is_the_first_hull() {
    // A loop head joins the hull at entry with the hull after the body; here the body narrows
    // the hull by a few equalities, which may rewrite many of its rows, so the second hull
    // shares part of its rows with the first and holds others rewritten. Either way round, the
    // join is the hull of the first's points.
    let mut rnd = Rng(23);
    for _ in 0..200 {
        let d = 3 + rnd.below(8) as usize;
        let k = rnd.below(4) as usize;
        let names: Vec<String> = (0..d).map(|i| format!("x{i}")).collect();
        let pts = on_plane(&mut rnd, d, k, k + 2);
        let a = pts
            .iter()
            .map(|p| point(&names, p))
            .reduce(|x, y| x.join(&y))
            .expect("a point");
        let mut b = a.clone();
        for _ in 0..1 + rnd.below(3) {
            let i = rnd.below(d as u64) as usize;
            let j = rnd.below(d as u64) as usize;
            b = b.and(&lin(&[(&names[i], 1), (&names[j], -2)], rnd.below(3) - 1));
        }
        is_hull_of(&a.clone().join(&b), &names, &pts);
        is_hull_of(&b.join(&a), &names, &pts);
    }
}

#[test]
fn a_join_of_hulls_built_apart_is_exact() {
    // Two hulls of one set built in different orders share no rows in memory; the join
    // compares their rows by value and keeps the hull.
    let mut rnd = Rng(31);
    for _ in 0..100 {
        let d = 3 + rnd.below(8) as usize;
        let k = rnd.below(4) as usize;
        let names: Vec<String> = (0..d).map(|i| format!("x{i}")).collect();
        let pts = on_plane(&mut rnd, d, k, k + 2);
        let of = |ps: &mut dyn Iterator<Item = &Vec<i128>>| {
            ps.map(|p| point(&names, p))
                .reduce(|x, y| x.join(&y))
                .expect("a point")
        };
        let a = of(&mut pts.iter());
        let b = of(&mut pts.iter().rev());
        is_hull_of(&a.clone().join(&b), &names, &pts);
        let rebuilt = Hull::of(a.rows());
        is_hull_of(&a.join(&rebuilt), &names, &pts);
    }
}

#[test]
fn a_join_after_a_row_that_rewrites_every_row_keeps_the_line() {
    // `x0 - x1, …, x0 - xn` hold on the line where every name is equal; `x0 - 7` then fixes
    // each, rewriting every row. The join of the two is the line again.
    let n = 40;
    let line = Hull::of(&star(n)[..n]);
    let fixed = line.clone().and(&lin(&[("x0", 1)], -7));
    assert_eq!(fixed.rows().count(), n + 1);
    let names: Vec<String> = (0..=n).map(|i| format!("x{i}")).collect();
    let pts = vec![vec![0; n + 1], vec![1; n + 1]];
    is_hull_of(&line.clone().join(&fixed), &names, &pts);
    is_hull_of(&fixed.join(&line), &names, &pts);
}

/// The rows `x0 - x1`, `x0 - x2`, …, `x0 - xn`, then `x0 - 7`, which rewrites the rows that
/// mention the pivot it takes.
fn star(n: usize) -> Vec<Lin> {
    (1..=n)
        .map(|i| lin(&[("x0", 1), (&format!("x{i}"), -1)], 0))
        .chain([lin(&[("x0", 1)], -7)])
        .collect()
}

#[test]
fn names_equal_to_one_name_and_then_fixed_are_all_fixed() {
    let h = Hull::of(&star(3));
    assert_eq!(
        h.to_string(),
        "x0 - 7 == 0, x1 - 7 == 0, x2 - 7 == 0, x3 - 7 == 0"
    );
}

#[test]
fn a_hull_is_built_row_by_row_in_time_near_its_rows() {
    // Each row is added to a hull that no one else holds, so it is changed in place.
    let rows: BTreeMap<usize, Vec<Lin>> = [512, scaling::FACTOR * 512]
        .into_iter()
        .map(|m| (m, star(m)))
        .collect();
    scaling::check("building a hull row by row", 512, |m| {
        let h = Hull::of(&rows[&m]);
        assert_eq!(h.rows().count(), m + 1);
    });
}
