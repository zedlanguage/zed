//! The unit checks of the affine hull and its join.

use std::collections::BTreeMap;

use zed_tests::scaling;
use zedc::store::hull::Hull;
use zedc::store::presburger::{Atom, Lin};

/// `sum of c * name` plus `k`.
fn lin(terms: &[(&str, i128)], k: i128) -> Lin {
    Lin {
        terms: terms
            .iter()
            .filter(|(_, c)| *c != 0)
            .map(|(s, c)| (Atom::Sym((*s).into()), *c))
            .collect(),
        constant: k,
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
    t.terms.iter().map(|(a, c)| c * m[a]).sum::<i128>() + t.constant
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

/// `n` joins as at a loop head, each of the hull `h` of `n` rows with itself and one more row;
/// with `copy`, each joins a copy of the hull that shares nothing with it.
fn loop_joins(h: &Hull, n: usize, copy: bool) {
    let mut h = h.clone();
    for i in 0..n {
        let b = h.and(&lin(&[(&format!("x{i}"), 1)], -(i as i128)));
        let a = if copy {
            let rows: Vec<Lin> = h.rows().cloned().collect();
            Hull::of(&rows)
        } else {
            h
        };
        h = a.join(&b);
    }
    assert_eq!(h.rows().count(), n);
}

#[test]
fn the_textbook_join_keeps_exactly_i_plus_j_minus_n() {
    // {i == 0, j == n} and {i == 1, j == n - 1} both hold i + j == n, and nothing else.
    let a = Hull::of(&[lin(&[("i", 1)], 0), lin(&[("j", 1), ("n", -1)], 0)]);
    let b = Hull::of(&[lin(&[("i", 1)], -1), lin(&[("j", 1), ("n", -1)], 1)]);
    assert_eq!(a.join(&b).to_string(), "i + j - n == 0");
    assert_eq!(b.join(&a).to_string(), "i + j - n == 0");
}

#[test]
fn a_contradiction_is_the_empty_hull_and_the_identity_of_join() {
    let e = Hull::of(&[lin(&[("x", 1)], 0), lin(&[("x", 1)], -1)]);
    assert!(e.is_empty);
    let a = Hull::of(&[lin(&[("x", 2), ("y", -4)], 6)]);
    assert_eq!(a.to_string(), "x - 2 * y + 3 == 0");
    assert_eq!(e.join(&a).to_string(), a.to_string());
    assert_eq!(a.join(&e).to_string(), a.to_string());
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
    // n joins of hulls of n rows differing in one: near n log² n in all.
    let hulls: BTreeMap<usize, Hull> = [256, scaling::FACTOR * 256]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    scaling::check("the join of hulls", 256, |m| {
        loop_joins(&hulls[&m], m, false)
    });
}

#[test]
fn control_the_scaling_check_catches_a_join_that_reads_every_row() {
    let hulls: BTreeMap<usize, Hull> = [64, scaling::FACTOR * 64]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    let caught = std::panic::catch_unwind(|| {
        scaling::check("the join of copies", 64, |m| {
            loop_joins(&hulls[&m], m, true)
        });
    });
    assert!(
        caught.is_err(),
        "the check passed a join that reads every row"
    );
}
