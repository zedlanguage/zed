//! The projection of rows over two atoms, besides atoms that an equation defines, by the
//! integer points of polygons (FAIL-join-pair-table, FAIL-scope-chain-scales-bytes).
//!
//! A formula of the class of the module above whose rows mention two atoms `x` and `y` and,
//! besides them, only atoms `d` that each appear in one equation alone with coefficient 1 or
//! -1 (`d == x + y`), is the set of integer points `(x, y)` of a union of convex polygons: one
//! for each range of `x`, range of `y` and range of each `d` (a `d` is a linear form in `x` and
//! `y`). The join of row sums keys `x` and `y` by one digit for each class of their rows, and
//! where their coefficients are not proportional (`y - x + 2 >= 0` and `d == x + y`) its table
//! holds every pair of values, of order m^2 for ranges of m values. Here each polygon is
//! projected onto each wanted atom by Fourier-Motzkin elimination of the other coordinate,
//! after a unimodular change of coordinates that makes the wanted form a coordinate, so the
//! cost does not depend on the widths of the ranges.
//!
//! Exactness. For an integer `p`, the integer `q` with `B_l·q >= -(A_l·p + C_l)` for each lower
//! bound `l` (`B_l > 0`) and `-B_u·q <= A_u·p + C_u` for each upper bound `u` (`B_u < 0`)
//! exists if and only if, for each pair `(l, u)`, the least integer above the lower bound is at
//! most the greatest integer below the upper one. Where `B_l == 1` the lower bound is an integer,
//! and an integer is at most the floor of a number if and only if it is at most that number;
//! the same holds where `B_u == -1`. So where every pair has a side of coefficient 1, the
//! integer `p` that have a `q` are exactly those that meet the pairs' real conditions, each
//! linear in `p`: an interval (W. Pugh, "The Omega test: a fast and practical integer
//! programming algorithm for dependence analysis", CACM 35(8), 1992, the exact shadow). Since
//! the change of coordinates is unimodular, the integer `(p, q)` are the integer `(x, y)`. A
//! pair with no side of coefficient 1, a form whose coefficients have a common factor above 1
//! (its values are a progression, as many pieces as values), or a number past `i128` is not
//! taken here: the formula goes to the join, which is exact, as before.

use zedc_lattice::interval::{End, IntervalSet, Num};

use super::rows::{Rows, gcd};

/// `a·x + b·y + c >= 0`.
#[derive(Clone, Copy, Debug)]
struct Half {
    a: i128,
    b: i128,
    c: i128,
}

/// The linear form `a·x + b·y + c`.
#[derive(Clone, Copy, Debug)]
struct Form {
    a: i128,
    b: i128,
    c: i128,
}

impl Form {
    /// The least and greatest values over the box `[x0, x1] × [y0, y1]`, at its corners.
    fn hull(&self, (x0, x1): (i128, i128), (y0, y1): (i128, i128)) -> Option<(i128, i128)> {
        let (xl, xh) = if self.a >= 0 { (x0, x1) } else { (x1, x0) };
        let (yl, yh) = if self.b >= 0 { (y0, y1) } else { (y1, y0) };
        let at = |x: i128, y: i128| {
            self.a
                .checked_mul(x)?
                .checked_add(self.b.checked_mul(y)?)?
                .checked_add(self.c)
        };
        Some((at(xl, yl)?, at(xh, yh)?))
    }
}

/// An atom of the formula, as this projection reads it.
#[derive(Clone, Copy)]
enum Role {
    /// The first (0) or second (1) of the two atoms the polygons are drawn over.
    Axis(usize),
    /// An atom an equation defines: its value is the form at each point.
    Defined(Form),
    /// An atom of no row: any value of its ranges, where the rows have a point.
    Alone,
}

/// Each wanted atom's set of values over the points of the rows, as `Plan::project` gives it;
/// `None` where the rows are not of the class the module note names, or a polygon's
/// projection is not shown exact there, so that the join answers instead.
// Complexity tradeoff: the join of row sums builds the table of the pairs of values of the two
// atoms, O(m_x·m_y / 64) word steps for ranges of m_x and m_y values, and its work passed
// `JOIN_LIMIT` (a refusal) at m = 512 (FAIL-join-pair-table); the `chain` family of l01_39
// asked one such question per test, k^3 in all. Here: one polygon per range of `x`, range of
// `y` and range of each defined atom that meets the form's values over the box of the first
// two, so P polygons with P at most r_x·r_y·Π r_d for r ranges per atom, and each polygon of
// h half-planes (4 for its box, 1 per inequality, 2 per equation or defined atom) costs
// O(h^2) per wanted atom, the pairs of Fourier-Motzkin elimination; the union of the pieces
// costs O(P log P). Nothing depends on the widths of the ranges. Not proved: that P is never
// more than the join's work where an atom has many ranges; P counts only ranges that meet the
// box, and the join's tables hold at least one key per value, so P passes the join's keys
// only where defined atoms with many short ranges each meet the boxes of many pairs of ranges
// of `x` and `y` (not met in the tests).
pub(super) fn project(rows: &Rows, want: &[bool]) -> Option<Vec<Option<IntervalSet>>> {
    let n = rows.atoms.len();
    let mut uses = vec![0usize; n];
    for row in &rows.rows {
        for &(j, _) in &row.terms {
            uses[j] += 1;
        }
    }
    // Each equation defines its first atom that appears in it alone with coefficient 1 or -1.
    let mut defines: Vec<Option<(usize, i128)>> = vec![None; rows.rows.len()];
    let mut defined = vec![false; n];
    for (r, row) in rows.rows.iter().enumerate() {
        if row.eq
            && let Some(&(j, c)) = (row.terms.iter()).find(|&&(j, c)| uses[j] == 1 && c.abs() == 1)
        {
            defines[r] = Some((j, c));
            defined[j] = true;
        }
    }
    let mut axes: Vec<usize> = (0..n).filter(|&j| uses[j] > 0 && !defined[j]).collect();
    axes.sort_unstable();
    let [ax, ay] = axes[..] else {
        return None;
    };
    let mut roles = vec![Role::Alone; n];
    roles[ax] = Role::Axis(0);
    roles[ay] = Role::Axis(1);
    // Each row as a form over the two axes, its defined atom put aside.
    let mut halves = Vec::new();
    let mut ranged: Vec<(Form, &[(i128, i128)])> = Vec::new();
    for (r, row) in rows.rows.iter().enumerate() {
        let mut f = Form {
            a: 0,
            b: 0,
            c: row.k,
        };
        for &(j, c) in &row.terms {
            if j == ax {
                f.a = c;
            } else if j == ay {
                f.b = c;
            }
        }
        match defines[r] {
            // `s·d + f == 0`, so `d == -s·f`.
            Some((d, s)) => {
                let s = -s;
                let g = Form {
                    a: s.checked_mul(f.a)?,
                    b: s.checked_mul(f.b)?,
                    c: s.checked_mul(f.c)?,
                };
                roles[d] = Role::Defined(g);
                ranged.push((g, &rows.domains[d]));
            }
            None => {
                halves.push(Half {
                    a: f.a,
                    b: f.b,
                    c: f.c,
                });
                if row.eq {
                    halves.push(Half {
                        a: f.a.checked_neg()?,
                        b: f.b.checked_neg()?,
                        c: f.c.checked_neg()?,
                    });
                }
            }
        }
    }
    let mut pieces: Vec<Vec<(End, End)>> = vec![Vec::new(); n];
    let mut any = false;
    for &bx in &rows.domains[ax] {
        for &by in &rows.domains[ay] {
            let mut polygon = halves.clone();
            polygon.extend([
                Half {
                    a: 1,
                    b: 0,
                    c: bx.0.checked_neg()?,
                },
                Half {
                    a: -1,
                    b: 0,
                    c: bx.1,
                },
                Half {
                    a: 0,
                    b: 1,
                    c: by.0.checked_neg()?,
                },
                Half {
                    a: 0,
                    b: -1,
                    c: by.1,
                },
            ]);
            any |= cases(want, &roles, &ranged, (bx, by), &mut polygon, &mut pieces)?;
        }
    }
    let mut sets = vec![None; n];
    for (a, w) in want.iter().enumerate() {
        if !*w {
            continue;
        }
        sets[a] = Some(match roles[a] {
            Role::Alone if any => IntervalSet::from_pieces(
                (rows.domains[a].iter())
                    .map(|&(l, h)| (fin(l), fin(h)))
                    .collect(),
            ),
            Role::Alone => IntervalSet::empty(),
            _ => IntervalSet::from_pieces(std::mem::take(&mut pieces[a])),
        });
    }
    Some(sets)
}

fn fin(v: i128) -> End {
    End::Fin(Num::from(v))
}

/// The polygons of one box: for each defined atom in turn, one for each of its ranges that
/// meets the form's values over the box. Adds each wanted atom's values to `pieces`; whether
/// any polygon has a point, or `None` where a projection is not shown exact.
fn cases(
    want: &[bool],
    roles: &[Role],
    ranged: &[(Form, &[(i128, i128)])],
    bx: ((i128, i128), (i128, i128)),
    polygon: &mut Vec<Half>,
    pieces: &mut [Vec<(End, End)>],
) -> Option<bool> {
    let Some(((g, ranges), rest)) = ranged.split_first() else {
        return polygon_pieces(want, roles, polygon, pieces);
    };
    let (lo, hi) = g.hull(bx.0, bx.1)?;
    // The ranges are sorted and disjoint: those that meet `[lo, hi]` are one run.
    let from = ranges.partition_point(|r| r.1 < lo);
    let mut any = false;
    for &(l, h) in ranges[from..].iter().take_while(|r| r.0 <= hi) {
        let len = polygon.len();
        polygon.push(Half {
            a: g.a,
            b: g.b,
            c: g.c.checked_sub(l)?,
        });
        polygon.push(Half {
            a: g.a.checked_neg()?,
            b: g.b.checked_neg()?,
            c: h.checked_sub(g.c)?,
        });
        let found = cases(want, roles, rest, bx, polygon, pieces);
        polygon.truncate(len);
        any |= found?;
    }
    Some(any)
}

/// The values of each wanted atom over one polygon, added to `pieces`; whether it has a point.
fn polygon_pieces(
    want: &[bool],
    roles: &[Role],
    polygon: &[Half],
    pieces: &mut [Vec<(End, End)>],
) -> Option<bool> {
    // The first axis's values: empty if and only if the polygon has no integer point.
    let Some(xs) = shadow(polygon, 1, 0)? else {
        return Some(false);
    };
    for (a, w) in want.iter().enumerate() {
        if !*w {
            continue;
        }
        let (lo, hi) = match roles[a] {
            Role::Axis(0) => xs,
            Role::Axis(_) => shadow(polygon, 0, 1)??,
            Role::Defined(g) => {
                if g.a == 0 && g.b == 0 {
                    (g.c, g.c)
                } else {
                    // A form with a common factor above 1 takes every g-th value: left to the
                    // join (module note).
                    if gcd(g.a.unsigned_abs(), g.b.unsigned_abs()) != 1 {
                        return None;
                    }
                    let (l, h) = shadow(polygon, g.a, g.b)??;
                    (l.checked_add(g.c)?, h.checked_add(g.c)?)
                }
            }
            Role::Alone => continue,
        };
        pieces[a].push((fin(lo), fin(hi)));
    }
    Some(true)
}

/// The values of `p = a·x + b·y` (`a` and `b` coprime) over the integer points of `polygon`:
/// `Some(None)` where there are none, `None` where the elimination is not shown exact (module
/// note) or a number passes `i128`.
fn shadow(polygon: &[Half], a: i128, b: i128) -> Option<Option<(i128, i128)>> {
    // `s·a + t·b == 1`; `q = u·x + v·y` with `(u, v) = (-t, s)` completes `p` to a unimodular
    // basis, whose inverse is `x = v·p - b·q`, `y = -u·p + a·q`.
    let (s, t) = bezout(a, b)?;
    let (u, v) = (t.checked_neg()?, s);
    // Each half-plane `A·p + B·q + C >= 0`, put by the sign of `B`.
    let (mut free, mut lower, mut upper) = (Vec::new(), Vec::new(), Vec::new());
    for h in polygon {
        let big_a = h.a.checked_mul(v)?.checked_sub(h.b.checked_mul(u)?)?;
        let big_b = h.b.checked_mul(a)?.checked_sub(h.a.checked_mul(b)?)?;
        let row = (big_a, big_b, h.c);
        match big_b.signum() {
            0 => free.push((big_a, h.c)),
            1 => lower.push(row),
            _ => upper.push(row),
        }
    }
    for &(al, bl, cl) in &lower {
        for &(au, bu, cu) in &upper {
            if bl != 1 && bu != -1 {
                return None;
            }
            // `(-(A_l·p + C_l)) / B_l <= (A_u·p + C_u) / (-B_u)`.
            let pa = bl.checked_mul(au)?.checked_sub(bu.checked_mul(al)?)?;
            let pc = bl.checked_mul(cu)?.checked_sub(bu.checked_mul(cl)?)?;
            free.push((pa, pc));
        }
    }
    // `A·p + C >= 0` for each.
    let (mut lo, mut hi): (Option<i128>, Option<i128>) = (None, None);
    for (pa, pc) in free {
        match pa.signum() {
            0 if pc < 0 => return Some(None),
            0 => {}
            1 => {
                let l = div_ceil(pc.checked_neg()?, pa)?;
                lo = Some(lo.map_or(l, |v| v.max(l)));
            }
            _ => {
                let h = div_floor(pc, pa.checked_neg()?)?;
                hi = Some(hi.map_or(h, |v| v.min(h)));
            }
        }
    }
    // The box bounds the polygon, so both ends are found (module note); else the join answers.
    let (lo, hi) = (lo?, hi?);
    Some((lo <= hi).then_some((lo, hi)))
}

/// `(s, t)` with `s·a + t·b == 1`, for `a` and `b` coprime (extended Euclid).
fn bezout(a: i128, b: i128) -> Option<(i128, i128)> {
    let (mut r0, mut r1) = (a, b);
    let (mut s0, mut s1) = (1i128, 0i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0.checked_div(r1)?;
        (r0, r1) = (r1, r0.checked_sub(q.checked_mul(r1)?)?);
        (s0, s1) = (s1, s0.checked_sub(q.checked_mul(s1)?)?);
        (t0, t1) = (t1, t0.checked_sub(q.checked_mul(t1)?)?);
    }
    match r0 {
        1 => Some((s0, t0)),
        -1 => Some((s0.checked_neg()?, t0.checked_neg()?)),
        _ => None,
    }
}

/// `floor(n / d)` for `d > 0`.
fn div_floor(n: i128, d: i128) -> Option<i128> {
    n.checked_div_euclid(d)
}

/// `ceil(n / d)` for `d > 0`.
fn div_ceil(n: i128, d: i128) -> Option<i128> {
    div_floor(n.checked_neg()?, d)?.checked_neg()
}

#[cfg(test)]
mod tests {
    use super::super::super::formula::Atom;
    use super::super::rows::Row;
    use super::*;

    /// Each atom's values over the points of `rows`, by trying every value of atoms 0 and 1:
    /// atom `2 + i` is the one of coefficient 1 or -1 in row `defs + i`, its value set by that
    /// row, and the atoms after those take every value of their ranges.
    fn by_points(rows: &Rows, defs: usize, n_def: usize) -> Vec<Vec<i128>> {
        let n = rows.atoms.len();
        let mut each = vec![std::collections::BTreeSet::new(); n];
        let all = |j: usize| rows.domains[j].iter().flat_map(|&(l, h)| l..=h);
        let inside = |j: usize, v: i128| rows.domains[j].iter().any(|&(l, h)| l <= v && v <= h);
        let mut point = vec![0i128; n];
        for x in all(0) {
            for y in all(1) {
                point[0] = x;
                point[1] = y;
                let mut fits = true;
                for i in 0..n_def {
                    let r = &rows.rows[defs + i];
                    let s = r.terms.iter().find(|t| t.0 == 2 + i).expect("defined").1;
                    let rest: i128 = r.k
                        + (r.terms.iter())
                            .filter(|t| t.0 < 2)
                            .map(|&(a, c)| c * point[a])
                            .sum::<i128>();
                    point[2 + i] = -s * rest;
                    fits &= inside(2 + i, point[2 + i]);
                }
                let holds = fits
                    && rows.rows.iter().all(|r| {
                        let v = r.k + r.terms.iter().map(|&(a, c)| c * point[a]).sum::<i128>();
                        if r.eq { v == 0 } else { v >= 0 }
                    });
                if holds {
                    for (s, &v) in each.iter_mut().zip(&point[..2 + n_def]) {
                        s.insert(v);
                    }
                    for (j, s) in each.iter_mut().enumerate().skip(2 + n_def) {
                        s.extend(all(j));
                    }
                }
            }
        }
        each.into_iter().map(|s| s.into_iter().collect()).collect()
    }

    fn values(set: &IntervalSet) -> Vec<i128> {
        let int = |e: &End| match e {
            End::Fin(v) => v.to_i128().expect("small"),
            _ => panic!("an infinite end"),
        };
        (set.pieces()).flat_map(|(l, h)| int(l)..=int(h)).collect()
    }

    /// Random rows over two atoms `x` and `y`, with up to two atoms an equation defines and one
    /// atom of no row, each atom over up to three ranges: wherever `project` answers, each set is
    /// that of the points. It answers about half (2,962 of 6,000 at this seed), 1,666 of
    /// those with no point and 349 with a defined atom and a point, and declines the rest (a
    /// pair `2·y >= ..`, `-3·y >= ..`; a defined atom `2·x + 2·y`; an atom defined by an
    /// equation over `x` alone).
    #[test]
    fn projections_are_those_of_the_points() {
        let mut seed = 0x2545_F491_4F6C_DD1D_u64;
        let mut next = move |n: u64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (seed >> 33) % n
        };
        // Ranges from about `-w` up, of up to `w` values each.
        let ranges = |w: u64, next: &mut dyn FnMut(u64) -> u64| {
            let mut at = -(w as i128) + next(6) as i128;
            let mut out = Vec::new();
            for _ in 0..1 + next(3) {
                let hi = at + next(w) as i128;
                out.push((at, hi));
                at = hi + 2 + next(4) as i128;
            }
            out
        };
        let (mut answered, mut declined, mut empty, mut defined) = (0, 0, 0, 0);
        for case in 0..6000 {
            let n_def = (case % 3) as usize;
            let alone = case % 5 == 0;
            let n = 2 + n_def + usize::from(alone);
            let mut domains = Vec::new();
            for j in 0..n {
                domains.push(ranges(if j < 2 { 9 } else { 30 }, &mut next));
            }
            let coef = |next: &mut dyn FnMut(u64) -> u64| next(7) as i128 - 3;
            let mut rows_v = Vec::new();
            for _ in 0..1 + next(2) {
                let (a, b) = (coef(&mut next), coef(&mut next));
                rows_v.push(Row {
                    terms: [(0, a), (1, b)].into_iter().filter(|t| t.1 != 0).collect(),
                    k: next(13) as i128 - 4,
                    eq: next(6) == 0,
                });
            }
            for d in 0..n_def {
                let (a, b) = (next(5) as i128 - 2, next(5) as i128 - 2);
                let s = if next(2) == 0 { 1 } else { -1 };
                let mut terms: Vec<(usize, i128)> =
                    [(0, a), (1, b)].into_iter().filter(|t| t.1 != 0).collect();
                terms.push((2 + d, s));
                rows_v.push(Row {
                    terms,
                    k: next(11) as i128 - 5,
                    eq: true,
                });
            }
            let rows = Rows {
                atoms: (0..n).map(|i| Atom::Sym(format!("a{i}").into())).collect(),
                domains,
                rows: rows_v,
                empty: false,
            };
            let want = vec![true; n];
            let points = by_points(&rows, rows.rows.len() - n_def, n_def);
            match project(&rows, &want) {
                Some(sets) => {
                    answered += 1;
                    empty += usize::from(points[0].is_empty());
                    defined += usize::from(n_def > 0 && !points[0].is_empty());
                    for (a, (got, w)) in sets.iter().zip(&points).enumerate() {
                        let got = values(got.as_ref().expect("wanted"));
                        assert_eq!(&got, w, "case {case}, atom {a}");
                    }
                }
                None => declined += 1,
            }
        }
        assert!(answered > 2500 && declined > 50, "{answered} {declined}");
        assert!(empty > 100 && defined > 300, "{empty} {defined}");
    }

    /// The question of each test of the `chain` family of l01_39 (`x + c·y >= 1` or
    /// `y - x >= c`, with `a == x + y`) is answered here, at every width: its eliminations all
    /// have a side of coefficient 1.
    #[test]
    fn the_chain_questions_are_answered() {
        for m in [8i128, 64, 512, 1 << 40] {
            for (row, c) in [((1, 7), -1), ((-1, 1), -5)] {
                let rows = Rows {
                    atoms: ["a", "x", "y"].map(|s| Atom::Sym(s.into())).to_vec(),
                    domains: vec![
                        vec![(-2 * m, 2 * m)],
                        vec![(-m, m)],
                        vec![(-m, -m / 8), (m / 8, m)],
                    ],
                    rows: vec![
                        Row {
                            terms: vec![(1, row.0), (2, row.1)],
                            k: c,
                            eq: false,
                        },
                        Row {
                            terms: vec![(0, -1), (1, 1), (2, 1)],
                            k: 0,
                            eq: true,
                        },
                    ],
                    empty: false,
                };
                let sets = project(&rows, &[true; 3]).expect("answered");
                assert!(
                    sets.iter()
                        .all(|s| s.as_ref().is_some_and(|s| s.len() <= 2))
                );
            }
        }
    }
}
