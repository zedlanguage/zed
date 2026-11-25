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
//! linear in `p`: an interval (W. Pugh, "The Omega test", 1991, doi:10.1145/125826.125848,
//! and its CACM 1992 version, doi:10.1145/135226.135233, sec. 2.3.2: the dark and real
//! shadows agree when `a = 1` or `b = 1`, the exact projection; full citations in the crate
//! root's References; the step is proved above and does not rest on the paper). Since
//! the change of coordinates is unimodular, the integer `(p, q)` are the integer `(x, y)`. A
//! pair with no side of coefficient 1, a form whose coefficients have a common factor above 1
//! (its values are a progression, as many pieces as values), or a number past `i128` is not
//! taken here: the formula goes to the join, which is exact, as before.
//!
//! Rows over one atom besides those an equation defines go to [`line`] instead: each defined
//! atom is an affine image of that atom, its set a progression held as ranges and a class
//! (`Classed`), with no value listed.

use zed_numtheory::{bezout_i128, gcd_u128 as gcd};
use zedc_int::int::{i128_div_ceil, i128_div_floor};
use zedc_lattice::classed::Classed;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::Congruence;

use super::rows::Rows;

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

/// Each wanted atom's set of values over the points of rows of the shape `shape` that have no
/// plan of the join (`Plan::of`: a key past 2^62), where the solver answers otherwise; `None`
/// where a polygon's projection is not shown exact or the enumeration would pass its
/// allowance, a node and a polygon ([`NODE_UNITS`] and [`Shape::leaf_units`]) for each range
/// of each atom of a row and one more for each such atom, so that the solver answers instead.
/// Where the rows have a plan, `Plan::project` runs the polygons after the join's prefix
/// tables, allowed the units those cost; the proof of that bound is there.
// Complexity tradeoff: the join of row sums builds the table of the pairs of values of the two
// atoms, O(m_x·m_y / 64) word steps for ranges of m_x and m_y values, and its work passed
// `JOIN_LIMIT` (a refusal) at m = 512 (FAIL-join-pair-table); the `chain` family of l01_39
// asked one such question per test, k^3 in all. Here: one polygon per range of `x`, range of
// `y` and range of each defined atom that meets the form's values over the box of the first
// two, and each polygon of h half-planes (4 for its box, 1 per inequality, 2 per equation or
// defined atom) costs O(h^2) per wanted atom, the pairs of Fourier-Motzkin elimination; the
// union of the pieces costs O(P log P) for P polygons. Nothing depends on the widths of the
// ranges. The polygons alone can be more than the join's work: with `d == x + y`, `x` and `y`
// each over 64 ranges of one value three apart and `d` over every other value, they visit
// 20,480 nodes where the join spends 15,416 units (`grid(3, 64, 1)` in the tests of
// `row_sums`). So the enumeration is charged in the join's units and stops past its
// allowance; the join, or here the solver, exact, answers then (PROOF-plane-route-bounds).
// With no plan the allowance is the formula's size in nodes, as before
// PERF-plane-allowance-join-bound, a cost every method pays to read the formula.
pub(super) fn project(
    shape: &Shape,
    rows: &Rows,
    want: &[bool],
) -> Option<Vec<Option<IntervalSet>>> {
    let per_range = NODE_UNITS.saturating_add(shape.leaf_units(want));
    let mut left = ranges(rows).saturating_mul(per_range);
    shape.polygons(rows, want, &mut left)
}

/// One more than its number of ranges for each atom of a row.
fn ranges(rows: &Rows) -> u64 {
    let mut used = vec![false; rows.atoms.len()];
    for row in &rows.rows {
        for &(j, _) in &row.terms {
            used[j] = true;
        }
    }
    (rows.domains.iter().zip(used))
        .filter(|(_, u)| *u)
        .map(|(d, _)| d.len() as u64 + 1)
        .sum()
}

/// The units of `Work` charged for a node of the enumeration ([`Shape::polygons`]), and for
/// each half-plane and each pair of a lower and an upper side in each shadow of a leaf
/// ([`Shape::leaf_units`]): their measured time over the join's fastest time per unit, on one
/// build at one load (A96, PERF-plane-shadow-pairs), rounded up. Measured 2026-11-15, debug
/// build, load 41–46, by a probe on `tests::bench::padded` (0 to 128 half-planes more, half
/// lower sides and half upper): the join's prefix tables 5.2 to 6.0 ns per unit (7,544,198
/// units in 40.2 ms; 1,838,557 in 9.5 ms; 31,020,579 in 185.8 ms), and the whole join down to
/// 3.67 ns per unit in another run; a leaf with a point, three shadows, at most 225·h + 18·p
/// ns for h half-planes and p pairs (1,118 ns at h = 6, 3,122 at 14, 15,023 at 38, 110,582 at
/// 134), so 75 ns a half-plane and 6 a pair per shadow; a node at most 162 ns (3.32 ms for
/// 20,480 nodes and 4,096 leaves), taken as 100. Each is charged at 2.5 ns per unit, below
/// the join's fastest. `tests::bench::the_route_and_the_join_on_both_sides_of_the_allowance`
/// prints both times per unit on each run.
// Complexity tradeoff: the alternative PERF-plane-shadow-pairs names, each shadow in
// O(h log h) by sorting the sides by slope, was not taken: h is fixed by the formula (4, one
// per row that defines no atom, two per defined atom), and the charge per pair makes the
// pairs' cost count against the same allowance as the join's own work; at h = 134 the pairs
// are about 70% of a leaf's time.
const NODE_UNITS: u64 = 40;
const HALF_UNITS: u64 = 30;
const PAIR_UNITS: u64 = 3;

/// `units` taken from `left`; `None` where they are not left, with nothing taken.
fn visit(left: &mut u64, units: u64) -> Option<()> {
    *left = left.checked_sub(units)?;
    Some(())
}

/// [`Shape::polygons`] of the rows' shape, `None` where they have none.
#[cfg(test)]
pub(super) fn polygons(
    rows: &Rows,
    want: &[bool],
    left: &mut u64,
) -> Option<Vec<Option<IntervalSet>>> {
    Shape::of(rows)?.polygons(rows, want, left)
}

/// The rows read as polygons over two atoms (module note): each atom's role, the half-planes
/// of the rows that define no atom, and each defined atom's form with its ranges.
pub(super) struct Shape<'a> {
    ax: usize,
    ay: usize,
    roles: Vec<Role>,
    halves: Vec<Half>,
    ranged: Vec<(Form, &'a [(i128, i128)])>,
}

impl<'a> Shape<'a> {
    /// The shape of `rows`; `None` where they are not of the class the module note names.
    pub(super) fn of(rows: &'a Rows) -> Option<Shape<'a>> {
        let n = rows.atoms.len();
        let (defines, axes) = defines_and_axes(rows);
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
        Some(Shape {
            ax,
            ay,
            roles,
            halves,
            ranged,
        })
    }

    /// The units of `Work` charged for a leaf of the enumeration, a polygon whose wanted atoms'
    /// values are found: the shadows [`polygon_pieces`] asks for (the first axis, and each wanted
    /// second axis or defined atom), each of `h` half-planes sorted by side and at most
    /// `⌊h/2⌋·⌈h/2⌉` pairs of a lower and an upper side, for `h` those of the box, the rows that
    /// define no atom and two for each defined atom.
    fn leaf_units(&self, want: &[bool]) -> u64 {
        let h = (self.halves.len() + 4 + 2 * self.ranged.len()) as u64;
        let pairs = (h / 2) * h.div_ceil(2);
        let shadows = 1
            + (want.iter().zip(&self.roles))
                .filter(|(w, r)| **w && matches!(r, Role::Axis(1) | Role::Defined(_)))
                .count() as u64;
        shadows.saturating_mul(HALF_UNITS * h + PAIR_UNITS * pairs)
    }

    /// [`project`] with `left` units of `Work` allowed, those of the enumeration taken from it:
    /// [`NODE_UNITS`] for each node, a box or a range of a defined atom tried in a box, and
    /// [`Shape::leaf_units`] for each polygon projected.
    pub(super) fn polygons(
        &self,
        rows: &Rows,
        want: &[bool],
        left: &mut u64,
    ) -> Option<Vec<Option<IntervalSet>>> {
        let n = rows.atoms.len();
        let (ax, ay, roles) = (self.ax, self.ay, &self.roles[..]);
        let leaf = self.leaf_units(want);
        let mut pieces: Vec<Vec<(End, End)>> = vec![Vec::new(); n];
        let mut any = false;
        // One polygon, the rows' half-planes then the box's and those of each defined atom's
        // range, written over from box to box; and the shadows' lists, cleared for each.
        let mut polygon = self.halves.clone();
        let mut scratch = Scratch::default();
        for &bx in &rows.domains[ax] {
            for &by in &rows.domains[ay] {
                visit(left, NODE_UNITS)?;
                polygon.truncate(self.halves.len());
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
                any |= cases(
                    want,
                    roles,
                    &self.ranged,
                    (bx, by),
                    &mut polygon,
                    &mut pieces,
                    &mut scratch,
                    (left, leaf),
                )?;
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
}

/// The atom each row defines, with its coefficient, and the axes, the atoms of a row that no
/// row defines, in increasing order. Each equation defines its first atom that appears in it
/// alone with coefficient 1 or -1. O(t + n) for t terms and n atoms.
fn defines_and_axes(rows: &Rows) -> (Vec<Option<(usize, i128)>>, Vec<usize>) {
    let n = rows.atoms.len();
    let mut uses = vec![0usize; n];
    for row in &rows.rows {
        for &(j, _) in &row.terms {
            uses[j] += 1;
        }
    }
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
    let axes = (0..n).filter(|&j| uses[j] > 0 && !defined[j]).collect();
    (defines, axes)
}

/// Each wanted atom's set of values over the points of rows over one atom `x` (the axis) and
/// atoms that each appear in one equation alone with coefficient 1 or -1, which defines them
/// (`y == 2·x + 4`); `None` for rows of another shape, or a number past `i128`.
///
/// Exactness, every step. A row that defines `d` is `s·d + a·x + c == 0` with `s` 1 or -1, so
/// at every point `d = g·x + h` with `g = -s·a` and `h = -s·c`; `d` is in no other row. Every
/// other row is `a·x + c >= 0` (or `== 0`), since an atom of a row that no row defines is the
/// axis. So the points are the `(x, (g_d·x + h_d)_d)` with `x` in `X`, the set of `x` in its
/// domain that meet each other row and have `g_d·x + h_d` in `d`'s domain for each `d`; their
/// projection onto `x` is `X` and onto `d` is `{g_d·x + h_d : x ∈ X}`. `X` is met here range by
/// range: `a·x + c >= 0` is `x >= ⌈-c/a⌉` for `a > 0` and `x <= ⌊c/-a⌋` for `a < 0` (an
/// integer is at least a number if and only if at least its ceiling), and every `x` or none for
/// `a == 0`; `g·x + h ∈ [l, u]` is `x ∈ [⌈(l - h)/g⌉, ⌊(u - h)/g⌋]` for `g > 0`, the ends
/// swapped for `g < 0`, and every `x` or none for `g == 0`. The image of a range `[p, q]` of `X`
/// under `g·x + h`, `g != 0`, is the members of class `h` modulo `|g|` in `[g·p + h, g·q + h]`
/// (ends swapped for `g < 0`): each member `v` there is `g·x + h` for `x = (v - h)/g`, an
/// integer between `p` and `q`, and each `g·x + h` is such a member. All ranges of `X` share
/// the one map, so the union of their images is the members of that one class in the union of
/// the image ranges, which [`Classed::new`] holds exactly. An atom of no row takes every value of
/// its domain where `X` is not empty and none where it is.
// Complexity tradeoff: the join of row sums builds the table of `x`'s and `d`'s keys, one bit
// per key over the ranges' widths, O(m / 64) word steps for ranges of m values, and its sets are
// ranges alone, so `d`'s answer `{2x : x ∈ [0, m]}` is m + 1 ranges (`plane` refuses such a
// form for that reason: as many pieces as values). The `families` strided bench of
// l01_39_scope_relations spent 4.0 times the instructions at 8 times m there (callgrind,
// 2026-11-25, LIMITS-classed-listing-per-set: `row_sums::Plan::project` 6.0M to 102.8M). Here:
// O(Σ p log p) for p ranges of the atoms' domains, the meets of sorted range lists and
// `Classed::new` of each image, nothing depending on the ranges' widths.
pub(super) fn line(rows: &Rows, want: &[bool]) -> Option<Vec<Option<Classed>>> {
    let (defines, axes) = defines_and_axes(rows);
    let [ax] = axes[..] else {
        return None;
    };
    let mut xs: Vec<(i128, i128)> = rows.domains[ax].clone();
    // Each defined atom's map `(g, h)`.
    let mut maps: Vec<Option<(i128, i128)>> = vec![None; rows.atoms.len()];
    for (row, def) in rows.rows.iter().zip(&defines) {
        let (mut a, c) = (0i128, row.k);
        for &(j, t) in &row.terms {
            if j == ax {
                a = a.checked_add(t)?;
            }
        }
        let allowed: Vec<(i128, i128)> = match *def {
            Some((d, s)) => {
                let (g, h) = (
                    s.checked_neg()?.checked_mul(a)?,
                    s.checked_neg()?.checked_mul(c)?,
                );
                maps[d] = Some((g, h));
                preimage(&rows.domains[d], g, h)?
            }
            None => {
                let mut r = at_least(a, c)?;
                if row.eq {
                    r = meet(&r, &at_least(a.checked_neg()?, c.checked_neg()?)?);
                }
                r
            }
        };
        xs = meet(&xs, &allowed);
    }
    let set = |r: &[(i128, i128)]| {
        IntervalSet::from_pieces(r.iter().map(|&(l, h)| (fin(l), fin(h))).collect())
    };
    let mut sets = vec![None; rows.atoms.len()];
    for (a, w) in want.iter().enumerate() {
        if !*w {
            continue;
        }
        sets[a] = Some(match maps[a] {
            _ if a == ax => Classed::plain(set(&xs)),
            Some((0, h)) if !xs.is_empty() => Classed::plain(set(&[(h, h)])),
            Some((g, h)) => {
                let mut image = Vec::with_capacity(xs.len());
                for &(p, q) in &xs {
                    let (u, v) = (
                        g.checked_mul(p)?.checked_add(h)?,
                        g.checked_mul(q)?.checked_add(h)?,
                    );
                    image.push((u.min(v), u.max(v)));
                }
                if g < 0 {
                    image.reverse();
                }
                Classed::new(set(&image), Congruence::new(Num::from(g), Num::from(h)))
            }
            None if xs.is_empty() => Classed::plain(IntervalSet::empty()),
            None => Classed::plain(set(&rows.domains[a])),
        });
    }
    Some(sets)
}

/// The `x` with `a·x + c >= 0`, as ranges: at most one.
fn at_least(a: i128, c: i128) -> Option<Vec<(i128, i128)>> {
    Some(match a.signum() {
        0 if c >= 0 => vec![(i128::MIN, i128::MAX)],
        0 => Vec::new(),
        1 => vec![(i128_div_ceil(c.checked_neg()?, a)?, i128::MAX)],
        _ => vec![(i128::MIN, i128_div_floor(c, a.checked_neg()?)?)],
    })
}

/// The `x` with `g·x + h` in `ranges` (sorted, disjoint), as sorted disjoint ranges.
fn preimage(ranges: &[(i128, i128)], g: i128, h: i128) -> Option<Vec<(i128, i128)>> {
    if g == 0 {
        let inside = ranges.iter().any(|&(l, u)| l <= h && h <= u);
        return Some(if inside {
            vec![(i128::MIN, i128::MAX)]
        } else {
            Vec::new()
        });
    }
    let mut out = Vec::with_capacity(ranges.len());
    for &(l, u) in ranges {
        let (l, u) = (l.checked_sub(h)?, u.checked_sub(h)?);
        let (p, q) = if g > 0 {
            (i128_div_ceil(l, g)?, i128_div_floor(u, g)?)
        } else {
            (i128_div_ceil(u, g)?, i128_div_floor(l, g)?)
        };
        if p <= q {
            out.push((p, q));
        }
    }
    if g < 0 {
        out.reverse();
    }
    Some(out)
}

/// The meet of two lists of sorted disjoint ranges, sorted and disjoint: O(p + q).
fn meet(xs: &[(i128, i128)], ys: &[(i128, i128)]) -> Vec<(i128, i128)> {
    let (mut i, mut j, mut out) = (0, 0, Vec::new());
    while i < xs.len() && j < ys.len() {
        let (lo, hi) = (xs[i].0.max(ys[j].0), xs[i].1.min(ys[j].1));
        if lo <= hi {
            out.push((lo, hi));
        }
        if xs[i].1 < ys[j].1 {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

fn fin(v: i128) -> End {
    End::Fin(Num::from(v))
}

/// The polygons of one box: for each defined atom in turn, one for each of its ranges that
/// meets the form's values over the box, each a node of [`NODE_UNITS`] taken from `left`, and
/// each polygon `leaf` units. Adds each wanted atom's values to `pieces`; whether any polygon
/// has a point, or `None` where a projection is not shown exact or the units are not left.
#[allow(clippy::too_many_arguments)]
fn cases(
    want: &[bool],
    roles: &[Role],
    ranged: &[(Form, &[(i128, i128)])],
    bx: ((i128, i128), (i128, i128)),
    polygon: &mut Vec<Half>,
    pieces: &mut [Vec<(End, End)>],
    scratch: &mut Scratch,
    (left, leaf): (&mut u64, u64),
) -> Option<bool> {
    let Some(((g, ranges), rest)) = ranged.split_first() else {
        visit(left, leaf)?;
        return polygon_pieces(want, roles, polygon, pieces, scratch);
    };
    let (lo, hi) = g.hull(bx.0, bx.1)?;
    // The ranges are sorted and disjoint: those that meet `[lo, hi]` are one run.
    let from = ranges.partition_point(|r| r.1 < lo);
    let mut any = false;
    for &(l, h) in ranges[from..].iter().take_while(|r| r.0 <= hi) {
        visit(left, NODE_UNITS)?;
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
        let found = cases(
            want,
            roles,
            rest,
            bx,
            polygon,
            pieces,
            scratch,
            (left, leaf),
        );
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
    scratch: &mut Scratch,
) -> Option<bool> {
    // The first axis's values: empty if and only if the polygon has no integer point.
    let Some(xs) = shadow(polygon, 1, 0, scratch)? else {
        return Some(false);
    };
    for (a, w) in want.iter().enumerate() {
        if !*w {
            continue;
        }
        let (lo, hi) = match roles[a] {
            Role::Axis(0) => xs,
            Role::Axis(_) => shadow(polygon, 0, 1, scratch)??,
            Role::Defined(g) => {
                if g.a == 0 && g.b == 0 {
                    (g.c, g.c)
                } else {
                    // A form with a common factor above 1 takes every g-th value: left to the
                    // join (module note).
                    if gcd(g.a.unsigned_abs(), g.b.unsigned_abs()) != 1 {
                        return None;
                    }
                    let (l, h) = shadow(polygon, g.a, g.b, scratch)??;
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
/// note) or a number passes `i128`. The lists of `scratch` are cleared and written here.
// Complexity tradeoff: O(h^2) for h half-planes, the pairs of Fourier-Motzkin elimination,
// charged in units by `Shape::leaf_units`. Sorting the bounds by slope would find the two
// vertices of the extreme values in O(h log h) (PERF-plane-shadow-pairs), but the exactness
// test of each pair (module note) and the overflow checks of each would then be argued apart;
// h is fixed for a formula (4 + its rows + 2 per defined atom, 7 on the `chain` family), so the
// pairs are a constant of the formula and the charge covers them. The three lists were made
// per shadow, three allocations, about half of a node's time; they are now cleared and reused.
fn shadow(
    polygon: &[Half],
    a: i128,
    b: i128,
    scratch: &mut Scratch,
) -> Option<Option<(i128, i128)>> {
    // `s·a + t·b == 1`; `q = u·x + v·y` with `(u, v) = (-t, s)` completes `p` to a unimodular
    // basis, whose inverse is `x = v·p - b·q`, `y = -u·p + a·q`.
    let (s, t) = bezout(a, b)?;
    let (u, v) = (t.checked_neg()?, s);
    // Each half-plane `A·p + B·q + C >= 0`, put by the sign of `B`.
    let Scratch { free, lower, upper } = scratch;
    free.clear();
    lower.clear();
    upper.clear();
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
    for &(al, bl, cl) in lower.iter() {
        for &(au, bu, cu) in upper.iter() {
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
    for &(pa, pc) in free.iter() {
        match pa.signum() {
            0 if pc < 0 => return Some(None),
            0 => {}
            1 => {
                let l = i128_div_ceil(pc.checked_neg()?, pa)?;
                lo = Some(lo.map_or(l, |v| v.max(l)));
            }
            _ => {
                let h = i128_div_floor(pc, pa.checked_neg()?)?;
                hi = Some(hi.map_or(h, |v| v.min(h)));
            }
        }
    }
    // The box bounds the polygon, so both ends are found (module note); else the join answers.
    let (lo, hi) = (lo?, hi?);
    Some((lo <= hi).then_some((lo, hi)))
}

/// The lists [`shadow`] writes, kept from one shadow to the next: the half-planes free of the
/// eliminated coordinate and the conditions of the pairs, and the lower and upper bounds.
#[derive(Default)]
struct Scratch {
    free: Vec<(i128, i128)>,
    lower: Vec<(i128, i128, i128)>,
    upper: Vec<(i128, i128, i128)>,
}

/// `(s, t)` with `s·a + t·b == 1`, for `a` and `b` coprime ([`bezout_i128`], whose cofactors
/// equal those of the signed Euclid this module used before; checked by
/// `bezout_cofactors_give_the_gcd_and_are_the_least` in zed-numtheory).
pub(in crate::presburger) fn bezout(a: i128, b: i128) -> Option<(i128, i128)> {
    let (g, s, t) = bezout_i128(a, b)?;
    (g == 1).then_some((s, t))
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
    /// atom of no row, each atom over up to three ranges: wherever the polygons answer, with no
    /// allowance, each set is that of the points, and so wherever `project` (the allowance of
    /// rows with no plan) answers, whose answers are those within its allowance. The counts are
    /// printed, not asserted, since they depend on the draws (PROOF-plane-route-bounds): at this
    /// seed the polygons answer 2,962 of 6,000, 1,666 of those with no point and 349 with a defined
    /// atom and a point, and decline the rest (a pair `2·y >= ..`, `-3·y >= ..`; a defined atom
    /// `2·x + 2·y`; an atom defined by an equation over `x` alone); `project` answers the share of
    /// those its allowance holds, printed as `route`.
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
        let (mut route, mut route_defined) = (0, 0);
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
            let all = polygons(&rows, &want, &mut { u64::MAX });
            match &all {
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
            // Within the allowance of rows with no plan, the answer is the one above or none.
            let shape = Shape::of(&rows);
            if let Some(sets) = shape.and_then(|s| project(&s, &rows, &want)) {
                assert_eq!(Some(sets), all, "case {case}");
                route += 1;
                route_defined += usize::from(n_def > 0);
            }
        }
        eprintln!(
            "polygons answered {answered} of 6000 ({empty} with no point, {defined} with a \
             defined atom and a point), declined {declined}; route {route} ({route_defined} \
             with a defined atom)"
        );
    }

    /// The question of each test of the `chain` family of l01_39 (`x + c·y >= 1` or
    /// `y - x >= c`, with `a == x + y`) is answered here, at every width: its eliminations all
    /// have a side of coefficient 1. With no allowance: whether `row_sums::project` takes them
    /// is the allowance's matter (`Plan::project`).
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
                let sets = polygons(&rows, &[true; 3], &mut { u64::MAX }).expect("answered");
                assert!(
                    sets.iter()
                        .all(|s| s.as_ref().is_some_and(|s| s.len() <= 2))
                );
            }
        }
    }

    /// Random rows over one atom `x` (atom 0), up to two atoms an equation defines over it
    /// (`d == g·x + h`, `g` in `[-3, 3]`, so most images are progressions) and one atom of no
    /// row, each over up to three ranges: each set [`line`] gives, listed, is that of the
    /// points, found by trying every value of `x`. Rows over two axes are declined.
    #[test]
    fn line_projections_are_those_of_the_points() {
        let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
        let mut next = move |n: u64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (seed >> 33) % n
        };
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
        let (mut nonempty, mut strided) = (0, 0);
        for case in 0..4000 {
            let n_def = 1 + (case % 2) as usize;
            let alone = case % 5 == 0;
            let n = 1 + n_def + usize::from(alone);
            let domains: Vec<_> = (0..n)
                .map(|j| ranges(if j == 0 { 12 } else { 40 }, &mut next))
                .collect();
            let mut rows_v = Vec::new();
            for _ in 0..next(3) {
                rows_v.push(Row {
                    terms: vec![(0, next(7) as i128 - 3)],
                    k: next(13) as i128 - 6,
                    eq: next(6) == 0,
                });
            }
            let mut maps = Vec::new();
            for d in 0..n_def {
                let (a, s) = (next(7) as i128 - 3, if next(2) == 0 { 1 } else { -1 });
                let k = next(11) as i128 - 5;
                rows_v.push(Row {
                    terms: vec![(0, a), (1 + d, s)],
                    k,
                    eq: true,
                });
                maps.push((-s * a, -s * k));
            }
            let rows = Rows {
                atoms: (0..n).map(|i| Atom::Sym(format!("a{i}").into())).collect(),
                domains,
                rows: rows_v,
                empty: false,
            };
            let inside = |j: usize, v: i128| rows.domains[j].iter().any(|&(l, h)| l <= v && v <= h);
            let mut each = vec![std::collections::BTreeSet::new(); n];
            for x in rows.domains[0].iter().flat_map(|&(l, h)| l..=h) {
                let ds: Vec<i128> = maps.iter().map(|&(g, h)| g * x + h).collect();
                let fits = ds.iter().enumerate().all(|(d, &v)| inside(1 + d, v))
                    && rows.rows[..rows.rows.len() - n_def].iter().all(|r| {
                        let v = r.k + r.terms[0].1 * x;
                        if r.eq { v == 0 } else { v >= 0 }
                    });
                if fits {
                    each[0].insert(x);
                    for (d, v) in ds.into_iter().enumerate() {
                        each[1 + d].insert(v);
                    }
                    if alone {
                        each[n - 1].extend(rows.domains[n - 1].iter().flat_map(|&(l, h)| l..=h));
                    }
                }
            }
            let sets = line(&rows, &vec![true; n]).expect("one axis");
            for (a, (got, w)) in sets.iter().zip(&each).enumerate() {
                let got = got.as_ref().expect("wanted");
                strided += usize::from(got.strided().is_some());
                let w: Vec<i128> = w.iter().copied().collect();
                assert_eq!(values(&got.met()), w, "case {case}, atom {a}");
            }
            nonempty += usize::from(!each[0].is_empty());
        }
        assert!(
            nonempty > 1000 && strided > 500,
            "{nonempty} with a point, {strided} strided"
        );
        // Two axes: not of the class.
        let two = Rows {
            atoms: (0..2).map(|i| Atom::Sym(format!("a{i}").into())).collect(),
            domains: vec![vec![(0, 9)], vec![(0, 9)]],
            rows: vec![Row {
                terms: vec![(0, 1), (1, -2)],
                k: 0,
                eq: false,
            }],
            empty: false,
        };
        assert!(line(&two, &[true, true]).is_none());
    }
}
