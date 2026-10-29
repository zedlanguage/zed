//! The tonicity table, the interval-revision (HC4) table and the reductions between domains
//! (DESIGN.md sec:domains and sec:constraints; written by step M0.5).
//!
//! Forward transfer of an operator over intervals is computed from its tonicity: each operand
//! is split at zero into parts of one sign, on which the operator is monotone or antitone in
//! each argument, and the image of a box of such parts is the interval between two of its
//! corners. Backward transfer, the projection onto an operand of a demand on the result, is
//! one entry per operator and operand. Interval revision runs these two over a constraint's
//! tree, one pass up and one down (sec:constraints).
//!
//! The source of these tables is `zed/prelude/revision.zed`; this module is the Rust-hosted
//! checker's copy.

use std::cmp::Ordering;
use std::ops::Neg;

use super::interval::{End, IntervalSet};
use super::lattice::{Congruence, FiniteSet, Lattice};
use End::{Fin, NegInf, PosInf};

/// An integer operator of the revision table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    /// `x + y`.
    Add,
    /// `x - y`.
    Sub,
    /// `-x`.
    Neg,
    /// `x * y`.
    Mul,
    /// `x ** k` for a constant `k`.
    Pow(u32),
    /// `x div y`, Euclidean: the remainder is in `0..abs(y)`.
    Div,
    /// `x mod y`, Euclidean.
    Mod,
    /// `abs(x)`.
    Abs,
    /// `min(x, y)`.
    Min,
    /// `max(x, y)`.
    Max,
}

/// How an operator's result moves with one argument, the others fixed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Tonicity {
    /// Monotone: ↑.
    Up,
    /// Antitone: ↓.
    Down,
    /// Constant.
    Const,
    /// ↑ where the other argument is at least 0, ↓ where it is at most 0.
    UpWhereOtherNonneg,
    /// ↓ where the other argument is at least 0, ↑ where it is below 0.
    DownWhereOtherNonneg,
    /// ↓ where this argument is at most 0, ↑ where it is at least 0.
    DownThenUp,
    /// Neither, on any part of one sign: the operator has its own forward entry.
    None,
}

/// The tonicity table: the entry of operator `op` in argument `arg` (0 or 1).
pub fn tonicity(op: Op, arg: usize) -> Tonicity {
    use Tonicity::*;
    match (op, arg) {
        (Op::Add, _) | (Op::Min, _) | (Op::Max, _) => Up,
        (Op::Sub, 0) => Up,
        (Op::Sub, _) | (Op::Neg, _) => Down,
        (Op::Mul, _) => UpWhereOtherNonneg,
        (Op::Pow(0), _) => Const,
        (Op::Pow(k), _) if k % 2 == 1 => Up,
        (Op::Pow(_), _) | (Op::Abs, _) => DownThenUp,
        // Euclidean `x div y` rises with x where y > 0 and falls where y < 0; in y it falls
        // where x >= 0 and rises where x < 0, on either side of y = 0.
        (Op::Div, 0) => UpWhereOtherNonneg,
        (Op::Div, _) => DownWhereOtherNonneg,
        (Op::Mod, _) => None,
    }
}

/// The number of arguments.
pub fn arity(op: Op) -> usize {
    match op {
        Op::Neg | Op::Pow(_) | Op::Abs => 1,
        _ => 2,
    }
}

/// The direction an endpoint is rounded in: down for a lower bound, up for an upper one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dir {
    Down,
    Up,
}

/// `op` at two endpoints, rounded outward in `dir` where the result is not an integer or not
/// defined by a limit, such as `inf - inf`.
fn at(op: Op, a: End, b: End, dir: Dir) -> End {
    let outward = if dir == Dir::Down { NegInf } else { PosInf };
    let inf = |sign: i8| match sign.cmp(&0) {
        Ordering::Less => NegInf,
        Ordering::Greater => PosInf,
        Ordering::Equal => Fin(0),
    };
    match (op, a, b) {
        (Op::Add, Fin(x), Fin(y)) => End::from_i128(x as i128 + y as i128),
        (Op::Add, NegInf, PosInf) | (Op::Add, PosInf, NegInf) => outward,
        (Op::Add, Fin(_), e) | (Op::Add, e, _) => e,
        (Op::Sub, _, _) => at(Op::Add, a, b.neg(), dir),
        (Op::Neg, _, _) => a.neg(),
        (Op::Mul, Fin(x), Fin(y)) => End::from_i128(x as i128 * y as i128),
        // 0 times an unbounded operand: every product with a finite member is 0.
        (Op::Mul, _, _) => inf(a.signum() * b.signum()),
        (Op::Pow(k), Fin(x), _) => (x as i128)
            .checked_pow(k)
            .map(End::from_i128)
            .unwrap_or(inf(if k % 2 == 0 { 1 } else { x.signum() as i8 })),
        (Op::Pow(0), _, _) => Fin(1),
        (Op::Pow(k), e, _) => {
            if k % 2 == 0 {
                PosInf
            } else {
                e
            }
        }
        (Op::Abs, _, _) => {
            if a.signum() < 0 {
                a.neg()
            } else {
                a
            }
        }
        (Op::Min, _, _) => a.min(b),
        (Op::Max, _, _) => a.max(b),
        (Op::Div, Fin(x), Fin(y)) if y != 0 => Fin(x.div_euclid(y)),
        // A finite numerator over an unbounded divisor: the limit of the Euclidean quotient.
        (Op::Div, Fin(x), _) if b != Fin(0) => match (x >= 0, b.signum() > 0) {
            (true, _) => Fin(0),
            (false, true) => Fin(-1),
            (false, false) => Fin(1),
        },
        (Op::Div, _, Fin(y)) if y != 0 => inf(a.signum() * y.signum() as i8),
        _ => outward,
    }
}

/// The image of the box of two pieces, each of one sign, under an operator monotone or
/// antitone in each argument there: the interval between two corners.
fn corners(op: Op, a: (End, End), b: (End, End)) -> (End, End) {
    let dir = |arg: usize, own: (End, End), other: (End, End)| -> Tonicity {
        let nonneg = |p: (End, End)| p.0 >= Fin(0);
        match tonicity(op, arg) {
            Tonicity::UpWhereOtherNonneg if nonneg(other) => Tonicity::Up,
            Tonicity::UpWhereOtherNonneg => Tonicity::Down,
            Tonicity::DownWhereOtherNonneg if nonneg(other) => Tonicity::Down,
            Tonicity::DownWhereOtherNonneg => Tonicity::Up,
            Tonicity::DownThenUp if nonneg(own) => Tonicity::Up,
            Tonicity::DownThenUp => Tonicity::Down,
            t => t,
        }
    };
    // The endpoint of a piece where the result is least, and where it is greatest.
    let pick = |t: Tonicity, p: (End, End)| match t {
        Tonicity::Down => (p.1, p.0),
        _ => (p.0, p.1),
    };
    let (alo, ahi) = pick(dir(0, a, b), a);
    let (blo, bhi) = if arity(op) == 2 {
        pick(dir(1, b, a), b)
    } else {
        (Fin(0), Fin(0))
    };
    (at(op, alo, blo, Dir::Down), at(op, ahi, bhi, Dir::Up))
}

/// Forward transfer: an interval containing `op` of every choice of members of the operands.
/// For every operator but `mod`, the hull of the result is the hull of the exact image when
/// each operand is one interval.
pub fn forward(op: Op, x: &IntervalSet, y: &IntervalSet) -> IntervalSet {
    let (xs, ys) = (x.sign_parts(), y.sign_parts());
    let one = [(Fin(0), Fin(0))];
    match op {
        Op::Mod => map2(&xs, y.pieces(), forward_mod),
        Op::Div => {
            let nonzero = IntervalSet::single(0).complement_in(y).sign_parts();
            map2(&xs, &nonzero, |a, b| vec![corners(op, a, b)])
        }
        _ if arity(op) == 1 => map2(&xs, &one, |a, b| vec![corners(op, a, b)]),
        _ => map2(&xs, &ys, |a, b| vec![corners(op, a, b)]),
    }
}

/// `x mod y` for one piece of each: `0..abs(y)`, or the piece of `x` itself shifted when one
/// constant divisor maps it without wrapping.
fn forward_mod(a: (End, End), b: (End, End)) -> Vec<(End, End)> {
    if b == (Fin(0), Fin(0)) {
        return Vec::new();
    }
    if let (Fin(lo), Fin(hi), Fin(c)) = (a.0, a.1, b.0)
        && b.0 == b.1
        && (hi as i128 - lo as i128) < c.unsigned_abs() as i128
        && lo.rem_euclid(c) <= hi.rem_euclid(c)
    {
        return vec![(Fin(lo.rem_euclid(c)), Fin(hi.rem_euclid(c)))];
    }
    // The remainder is below the largest abs(y), and for x >= 0 at most x.
    let top = match b.0.neg().max(b.1) {
        Fin(m) => Fin(m - 1),
        e => e,
    };
    let top = if a.0 >= Fin(0) { top.min(a.1) } else { top };
    vec![(Fin(0), top)]
}

impl IntervalSet {
    /// The members of `within` that are not members of `self`.
    pub fn complement_in(&self, within: &IntervalSet) -> IntervalSet {
        let mut gaps = Vec::new();
        let mut from = NegInf;
        for &(lo, hi) in self.pieces() {
            if from == NegInf || from <= lo {
                gaps.push((from, lo.pred()));
            }
            from = hi.succ();
        }
        if self.pieces().last().is_none_or(|p| p.1 != PosInf) {
            gaps.push((from, PosInf));
        }
        IntervalSet::from_pieces(gaps).meet(within)
    }
}

/// The image of each pair of parts under `f`, joined.
fn map2(
    a: &[(End, End)],
    b: &[(End, End)],
    f: impl Fn((End, End), (End, End)) -> Vec<(End, End)>,
) -> IntervalSet {
    IntervalSet::from_pieces(
        a.iter()
            .flat_map(|&p| b.iter().flat_map(|&q| f(p, q)).collect::<Vec<_>>())
            .collect(),
    )
}

/// The real quotient `z / y` at two endpoints, rounded outward in `dir`.
fn quotient(z: End, y: End, dir: Dir) -> End {
    match (z, y) {
        (Fin(n), Fin(d)) if d != 0 => {
            let (q, r) = (n.div_euclid(d), n.rem_euclid(d));
            // Euclidean division rounds toward -inf for d > 0 and toward +inf for d < 0.
            let floor = if r != 0 && d < 0 { q - 1 } else { q };
            let exact = r == 0;
            match dir {
                Dir::Down => Fin(floor),
                Dir::Up => Fin(if exact { floor } else { floor + 1 }),
            }
        }
        (Fin(_), _) if y != Fin(0) => Fin(0),
        (_, Fin(d)) if d != 0 => {
            if z.signum() * d.signum() as i8 > 0 {
                PosInf
            } else {
                NegInf
            }
        }
        _ => {
            if dir == Dir::Down {
                NegInf
            } else {
                PosInf
            }
        }
    }
}

/// Backward transfer: the members of operand `arg` (0 or 1) of `op` that can give a result in
/// `z` with the other operand in its interval. The result is contained in the operand's
/// interval, and contains every member that can give a result in `z`.
pub fn backward(
    op: Op,
    arg: usize,
    x: &IntervalSet,
    y: &IntervalSet,
    z: &IntervalSet,
) -> IntervalSet {
    let own = if arg == 0 { x } else { y };
    let other = if arg == 0 { y } else { x };
    let narrowed = match (op, arg) {
        (Op::Add, _) => forward(Op::Sub, z, other),
        (Op::Sub, 0) => forward(Op::Add, z, y),
        (Op::Sub, _) => forward(Op::Sub, x, z),
        (Op::Neg, _) => z.neg(),
        (Op::Mul, _) => {
            if z.contains(0) && other.contains(0) {
                IntervalSet::top()
            } else {
                let nonzero = IntervalSet::single(0).complement_in(other).sign_parts();
                map2(&z.sign_parts(), &nonzero, |zp, yp| {
                    let corner = |zz: End, yy: End, d| quotient(zz, yy, d);
                    // z / y over a box of one sign in each: monotone in each argument, so
                    // its extremes are among the four corners.
                    let qs = [(zp.0, yp.0), (zp.0, yp.1), (zp.1, yp.0), (zp.1, yp.1)];
                    let lo = qs
                        .iter()
                        .map(|&(a, b)| corner(a, b, Dir::Down))
                        .min()
                        .unwrap();
                    let hi = qs
                        .iter()
                        .map(|&(a, b)| corner(a, b, Dir::Up))
                        .max()
                        .unwrap();
                    vec![(lo, hi)]
                })
            }
        }
        (Op::Pow(0), _) => IntervalSet::top(),
        (Op::Pow(k), _) => z.lift1(|(lo, hi)| roots(k, lo, hi)),
        (Op::Abs, _) => z.lift1(|(lo, hi)| {
            let lo = lo.max(Fin(0));
            vec![(hi.neg(), lo.neg()), (lo, hi)]
        }),
        (Op::Min, _) => match (z.bounds(), other.bounds()) {
            (Some((_, zhi)), Some((olo, _))) if olo > zhi => z.clone(),
            (Some((zlo, _)), _) => IntervalSet::range(zlo, PosInf),
            (None, _) => IntervalSet::empty(),
        },
        (Op::Max, _) => match (z.bounds(), other.bounds()) {
            (Some((zlo, _)), Some((_, ohi))) if ohi < zlo => z.clone(),
            (Some((_, zhi)), _) => IntervalSet::range(NegInf, zhi),
            (None, _) => IntervalSet::empty(),
        },
        // x = q * y + r with q in z and r in 0..abs(y).
        (Op::Div, 0) => {
            let largest = forward(Op::Abs, y, y).bounds().map_or(Fin(0), |b| b.1);
            let rest = IntervalSet::range(Fin(0), largest.pred());
            forward(Op::Add, &forward(Op::Mul, z, y), &rest)
        }
        // A remainder r needs abs(y) > r.
        (Op::Mod, 1) => match z.bounds() {
            Some((Fin(r), _)) if r >= 0 => IntervalSet::from_pieces(vec![
                (NegInf, End::from_i128(-(r as i128) - 1)),
                (End::from_i128(r as i128 + 1), PosInf),
            ]),
            Some(_) => IntervalSet::top(),
            None => IntervalSet::empty(),
        },
        (Op::Div, _) | (Op::Mod, _) => IntervalSet::top(),
    };
    own.meet(&narrowed)
}

/// The members of `x` with `x ** k` in `lo..=hi`, for `k >= 1`, as at most two pieces.
fn roots(k: u32, lo: End, hi: End) -> Vec<(End, End)> {
    // The largest r >= 0 with r ** k <= v, for v >= 0.
    let floor_root = |v: End| -> End {
        let Fin(v) = v else { return PosInf };
        let (mut a, mut b) = (0i128, (v as i128).max(1) + 1);
        while b - a > 1 {
            let m = (a + b) / 2;
            match m.checked_pow(k) {
                Some(p) if p <= v as i128 => a = m,
                _ => b = m,
            }
        }
        Fin(a as i64)
    };
    // The least r >= 0 with r ** k >= v, for v >= 0.
    let ceil_root = |v: End| -> End {
        match floor_root(v) {
            Fin(r)
                if (r as i128).pow(k)
                    == match v {
                        Fin(v) => v as i128,
                        _ => 0,
                    } =>
            {
                Fin(r)
            }
            Fin(r) => Fin(r + 1),
            e => e,
        }
    };
    if k % 2 == 1 {
        // Odd powers are increasing, and odd about 0.
        let up = |v: End| {
            if v >= Fin(0) {
                floor_root(v)
            } else {
                ceil_root(v.neg()).neg()
            }
        };
        let down = |v: End| {
            if v >= Fin(0) {
                ceil_root(v)
            } else {
                floor_root(v.neg()).neg()
            }
        };
        return vec![(down(lo), up(hi))];
    }
    if hi < Fin(0) {
        return Vec::new();
    }
    let (r_lo, r_hi) = (ceil_root(lo.max(Fin(0))), floor_root(hi));
    vec![(r_hi.neg(), r_lo.neg()), (r_lo, r_hi)]
}

/// The reduction between an interval and a congruence (sec:constraints): each piece's
/// endpoints move inward to the nearest members of the class, and a single value fixes the
/// other domain.
pub fn reduce_congruence(x: &IntervalSet, c: &Congruence) -> (IntervalSet, Congruence) {
    let Congruence::Class { modulus, residue } = *c else {
        return (IntervalSet::empty(), Congruence::Bottom);
    };
    let x = match modulus {
        0 => x.meet(&IntervalSet::single(residue)),
        1 => x.clone(),
        m => x.lift1(|(lo, hi)| {
            let m = m as i128;
            let up = |e: End| match e {
                Fin(v) => End::from_i128(v as i128 + (residue as i128 - v as i128).rem_euclid(m)),
                e => e,
            };
            let down = |e: End| match e {
                Fin(v) => End::from_i128(v as i128 - (v as i128 - residue as i128).rem_euclid(m)),
                e => e,
            };
            vec![(up(lo), down(hi))]
        }),
    };
    let c = match x.bounds() {
        None => Congruence::Bottom,
        Some((Fin(a), Fin(b))) if a == b => c.meet(&Congruence::single(a)),
        Some(_) => *c,
    };
    (x, c)
}

/// The reduction between an interval and a finite set of integers: each is met with the
/// other.
pub fn reduce_finite(x: &IntervalSet, s: &FiniteSet<i64>) -> (IntervalSet, FiniteSet<i64>) {
    match s {
        FiniteSet::Top => (x.clone(), FiniteSet::Top),
        FiniteSet::Set(vs) => {
            let kept: FiniteSet<i64> = FiniteSet::of(vs.iter().copied().filter(|&v| x.contains(v)));
            let FiniteSet::Set(k) = &kept else {
                unreachable!()
            };
            let points = IntervalSet::from_pieces(k.iter().map(|&v| (Fin(v), Fin(v))).collect());
            (x.meet(&points), kept)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const WINDOW: std::ops::RangeInclusive<i64> = -12..=12;

    /// Every interval with endpoints in -4..=4 or infinite, and some unions.
    fn operands() -> Vec<IntervalSet> {
        let ends: Vec<End> = std::iter::once(NegInf)
            .chain((-4..=4).map(Fin))
            .chain(std::iter::once(PosInf))
            .collect();
        let mut out = vec![IntervalSet::empty()];
        for &lo in &ends {
            for &hi in &ends {
                if lo <= hi && lo != PosInf && hi != NegInf {
                    out.push(IntervalSet::range(lo, hi));
                }
            }
        }
        out.push(IntervalSet::of(-4, -2).join(&IntervalSet::of(2, 3)));
        out.push(
            IntervalSet::single(-3)
                .join(&IntervalSet::single(0))
                .join(&IntervalSet::single(4)),
        );
        out
    }

    /// The members of `s` in the test window, which every finite endpoint of `operands` lies
    /// well inside.
    fn members(s: &IntervalSet) -> Vec<i64> {
        WINDOW.filter(|&v| s.contains(v)).collect()
    }

    fn apply(op: Op, x: i64, y: i64) -> Option<i64> {
        match op {
            Op::Add => Some(x + y),
            Op::Sub => Some(x - y),
            Op::Neg => Some(-x),
            Op::Mul => Some(x * y),
            Op::Pow(k) => Some(x.pow(k)),
            Op::Div => (y != 0).then(|| x.div_euclid(y)),
            Op::Mod => (y != 0).then(|| x.rem_euclid(y)),
            Op::Abs => Some(x.abs()),
            Op::Min => Some(x.min(y)),
            Op::Max => Some(x.max(y)),
        }
    }

    const OPS: [Op; 12] = [
        Op::Add,
        Op::Sub,
        Op::Neg,
        Op::Mul,
        Op::Pow(0),
        Op::Pow(2),
        Op::Pow(3),
        Op::Div,
        Op::Mod,
        Op::Abs,
        Op::Min,
        Op::Max,
    ];

    #[test]
    fn forward_transfer_contains_every_result_in_the_window() {
        for op in OPS {
            for x in operands() {
                for y in operands() {
                    let f = forward(op, &x, &y);
                    let ys = if arity(op) == 1 { vec![0] } else { members(&y) };
                    for a in members(&x) {
                        for &b in &ys {
                            if let Some(r) = apply(op, a, b) {
                                assert!(
                                    f.contains(r),
                                    "{op:?} {x} {y}: {a}, {b} -> {r} not in {f}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn forward_transfer_is_exact_on_finite_intervals_except_mod() {
        // On operands of one finite piece, the result's hull is the hull of the image.
        for op in OPS.into_iter().filter(|&op| op != Op::Mod) {
            for x in operands().into_iter().filter(finite_piece) {
                for y in operands().into_iter().filter(finite_piece) {
                    let ys = if arity(op) == 1 { vec![0] } else { members(&y) };
                    let image: Vec<i64> = members(&x)
                        .into_iter()
                        .flat_map(|a| ys.iter().filter_map(move |&b| apply(op, a, b)))
                        .collect();
                    let want = match (image.iter().min(), image.iter().max()) {
                        (Some(&lo), Some(&hi)) => IntervalSet::of(lo, hi),
                        _ => IntervalSet::empty(),
                    };
                    assert_eq!(forward(op, &x, &y).hull(), want, "{op:?} {x} {y}");
                }
            }
        }
    }

    fn finite_piece(s: &IntervalSet) -> bool {
        matches!(s.pieces(), [(Fin(_), Fin(_))])
    }

    #[test]
    fn backward_transfer_keeps_every_operand_that_can_give_the_result() {
        let zs = operands();
        for op in OPS {
            for arg in 0..arity(op) {
                for x in operands() {
                    for y in operands().into_iter().step_by(3) {
                        for z in zs.iter().step_by(2) {
                            let got = backward(op, arg, &x, &y, z);
                            assert!(got.is_subset(if arg == 0 { &x } else { &y }));
                            let ys = if arity(op) == 1 { vec![0] } else { members(&y) };
                            for a in members(&x) {
                                for &b in &ys {
                                    let Some(r) = apply(op, a, b) else { continue };
                                    let kept = if arg == 0 { a } else { b };
                                    if z.contains(r) && !got.contains(kept) {
                                        panic!(
                                            "{op:?} arg {arg}: x {x} y {y} z {z}: {a}, {b} -> {r} lost from {got}"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn a_product_with_a_possible_zero_gives_no_bound() {
        // Projected onto an operand, a product of independent operands gives no bound when
        // both the other operand and the result may be 0 (sec:constraints).
        let z = IntervalSet::of(0, 10);
        let x = IntervalSet::top();
        assert_eq!(backward(Op::Mul, 0, &x, &IntervalSet::of(0, 3), &z), x);
        assert_eq!(
            backward(Op::Mul, 0, &x, &IntervalSet::of(1, 3), &z),
            IntervalSet::of(0, 10)
        );
    }

    #[test]
    fn the_reductions_keep_every_common_member_and_tighten_the_endpoints() {
        // The interval keeps every member of both and loses only members outside the class;
        // each finite endpoint of the result is a member of the class. An interval cannot
        // hold the intersection exactly: [..=-4] with 0 mod 2 keeps -5.
        for x in operands() {
            for m in 0..=5u64 {
                for r in -2..=4 {
                    let c = Congruence::new(m, r);
                    let (x2, c2) = reduce_congruence(&x, &c);
                    assert!(x2.is_subset(&x), "{x} {c:?}");
                    for v in WINDOW {
                        if x.contains(v) && c.contains(v) {
                            assert!(x2.contains(v) && c2.contains(v), "{x} {c:?} lost {v}");
                        }
                    }
                    for &(lo, hi) in x2.pieces() {
                        for e in [lo, hi] {
                            if let Fin(v) = e {
                                assert!(c.contains(v), "{x} {c:?}: endpoint {v} of {x2}");
                            }
                        }
                    }
                }
            }
            let s = FiniteSet::of([-3, 0, 1, 7]);
            let (x2, s2) = reduce_finite(&x, &s);
            let FiniteSet::Set(kept) = s2 else { panic!() };
            assert_eq!(members(&x2), kept.into_iter().collect::<Vec<_>>());
        }
        let (x, _) =
            reduce_congruence(&IntervalSet::range(NegInf, Fin(-4)), &Congruence::new(3, 1));
        assert_eq!(x, IntervalSet::range(NegInf, Fin(-5)));
    }
}
