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

use super::interval::{End, IntervalSet, Num, cap_pieces, normal_pieces, split_signs};
use super::lattice::{Congruence, FiniteSet, Lattice};
use End::{Fin, NegInf, PosInf};
use zedc_int::int::Int;

/// An integer operator of the revision table.
#[derive(Clone, Debug)]
pub enum Op {
    /// `x + y`.
    Add,
    /// `x - y`.
    Sub,
    /// `-x`.
    Neg,
    /// `x * y`.
    Mul,
    /// `x ^ k` for a constant `k >= 0` of any size, held exactly. Every entry reads whether
    /// `k` is 0 and its parity in O(1) time; an endpoint is exact for every `k` that is not
    /// kept, and bounded outward otherwise (`pow_end`).
    Pow(Exponent),
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

/// The constant exponent `k >= 0` of `x ^ k`, of any size, held exactly.
#[derive(Clone, Debug)]
pub enum Exponent {
    /// A constant of any size, or the number of factors of a product of one value (S30),
    /// which has `d` bits for a squaring name nested `d` deep. A kernel integer past the
    /// 64-bit range is kept as the kernel holds it, prime powers unbuilt: `10 ^ 10 ^ 9` is
    /// two kept powers, where it is 3.3·10^9 bits built.
    Num(Num),
}

impl Exponent {
    /// Whether `k` is 0.
    pub fn is_zero(&self) -> bool {
        self.num().is_zero()
    }

    /// Whether `k` is odd, in O(1) time for a value that is not kept.
    pub fn is_odd(&self) -> bool {
        self.num().is_odd()
    }

    /// `k` when it fits in `u32`.
    pub fn to_u32(&self) -> Option<u32> {
        u32::try_from(self.num().to_i64()?).ok()
    }

    /// `k`.
    pub fn num(&self) -> &Num {
        match self {
            Exponent::Num(k) => k,
        }
    }
}

impl From<Num> for Exponent {
    fn from(k: Num) -> Exponent {
        Exponent::Num(k)
    }
}

impl From<Int> for Exponent {
    fn from(k: Int) -> Exponent {
        Exponent::Num(Num::from(&k))
    }
}

impl From<u32> for Exponent {
    fn from(k: u32) -> Exponent {
        Exponent::Num(Num::from(i64::from(k)))
    }
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
pub fn tonicity(op: &Op, arg: usize) -> Tonicity {
    use Tonicity::*;
    match (op, arg) {
        (Op::Add, _) | (Op::Min, _) | (Op::Max, _) => Up,
        (Op::Sub, 0) => Up,
        (Op::Sub, _) | (Op::Neg, _) => Down,
        (Op::Mul, _) => UpWhereOtherNonneg,
        (Op::Pow(k), _) if k.is_zero() => Const,
        (Op::Pow(k), _) if k.is_odd() => Up,
        (Op::Pow(_), _) | (Op::Abs, _) => DownThenUp,
        // Euclidean `x div y` rises with x where y > 0 and falls where y < 0; in y it falls
        // where x >= 0 and rises where x < 0, on either side of y = 0.
        (Op::Div, 0) => UpWhereOtherNonneg,
        (Op::Div, _) => DownWhereOtherNonneg,
        (Op::Mod, _) => None,
    }
}

/// The number of arguments.
pub fn arity(op: &Op) -> usize {
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

/// `op` at two endpoints, rounded outward in `dir` where the result is not defined by a
/// limit, such as `inf - inf`. Finite results are exact at any magnitude.
fn at(op: &Op, a: &End, b: &End, dir: Dir) -> End {
    let outward = if dir == Dir::Down { NegInf } else { PosInf };
    let inf = |sign: i8| match sign.cmp(&0) {
        Ordering::Less => NegInf,
        Ordering::Greater => PosInf,
        Ordering::Equal => End::of(0),
    };
    match (op, a, b) {
        (Op::Add, Fin(x), Fin(y)) => Fin(x + y),
        (Op::Add, NegInf, PosInf) | (Op::Add, PosInf, NegInf) => outward,
        (Op::Add, Fin(_), e) | (Op::Add, e, _) => e.clone(),
        (Op::Sub, Fin(x), Fin(y)) => Fin(x - y),
        (Op::Sub, _, _) => at(&Op::Add, a, &-b, dir),
        (Op::Neg, _, _) => -a,
        (Op::Mul, Fin(x), Fin(y)) => Fin(x * y),
        // 0 times an unbounded operand: every product with a finite member is 0.
        (Op::Mul, _, _) => inf(a.signum() * b.signum()),
        (Op::Pow(k), Fin(x), _) => pow_end(x, k, dir),
        (Op::Pow(k), _, _) if k.is_zero() => End::of(1),
        (Op::Pow(k), e, _) => {
            if k.is_odd() {
                e.clone()
            } else {
                PosInf
            }
        }
        (Op::Abs, Fin(x), _) => Fin(x.abs()),
        (Op::Abs, _, _) => {
            if a.signum() < 0 {
                -a
            } else {
                a.clone()
            }
        }
        (Op::Min, _, _) => a.min(b).clone(),
        (Op::Max, _, _) => a.max(b).clone(),
        (Op::Div, Fin(x), Fin(y)) if !y.is_zero() => Fin(x.div_euclid(y)),
        // A finite numerator over an unbounded divisor: the limit of the Euclidean quotient.
        (Op::Div, Fin(x), _) if b.signum() != 0 => match (x.signum() >= 0, b.signum() > 0) {
            (true, _) => End::of(0),
            (false, true) => End::of(-1),
            (false, false) => End::of(1),
        },
        (Op::Div, _, Fin(y)) if !y.is_zero() => inf(a.signum() * y.signum()),
        _ => outward,
    }
}

/// The endpoint of a piece where a result of tonicity `t` is least, and where it is
/// greatest.
fn pick(t: Tonicity, p: &(End, End)) -> (&End, &End) {
    match t {
        Tonicity::Down => (&p.1, &p.0),
        _ => (&p.0, &p.1),
    }
}

/// The image of the box of two pieces, each of one sign, under an operator monotone or
/// antitone in each argument there: the interval between two corners.
fn corners(op: &Op, a: &(End, End), b: &(End, End)) -> (End, End) {
    let dir = |arg: usize, own: &(End, End), other: &(End, End)| -> Tonicity {
        let nonneg = |p: &(End, End)| p.0.signum() >= 0;
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
    let zero = End::of(0);
    let (alo, ahi) = pick(dir(0, a, b), a);
    let (blo, bhi) = if arity(op) == 2 {
        pick(dir(1, b, a), b)
    } else {
        (&zero, &zero)
    };
    (at(op, alo, blo, Dir::Down), at(op, ahi, bhi, Dir::Up))
}

/// Forward transfer: an interval containing `op` of every choice of members of the operands.
/// For every operator but `mod`, the hull of the result is the hull of the exact image when
/// each operand is one interval.
// Complexity tradeoff: naive version, every operand split at zero and each pair of parts
// mapped, the images grouped by sign, capped and joined ([`map2`]), with eight vectors made
// and freed, about 22,000 instructions for `x + 2` over one interval each (COMPLEXITY.md row
// PA-bind-cost). Used: for `+` and `-` of two operands of one piece each, the two corners of
// the pieces, O(1): the images of the parts' pairs then fill the one interval between those
// corners, so the general path gives that interval. Test:
// `a_sum_or_difference_of_two_pieces_is_what_the_parts_give`.
pub fn forward(op: &Op, x: &IntervalSet, y: &IntervalSet) -> IntervalSet {
    if let (Op::Add | Op::Sub, Some(a), Some(b)) = (op, x.first(), y.first())
        && x.len() == 1
        && y.len() == 1
    {
        let (lo, hi) = corners(op, a, b);
        return IntervalSet::range(lo, hi);
    }
    let (xs, ys) = (x.sign_parts(), y.sign_parts());
    let one = [(End::of(0), End::of(0))];
    match op {
        Op::Mod => map2(&xs, &y.clone().into_pieces(), forward_mod),
        Op::Div => map2(&xs, &nonzero(ys), |a, b| vec![corners(op, a, b)]),
        _ if arity(op) == 1 => map2(&xs, &one, |a, b| vec![corners(op, a, b)]),
        _ => map2(&xs, &ys, |a, b| vec![corners(op, a, b)]),
    }
}

/// Forward transfer of the int power `x ^ n` at an exponent `n` that is a set, not a constant:
/// an interval containing `x ^ k` for every member `x` of `x` and every member `k >= 0` of `n`.
/// The members of `n` below 0 give no int (a checked program raises an int to none, DESIGN.md
/// L1.26), so an `n` with no member at least 0 gives the empty set. One exponent is the table's
/// entry [`Op::Pow`], exact on every base. On a base of int[0..] the power is monotone in each
/// argument where the base is at least 1, so the result lies between the corners
/// `lo(x) ^ lo(n)` and `hi(x) ^ hi(n)`, each exact at any size through [`Num::pow_by`]; a base
/// of 0 adds the value 0 (and 1 at the exponent 0) below them. A base that may be negative
/// gives any int.
// Complexity tradeoff: O(1) operations on the four ends, where reading the image of each
// member pair is O(|x| |n|) or unbounded. The corners are exact: `Num::pow_by` keeps a power
// of a value past `i128` as its base and exponent, never written out, so `2 ^ (2 ^ 40)` costs
// the bits of 2 and of `2 ^ 40`; an exponent that is itself kept has no form there, and the
// end is bounded outward by `pow_end`. Before POW-scope-exponent the checker read only the
// lower bound, by Bernoulli's inequality `b ^ k >= 1 + k (b - 1)` (O(1) words, below `b ^ k`
// from k = 2 on, so `2^(5^(2^k + 1) - 10)` was rejected); the exact corner costs the same
// order. Given up: precision on a base that may be negative (`(-2)^(2*k)` is any int), which
// needs the parity of each exponent. Test: `l01_29_diagnostics::power_repairs`; COMPLEXITY.md
// C60.
pub fn forward_pow(x: &IntervalSet, n: &IntervalSet) -> IntervalSet {
    let n = n.meet(&IntervalSet::range(End::of(0), PosInf));
    // The least member of a set of ints at least 0 is finite.
    let (Some((blo, bhi)), Some((Fin(klo), khi))) = (x.bounds(), n.bounds()) else {
        return IntervalSet::empty();
    };
    if matches!(khi, Fin(h) if h == klo) {
        return forward(&Op::Pow(klo.clone().into()), x, x);
    }
    if blo.signum() < 0 {
        return IntervalSet::top();
    }
    // `n` has two members at least, so its greatest is at least 1, and `0 ^ hi(n)` is 0.
    let lo = match blo {
        Fin(b) if !b.is_zero() => pow_end(b, &klo.clone().into(), Dir::Down),
        _ => End::of(0),
    };
    let hi = match (bhi, khi) {
        (Fin(b), _) if b.is_zero() => End::of(if klo.signum() == 0 { 1 } else { 0 }),
        (Fin(b), _) if *b == Num::ONE => End::of(1),
        (Fin(b), Fin(k)) => pow_end(b, &k.clone().into(), Dir::Up),
        _ => PosInf,
    };
    IntervalSet::range(lo, hi)
}

/// `x mod y` for one piece of each: `0..abs(y)`, or the piece of `x` itself shifted when one
/// constant divisor maps it without wrapping.
fn forward_mod(a: &(End, End), b: &(End, End)) -> Vec<(End, End)> {
    if b.0.signum() == 0 && b.1.signum() == 0 {
        return Vec::new();
    }
    if let (Fin(lo), Fin(hi), Fin(c)) = (&a.0, &a.1, &b.0)
        && b.0 == b.1
        && (hi - lo) < c.abs()
        && lo.rem_euclid(c) <= hi.rem_euclid(c)
    {
        return vec![(Fin(lo.rem_euclid(c)), Fin(hi.rem_euclid(c)))];
    }
    // The remainder is below the largest abs(y), and for x >= 0 at most x.
    let top = match (-&b.0).max(b.1.clone()) {
        Fin(m) => Fin(&m - &Num::ONE),
        e => e,
    };
    let top = if a.0.signum() >= 0 {
        top.min(a.1.clone())
    } else {
        top
    };
    vec![(End::of(0), top)]
}

impl IntervalSet {
    /// The members of `within` that are not members of `self`. Ends are exact at any
    /// magnitude, so the complement of `{i64::MAX}` keeps every integer past it: the preimage
    /// of `y + (i64::MAX - 3) == i64::MAX` being false keeps every `y` above 3.
    pub fn complement_in(&self, within: &IntervalSet) -> IntervalSet {
        within.minus(self)
    }
}

/// The sign region of a part: negative, zero or positive.
fn region(p: &(End, End)) -> usize {
    if p.1.signum() < 0 {
        0
    } else if p.0.signum() > 0 {
        2
    } else {
        1
    }
}

/// The sign parts of a set without 0: the parts of [`IntervalSet::sign_parts`] but the part
/// `0..=0`, which are the sign parts of the set minus 0.
fn nonzero(mut parts: Vec<(End, End)>) -> Vec<(End, End)> {
    parts.retain(|p| region(p) != 1);
    parts
}

/// The parts of the union of `parts` split at zero, grouped by sign region: the sign parts of
/// [`IntervalSet::from_pieces`] of `parts`.
// Complexity tradeoff: the naive version builds the set of the parts and lists its sign
// parts, O(p log p) with a tree node allocated per piece and freed at once. Used: the same
// sort and merge on the list, then one split at zero, O(p log p) with no set built. Same
// output, no precondition (PERF-refused-assume).
fn regions(parts: Vec<(End, End)>) -> [Vec<(End, End)>; 3] {
    let mut out: [Vec<(End, End)>; 3] = Default::default();
    for p in split_signs(normal_pieces(parts)) {
        out[region(&p)].push(p);
    }
    out
}

/// The image of each pair of parts under `f`, joined, with work linear in the operands and no
/// constant bound. The operand with fewer parts is first capped to `ceil((k + m) / k)` pieces
/// for `k >= m` parts, so at most `4(k + 2)` pairs are taken once both are split at 0; and
/// each sign region of the image is
/// capped to the most pieces either operand has in one region, so no chain of operators
/// multiplies piece counts (the rule of low complexity, Part G). With one operand of one
/// piece, nothing is merged before the image is taken.
///
/// Complexity tradeoff: the merged pieces fill the gaps between them, so the image can hold
/// values no pair of operand values gives (for k ≥ m pieces, at most 4(k + 2) pairs are taken,
/// not k·m). Why: the exact image has up to k·m pieces, and a chain of n
/// operators up to k^n. Trigger: two operands of more than one piece each, or an image with
/// more pieces in a sign region than either operand has there; the limits are relative to
/// the operands, never constants. Tests:
/// `l01_24_refinement_lattices::scaling::a_chain_of_operators_keeps_to_its_operands_pieces`,
/// `l01_24_refinement_lattices::scaling::an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region`,
/// `l01_24_refinement_lattices::scaling::the_interval_operations_scale`. COMPLEXITY.md rows S4
/// and S14. A complete solution would keep the image as a symbolic set (the operation applied
/// to the operands) and list its pieces only on demand, at a cost in k·m when asked.
fn map2(
    a: &[(End, End)],
    b: &[(End, End)],
    f: impl Fn(&(End, End), &(End, End)) -> Vec<(End, End)>,
) -> IntervalSet {
    // The lists are kept as lists, sorted and merged as `IntervalSet::from_pieces` would, and
    // a set is built only for the result: each list here is read once (PERF-refused-assume).
    let (ra, rb) = (regions(a.to_vec()), regions(b.to_vec()));
    let most = ra.iter().chain(&rb).map(Vec::len).max().unwrap_or(0);
    let shrink = |r: [Vec<(End, End)>; 3], big: usize, small: usize| {
        let c = (big + small).div_ceil(big.max(1));
        split_signs(cap_pieces(normal_pieces(r.concat()), c))
    };
    let (na, nb) = (a.len(), b.len());
    let (pa, pb) = if na >= nb {
        (ra.concat(), shrink(rb, na, nb))
    } else {
        (shrink(ra, nb, na), rb.concat())
    };
    let f = &f;
    let image: Vec<(End, End)> = pa
        .iter()
        .flat_map(|p| pb.iter().flat_map(move |q| f(p, q)))
        .collect();
    IntervalSet::from_pieces(
        regions(image)
            .into_iter()
            .flat_map(|ps| cap_pieces(ps, most))
            .collect(),
    )
}

/// The real quotient `z / y` at two endpoints, rounded outward in `dir`.
fn quotient(z: &End, y: &End, dir: Dir) -> End {
    match (z, y) {
        (Fin(n), Fin(d)) if !d.is_zero() => {
            let floor = n.div_floor(d);
            match dir {
                Dir::Up if !n.mod_floor(d).is_zero() => Fin(&floor + &Num::ONE),
                _ => Fin(floor),
            }
        }
        (Fin(_), _) if y.signum() != 0 => End::of(0),
        (_, Fin(d)) if !d.is_zero() => {
            if z.signum() * d.signum() > 0 {
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
    op: &Op,
    arg: usize,
    x: &IntervalSet,
    y: &IntervalSet,
    z: &IntervalSet,
) -> IntervalSet {
    let own = if arg == 0 { x } else { y };
    let other = if arg == 0 { y } else { x };
    let narrowed = match (op, arg) {
        (Op::Add, _) => forward(&Op::Sub, z, other),
        (Op::Sub, 0) => forward(&Op::Add, z, y),
        (Op::Sub, _) => forward(&Op::Sub, x, z),
        (Op::Neg, _) => z.neg(),
        (Op::Mul, _) => {
            if z.contains(0) && other.contains(0) {
                IntervalSet::top()
            } else {
                map2(&z.sign_parts(), &nonzero(other.sign_parts()), |zp, yp| {
                    // z / y over a box of one sign in each: monotone in each argument, so
                    // its extremes are among the four corners.
                    let qs = [
                        (&zp.0, &yp.0),
                        (&zp.0, &yp.1),
                        (&zp.1, &yp.0),
                        (&zp.1, &yp.1),
                    ];
                    let lo = qs
                        .iter()
                        .map(|&(a, b)| quotient(a, b, Dir::Down))
                        .min()
                        .unwrap();
                    let hi = qs
                        .iter()
                        .map(|&(a, b)| quotient(a, b, Dir::Up))
                        .max()
                        .unwrap();
                    vec![(lo, hi)]
                })
            }
        }
        (Op::Pow(k), _) if k.is_zero() => IntervalSet::top(),
        (Op::Pow(k), _) => z.lift1(|(lo, hi)| roots(k, lo, hi)),
        (Op::Abs, _) => z.lift1(|(lo, hi)| {
            let lo = lo.clone().max(End::of(0));
            vec![(-hi, -&lo), (lo, hi.clone())]
        }),
        (Op::Min, _) => match (z.bounds(), other.bounds()) {
            (Some((_, zhi)), Some((olo, _))) if olo > zhi => z.clone(),
            (Some((zlo, _)), _) => IntervalSet::range(zlo.clone(), PosInf),
            (None, _) => IntervalSet::empty(),
        },
        (Op::Max, _) => match (z.bounds(), other.bounds()) {
            (Some((zlo, _)), Some((_, ohi))) if ohi < zlo => z.clone(),
            (Some((_, zhi)), _) => IntervalSet::range(NegInf, zhi.clone()),
            (None, _) => IntervalSet::empty(),
        },
        // x = q * y + r with q in z and r in 0..abs(y).
        (Op::Div, 0) => {
            let largest = forward(&Op::Abs, y, y)
                .bounds()
                .map_or(End::of(0), |b| b.1.clone());
            let rest = IntervalSet::range(End::of(0), largest.pred());
            forward(&Op::Add, &forward(&Op::Mul, z, y), &rest)
        }
        // A remainder r needs abs(y) > r.
        (Op::Mod, 1) => match z.bounds() {
            Some((Fin(r), _)) if r.signum() >= 0 => {
                let past = r + &Num::ONE;
                IntervalSet::from_pieces(vec![(NegInf, Fin(-&past)), (Fin(past), PosInf)])
            }
            Some(_) => IntervalSet::top(),
            None => IntervalSet::empty(),
        },
        (Op::Div, _) | (Op::Mod, _) => IntervalSet::top(),
    };
    own.meet(&narrowed)
}

/// The members of `x` with `x ^ k` in `lo..=hi`, for `k >= 1`, as at most two pieces.
fn roots(k: &Exponent, lo: &End, hi: &End) -> Vec<(End, End)> {
    // The largest r >= 0 with r ^ k <= v, for v >= 0, or a greater bound when `k` has no
    // exact form.
    let floor_root = |v: &End| -> End {
        let Fin(v) = v else { return PosInf };
        if let Some(r) = v.floor_root_by(k.num()) {
            return Fin(r);
        }
        // Complexity tradeoff: see `pow_end`, a kept `k` (past `2 ^ 127`). `r ^ k` exceeds `v`
        // for every `r >= 2` while `v < 2 ^ u32::MAX`, so the root is then exact (0 or 1); past
        // that the bound is the root for `u32::MAX`, which is at least the root for `k`.
        Fin(if *v <= Num::ONE {
            v.clone()
        } else if *v < Num::from(2).pow(u32::MAX) {
            Num::ONE
        } else {
            v.floor_root(u32::MAX)
        })
    };
    // The least r >= 0 with r ^ k >= v, for v >= 0, or a smaller bound when `k` has no exact
    // form.
    let ceil_root = |v: &End| -> End {
        let Fin(v) = v else { return PosInf };
        // Complexity tradeoff: see `pow_end`, a kept `k`. The root is `v` for `v <= 1` and at
        // least 2 past it.
        Fin(v
            .ceil_root_by(k.num())
            .unwrap_or_else(|| v.clone().min(Num::from(2))))
    };
    if k.is_odd() {
        // Odd powers are increasing, and odd about 0.
        let up = |v: &End| {
            if v.signum() >= 0 {
                floor_root(v)
            } else {
                -ceil_root(&-v)
            }
        };
        let down = |v: &End| {
            if v.signum() >= 0 {
                ceil_root(v)
            } else {
                -floor_root(&-v)
            }
        };
        return vec![(down(lo), up(hi))];
    }
    if hi.signum() < 0 {
        return Vec::new();
    }
    let (r_lo, r_hi) = (ceil_root(&lo.clone().max(End::of(0))), floor_root(hi));
    vec![(-&r_hi, -&r_lo), (r_lo, r_hi)]
}

/// `x ^ k` at a finite end `x`, rounded outward in `dir`: exact for every `k` that is not
/// kept ([`Num::pow_by`]), with a kept power for a result past `i128`. A count of factors is
/// exact at any size (S30b), so a squaring name nested 33 deep is exact.
///
/// Complexity tradeoff: two exponents have no exact form, and for them the end is bounded
/// by `2 ^ u32::MAX` on the side toward 0 and is infinite on the side away from 0, for
/// `abs(x) >= 2`: a kept exponent, such as `2 ^ 200` or the kernel's `10 ^ 10 ^ 9`, whose
/// power would need a kept atom with a kept exponent; and a kept base that is not bare (a
/// sum) with `k` past `u32`, whose expansion squares its terms about 32 times. Why: an atom
/// with a kept exponent needs an approximation whose shift is itself kept (a tower), and
/// how such values compare is not specified (open: POW-tower). Trigger:
/// `x ^ (2 ^ 200)` on a base other than -1, 0 and 1, or `(2 ^ 200 + 1) ^ (2 ^ 40)`.
/// Test: `l01_25_preimage_catalog::powers::an_exponent_of_any_size_is_read_by_its_parity`
/// and `l01_24_refinement_lattices::past_i64::an_exponent_with_no_exact_form_bounds_outward`;
/// COMPLEXITY.md S36. A complete solution would keep the exponent of a kept power as a kept
/// value, and `s ^ k` as an atom.
fn pow_end(x: &Num, k: &Exponent, dir: Dir) -> End {
    if let Some(v) = x.pow_by(k.num()) {
        return Fin(v);
    }
    match x.to_i64() {
        Some(0) => return End::of(0),
        Some(1) => return End::of(1),
        Some(-1) => return End::of(if k.is_odd() { -1 } else { 1 }),
        _ => {}
    }
    let least = Num::from(2).pow(u32::MAX);
    match (x.signum() < 0 && k.is_odd(), dir) {
        (false, Dir::Down) => Fin(least),
        (false, Dir::Up) => PosInf,
        (true, Dir::Down) => NegInf,
        (true, Dir::Up) => Fin(-&least),
    }
}

/// The reduction between an interval and a congruence (sec:constraints): each piece's
/// endpoints move inward to the nearest members of the class, and a single value fixes the
/// other domain.
pub fn reduce_congruence(x: &IntervalSet, c: &Congruence) -> (IntervalSet, Congruence) {
    let Congruence::Class {
        modulus: m,
        residue,
    } = c
    else {
        return (IntervalSet::empty(), Congruence::Bottom);
    };
    let x = if m.is_zero() {
        x.meet(&IntervalSet::point(residue.clone()))
    } else if *m == Num::ONE {
        x.clone()
    } else {
        x.lift1(|(lo, hi)| {
            let up = |e: &End| match e {
                Fin(v) => Fin(v + &(residue - v).rem_euclid(m)),
                e => e.clone(),
            };
            let down = |e: &End| match e {
                Fin(v) => Fin(v - &(v - residue).rem_euclid(m)),
                e => e.clone(),
            };
            vec![(up(lo), down(hi))]
        })
    };
    let c = match x.bounds() {
        None => Congruence::Bottom,
        Some((Fin(a), Fin(b))) if a == b => c.meet(&Congruence::single(a.clone())),
        Some(_) => c.clone(),
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
            let points =
                IntervalSet::from_pieces(k.iter().map(|&v| (End::of(v), End::of(v))).collect());
            (x.meet(&points), kept)
        }
    }
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod tests {
    use super::*;

    const WINDOW: std::ops::RangeInclusive<i64> = -12..=12;

    /// Every interval with endpoints in -4..=4 or infinite, and some unions.
    pub(super) fn operands() -> Vec<IntervalSet> {
        operands_with_ends(-4..=4)
    }

    /// The empty set, every interval with endpoints in `finite` or infinite, and two unions.
    fn operands_with_ends(finite: impl IntoIterator<Item = i64>) -> Vec<IntervalSet> {
        let ends: Vec<End> = std::iter::once(NegInf)
            .chain(finite.into_iter().map(End::of))
            .chain(std::iter::once(PosInf))
            .collect();
        let mut out = vec![IntervalSet::empty()];
        for lo in &ends {
            for hi in &ends {
                if lo <= hi && *lo != PosInf && *hi != NegInf {
                    out.push(IntervalSet::range(lo.clone(), hi.clone()));
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

    fn apply(op: &Op, x: i64, y: i64) -> Option<i64> {
        match op {
            Op::Add => Some(x + y),
            Op::Sub => Some(x - y),
            Op::Neg => Some(-x),
            Op::Mul => Some(x * y),
            Op::Pow(k) => Some(x.pow(k.to_u32()?)),
            Op::Div => (y != 0).then(|| x.div_euclid(y)),
            Op::Mod => (y != 0).then(|| x.rem_euclid(y)),
            Op::Abs => Some(x.abs()),
            Op::Min => Some(x.min(y)),
            Op::Max => Some(x.max(y)),
        }
    }

    fn ops() -> [Op; 12] {
        [
            Op::Add,
            Op::Sub,
            Op::Neg,
            Op::Mul,
            Op::Pow(Int::ZERO.into()),
            Op::Pow(Int::from(2).into()),
            Op::Pow(Int::from(3).into()),
            Op::Div,
            Op::Mod,
            Op::Abs,
            Op::Min,
            Op::Max,
        ]
    }

    /// `+` and `-` of two sets of one piece each, read from the pieces' corners, are what the
    /// general path of [`forward`] gives from the parts split at zero, on every pair of
    /// operands and on random pieces with large and infinite ends.
    #[test]
    fn a_sum_or_difference_of_two_pieces_is_what_the_parts_give() {
        let general = |op: &Op, x: &IntervalSet, y: &IntervalSet| {
            map2(&x.sign_parts(), &y.sign_parts(), |a, b| {
                vec![corners(op, a, b)]
            })
        };
        let mut pairs = Vec::new();
        for x in operands() {
            for y in operands() {
                pairs.push((x.clone(), y));
            }
        }
        let mut seed =
            crate::seed::seed("a_sum_or_difference_of_two_pieces_is_what_the_parts_give") | 1;
        let mut below = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n
        };
        let end = |below: &mut dyn FnMut(u64) -> u64| match below(10) {
            0 => NegInf,
            1 => PosInf,
            2 => End::from(i128::MAX - below(5) as i128),
            3 => End::from(i128::MIN + below(5) as i128),
            _ => End::of(below(41) as i64 - 20),
        };
        for _ in 0..1000 {
            let (a, b, c, d) = (
                end(&mut below),
                end(&mut below),
                end(&mut below),
                end(&mut below),
            );
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
            let (lo2, hi2) = if c <= d { (c, d) } else { (d, c) };
            pairs.push((IntervalSet::range(lo, hi), IntervalSet::range(lo2, hi2)));
        }
        let mut one = 0;
        for op in [Op::Add, Op::Sub] {
            for (x, y) in &pairs {
                one += usize::from(x.len() == 1 && y.len() == 1);
                assert_eq!(forward(&op, x, y), general(&op, x, y), "{op:?} {x:?} {y:?}");
            }
        }
        assert!(one > 8000, "{one} pairs of one piece each");
    }

    #[test]
    fn forward_transfer_contains_every_result_in_the_window() {
        for op in &ops() {
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
        for op in ops().iter().filter(|op| !matches!(op, Op::Mod)) {
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
        matches!(s.only(), Some((Fin(_), Fin(_))))
    }

    /// On every interval with ends in `{-2, 0, 1, 3}` or infinite and two unions, as `x` and
    /// `y`, and with ends in `{-2, 0, 3}` as `z`: ends below, at and above zero, pieces of one
    /// sign that do not touch zero, and pieces of one point. The sweep over ends in `-4..=4` is
    /// in `bench.rs`.
    #[test]
    fn backward_transfer_keeps_every_operand_that_can_give_the_result() {
        let some = operands_with_ends([-2, 0, 1, 3]);
        backward_keeps_every_operand(&some, &some, &operands_with_ends([-2, 0, 3]));
    }

    /// Checks `backward` on every op, operand and triple of `xs`, `ys` and `zs`: the result
    /// lies in the operand and keeps each member of it that, with a member of the other
    /// operand, gives a result in `z` inside the test window.
    pub(super) fn backward_keeps_every_operand(
        xs: &[IntervalSet],
        ys: &[IntervalSet],
        zs: &[IntervalSet],
    ) {
        for op in &ops() {
            for arg in 0..arity(op) {
                for x in xs {
                    for y in ys {
                        for z in zs {
                            let got = backward(op, arg, x, y, z);
                            assert!(got.is_subset(if arg == 0 { x } else { y }));
                            let bs = if arity(op) == 1 { vec![0] } else { members(y) };
                            for a in members(x) {
                                for &b in &bs {
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
        assert_eq!(backward(&Op::Mul, 0, &x, &IntervalSet::of(0, 3), &z), x);
        assert_eq!(
            backward(&Op::Mul, 0, &x, &IntervalSet::of(1, 3), &z),
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
                        if x.contains(v) && c.contains(&Num::from(v)) {
                            assert!(
                                x2.contains(v) && c2.contains(&Num::from(v)),
                                "{x} {c:?} lost {v}"
                            );
                        }
                    }
                    for (lo, hi) in x2.pieces() {
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
        let (x, _) = reduce_congruence(
            &IntervalSet::range(NegInf, End::of(-4)),
            &Congruence::new(3, 1),
        );
        assert_eq!(x, IntervalSet::range(NegInf, End::of(-5)));
    }

    /// The power at an exponent that is a set holds every power of its members, and on a base
    /// of int[0..] whose members are all in the window it is their hull: its ends are the
    /// least and greatest powers. An exponent with no member at least 0 gives nothing.
    #[test]
    fn a_power_at_a_set_of_exponents_holds_each_power_and_no_more() {
        for x in operands() {
            for n in operands() {
                let f = forward_pow(&x, &n);
                let ks: Vec<i64> = members(&n).into_iter().filter(|&k| k >= 0).collect();
                let mut powers = Vec::new();
                for b in members(&x) {
                    for &k in &ks {
                        let v = b.pow(u32::try_from(k).expect("k >= 0"));
                        assert!(f.contains(v), "{x} ^ {n} = {f} lacks {b}^{k}");
                        powers.push(v);
                    }
                }
                if ks.is_empty() && n.meet(&IntervalSet::range(End::of(0), PosInf)).is_empty() {
                    assert_eq!(f, IntervalSet::empty(), "{x} ^ {n}");
                }
                let finite = |s: &IntervalSet| matches!(s.bounds(), Some((Fin(_), Fin(_))));
                let nonneg = x.bounds().is_some_and(|(lo, _)| lo.signum() >= 0);
                if nonneg && finite(&x) && finite(&n) && !powers.is_empty() {
                    let (lo, hi) = (powers.iter().min(), powers.iter().max());
                    let want = IntervalSet::range(
                        End::of(*lo.expect("a power")),
                        End::of(*hi.expect("a power")),
                    );
                    assert_eq!(f, want, "{x} ^ {n}");
                }
            }
        }
        // The least power is exact, where Bernoulli's inequality gives 1 + 2 * 4 = 9.
        let at_least = |v: i64| IntervalSet::range(End::of(v), PosInf);
        assert_eq!(forward_pow(&at_least(5), &at_least(2)), at_least(25));
        // An end of any size is held as a power, not written out.
        let k = Num::from(2).pow(40);
        let f = forward_pow(&at_least(2), &IntervalSet::range(Fin(k.clone()), PosInf));
        let want = Num::from(2).pow_by(&k).expect("a power of an int");
        assert_eq!(f, IntervalSet::range(Fin(want), PosInf));
        // A base that may be negative gives any int; at one exponent, the table's entry.
        assert_eq!(
            forward_pow(&IntervalSet::of(-2, 3), &at_least(0)),
            IntervalSet::top()
        );
        assert_eq!(
            forward_pow(&IntervalSet::of(-2, 3), &IntervalSet::single(2)),
            IntervalSet::of(0, 9)
        );
    }

    /// The tonicity table's entries for `div` and `mod`, which no pair of operands reads
    /// through `forward`'s general path.
    #[test]
    fn div_and_mod_have_their_own_tonicity() {
        assert_eq!(tonicity(&Op::Div, 0), Tonicity::UpWhereOtherNonneg);
        assert_eq!(tonicity(&Op::Div, 1), Tonicity::DownWhereOtherNonneg);
        assert_eq!(tonicity(&Op::Mod, 0), Tonicity::None);
        assert_eq!(tonicity(&Op::Mod, 1), Tonicity::None);
    }

    /// `at` on infinite ends: `inf + -inf` and `inf - inf` round outward, an infinite
    /// numerator over a finite divisor is infinite by the signs, a finite numerator over an
    /// infinite divisor is the limit of the Euclidean quotient, and a zero divisor rounds
    /// outward.
    #[test]
    fn ends_at_infinity_take_their_limits_or_round_outward() {
        use Dir::{Down, Up};
        let five = End::of(5);
        assert_eq!(at(&Op::Add, &NegInf, &PosInf, Down), NegInf);
        assert_eq!(at(&Op::Add, &PosInf, &NegInf, Up), PosInf);
        assert_eq!(at(&Op::Sub, &PosInf, &PosInf, Down), NegInf);
        assert_eq!(at(&Op::Sub, &NegInf, &NegInf, Up), PosInf);
        assert_eq!(at(&Op::Add, &five, &PosInf, Down), PosInf);
        assert_eq!(at(&Op::Div, &PosInf, &End::of(2), Up), PosInf);
        assert_eq!(at(&Op::Div, &PosInf, &End::of(-2), Down), NegInf);
        assert_eq!(at(&Op::Div, &NegInf, &End::of(-3), Up), PosInf);
        assert_eq!(at(&Op::Div, &NegInf, &End::of(3), Down), NegInf);
        // -5 = -1 * y + (y - 5) for a large positive y, and 1 * y + (-5 - y) for a large
        // negative one.
        assert_eq!(at(&Op::Div, &five, &PosInf, Down), End::of(0));
        assert_eq!(at(&Op::Div, &five, &NegInf, Down), End::of(0));
        assert_eq!(at(&Op::Div, &End::of(-5), &PosInf, Down), End::of(-1));
        assert_eq!(at(&Op::Div, &End::of(-5), &NegInf, Up), End::of(1));
        assert_eq!(at(&Op::Div, &five, &End::of(0), Down), NegInf);
        assert_eq!(at(&Op::Div, &PosInf, &End::of(0), Up), PosInf);
    }

    /// The reductions with a fact that holds nothing, the bottom congruence, and with one
    /// that holds everything, the top finite set.
    #[test]
    fn reductions_with_bottom_and_top() {
        let x = IntervalSet::of(-3, 7);
        assert_eq!(
            reduce_congruence(&x, &Congruence::Bottom),
            (IntervalSet::empty(), Congruence::Bottom)
        );
        assert_eq!(
            reduce_finite(&x, &FiniteSet::Top),
            (x.clone(), FiniteSet::Top)
        );
    }

    /// A kept exponent, `2 ^ (2 ^ 200)` and that plus 1, has no exact power past -1, 0 and 1:
    /// forward, an end is bounded by `2 ^ u32::MAX` toward 0 and infinite away from it;
    /// backward, the roots of results up to 10 are exact (0 and 1), and of 2 and more none.
    #[test]
    fn a_kept_exponent_bounds_powers_and_roots() {
        let even = Num::pow2(&Num::pow2(&Num::from(200)));
        let odd = &even + &Num::ONE;
        let (pe, po) = (Op::Pow(even.into()), Op::Pow(odd.into()));
        let least = Num::from(2).pow(u32::MAX);
        let up = IntervalSet::range(Fin(least.clone()), PosInf);
        let down = IntervalSet::range(NegInf, Fin(-&least));
        let one = IntervalSet::single;
        let y = IntervalSet::top();
        for v in [-1, 0, 1] {
            assert_eq!(forward(&pe, &one(v), &y), one(v * v), "{v} ^ even");
            assert_eq!(forward(&po, &one(v), &y), one(v), "{v} ^ odd");
        }
        assert_eq!(forward(&pe, &one(2), &y), up);
        assert_eq!(forward(&pe, &one(-2), &y), up);
        assert_eq!(forward(&po, &one(2), &y), up);
        assert_eq!(forward(&po, &one(-2), &y), down);
        let x = IntervalSet::of(-5, 5);
        let back = |op: &Op, lo: i64, hi: i64| backward(op, 0, &x, &y, &IntervalSet::of(lo, hi));
        assert_eq!(back(&pe, 0, 10), IntervalSet::of(-1, 1));
        assert_eq!(back(&po, 0, 10), IntervalSet::of(0, 1));
        assert_eq!(back(&po, -10, -1), IntervalSet::single(-1));
        assert!(back(&pe, 2, 10).is_empty());
        assert!(back(&po, 2, 10).is_empty());
    }
}
