//! The integer roots of a polynomial with integer coefficients in one name, within an interval
//! (DESIGN.md sec:constraints, "Reduction", QUESTIONS A81): where an obligation's negation is
//! such a polynomial equal to 0, its integer roots in the name's interval are a listed set, and
//! each written constraint is evaluated at each root as at a listed member.
//!
//! The method is that of Cucker, Koiran and Smale, "A polynomial time algorithm for
//! Diophantine equations in one variable" (J. Symbolic Computation 27, 1999): its time is
//! polynomial in the sparse size of the polynomial, the number of its terms and the bits of
//! its coefficients and exponents, and not in its degree.
//!
//! 1. Root 0 is read off the least exponent, and roots 1 and -1 off the sums of the
//!    coefficients.
//! 2. For `|x| >= 2` the polynomial is split at each gap in its exponents wider than the bits
//!    of the 1-norm of the terms below the gap: with `f = g + x^m h`, `g` of degree `d` and
//!    `2^(m - d) > ||g||_1`, a root `x` with `h(x) != 0` would give
//!    `|x|^m <= |x^m h(x)| = |g(x)| <= ||g||_1 |x|^d`, so `2^(m - d) <= ||g||_1`; hence each
//!    root with `|x| >= 2` is a root of `g` and of `h`, and so of every piece (`split`). Each
//!    piece's degree is under `t` times the bits of the 1-norm, for `t` terms, whatever the
//!    degree of the whole.
//! 3. The positive roots of the piece of least degree, and those of its reflection `x -> -x`,
//!    are found by branch and bound over integer intervals (`positive_roots`), in place of
//!    the paper's chain of derivatives: an interval is dropped when an interval evaluation
//!    bounded by the carries of the terms below each term shows no root in it
//!    (`may_hold_a_root`), and where `x p'(x)` has one sign on it the one sign change is found
//!    by Newton's method on the integers, each step that does not halve the bracket followed
//!    by a bisection (`search`).
//! 4. A candidate is kept when every other piece is 0 at it.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Pow, Signed, Zero};

use crate::term::{Prim, Term};
use crate::value::Value;

/// A polynomial in one name with integer coefficients: its terms, each an exponent and a
/// coefficient that is not zero, by increasing exponent. The zero polynomial has no terms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sparse {
    terms: Vec<(u64, BigInt)>,
}

/// The integer roots of a polynomial within an interval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Roots {
    /// The polynomial is zero: every member of the interval is a root.
    Every,
    /// The roots, in increasing order.
    Listed(Vec<BigInt>),
}

impl Sparse {
    /// The sum of `terms`, each an exponent and a coefficient. O(t log t) for `t` terms.
    pub fn new(terms: impl IntoIterator<Item = (u64, BigInt)>) -> Sparse {
        let mut sum: BTreeMap<u64, BigInt> = BTreeMap::new();
        for (e, c) in terms {
            *sum.entry(e).or_default() += c;
        }
        Sparse {
            terms: sum.into_iter().filter(|(_, c)| !c.is_zero()).collect(),
        }
    }

    /// The terms, by increasing exponent, no coefficient zero.
    pub fn terms(&self) -> &[(u64, BigInt)] {
        &self.terms
    }

    fn plus(&self, other: &Sparse) -> Sparse {
        Sparse::new(self.terms.iter().chain(&other.terms).cloned())
    }

    fn negated(&self) -> Sparse {
        Sparse {
            terms: self.terms.iter().map(|(e, c)| (*e, -c)).collect(),
        }
    }

    /// The product, or none when an exponent passes `u64::MAX`. O(a b log(a b)) for `a` and
    /// `b` terms: the size of the product written out, which a sparse method reads whole.
    fn times(&self, other: &Sparse) -> Option<Sparse> {
        let mut out = Vec::with_capacity(self.terms.len() * other.terms.len());
        for (e, c) in &self.terms {
            for (f, d) in &other.terms {
                out.push((e.checked_add(*f)?, c * d));
            }
        }
        Some(Sparse::new(out))
    }
}

/// `t` as a polynomial in the name `x`, each other name read through `constant` (none where
/// it has no one value); none for a term that is not such a polynomial. A literal, the name,
/// `-`, `+`, `-` and `*` are read, and `a ^ k` for a literal `k >= 1` where `a` is one term of
/// coefficient 1 or -1. A power of any other base is not read here, as the size of its terms
/// written out grows with the value of `k` and so exponentially with its digits: at the top of
/// an equation [`term_roots`] reads its base alone. O(the size of the result times the size of
/// `t`).
pub fn read(t: &Term, x: &str, constant: &dyn Fn(&str) -> Option<BigInt>) -> Option<Sparse> {
    let of = |c: BigInt| Sparse::new([(0, c)]);
    Some(match t {
        Term::Lit(Value::Int(k)) => of(BigInt::from(*k)),
        Term::Var(n) if &**n == x => Sparse::new([(1, BigInt::one())]),
        Term::Var(n) => of(constant(n)?),
        Term::Prim(Prim::Neg, a) if a.len() == 1 => read(&a[0], x, constant)?.negated(),
        Term::Prim(p @ (Prim::Add | Prim::Sub | Prim::Mul), a) if a.len() == 2 => {
            let (l, r) = (read(&a[0], x, constant)?, read(&a[1], x, constant)?);
            match p {
                Prim::Add => l.plus(&r),
                Prim::Sub => l.plus(&r.negated()),
                _ => l.times(&r)?,
            }
        }
        Term::Prim(Prim::Pow, a) if a.len() == 2 => {
            let Term::Lit(Value::Int(k)) = &a[1] else {
                return None;
            };
            let k = u64::try_from(*k).ok().filter(|&k| k >= 1)?;
            let base = read(&a[0], x, constant)?;
            let [(e, c)] = &base.terms[..] else {
                return None;
            };
            if !c.abs().is_one() {
                return None;
            }
            let c = if c.is_negative() && k % 2 == 1 {
                -BigInt::one()
            } else {
                BigInt::one()
            };
            Sparse::new([(e.checked_mul(k)?, c)])
        }
        _ => return None,
    })
}

/// The integer roots in `lo..=hi` (an end of none is open) of the polynomial `t` in `x`, read
/// as [`read`] reads it, except that a product's roots are those of its factors, and those of
/// a negation or of a power `a ^ k`, `k >= 1`, those of `a`: so `(p - 4) * (p - 9)` is not
/// multiplied out, and `(p - 1)^1000` is read. None where some part is not read.
pub fn term_roots(
    t: &Term,
    x: &str,
    constant: &dyn Fn(&str) -> Option<BigInt>,
    lo: Option<&BigInt>,
    hi: Option<&BigInt>,
) -> Option<Roots> {
    match t {
        Term::Prim(Prim::Mul, a) if a.len() == 2 => {
            let l = term_roots(&a[0], x, constant, lo, hi)?;
            let r = term_roots(&a[1], x, constant, lo, hi)?;
            Some(match (l, r) {
                (Roots::Listed(mut l), Roots::Listed(r)) => {
                    l.extend(r);
                    l.sort();
                    l.dedup();
                    Roots::Listed(l)
                }
                _ => Roots::Every,
            })
        }
        Term::Prim(Prim::Neg, a) if a.len() == 1 => term_roots(&a[0], x, constant, lo, hi),
        Term::Prim(Prim::Pow, a)
            if a.len() == 2 && matches!(&a[1], Term::Lit(Value::Int(k)) if *k >= 1) =>
        {
            term_roots(&a[0], x, constant, lo, hi)
        }
        _ => Some(integer_roots(&read(t, x, constant)?, lo, hi)),
    }
}

/// The integer roots of `f` in `lo..=hi`, an end of none open.
///
/// Complexity tradeoff. Naive: evaluate `f` at each member of the interval, O(w) evaluations
/// for `w` members, 10^9 for `int[1..=1000000000]`; or isolate the real roots of the dense
/// polynomial, polynomial in its degree, which a term `p^1000000` makes 10^6. Here, after
/// [Cucker, Koiran and Smale 1999], the cost is polynomial in the sparse size and in the log of
/// the degree: for `t` terms whose 1-norm has `B` bits, the split is O(t) additions, and the
/// search (`positive_roots`) costs O(t) products of numbers of O(B) bits per interval it
/// keeps, linear in `t` where the roots are few (measured: 7.6 times the work at 8 times the
/// terms). Given up: the paper's chain of `t` derivatives, O(t^3) evaluations (80.5 times the
/// work at 8 times the terms), which bounds the number of intervals where this method has no
/// proven bound; and on dense polynomials with many integer roots, as `(x - 2) … (x - 65)`, the
/// chain was about 2 times faster (40 against 80 ms at 64 roots), and on a small cubic as
/// `(x - 4)(x - 5)(x - 7)` about 1.5 times (27 against 42 us), because an interval evaluation
/// in the monomial basis overestimates across a cluster of roots, and each of its numbers is a
/// `BigInt`. Hensel lifting of the roots modulo a prime would
/// cost O(D) per prime and digit, but a repeated root and a prime dividing the discriminant
/// each need a case of their own. Tests: `l01_39_reduced_product::roots` (scaling in the
/// degree, the bits and the number of terms).
pub fn integer_roots(f: &Sparse, lo: Option<&BigInt>, hi: Option<&BigInt>) -> Roots {
    let Some((e0, _)) = f.terms.first() else {
        return Roots::Every;
    };
    let within = |x: &BigInt| lo.is_none_or(|l| l <= x) && hi.is_none_or(|h| x <= h);
    let g: Vec<(u64, BigInt)> = (f.terms.iter()).map(|(e, c)| (e - e0, c.clone())).collect();
    let mut out = Vec::new();
    if *e0 > 0 && within(&BigInt::zero()) {
        out.push(BigInt::zero());
    }
    // `g(1)` and `g(-1)`, read off the coefficients and the parity of the exponents.
    let at_one: BigInt = g.iter().map(|(_, c)| c).sum();
    let at_minus_one: BigInt = (g.iter())
        .map(|(e, c)| if e % 2 == 0 { c.clone() } else { -c })
        .sum();
    for (x, v) in [(-1, at_minus_one), (1, at_one)] {
        let x = BigInt::from(x);
        if v.is_zero() && within(&x) {
            out.push(x);
        }
    }
    let pieces = split(&g);
    let (k, least) = (pieces.iter().enumerate())
        .min_by_key(|(_, p)| p.last().map_or(0, |(e, _)| *e))
        .expect("a polynomial that is not zero has a piece");
    let two = BigInt::from(2);
    let from = |l: Option<BigInt>| l.map_or(two.clone(), |l| l.max(two.clone()));
    let mut candidates = positive_roots(least, from(lo.cloned()), hi.cloned());
    candidates.extend(
        positive_roots(&reflected(least), from(hi.map(|h| -h)), lo.map(|l| -l))
            .into_iter()
            .map(|y| -y),
    );
    // Each candidate is checked in each other piece at its point: O(t) products of numbers of
    // the bits of the 1-norm and the candidate, not the evaluation of the piece, of up to
    // `D bits(x)` bits.
    let is_root = |p: &[(u64, BigInt)], x: &BigInt| match x.is_negative() {
        false => may_hold_a_root(p, x, x),
        true => may_hold_a_root(&reflected(p), &-x, &-x),
    };
    for x in candidates {
        if (pieces.iter().enumerate()).all(|(i, p)| i == k || is_root(p, &x)) {
            out.push(x);
        }
    }
    out.sort();
    out.dedup();
    Roots::Listed(out)
}

/// The pieces of `g`, whose least exponent is 0, each shifted to least exponent 0, such that
/// each root `x` of `g` with `|x| >= 2` is a root of every piece and each common root of the
/// pieces a root of `g`. A piece ends below a gap of at least the bits of the 1-norm of its
/// terms. O(t) additions for `t` terms.
fn split(g: &[(u64, BigInt)]) -> Vec<Vec<(u64, BigInt)>> {
    let shifted = |p: &[(u64, BigInt)]| -> Vec<(u64, BigInt)> {
        let e0 = p[0].0;
        p.iter().map(|(e, c)| (e - e0, c.clone())).collect()
    };
    let mut pieces = Vec::new();
    let mut start = 0;
    let mut norm = g[0].1.abs();
    for i in 1..g.len() {
        // `2^gap >= 2^bits > norm`, the condition of the split.
        if g[i].0 - g[i - 1].0 >= norm.bits() {
            pieces.push(shifted(&g[start..i]));
            start = i;
            norm = BigInt::zero();
        }
        norm += g[i].1.abs();
    }
    pieces.push(shifted(&g[start..]));
    pieces
}

/// `p` with `x` replaced by `-x`: the coefficient of each odd exponent negated.
fn reflected(p: &[(u64, BigInt)]) -> Vec<(u64, BigInt)> {
    (p.iter())
        .map(|(e, c)| (*e, if e % 2 == 1 { -c } else { c.clone() }))
        .collect()
}

/// `x^g` where it is at most `cap`, and `cap + 1` where it is above. `x >= 1`. As
/// `x^g >= 2^((bits(x) - 1) g)`, a power is formed only when it has under `bits(cap) bits(x) /
/// (bits(x) - 1) <= 2 bits(cap)` bits, so a gap of any width costs what one of the bits of
/// `cap` does.
fn capped_pow(x: &BigInt, g: u64, cap: &BigInt) -> BigInt {
    if (x.bits() - 1)
        .checked_mul(g)
        .is_none_or(|b| b >= cap.bits())
    {
        return cap + 1;
    }
    Pow::pow(x, g).min(cap + 1)
}

/// `floor(n / x^g)` for `x >= 2`, with the power capped above `|n|`, past which the quotient
/// is 0 or -1 by the sign of `n` alone.
fn floor_over_pow(n: &BigInt, x: &BigInt, g: u64) -> BigInt {
    n.div_floor(&capped_pow(x, g, &n.abs()))
}

/// The carry bounds of `p` at `l >= 2`: for each `k`, `B_k = floor(sum over i < k of |c_i|
/// l^(e_i - e_k))`, `B_0 = 0`. Write `U_k(x) = sum over i >= k of c_i x^(e_i - e_k)`, the terms
/// from the `k`th up divided by the `k`th power. At an integer root `x >= l`, `p(x) = 0` gives
/// `x^(e_k) U_k(x) = -(the terms below the k-th)`, so the carry `-U_k(x)` is an integer of
/// magnitude at most `sum over i < k of |c_i| x^(e_i - e_k)`, which falls as `x` grows: so
/// `|U_k(x)| <= B_k`. `B_k = floor((B_(k-1) + |c_(k-1)|) / l^(e_k - e_(k-1)))`, as
/// `floor(floor(z) / L) = floor(z / L)` for an integer `L >= 1`. O(t) divisions of numbers of
/// at most the bits of the 1-norm.
fn bounds(p: &[(u64, BigInt)], l: &BigInt) -> Vec<BigInt> {
    let mut out = Vec::with_capacity(p.len());
    out.push(BigInt::zero());
    for k in 1..p.len() {
        let below = &out[k - 1] + p[k - 1].1.abs();
        out.push(floor_over_pow(&below, l, p[k].0 - p[k - 1].0));
    }
    out
}

/// Whether `p` may have an integer root in `l..=h`, `2 <= l <= h`: false only where none lies
/// there, and, where `l == h`, true exactly where `l` is a root. Horner's rule from the top
/// term encloses `U_k` over the interval, `U_k = c_k + x^(e_(k+1) - e_k) U_(k+1)`, and each
/// enclosure is cut to `-B_k..=B_k` ([`bounds`]): an empty one leaves no root, and as `B_0 = 0`
/// the last asks that `p` itself may be 0. A product past `cap = B_k + |c_k| + 1` is cut to
/// `cap`, which changes no cut enclosure, so each number keeps the bits of the 1-norm and the
/// interval's ends, whatever the degree. O(t) products of such numbers.
///
/// The cut also does what the gap split does: where `B_k = 0`, `U_k` must be 0 at a root.
fn may_hold_a_root(p: &[(u64, BigInt)], l: &BigInt, h: &BigInt) -> bool {
    let b = bounds(p, l);
    let n = p.len();
    let (mut lo, mut hi) = (p[n - 1].1.clone(), p[n - 1].1.clone());
    for k in (0..n).rev() {
        if k + 1 < n {
            let g = p[k + 1].0 - p[k].0;
            let cap = &b[k] + p[k].1.abs() + 1;
            let (pl, ph) = (capped_pow(l, g, &cap), capped_pow(h, g, &cap));
            let least = if lo.is_negative() {
                &lo * &ph
            } else {
                &lo * &pl
            };
            let most = if hi.is_negative() {
                &hi * &pl
            } else {
                &hi * &ph
            };
            let within = |v: BigInt| v.clamp(-&cap, cap.clone()) + &p[k].1;
            (lo, hi) = (within(least), within(most));
        }
        lo = lo.max(-&b[k]);
        hi = hi.min(b[k].clone());
        if lo > hi {
            return false;
        }
    }
    true
}

/// Whether `q` (`-q` where `negate`) is positive at every real point of `l..=h`, `2 <= l <=
/// h`; where `l == h`, exactly whether it is positive at `l`. The least value of each `U_k` over
/// the interval is carried down from the top term (it depends on the least value of `U_(k+1)`
/// alone); where it passes `B_k` (`b`, the [`bounds`] of `q` at `l`), `U_k` outweighs every term
/// below and `q` is positive, and where it falls under `-B_k` the proof is given up. As in
/// [`may_hold_a_root`], a product past `cap` decides the step either way, so it is cut there.
/// O(t) products of numbers of the bits of the 1-norm and the interval's ends.
fn positive_on(q: &[(u64, BigInt)], b: &[BigInt], l: &BigInt, h: &BigInt, negate: bool) -> bool {
    let c = |k: usize| if negate { -&q[k].1 } else { q[k].1.clone() };
    let mut lo = c(q.len() - 1);
    for k in (0..q.len()).rev() {
        if k + 1 < q.len() {
            let g = q[k + 1].0 - q[k].0;
            let cap = &b[k] + q[k].1.abs() + 1;
            let x = if lo.is_negative() { h } else { l };
            lo = (lo * capped_pow(x, g, &cap)).clamp(-&cap, cap.clone()) + c(k);
        }
        if lo > b[k] {
            return true;
        }
        if lo < -&b[k] {
            return false;
        }
    }
    false
}

/// The sign of `q` at `x >= 2`, by [`positive_on`] at the point.
fn sign_at(q: &[(u64, BigInt)], x: &BigInt) -> Ordering {
    let b = bounds(q, x);
    if positive_on(q, &b, x, x, false) {
        Ordering::Greater
    } else if positive_on(q, &b, x, x, true) {
        Ordering::Less
    } else {
        Ordering::Equal
    }
}

/// `floor(2^s q(x) / x^D)` for `x >= 2`, `D` the greatest exponent of `q`: exact, from the
/// least term up, `a_i = floor(a_(i-1) / x^(e_i - e_(i-1))) + 2^s c_i`, each number of at most
/// `s` bits more than the 1-norm. Newton's step in [`search`] is read from two such values, so
/// that it never forms `q(x)`, of up to `D bits(x)` bits. O(t) divisions.
fn scaled(q: &[(u64, BigInt)], x: &BigInt, s: u64) -> BigInt {
    let mut acc = BigInt::zero();
    for (i, (e, c)) in q.iter().enumerate() {
        if i > 0 {
            acc = floor_over_pow(&acc, x, e - q[i - 1].0);
        }
        acc += c << s;
    }
    acc
}

/// The integer roots of `p`, whose least exponent is 0 and constant term not zero, in
/// `a..=b` with `a >= 2`, `b` none for no upper end. Cauchy's bound `1 + max |c|` closes the
/// interval. Branch and bound over integer intervals: an interval [`may_hold_a_root`] clears is
/// dropped; one point is a root; on one where `x p'(x)` has one sign ([`positive_on`]) `p` is
/// monotone and its one sign change is found by [`search`]; any other is cut in two, at the
/// power of 2 halfway between its ends' bits while `h > 4 l`, so that a root's magnitude is
/// reached in O(log B) cuts for a bound of `B` bits, and else at its middle.
///
/// Complexity tradeoff. Each interval costs O(t) products of numbers of O(B) bits, `B` the
/// bits of the 1-norm and the bound, by [`bounds`] and the cut products: no number has the
/// bits of the degree. An interval is cut only while it may hold an integer root and `p` is
/// not shown monotone on it, so the intervals kept at each depth lie about the integer roots
/// of `p` and the real roots of `p'`, under `t` each by Descartes' rule of signs. Measured (the
/// tests below): a polynomial of `t` terms with a root at 4 is linear in `t`, and a cubic
/// whose roots have `B` bits close to linear in `B`. Not proven: the number of intervals kept
/// at a depth, in the worst case; the bound for the method replaced (the chain of `t`
/// derivatives of [Cucker, Koiran and Smale 1999], step 3) was O(t^3) evaluations of numbers
/// of up to `t (B + 1)(B + 2)` bits, reached by `t` terms with a root at 4 (80.5 times the
/// work at 8 times the terms).
fn positive_roots(p: &[(u64, BigInt)], a: BigInt, b: Option<BigInt>) -> Vec<BigInt> {
    if p.len() < 2 {
        return Vec::new();
    }
    let bound = BigInt::one() + p.iter().map(|(_, c)| c.abs()).max().expect("terms");
    let hi = b.map_or(bound.clone(), |b| b.min(bound));
    if let [(_, c0), (g, c1)] = p {
        // A binomial `c0 + c1 x^g` (the piece a gap leaves, as in `(x^n + 1)(x - 4)`) has at
        // most one root above 1: the `g`-th root of `-c0 / c1` where that is an integer, and
        // as `2^g <= x^g` only where `g` is under the bits of the quotient. O(log g)
        // products of numbers of the bits of `c0`, against the O(t) of an interval.
        let q = -c0 / c1;
        let x = ((c0 % c1).is_zero() && q > BigInt::one() && *g < q.bits())
            .then(|| q.nth_root(u32::try_from(*g).expect("under the bits of q")))
            .filter(|x| Pow::pow(x, *g) == q && &a <= x && x <= &hi);
        return x.into_iter().collect();
    }
    // `x p'(x)`, of the sign of `p'` for `x > 0`, on the exponents of `p` above 0.
    let slope: Vec<(u64, BigInt)> = (p[1..].iter())
        .map(|(e, c)| (*e, c * BigInt::from(*e)))
        .collect();
    let mut out = Vec::new();
    let mut open = vec![(a, hi)];
    while let Some((l, h)) = open.pop() {
        if l > h || !may_hold_a_root(p, &l, &h) {
            continue;
        }
        if l == h {
            out.push(l);
            continue;
        }
        // Two integers are tested as two points: a search would test both ends and more.
        if &h - &l == BigInt::one() {
            open.push((h.clone(), h));
            open.push((l.clone(), l));
            continue;
        }
        let b = bounds(&slope, &l);
        if positive_on(&slope, &b, &l, &h, false) || positive_on(&slope, &b, &l, &h, true) {
            out.extend(search(p, &slope, l, h));
            continue;
        }
        let m = match &l * 4 < h {
            true => (BigInt::one() << ((l.bits() + h.bits()) / 2)) - 1,
            false => (&l + &h).div_floor(&BigInt::from(2)),
        };
        open.push((&m + 1, h));
        open.push((l, m));
    }
    out.sort();
    out
}

/// The integer root of `p` in `lo..=hi`, `2 <= lo < hi`, on which `p` is strictly monotone
/// (`slope`, `x p'(x)`, has one sign there), if it has one. With the signs of `p` at the ends
/// ([`sign_at`]) opposite, each step takes Newton's guess from the end of the smaller value
/// and the integers beside it, so that a guess within 1 of the root closes the bracket; a step
/// that does not halve the bracket is followed by a bisection, so a search takes at most twice
/// the bits of `hi - lo` steps. Before those steps, while `hi > 4 lo`, the bracket is cut at
/// the power of 2 whose exponent is the mean of its ends' bits, so a root far below the end
/// Newton's method starts from is reached in O(log B) steps for ends of B bits.
///
/// Complexity tradeoff. Naive: Newton's step from `p(x)` and `p'(x)` written out, numbers of
/// up to `D bits(x)` bits for degree `D`, and O(t) products of them per step. Here the step
/// `x - x Phi / Psi` is read from `Phi = floor(2^s p(x) / x^D)` and `Psi = floor(2^s x p'(x) /
/// x^D)` ([`scaled`]), with `s` twice the bits of `hi`: O(t) divisions of numbers of O(B + s)
/// bits. The floors make the guess exact to within 1 where `|p'|` near the root is at least
/// about `x^(D - 1)`, as at a simple root of a polynomial whose leading term rules there; where
/// it is not, the guess is poor and the bisection bounds the steps. The signs are exact.
fn search(p: &[(u64, BigInt)], slope: &[(u64, BigInt)], lo: BigInt, hi: BigInt) -> Option<BigInt> {
    let (mut lo, mut hi) = (lo, hi);
    let below = sign_at(p, &lo);
    if below == Ordering::Equal {
        return Some(lo);
    }
    match sign_at(p, &hi) {
        Ordering::Equal => return Some(hi),
        above if above == below => return None,
        _ => {}
    }
    let s = 2 * hi.bits();
    let mut bisect = false;
    while &hi - &lo > BigInt::one() {
        if &lo * 4 < hi {
            let x = BigInt::one() << ((lo.bits() + hi.bits()) / 2);
            if lo < x && x < hi {
                match sign_at(p, &x) {
                    Ordering::Equal => return Some(x),
                    o if o == below => lo = x,
                    _ => hi = x,
                }
                continue;
            }
        }
        let width = &hi - &lo;
        let newton = match bisect {
            true => None,
            false => {
                let (fl, fh) = (scaled(p, &lo, s), scaled(p, &hi, s));
                let (x, fx) = if fl.abs() <= fh.abs() {
                    (&lo, fl)
                } else {
                    (&hi, fh)
                };
                let d = scaled(slope, x, s);
                (!d.is_zero()).then(|| x - (x * fx).div_floor(&d))
            }
        };
        let guess = newton.filter(|g| &lo < g && g < &hi);
        let x = guess
            .clone()
            .unwrap_or_else(|| (&lo + &hi).div_floor(&BigInt::from(2)));
        let mut probe = vec![x];
        if guess.is_some() {
            probe.push(probe[0].clone() + 1);
            probe.push(probe[0].clone() - 1);
        }
        for x in probe {
            if !(lo < x && x < hi) {
                continue;
            }
            match sign_at(p, &x) {
                Ordering::Equal => return Some(x),
                o if o == below => lo = x,
                _ => hi = x,
            }
        }
        bisect = (&hi - &lo) * 2 > width;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `p` at `x`, by Horner's rule over the gaps between its exponents.
    fn eval(p: &[(u64, BigInt)], x: &BigInt) -> BigInt {
        let Some((mut last, _)) = p.last().cloned() else {
            return BigInt::zero();
        };
        let mut acc = BigInt::zero();
        for (e, c) in p.iter().rev() {
            acc = acc * Pow::pow(x, last - e) + c;
            last = *e;
        }
        acc * Pow::pow(x, last)
    }

    fn poly(terms: &[(u64, i64)]) -> Sparse {
        Sparse::new(terms.iter().map(|&(e, c)| (e, BigInt::from(c))))
    }

    fn listed(r: Roots) -> Vec<i64> {
        match r {
            Roots::Listed(v) => v.iter().map(|x| i64::try_from(x).expect("small")).collect(),
            Roots::Every => panic!("every member"),
        }
    }

    fn roots(f: &Sparse, lo: i64, hi: i64) -> Vec<i64> {
        listed(integer_roots(
            f,
            Some(&BigInt::from(lo)),
            Some(&BigInt::from(hi)),
        ))
    }

    /// The product of `x - r` for each `r` in `rs`, times `c`.
    fn from_roots(c: i64, rs: &[i64]) -> Sparse {
        let mut p = poly(&[(0, c)]);
        for &r in rs {
            p = p.times(&poly(&[(1, 1), (0, -r)])).expect("small");
        }
        p
    }

    #[test]
    fn a_cubic_with_three_roots() {
        let f = from_roots(1, &[-3, 2, 7]);
        assert_eq!(roots(&f, -100, 100), [-3, 2, 7]);
        assert_eq!(roots(&f, 0, 5), [2]);
        assert_eq!(roots(&f, 3, 6), Vec::<i64>::new());
        assert_eq!(listed(integer_roots(&f, None, None)), [-3, 2, 7]);
    }

    #[test]
    fn zero_one_and_minus_one() {
        // x^3 (x - 1)(x + 1)
        let f = from_roots(1, &[0, 0, 0, 1, -1]);
        assert_eq!(roots(&f, -5, 5), [-1, 0, 1]);
        assert_eq!(roots(&f, 1, 5), [1]);
        assert_eq!(integer_roots(&poly(&[]), None, None), Roots::Every);
        assert_eq!(roots(&poly(&[(0, 7)]), -9, 9), Vec::<i64>::new());
    }

    #[test]
    fn repeated_and_clustered_roots() {
        assert_eq!(roots(&from_roots(3, &[5, 5, 5, -2, -2]), -50, 50), [-2, 5]);
        assert_eq!(
            roots(&from_roots(-1, &[10, 11, 12, 13]), -50, 50),
            [10, 11, 12, 13]
        );
        // No integer root: x^2 - 2, and 4x^2 - 1 with roots ±1/2.
        assert_eq!(roots(&poly(&[(2, 1), (0, -2)]), -50, 50), Vec::<i64>::new());
        assert_eq!(roots(&poly(&[(2, 4), (0, -1)]), -50, 50), Vec::<i64>::new());
    }

    #[test]
    fn a_gap_splits_a_polynomial_of_high_degree() {
        // (x^1000000 + 1)(x - 3) and (x^1000000 - 1)(x + 2): the factor of high degree has
        // roots only among 1 and -1.
        let a = poly(&[(1_000_001, 1), (1_000_000, -3), (1, 1), (0, -3)]);
        assert_eq!(roots(&a, -1_000_000_000, 1_000_000_000), [3]);
        let b = poly(&[(1_000_001, 1), (1_000_000, 2), (1, -1), (0, -2)]);
        assert_eq!(roots(&b, -1_000_000_000, 1_000_000_000), [-2, -1, 1]);
    }

    /// Each polynomial of a deterministic family checked against evaluation at every integer of
    /// `-60..=60`, which holds every root by Cauchy's bound.
    #[test]
    fn agrees_with_evaluation_at_every_member() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for _ in 0..400 {
            let f = match next(2) {
                0 => {
                    let n = 1 + next(5) as usize;
                    let rs: Vec<i64> = (0..n).map(|_| next(21) as i64 - 10).collect();
                    let c = [1, -1, 2, -3][next(4) as usize];
                    from_roots(c, &rs).plus(&poly(&[(0, [0, 0, 1, -1][next(4) as usize])]))
                }
                _ => {
                    let t = 1 + next(5);
                    Sparse::new((0..t).map(|_| (next(9), BigInt::from(next(41) as i64 - 20))))
                }
            };
            let want: Vec<i64> = (-60..=60)
                .filter(|&x| eval(&f.terms, &BigInt::from(x)).is_zero())
                .collect();
            match integer_roots(&f, Some(&BigInt::from(-60)), Some(&BigInt::from(60))) {
                Roots::Every => assert!(f.terms.is_empty()),
                Roots::Listed(_) if f.terms.is_empty() => panic!("zero"),
                got => assert_eq!(listed(got), want, "{f:?}"),
            }
        }
    }

    /// A piece of two terms has the root of its quotient, where that is an integer power.
    #[test]
    fn a_binomial_has_the_root_of_its_quotient() {
        assert_eq!(roots(&poly(&[(5, 2), (0, -64)]), -50, 50), [2]);
        assert_eq!(roots(&poly(&[(3, 1), (0, 8)]), -50, 50), [-2]);
        assert_eq!(roots(&poly(&[(2, 3), (0, -12)]), -50, 50), [-2, 2]);
        assert_eq!(roots(&poly(&[(2, 3), (0, -12)]), -1, 50), [2]);
        assert_eq!(roots(&poly(&[(2, 1), (0, -8)]), -50, 50), Vec::<i64>::new());
        assert_eq!(roots(&poly(&[(2, 4), (0, -1)]), -50, 50), Vec::<i64>::new());
        assert_eq!(roots(&poly(&[(2, 1), (0, 4)]), -50, 50), Vec::<i64>::new());
        // x^64 - 2^64 has the roots 2 and -2; x^65 - 2^64, of an exponent past the bits of
        // the quotient, none.
        let two_64 = BigInt::from(1u8) << 64u32;
        let f = Sparse::new([(64, BigInt::one()), (0, -two_64.clone())]);
        assert_eq!(listed(integer_roots(&f, None, None)), [-2, 2]);
        let f = Sparse::new([(65, BigInt::one()), (0, -two_64)]);
        assert_eq!(listed(integer_roots(&f, None, None)), Vec::<i64>::new());
    }

    /// Roots of 71 bits, negative, and repeated, in a polynomial of 40 terms: `(x - 2^70)
    /// (x + 2^70 + 1) (x - 7)^2 (1 + x^2 + … + x^70)`, the last factor positive everywhere.
    #[test]
    fn large_and_repeated_roots_among_many_terms() {
        let big = BigInt::from(1u8) << 70u32;
        let line = |r: BigInt| Sparse::new([(1, BigInt::one()), (0, -r)]);
        let even = Sparse::new((0..36u64).map(|i| (2 * i, BigInt::one())));
        let f = [
            line(big.clone()),
            line(-&big - 1),
            line(7.into()),
            line(7.into()),
        ]
        .iter()
        .try_fold(even, |f, l| f.times(l))
        .expect("small exponents");
        assert!(f.terms.len() >= 38, "{}", f.terms.len());
        let want = vec![-&big - 1, BigInt::from(7), big.clone()];
        assert_eq!(integer_roots(&f, None, None), Roots::Listed(want));
        let (lo, hi) = (BigInt::from(8), big.clone() - 1);
        assert_eq!(
            integer_roots(&f, Some(&lo), Some(&hi)),
            Roots::Listed(vec![])
        );
    }

    /// Products of up to three planted roots in `-20..=20` and a sparse factor of up to 8
    /// terms, within a random interval: the roots are the planted ones and those of the factor,
    /// found by evaluation within Cauchy's bound of the factor.
    #[test]
    fn agrees_with_planted_roots_over_many_terms() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for _ in 0..300 {
            let t = 1 + next(8);
            let h = Sparse::new((0..t).map(|_| (next(16), BigInt::from(next(7) as i64 - 3))));
            if h.terms.is_empty() {
                continue;
            }
            let rs: Vec<i64> = (0..next(4)).map(|_| next(41) as i64 - 20).collect();
            let f = h.times(&from_roots(1, &rs)).expect("small");
            let (lo, hi) = (next(61) as i64 - 30, next(61) as i64 - 30);
            let norm: i64 = (h.terms.iter())
                .map(|(_, c)| i64::try_from(c.abs()).expect("small"))
                .sum();
            let mut want: Vec<i64> = (-norm - 1..=norm + 1)
                .filter(|&x| eval(&h.terms, &BigInt::from(x)).is_zero())
                .chain(rs)
                .filter(|x| lo <= *x && *x <= hi)
                .collect();
            want.sort();
            want.dedup();
            assert_eq!(roots(&f, lo, hi), want, "{f:?} in {lo}..={hi}");
        }
    }

    #[test]
    fn a_term_is_read_with_its_factors_apart() {
        use crate::term::build::{lit, prim, var};
        let none = |_: &str| None;
        let p = || var("p");
        // (p - 4) * (p - 9) and (p - 1)^1000 within 0..=100.
        let t = prim(
            Prim::Mul,
            vec![
                prim(Prim::Sub, vec![p(), lit(4)]),
                prim(Prim::Sub, vec![p(), lit(9)]),
            ],
        );
        let (lo, hi) = (BigInt::from(0), BigInt::from(100));
        let r = term_roots(&t, "p", &none, Some(&lo), Some(&hi)).map(listed);
        assert_eq!(r, Some(vec![4, 9]));
        let t = prim(
            Prim::Pow,
            vec![prim(Prim::Sub, vec![p(), lit(1)]), lit(1000)],
        );
        let r = term_roots(&t, "p", &none, Some(&lo), Some(&hi)).map(listed);
        assert_eq!(r, Some(vec![1]));
        // p * p - 3 * p - 4, with the constant 3 a name `k` of one value.
        let k = |n: &str| (n == "k").then(|| BigInt::from(3));
        let t = prim(
            Prim::Sub,
            vec![
                prim(
                    Prim::Sub,
                    vec![
                        prim(Prim::Mul, vec![p(), p()]),
                        prim(Prim::Mul, vec![var("k"), p()]),
                    ],
                ),
                lit(4),
            ],
        );
        let r = term_roots(&t, "p", &k, Some(&lo), Some(&hi)).map(listed);
        assert_eq!(r, Some(vec![4]));
        // A power of a sum under a sum is not read, nor a name of no one value.
        let t = prim(
            Prim::Add,
            vec![
                prim(Prim::Pow, vec![prim(Prim::Add, vec![p(), lit(1)]), lit(2)]),
                lit(-9),
            ],
        );
        assert_eq!(term_roots(&t, "p", &none, None, None), None);
        let t = prim(Prim::Sub, vec![p(), var("q")]);
        assert_eq!(term_roots(&t, "p", &none, None, None), None);
    }
}
