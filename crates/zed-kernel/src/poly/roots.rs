//! The integer roots of a polynomial with integer coefficients in one name, within an interval
//! (DESIGN.md sec:constraints, "Reduction", QUESTIONS A81): where an obligation's negation is
//! such a polynomial equal to 0, its integer roots in the name's interval are a listed set, and
//! each written constraint is evaluated at each root as at a listed member.
//!
//! The method is that of F. Cucker, P. Koiran and S. Smale, "A polynomial time algorithm for
//! Diophantine equations in one variable", J. Symbolic Comput. 27(1):21-29, 1999,
//! doi:10.1006/jsco.1998.0242 (checked 2026-11-20 against Crossref and the paper's text). Its
//! Theorem 1: "There is a polynomial time algorithm which given input f ∈ Z\[t\] decides whether
//! f has an integer root and, moreover, the algorithm outputs the set of integer roots of f",
//! in the sparse encoding: polynomial in the number of terms and the bits of the coefficients
//! and exponents, and not in the degree. What is taken from it and what is not:
//!
//! - Step 2 below is its Proposition 2 (section 4, "a simple known fact"): with
//!   `f = r_k + x^(α_(k+1)) q_k`, an integer root `|x| >= 2` is a root of both `q_k` and `r_k`
//!   "provided that α_(k+1) − α_k > 1 + log M_k", `M_k` the largest coefficient of `r_k`. The
//!   test here is its own, with the 1-norm (`2^(m - d) > ||g||_1`), proved in step 2; it
//!   splits at different gaps from the paper's (`log ||g||_1 <= log M_k + log(k + 1)`, so
//!   neither test implies the other). Mutating it to allow a gap one bit smaller fails
//!   `a_gap_splits_a_polynomial_of_high_degree`, `a_binomial_has_the_root_of_its_quotient`
//!   and `agrees_with_evaluation_at_every_member` (checked 2026-11-20).
//! - Step 3 replaces the paper's proof of Theorem 1 (section 3), which isolates the roots of
//!   the chain `p_1, ..., p_k` (each `p_(i+1)` the derivative of `p_i` with its power of `t`
//!   divided out) one level at a time by its Proposition 1, with a branch and bound tried
//!   first. Its number of intervals has no bound in `t` and the bits: on a cubic with no
//!   integer root near `c` and on four roots clustered at `c` it grows as about `c^(1/2)` and
//!   `c^(2/3)` (counts at `positive_roots`). So the branch and bound stops after
//!   `chain_ends(t)` units of work, the chain's own proved count of evaluations at the ends of
//!   stretches, and the chain answers (`chain_roots`, its bound proved there), with integer
//!   cells in place of Proposition 1's isolating intervals.
//! - The paper's remark that a nonzero integer root divides `a_k`, the coefficient of the
//!   least exponent, is not used to list candidates; the search is bounded by 1 plus the
//!   largest coefficient instead (`positive_roots`).
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
//!    by a bisection (`search`). Past `chain_ends(t)` intervals and search steps the partial
//!    result is dropped and the chain of derivatives answers instead (`chain_roots`).
//! 4. A candidate is kept when every other piece is 0 at it.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Pow, Signed, Zero};

use crate::num::nth_root_rem_uint;
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
                    zed_collections::sorted::sort_dedup(&mut l);
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
/// terms). Where the intervals must be narrow to be decided, the count of them grows with `t`:
/// on `(x - r)(1 + x^2 + ... + x^(t - 2))` with `r = 2^40`, `t` terms, `positive_roots`
/// spends exactly `2 log2(t) + 8` units at every `t` from 32 to 131,072 (measured 2026-11-20,
/// BENCH-over-nlogn-prediction item 15), each O(t) operations on numbers of one or two words:
/// so the work is `a t (log2 t + 4)`, 1,842 to 2,216 instructions per term and unit. The
/// enclosure of the slope in the monomial form shows its sign only within `r / (t - 1)` of the
/// root, so one more cut is needed at each doubling of `t` (proved, with the count, at the test
/// `the_count_of_units_on_far_roots_is_proved`, row PROOF-roots-terms-depth). The depth is at
/// most the bits of the bound, so for coefficients of fixed size the count is bounded and the
/// work linear once `log2 t` passes them. Given up: the paper's chain of `t` derivatives,
/// O(t^3) evaluations (80.5 times the work at 8 times the terms), which bounds the
/// number of intervals where this method has no proven bound; and on dense polynomials with many
/// integer roots, as `(x - 2) … (x - 65)`, the chain was about 2 times faster (40 against 80 ms
/// at 64 roots), and on a small cubic as `(x - 4)(x - 5)(x - 7)` about 1.5 times (27 against
/// 42 us), because an interval evaluation in the monomial basis overestimates across a cluster
/// of roots, and each of its numbers is a `BigInt`. Hensel lifting of the roots modulo a prime
/// would cost O(D) per prime and digit, but a repeated root and a prime dividing the discriminant
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
    zed_collections::sorted::sort_dedup(&mut out);
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
/// whose roots have `B` bits close to linear in `B`.
///
/// No bound on the intervals in `t` and `B` holds (plan row ROOTS-interval-bound, proof5,
/// 2026-11-20): the interval evaluations of [`may_hold_a_root`] and [`positive_on`] are in the
/// monomial form, so on `l..=h` of width `w` near `c` they widen by about `w` times the
/// coefficients' size, and a root or a point where `p'` is small near a large `c` is cut down to
/// intervals of width about `|p(x)| / c^2` before either test succeeds. Measured with the
/// count of intervals popped (`the_search_is_bounded_on_families_that_defeat_the_cuts`, before
/// the fallback below): the cubic `x^3 - 3c x^2 + 3(c^2 + 1) x - (c^3 + 3c + 1)`, `p' = 3((x -
/// c)^2 + 1) > 0`, no integer root, took 2,444, 37,398 and 598,260 intervals at `c = 2^16, 2^24,
/// 2^32`, about `c^(1/2)`; four integer roots at `c..=c + 3`, 13,396, 557,282 and 21,739,964
/// (98.6 s), about `c^(2/3)`; `(x - c)^4 + 1` and `(x - c)^4 - 2` as the four roots. Each is
/// exponential in the bits for `t = 4`, so no polynomial in `t` and `B` bounds the count.
///
/// So the branch and bound is stopped after [`chain_ends`]`(t)` units, an interval popped or a
/// step of a [`search`], and [`chain_roots`], the chain of [Cucker, Koiran and Smale 1999]
/// (doi:10.1006/jsco.1998.0242, checked 2026-11-20) with its proved bound, gives the roots
/// instead, the partial list dropped. Proof of the
/// bound of the whole: the branch and bound spends at most `chain_ends(t)` units and the steps
/// of the one search that passes it, at most `2 bits(h - l)` plus O(log B) ([`search`]); each
/// unit is at most 12 passes over the terms, each pass O(t) products or divisions of numbers of
/// O(B + s) bits, `s = 2 bits(h)`: an interval popped is [`bounds`] of `p` and of the slope,
/// [`may_hold_a_root`] and two [`positive_on`], and the two [`sign_at`] (three passes each) of
/// the search it may start, 11 passes; a search step is three [`scaled`] and at most three
/// [`sign_at`], 12. One of the chain's evaluations at a stretch's end ([`chain_ends`],
/// [`eval`]) is one pass of O(t) products, so a unit costs a constant number of them, not one:
/// measured 9.3 to 18.0 of them per unit (`poly::roots::bench`, plan row
/// BENCH-over-nlogn-prediction item 16, 2026-11-20), on the flat cubic and the cluster of four
/// roots at `c = 2^16` to `2^1024`, where the budget's units cost 6.4 to 10.2 times the chain's
/// whole run. The chain then costs what [`chain_roots`] proves, O(t^3) evaluations of numbers
/// of at most `t (B + 1)(B + 2)` bits. So the whole is at most a constant factor times that
/// (measured, the phase before the switch and the chain, 7.4 to 11.2 times the chain alone),
/// polynomial in `t` and `B`. Before item 16 this comment said a unit costs no more than one
/// end evaluation and the whole about twice the chain, which the measurement refutes. Both
/// methods are exact, so the roots do not depend on which answers.
///
/// Complexity tradeoff of the switch: the chain alone is O(t^3) evaluations, 80.5 times the
/// work at 8 times the terms for `t` terms with a root at 4, where the branch and bound is
/// linear (`l01_39_reduced_product::roots::bench`); the branch and bound alone is exponential
/// in `B` on the families above. The budget does not grow with `B`: a budget of the chain's
/// search steps, O(t^2 B), would let the cubic spend O(B) units of O(M(B)) each before the
/// switch, against the chain's O(log B) Newton steps there. It is the chain's own proved bound,
/// not a measured size, so it is not a threshold tuned to a machine. On the families that spend
/// it, the branch and bound so does 6.4 to 10.2 times the chain's work before the chain answers
/// (above). Dividing the budget by the measured cost of a unit in end evaluations would remove
/// most of that, but the divisor would be a constant measured on one machine's arithmetic, so it
/// is not done; charging each unit its proved count of passes, 12, would also remove most of
/// it, at the price of sending to the chain, O(t^3) evaluations, inputs the branch and bound
/// finishes between `chain_ends(t) / 12` and `chain_ends(t)` units.
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
        // products of numbers of the bits of `c0`, against the O(t) of an interval. The root
        // and its remainder by the kernel's `nth_root_rem_uint`, O(M(n)) for a fixed `g`,
        // where num-bigint's `nth_root` is above it (item PERF-wide-odd-base-ratio-9); a zero
        // remainder is an integer root.
        let q = -c0 / c1;
        let x = ((c0 % c1).is_zero() && q > BigInt::one() && *g < q.bits())
            .then(|| {
                nth_root_rem_uint(
                    q.magnitude(),
                    u32::try_from(*g).expect("under the bits of q"),
                )
            })
            .filter(|(_, rem)| rem.is_zero())
            .map(|(x, _)| BigInt::from(x))
            .filter(|x| &a <= x && x <= &hi);
        return x.into_iter().collect();
    }
    // `x p'(x)`, of the sign of `p'` for `x > 0`, on the exponents of `p` above 0.
    let slope: Vec<(u64, BigInt)> = (p[1..].iter())
        .map(|(e, c)| (*e, c * BigInt::from(*e)))
        .collect();
    let budget = chain_ends(p.len());
    let mut spent: u64 = 0;
    let mut out = Vec::new();
    let mut open = vec![(a.clone(), hi.clone())];
    while let Some((l, h)) = open.pop() {
        spent += 1;
        if spent > budget {
            #[cfg(test)]
            tests::CHAINED.with(|c| c.set(c.get() + 1));
            #[cfg(test)]
            tests::UNITS.with(|u| u.set(u.get() + budget));
            return chain_roots(p, a, Some(hi));
        }
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
            out.extend(search(p, &slope, l, h, &mut spent));
            continue;
        }
        let m = match &l * 4 < h {
            true => (BigInt::one() << ((l.bits() + h.bits()) / 2)) - 1,
            false => (&l + &h).div_floor(&BigInt::from(2)),
        };
        open.push((&m + 1, h));
        open.push((l, m));
    }
    #[cfg(test)]
    tests::UNITS.with(|u| u.set(u.get() + spent));
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
fn search(
    p: &[(u64, BigInt)],
    slope: &[(u64, BigInt)],
    lo: BigInt,
    hi: BigInt,
    steps: &mut u64,
) -> Option<BigInt> {
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
        *steps += 1;
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
        for x in probes(newton, &lo, &hi) {
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

/// The points a step of [`search`] or [`chain_search`] tests on the bracket `lo..=hi`, with
/// `hi - lo > 1`: Newton's guess `g`, if any, taken into `lo..=hi`, and `g + 1` and `g - 1`,
/// those strictly inside; else the middle. A guess within 1 of a root then has the integer on
/// the root's far side among the points, so a root in `g..g + 1` closes the bracket in one
/// step, also where `g` is `lo` (or `hi`) itself; before plan row ROOTS-interval-bound a guess
/// equal to an end was dropped with its neighbors and the step bisected, so a root in
/// `lo..lo + 1` took a bisection per bit of `hi - lo`: on `q = p''` of four roots at
/// `c..=c + 3`, 275 steps at `c = 2^256` and 2,073 at `2^2048`. The middle is strictly inside
/// as `hi - lo > 1`, so a step always tests some point and the bisection that follows a weak
/// step still halves the bracket. Tests: `the_search_is_bounded_on_families_that_defeat_the_cuts`
/// and the bench `roots_of_families_that_defeat_the_cuts_scale_in_the_bits`.
fn probes(newton: Option<BigInt>, lo: &BigInt, hi: &BigInt) -> Vec<BigInt> {
    let inside = |x: &BigInt| lo < x && x < hi;
    let near: Vec<BigInt> = match newton {
        Some(g) => {
            let g = g.clamp(lo.clone(), hi.clone());
            [g.clone(), &g + 1, &g - 1]
                .into_iter()
                .filter(|x| inside(x))
                .collect()
        }
        None => Vec::new(),
    };
    match near.is_empty() {
        true => vec![(lo + hi).div_floor(&BigInt::from(2))],
        false => near,
    }
}

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

/// The derivative of `q`, divided by the power of the name that leaves its least exponent 0:
/// on `x > 0` it has the sign of the derivative of `q`, whose least exponent is 0, and one
/// term less.
fn derived(q: &[(u64, BigInt)]) -> Vec<(u64, BigInt)> {
    let e1 = q[1].0;
    (q[1..].iter())
        .map(|(e, c)| (e - e1, c * BigInt::from(*e)))
        .collect()
}

/// The integer roots of `p`, whose least exponent is 0 and constant term not zero, in
/// `a..=b` with `a >= 1`, `b` none for no upper end, by the proof of Theorem 1 of [Cucker,
/// Koiran and Smale 1999], doi:10.1006/jsco.1998.0242, checked 2026-11-20 (section 3; the
/// module doc quotes its Theorem 1): Rolle's theorem over the chain of
/// [`derived`] polynomials, the cells of each member found from those of its successor, the
/// last member, of one term, having none ([`chain_cells`]). Cauchy's bound `1 + max |c|`
/// closes the interval. [`positive_roots`] calls it once its branch and bound has spent
/// [`chain_ends`]`(t)` units.
///
/// Proof of the bound (the departure from the paper is only that cells are integer intervals
/// `c..=c + 1` and its Proposition 1 is replaced by [`chain_search`]). Let the member `q_m`
/// have `m` terms, so its successor has `m - 1` and the last, of 1 term, has no real root on
/// `x > 0` and no cell: `C(1) = 0`. [`chain_cells`] keeps the `C(m - 1)` cells of the
/// successor and adds at most one cell per stretch between them, and only for a stretch on
/// which `q_m` changes sign or is 0 at an end, that is, which holds a real root of `q_m`. The
/// stretches are disjoint (each starts one past the cell before it), so the cells added are at
/// most the positive real roots of `q_m`, under `m` by Descartes' rule of signs (`m` terms
/// have at most `m - 1` sign changes): `C(m) <= C(m - 1) + m - 1`, so `C(m) <= m (m - 1) / 2`.
/// Member `q_m` has at most `C(m - 1) + 1` stretches and is evaluated at both ends of each,
/// which is [`chain_ends`]; it searches at most `m - 1` of them, each search at most
/// `2 (B + 2)` steps and O(log B) cuts at powers of 2 ([`chain_search`]), `B` the bits of the
/// bound. Each evaluation is O(t) products of numbers of at most `D (B + 2)` bits, `D < t (B +
/// 1)` the degree of the piece (module doc, step 2). In all O(t^3) evaluations at stretch ends
/// and O(t^2 B) in searches: polynomial in `t` and `B`, and not in the degree. Tests:
/// `the_chain_agrees_with_the_branch_and_bound`, and the families of
/// `the_search_is_bounded_on_families_that_defeat_the_cuts`.
fn chain_roots(p: &[(u64, BigInt)], a: BigInt, b: Option<BigInt>) -> Vec<BigInt> {
    if p.len() < 2 {
        return Vec::new();
    }
    let bound = BigInt::one() + p.iter().map(|(_, c)| c.abs()).max().expect("terms");
    let hi = b.map_or(bound.clone(), |b| b.min(bound));
    if a > hi {
        return Vec::new();
    }
    let mut chain = vec![p.to_vec()];
    while chain.last().expect("one member").len() > 1 {
        let next = derived(chain.last().expect("one member"));
        chain.push(next);
    }
    let mut below = Vec::new();
    for q in chain.iter().rev().skip(1) {
        below = chain_cells(q, &below, &a, &hi);
    }
    let mut out = Vec::new();
    for c in &below {
        for x in [c.clone(), c + 1] {
            if a <= x && x <= hi && eval(p, &x).is_zero() {
                out.push(x);
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The cells of `q` in `a..=hi`: integers `c` such that each real root of `q` there lies in
/// `c..=c + 1` for some `c`, given `below`, the cells of its [`derived`] successor, between
/// which `q` is monotone. Each of `below` is kept, as `q` may have roots in a cell where its
/// derivative is 0; each stretch between them adds the cell of its sign change, if any.
fn chain_cells(q: &[(u64, BigInt)], below: &[BigInt], a: &BigInt, hi: &BigInt) -> Vec<BigInt> {
    let mut out = below.to_vec();
    let mut stretches = Vec::new();
    let mut u = a.clone();
    for c in below {
        if &u <= c {
            stretches.push((u.clone(), c.clone()));
        }
        u = u.max(c + 1);
    }
    if &u <= hi {
        stretches.push((u, hi.clone()));
    }
    for (u, v) in stretches {
        let (fu, fv) = (eval(q, &u), eval(q, &v));
        if fu.is_zero() {
            out.push(u.clone());
        }
        if fv.is_zero() {
            out.push(v.clone());
        }
        if fu.signum() * fv.signum() < BigInt::zero() {
            out.push(chain_search(q, u, v, fu, fv));
        }
    }
    out.sort();
    out.dedup();
    out
}

/// A cell `c` in `lo..hi` at which `q`, monotone on `lo..=hi`, changes sign or is 0, given
/// its values `flo` and `fhi`, of opposite signs, at the ends. Each step takes Newton's guess
/// from the end of the smaller value and the integer beside it toward the root, so that a
/// guess within 1 of a simple root closes the bracket; a step that does not halve the bracket
/// is followed by a bisection, so a search takes at most twice the bits of `hi - lo` steps.
/// Before those steps, while `hi > 4 max(lo, 1)`, the bracket is cut at the power of 2 whose
/// exponent is the mean of its ends' bits, so a root far below the end Newton's method starts
/// from is reached in O(log B) steps for ends of B bits.
fn chain_search(
    q: &[(u64, BigInt)],
    mut lo: BigInt,
    mut hi: BigInt,
    mut flo: BigInt,
    mut fhi: BigInt,
) -> BigInt {
    let slope: Vec<(u64, BigInt)> = (q.iter())
        .filter(|(e, _)| *e > 0)
        .map(|(e, c)| (e - 1, c * BigInt::from(*e)))
        .collect();
    let mut bisect = false;
    while &hi - &lo > BigInt::one() {
        // Complexity tradeoff: a bracket over many orders of magnitude is first narrowed by
        // the magnitude of its ends, at `2^((bits(lo) + bits(hi)) / 2)`, until `hi <= 4 lo`:
        // O(log B) steps for ends of B bits. Newton's method from an end far from the root
        // moves by a constant factor per step, and bisection halves the bracket, so either
        // alone takes O(B) steps of O(B)-bit arithmetic here.
        let floor = lo.clone().max(BigInt::one());
        if &floor * 4 < hi {
            let x = BigInt::one() << ((floor.bits() + hi.bits()) / 2);
            if lo < x && x < hi {
                let fx = eval(q, &x);
                if fx.is_zero() {
                    return x;
                }
                match fx.signum() == flo.signum() {
                    true => (lo, flo) = (x, fx),
                    false => (hi, fhi) = (x, fx),
                }
                continue;
            }
        }
        let width = &hi - &lo;
        let newton = match bisect {
            true => None,
            false => {
                let (x, fx) = if flo.abs() <= fhi.abs() {
                    (&lo, &flo)
                } else {
                    (&hi, &fhi)
                };
                let d = eval(&slope, x);
                (!d.is_zero()).then(|| (x * &d - fx).div_floor(&d))
            }
        };
        for x in probes(newton, &lo, &hi) {
            if !(lo < x && x < hi) {
                continue;
            }
            let fx = eval(q, &x);
            if fx.is_zero() {
                return x;
            }
            if fx.signum() == flo.signum() {
                (lo, flo) = (x, fx);
            } else {
                (hi, fhi) = (x, fx);
            }
        }
        bisect = (&hi - &lo) * 2 > width;
    }
    lo
}

/// The bound proved at [`chain_roots`] on the evaluations it makes at the ends of stretches,
/// for `t` terms: `2 * sum over m in 2..=t of (C(m - 1) + 1)`, `C(k) = k (k - 1) / 2`, which
/// is `2 ((t - 2)(t - 1) t / 6 + t - 1)` (`sum over j in 1..=n of j (j - 1) / 2 = (n + 1) n
/// (n - 1) / 6`, at `n = t - 1`; a product of three consecutive integers is divisible by 6, so
/// the division is exact); 14 for a cubic. Computed in `u128`: `t^3 < 2^128` for `t < 2^42`,
/// and `t` terms of at least 32 bytes each are under memory far below that. A sum past
/// `u64::MAX` is cut to it, which no count of work reaches. Each of `positive_roots`'s units,
/// an interval or a search step, is at most 12 passes of O(t) products or divisions of numbers
/// of O(B + s) bits (proof at [`positive_roots`]), and one such evaluation is one pass of O(t)
/// products: so the branch and bound, stopped past this many units, costs a constant factor
/// times this part of the chain's bound, not at most it. Measured (`poly::roots::bench`,
/// 2026-11-20): a unit costs 9.3 to 18.0 end evaluations on the families that reach the budget.
/// Tests: `chain_ends_is_the_sum_it_bounds`.
fn chain_ends(t: usize) -> u64 {
    let t = t as u128;
    if t < 2 {
        return 0;
    }
    let ends = 2 * ((t - 2) * (t - 1) * t / 6 + t - 1);
    u64::try_from(ends).unwrap_or(u64::MAX)
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod tests {
    use super::*;

    thread_local! {
        /// How many times [`positive_roots`] has handed over to [`chain_roots`] on this thread.
        pub(super) static CHAINED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// The units [`positive_roots`] has spent on this thread, a handover to the chain counted
        /// as the whole budget.
        pub(super) static UNITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    }

    fn big(terms: &[(u64, BigInt)]) -> Sparse {
        Sparse::new(terms.iter().cloned())
    }

    /// The product of `x - r` for each `r` in `rs`.
    fn from_big_roots(rs: &[BigInt]) -> Sparse {
        let mut p = poly(&[(0, 1)]);
        for r in rs {
            p = p
                .times(&big(&[(1, BigInt::one()), (0, -r.clone())]))
                .expect("small");
        }
        p
    }

    /// The families that defeat the cuts of the branch and bound (`positive_roots`: its count
    /// of intervals grows as `c^(1/2)` and `c^(2/3)` on them), at `c = 2^k`: each is answered
    /// exactly, by the chain, at sizes where the branch and bound alone would take more than
    /// 2^40 intervals.
    #[test]
    fn the_search_is_bounded_on_families_that_defeat_the_cuts() {
        let chained = || CHAINED.with(|c| c.get());
        for k in [16u64, 64, 128, 256] {
            let c = BigInt::one() << k;
            let c2 = &c * &c;
            // `p' = 3((x - c)^2 + 1) > 0`; the one real root is not an integer.
            let cubic = big(&[
                (0, -(&c2 * &c + 3 * &c + 1)),
                (1, 3 * (&c2 + 1)),
                (2, -3 * &c),
                (3, BigInt::one()),
            ]);
            let four = from_big_roots(&[c.clone(), c.clone(), c.clone(), c.clone()]);
            let cluster: Vec<BigInt> = (0..4).map(|i| &c + i).collect();
            let near: Vec<BigInt> = (0..4).map(|i| -(&c + 2 * i)).collect();
            let cases: [(Sparse, Vec<BigInt>); 5] = [
                (cubic, vec![]),
                (from_big_roots(&cluster), cluster.clone()),
                (four.plus(&poly(&[(0, 1)])), vec![]),
                (four.plus(&poly(&[(0, -2)])), vec![]),
                (from_big_roots(&near), near.iter().rev().cloned().collect()),
            ];
            for (f, want) in cases {
                let before = chained();
                assert_eq!(
                    integer_roots(&f, None, None),
                    Roots::Listed(want),
                    "k = {k}: {f:?}"
                );
                assert!(
                    chained() > before,
                    "k = {k}: the chain did not answer {f:?}"
                );
            }
        }
        // Roots at the powers of 2 up to `2^m`, and one past each: alternating signs, and
        // roots where the cuts of the branch and bound fall.
        for m in [4u64, 16, 48] {
            let at: Vec<BigInt> = (1..=m).map(|j| BigInt::one() << j).collect();
            let past: Vec<BigInt> = at.iter().map(|x| x + 1).collect();
            for rs in [at, past] {
                let mut want = rs.clone();
                want.sort();
                assert_eq!(
                    integer_roots(&from_big_roots(&rs), None, None),
                    Roots::Listed(want)
                );
            }
        }
    }

    /// The chain alone, the branch and bound with its switch, and evaluation at every member
    /// of `2..=60` agree on random polynomials whose constant term is not 0.
    #[test]
    fn the_chain_agrees_with_the_branch_and_bound() {
        let (mut rng, _) = crate::seed::Rng::fresh("the_chain_agrees_with_the_branch_and_bound");
        let mut next = |m: u64| rng.below_u64(m);
        let hi = BigInt::from(60);
        for _ in 0..400 {
            let f = match next(2) {
                0 => {
                    let n = 1 + next(6) as usize;
                    let rs: Vec<i64> = (0..n).map(|_| 2 + next(20) as i64).collect();
                    let c = [1, -1, 2, -3][next(4) as usize];
                    from_roots(c, &rs).plus(&poly(&[(0, [0, 0, 1, -1][next(4) as usize])]))
                }
                _ => {
                    let t = 1 + next(6);
                    let c0 = BigInt::from([1, -1, 6, -24][next(4) as usize]);
                    Sparse::new(
                        (0..t)
                            .map(|_| (1 + next(9), BigInt::from(next(41) as i64 - 20)))
                            .chain([(0, c0)]),
                    )
                }
            };
            let p = f.terms();
            if p.first().is_none_or(|(e, _)| *e != 0) {
                continue;
            }
            let want: Vec<BigInt> = (2..=60)
                .map(BigInt::from)
                .filter(|x| eval(p, x).is_zero())
                .collect();
            let chain = chain_roots(p, BigInt::from(2), Some(hi.clone()));
            assert_eq!(chain, want, "the chain on {f:?}");
            let branch = positive_roots(p, BigInt::from(2), Some(hi.clone()));
            assert_eq!(branch, want, "the branch and bound on {f:?}");
        }
    }

    /// [`chain_ends`] is the sum it is written as, for every `t` up to 300.
    #[test]
    fn chain_ends_is_the_sum_it_bounds() {
        let cells = |k: u64| k * k.saturating_sub(1) / 2;
        for t in 0..300u64 {
            let sum: u64 = (2..=t).map(|m| 2 * (cells(m - 1) + 1)).sum();
            assert_eq!(chain_ends(t as usize), sum, "t = {t}");
        }
        assert_eq!(chain_ends(4), 14);
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

    /// Each polynomial of a random family checked against evaluation at every integer of
    /// `-60..=60`, which holds every root by Cauchy's bound.
    #[test]
    fn agrees_with_evaluation_at_every_member() {
        let (mut rng, _) = crate::seed::Rng::fresh("agrees_with_evaluation_at_every_member");
        let mut next = |m: u64| rng.below_u64(m);
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
        let (mut rng, _) = crate::seed::Rng::fresh("agrees_with_planted_roots_over_many_terms");
        let mut next = |m: u64| rng.below_u64(m);
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
            zed_collections::sorted::sort_dedup(&mut want);
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

    /// The count of units on far roots (row PROOF-roots-terms-depth). On
    /// `p = (x - r)(1 + x^2 + ... + x^(t - 2))`, `r = 2^40`, `t = 2^tau` terms (`-r` on the even
    /// powers, 1 on the odd), [`positive_roots`] spends exactly `2 tau + 8` units, the count
    /// [`integer_roots`] states, and the reflected polynomial 1 more. The proof, for
    /// `8 <= t <= 2^37`, with `l..=h` an interval the branch and bound pops:
    ///
    /// 1. Where `h < r`, [`may_hold_a_root`] drops it. The carry bounds of `p` at `l`
    ///    ([`bounds`]) satisfy `B_odd <= (B_even + r) / l` and `B_even <= (B_odd + 1) / l`, so
    ///    `B_even <= (l + r) / (l^2 - 1)`. Horner's rule starts from the top term, 1, and the
    ///    next step encloses `U = x - r` in `l - r..=h - r`, which misses `-B_even..=B_even` when
    ///    `r - h > (l + r) / (l^2 - 1)`: at `l = 2` (only with `h = 2^21 - 1`) the right side is
    ///    about `r / 3` and the left about `r`, and for `l >= 2^21` the right side is below 1.
    /// 2. The slope `q = x p'(x)` has `(t - 1)` on `x^(t - 1)` and `-(t - 2) r` on `x^(t - 2)`.
    ///    For `l > 3t + 2` its carry bound at the even powers is 0 and at the top
    ///    `B_top = floor((t - 2) r / l)`, so [`positive_on`] returns true at its first step
    ///    exactly when `t - 1 > B_top`, that is when `l > r (t - 2) / (t - 1)`. Otherwise its
    ///    next value is `(t - 1) l - (t - 2) r`, which is not 0 (`t - 1` is odd and prime to
    ///    `t - 2`, so it divides no `(t - 2) 2^40`), so it is below the bound 0 and the test
    ///    returns false. The negated test starts at `-(t - 1) >= -B_top`, and its next value
    ///    `-(t - 1) h + (t - 2) r`, with `h >= r`, passes the cap `(t - 2) r + 1` and is cut to
    ///    `-1 < 0`: false. On the intervals of step 3 with `l <= 2^36` both tests fail the same
    ///    way, the negative values being cut at the cap.
    /// 3. The cuts. While `4 l < h` the cut is `2^((bits l + bits h) / 2) - 1`: from `2..=r + 1`
    ///    the right parts start at `2^21`, `2^31`, `2^36` and `2^39`, four cuts, each costing the
    ///    unit of the cut interval and the unit of its left part, dropped by (1): 8 units. Then
    ///    bisection of `l..=r + 1` with `d = r - l`: `d_0 = 2^39`, `d_(k + 1) = ceil((d_k - 1) /
    ///    2) - 1`, so `d_1 = 2^38 - 1` and `d_k = 2^(39 - k) - 2` for `k >= 2`, again 2 units a
    ///    cut. By (2) the slope is shown positive first where `d_k < r / (t - 1)`: true at
    ///    `k = tau - 1`, `2^(40 - tau) - 2 < 2^40 / (2^tau - 1)`, and false at `k = tau - 2`, as
    ///    `(2^(41 - tau) - 2)(2^tau - 1) >= 2^40` is `2^40 + 2 >= 2^(41 - tau) + 2^(tau + 1)`,
    ///    true for `1 <= tau <= 39`. That is `2 (tau - 1)` units, 1 for the interval the slope
    ///    decides, and 1 for the one [`search`] step, whose Newton guess from `r + 1` lands
    ///    within 1 of `r`: `8 + 2 (tau - 1) + 2 = 2 tau + 8`.
    /// 4. The reflected polynomial `p(-x)` has `-r` on the even powers and `-1` on the odd, all
    ///    negative, so its one interval is dropped in 1 unit.
    ///
    /// For an `r` of `B` bits the first phase halves the bits between the ends at each cut,
    /// `O(log B)` cuts, and the count is `2 log2 t + O(log B)`. The test checks the count at
    /// `tau = 3` to 14, and the trace of the intervals at `tau = 3` was read against (3): eight
    /// units on the powers of 2, two cuts, the interval the slope decides.
    #[test]
    fn the_count_of_units_on_far_roots_is_proved() {
        let r = BigInt::one() << 40u32;
        for tau in 3..=14u32 {
            let t = 1u64 << tau;
            let mut terms = Vec::new();
            for i in 0..t / 2 {
                terms.push((2 * i, -r.clone()));
                terms.push((2 * i + 1, BigInt::one()));
            }
            UNITS.with(|u| u.set(0));
            let roots = integer_roots(&big(&terms), None, None);
            let units = UNITS.with(|u| u.get());
            assert_eq!(roots, Roots::Listed(vec![r.clone()]), "tau = {tau}");
            // `2 tau + 8` in the search above 1, 1 for the reflected polynomial.
            assert_eq!(units, u64::from(2 * tau + 9), "tau = {tau}");
        }
    }
}
