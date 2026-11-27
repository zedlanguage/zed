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

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::num::{div_floor_int, div_rem_uint, mul_int, nth_root_rem_uint, pow_uint};
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
    BigInt::from(pow_uint(x.magnitude(), g)).min(cap + 1)
}

/// The interval tests of the branch and bound, written once and built for two kinds of number:
/// `BigInt`, here, and `i128` in [`small`], where every number they form is proved to fit.
/// Each kind has its own `capped_pow`, `mul_int` and `div_floor_int`; the bodies are the same
/// text. `$v` is the visibility given to each function.
///
/// Complexity tradeoff: on `BigInt` the products and quotients are the kernel's
/// ([`mul_int`], [`div_floor_int`], [`pow_uint`] in `capped_pow`), which take num-bigint's
/// below their measured crossovers and transforms, O(n log n) a product, above them. Below
/// the crossovers the work is mostly num-bigint's, whose method is chosen by word counts
/// (num-bigint 0.4.8, `biguint/multiplication.rs` and `biguint/division.rs`, read
/// 2026-11-22): a product is long multiplication, `n^2`, while its shorter factor has at most
/// 32 words, Karatsuba's, `n^1.585`, up to 256, and Toom-3, `n^1.465`, past that; a quotient
/// is Knuth's algorithm D, `n^2`, unless the dividend has over 128 words and the divisor over
/// 64, and then Burnikel and Ziegler's, whose cost is its products'. So 8 times the bits cost
/// from `8^1.465 = 21.0` to 64 times the work of one product, by the size, whatever the count
/// of steps (plan row ROOTS-cubic-bits-bytes; measurements at the benchmark
/// `l01_39_reduced_product::roots::bench::roots_scale_in_the_degree_and_in_the_bits`).
macro_rules! interval_tests {
    ($v:vis $n:ty) => {
        /// `floor(n / x^g)` for `x >= 2`, with the power capped above `|n|`, past which the
        /// quotient is 0 or -1 by the sign of `n` alone.
        $v fn floor_over_pow(n: &$n, x: &$n, g: u64) -> $n {
            div_floor_int(n, &capped_pow(x, g, &n.abs()))
        }

        /// The carry bounds of `p` at `l >= 2`: for each `k`, `B_k = floor(sum over i < k of
        /// |c_i| l^(e_i - e_k))`, `B_0 = 0`. Write
        /// `U_k(x) = sum over i >= k of c_i x^(e_i - e_k)`, the terms from the `k`th up
        /// divided by the `k`th power. At an integer root `x >= l`, `p(x) = 0` gives
        /// `x^(e_k) U_k(x) = -(the terms below the k-th)`, so the carry `-U_k(x)` is an
        /// integer of magnitude at most `sum over i < k of |c_i| x^(e_i - e_k)`, which
        /// falls as `x` grows: so `|U_k(x)| <= B_k`. `B_k = floor((B_(k-1) +
        /// |c_(k-1)|) / l^(e_k - e_(k-1)))`, as `floor(floor(z) / L) = floor(z / L)` for an
        /// integer `L >= 1`. O(t) divisions of numbers of at most the bits of the 1-norm.
        $v fn bounds(p: &[(u64, $n)], l: &$n) -> Vec<$n> {
            let mut out = Vec::with_capacity(p.len());
            out.push(<$n>::zero());
            for k in 1..p.len() {
                let below = &out[k - 1] + p[k - 1].1.abs();
                out.push(floor_over_pow(&below, l, p[k].0 - p[k - 1].0));
            }
            out
        }

        /// Whether `p` may have an integer root in `l..=h`, `2 <= l <= h`: false only where
        /// none lies there, and, where `l == h`, true exactly where `l` is a root. Horner's rule
        /// from the top term encloses `U_k` over the interval, `U_k = c_k + x^(e_(k+1) - e_k)
        /// U_(k+1)`, and each enclosure is cut to `-B_k..=B_k` ([`bounds`]): an empty one leaves
        /// no root, and as `B_0 = 0` the last asks that `p` itself may be 0. A product past `cap
        /// = B_k + |c_k| + 1` is cut to `cap`, which changes no cut enclosure, so each number
        /// keeps the bits of the 1-norm and the interval's ends, whatever the degree. O(t)
        /// products of such numbers.
        ///
        /// The cut also does what the gap split does: where `B_k = 0`, `U_k` must be 0 at a
        /// root.
        $v fn may_hold_a_root(p: &[(u64, $n)], l: &$n, h: &$n) -> bool {
            let b = bounds(p, l);
            let n = p.len();
            let (mut lo, mut hi) = (p[n - 1].1.clone(), p[n - 1].1.clone());
            for k in (0..n).rev() {
                if k + 1 < n {
                    let g = p[k + 1].0 - p[k].0;
                    let cap = &b[k] + p[k].1.abs() + 1;
                    let (pl, ph) = (capped_pow(l, g, &cap), capped_pow(h, g, &cap));
                    let least = if lo.is_negative() {
                        mul_int(&lo, &ph)
                    } else {
                        mul_int(&lo, &pl)
                    };
                    let most = if hi.is_negative() {
                        mul_int(&hi, &pl)
                    } else {
                        mul_int(&hi, &ph)
                    };
                    let within = |v: $n| v.clamp(-&cap, cap.clone()) + &p[k].1;
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

        /// Whether `q` (`-q` where `negate`) is positive at every real point of `l..=h`, `2 <= l
        /// <= h`; where `l == h`, exactly whether it is positive at `l`. The least value of
        /// each `U_k` over the interval is carried down from the top term (it depends on the
        /// least value of `U_(k+1)` alone); where it passes `B_k` (`b`, the [`bounds`] of `q` at
        /// `l`), `U_k` outweighs every term below and `q` is positive, and where it falls under
        /// `-B_k` the proof is given up. As in [`may_hold_a_root`], a product past `cap` decides
        /// the step either way, so it is cut there. O(t) products of numbers of the bits of the
        /// 1-norm and the interval's ends.
        $v fn positive_on(q: &[(u64, $n)], b: &[$n], l: &$n, h: &$n, negate: bool) -> bool {
            let c = |k: usize| if negate { -&q[k].1 } else { q[k].1.clone() };
            let mut lo = c(q.len() - 1);
            for k in (0..q.len()).rev() {
                if k + 1 < q.len() {
                    let g = q[k + 1].0 - q[k].0;
                    let cap = &b[k] + q[k].1.abs() + 1;
                    let x = if lo.is_negative() { h } else { l };
                    lo = mul_int(&lo, &capped_pow(x, g, &cap)).clamp(-&cap, cap.clone()) + c(k);
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
        $v fn sign_at(q: &[(u64, $n)], x: &$n) -> Ordering {
            let b = bounds(q, x);
            if positive_on(q, &b, x, x, false) {
                Ordering::Greater
            } else if positive_on(q, &b, x, x, true) {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        }
    };
}

interval_tests!(BigInt);

/// The interval tests in `i128`, for a polynomial and its slope whose coefficients are under
/// [`small::BOUND`] in magnitude and an interval within `2..=BOUND`.
///
/// Proof that no number overflows. Let `M < 2^60` bound the magnitudes of the coefficients of
/// the polynomial and of its slope, and let every point `x` be in `2..=2^60` (the branch and
/// bound's intervals lie in `a..=1 + max |c| <= 2^60`). [`bounds`]: the exponents rise
/// strictly, so `e_k - e_i >= k - i`, and `l >= 2`, so `B_k = floor(sum over i < k of |c_i|
/// l^(e_i - e_k)) <= floor(sum over j >= 1 of M 2^(-j)) < M`, and `below = B_(k-1) +
/// |c_(k-1)| < 2M`. `capped_pow(x, g, cap)` is called with `cap < 2M < 2^61` (by
/// [`may_hold_a_root`] and [`positive_on`], `cap = B_k + |c_k| + 1 <= (M - 1) + M + 1`; by
/// `floor_over_pow`, `cap = |n| = below`), and forms `x^g` only where
/// `(bits(x) - 1) g < bits(cap) <= 61`; as `x >= 2`, `bits(x) <= 2 (bits(x) - 1)`, so
/// `x^g < 2^(bits(x) g) <= 2^(2 (bits(x) - 1) g) <= 2^120`, and it returns at most
/// `cap + 1 <= 2^61`. The enclosures of [`may_hold_a_root`] and [`positive_on`] start at a
/// coefficient, at most `M`, and each step clamps to `-cap..=cap` before adding a coefficient,
/// so they stay within `cap + M < 2^62`; a product of one of them and a capped power is under
/// `2^62 2^61 = 2^123`. Every sum is of two numbers under `2^123`. So all numbers are under
/// `2^124 < 2^127`.
///
/// The bound is on the greatest coefficient, not on the 1-norm, so the number of terms does not
/// decide which kind runs: `t` terms of a fixed size take the `i128` path at every `t`, and a
/// benchmark over `t` (`roots_are_linear_in_the_number_of_terms`) times one kind at both of its
/// sizes. A bound on the 1-norm put its slope (coefficients `2i 2^40`, 1-norm about `t^2 2^40`)
/// on the `i128` path at 1,024 terms and the `BigInt` path at 8,192.
///
/// Complexity tradeoff: the same steps as the `BigInt` tests, so the same O(t) per interval;
/// what falls is the constant of each step, which no longer allocates. Measured 2026-11-22 on a
/// Colab VM, processor time, against the `BigInt` path (ROOTS-small-constant): 13 against 27 us
/// on the cubic `(x-4)(x-5)(x-7)`, 11 against 33 us on a cubic with roots in -100..=100, 0.11
/// against 0.74 ms on `(x-2)...(x-17)`, 45 against 154 ms on 8,192 terms with a root at 2^40;
/// equal on 64 roots and past `i128`, where the time is in the evaluations and in `BigInt`.
// The shared bodies clone as `BigInt` needs; on `i128` the clone is a copy.
#[allow(clippy::clone_on_copy)]
mod small {
    use std::cmp::Ordering;

    use num_bigint::BigInt;
    use num_integer::Integer;
    use num_traits::Zero;
    use zed_numtheory::BitLen;

    /// The bound on the coefficients and the points of the proof above: `2^60`.
    pub(super) const BOUND: i128 = 1 << 60;

    /// `p` in `i128`, where each coefficient is under [`BOUND`] in magnitude.
    pub(super) fn words(p: &[(u64, BigInt)]) -> Option<Vec<(u64, i128)>> {
        p.iter()
            .map(|(e, c)| {
                let c = i128::try_from(c).ok().filter(|c| c.abs() < BOUND)?;
                Some((*e, c))
            })
            .collect()
    }

    /// `super::capped_pow` in `i128`: `x^g` where it is at most `cap`, and `cap + 1` where it
    /// is above. `x >= 2`. The power fits (proof at the module).
    fn capped_pow(x: &i128, g: u64, cap: &i128) -> i128 {
        let bits = |v: &i128| u64::from(v.unsigned_abs().bit_len());
        if (bits(x) - 1).checked_mul(g).is_none_or(|b| b >= bits(cap)) {
            return cap + 1;
        }
        let g = u32::try_from(g).expect("under bits(cap), so under 64");
        x.pow(g).min(cap + 1)
    }

    /// `a * b`, which fits (proof at the module).
    fn mul_int(a: &i128, b: &i128) -> i128 {
        a * b
    }

    /// `floor(a / b)` for `b` not zero.
    fn div_floor_int(a: &i128, b: &i128) -> i128 {
        Integer::div_floor(a, b)
    }

    interval_tests!(pub(super) i128);
}

/// A polynomial and its slope in `i128`, for the tests of [`small`].
struct Words {
    p: Vec<(u64, i128)>,
    slope: Vec<(u64, i128)>,
}

impl Words {
    /// `p` and `slope` in `i128`, where every coefficient of both is under [`small::BOUND`] in
    /// magnitude.
    fn of(p: &[(u64, BigInt)], slope: &[(u64, BigInt)]) -> Option<Words> {
        Some(Words {
            p: small::words(p)?,
            slope: small::words(slope)?,
        })
    }

    /// These and the interval `l..=h` in `i128`, where both ends are in `2..=small::BOUND`, as
    /// the proof at [`small`] asks.
    fn at(&self, l: &BigInt, h: &BigInt) -> Option<(&Words, i128, i128)> {
        let word = |x: &BigInt| {
            i128::try_from(x)
                .ok()
                .filter(|x| (2..=small::BOUND).contains(x))
        };
        Some((self, word(l)?, word(h)?))
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
/// [`sign_at`], 12; a step of NEWREFINE ([`refine`]) at most 11 [`sign_at`] and 6 [`scaled`],
/// 39, counted as 4 units; a step of [`doubling`] in a search is two [`scaled`] of numbers of fewer
/// bits, 2, and the step from its guess one [`scaled`] at full precision, one at fewer bits
/// and two [`sign_at`], 8, each counted as a unit (plan row ROOTS-doubling-newton). One of the
/// chain's evaluations at a stretch's end ([`chain_ends`], [`eval`]) is one pass of O(t)
/// products, so a unit costs a constant number of them, not one: measured 9.3 to 18.0 of them
/// per unit (`poly::roots::bench`, plan row BENCH-over-nlogn-prediction item 16, 2026-11-20),
/// on the flat cubic and the cluster of four roots at `c = 2^16` to `2^1024`, where the
/// budget's units cost 6.4 to 10.2 times the chain's whole run. The chain then costs what
/// [`chain_roots`] proves, O(t^3) evaluations of numbers of at most `t (B + 1)(B + 2)` bits.
/// So the whole is at most a constant factor times that (measured, the phase before the switch
/// and the chain, 7.4 to 11.2 times the chain alone), polynomial in `t` and `B`. Before item
/// 16 this comment said a unit costs no more than one end evaluation and the whole about twice
/// the chain, which the measurement refutes. Both methods are exact, so the roots do not
/// depend on which answers.
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
///
/// The bound from above (plan row ROOTS-dense-cluster-constant, cross-review
/// XR-lazy-and-kernel-batch-1 round 1). On `(x - 2) … (x - 65)` 1,152 of the 1,293 intervals
/// popped (89%) lay above the largest root, between 66 and Cauchy's bound `1 + max |c|` of 306
/// bits, where the monomial form's interval test fails by the cancellation of the alternating
/// coefficients (Gemini's `verify_req2`, rerun by the orchestrator): the cluster bound never
/// counted that work. So once the units spent reach [`HORNER_COST`]` D^2 / t`, the cost of one
/// test of [`positive_from`] in units, the least power of 2 past every root and then the least
/// integer `u` past them are found by that test ([`horner_bound`]), and the intervals are cut to
/// `u - 1`. Ski rental: the test is bought once the branch and bound has spent what one test
/// costs, so the whole is at most about twice the cheaper of the two on every input whose
/// bound search runs a few tests. Sparse inputs of high degree are left as they were: the
/// trigger needs `spent t >= HORNER_COST D^2` and the cap of [`horner_bound`] `D <= B`, and
/// `roots_are_linear_in_the_number_of_terms` (`t = D = 8192`) finishes in 34 units (test
/// `the_bound_from_above_leaves_sparse_inputs_as_they_were`).
fn positive_roots(p: &[(u64, BigInt)], a: BigInt, b: Option<BigInt>) -> Vec<BigInt> {
    positive_roots_by(p, a, b, Horner::Built).0
}

/// When [`positive_roots_by`] runs [`horner_bound`]: never, at its first interval, or as built,
/// once `spent t >= HORNER_COST D^2`. The first two are for `crossover roots-horner`, which
/// measures [`HORNER_COST`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Horner {
    Off,
    AtStart,
    Built,
}

/// The cost of one test of [`positive_from`] on a polynomial of degree `D`, `D (D + 1) / 2`
/// products of a coefficient by `u` and sums, in units of the branch and bound of
/// [`positive_roots`] per term (a unit is at most 12 passes of `t` products): the constant `C`
/// of the trigger `spent t >= C D^2`. Measured by `crossover roots-horner` (zed-benches), on
/// the clusters `(x - 2) … (x - k - 1)`, `k` from 8 to 128: every `C` from 0 to 6.56 gives a
/// worst ratio of 1.00 to the cheaper of the two, and the worst ratio rises past it (2.08 at
/// 6.6, 9.9 past 33.6; local, load 12.5 to 14.7, 2026-11-27). 1, the value of the ski-rental
/// argument at [`positive_roots`], is inside that range. Built itself, the bound found once the
/// trigger fires, measured as a third arm (`crossover roots-horner-built`, Codex's B1 of round
/// 2, instructions, local, load 13.6, 2026-11-27): 1.29 times the cheaper of the two at `k` 4,
/// falling to 1.10 at 16, 1.04 at 64 and 1.006 at 128; on the sparse `(x - 4) (x^n + 1)`, `n`
/// 64, 1,000 and 8,192, 1.004, where the bound from the first interval costs 1.01 times no
/// bound. The bench holds it to 2, the ski-rental bound.
const HORNER_COST: f64 = 1.0;

/// The units [`horner_bound`] charges for one test of [`positive_from`]: `D (D + 1) / 2`
/// products and sums, in groups of `t`, each group under one pass of a unit.
fn horner_units(d: u64, t: usize) -> u64 {
    (d * (d + 1) / 2).div_ceil(t as u64).max(1)
}

/// Whether `p(x)` has the sign of its leading coefficient at every real `x >= u`, shown by the
/// coefficients of `p(u + y)` in `y`: each of that sign or 0, and the constant term not 0
/// (Budan's test of the shift by `u`; with them so, `p(u + y)` for `y >= 0` is a sum of terms of
/// one sign, the constant term among them, so not 0). Ruffini's scheme: pass `i` adds `u` times
/// each coefficient into the one below it, from the top down to `i`, and leaves the `i`-th
/// coefficient of `p(u + y)` final, so the test stops at the first of the wrong sign.
/// The test is the case of no sign variation of Descartes' rule of signs, applied to `p(u + y)`:
/// Li and Paulson, arXiv:1811.11093 §3.2, Theorem 3.8 (`descartes_sign`, proved in
/// Isabelle/HOL), the positive roots counted by "the number of sign variations of the
/// coefficient sequence of P" and at most that count (verification/bib.md, LiPaulson). The
/// paper supports only this test; the synthetic division above and the trigger and cap of
/// [`horner_bound`] are proved here.
/// `D (D + 1) / 2` products of a coefficient by `u` at most; every number is a partial sum of
/// `sum |c_k| (1 + u)^k`, of at most `B + D bits(u + 1) + bits(t)` bits for coefficients of `B`
/// bits.
fn positive_from(p: &[(u64, BigInt)], u: &BigInt) -> bool {
    #[cfg(test)]
    tests::HORNER_TESTS.with(|n| n.set(n.get() + 1));
    let (d, lead) = p.last().expect("terms");
    let d = usize::try_from(*d).expect("a degree under the cap");
    let flip = lead.is_negative();
    let mut c = vec![BigInt::zero(); d + 1];
    for (e, v) in p {
        c[*e as usize] = if flip { -v } else { v.clone() };
    }
    for i in 0..=d {
        for j in (i..d).rev() {
            let add = u * &c[j + 1];
            c[j] += add;
        }
        if c[i].is_negative() || (i == 0 && c[i].is_zero()) {
            return false;
        }
    }
    true
}

/// The least integer `u >= 2` with [`positive_from`]`(p, u)`, if it is found below `hi` under
/// the cap: the powers of 2 from 2 up to the first that passes, then the bisection between it
/// and the one before (the test passes at every point above one where it passes: `p(u' + y) =
/// p(u + ((u' - u) + y))`, a polynomial of coefficients of one sign taken at a shift `u' - u >=
/// 0`, keeps them so). Every real root of `p` is then below `u`, so `u - 1` bounds the integers
/// searched, not the real roots: `(2x - 5)(x + 1)` passes at `u = 3`, and its root 5/2 lies
/// above 2 (Codex, cross-review XR-lazy-and-kernel-batch-1 round 2, B1). At most `2 bits(u)`
/// tests, each charged [`horner_units`] to `spent`.
///
/// The cap: a test at `u` is run only where `D bits(u) <= 2 B`, `B` the most bits of a
/// coefficient, so that each number of a test has at most `B + D bits(u + 1) + bits(t) <= 4 B +
/// bits(t)` bits (as `D <= B` from the cap at `u = 2`): a test is then `D (D + 1) / 2` products
/// of numbers of O(B) bits, `horner_units` groups of `t`, each within the cost of a unit, and the
/// proof of [`positive_roots`]'s bound holds with these units in its count. Without the cap a
/// root near `2^B` (as in `(x - 2^B)(x^(D - 1) + 1)`) would make the shifted coefficients of `D
/// B` bits. The decision's cap read `D bits(u) <= B`; on `(x - 2) … (x - 65)` that refuses the
/// test at 66 (`64 * 7 = 448 > 305`, `B` 305 bits there, as Codex's check computed), so the
/// factor is 2, the least power of 2 that admits it.
fn horner_bound(p: &[(u64, BigInt)], hi: &BigInt, spent: &mut u64) -> Option<BigInt> {
    let d = p.last().map_or(0, |(d, _)| *d);
    let b = p.iter().map(|(_, c)| c.bits()).max().unwrap_or(0);
    let units = horner_units(d, p.len());
    let under_cap = |u: &BigInt| d.checked_mul(u.bits()).is_some_and(|w| w <= 2 * b);
    let mut test = |u: &BigInt| {
        *spent += units;
        positive_from(p, u)
    };
    let mut u = BigInt::from(2);
    let mut below = BigInt::one();
    loop {
        if &u >= hi || !under_cap(&u) {
            return None;
        }
        if test(&u) {
            break;
        }
        below = u.clone();
        u <<= 1u32;
    }
    while &u - &below > BigInt::one() {
        let mid: BigInt = (&u + &below) >> 1u32;
        match test(&mid) {
            true => u = mid,
            false => below = mid,
        }
    }
    Some(u)
}

/// [`positive_roots`] with [`horner_bound`] run as `horner` says, and the units spent.
pub(super) fn positive_roots_by(
    p: &[(u64, BigInt)],
    a: BigInt,
    b: Option<BigInt>,
    horner: Horner,
) -> (Vec<BigInt>, u64) {
    if p.len() < 2 {
        return (Vec::new(), 0);
    }
    let bound = BigInt::one() + p.iter().map(|(_, c)| c.abs()).max().expect("terms");
    let mut hi = b.map_or(bound.clone(), |b| b.min(bound));
    if let [(_, c0), (g, c1)] = p {
        // A binomial `c0 + c1 x^g` (the piece a gap leaves, as in `(x^n + 1)(x - 4)`) has at
        // most one root above 1: the `g`-th root of `-c0 / c1` where that is an integer, and
        // as `2^g <= x^g` only where `g` is under the bits of the quotient. O(log g)
        // products of numbers of the bits of `c0`, against the O(t) of an interval. The root
        // and its remainder by the kernel's `nth_root_rem_uint`, O(M(n)) for a fixed `g`,
        // where num-bigint's `nth_root` is above it (item PERF-wide-odd-base-ratio-9); a zero
        // remainder is an integer root. The quotient is the kernel's division of the
        // magnitudes ([`div_rem_uint`], O(M(n)) past its crossover, where num-bigint's `/` and
        // `%` are Knuth's or Burnikel and Ziegler's; plan row ROOTS-binomial-div), and `-c0 /
        // c1` is above 0 only where `c0` and `c1` have opposite signs.
        let (q, r) = div_rem_uint(c0.magnitude(), c1.magnitude());
        let x = (r.is_zero() && c0.sign() != c1.sign() && q > BigUint::one() && *g < q.bits())
            .then(|| nth_root_rem_uint(&q, u32::try_from(*g).expect("under the bits of q")))
            .filter(|(_, rem)| rem.is_zero())
            .map(|(x, _)| BigInt::from(x))
            .filter(|x| &a <= x && x <= &hi);
        return (x.into_iter().collect(), 0);
    }
    // `x p'(x)`, of the sign of `p'` for `x > 0`, on the exponents of `p` above 0.
    let slope: Vec<(u64, BigInt)> = (p[1..].iter())
        .map(|(e, c)| (*e, c * BigInt::from(*e)))
        .collect();
    let words = Words::of(p, &slope);
    let budget = chain_ends(p.len());
    let mut spent: u64 = 0;
    let mut out = Vec::new();
    let mut open = vec![(a.clone(), hi.clone())];
    // The trigger of the bound from above, `spent t >= HORNER_COST D^2`; tried once.
    let d = p.last().map_or(0, |(d, _)| *d) as f64;
    let trigger = HORNER_COST * d * d / p.len() as f64;
    let mut bounded = horner == Horner::Off;
    while let Some((l, mut h)) = open.pop() {
        spent += 1;
        if spent > budget {
            #[cfg(test)]
            tests::CHAINED.with(|c| c.set(c.get() + 1));
            #[cfg(test)]
            tests::UNITS.with(|u| u.set(u.get() + budget));
            let roots = match a <= hi {
                true => chain_roots(p, a, Some(hi)),
                false => Vec::new(),
            };
            return (roots, budget);
        }
        if !bounded && (horner == Horner::AtStart || spent as f64 >= trigger) {
            bounded = true;
            if let Some(u) = horner_bound(p, &hi, &mut spent) {
                hi = u - 1;
                open.retain_mut(|(ol, oh)| {
                    if *oh > hi {
                        *oh = hi.clone();
                    }
                    *ol <= hi
                });
                if h > hi {
                    h = hi.clone();
                }
            }
        }
        if l > h {
            continue;
        }
        #[cfg(test)]
        tests::BOXES.with(|v| {
            if let Some(v) = v.borrow_mut().as_mut() {
                v.push((l.clone(), h.clone()));
            }
        });
        let at = words.as_ref().and_then(|w| w.at(&l, &h));
        let may_hold = match &at {
            Some((w, l, h)) => small::may_hold_a_root(&w.p, l, h),
            None => may_hold_a_root(p, &l, &h),
        };
        if !may_hold {
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
        let monotone = match &at {
            Some((w, l, h)) => {
                let b = small::bounds(&w.slope, l);
                small::positive_on(&w.slope, &b, l, h, false)
                    || small::positive_on(&w.slope, &b, l, h, true)
            }
            None => {
                let b = bounds(&slope, &l);
                positive_on(&slope, &b, &l, &h, false) || positive_on(&slope, &b, &l, &h, true)
            }
        };
        if monotone {
            out.extend(search(p, &slope, words.as_ref(), l, h, &mut spent, budget));
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
    (out, spent)
}

/// The integer root of `p` in `lo..=hi`, `2 <= lo < hi`, on which `p` is strictly monotone
/// (`slope`, `x p'(x)`, has one sign there), if it has one; `steps` counts the units spent,
/// and `budget` bounds the units the scale of a Newton ratio may raise them to (the scale
/// loop below). With the signs of `p` at the ends
/// ([`sign_at`]) opposite, each step is a step of Sagraloff's NEWREFINE ([`refine`]): a
/// boundary test, then the secant zeros of `p / p'` through the quarter points, each tested on
/// a grid of `N` cells, `N` squared on a success and its square root on a bisection. A step
/// leaves at most half the bracket, so a search takes at most the bits of `hi - lo` steps, and
/// `O(log log)` of the bracket over the cluster's size near a cluster of roots, where the
/// earlier step, Newton's from an end and a bisection after a weak one, took a step per bit
/// (plan row ROOTS-fallback-worst-case). Before those steps, while `hi > 4 lo`, the
/// bracket is cut at the power of 2 whose exponent is the mean of its ends' bits, so a root
/// far below the end Newton's method starts from is reached in O(log B) steps for ends of B
/// bits. Once the cuts end, [`doubling`] gives a guess from the top bits of the bracket at
/// doubling precision, and one Newton step from it at full precision and its neighbor close
/// the bracket; the steps above go on from the bracket left where they do not (plan row
/// ROOTS-doubling-newton; test `a_search_evaluates_at_full_precision_at_most_three_times`).
///
/// Complexity tradeoff. Naive: `p(x)` and `p'(x)` written out for the ratio `v = p / p'`,
/// numbers of up to `D bits(x)` bits for degree `D`, and O(t) products of them per point.
/// Here `v = x Phi / Psi` is read from `Phi = floor(2^s p(x) / x^D)` and `Psi = floor(2^s x
/// p'(x) / x^D)` ([`scaled`]), with `s` twice the bits of `hi`: O(t) divisions of numbers of
/// O(B + s) bits. The floors make `v` exact to within 1 where `|p'|` near the root is at least
/// about `x^(D - 1)`, as at a simple root of a polynomial whose leading term rules there; where
/// it is not, the guesses are poor and the bisection bounds the steps. The signs are exact.
fn search(
    p: &[(u64, BigInt)],
    slope: &[(u64, BigInt)],
    words: Option<&Words>,
    lo: BigInt,
    hi: BigInt,
    steps: &mut u64,
    budget: u64,
) -> Option<BigInt> {
    let sign_at = |p: &[(u64, BigInt)], x: &BigInt| match words.and_then(|w| w.at(x, x)) {
        Some((w, x, _)) => small::sign_at(&w.p, &x),
        None => sign_at(p, x),
    };
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
    // `n` of [`refine`]'s `N = 2^(2^n)`, from `N = 4`.
    let mut level = 1u32;
    let (mut tried, mut newton) = (false, false);
    #[cfg(test)]
    let mut wide = false;
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
        // Once the cuts end, so `hi <= 4 lo` and the root's top bits are its ends' (proof and
        // tradeoff at [`doubling`]).
        if !tried && &lo * 4 >= hi {
            tried = true;
            #[cfg(test)]
            {
                wide = hi.bits() > DOUBLING_BASE;
                if wide {
                    tests::SEARCHES.with(|n| n.set(n.get() + 1));
                }
            }
            // Each call of the step is a unit: two [`scaled`] at reduced precision, under the
            // 12 passes at full precision of a unit ([`positive_roots`]).
            let mut calls = 0u64;
            let start: BigInt = (&lo + &hi) >> 1u32;
            let guess = doubling_on()
                .then(|| {
                    doubling(&lo, &hi, &start, below, |e, y| {
                        calls += 1;
                        search_level(p, slope, &hi, e, y)
                    })
                })
                .flatten();
            *steps += calls;
            if let Some((e, y)) = guess {
                // The guess of [`doubling`] is a Newton step at full precision: the one below
                // is not taken again.
                newton = true;
                // Newton's step from `x0 = 2^e y` at full precision, `Phi` of `x0` exact to the
                // floor as in the loop below and `Psi` from the level of `e`, `2^(s - s_e + f)
                // Psi_e(y)` (`s_e` the scale of that level and `f` its [`lead_shift`], as the
                // level's slope stands `f` bits low), then `g` and its neighbor toward the root
                // by [`sign_at`]: one [`scaled`] at full precision, one at the level's, and two
                // signs, 8 passes, the loop pass's one unit.
                let x0 = &y << e;
                let s_e = 2 * ((&hi >> e) + 1u32).bits();
                let f = lead_shift(p, hi.bits() - e);
                let d = scaled(&truncated(slope, e, f), &y, s_e) << (s - s_e + f);
                #[cfg(test)]
                full_eval(wide);
                let fx = scaled(p, &x0, s);
                if !d.is_zero() {
                    let g =
                        (&x0 - div_floor_int(&mul_int(&x0, &fx), &d)).clamp(lo.clone(), hi.clone());
                    for near in [false, true] {
                        let x = match near {
                            false => g.clone(),
                            true if lo == g => &g + 1,
                            true if hi == g => &g - 1,
                            true => break,
                        };
                        if !(lo < x && x < hi) {
                            continue;
                        }
                        #[cfg(test)]
                        full_eval(wide);
                        match sign_at(p, &x) {
                            Ordering::Equal => return Some(x),
                            o if o == below => lo = x,
                            _ => hi = x,
                        }
                    }
                }
                #[cfg(test)]
                if wide && &hi - &lo > BigInt::one() {
                    tests::FALLBACKS.with(|n| n.set(n.get() + 1));
                }
                continue;
            }
            #[cfg(test)]
            if wide {
                tests::FALLBACKS.with(|n| n.set(n.get() + 1));
            }
        }
        // Once, where [`doubling`] gave no guess (an upper end of at most `DOUBLING_BASE`
        // bits, or no certified sign): Newton's step from the end where `|p|` is less, and the
        // integers beside its guess, 1 unit, the step before plan row
        // ROOTS-fallback-worst-case. Where the guess lands within 1 of a simple root near an
        // end, this closes the bracket, where NEWREFINE, starting from `N = 4`, takes `O(log
        // log w)` steps of 4 units: on the far roots of
        // `the_count_of_units_on_far_roots_is_proved` (`w` about `2^37`) [`positive_roots`]
        // spent 23 units at `tau = 3` without it, against the 14 proved there (measured
        // 2026-11-27, local). It adds one step to NEWREFINE's bound.
        if !newton {
            newton = true;
            #[cfg(test)]
            (0..3).for_each(|_| full_eval(wide));
            let (fl, fh) = (scaled(p, &lo, s), scaled(p, &hi, s));
            let (x, fx) = match fl.abs() <= fh.abs() {
                true => (&lo, fl),
                false => (&hi, fh),
            };
            let d = scaled(slope, x, s);
            if !d.is_zero() {
                let g = (x - div_floor_int(&mul_int(x, &fx), &d)).clamp(lo.clone(), hi.clone());
                for x in [g.clone(), &g + 1, &g - 1] {
                    if !(lo < x && x < hi) {
                        continue;
                    }
                    #[cfg(test)]
                    full_eval(wide);
                    match sign_at(p, &x) {
                        Ordering::Equal => return Some(x),
                        o if o == below => lo = x,
                        _ => hi = x,
                    }
                }
            }
            continue;
        }
        // A step of NEWREFINE, 4 units ([`refine`]): at most 11 [`sign_at`] of 3 passes each
        // and 3 ratios of two [`scaled`] each, 39 passes, under 4 units of 12 (the loop's head
        // charged one). `v = p / p'` is `x Phi / Psi`, `Phi` and `Psi` [`scaled`] at a scale of
        // at least `s`.
        *steps += 3;
        let mut side = |x: &BigInt| {
            #[cfg(test)]
            full_eval(wide);
            match sign_at(p, x) {
                Ordering::Equal => Side::Root,
                o if o == below => Side::Below,
                _ => Side::Above,
            }
        };
        // The scale of `v`. Each of `Phi` and `Psi` is below its value `2^s p(x) / x^D` (and
        // `2^s x p'(x) / x^D`) by under `t`, one floor a term, so `x Phi / Psi` is within `(x
        // / |Psi|) t (1 + |v| / x)` of `v`, under `2 t x / |Psi|` where `|v| <= x`, and so
        // within `1/2` once `|Psi| >= 4 t x`: `bits(x) + bits(t) + 3` bits. Near a cluster
        // `p'(x)` is far below `x^(D - 1)` and `Psi` at the scale `s` loses those bits: on
        // family B of `newrefine_takes_log_log_steps_on_a_cluster` (a quintic, `x` about
        // `2^n`, `s = 2n`) `Psi` was 0 or a few bits, and [`refine`] took 18, 42 and 82 steps at
        // n = 256, 512 and 1,024, a step per bit of the bracket, where the exact values of
        // [`chain_search`] then took 7, 9 and 13 (measured 2026-11-27, local; with the step
        // as the source states it, 10, 13 and 17, and this scale the same). So the scale is raised
        // by the bits `Psi` lacks, or doubled where it is 0, until `Psi` has them; at `s >= D
        // bits(x) + need` it has them, as `x p'(x)` is a nonzero integer (`p` is monotone on
        // the bracket), so the scale stays under `2 (D bits(x) + need)`, the bits of the exact
        // values. Each scale past `s` is charged `ceil(s' / s)` units more, as the numbers have
        // about `s'` bits more than the 1-norm in place of `s`.
        //
        // The cap `top = D bits(x) + need` saturates at `u64::MAX` (cross-review
        // XR-lazy-and-kernel-batch-1 round 2, Gemini B.2; it was an unchecked product). It can
        // pass 2^64 on an input of [`integer_roots`], as a sparse degree costs no memory:
        // 1. [`split`] cuts at every gap of at least the bits of the 1-norm of the terms below
        //    it, so in a piece of `t` terms and 1-norm of `B` bits each gap is under `B` and
        //    `D < t B`;
        // 2. the brackets of [`positive_roots`] lie in `2..=1 + max |c|`, so `bits(x) <= B + 1`;
        // 3. so `D bits(x) + need < t B (B + 1) + B + log2(t) + 5`, past 2^64 once `t B^2` is
        //    about 2^64: `t = 2^16` terms and one coefficient of 2 MB (`B = 2^24`), or `t = 16`
        //    and `B = 2^30`. The test
        //    `search_on_a_sparse_high_degree_polynomial_does_not_overflow_the_scale_cap`
        //    reaches the product with `D = 2^62` on `2048..=4096`.
        // `at` is bounded by `top` and by `budget`, the units [`positive_roots_by`] allows: a
        // raise whose charge would pass it is not taken. A capped scale cannot change an answer:
        // `ratio` only places the cells of [`refine`], each then tested by an exact sign
        // ([`sign_at`]), and [`refine`] takes a rounded value or `None` as it takes any other.
        let mut extra = 0u64;
        let base = *steps;
        let need = |x: &BigInt| x.bits() + (p.len() as u64).ilog2() as u64 + 4;
        let mut ratio = |x: &BigInt| {
            let need = need(x);
            let top = (p.last().map_or(0, |(d, _)| *d))
                .saturating_mul(x.bits())
                .saturating_add(need);
            let mut at = s;
            let (at, d) = loop {
                #[cfg(test)]
                (0..2).for_each(|_| full_eval(wide));
                let d = scaled(slope, x, at);
                if d.bits() >= need || at >= top {
                    break (at, d);
                }
                let next = match d.is_zero() {
                    true => at.saturating_mul(2),
                    false => at.saturating_add(need - d.bits()),
                }
                .min(top);
                let cost = next.div_ceil(s);
                if base.saturating_add(extra).saturating_add(cost) > budget {
                    break (at, d);
                }
                at = next;
                extra = extra.saturating_add(cost);
            };
            (!d.is_zero()).then(|| (mul_int(x, &scaled(p, x, at)), d))
        };
        let degree = p.last().map_or(0, |(d, _)| *d);
        let found = refine(&mut lo, &mut hi, &mut level, degree, &mut side, &mut ratio);
        *steps = steps.saturating_add(extra);
        if let Some(x) = found {
            return Some(x);
        }
    }
    None
}

/// Where a point of a bracket lies by the sign of the polynomial there: on a root, or on the
/// side of the root of the bracket's lower end (its sign), or of its upper end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Side {
    Root,
    Below,
    Above,
}

/// One step of Sagraloff's algorithm NEWREFINE (arXiv:1401.6011, "A near-optimal algorithm
/// for computing real roots of sparse polynomials", Section 3; plan row
/// ROOTS-fallback-worst-case, cross-review XR-lazy-and-kernel-batch-1 rounds 1 and 2) on the
/// bracket `a..b` (`lo..hi`), `w = b - a > 1`, of one root, with `N = 2^(2^n)`. `side` gives
/// the side of a point by an exact sign, and `ratio(x)` the value of `v = q / q'` at `x` as a
/// quotient, `None` where `q'(x)` is 0; it may be rounded, as it only places the intervals the
/// exact signs then test. `degree` is the degree `n` of the source's conditions (here `D`, as
/// the step's `n` is the level of `N`).
///
/// The source's step, quoted (Section 3, the source's TeX; equation numbers as printed, Section
/// 3's equations being numbered (3.1) on):
///
/// > Newton-Test_signat: Consider the points `\xi_{1}:=a+\frac{1}{4}\cdot w(I)`,
/// > `\xi_{2}:=a+\frac{1}{2}\cdot w(I)`, `\xi_{3}:=a+\frac{3}{4}\cdot w(I)` [...] The points
/// > `\xi_j^*` define values `v_{j}:=\frac{p(\xi_{j}^{*})}{p'(\xi_{j}^{*})}`. Then, for the
/// > three distinct pairs of indices `i,j\in\{1,2,3\}` with `i<j`, [...] We stop doubling `L`
/// > for a particular pair `(i,j)` if we can either verify that (3.3) `|v_{i}|,|v_{j}|>w(I)`
/// > or `|v_{i}-v_{j}|<\frac{w(I)}{4n}` or that (3.4) `|v_{i}|,|v_{j}|<2\cdot w(I)` and
/// > `|v_{i}-v_{j}|>\frac{w(I)}{8n}`. If (3.3) holds, we discard the pair `(i,j)`. Otherwise,
/// > [...] we can derive an approximation `\tilde{\lambda}_{i,j}` of (3.5)
/// > `\lambda_{i,j}:=\xi_{i}^{*}+\frac{\xi^{*}_{j}-\xi^{*}_{i}}{v_{j}-v_{j}}\cdot v_{i}` with
/// > `|\tilde{\lambda}_{i,j}-\lambda_{i,j}|\le \frac{1}{32N_{I}}`. If
/// > `\tilde{\lambda}_{i,j} \not\in[a,b]`, we discard the pair `(i,j)`. Otherwise, let
/// > `\ell_{i,j}:=\floor{\frac{4N_I\cdot(\tilde{\lambda}_{i,j}-a)}{w(I)}}`. [...]
/// > `I_{i,j}:=(a+\max(0,\ell_{i,j}-1)\cdot\frac{w(I)}{4N_{I}},
/// > a+\min(4N_{I},\ell_{i,j}+2)\cdot\frac{w(I)}{4N_{I}})`. [...] `I'` is isolating for `\xi`
/// > if and only if `p(a_{i,j}^{*})\cdot p(b_{i,j}^{*})<0`, hence, if the latter inequality is
/// > fulfilled, we return `I'`. Otherwise, we discard `(i,j)`. [...] If the
/// > Newton-Test_signat succeeds, we replace `\mathcal{A}=(I,N_I)` by
/// > `\mathcal{A}:=(I',N_{I'})`, with `N_{I'}:=N_I^2`. If the Newton-Test_signat fails, we
/// > continue with the so-called Boundary-Test_signat. [...] Let `m_{\ell}:=a+\frac{w(I)}{2N_{I}}`
/// > and `m_{r}:=b-\frac{w(I)}{2N_{I}}` [...] If `p(a)\cdot p(m_{\ell}^{*})<0`, then
/// > `I':=(a,m_{\ell})` isolates `\xi`, and thus, we return `I'`. If `p(b)\cdot p(m_{r}^{*})<0`,
/// > we return `I'=(m_{r},b)`. [...] If the Boundary-Test_signat succeeds, then
/// > `\mathcal{A}=(I,N_I)` is replaced by `\mathcal{A}:=(I',N_{I'})`, with `N':=N_I^2`. If the
/// > Newton-Test_signat as well as the Boundary-Test_signat fail, [...] we replace
/// > `\mathcal{A}=(I,N_I)` by `\mathcal{A}:=(I',N_{I'})`, with `I'=(a,m^*)` and
/// > `N_{I'}:=\max(4,\sqrt{N_{I}})` [or `I'=(m^*,b)`].
///
/// and, of the points `\xi_j^*` and the like: "For now, the reader may assume that we always
/// choose `m_i=m`, and that exact arithmetic over rational numbers is used." This step takes
/// `m_i = m` throughout. Three readings of the source:
///
/// - (3.5) as printed has the denominator `v_j - v_j`, which is 0. The line through `(xi_i,
///   v_i)` and `(xi_j, v_j)` has its zero at `xi_i + (xi_j - xi_i) v_i / (v_i - v_j)`, the
///   printed form with the denominator `v_i - v_j`, and that is the form used here (Gemini's
///   finding of round 1 named the sign; round 2 found the printed `v_j - v_j`).
/// - With exact values the doubling of `L` is not needed, and the source leaves open which of
///   (3.3) and (3.4) a run verifies first where both hold. A pair goes on here where (3.3)
///   fails (`|v_i|, |v_j| > w(I)` read as both) or (3.4) holds: every pair some run of the
///   source goes on with, so the test succeeds wherever a run of the source's succeeds at the
///   same points (a pair more only tests one more interval, by exact signs). Measured: the
///   reading "goes on only where `max(|v_i|, |v_j|) <= w` and `|v_i - v_j| >= w / (4n)`" took
///   the same steps on the cluster tests but one bisection more on family B at n = 256.
/// - The values are exact here (or rounded by `ratio`), so `\tilde{\lambda}_{i,j}` is `lambda`
///   itself and `ell` its exact floor.
///
/// The one change: the bracket's ends are integers, as `side` and `ratio` take integers (an
/// exact sign at a rational point of a sparse polynomial of degree `D` costs numbers of `D`
/// times the point's bits, and `D` goes to `2^62` here, test
/// `search_on_a_sparse_high_degree_polynomial_does_not_overflow_the_scale_cap`). So each point
/// `a + l w / (4N)` of the source is `g(l) = a + floor(l w / (4N))`: `xi_1, xi_2, xi_3` are
/// `g(N), g(2N), g(3N)`, the ends of `I_ij` are `g(max(0, l - 1))` and `g(min(4N, l + 2))`, and
/// `m_l, m_r` are `g(2)` and `g(4N - 2)`; `g(0) = a`, `g(4N) = b`. Where `4N` divides `w` every
/// `g(l)` is the source's point and the step is the source's step; else each point is below
/// the source's by less than 1. The bisection is at `xi_2 = g(2N)`, the source's `m^*`. With
/// it, `4N` is cut to `2^max(4, bits(w))`, at most `2 w` where `w >= 8`: the grid's cells are
/// then at least `1/2` wide, so `I_ij`, 3 cells, has two distinct integer ends, where on a grid of
/// cells far under 1 the points fall on the same integers and the test fails. Measured
/// 2026-11-27, local, the most steps on the tests named below (n = 256 to 8,192 on Codex's
/// family of `a_cluster_at_an_end_of_a_chain_stretch_takes_log_log_steps`, 2^8 to 2^15 on
/// the two families of `newrefine_takes_log_log_steps_on_a_cluster`):
///
/// | `4N` cut to   | Codex's family     | the two families                  |
/// |---------------|--------------------|-----------------------------------|
/// | no cut        | 6, 7, 21, 20, 26   | 10, 13, 16, 19, 26, 29, 34, 37    |
/// | `2^bits(w)/2` | 5, 8, 9, 10, 10    | 12, 14, 16, 20, 28, 31, 35, 38    |
/// | `2^bits(w)`   | 6, 8, 8, 9, 10     | 10, 13, 17, 19, 27, 29, 34, 39    |
/// | `2^bits(w)*2` | 6, 7, 15, 17, 9    | 10, 13, 15, 19, 26, 29, 34, 37    |
///
/// `2^bits(w)` is taken: within 2 of no cut on the two families, and the fewest on Codex's.
///
/// Proved here: (1) the root stays in the bracket, as every new bracket is taken on the exact
/// signs at its ends (`Below` at the lower, `Above` at the upper), so the answer does not
/// depend on `ratio`; (2) where `w > 4` each step leaves at most `ceil(w / 2)` (an `I_ij` spans
/// at most 3 of the `4N >= 16` cells, `3 w / 16 + 1 < w / 2`; the boundary test leaves
/// `ceil(w / (2N)) <= w / 8 + 1 < w / 2`; the bisection `ceil(w / 2)`), and a bracket of width
/// at most 4 is bisected, so a search takes at most `bits(w) + 2` steps; (3) the shift `cells`
/// is at most `max(4, bits(w))`, whatever `n` is (`n` grows by 1 a step, saturating, and a
/// shift past 63 is taken as no bound before the cut).
///
/// Not proved here: the source's iteration bound. Its Theorem 7 ("NEWREFINE needs
/// `O(var(p, I_0) (log n + log(tau + L)))` many iterations", `var(p, I_0)` the sign changes of
/// `p` on `I_0` after a Moebius transformation, at most `k - 1` for a `k`-nomial, `tau` the
/// bits of the coefficients, `L` the bits of the width sought) rests on its Lemma 6, which it
/// takes from Sagraloff and Mehlhorn (arXiv:1308.4088, Lemmas 20 and 23) for the exact points.
/// Where `4N` divides `w` and is not cut the step is that step; that the rounding by less than
/// 1 and the cut elsewhere keep the bound is not proved (Codex's B2 of round 2: from the exact
/// signs alone the bound is the `bits(w) + 2` of (2)). The counts are measured: on
/// `(x - R)^3 - S^3` on `R + 1..=R + H` (`R = 2^n + 2^(n/4)`, `H = 2^(n/8)`, `S = 2^(n/16)`) the old
/// step, Newton's method from an end with a bisection after a weak step, took 32, 64 and 128
/// steps at `n` = 256, 512 and 1,024 (Gemini's `verify_req3`, rerun by the orchestrator), and
/// this step at most 10, 13, 17, 19, 27, 29, 34 and 39 at `n` = 2^8 to 2^15 on the two
/// families of test `newrefine_takes_log_log_steps_on_a_cluster`: about 4 more a doubling of
/// `n`, a line in `log2 n`, so `log log w` as Theorem 7's `log (tau + L)` gives (`tau` and `L`
/// about `n`).
///
/// The cost of a step on `w > 4`: 3 signs and 3 ratios at the quarter points, 2 signs for each
/// of the 3 pairs, 2 signs for the boundary test, so at most 11 signs and 3 ratios (each ratio
/// a value and a slope): 17 evaluations. In [`search`] a sign is a [`sign_at`], 3 passes, and
/// a ratio two [`scaled`], so a step is at most 39 passes, and [`search`] charges it 4 units
/// of 12 passes (Claude's B-4 of round 2: the 2 units charged before were under the cost).
fn refine(
    lo: &mut BigInt,
    hi: &mut BigInt,
    n: &mut u32,
    degree: u64,
    side: &mut dyn FnMut(&BigInt) -> Side,
    ratio: &mut dyn FnMut(&BigInt) -> Option<(BigInt, BigInt)>,
) -> Option<BigInt> {
    let w = &*hi - &*lo;
    if w <= BigInt::from(4) {
        let mid: BigInt = (&*lo + &*hi) >> 1u32;
        match side(&mid) {
            Side::Root => return Some(mid),
            Side::Below => *lo = mid,
            Side::Above => *hi = mid,
        }
        #[cfg(test)]
        tests::BISECTIONS.with(|c| c.set(c.get() + 1));
        *n = n.saturating_sub(1).max(1);
        return None;
    }
    // `4N = 2^cells`, and the source's point `a + l w / (4N)` is `g(l)`.
    let cells = (1u64.checked_shl(*n))
        .map_or(u64::MAX, |c| c + 2)
        .min(w.bits().max(4));
    let a = lo.clone();
    let g = |l: &BigInt| &a + ((l * &w) >> cells);
    let four_n = BigInt::one() << cells;
    let quarter = BigInt::one() << (cells - 2);
    let narrowed = 'tests: {
        // The Newton test.
        let xs = [g(&quarter), g(&(&quarter << 1u32)), g(&(&quarter * 3u32))];
        let mut at = Vec::with_capacity(3);
        for x in &xs {
            let s = side(x);
            if s == Side::Root {
                return Some(x.clone());
            }
            // `v = c / d` with `d > 0`.
            at.push((
                s,
                ratio(x).map(|(c, d)| if d.is_negative() { (-c, -d) } else { (c, d) }),
            ));
        }
        let four_degree = BigInt::from(degree) << 2u32;
        for (i, j) in [(0, 1), (0, 2), (1, 2)] {
            // `q'` 0 at a point: `v` is unbounded there, and (3.3) holds.
            let (Some((ci, di)), Some((cj, dj))) = (&at[i].1, &at[j].1) else {
                continue;
            };
            // On where (3.3) fails or (3.4) holds, with `|v_i - v_j| = |c_i d_j - c_j d_i| /
            // (d_i d_j)`; either makes the denominator of (3.5) nonzero.
            let den = mul_int(ci, dj) - mul_int(cj, di);
            // `|v| <= w` is `|c| <= w d`, and `|v| < 2 w` is `|c| < 2 w d`.
            let w_d = |c: &BigInt, d: &BigInt| (c.abs(), mul_int(&w, d));
            let [(ai, wi), (aj, wj)] = [w_d(ci, di), w_d(cj, dj)];
            // `|v_i - v_j| >= w / (4n)` is `apart >= spread`, `> w / (8n)` is `2 apart > spread`.
            let apart = mul_int(&den.abs(), &four_degree);
            let spread = mul_int(&w, &mul_int(di, dj));
            let fails_3_3 = (ai <= wi || aj <= wj) && apart >= spread;
            let holds_3_4 = ai < (&wi << 1u32) && aj < (&wj << 1u32) && (&apart << 1u32) > spread;
            if !(fails_3_3 || holds_3_4) {
                continue;
            }
            // (3.5): `lambda - a = (xi_i - a) + (xi_j - xi_i) v_i / (v_i - v_j)`, and `v_i /
            // (v_i - v_j) = c_i d_j / den`; so `4N (lambda - a) / w = top / bottom`.
            let mut top = (mul_int(&(&xs[i] - &a), &den)
                + mul_int(&(&xs[j] - &xs[i]), &mul_int(ci, dj)))
                << cells;
            let mut bottom = mul_int(&w, &den);
            if bottom.is_negative() {
                (top, bottom) = (-top, -bottom);
            }
            // `lambda` in `[a, b]`: `0 <= 4N (lambda - a) / w <= 4N`.
            if top.is_negative() || top > mul_int(&four_n, &bottom) {
                continue;
            }
            let l = div_floor_int(&top, &bottom);
            let from = g(&(&l - 1u32).max(BigInt::zero()));
            let to = g(&(&l + 2u32).min(four_n.clone()));
            let sf = side_in(&from, lo, hi, side);
            if sf == Side::Root {
                return Some(from);
            }
            let st = side_in(&to, lo, hi, side);
            if st == Side::Root {
                return Some(to);
            }
            if (sf, st) == (Side::Below, Side::Above) {
                (*lo, *hi) = (from, to);
                break 'tests true;
            }
        }
        // The boundary test, at `m_l = g(2)` and `m_r = g(4N - 2)`.
        let ml = g(&BigInt::from(2));
        if *lo < ml {
            match side(&ml) {
                Side::Root => return Some(ml),
                Side::Above => {
                    *hi = ml;
                    break 'tests true;
                }
                Side::Below => {}
            }
        }
        let mr = g(&(&four_n - 2u32));
        if mr < *hi {
            match side(&mr) {
                Side::Root => return Some(mr),
                Side::Below => {
                    *lo = mr;
                    break 'tests true;
                }
                Side::Above => {}
            }
        }
        // The bisection, at `xi_2`, whose side the Newton test has.
        match at[1].0 {
            Side::Below => *lo = xs[1].clone(),
            _ => *hi = xs[1].clone(),
        }
        false
    };
    match narrowed {
        true => {
            #[cfg(test)]
            tests::REFINED.with(|c| c.set(c.get() + 1));
            *n = n.saturating_add(1);
        }
        false => {
            #[cfg(test)]
            tests::BISECTIONS.with(|c| c.set(c.get() + 1));
            *n = n.saturating_sub(1).max(1);
        }
    }
    None
}

/// The side of `x` in `lo..=hi`, by `side` but at the ends, whose sides the bracket has.
fn side_in(x: &BigInt, lo: &BigInt, hi: &BigInt, side: &mut dyn FnMut(&BigInt) -> Side) -> Side {
    match () {
        _ if x == lo => Side::Below,
        _ if x == hi => Side::Above,
        _ => side(x),
    }
}

/// The bits of the first level of [`doubling`]: 64, one machine word. A bracket whose upper
/// end has at most this many bits is searched at full precision alone, as no lower precision
/// costs less there: num-bigint multiplies numbers of one word by one machine product, 16 bits
/// or 64.
const DOUBLING_BASE: u64 = 64;

/// The bits each level of [`doubling`] keeps above half of the next: the level of `k` bits
/// follows one of `ceil(k / 2) + 8`. The error of Newton's step is about the square of the error
/// it starts from (Brent and Zimmermann, cited at [`doubling`], equation 4.1), so a start
/// within `c` units of the last place at `k / 2 + 8` bits gives about `c^2 2^-16` units at `k`
/// bits, times the ratio of `q''` to `q'` near the root: a guard against that ratio and the
/// floors of the truncated coefficients, each under one unit. One byte, not a measured value;
/// a guess that misses costs the fallback of [`chain_search`] and [`search`], not a wrong
/// answer.
const DOUBLING_GUARD: u64 = 8;

/// `q` at the precision `2^e`, all of it `f` bits lower: each coefficient `c_i` of `x^i` cut
/// to `floor(c_i / 2^((D - i) e + f))`, `D` the greatest exponent, so that `q_e(y)`, with `y`
/// the top bits of `x = 2^e y`, is `q(x) / 2^(D e + f)` less under one unit for each term,
/// times `y^i`: the coefficient of `x^i` stands `(D - i) e + f` bits lower in `q_e` than in
/// `q`, and only its top bits remain. A shift past the bits of `c_i` (or past `u64`) leaves
/// `0`, or `-1` for `c_i < 0`. O(t) shifts. The common shift `f` is [`lead_shift`]: without it
/// the leading coefficient is never cut, so a leading coefficient of `L` bits keeps all of
/// them at every level of [`doubling`], and a level of `k` bits costs `M(L + D k)` in place of
/// `M((D + 1) k)` (plan row ROOTS-doubling-newton, cross-review XR-ROOTS-REF round 2, D4).
fn truncated(q: &[(u64, BigInt)], e: u64, f: u64) -> Vec<(u64, BigInt)> {
    let d = q.last().map_or(0, |(d, _)| *d);
    let out: Vec<(u64, BigInt)> = (q.iter())
        .map(|(i, c)| {
            let c = match (d - i).checked_mul(e).and_then(|s| s.checked_add(f)) {
                Some(s) if s < c.bits() => c >> s,
                _ if c.is_negative() => -BigInt::one(),
                _ => BigInt::zero(),
            };
            (*i, c)
        })
        .collect();
    #[cfg(test)]
    tests::note_level(
        e,
        out.iter().map(|(_, c)| c.bits()).max().unwrap_or(0),
        out.last().map_or(0, |(_, c)| c.bits()),
    );
    out
}

/// The common shift of [`truncated`] at the level of [`doubling`] whose points have `k` bits:
/// the bits of `q`'s leading coefficient past `k`, or 0. Then the leading coefficient keeps
/// at most `k` bits, and a coefficient `c_i` of at most `bits(c_D) + (D - i) bits(hi) + g`
/// bits (as for `c_D` times a polynomial whose roots are under `hi`, `g` the bits of the
/// binomial factors) keeps at most `(D - i + 1) k + g`, `k = bits(hi) - e`: the shift is
/// `(D - i) e + bits(c_D) - k`. So the level's numbers are of `O(k)` bits, and the levels,
/// whose `k` sum to under `bits(hi)` plus 18 a level (`k_(j + 1) <= k_j / 2 + 9`), cost
/// `O(M(n))` together whatever the leading coefficient (test
/// `a_wide_leading_coefficient_is_cut_at_each_level`).
fn lead_shift(q: &[(u64, BigInt)], k: u64) -> u64 {
    #[cfg(test)]
    if !tests::LEAD_SHIFT.with(std::cell::Cell::get) {
        return 0;
    }
    q.last().map_or(0, |(_, c)| c.bits()).saturating_sub(k)
}

/// The sign of a value whose true value `v` is at least `w`, the one computed, and below `w +
/// 2^error_bits`: positive where `w > 0`, as `v >= w`; negative where `w <= -2^error_bits`,
/// as `v < w + 2^error_bits <= 0`; else none, the sign not certified. [`doubling`]'s first
/// level moves an end only on a sign certified so (plan row ROOTS-doubling-newton, D5).
fn certified_sign(w: &BigInt, error_bits: u64) -> Option<Ordering> {
    match w.sign() {
        Sign::Plus => Some(Ordering::Greater),
        Sign::Minus if w.bits() > error_bits => Some(Ordering::Less),
        _ => None,
    }
}

/// A step of [`doubling`] for [`search`]: at `x = 2^e y`, the sign of `p` and Newton's guess,
/// in units of `2^e`, from `Phi_e = scaled(p_e, y, s_e)` and `Psi_e = scaled(slope_e, y, s_e)`,
/// `p_e` and `slope_e` [`truncated`] at `e` with the shift [`lead_shift`] `f` of `p`, and `s_e
/// = 2 bits(hi / 2^e + 1)`. Two [`scaled`] at the level's precision.
///
/// Proof that the sign is certified (by [`certified_sign`]). Write `T = 2^s_e p(x) / (2^(f +
/// D e) y^D)`, the real number `Phi_e` stands for, of the sign of `p(x)`. Each cut coefficient
/// is `floor(c_i / 2^((D - i) e + f))`, at most 1 below `c_i / 2^((D - i) e + f)`, and stands
/// in `Phi_e` times `2^s_e y^(i - D)`; each floor of [`scaled`] loses under 1 and is divided
/// by `y` at least once per later term; every loss is downward. So `T - 2^s_e (lead +
/// 1/(y - 1)) - y/(y - 1) < Phi_e <= T`, `lead` 1 where `f > 0` (the leading coefficient cut)
/// and 0 where `f = 0` (`c_D` kept whole), as `sum over j >= 1 of y^-j = 1/(y - 1)`. For `y >=
/// 3`, `2^s_e / (y - 1) <= 2^(s_e - bits(y) + 2)` (as `y - 1 >= 2^(bits(y) - 2)`) and `y/(y - 1)
/// <= 2`; `y < 2^(s_e / 2)` gives `s_e - bits(y) + 2 >= 2`, so the error is under
/// `2^(s_e - bits(y) + 3)` where `f = 0`, and under `2^s_e + 2^(s_e - 1) + 2 <= 2^(s_e + 1)`
/// where `f > 0`. Below 3 no sign is given.
fn search_level(
    p: &[(u64, BigInt)],
    slope: &[(u64, BigInt)],
    hi: &BigInt,
    e: u64,
    y: &BigInt,
) -> (Option<Ordering>, Option<BigInt>) {
    let s_e = 2 * ((hi >> e) + 1u32).bits();
    let f = lead_shift(p, hi.bits() - e);
    let fy = scaled(&truncated(p, e, f), y, s_e);
    let dy = scaled(&truncated(slope, e, f), y, s_e);
    let g = (!dy.is_zero()).then(|| y - div_floor_int(&mul_int(y, &fy), &dy));
    let error_bits = match f {
        0 => (s_e + 3).saturating_sub(y.bits()),
        _ => s_e + 1,
    };
    let sign = (*y >= BigInt::from(3)).then(|| certified_sign(&fy, error_bits));
    (sign.flatten(), g)
}

/// A step of [`doubling`] for [`chain_search`]: at `x = 2^e y`, the sign of `q` and Newton's
/// guess, in units of `2^e`, from `q_e(y)` and `q'_e(y)` ([`eval`] of [`truncated`] at `e`
/// with the shift [`lead_shift`] `f` of `q`). Two [`eval`] at the level's precision.
///
/// Newton's step `floor((y q'(y) - q(y)) / q'(y))`, written as `y + floor(-q(y) / q'(y))`,
/// equal as `y` is an integer: the quotient is the step's correction, about half the level's
/// bits on its first step and a few bits on its second, not all of `y`'s, so the division is
/// of a short quotient ([`crate::num::div_floor_int`] takes the top bits and one product below
/// `DIV_LEAF` bits of quotient) and no product `y q'(y)` is formed. At 524,288 bits these
/// divisions were 583 million of 3,340 million instructions and grew 4.50 times from 262,144
/// (h5-req24).
///
/// Proof that the sign is certified (by [`certified_sign`]). `q_e(y) = sum of c'_i y^i` with
/// each `c'_i` at most 1 below `c_i / 2^((D - i) e + f)`, so for `y >= 2` the true `q(x) /
/// 2^(D e + f)` exceeds `q_e(y)` by under `sum over i <= D' of y^i = (y^(D' + 1) - 1) / (y -
/// 1) < 2 y^D' < 2^(1 + D' bits(y))`, where `D' = D - 1` if `f = 0` (the leading coefficient
/// kept whole) and `D' = D` if not. Below 2 no sign is given.
fn chain_level(
    q: &[(u64, BigInt)],
    slope: &[(u64, BigInt)],
    hi: &BigInt,
    e: u64,
    y: &BigInt,
) -> (Option<Ordering>, Option<BigInt>) {
    let f = lead_shift(q, hi.bits() - e);
    let qy = eval(&truncated(q, e, f), y);
    let dy = eval(&truncated(slope, e, f), y);
    let g = (!dy.is_zero()).then(|| y + div_floor_int(&-&qy, &dy));
    let degree = q.last().map_or(0, |(d, _)| *d);
    let top = match f {
        0 => degree.saturating_sub(1),
        _ => degree,
    };
    let error_bits = top.saturating_mul(y.bits()).saturating_add(1);
    let sign = (*y >= BigInt::from(2)).then(|| certified_sign(&qy, error_bits));
    (sign.flatten(), g)
}

/// Newton's guess at doubling precision for the root of a monotone function on `lo..=hi`,
/// `0 <= lo < hi`, whose sign at `lo` is `below`, read from the top bits of the points: at
/// level `e` the point `x` is `2^e y`, and `step(e, y)` gives the sign of the function at
/// precision `2^e` and Newton's guess there, in units of `2^e`, from the polynomial whose
/// coefficients [`truncated`] cuts. Returns `(e, y)` for the last level below full precision,
/// `e > 0`, or none where `hi` has at most [`DOUBLING_BASE`] bits, or where a slope is 0.
///
/// The levels, from the top: `k_0 = bits(hi)`, `k_(j + 1) = ceil(k_j / 2) +`
/// [`DOUBLING_GUARD`], until one is at most [`DOUBLING_BASE`]; each level has about twice the
/// bits of the one before. On the first, a bracketed search from `start`: the sign at each
/// point moves an end, and the next point is Newton's guess where it lies strictly inside and
/// the step before it was not a Newton step that failed to halve the bracket, else the middle,
/// at most `2 (k + 2)` points, twice the bits of a bracket of at most `2^k + 1`. On each later
/// level the point is shifted left by the difference of the levels, and two Newton steps are
/// taken, each clamped into the level's bracket.
///
/// Proof that the bracket kept at each level holds the root. The root `r` of the function, a
/// real number, is in `lo..=hi`, as the signs at `lo` and `hi` are exact and opposite (by
/// [`chain_search`] and [`search`], which call this). At level `e` the bracket is
/// `floor(lo / 2^e)..=floor(hi / 2^e) + 1`, and `floor(lo / 2^e) <= lo / 2^e <= r / 2^e <= hi /
/// 2^e < floor(hi / 2^e) + 1`. The first level moves an end only on a sign the step certifies
/// (by [`certified_sign`], from the bound on the cut's error at [`search_level`] and
/// [`chain_level`]), so its bracket keeps the root, and it stops at the first sign it cannot
/// certify; before plan row ROOTS-doubling-newton's round 2 (D5) it took the raw sign of the
/// cut polynomial, which near the root can be the wrong one, and the end moved past the root
/// (test `doubling_keeps_the_root_where_a_cut_sign_is_wrong`). A guess may still be poor, and
/// the later levels take no sign. So the result is a guess alone: the caller tests it and its
/// neighbor at full precision, by exact signs, and on a miss goes on with its own
/// full-precision search from the bracket those exact signs left. The answer is decided at
/// full precision, so it is the one the full-precision search alone gives.
///
/// Complexity tradeoff. Naive: each Newton step at full precision, numbers of the full bits at
/// every step, about `log2 bits(hi)` steps from a start within a factor 4 of the root (the cuts
/// at powers of 2 leave `hi <= 4 lo`): `O(M(n) log n)` for numbers of `n` bits. Here (R. P.
/// Brent and P. Zimmermann, Modern Computer Arithmetic, Cambridge University Press, 2010,
/// arXiv:1004.4710, version 0.5.1, section 4.8.4, p. 176, read 2026-11-22: "when using
/// Newton's method or evaluating power series, many of the computations can be performed with
/// reduced precision, which saves a log n factor"; section 4.2 for the quadratic convergence
/// that makes each level's two steps enough) the level of `k` bits costs `O(t M(D k + g))`,
/// its numbers cut to `O(D k + g)` bits by [`truncated`] with the common shift [`lead_shift`]
/// (`g` the bits of the binomial factors, as there), and the bits of the levels sum to under
/// `bits(hi)` plus 18 a level, so the whole is `O(M(n))`, and the caller adds three
/// evaluations at full precision. Exact, as said above.
fn doubling(
    lo: &BigInt,
    hi: &BigInt,
    start: &BigInt,
    below: Ordering,
    mut step: impl FnMut(u64, &BigInt) -> (Option<Ordering>, Option<BigInt>),
) -> Option<(u64, BigInt)> {
    let bits = hi.bits();
    #[cfg(test)]
    tests::LEVELS.with(|v| v.borrow_mut().push((bits, BTreeMap::new())));
    let mut levels = vec![bits];
    while let Some(&k) = levels.last().filter(|&&k| k > DOUBLING_BASE) {
        levels.push(k.div_ceil(2) + DOUBLING_GUARD);
    }
    levels.remove(0);
    levels.reverse();
    let first = *levels.first()?;
    let bracket = |e: u64| (lo >> e, (hi >> e) + BigInt::one());
    let mut e = bits - first;
    let (mut ly, mut hy) = bracket(e);
    let mut y = start >> e;
    let mut newton = false;
    for _ in 0..2 * (first + 2) {
        if &hy - &ly <= BigInt::one() {
            break;
        }
        let width = &hy - &ly;
        let (sign, guess) = step(e, &y);
        match sign {
            None | Some(Ordering::Equal) => break,
            Some(s) if s == below => ly = ly.max(y.clone()),
            Some(_) => hy = hy.min(y.clone()),
        }
        let halved = (&hy - &ly) * 2 <= width;
        (y, newton) = match guess.filter(|g| (halved || !newton) && &ly < g && g < &hy) {
            Some(g) => (g, true),
            None => ((&ly + &hy) >> 1u32, false),
        };
    }
    #[cfg(test)]
    tests::LEVEL_ONE.with(|b| *b.borrow_mut() = Some((e, ly.clone(), hy.clone())));
    for &k in &levels[1..] {
        let next = bits - k;
        y <<= e - next;
        e = next;
        let (ly, hy) = bracket(e);
        y = y.clamp(ly.clone(), hy.clone());
        for _ in 0..2 {
            let g = step(e, &y).1?.clamp(ly.clone(), hy.clone());
            if g == y {
                break;
            }
            y = g;
        }
    }
    Some((e, y))
}

/// Whether [`chain_search`] and [`search`] take the guess of [`doubling`]: always, but for
/// the tests that turn it off to count the full-precision search alone.
#[cfg(not(test))]
fn doubling_on() -> bool {
    true
}

#[cfg(test)]
fn doubling_on() -> bool {
    tests::DOUBLING.with(std::cell::Cell::get)
}

/// Counts, for the tests, one evaluation at full precision after the cuts of a search whose
/// upper end had over [`DOUBLING_BASE`] bits when the cuts ended (`wide`).
#[cfg(test)]
fn full_eval(wide: bool) {
    if wide {
        tests::FULL_EVALS.with(|n| n.set(n.get() + 1));
    }
}

/// `p` at `x`, by Horner's rule over the gaps between its exponents. The products and powers
/// are the kernel's ([`mul_int`], [`pow_uint`]), O(n log n) a product past their crossovers,
/// and num-bigint's below them, from `n^2` to `n^1.465` by the size (tradeoff at the macro
/// `interval_tests`).
fn eval(p: &[(u64, BigInt)], x: &BigInt) -> BigInt {
    let Some((mut last, _)) = p.last().cloned() else {
        return BigInt::zero();
    };
    let power = |k: u64| {
        let m = BigInt::from(pow_uint(x.magnitude(), k));
        match x.is_negative() && k % 2 == 1 {
            true => -m,
            false => m,
        }
    };
    let mut acc = BigInt::zero();
    for (e, c) in p.iter().rev() {
        acc = mul_int(&acc, &power(last - e)) + c;
        last = *e;
    }
    mul_int(&acc, &power(last))
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
    zed_collections::sorted::sort_dedup(&mut out);
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
    // Every evaluation at the end of a stretch goes through `end`, so that the tests count
    // them against `chain_ends` (`chain_cells_makes_the_end_evaluations_chain_ends_bounds`).
    let end = |x: &BigInt| {
        #[cfg(test)]
        tests::END_EVALS.with(|n| n.set(n.get() + 1));
        eval(q, x)
    };
    for (u, v) in stretches {
        let (fu, fv) = (end(&u), end(&v));
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
    zed_collections::sorted::sort_dedup(&mut out);
    out
}

/// A cell `c` in `lo..hi` at which `q`, monotone on `lo..=hi`, changes sign or is 0, given
/// its values `flo` and `fhi`, of opposite signs, at the ends. Each step is a step of
/// NEWREFINE ([`refine`]) on the exact values of `q` and `q'`, so a search takes at most the
/// bits of `hi - lo` steps, and `O(log log)` of the bracket over the cluster's size at a
/// cluster of roots at an end of a stretch (plan row ROOTS-fallback-worst-case; the proof at
/// [`refine`]). Before those steps, while `hi > 4 max(lo, 1)`, the bracket is cut at the power
/// of 2 whose exponent is the mean of its ends' bits, so a root far below the end Newton's
/// method starts from is reached in O(log B) steps for ends of B bits. Once the cuts end,
/// [`doubling`] gives
/// a guess from the top bits of the bracket at doubling precision, and an exact evaluation
/// there, one Newton step from it and its neighbor, three evaluations at full precision, close
/// the bracket; the steps above go on from the bracket left where they do not (plan row
/// ROOTS-doubling-newton; test `a_search_evaluates_at_full_precision_at_most_three_times`).
/// The step at full precision takes `q'(x0)` from the level of the guess, `2^((D - 1) e)
/// q'_e(y)`, so its error is that of the truncated slope; the exact signs at the probes decide.
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
    // `n` of [`refine`]'s `N = 2^(2^n)`, from `N = 4`.
    let mut level = 1u32;
    let mut tried = false;
    #[cfg(test)]
    let mut wide = false;
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
        // Once the cuts end, so `hi <= 4 lo` and the root's top bits are its ends' (proof and
        // tradeoff at [`doubling`]).
        if !tried && &floor * 4 >= hi {
            tried = true;
            #[cfg(test)]
            {
                wide = hi.bits() > DOUBLING_BASE;
                if wide {
                    tests::SEARCHES.with(|n| n.set(n.get() + 1));
                }
            }
            let start = if flo.abs() <= fhi.abs() { &lo } else { &hi };
            let below = flo.sign();
            let zero = BigInt::zero();
            let guess = doubling_on()
                .then(|| {
                    doubling(&lo, &hi, start, flo.cmp(&zero), |e, y| {
                        chain_level(q, &slope, &hi, e, y)
                    })
                })
                .flatten();
            if let Some((e, y)) = guess {
                // Newton's step from `x0 = 2^e y` at full precision, `q(x0)` exact (and its
                // sign kept, as at any probe) and `q'(x0)` from the level of `e`, as
                // `2^((D - 1) e + f) q'_e(y)` (`f` the level's [`lead_shift`]), then `g` and its
                // neighbor toward the root: three evaluations of `q` at full precision.
                let x0 = &y << e;
                if lo < x0 && x0 < hi {
                    #[cfg(test)]
                    full_eval(wide);
                    let fx = eval(q, &x0);
                    if fx.is_zero() {
                        return x0;
                    }
                    let f = lead_shift(q, hi.bits() - e);
                    let d = eval(&truncated(&slope, e, f), &y);
                    let shift = (slope.last())
                        .and_then(|(m, _)| m.checked_mul(e).and_then(|m| m.checked_add(f)));
                    let g = shift.filter(|_| !d.is_zero()).map(|m| {
                        let (n, d) = match d.is_negative() {
                            true => (-&fx, -d),
                            false => (fx.clone(), d),
                        };
                        &x0 - div_floor_int(&(n >> m), &d)
                    });
                    match fx.sign() == below {
                        true => (lo, flo) = (x0, fx),
                        false => (hi, fhi) = (x0, fx),
                    }
                    if let Some(g) = g {
                        let g = g.clamp(lo.clone(), hi.clone());
                        for near in [false, true] {
                            let x = match near {
                                false => g.clone(),
                                true if lo == g => &g + 1,
                                true if hi == g => &g - 1,
                                true => break,
                            };
                            if !(lo < x && x < hi) {
                                continue;
                            }
                            #[cfg(test)]
                            full_eval(wide);
                            let fx = eval(q, &x);
                            if fx.is_zero() {
                                return x;
                            }
                            match fx.sign() == below {
                                true => (lo, flo) = (x, fx),
                                false => (hi, fhi) = (x, fx),
                            }
                        }
                    }
                }
                #[cfg(test)]
                if wide && &hi - &lo > BigInt::one() {
                    tests::FALLBACKS.with(|n| n.set(n.get() + 1));
                }
                continue;
            }
            #[cfg(test)]
            if wide {
                tests::FALLBACKS.with(|n| n.set(n.get() + 1));
            }
        }
        // A step of NEWREFINE ([`refine`]), on the exact values: `v = q / q'`.
        let below = flo.sign();
        let mut side = |x: &BigInt| {
            #[cfg(test)]
            full_eval(wide);
            let fx = eval(q, x);
            match fx.sign() {
                Sign::NoSign => Side::Root,
                s if s == below => Side::Below,
                _ => Side::Above,
            }
        };
        let mut ratio = |x: &BigInt| {
            #[cfg(test)]
            (0..2).for_each(|_| full_eval(wide));
            let d = eval(&slope, x);
            (!d.is_zero()).then(|| (eval(q, x), d))
        };
        let degree = q.last().map_or(0, |(d, _)| *d);
        if let Some(x) = refine(&mut lo, &mut hi, &mut level, degree, &mut side, &mut ratio) {
            return x;
        }
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
/// Tests: `chain_ends_is_the_sum_it_bounds`, and
/// `chain_cells_makes_the_end_evaluations_chain_ends_bounds`, which counts the evaluations
/// and reaches the bound.
fn chain_ends(t: usize) -> u64 {
    let t = t as u128;
    if t < 2 {
        return 0;
    }
    let ends = 2 * ((t - 2) * (t - 1) * t / 6 + t - 1);
    u64::try_from(ends).unwrap_or(u64::MAX)
}

/// The branch and bound of `positive_roots` without the bound from above and with it from
/// the first interval, for the benchmark `crossover roots-horner` (crate zed-benches), which
/// fits `HORNER_COST`. Not for other use.
#[doc(hidden)]
pub mod crossover {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    use super::{Horner, positive_roots_by};

    /// `super::HORNER_COST` as built.
    pub const HORNER_COST: f64 = super::HORNER_COST;

    /// The terms of `(x - 2) (x - 3) … (x - k - 1)`, by exponent, the cluster the benchmark
    /// runs on.
    pub fn cluster(k: u64) -> Vec<(u64, BigInt)> {
        let mut c = vec![BigInt::one()];
        for r in 2..k + 2 {
            let mut next = vec![BigInt::zero(); c.len() + 1];
            for (i, v) in c.iter().enumerate() {
                next[i + 1] += v;
                next[i] -= v * r;
            }
            c = next;
        }
        c.into_iter()
            .enumerate()
            .filter(|(_, v)| !v.is_zero())
            .map(|(e, v)| (e as u64, v))
            .collect()
    }

    /// The roots of `p` above 1, without the bound from above.
    pub fn off(p: &[(u64, BigInt)]) -> Vec<BigInt> {
        positive_roots_by(p, BigInt::from(2), None, Horner::Off).0
    }

    /// The roots of `p` above 1, with the bound from above found at the first interval.
    pub fn at_start(p: &[(u64, BigInt)]) -> Vec<BigInt> {
        positive_roots_by(p, BigInt::from(2), None, Horner::AtStart).0
    }

    /// The roots of `p` above 1 as `positive_roots` finds them, the bound from above
    /// once the branch and bound has spent `HORNER_COST D^2 / t` units (Codex's B1, round 2:
    /// the third arm of `crossover roots-horner-built`).
    pub fn built(p: &[(u64, BigInt)]) -> Vec<BigInt> {
        positive_roots_by(p, BigInt::from(2), None, Horner::Built).0
    }

    /// The terms of `(x - 4) (x^n + 1)`, sparse and of degree `n + 1`, with the one root 4 above
    /// 1 (as in the test `the_bound_from_above_leaves_sparse_inputs_as_they_were`).
    pub fn sparse(n: u64) -> Vec<(u64, BigInt)> {
        let one = BigInt::one();
        let four = BigInt::from(-4);
        vec![(0, four.clone()), (1, one.clone()), (n, four), (n + 1, one)]
    }

    /// The value of `HORNER_COST` below which the code as built finds the bound: the units the
    /// branch and bound spends without it, times `t / D^2`.
    pub fn flip(p: &[(u64, BigInt)]) -> f64 {
        let (_, spent) = positive_roots_by(p, BigInt::from(2), None, Horner::Off);
        let d = p.last().map_or(0, |(d, _)| *d) as f64;
        spent as f64 * p.len() as f64 / (d * d)
    }
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod tests {
    use super::*;

    /// For each call of [`doubling`], the bits of its `hi` and, for each precision `e` of
    /// [`truncated`] after it, the most bits of a cut coefficient and of a cut leading
    /// coefficient ([`LEVELS`]).
    pub(super) type Levels = Vec<(u64, BTreeMap<u64, (u64, u64)>)>;

    thread_local! {
        /// How many times [`positive_roots`] has handed over to [`chain_roots`] on this thread.
        pub(super) static CHAINED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// The tests of [`positive_from`] on this thread.
        pub(super) static HORNER_TESTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// Where `Some`, each interval [`positive_roots_by`] pops on this thread, after the cut
        /// of [`horner_bound`].
        pub(super) static BOXES: std::cell::RefCell<Option<Vec<(BigInt, BigInt)>>> =
            const { std::cell::RefCell::new(None) };
        /// The units [`positive_roots`] has spent on this thread, a handover to the chain counted
        /// as the whole budget.
        pub(super) static UNITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// The evaluations [`chain_cells`] has made at the ends of stretches on this thread.
        pub(super) static END_EVALS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// The steps of [`refine`] in [`search`] and [`chain_search`] on this thread that cut
        /// the bracket by a test (the boundary test or a guess's cell), and those that
        /// bisected it.
        pub(super) static REFINED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        pub(super) static BISECTIONS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// Whether [`search`] and [`chain_search`] take the guess of [`doubling`] on this
        /// thread ([`doubling_on`]).
        pub(super) static DOUBLING: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
        /// The searches whose upper end had over [`DOUBLING_BASE`] bits when their cuts
        /// ended, the evaluations at full precision they made after the cuts ([`full_eval`]),
        /// and how many of them went on with the full-precision search after the guess of
        /// [`doubling`] (or without one), on this thread.
        pub(super) static SEARCHES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        pub(super) static FULL_EVALS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        pub(super) static FALLBACKS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// Whether [`lead_shift`] gives its shift on this thread; off, it gives 0, the cut
        /// before plan row ROOTS-doubling-newton's round 2 (D4), for the negative control.
        pub(super) static LEAD_SHIFT: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
        /// For each call of [`doubling`] on this thread, the bits of its `hi`, and for each
        /// precision `e` of [`truncated`] after it, the most bits of a cut coefficient and of a
        /// cut leading coefficient.
        pub(super) static LEVELS: std::cell::RefCell<Levels> =
            const { std::cell::RefCell::new(Vec::new()) };
        /// The precision and the bracket the first level of [`doubling`] ended with, last.
        pub(super) static LEVEL_ONE: std::cell::RefCell<Option<(u64, BigInt, BigInt)>> =
            const { std::cell::RefCell::new(None) };
    }

    /// Records, for [`LEVELS`], a cut at the precision `e` whose widest coefficient has
    /// `widest` bits and whose leading coefficient has `lead`.
    pub(super) fn note_level(e: u64, widest: u64, lead: u64) {
        LEVELS.with(|v| {
            if let Some((_, m)) = v.borrow_mut().last_mut() {
                let w = m.entry(e).or_insert((0, 0));
                *w = (w.0.max(widest), w.1.max(lead));
            }
        });
    }

    /// A cubic of three roots of `bits` bits each, the top bit set and the others and the
    /// signs drawn from `rng`, and its roots in order: dense coefficients, where those of
    /// [`of_bits`] are sparse in their bits.
    fn dense_cubic(rng: &mut crate::seed::Rng, bits: u64) -> (Sparse, Vec<BigInt>) {
        let mut rs: Vec<BigInt> = (0..3)
            .map(|_| {
                let words = bits.div_ceil(32);
                let digits = (0..words).map(|_| rng.next_u64() as u32).collect();
                let r = (BigInt::from(num_bigint::BigUint::new(digits)) >> (32 * words - bits))
                    | (BigInt::one() << (bits - 1));
                match rng.below_u64(2) {
                    0 => r,
                    _ => -r,
                }
            })
            .collect();
        zed_collections::sorted::sort_dedup(&mut rs);
        (from_big_roots(&rs), rs)
    }

    /// A search whose bracket has over [`DOUBLING_BASE`] bits when its cuts end makes at most
    /// three evaluations at full precision after them (plan row ROOTS-doubling-newton): the
    /// guess of [`doubling`] is within 1 of the root, so its three probes close the bracket
    /// and the full-precision search never runs, on the cubic of [`of_bits`] and on a dense
    /// cubic of three seeded random roots ([`dense_cubic`]), and on that cubic times a
    /// leading coefficient of as many bits ([`times_wide`], the fixture of D4 in cross-review
    /// XR-ROOTS-REF round 2), at 256, 2,048 and 8,192 bits. Negative control, run here: with
    /// [`doubling`] off (`DOUBLING` false), the full-precision search alone takes about `log2
    /// bits` Newton steps of four or more evaluations each, and each case has more than three
    /// evaluations at full precision per search or a fallback.
    #[test]
    fn a_search_evaluates_at_full_precision_at_most_three_times() {
        let mut rng = crate::seed::Rng::new(0x726f_6f74);
        for bits in [256u64, 2048, 8192] {
            let (dense, roots) = dense_cubic(&mut rng, bits);
            let wide = times_wide(&mut rng, &dense, bits);
            for (name, (f, rs)) in [
                ("of_bits", of_bits(bits)),
                ("dense_cubic", (dense, roots.clone())),
                ("non_monic", (wide, roots)),
            ] {
                for on in [true, false] {
                    DOUBLING.with(|d| d.set(on));
                    for counter in [&SEARCHES, &FULL_EVALS, &FALLBACKS] {
                        counter.with(|n| n.set(0));
                    }
                    assert_eq!(integer_roots(&f, None, None), Roots::Listed(rs.clone()));
                    let [searches, full, fallbacks] =
                        [&SEARCHES, &FULL_EVALS, &FALLBACKS].map(|c| c.with(|n| n.get()));
                    println!(
                        "{name}({bits}), doubling {on}: {searches} searches, {full} evaluations \
                         at full precision, {fallbacks} fallbacks"
                    );
                    assert!(searches > 0, "{name}({bits}): no search");
                    assert_eq!(
                        full <= 3 * searches && fallbacks == 0,
                        on,
                        "{name}({bits}), doubling {on}: {full} evaluations at full precision \
                         and {fallbacks} fallbacks over {searches} searches"
                    );
                }
            }
        }
        DOUBLING.with(|d| d.set(true));
    }

    /// Codex's family of cross-review XR-ROOTS-REF round 2 (D6), `(2x - A)^3 + (2x - A)` on
    /// `R - H..=R + H` with `R = 2^n + 2^(n/4)`, `H = 2^(n/8)`, `A = 2R + 1`, through the public
    /// entry, and a variant that reaches the case it aims at. Plan row ROOTS-fallback-worst-case.
    ///
    /// Codex's family is not reached. Its real root is `A/2 = R + 1/2`, the root of its second
    /// derivative, `24 (2x - A)`, too. The branch and bound cannot prove the slope one-signed
    /// on a cell around `R` before its budget (`chain_ends`), so the chain runs
    /// (`chain_roots`): the cell of `q''` is `R` (its search is the one Newton step counted),
    /// `q'`, `2 (3 (2x - A)^2 + 1) > 0`, adds none, and `q` itself is negative on `..=R` and
    /// positive on `R + 1..`, so neither stretch beside the cell has a sign change and no
    /// search of `q` runs.
    ///
    /// The variant `(x - R)^3 - S^3`, `S = 2^(n/16)`, root `R + S`, is reached. Its cluster
    /// of three roots `R + S w^k` (`w^3 = 1`) sits at the end `R` of the stretch the chain
    /// searches (the cell of `q''` and `q'`), so `q` is flat near that end and steep near the
    /// other. Before plan row ROOTS-fallback-worst-case's NEWREFINE ([`refine`]), Newton's step
    /// from the end of the smaller value, `R` (`q'(R) = 0`), left the bracket, and each step was
    /// a bisection after a Newton step that failed, one bit of the bracket for two
    /// full-precision steps, `n/8 - n/16` bits: `n/16 + 1` Newton steps and `n/16` bisections
    /// (measured 2026-11-23), `O(n M(n))` in all, with or without [`doubling`]: no reduced level
    /// can certify a sign in the bracket, as `q` is about `S^3`, `3n/16` bits, there and its
    /// terms `3n` bits, and the truncation error of a level is `2^((D - 1) n + e)`
    /// (`chain_level`). NEWREFINE's secant on `q / q'`, about `(x - R - S) / 3` past the
    /// cluster, needs no count of the cluster's roots and takes `O(log n)` steps: at most
    /// `4 log2 n - 21` asserted here, the line of `newrefine_takes_log_log_steps_on_a_cluster`,
    /// and the exact counts printed (the steps that cut by a test, the bisections). Measured
    /// 2026-11-27, local, at n = 256, 1,024, 2,048, 4,096 and 8,192: Codex's family 6, 8, 8, 9
    /// and 10 (6, 7, 21, 20 and 26 without the cut of `4N` at [`refine`]), the variant 4, 9,
    /// 13, 16 and 17; the bound `log2 n + 3` of the step before the source's order (boundary
    /// test first, Newton's guess at `xi_2` added) fails at 4,096 and 8,192 on the variant.
    /// Negative control: the old step (Newton's guess from an end, a bisection
    /// after a weak one, `git show 06ed591d0:crates/zed-kernel/src/poly/roots.rs`) gives the
    /// `n/16 + 1` and `n/16` above.
    #[test]
    fn a_cluster_at_an_end_of_a_chain_stretch_takes_log_log_steps() {
        let one = BigInt::one();
        let mut over = Vec::new();
        for n in [256u64, 1024, 2048, 4096, 8192] {
            let r = (&one << n) + (&one << (n / 4));
            let h = &one << (n / 8);
            let a = &r * 2u32 + 1u32;
            let codex = Sparse::new([
                (3, BigInt::from(8)),
                (2, -12 * &a),
                (1, 6 * &a * &a + 2u32),
                (0, -(&a * &a * &a + &a)),
            ]);
            let s = &one << (n / 16);
            let cubed = &s * &s * &s;
            let variant = Sparse::new([
                (3, one.clone()),
                (2, -3 * &r),
                (1, 3 * &r * &r),
                (0, -(&r * &r * &r + &cubed)),
            ]);
            for (name, f, rs) in [
                ("codex", &codex, vec![]),
                ("variant", &variant, vec![&r + &s]),
            ] {
                for on in [true, false] {
                    DOUBLING.with(|d| d.set(on));
                    for c in [
                        &REFINED,
                        &BISECTIONS,
                        &FULL_EVALS,
                        &FALLBACKS,
                        &SEARCHES,
                        &CHAINED,
                        &UNITS,
                    ] {
                        c.with(|n| n.set(0));
                    }
                    let (l, u) = (&r - &h, &r + &h);
                    assert_eq!(
                        integer_roots(f, Some(&l), Some(&u)),
                        Roots::Listed(rs.clone()),
                        "{name}({n})"
                    );
                    let [rf, bi, fe, fb, se, ch, un] = [
                        &REFINED,
                        &BISECTIONS,
                        &FULL_EVALS,
                        &FALLBACKS,
                        &SEARCHES,
                        &CHAINED,
                        &UNITS,
                    ]
                    .map(|c| c.with(|n| n.get()));
                    println!(
                        "{name}({n}) doubling {on}: {rf} steps cut by a test, {bi} bisections, \
                         {fe} evaluations at full precision, {fb} fallbacks, {se} searches, \
                         {ch} chained, {un} units"
                    );
                    let bound = 4 * n.ilog2() as u64 - 21;
                    if rf + bi > bound {
                        over.push(format!(
                            "{name}({n}), {on}: {rf} + {bi} steps, over {bound}"
                        ));
                    }
                    assert_eq!([ch, un], [1, 15], "{name}({n}), {on}");
                }
            }
        }
        DOUBLING.with(|d| d.set(true));
        assert!(over.is_empty(), "{over:#?}");
    }

    /// `f` times a positive number of `bits` bits, the top bit set and the others drawn from
    /// `rng`: a polynomial of the same roots whose leading coefficient has `bits` bits more.
    fn times_wide(rng: &mut crate::seed::Rng, f: &Sparse, bits: u64) -> Sparse {
        let words = bits.div_ceil(32);
        let digits = (0..words).map(|_| rng.next_u64() as u32).collect();
        let c = (BigInt::from(num_bigint::BigUint::new(digits)) >> (32 * words - bits))
            | (BigInt::one() << (bits - 1));
        Sparse::new(f.terms().iter().map(|(i, a)| (*i, a * &c)))
    }

    /// Plan row ROOTS-doubling-newton, D4 of cross-review XR-ROOTS-REF round 2: on a dense
    /// cubic of roots of 8,192 bits times a number of 8,192 bits, the leading coefficient cut
    /// at each level of [`doubling`] has at most the level's bits, by the common shift
    /// [`lead_shift`]: summed over the levels of each search, it is at most `2 bits(hi)` plus
    /// 64 a level, and the widest cut coefficient, at most `(D + 1) k + g` bits a level of
    /// `k` bits (proof at [`lead_shift`]), sums to at most 4 times that for this cubic.
    /// Negative control, run here: with the shift off (`LEAD_SHIFT` false, the cut before
    /// D4) the leading coefficient keeps its 8,192 extra bits at every level, and some search
    /// is over the bounds. The roots are exact both ways.
    #[test]
    fn a_wide_leading_coefficient_is_cut_at_each_level() {
        let mut rng = crate::seed::Rng::new(0x6c65_6164);
        let bits = 8192u64;
        let (f, rs) = dense_cubic(&mut rng, bits);
        let f = times_wide(&mut rng, &f, bits);
        for shift in [true, false] {
            LEAD_SHIFT.with(|s| s.set(shift));
            LEVELS.with(|v| v.borrow_mut().clear());
            assert_eq!(integer_roots(&f, None, None), Roots::Listed(rs.clone()));
            let runs = LEVELS.with(|v| v.borrow().clone());
            let mut over = Vec::new();
            for (hb, m) in runs
                .iter()
                .filter(|(hb, m)| *hb > DOUBLING_BASE && !m.is_empty())
            {
                let levels = m.len() as u64;
                let lead: u64 = m.values().map(|w| w.1).sum();
                let widest: u64 = m.values().map(|w| w.0).sum();
                let bound = 2 * hb + 64 * levels;
                println!(
                    "shift {shift}: bits(hi) {hb}, {levels} levels, leading {lead}, widest \
                     {widest}, bound {bound}"
                );
                if lead > bound || widest > 4 * bound {
                    over.push(*hb);
                }
            }
            assert!(runs.iter().any(|(hb, _)| *hb > DOUBLING_BASE), "no search");
            assert_eq!(
                over.is_empty(),
                shift,
                "shift {shift}: over the bounds at {over:?}"
            );
        }
        LEAD_SHIFT.with(|s| s.set(true));
    }

    /// Plan row ROOTS-doubling-newton, D5 of cross-review XR-ROOTS-REF round 2 (Codex's case):
    /// the first level of [`doubling`] moves an end only on a certified sign. `q = (x - 2)(x -
    /// (z - 1))`, `z = 2^65`, on `z - 4 S..=z + 4 S`, `S = 2^25`, has its one level at `e =
    /// 25`, where the cut polynomial at `y = z / 2^25 = 2^40` is negative by [`eval`] (`-2^40 +
    /// 2^16 - 1`) and by [`scaled`] while `q(z) = 2^65 - 2` is positive: the raw sign would set
    /// the lower end to `2^40`, `2^65` in full, past the root `z - 1`. The bracket the level
    /// ends with holds the root on both paths ([`chain_level`], [`search_level`]), and both
    /// searches find it. Negative control: the raw sign (`Some(qy.cmp(&zero))` in place of
    /// [`certified_sign`] in both functions) fails the bracket assertions.
    #[test]
    fn doubling_keeps_the_root_where_a_cut_sign_is_wrong() {
        let s = BigInt::one() << 25u32;
        let z = BigInt::one() << 65u32;
        let root = &z - 1u32;
        let (lo, hi) = (&z - 4u32 * &s, &z + 4u32 * &s);
        let f = from_big_roots(&[BigInt::from(2), root.clone()]);
        let q = f.terms();
        let derivative: Vec<(u64, BigInt)> = (q.iter())
            .filter(|(e, _)| *e > 0)
            .map(|(e, c)| (e - 1, c * BigInt::from(*e)))
            .collect();
        let times_x: Vec<(u64, BigInt)> = (q.iter())
            .filter(|(e, _)| *e > 0)
            .map(|(e, c)| (*e, c * BigInt::from(*e)))
            .collect();
        assert!(eval(q, &z).is_positive());
        let y = &z >> 25u32;
        let s_e = 2 * ((&hi >> 25u32) + 1u32).bits();
        assert!(eval(&truncated(q, 25, 0), &y).is_negative());
        assert!(scaled(&truncated(q, 25, 0), &y, s_e).is_negative());
        for path in ["chain_level", "search_level"] {
            LEVEL_ONE.with(|b| *b.borrow_mut() = None);
            let guess = doubling(&lo, &hi, &z, Ordering::Less, |e, y| match path {
                "chain_level" => chain_level(q, &derivative, &hi, e, y),
                _ => search_level(q, &times_x, &hi, e, y),
            });
            let (e, ly, hy) = LEVEL_ONE
                .with(|b| b.borrow().clone())
                .expect("a first level");
            println!("{path}: e {e}, bracket {ly}..={hy}, guess {guess:?}");
            assert_eq!(e, 25, "{path}");
            assert!(
                (&ly << e) <= root && root <= (&hy << e),
                "{path}: {ly}..={hy}"
            );
        }
        let (flo, fhi) = (eval(q, &lo), eval(q, &hi));
        assert_eq!(chain_search(q, lo.clone(), hi.clone(), flo, fhi), root);
        assert_eq!(
            search(q, &times_x, None, lo, hi, &mut 0, u64::MAX),
            Some(root)
        );
    }

    /// The roots of dense cubics of three random roots are found exactly, from 65 to 1,024
    /// bits, with [`doubling`] on and off (a fresh seed each run, printed; author P169).
    #[test]
    fn dense_cubics_have_their_roots_with_and_without_doubling() {
        let (mut rng, seed) = crate::seed::Rng::fresh("dense_cubics_have_their_roots");
        for _ in 0..12 {
            let bits = 65 + rng.below_u64(960);
            let (f, rs) = dense_cubic(&mut rng, bits);
            for on in [true, false] {
                DOUBLING.with(|d| d.set(on));
                assert_eq!(
                    integer_roots(&f, None, None),
                    Roots::Listed(rs.clone()),
                    "seed {seed}, {bits} bits, doubling {on}"
                );
            }
        }
        DOUBLING.with(|d| d.set(true));
    }

    /// The cubic `(x - a)(x - b)(x - 5)` with `a = 2^bits + 3` and `b = -(2^bits + 7)`, of the
    /// benchmark `l01_39_reduced_product::roots::bench::roots_scale_in_the_degree_and_in_the_bits`,
    /// and its roots in order.
    fn of_bits(bits: u64) -> (Sparse, Vec<BigInt>) {
        let a = (BigInt::one() << bits) + 3;
        let b = -((BigInt::one() << bits) + 7);
        let rs = vec![b, BigInt::from(5), a];
        (from_big_roots(&rs), rs)
    }

    /// A search takes at most a step per bit of its bracket ([`refine`]: each step leaves at
    /// most half of it): on the cubic of [`of_bits`] at 2,048 bits and on dense cubics of 1,024
    /// and 4,096 bits, with the guess of [`doubling`] off so that the searches run at full
    /// precision, the steps of all searches are at most 3 times the bits plus 2 (three roots,
    /// each searched once), and most of them cut the bracket by a test, not a bisection.
    /// Before plan row ROOTS-fallback-worst-case the old step (Newton's guess, a bisection
    /// after a weak one, plan row ROOTS-bisect-flag) took 36, 42 and 58 bisections here
    /// (measured 2026-11-23).
    #[test]
    fn a_search_takes_at_most_a_step_per_bit() {
        let mut rng = crate::seed::Rng::new(0x6269_7365);
        let cases = [
            (2048, "of_bits(2048)", of_bits(2048)),
            (1024, "dense_cubic(1024)", dense_cubic(&mut rng, 1024)),
            (4096, "dense_cubic(4096)", dense_cubic(&mut rng, 4096)),
        ];
        DOUBLING.with(|d| d.set(false));
        for (bits, name, (f, rs)) in cases {
            for c in [&REFINED, &BISECTIONS] {
                c.with(|n| n.set(0));
            }
            assert_eq!(integer_roots(&f, None, None), Roots::Listed(rs), "{name}");
            let [refined, bisections] = [&REFINED, &BISECTIONS].map(|c| c.with(|n| n.get()));
            println!("{name}: {refined} steps cut by a test, {bisections} bisections");
            assert!(
                refined + bisections <= 3 * (bits + 2),
                "{name}: {refined} + {bisections} steps"
            );
            assert!(
                bisections <= refined,
                "{name}: {bisections} bisections, {refined} cut by a test"
            );
        }
        DOUBLING.with(|d| d.set(true));
    }

    /// Plan row ROOTS-fallback-worst-case, cross-review XR-lazy-and-kernel-batch-1 round 1:
    /// NEWREFINE ([`refine`]) takes `O(log log)` steps of the bracket over the cluster's size,
    /// called directly in [`chain_search`] (exact values) and [`search`] (scaled values), with
    /// the guess of [`doubling`] on and off. `R = 2^n + 2^(n/4)`, `H = 2^(n/8)`, `S =
    /// 2^(n/16)`, n = 2^8 to 2^15. Family A, `(x - R)^3 - S^3` on `R + 1..=R + H`, root `R +
    /// S` at the end of a cluster of three, where the old step (Newton's method from an end)
    /// took 32, 64 and 128 steps at n = 256, 512 and 1,024. Family B, `((x - M)^3 - S^3) ((x -
    /// M)^2 + K^2)`, `M = R + floor(5H / 13)`, `K = H / 2`, on `R..=R + H`, a cluster of three
    /// inside the bracket of a quintic, where the old step took 31, 56 and 112 (Gemini's
    /// `verify_req3`, rerun by the orchestrator). The counts are steps of [`refine`] (those
    /// that cut by a test plus the bisections). Measured 2026-11-27, local, the most over the
    /// two families, both sites and the guess of [`doubling`] on and off: 10, 13, 17, 19, 27,
    /// 29, 34 and 39 (family A 5, 12, 13, 18, 24, 22, 32, 39; family B 10, 13, 17, 19, 27, 29,
    /// 34, 37). Claude's B-5 of round 2 asked for `c log2 n` with `c` fitted on the first three
    /// sizes: that `c`, 1.7, fails at 2,048 (19 over 18.7) and at every size past it; the
    /// counts grow by 2 to 8, 4 on average, a doubling, with no rise in the step, so the bound asserted is the line `4 log2 n - 21` over all eight sizes, `O(log
    /// log w)` (`w` has `n / 8` bits). Every count is printed before any is checked.
    #[test]
    fn newrefine_takes_log_log_steps_on_a_cluster() {
        let one = BigInt::one();
        let mut over = Vec::new();
        let product = |a: &[(u64, BigInt)], b: &[(u64, BigInt)]| {
            let mut m = BTreeMap::<u64, BigInt>::new();
            for (i, x) in a {
                for (j, y) in b {
                    *m.entry(i + j).or_insert_with(BigInt::zero) += x * y;
                }
            }
            m.into_iter()
                .filter(|(_, c)| !c.is_zero())
                .collect::<Vec<_>>()
        };
        let cubic = |m: &BigInt, s: &BigInt| -> Vec<(u64, BigInt)> {
            vec![
                (0, -(m.pow(3) + s.pow(3))),
                (1, 3 * m * m),
                (2, -3 * m),
                (3, one.clone()),
            ]
        };
        for n in (8..=15).map(|e| 1u64 << e) {
            let most = 4 * n.ilog2() as u64 - 21;
            let r = (&one << n) + (&one << (n / 4));
            let h = &one << (n / 8);
            let s = &one << (n / 16);
            let m = &r + (&h * 5u32) / 13u32;
            let k = &h >> 1u32;
            let quadratic: Vec<(u64, BigInt)> =
                vec![(0, &m * &m + &k * &k), (1, -2 * &m), (2, one.clone())];
            let cases = [
                ("A", cubic(&r, &s), &r + 1u32, &r + &h, &r + &s),
                (
                    "B",
                    product(&cubic(&m, &s), &quadratic),
                    r.clone(),
                    &r + &h,
                    &m + &s,
                ),
            ];
            for (name, q, lo, hi, root) in cases {
                let times_x: Vec<(u64, BigInt)> = (q.iter())
                    .filter(|(e, _)| *e > 0)
                    .map(|(e, c)| (*e, c * BigInt::from(*e)))
                    .collect();
                for on in [false, true] {
                    DOUBLING.with(|d| d.set(on));
                    for site in ["chain_search", "search"] {
                        for c in [&REFINED, &BISECTIONS] {
                            c.with(|n| n.set(0));
                        }
                        let found = match site {
                            "chain_search" => {
                                let (flo, fhi) = (eval(&q, &lo), eval(&q, &hi));
                                chain_search(&q, lo.clone(), hi.clone(), flo, fhi)
                            }
                            _ => {
                                search(&q, &times_x, None, lo.clone(), hi.clone(), &mut 0, u64::MAX)
                                    .expect("a root")
                            }
                        };
                        let [rf, bi] = [&REFINED, &BISECTIONS].map(|c| c.with(|n| n.get()));
                        println!(
                            "family {name}, n = {n}, {site}, doubling {on}: {rf} steps cut by \
                             a test, {bi} bisections"
                        );
                        assert_eq!(found, root, "family {name}, n = {n}, {site}, {on}");
                        if rf + bi > most {
                            over.push(format!(
                                "family {name}, n = {n}, {site}, {on}: {rf} + {bi} steps, \
                                 over {most}"
                            ));
                        }
                    }
                }
            }
        }
        DOUBLING.with(|d| d.set(true));
        assert!(over.is_empty(), "{over:#?}");
    }

    /// The roots [`chain_roots`] finds on `p` in `2..=b`, and the evaluations at the ends of
    /// stretches it made.
    fn chain_and_ends(p: &[(u64, BigInt)], b: Option<i64>) -> (Vec<BigInt>, u64) {
        END_EVALS.with(|n| n.set(0));
        let roots = chain_roots(p, BigInt::from(2), b.map(BigInt::from));
        (roots, END_EVALS.with(|n| n.get()))
    }

    /// [`chain_cells`] makes the evaluations at the ends of stretches that [`chain_ends`]
    /// bounds, counted: exactly `chain_ends(t)` on the product of `x - 10^k` for `k` in
    /// `1..t`, `t = 2..=6`, where each member of the chain has as many positive roots as
    /// Descartes' rule allows and each lies in a stretch of its own, so the bound is reached
    /// (2, 6, 14, 28 and 50), and on `(x - 4)(x - 10)(x - 12)` within `2..=60` (14); at most
    /// `chain_ends(t)` over the 400 random polynomials of
    /// `the_chain_agrees_with_the_branch_and_bound`. Negative control: one more evaluation per
    /// stretch fails the equalities.
    #[test]
    fn chain_cells_makes_the_end_evaluations_chain_ends_bounds() {
        for t in 2..=6usize {
            let ten = num_bigint::BigUint::from(10u8);
            let rs: Vec<BigInt> = (1..t as u64)
                .map(|k| BigInt::from(pow_uint(&ten, k)))
                .collect();
            let f = from_big_roots(&rs);
            assert_eq!(f.terms().len(), t);
            let (roots, n) = chain_and_ends(f.terms(), None);
            assert_eq!(roots, rs, "t = {t}");
            assert_eq!(n, chain_ends(t), "t = {t}");
        }
        let f = from_roots(1, &[4, 10, 12]);
        let (roots, n) = chain_and_ends(f.terms(), Some(60));
        assert_eq!(roots, [4, 10, 12].map(BigInt::from));
        assert_eq!(n, chain_ends(4));
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
            let (chain, ends) = chain_and_ends(p, Some(60));
            assert_eq!(chain, want, "the chain on {f:?}");
            assert!(
                ends <= chain_ends(p.len()),
                "{ends} end evaluations on {f:?}"
            );
            let branch = positive_roots(p, BigInt::from(2), Some(hi.clone()));
            assert_eq!(branch, want, "the branch and bound on {f:?}");
        }
    }

    /// The dense product `(x - 2) … (x - 65)`, whose coefficients pass 2^60 (plan row
    /// ROOTS-dense-cluster-constant): the branch and bound with its switch and the chain alone
    /// each give exactly `2..=65`. It prints the least wall time of three runs of each and whether
    /// the branch and bound spent its budget and switched to the chain, so that one run on one
    /// machine compares the two methods; the comment at [`integer_roots`] says the chain was
    /// about 2 times faster here (40 against 80 ms), measured on another machine. Run it alone,
    /// with `--exact --nocapture`, for the times to mean anything.
    #[test]
    fn the_dense_cluster_of_64_roots_on_each_method() {
        let rs: Vec<i64> = (2..=65).collect();
        let f = from_roots(1, &rs);
        let p = f.terms();
        assert!(
            p.iter().any(|(_, c)| c.bits() > 60),
            "the coefficients pass 2^60"
        );
        let want: Vec<BigInt> = rs.iter().map(|&r| BigInt::from(r)).collect();
        let least = |run: &dyn Fn() -> Vec<BigInt>| {
            (0..3)
                .map(|_| {
                    let t = std::time::Instant::now();
                    assert_eq!(run(), want);
                    t.elapsed()
                })
                .min()
                .expect("three runs")
        };
        let before = CHAINED.with(|c| c.get());
        let branch = least(&|| positive_roots(p, BigInt::from(2), None));
        let switched = CHAINED.with(|c| c.get()) > before;
        let chain = least(&|| chain_roots(p, BigInt::from(2), None));
        println!(
            "(x - 2) … (x - 65): branch and bound {branch:?} (switched to the chain: \
             {switched}), chain alone {chain:?}"
        );
    }

    /// The intervals [`positive_roots_by`] pops on `p` from 2 with `horner`, those of them
    /// that meet `[lo, hi]` and those wholly above `hi`, and the tests of [`positive_from`].
    fn boxes(
        p: &[(u64, BigInt)],
        horner: Horner,
        lo: i64,
        hi: i64,
    ) -> (Vec<BigInt>, u64, u64, u64) {
        BOXES.with(|v| *v.borrow_mut() = Some(Vec::new()));
        let before = HORNER_TESTS.with(|n| n.get());
        let (roots, _) = positive_roots_by(p, BigInt::from(2), None, horner);
        let tests = HORNER_TESTS.with(|n| n.get()) - before;
        let popped = BOXES.with(|v| v.borrow_mut().take()).expect("recorded");
        let (lo, hi) = (BigInt::from(lo), BigInt::from(hi));
        let meet = popped.iter().filter(|(l, h)| *l <= hi && *h >= lo).count() as u64;
        let above = popped.iter().filter(|(l, _)| *l > hi).count() as u64;
        (roots, meet, above, tests)
    }

    /// The bound from above on `(x - 2) … (x - 65)` (plan row ROOTS-dense-cluster-constant,
    /// cross-review XR-lazy-and-kernel-batch-1 round 1): as built, no interval popped lies wholly
    /// above the largest root, 65, and at least 127 meet `[2, 65]`, Claude's proved lower bound
    /// for that count (a box holding two roots is split, so 64 roots need 63 splits and 64
    /// leaves at least). Negative control: without the bound the intervals above 65 are the
    /// 1,152 Gemini's `verify_req2` counted, of 1,293.
    #[test]
    fn the_bound_from_above_drops_the_intervals_past_the_cluster() {
        let rs: Vec<i64> = (2..=65).collect();
        let f = from_roots(1, &rs);
        let p = f.terms();
        let want: Vec<BigInt> = rs.iter().map(|&r| BigInt::from(r)).collect();
        let (roots, meet, above, tests) = boxes(p, Horner::Built, 2, 65);
        assert_eq!(roots, want);
        assert_eq!(above, 0, "intervals above 65 as built");
        assert!(meet >= 127, "{meet} intervals meet [2, 65]");
        assert!(tests > 0, "the bound was found");
        let (roots, meet_off, above_off, tests_off) = boxes(p, Horner::Off, 2, 65);
        assert_eq!(roots, want);
        assert_eq!(tests_off, 0);
        println!(
            "as built: {meet} meet [2, 65], {tests} tests; without: {meet_off} meet, {above_off} above"
        );
        assert!(
            above_off > 1_000,
            "{above_off} intervals above 65 without the bound"
        );
    }

    /// The bound from above is sound where its test fails low and where the cap stops it: on
    /// `(x - 2) … (x - k - 1)` for `k` from 1 to 34, with a root of `2^b` added for `b` in 8, 64
    /// and 300 (past the cap at `b = 300`, as `D bits(u) > 2 B` before `u` reaches the root),
    /// each mode gives the same roots, and the `u` of [`horner_bound`], where it is found, is
    /// above the largest root and the least integer whose test passes.
    #[test]
    fn the_bound_from_above_keeps_every_root() {
        for k in [1i64, 2, 3, 5, 8, 13, 21, 34] {
            for far in [None, Some(8u32), Some(64), Some(300)] {
                let mut rs: Vec<BigInt> = (2..k + 2).map(BigInt::from).collect();
                if let Some(b) = far {
                    rs.push(BigInt::one() << b);
                }
                let f = from_big_roots(&rs);
                let p = f.terms();
                let off = positive_roots_by(p, BigInt::from(2), None, Horner::Off).0;
                assert_eq!(off, rs, "k = {k}, far {far:?}, off");
                for horner in [Horner::AtStart, Horner::Built] {
                    let on = positive_roots_by(p, BigInt::from(2), None, horner).0;
                    assert_eq!(on, rs, "k = {k}, far {far:?}, {horner:?}");
                }
                let mut spent = 0;
                let top = rs.last().expect("a root").clone();
                if let Some(u) = horner_bound(p, &(&top << 2u32), &mut spent) {
                    assert!(u > top, "k = {k}, far {far:?}: {u} not above {top}");
                    assert!(
                        u == BigInt::from(2) || !positive_from(p, &(&u - 1)),
                        "k = {k}: {u} not the least"
                    );
                }
            }
        }
    }

    /// The sparse inputs stay as they were: on `(x^n + 1)(x - 4)` (`t = 4`, `D = n + 1`) for
    /// `n` to 8,192, the trigger `spent t >= HORNER_COST D^2` is not reached and no test of
    /// [`positive_from`] runs (the units of the far roots of
    /// [`the_count_of_units_on_far_roots_is_proved`] are checked there, also with no test).
    #[test]
    fn the_bound_from_above_leaves_sparse_inputs_as_they_were() {
        for n in [3u64, 64, 1_000, 8_192] {
            let p = big(&[
                (0, BigInt::from(-4)),
                (1, BigInt::one()),
                (n, BigInt::from(-4)),
                (n + 1, BigInt::one()),
            ]);
            let (roots, _, _, tests) = boxes(p.terms(), Horner::Built, 2, 4);
            assert_eq!(roots, vec![BigInt::from(4)], "n = {n}");
            assert_eq!(tests, 0, "n = {n}");
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

    /// The `i128` interval tests ([`small`]) give the `BigInt` tests' answers, on random
    /// polynomials whose coefficients reach past [`small::BOUND`] at random intervals in
    /// `2..=BOUND`, and on fixed ones at the ends of the proof there: every coefficient at
    /// `BOUND - 1` with gaps of 1, the most the carry bounds can hold, and points at `BOUND`. A
    /// coefficient of `BOUND` or more is declined (ROOTS-small-constant).
    #[test]
    fn the_word_tests_agree_with_the_bigint_tests() {
        type Case = (Vec<(u64, BigInt)>, i128, i128);
        let (mut rng, seed) = crate::seed::Rng::fresh("the_word_tests_agree_with_the_bigint_tests");
        let bound = BigInt::from(small::BOUND);
        let m: BigInt = &bound - 1;
        let top_heavy: Vec<(u64, BigInt)> = (0..6)
            .map(|e| (e, if e % 2 == 0 { m.clone() } else { -m.clone() }))
            .collect();
        let mut cases: Vec<Case> = vec![
            (
                vec![(0, &bound - 2), (1, BigInt::one())],
                small::BOUND,
                small::BOUND,
            ),
            (
                vec![(0, -(&bound - 2)), (1, BigInt::one())],
                2,
                small::BOUND,
            ),
            (
                vec![(0, BigInt::one()), (60, -(&bound - 2))],
                small::BOUND - 1,
                small::BOUND,
            ),
            (
                vec![(0, -BigInt::one()), (1, -(&bound - 3)), (2, BigInt::one())],
                2,
                2,
            ),
            (top_heavy.clone(), 2, small::BOUND),
            (top_heavy.clone(), 2, 2),
            (top_heavy.iter().map(|(e, c)| (*e, c.abs())).collect(), 2, 3),
            (
                vec![(0, -m.clone()), (1, -m.clone()), (2, m.clone())],
                2,
                small::BOUND,
            ),
            (vec![(0, bound.clone()), (1, BigInt::one())], 2, 2),
        ];
        for _ in 0..3000 {
            let bits = [4, 20, 58, 60, 61][rng.below_u64(5) as usize];
            let mut e = 0;
            let p: Vec<(u64, BigInt)> = (0..2 + rng.below_u64(5))
                .map(|i| {
                    e += u64::from(i > 0) + rng.below_u64(4);
                    let c = 1 + rng.below_u64((1 << bits) - 1) as i64;
                    (e, BigInt::from(if rng.below_u64(2) == 0 { c } else { -c }))
                })
                .collect();
            let top = [16, 1 << 20, small::BOUND][rng.below_u64(3) as usize];
            let l = 2 + i128::from(rng.below_u64(top as u64 - 1));
            let h = l + i128::from(rng.below_u64((small::BOUND - l) as u64 + 1) % (top as u64));
            cases.push((p, l, h.min(small::BOUND)));
        }
        let (mut checked, mut declined) = (0, 0);
        for (p, l, h) in cases {
            let words = Words::of(&p, &p);
            let over = p.iter().any(|(_, c)| c.abs() >= bound);
            assert_eq!(words.is_none(), over, "{p:?} ZED_TEST_SEED={seed}");
            let Some((w, wl, wh)) = words.as_ref().and_then(|w| w.at(&l.into(), &h.into())) else {
                declined += 1;
                continue;
            };
            let (bl, bh) = (BigInt::from(l), BigInt::from(h));
            let at = format!("{p:?} on {l}..={h}, ZED_TEST_SEED={seed}");
            let b = bounds(&p, &bl);
            let wb = small::bounds(&w.p, &wl);
            assert_eq!(
                b,
                wb.iter().map(|&x| BigInt::from(x)).collect::<Vec<_>>(),
                "{at}"
            );
            assert_eq!(
                may_hold_a_root(&p, &bl, &bh),
                small::may_hold_a_root(&w.p, &wl, &wh),
                "{at}"
            );
            for negate in [false, true] {
                assert_eq!(
                    positive_on(&p, &b, &bl, &bh, negate),
                    small::positive_on(&w.p, &wb, &wl, &wh, negate),
                    "{at}"
                );
            }
            assert_eq!(sign_at(&p, &bh), small::sign_at(&w.p, &wh), "{at}");
            checked += 1;
        }
        assert!(checked > 1000 && declined > 100, "{checked} {declined}");
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

    /// The quotient of a binomial `c0 + c1 x^g` is taken by the kernel's division of the
    /// magnitudes with the signs apart (plan row ROOTS-binomial-div): each sign of `c0` and `c1`,
    /// quotients that are not exact (`7 / 2`, where a truncated quotient is 3 and a floored one
    /// is -4 or 3 by the signs), equal signs, whose quotient is negative, and a dense `c1 x^3 -
    /// c1 r^3` of 8,192-bit `c1` and 4,096-bit `r`, divisor and quotient both past `DIV_LEAF`
    /// bits, so that the kernel's division runs and not num-bigint's below the leaf
    /// (`crate::num::fast::div_rem`), with `c1 r^3 + 1` among its neighbors, whose quotient
    /// `r^3` is a cube and whose remainder is 1. Negative controls: dropping the test of the
    /// signs gives `x^3 + 8` the root 2 as well; dropping the test of the remainder gives
    /// `c1 x^3 - (c1 r^3 + 1)` the root `r`.
    #[test]
    fn a_binomial_quotient_has_its_signs_and_its_remainder() {
        assert_eq!(roots(&poly(&[(5, -2), (0, 64)]), -50, 50), [2]);
        assert_eq!(roots(&poly(&[(3, -1), (0, -8)]), -50, 50), [-2]);
        assert_eq!(roots(&poly(&[(3, 1), (0, 8)]), -50, 50), [-2]);
        assert_eq!(roots(&poly(&[(3, 1), (0, -8)]), -50, 50), [2]);
        for (c1, c0) in [(2, -7), (-2, 7), (2, 7), (-2, -7), (3, 3), (-3, -3)] {
            assert_eq!(
                roots(&poly(&[(1, c1), (0, c0)]), -50, 50),
                match (c1, c0) {
                    (3, 3) | (-3, -3) => vec![-1],
                    _ => Vec::<i64>::new(),
                },
                "{c1} x + {c0}"
            );
            assert_eq!(
                roots(&poly(&[(4, c1), (0, c0)]), -50, 50),
                Vec::<i64>::new(),
                "{c1} x^4 + {c0}"
            );
        }
        let mut rng = crate::seed::Rng::new(0x6269_6e6f);
        let mut wide = |bits: u64| {
            let digits = (0..bits / 32).map(|_| rng.next_u64() as u32).collect();
            BigInt::from(BigUint::new(digits)) | (BigInt::one() << (bits - 1))
        };
        let (c1, r) = (wide(8192), wide(4096));
        let c0 = -(&c1 * &r * &r * &r);
        for (c1, c0, want) in [
            (c1.clone(), c0.clone(), vec![r.clone()]),
            (-&c1, -&c0, vec![r.clone()]),
            (c1.clone(), -&c0, vec![-&r]),
            (c1.clone(), &c0 + 1, vec![]),
            (c1.clone(), &c0 - 1, vec![]),
            (c1.clone(), &c0 - &c1, vec![]),
        ] {
            let f = Sparse::new([(0, c0), (3, c1)]);
            assert_eq!(integer_roots(&f, None, None), Roots::Listed(want));
        }
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
            // The proof is of the branch and bound alone: `2 tau + 8` units above 1.
            let (_, spent) = positive_roots_by(&terms, BigInt::from(2), None, Horner::Off);
            println!("tau = {tau}: {spent} units above 1 without the bound from above");
            assert_eq!(spent, u64::from(2 * tau + 8), "tau = {tau}");
            UNITS.with(|u| u.set(0));
            let tests = HORNER_TESTS.with(|n| n.get());
            let roots = integer_roots(&big(&terms), None, None);
            let units = UNITS.with(|u| u.get());
            assert_eq!(roots, Roots::Listed(vec![r.clone()]), "tau = {tau}");
            // As built, the bound from above is tried only once the units reach the trigger
            // `HORNER_COST D^2 / t`, `D = t - 1`, so not where the trigger is above the
            // `2 tau + 8` units; where it is not tried, the count is the proved one, and 1 for
            // the reflected polynomial.
            let d = (t - 1) as f64;
            let past = HORNER_COST * d * d / t as f64 > f64::from(2 * tau + 8);
            let tried = HORNER_TESTS.with(|n| n.get()) != tests;
            if past {
                assert!(!tried, "tau = {tau}: Horner tried");
            }
            if !tried {
                assert_eq!(units, u64::from(2 * tau + 9), "tau = {tau}");
            }
        }
    }

    /// Gemini B.2 of cross-review XR-lazy-and-kernel-batch-1 round 2: the cap `D bits(x) +
    /// need` on the scale of `search` was an unchecked u64 product. The polynomial `x^(2^62) -
    /// 3072 x^(2^62 - 1) - 1` on `2048..=4096` (no integer root; the root is just above 3072)
    /// has `D bits(x)` at least `12 * 2^62`. The Newton step from either end moves it by under 1
    /// at this degree, so NEWREFINE's `ratio` runs (red before the fix, 2026-11-27, local:
    /// "attempt to multiply with overflow" at the cap). Then the same without its constant
    /// term, whose root 3072 is found with and without a budget for a raised scale.
    #[test]
    fn search_on_a_sparse_high_degree_polynomial_does_not_overflow_the_scale_cap() {
        let d = 1u64 << 62;
        let p = vec![
            (0, BigInt::from(-1)),
            (d - 1, BigInt::from(-3072)),
            (d, BigInt::one()),
        ];
        let times_x: Vec<(u64, BigInt)> = (p[1..].iter())
            .map(|(e, c)| (*e, c * BigInt::from(*e)))
            .collect();
        let mut steps = 0;
        let (lo, hi) = (BigInt::from(2048), BigInt::from(4096));
        let found = search(
            &p,
            &times_x,
            None,
            lo.clone(),
            hi.clone(),
            &mut steps,
            u64::MAX,
        );
        assert_eq!(found, None, "steps {steps}");
        // With the integer root 3072, the same with no budget for a raised scale: the answer is
        // the exact signs', not the scale's.
        let q = &p[1..];
        let q_x: Vec<(u64, BigInt)> = (q.iter())
            .map(|(e, c)| (*e, c * BigInt::from(*e)))
            .collect();
        for budget in [u64::MAX, 0] {
            let mut steps = 0;
            let found = search(q, &q_x, None, lo.clone(), hi.clone(), &mut steps, budget);
            assert_eq!(
                found,
                Some(BigInt::from(3072)),
                "budget {budget}, steps {steps}"
            );
        }
    }
}
