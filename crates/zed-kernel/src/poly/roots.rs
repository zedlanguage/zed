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
//!    root with `|x| >= 2` is a root of `g` and of `h`, and so of every piece ([`split`]). Each
//!    piece's degree is under `t` times the bits of the 1-norm, for `t` terms, whatever the
//!    degree of the whole.
//! 3. The positive roots of the piece of least degree, and those of its reflection `x -> -x`,
//!    are found by Rolle's theorem over the chain of sparse derivatives
//!    ([`positive_roots`]): dividing `q` by its least power and differentiating removes one
//!    term, so the chain has `t` members, and between two real roots of a member's successor
//!    the member is monotone. A sign change on a monotone stretch is found by Newton's method
//!    on the integers, each step that does not halve the bracket followed by a bisection
//!    ([`search`]).
//! 4. A candidate is kept when every other piece is 0 at it.

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
/// the degree: for `t` terms whose 1-norm has `B` bits, the split is O(t) additions, the piece
/// searched has degree `D < t (B + 1)`, its chain of derivatives `t` members, and each member
/// keeps at most the cells of its successor plus one per real root, under `t` by Descartes'
/// rule of signs, so O(t^2) cells and O(t^3) evaluations at the ends of monotone stretches in
/// all, plus O(t^2) searches, each of O(log B) steps by the magnitudes of its ends and then
/// O(log B) Newton steps where the roots are simple. Each evaluation is O(t) multiplications
/// of numbers of at most `D (B + 2)` bits. Given up: the O(t^3) count is reached only where
/// every derivative has as many real roots in the interval as the rule of signs allows, and is
/// above the O(t^2) of reading the cells once; and Newton's method converges only linearly near
/// a cluster of roots closer than 1, where the bisection after each step that does not halve
/// the bracket bounds a search by 2 (B + 2) steps. Hensel lifting of the roots modulo a prime
/// would cost O(D) per prime and digit, but a repeated root and a prime dividing the
/// discriminant each need a case of their own. Tests:
/// `l01_39_reduced_product::roots` (scaling in the degree and in the bits).
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
    let reflected: Vec<(u64, BigInt)> = (least.iter())
        .map(|(e, c)| (*e, if e % 2 == 1 { -c } else { c.clone() }))
        .collect();
    candidates.extend(
        positive_roots(&reflected, from(hi.map(|h| -h)), lo.map(|l| -l))
            .into_iter()
            .map(|y| -y),
    );
    for x in candidates {
        if (pieces.iter().enumerate()).all(|(i, p)| i == k || eval(p, &x).is_zero()) {
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
/// `a..=b` with `a >= 1`, `b` none for no upper end. Cauchy's bound `1 + max |c|` closes the
/// interval. The cells of each member of the chain of [`derived`] polynomials are found from
/// those of its successor, the last member, of one term, having none ([`cells`]).
fn positive_roots(p: &[(u64, BigInt)], a: BigInt, b: Option<BigInt>) -> Vec<BigInt> {
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
        below = cells(q, &below, &a, &hi);
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
fn cells(q: &[(u64, BigInt)], below: &[BigInt], a: &BigInt, hi: &BigInt) -> Vec<BigInt> {
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
            out.push(search(q, u, v, fu, fv));
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
fn search(
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

#[cfg(test)]
mod tests {
    use super::*;

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
