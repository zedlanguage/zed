//! A row in one variable read as bounds on it, and the elimination of a variable `y` from a
//! lower bound and an upper bound on it by Fourier-Motzkin: the real shadow, Pugh's dark shadow,
//! and the test of whether the two have the same integer points (DRY-affine-crate-2026-11-26,
//! batch 2; the sites each routine replaced are named at it).
//!
//! The source: W. Pugh, "The Omega test: a fast and practical integer programming algorithm for
//! dependence analysis", Supercomputing '91, ACM, 1991, pp. 4-13, doi:10.1145/125826.125848,
//! and its expanded journal form, "A practical algorithm for exact array dependence analysis",
//! Communications of the ACM 35(8), 1992, pp. 102-114, doi:10.1145/135226.135233; sec. 2.3.2
//! of the author's expanded text (www.cs.umd.edu/~pugh/papers/omega.pdf). For a lower bound
//! `a·y >= α` and an upper bound `b·y <= β`, `a, b >= 1`, the real shadow is `a·β >= b·α` and the
//! dark shadow `a·β - b·α >= (a - 1)·(b - 1)`.
//!
//! Why the dark shadow has an integer `y` (the proof Pugh gives, written out): suppose no
//! integer `y` has `α <= a·y` and `b·y <= β`. Let `y0` be the least integer with `a·y0 >= α`;
//! then `a·(y0 - 1) < α`, so `a·(y0 - 1) <= α - 1`, that is `a·y0 <= α + a - 1`; and as `y0`
//! breaks the upper bound, `b·y0 > β`, so `b·y0 >= β + 1`. Multiplying the first by `b` and the
//! second by `a`: `a·β + a <= a·b·y0 <= b·α + a·b - b`, so `a·β - b·α <= a·b - a - b =
//! (a - 1)·(b - 1) - 1`, which the dark shadow excludes. Where `a == 1` or `b == 1` the gap is
//! 0 and the two shadows are one row: the exact shadow.

use zedc_int::int::{Int, i128_div_ceil, i128_div_floor};

/// The one end that `p·x + q >= 0`, `p` not zero, puts on the integer `x`: the least,
/// `⌈-q / p⌉`, for `p > 0`, and the greatest, `⌊q / -p⌋`, for `p < 0`; `None` for `p == 0` or
/// where a value passes `i128` (`-q` or `-p` at `i128::MIN`). The `i128` form of
/// [`zedc_int::int::row_bound`]. Why the ends: for `p > 0`, `p·x + q >= 0` is `x >= -q / p`,
/// whose least integer is the ceiling; for `p < 0` it is `x <= q / -p`, whose greatest is the
/// floor. Replaced the inline reads of zedc-preimage loops.rs (the box of a scope and the
/// limit of a written term). O(1).
pub fn i128_row_bound(p: i128, q: i128) -> Option<i128> {
    match p.signum() {
        1 => i128_div_ceil(q.checked_neg()?, p),
        -1 => i128_div_floor(q, p.checked_neg()?),
        _ => None,
    }
}

/// The bounds of `p·x + q >= 0` on the integer `x`, met into `lo` and `hi` (`None` an open
/// end): `Some(true)` once met, `Some(false)` where the row holds at no `x` (`p == 0` and
/// `q < 0`), and `None` where a value passes `i128`, with `lo` and `hi` left as they were. A
/// row with `p == 0` and `q >= 0` holds everywhere and changes nothing. Replaced `meet` of
/// zedc-presburger's two-pin reading and the inline loop of the row-sums plane's `shadow`.
/// O(1).
pub fn i128_meet(p: i128, q: i128, lo: &mut Option<i128>, hi: &mut Option<i128>) -> Option<bool> {
    if p == 0 {
        return Some(q >= 0);
    }
    let end = i128_row_bound(p, q)?;
    if p > 0 {
        *lo = Some(lo.map_or(end, |v| v.max(end)));
    } else {
        *hi = Some(hi.map_or(end, |v| v.min(end)));
    }
    Some(true)
}

/// The row in `x` that eliminating `y` from the lower bound `lo = (xl, yl, cl)`, the row
/// `xl·x + yl·y + cl >= 0` with `yl > 0`, and the upper bound `hi = (xu, yu, cu)` with `yu < 0`
/// gives: `(p, q)` for `p·x + q >= 0`, the real shadow, or with `dark` the dark shadow, `None`
/// where a value passes `i128`. In Pugh's form the bounds are `yl·y >= -(xl·x + cl)` and
/// `(-yu)·y <= xu·x + cu`, so the real shadow `yl·(xu·x + cu) + (-yu)·(-(xl·x + cl)) >= 0` is
/// `(yl·xu - yu·xl)·x + (yl·cu - yu·cl) >= 0`, and the dark one takes `(yl - 1)·(-yu - 1)` off
/// its constant (module note). Replaced the pair loops of the two-pin reading's `shadow` and
/// of the row-sums plane's `shadow`, which wrote the same products. `yl - 1` and `-yu - 1`
/// cannot overflow, as `yl > 0` and `-yu > 0` once `-yu` is formed. O(1).
pub fn i128_pair(
    (xl, yl, cl): (i128, i128, i128),
    (xu, yu, cu): (i128, i128, i128),
    dark: bool,
) -> Option<(i128, i128)> {
    debug_assert!(yl > 0 && yu < 0, "a lower and an upper bound on y");
    let p = yl.checked_mul(xu)?.checked_sub(yu.checked_mul(xl)?)?;
    let q = yl.checked_mul(cu)?.checked_sub(yu.checked_mul(cl)?)?;
    if !dark {
        return Some((p, q));
    }
    let gap = (yl - 1).checked_mul(yu.checked_neg()? - 1)?;
    Some((p, q.checked_sub(gap)?))
}

/// `(a - 1)·(b - 1)`, the amount the dark shadow of the lower bound `a·y >= α` and the upper
/// bound `b·y <= β` takes off the real one (module note), for `a, b >= 1`. Replaced the
/// product written out in `dark_is_real`, the Omega test's `combine` and `lossless_pair` of
/// zedc-presburger, and the slack of its exact projection's `shadow`. Two subtractions and
/// one product.
pub fn dark_gap(a: &Int, b: &Int) -> Int {
    &(a - &Int::ONE) * &(b - &Int::ONE)
}

/// Whether the real shadow `Σ c·x + k >= 0` (`coeffs` its coefficients `c`) and the dark shadow,
/// the same row with constant `k - d`, `d` the [`dark_gap`] of the pair, have the same integer
/// points, so that eliminating `y` by the real shadow alone is exact for this pair.
///
/// Proof. When `d == 0` the rows are one. With `g` the gcd of the coefficients, the form
/// `Σ c·x` takes exactly the multiples of `g` (Bezout), so when no coefficient is left (`g ==
/// 0`) the real row holds iff `k >= 0` and the dark one iff `k >= d`, which agree iff `k >= d`
/// or `k < 0`. Otherwise the real row holds where `g·t + k >= 0`, that is `t >= -⌊k/g⌋`, and
/// the dark one where `t >= -⌊(k - d)/g⌋`; with `k = q·g + r`, `0 <= r < g`, the second floor
/// is `q + ⌊(r - d)/g⌋`, and `r - d < g`, so the two are equal iff `r >= d`, that is
/// `k mod g >= d`. The gcd only shrinks as coefficients are read, and `r < g` for the final
/// `g`, so once the running gcd is at most `d` the final one is too and `r < d`: the answer is
/// `false` and the rest are not read.
///
/// Replaced `dark_is_real` of zedc-presburger's elimination of one-sided atoms, which compared
/// `⌊k/g⌋` with `⌊(k - d)/g⌋` (the same test) after reading every coefficient, and
/// `lossless_pair` of its Omega test, whose early stop this keeps. O(the coefficients read),
/// one gcd each.
pub fn dark_exact<'a>(k: &Int, d: &Int, coeffs: impl IntoIterator<Item = &'a Int>) -> bool {
    if d.is_zero() {
        return true;
    }
    let mut g = Int::ZERO;
    for c in coeffs {
        g = g.gcd(c);
        if g <= *d {
            return false;
        }
    }
    if g.is_zero() {
        *k >= *d || k.is_negative()
    } else {
        k.mod_floor(&g) >= *d
    }
}
