//! Vectors and lattices in a fixed dimension `N` over the exact rationals [`Q`] and the integers
//! [`Int`]: sums and inner products, the cross product and the inverse of a 3×3 matrix, the
//! primitive integer multiple of a rational vector, the completion of a primitive integer vector
//! to a unimodular matrix, and the LLL reduction of `Zᴺ` under a positive definite quadratic
//! form with Babai's nearest plane point. Moved from zedc-solvers `live3` (Lenstra's method in
//! dimension three, its one caller; DRY-affine-crate-2026-11-26, batch 4), where the proofs of
//! the bounds that method draws from them stay, at `live3::reduce` and `live3::simplex`.
//!
//! Sources. A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring polynomials with rational
//! coefficients", Math. Ann. 261 (1982), 515-534, doi:10.1007/bf01457454, read 2026-11-21 (the
//! paper's text, pp. 516-517; the full citation, with what was checked, is in zedc-solvers'
//! `lib.rs`, "References"): a basis is reduced when every `|μ_ij| <= 1/2` for `j < i` (1.4) and
//! `|b_i* + μ_i,i-1·b_i-1*|² >= 3/4·|b_i-1*|²` (1.5); the proof of (1.6) gives `|b_j*|² <=
//! 2^(i-j)·|b_i*|²`. L. Babai, "On Lovász' lattice reduction and the nearest lattice point
//! problem", Combinatorica 6 (1986), 1-13, doi:10.1007/BF02579403, read 2026-11-21, sec. 4, p. 5,
//! (4.3): the nearest plane point `w` of `x` has `|x - w|² <= (|b1*|² + ... + |bd*|²) / 4`.

use std::array;

use zedc_int::int::Int;
use zedc_int::q::Q;

fn zero() -> Q {
    Q::of(Int::ZERO)
}

/// `floor(c + 1/2)`, the nearest integer to `c`, the greater on a tie.
// `#[inline]`: not generic, and called from live3 in zedc-solvers (common brief item 5).
#[inline]
pub fn nearest(c: &Q) -> Int {
    c.add(&Q::new(Int::ONE, Int::from(2))).floor()
}

/// `a + b`, entry by entry.
pub fn add<const N: usize>(a: &[Q; N], b: &[Q; N]) -> [Q; N] {
    array::from_fn(|i| a[i].add(&b[i]))
}

/// `a - b`, entry by entry.
pub fn sub<const N: usize>(a: &[Q; N], b: &[Q; N]) -> [Q; N] {
    array::from_fn(|i| a[i].sub(&b[i]))
}

/// `Σ a_i·b_i`.
pub fn dot<const N: usize>(a: &[Q; N], b: &[Q; N]) -> Q {
    (0..N).fold(zero(), |s, i| s.add(&a[i].mul(&b[i])))
}

/// The cross product `a × b`.
#[inline]
pub fn cross(a: &[Q; 3], b: &[Q; 3]) -> [Q; 3] {
    [0, 1, 2].map(|i| {
        let (j, k) = ((i + 1) % 3, (i + 2) % 3);
        a[j].mul(&b[k]).sub(&a[k].mul(&b[j]))
    })
}

/// The inverse of the matrix whose columns are `c`, which is invertible: row `i` of the inverse
/// is the cross product of the other two columns, in cyclic order, over the determinant
/// `c0·(c1 × c2)`. (Row `i` times column `j` is `c_j·(c_i+1 × c_i+2) / det`, the triple product,
/// which is `det / det = 1` for `j = i` and 0 otherwise, as a triple product with a repeated
/// vector is 0.)
#[inline]
pub fn inverse(c: &[[Q; 3]; 3]) -> [[Q; 3]; 3] {
    let det = dot(&c[0], &cross(&c[1], &c[2]));
    [0, 1, 2].map(|i| cross(&c[(i + 1) % 3], &c[(i + 2) % 3]).map(|x| x.div(&det)))
}

/// The integer multiple of `v`, which is not zero, whose entries have no common factor: `v`
/// times the least common multiple of its denominators, over the gcd of the numerators that
/// gives. The sign is that of `v`.
pub fn primitive<const N: usize>(v: &[Q; N]) -> [Int; N] {
    let l = v.iter().fold(Int::ONE, |l, c| {
        let g = l.gcd(c.denom());
        &l.div_floor(&g) * c.denom()
    });
    let n: [Int; N] = array::from_fn(|i| v[i].numer() * &l.div_floor(v[i].denom()));
    let g = n.iter().fold(Int::ZERO, |g, c| g.gcd(c));
    n.map(|c| c.div_floor(&g))
}

/// The identity matrix over the integers, as `N` rows.
fn identity<const N: usize>() -> [[Int; N]; N] {
    array::from_fn(|i| array::from_fn(|j| Int::from(i64::from(i == j))))
}

/// The columns of a unimodular matrix `V` with `u·V = e1`, for `u` with no common factor: the
/// column operations of Euclid's algorithm on the entries of `u`, applied to the identity.
/// Each step subtracts an integer multiple of one column from another, or swaps two, so `V`
/// stays unimodular and `u·V` stays the vector of remainders `r`; Euclid's algorithm leaves
/// `r = (±gcd(u), 0, ..., 0)` = `(±1, 0, ..., 0)`, and the first column is negated when the
/// sign is `-`.
pub fn complete<const N: usize>(u: &[Int; N]) -> [[Int; N]; N] {
    let mut r = u.clone();
    let mut v = identity::<N>();
    for j in 1..N {
        while !r[j].is_zero() {
            let c = r[0].div_floor(&r[j]);
            r[0] = &r[0] - &(&c * &r[j]);
            let (first, rest) = v.split_at_mut(1);
            for (x, y) in first[0].iter_mut().zip(&rest[j - 1]) {
                *x = &*x - &(&c * y);
            }
            r.swap(0, j);
            v.swap(0, j);
        }
    }
    if r[0].is_negative() {
        for x in &mut v[0] {
            *x = -&*x;
        }
    }
    debug_assert!(r[0].is_unit(), "a direction with no common factor");
    v
}

/// `xᵀ·F·y` for the matrix `form` of a quadratic form `F`.
pub fn inner<const N: usize>(form: &[[Q; N]; N], x: &[Q; N], y: &[Q; N]) -> Q {
    let mut s = zero();
    for i in 0..N {
        for j in 0..N {
            s = s.add(&x[i].mul(&form[i][j]).mul(&y[j]));
        }
    }
    s
}

/// A basis of `Zᴺ` reduced under a quadratic form, with its Gram–Schmidt vectors.
pub struct Reduced<const N: usize> {
    /// The basis vectors `b_i`, integer and unimodular together.
    pub basis: [[Int; N]; N],
    /// The Gram–Schmidt vectors `b_i*` under the form.
    pub star: [[Q; N]; N],
    /// Their squared lengths `|b_i*|²` under the form, each above zero.
    pub len: [Q; N],
}

/// The Gram–Schmidt vectors of `b` under `form`, their squared lengths, and the coefficients
/// `μ_ij = ⟨b_i, b_j*⟩ / |b_j*|²` for `j < i` (zero elsewhere).
type GramSchmidt<const N: usize> = ([[Q; N]; N], [Q; N], [[Q; N]; N]);

fn gram_schmidt<const N: usize>(form: &[[Q; N]; N], b: &[[Int; N]; N]) -> GramSchmidt<N> {
    let asq = |v: &[Int; N]| v.clone().map(Q::of);
    let mut st: [[Q; N]; N] = array::from_fn(|i| asq(&b[i]));
    let mut len: [Q; N] = array::from_fn(|_| zero());
    let mut mu: [[Q; N]; N] = array::from_fn(|_| array::from_fn(|_| zero()));
    for i in 0..N {
        for j in 0..i {
            mu[i][j] = inner(form, &asq(&b[i]), &st[j]).div(&len[j]);
            st[i] = sub(&st[i], &st[j].each_ref().map(|x| x.mul(&mu[i][j])));
        }
        len[i] = inner(form, &st[i], &st[i]);
    }
    (st, len, mu)
}

/// The LLL reduction with `δ = 3/4` of the standard basis of `Zᴺ` under the positive definite
/// form `form` [LLL 1982, pp. 516-517, (1.4) and (1.5), cited in the module comment]. The loop
/// size-reduces `b_k` against `b_k-1, ..., b_1` (each `|μ_kj| <= 1/2` after), then tests the
/// Lovász condition (1.5) in the form `|b_k*|² >= (3/4 - μ_k,k-1²)·|b_k-1*|²` (the two are the
/// same, as `b_k* + μ_k,k-1·b_k-1*` has squared length `|b_k*|² + μ_k,k-1²·|b_k-1*|²` by the
/// orthogonality of the `b*`): it moves on when it holds, and swaps `b_k` with `b_k-1` and steps
/// back otherwise. The result satisfies (1.4) and (1.5), so `|b_i-1*|² <= 2·|b_i*|²` for each
/// `i`. It ends, since each swap multiplies the product of the Gram determinants of the
/// leading sub-bases by a factor below 3/4 and size reduction leaves it unchanged, while that
/// product is bounded below by a positive constant for a positive definite form with rational
/// entries (the termination argument of LLL 1982, p. 521, written here from memory of the
/// paper; the page was not checked again on 2026-11-26). Exact: the arithmetic is in [`Q`].
/// The Gram–Schmidt data is computed afresh at each step, `O(N³)` operations on `Q` a step;
/// the one caller has `N = 3`, where that is a constant.
pub fn lll<const N: usize>(form: &[[Q; N]; N]) -> Reduced<N> {
    let mut b = identity::<N>();
    let delta = Q::new(Int::from(3), Int::from(4));
    let mut k = 1;
    while k < N {
        for j in (0..k).rev() {
            let (_, _, mu) = gram_schmidt(form, &b);
            let c = nearest(&mu[k][j]);
            if !c.is_zero() {
                let (low, high) = b.split_at_mut(k);
                for (x, y) in high[0].iter_mut().zip(&low[j]) {
                    *x = &*x - &(&c * y);
                }
            }
        }
        let (_, len, mu) = gram_schmidt(form, &b);
        let m2 = mu[k][k - 1].mul(&mu[k][k - 1]);
        if len[k] >= delta.sub(&m2).mul(&len[k - 1]) {
            k += 1;
        } else {
            b.swap(k, k - 1);
            k = (k - 1).max(1);
        }
    }
    let (star, len, _) = gram_schmidt(form, &b);
    Reduced {
        basis: b,
        star,
        len,
    }
}

/// Babai's nearest plane point of `target` in the lattice of `r.basis` [Babai 1986, sec. 4,
/// (4.3), cited in the module comment]: from the last basis vector down, subtract from the rest
/// `t` (at first `target`) the integer multiple `c_i` of `b_i` nearest to its coordinate along
/// `b_i*`, `c_i = nearest(⟨t, b_i*⟩ / |b_i*|²)`. Then `target - z = Σ c'_i·b_i*` with each
/// `|c'_i| <= 1/2`, so `|target - z|² <= (|b1*|² + ... + |bN*|²) / 4` under the form. The point
/// `z = target - t` is a sum of integer multiples of the basis, so it has integer entries.
pub fn nearest_plane<const N: usize>(
    form: &[[Q; N]; N],
    r: &Reduced<N>,
    target: &[Q; N],
) -> [Int; N] {
    let mut t = target.clone();
    for i in (0..N).rev() {
        let c = Q::of(nearest(&inner(form, &t, &r.star[i]).div(&r.len[i])));
        t = sub(&t, &r.basis[i].clone().map(|x| Q::of(x).mul(&c)));
    }
    sub(target, &t).map(|x| {
        let (n, d) = x.into_parts();
        debug_assert!(d == Int::ONE, "a lattice point");
        n
    })
}
