//! Integer affine forms `Σ c·x + k` of the compiler `zedc`'s constraint solvers: the terms
//! `x ↦ c` kept in a `BTreeMap` without zero coefficients, the merge that adds to them, the
//! division of a row by the gcd of its coefficients, and the primitive form of a list of terms.
//! Each routine here was written out at several sites of zedc-presburger and zedc-lattice
//! before (DRY-affine-crate-2026-11-26; the sites are named at each routine). The coefficients
//! are [`Coef`]: [`Int`] and [`Num`]. Module [`shadow`] reads a row in one variable as bounds
//! and eliminates a variable from a pair of bounds (the real and the dark shadow). Module
//! [`plane`] holds the plane geometry of the two-variable readers: cross and dot products,
//! angle order, Cramer's rule and the unimodular basis from Bezout. Module [`lines`] holds the
//! upper envelope of a set of lines (the convex hull trick) and the floor sum. Module [`space`]
//! holds vectors in a fixed dimension over the rationals, the completion of a primitive integer
//! vector to a unimodular matrix, LLL reduction under a quadratic form and Babai's nearest
//! plane point. Module [`equalities`] solves a system's unit equalities and substitutes them
//! out (the Gauss–Jordan step on unit pivots).

pub mod equalities;
pub mod lines;
pub mod plane;
pub mod shadow;
pub mod space;

use std::collections::BTreeMap;

use zedc_int::int::{Int, Num};

/// An integer coefficient: the operations the routines of this crate take of one.
pub trait Coef: Clone + Ord {
    /// Zero.
    const ZERO: Self;
    /// Whether the value is 0.
    fn is_zero(&self) -> bool;
    /// Whether the value is below 0.
    fn is_negative(&self) -> bool;
    /// Whether the value is 1 or -1.
    fn is_unit(&self) -> bool;
    /// The greatest common divisor, never negative.
    fn gcd(&self, other: &Self) -> Self;
    /// The quotient rounded toward -∞, for `d` not zero.
    fn div_floor(&self, d: &Self) -> Self;
    /// The remainder with the sign of `d` (0 when `d` divides the value), for `d` not zero.
    fn mod_floor(&self, d: &Self) -> Self;
    /// `self + other`.
    fn add(&self, other: &Self) -> Self;
    /// `self · other`.
    fn mul(&self, other: &Self) -> Self;
    /// `-self`.
    fn neg(&self) -> Self;
}

// `#[inline]` on each method: they are not generic, so without it Rust compiles them once here
// and does not inline them into the generic routines that call them from other crates (common
// brief item 5, 2026-11-26). Measured on one VM against
// eba97bf71, in instructions at n, two runs each: omega lossless_bands 1,221.5M to 1,221.1M,
// eliminations 60.95M to 60.95M, extend r5_diamond_unions 1,857.2M to 1,857.2M, l01_39
// chain 1,322.4M to 1,322.1M, all within 0.05% (8n the same); the cost the item names was
// not seen here, and the marks are kept against a later change of inlining heuristics.
impl Coef for Int {
    const ZERO: Int = Int::ZERO;
    #[inline]
    fn is_zero(&self) -> bool {
        Int::is_zero(self)
    }
    #[inline]
    fn is_negative(&self) -> bool {
        Int::is_negative(self)
    }
    #[inline]
    fn is_unit(&self) -> bool {
        Int::is_unit(self)
    }
    #[inline]
    fn gcd(&self, other: &Int) -> Int {
        Int::gcd(self, other)
    }
    #[inline]
    fn div_floor(&self, d: &Int) -> Int {
        Int::div_floor(self, d)
    }
    #[inline]
    fn mod_floor(&self, d: &Int) -> Int {
        Int::mod_floor(self, d)
    }
    #[inline]
    fn add(&self, other: &Int) -> Int {
        self + other
    }
    #[inline]
    fn mul(&self, other: &Int) -> Int {
        self * other
    }
    #[inline]
    fn neg(&self) -> Int {
        -self
    }
}

impl Coef for Num {
    const ZERO: Num = Num::ZERO;
    #[inline]
    fn is_zero(&self) -> bool {
        Num::is_zero(self)
    }
    #[inline]
    fn is_negative(&self) -> bool {
        *self < Num::ZERO
    }
    #[inline]
    fn is_unit(&self) -> bool {
        *self == Num::ONE || *self == -&Num::ONE
    }
    #[inline]
    fn gcd(&self, other: &Num) -> Num {
        Num::gcd(self, other)
    }
    #[inline]
    fn div_floor(&self, d: &Num) -> Num {
        Num::div_floor(self, d)
    }
    #[inline]
    fn mod_floor(&self, d: &Num) -> Num {
        Num::mod_floor(self, d)
    }
    #[inline]
    fn add(&self, other: &Num) -> Num {
        self + other
    }
    #[inline]
    fn mul(&self, other: &Num) -> Num {
        self * other
    }
    #[inline]
    fn neg(&self) -> Num {
        -self
    }
}

/// `terms[x] += c`, the entry removed when the sum is 0 and made when `x` had none, so that
/// `terms` keeps no zero coefficient. The key and `c` are cloned only when an entry is made.
/// O(log n).
///
/// The merge of every affine form here; it was written out as `Lin::plus_assign` (formula.rs),
/// `Side1::combine` and the substitution and Fourier-Motzkin pairs of `real_end`
/// (presburger.rs), each removing and inserting the key, or cloning it on every update.
pub fn add_term<K: Ord + Clone, V: Coef>(terms: &mut BTreeMap<K, V>, x: &K, c: &V) {
    if c.is_zero() {
        return;
    }
    match terms.get_mut(x) {
        Some(v) => {
            *v = v.add(c);
            if v.is_zero() {
                terms.remove(x);
            }
        }
        None => {
            terms.insert(x.clone(), c.clone());
        }
    }
}

/// `terms += other`, entry by entry as [`add_term`]. O(|other| log |terms|).
pub fn add_terms<K: Ord + Clone, V: Coef>(terms: &mut BTreeMap<K, V>, other: &BTreeMap<K, V>) {
    for (x, c) in other {
        add_term(terms, x, c);
    }
}

/// `terms += f · other`, entry by entry as [`add_term`]. O(|other| log |terms|).
pub fn add_scaled<K: Ord + Clone, V: Coef>(
    terms: &mut BTreeMap<K, V>,
    other: &BTreeMap<K, V>,
    f: &V,
) {
    if f.is_zero() {
        return;
    }
    for (x, c) in other {
        add_term(terms, x, &c.mul(f));
    }
}

/// `k · terms`: empty for `k` zero, so that no zero coefficient is kept; otherwise each
/// coefficient times `k`, none of which is 0 since neither factor is. O(n).
pub fn scaled<K: Ord + Clone, V: Coef>(terms: &BTreeMap<K, V>, k: &V) -> BTreeMap<K, V> {
    if k.is_zero() {
        return BTreeMap::new();
    }
    (terms.iter()).map(|(x, c)| (x.clone(), c.mul(k))).collect()
}

/// The greatest common divisor of `coeffs`, 0 for none. The fold stops at the first gcd of 1,
/// which no later coefficient changes (gcd(1, c) = 1), so a row with a unit coefficient near
/// its front costs that many steps and not its length.
pub fn content<'a, V: Coef + 'a>(coeffs: impl IntoIterator<Item = &'a V>) -> V {
    let mut g = V::ZERO;
    for c in coeffs {
        g = g.gcd(c);
        if g.is_unit() {
            break;
        }
    }
    g
}

/// What dividing a row `Σ c·x + k >= 0` or `== 0` by the gcd of its coefficients gives
/// ([`row_divisor`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Divisor<V> {
    /// The gcd is 1, or the row has no term (gcd 0): the row is kept as it is.
    Keep,
    /// An equation whose constant the gcd does not divide: no integer point holds it.
    Infeasible,
    /// Divide by this gcd, above 1 ([`divide_row`]).
    By(V),
}

/// How to divide the row `Σ c·x + k >= 0` (`eq` false) or `Σ c·x + k == 0` (`eq` true) with
/// the coefficients `coeffs` and constant `k` by the gcd `g` of its coefficients, keeping its
/// integer points.
///
/// Proof. With `g` dividing every coefficient, `Σ c·x = g·s` for an integer `s` at every
/// integer point, `s` the sum of the divided terms. An equation `g·s + k == 0` needs `g | k`,
/// else no point holds it ([`Divisor::Infeasible`]); with `g | k` it is `s + k/g == 0`. An
/// inequality `g·s + k >= 0` is `s >= -k/g`, which for integer `s` is `s >= ⌈-k/g⌉ =
/// -⌊k/g⌋`, so `s + ⌊k/g⌋ >= 0`; [`divide_row`] takes `⌊k/g⌋` by `div_floor`, which rounds
/// toward -∞ for either sign of `k` as `g > 0`. This is the normalization step of the Omega
/// test (Pugh, "The Omega test", Supercomputing '91, 1991, doi:10.1145/125826.125848, sec.
/// 2.1, read 2026-11-21: "we take the floor when dividing a_0 by g"). Tests: this crate's
/// `row_division_keeps_the_integer_points`, against every point of a box; it cannot catch a
/// fault that shows only outside the box it walks.
///
/// Was written out as `Con::reduced` (formula.rs), `tidy` and the `norm` of `real_end`
/// (presburger.rs), `normal` (exact/guarded.rs), and `normalized` and `tidied`
/// (exact/projection.rs).
pub fn row_divisor<'a, V: Coef + 'a>(
    coeffs: impl IntoIterator<Item = &'a V>,
    k: &V,
    eq: bool,
) -> Divisor<V> {
    let g = content(coeffs);
    if g.is_zero() || g.is_unit() {
        return Divisor::Keep;
    }
    if eq && !k.mod_floor(&g).is_zero() {
        return Divisor::Infeasible;
    }
    Divisor::By(g)
}

/// The row `terms, k` divided by `g` above 0, which divides every coefficient: each
/// coefficient divided exactly, the constant rounded down ([`row_divisor`] has the proof that
/// this keeps the integer points of `>= 0`, and of `== 0` when `g | k`). O(n).
pub fn divide_row<K, V: Coef>(terms: &mut BTreeMap<K, V>, k: &mut V, g: &V) {
    for c in terms.values_mut() {
        *c = c.div_floor(g);
    }
    *k = k.div_floor(g);
}

/// The inequality `terms, k >= 0` divided by the gcd of its coefficients when that is above 1,
/// its constant rounded down: [`row_divisor`] and [`divide_row`] for a row that is no
/// equation, the same integer points (the proof is at [`row_divisor`]). O(n).
pub fn tighten_ge<K, V: Coef>(terms: &mut BTreeMap<K, V>, k: &mut V) {
    if let Divisor::By(g) = row_divisor(terms.values(), k, false) {
        divide_row(terms, k, &g);
    }
}

/// The primitive form of `terms`: the terms divided by the gcd `g` of their coefficients, the
/// signs flipped when the first is below zero, so that the first coefficient is above zero.
/// Two lists of terms that are multiples of one another (`2x - 4y` and `-x + 2y`) have one
/// primitive form, and `terms = s·g·form` with `s` -1 when `flipped`, else 1. `None` for no
/// terms. O(n).
///
/// Was written out twice as the `canonical_form` closure of presburger.rs (the vacuous check of
/// `sweep_disjoint`'s leftover items, and `cell_items`' index of placed equations).
pub fn primitive_form<K: Clone, V: Coef>(terms: &BTreeMap<K, V>) -> Option<Primitive<K, V>> {
    let flipped = terms.values().next()?.is_negative();
    let g = content(terms.values());
    let form = (terms.iter())
        .map(|(x, c)| {
            let q = c.div_floor(&g);
            (x.clone(), if flipped { q.neg() } else { q })
        })
        .collect();
    Some(Primitive { form, flipped, g })
}

/// The primitive form of a list of terms ([`primitive_form`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Primitive<K, V> {
    /// The terms over `g`, the first coefficient above zero.
    pub form: Vec<(K, V)>,
    /// Whether the signs were flipped: the first coefficient of the terms was below zero.
    pub flipped: bool,
    /// The gcd of the coefficients, above zero.
    pub g: V,
}

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;

#[cfg(test)]
mod tests;
