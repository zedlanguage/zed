//! Plane geometry over the integers, shared by the readers of two-variable regions
//! (zedc-presburger's `exact::guarded::two_pins`, `row_sums::plane` and `extend::plane`): the
//! cross and dot products, the order of directions by angle, the meeting point of two lines by
//! Cramer's rule, and the change of basis that Bezout's cofactors make unimodular.
//!
//! Each routine is written once over [`Coord`], a number with checked products and sums: on
//! [`Int`] they never fail, on `i128` they answer `None` past `i128`, which the `i128` readers
//! take as "read this part another way". A routine on `Int` answers `Some` always, so its
//! callers unwrap it.

use std::cmp::Ordering;

use zedc_int::int::Int;

/// A number the plane routines compute with. `None` is an overflow; [`Int`] has none.
pub trait Coord: Sized + Ord {
    /// 0.
    fn zero() -> Self;
    /// `self · o`.
    fn times(&self, o: &Self) -> Option<Self>;
    /// `self + o`.
    fn plus(&self, o: &Self) -> Option<Self>;
    /// `self - o`.
    fn minus(&self, o: &Self) -> Option<Self>;
    /// `-self`.
    fn negated(&self) -> Option<Self>;
    /// `(s, t)` with `s·a + t·b == 1`, `None` when `gcd(a, b) != 1` (or past `i128`).
    fn bezout(a: &Self, b: &Self) -> Option<(Self, Self)>;
}

// `#[inline]` on each method: they are not generic, so without it Rust compiles them once here
// and does not inline them into the generic routines that call them from other crates (common
// brief item 5, 2026-11-26). COUNTS
impl Coord for i128 {
    #[inline]
    fn zero() -> Self {
        0
    }
    #[inline]
    fn times(&self, o: &Self) -> Option<Self> {
        self.checked_mul(*o)
    }
    #[inline]
    fn plus(&self, o: &Self) -> Option<Self> {
        self.checked_add(*o)
    }
    #[inline]
    fn minus(&self, o: &Self) -> Option<Self> {
        self.checked_sub(*o)
    }
    #[inline]
    fn negated(&self) -> Option<Self> {
        self.checked_neg()
    }
    /// [`zed_numtheory::bezout_i128`], whose cofactors equal those of the signed Euclid the
    /// readers used before (`bezout_cofactors_give_the_gcd_and_are_the_least` in
    /// zed-numtheory).
    #[inline]
    fn bezout(a: &Self, b: &Self) -> Option<(Self, Self)> {
        let (g, s, t) = zed_numtheory::bezout_i128(*a, *b)?;
        (g == 1).then_some((s, t))
    }
}

impl Coord for Int {
    #[inline]
    fn zero() -> Self {
        Int::ZERO
    }
    #[inline]
    fn times(&self, o: &Self) -> Option<Self> {
        Some(self * o)
    }
    #[inline]
    fn plus(&self, o: &Self) -> Option<Self> {
        Some(self + o)
    }
    #[inline]
    fn minus(&self, o: &Self) -> Option<Self> {
        Some(self - o)
    }
    #[inline]
    fn negated(&self) -> Option<Self> {
        Some(-self)
    }
    /// [`Int::bezout`].
    #[inline]
    fn bezout(a: &Self, b: &Self) -> Option<(Self, Self)> {
        let (g, s, t) = a.bezout(b);
        (g == Int::ONE).then_some((s, t))
    }
}

/// The cross product `u × v = u.0·v.1 - u.1·v.0`: above 0 when `v` is counterclockwise from
/// `u` by less than a half-turn, 0 when they are parallel.
pub fn cross<T: Coord>(u: (&T, &T), v: (&T, &T)) -> Option<T> {
    u.0.times(v.1)?.minus(&u.1.times(v.0)?)
}

/// The dot product `u · v`.
pub fn dot<T: Coord>(u: (&T, &T), v: (&T, &T)) -> Option<T> {
    u.0.times(v.0)?.plus(&u.1.times(v.1)?)
}

/// The order of the angles of two directions, counterclockwise from the first axis, the axis
/// itself first: the half `y > 0` or `y == 0 < x` comes first, and within a half (where every
/// two directions are less than a half-turn apart) `u` comes before `v` exactly when `u × v >
/// 0`. Two directions of one angle are `Equal`. [`angle_cmp_from`] with `base = (1, 0)`, without
/// its two products. The cross product is taken only for two directions in one half, so a pair
/// in two halves is ordered even where it would pass `i128`.
pub fn angle_cmp<T: Coord>(u: (&T, &T), v: (&T, &T)) -> Option<Ordering> {
    let zero = T::zero();
    let upper = |w: (&T, &T)| *w.1 > zero || (*w.1 == zero && *w.0 > zero);
    match upper(v).cmp(&upper(u)) {
        Ordering::Equal => Some(zero.cmp(&cross(u, v)?)),
        o => Some(o),
    }
}

/// Whether `v` is in the half-turn counterclockwise from `base`, `base`'s own direction in and
/// the opposite one out: `base × v > 0`, or `v` along `base`.
pub fn first_half<T: Coord>(base: (&T, &T), v: (&T, &T)) -> Option<bool> {
    let c = cross(base, v)?;
    let zero = T::zero();
    if c != zero {
        return Some(c > zero);
    }
    Some(dot(base, v)? > zero)
}

/// The order of the angles of `u` and `v` counterclockwise from `base`, `base`'s own direction
/// first, by the same two steps as [`angle_cmp`]: the half from [`first_half`], then the cross
/// product within it.
pub fn angle_cmp_from<T: Coord>(base: (&T, &T), u: (&T, &T), v: (&T, &T)) -> Option<Ordering> {
    let (hu, hv) = (first_half(base, u)?, first_half(base, v)?);
    match hv.cmp(&hu) {
        Ordering::Equal => Some(T::zero().cmp(&cross(u, v)?)),
        o => Some(o),
    }
}

/// Where the lines `f.0·x + f.1·y = f.2` and `g.0·x + g.1·y = g.2` meet, by Cramer's rule, as
/// `(x·d, y·d, d)` with `d > 0`; `None` where they are parallel (`d = f × g = 0`), or past
/// `i128`. With `d = f.0·g.1 - f.1·g.0`, `x = (f.2·g.1 - g.2·f.1) / d` and `y = (f.0·g.2 -
/// g.0·f.2) / d`; the three are negated together when `d < 0`, which keeps the point. A line
/// written `a·x + b·y + c = 0` is this one with `-c`, which negates `x·d` and `y·d` and keeps
/// `d`.
pub fn cramer<T: Coord>(f: (&T, &T, &T), g: (&T, &T, &T)) -> Option<(T, T, T)> {
    let d = cross((f.0, f.1), (g.0, g.1))?;
    let zero = T::zero();
    if d == zero {
        return None;
    }
    let x = f.2.times(g.1)?.minus(&g.2.times(f.1)?)?;
    let y = f.0.times(g.2)?.minus(&g.0.times(f.2)?)?;
    Some(if d < zero {
        (x.negated()?, y.negated()?, d.negated()?)
    } else {
        (x, y, d)
    })
}

/// The unimodular change of coordinates that makes the primitive direction `(a, b)` the first
/// coordinate: `u = a·x + b·y` and `w = -t·x + s·y`, with `s·a + t·b == 1` from Bezout. Its
/// matrix `[[a, b], [-t, s]]` has determinant `a·s + b·t = 1`, so it maps the integer points
/// one to one onto the integer points, with inverse `x = s·u - b·w`, `y = t·u + a·w`. A row
/// `A·x + B·y` is `(A·s + B·t)·u + (B·a - A·b)·w` ([`Basis::row`]): put the inverse in, `A·(s·u
/// - b·w) + B·(t·u + a·w)`. A row `P·u + Q·w` is `(P·a - Q·t)·x + (P·b + Q·s)·y`
/// ([`Basis::back`]), by putting the two coordinates in.
pub struct Basis<T> {
    pub a: T,
    pub b: T,
    pub s: T,
    pub t: T,
}

impl<T: Coord + Clone> Basis<T> {
    /// The basis of the direction `(a, b)`; `None` when `gcd(a, b) != 1`, or past `i128`.
    pub fn new(a: T, b: T) -> Option<Self> {
        let (s, t) = T::bezout(&a, &b)?;
        Some(Basis { a, b, s, t })
    }

    /// The coefficients `(A·s + B·t, B·a - A·b)` of `u` and `w` in the row `A·x + B·y`.
    pub fn row(&self, big_a: &T, big_b: &T) -> Option<(T, T)> {
        let e = big_a.times(&self.s)?.plus(&big_b.times(&self.t)?)?;
        let d = big_b.times(&self.a)?.minus(&big_a.times(&self.b)?)?;
        Some((e, d))
    }

    /// The coefficients `(P·a - Q·t, P·b + Q·s)` of `x` and `y` in the row `P·u + Q·w`.
    pub fn back(&self, p: &T, q: &T) -> Option<(T, T)> {
        let x = p.times(&self.a)?.minus(&q.times(&self.t)?)?;
        let y = p.times(&self.b)?.plus(&q.times(&self.s)?)?;
        Some((x, y))
    }
}
