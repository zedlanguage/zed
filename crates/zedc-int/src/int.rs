//! The solver's integers (DESIGN.md sec:domains, "exact, over unbounded integers"): unbounded,
//! with `i128` arithmetic while a value fits, since nearly all of them do. Zed's `int` is
//! unbounded, so this module goes at the port (ZED_PORT_GAPS.md).

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Mul, Neg, Sub};
use std::sync::{Arc, Mutex};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
use zed_kernel::num::{
    TooLarge, div_rem_uint, gcd_uint, is_prime, mul_int, mul_uint, pow_uint, read_digits, room,
    to_decimal,
};

/// The greatest common divisor by Stein's binary algorithm: shifts and subtractions, no
/// division.
macro_rules! stein {
    ($name:ident, $t:ty) => {
        fn $name(mut a: $t, mut b: $t) -> $t {
            if a == 0 || b == 0 {
                return a | b;
            }
            let s = (a | b).trailing_zeros();
            a >>= a.trailing_zeros();
            loop {
                b >>= b.trailing_zeros();
                if a > b {
                    (a, b) = (b, a);
                }
                b -= a;
                if b == 0 {
                    return a << s;
                }
            }
        }
    };
}

stein!(stein64, u64);
stein!(stein128, u128);

/// An integer. A value that fits in `i128` is always `Small`, so that two equal values have
/// one form.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Repr {
    Small(i128),
    Big(Arc<BigInt>),
}

/// An unbounded integer.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Int(Repr);

impl Default for Int {
    fn default() -> Int {
        Int::ZERO
    }
}

impl From<i32> for Int {
    fn from(v: i32) -> Int {
        Int(Repr::Small(v.into()))
    }
}

impl From<i64> for Int {
    fn from(v: i64) -> Int {
        Int(Repr::Small(v.into()))
    }
}

impl From<usize> for Int {
    fn from(v: usize) -> Int {
        Int(Repr::Small(v as i128))
    }
}

impl From<i128> for Int {
    fn from(v: i128) -> Int {
        Int(Repr::Small(v))
    }
}

impl From<BigInt> for Int {
    fn from(v: BigInt) -> Int {
        Int(match i128::try_from(&v) {
            Ok(s) => Repr::Small(s),
            Err(_) => Repr::Big(Arc::new(v)),
        })
    }
}

impl Int {
    /// Zero.
    pub const ZERO: Int = Int(Repr::Small(0));
    /// One.
    pub const ONE: Int = Int(Repr::Small(1));

    fn big(&self) -> Cow<'_, BigInt> {
        match &self.0 {
            Repr::Small(v) => Cow::Owned(BigInt::from(*v)),
            Repr::Big(v) => Cow::Borrowed(v),
        }
    }

    /// The value, when it fits in `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match self.0 {
            Repr::Small(v) => Some(v),
            Repr::Big(_) => None,
        }
    }

    /// Whether the value is below zero.
    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v < 0,
            Repr::Big(v) => v.sign() == Sign::Minus,
        }
    }

    /// Whether the value is above zero.
    pub fn is_positive(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v > 0,
            Repr::Big(v) => v.sign() == Sign::Plus,
        }
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        self.0 == Repr::Small(0)
    }

    /// Whether the value is odd, in O(1) time whatever its size.
    pub fn is_odd(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => v & 1 == 1,
            Repr::Big(v) => v.is_odd(),
        }
    }

    /// Whether the value is 1 or -1.
    pub fn is_unit(&self) -> bool {
        matches!(self.0, Repr::Small(1 | -1))
    }

    /// The absolute value.
    pub fn abs(&self) -> Int {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    /// The greatest common divisor, never negative.
    pub fn gcd(&self, other: &Int) -> Int {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => {
                let (a, b) = (a.unsigned_abs(), b.unsigned_abs());
                // In 64 bits when both fit, where each step is one instruction.
                let g = match (u64::try_from(a), u64::try_from(b)) {
                    (Ok(a), Ok(b)) => u128::from(stein64(a, b)),
                    _ => stein128(a, b),
                };
                i128::try_from(g).map_or_else(|_| BigInt::from(g).into(), Int::from)
            }
            _ => self.big().gcd(&other.big()).into(),
        }
    }

    /// `self / m` rounded down, for `m` of either sign and not zero.
    pub fn div_floor(&self, m: &Int) -> Int {
        match (&self.0, &m.0) {
            // In 64 bits when both fit, where a 128-bit division is many times slower; the
            // one quotient that overflows, `MIN / -1`, is left to the next width.
            (Repr::Small(a), Repr::Small(b)) => match (i64::try_from(*a), i64::try_from(*b)) {
                (Ok(a), Ok(b)) if (a, b) != (i64::MIN, -1) => Integer::div_floor(&a, &b).into(),
                _ if (*a, *b) != (i128::MIN, -1) => Integer::div_floor(a, b).into(),
                _ => self.big().div_floor(&m.big()).into(),
            },
            _ => self.big().div_floor(&m.big()).into(),
        }
    }

    /// The remainder of [`Int::div_floor`], which has the sign of `m`.
    pub fn mod_floor(&self, m: &Int) -> Int {
        match (&self.0, &m.0) {
            // `MIN mod -1` is 0, but `rem` overflows computing it, as `MIN / -1` does.
            (Repr::Small(_), Repr::Small(-1)) => Int::ZERO,
            (Repr::Small(a), Repr::Small(b)) => match (i64::try_from(*a), i64::try_from(*b)) {
                (Ok(a), Ok(b)) => Integer::mod_floor(&a, &b).into(),
                _ => Integer::mod_floor(a, b).into(),
            },
            _ => self.big().mod_floor(&m.big()).into(),
        }
    }
}

impl Add for &Int {
    type Output = Int;

    fn add(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_add(*b)
        {
            return v.into();
        }
        (&*self.big() + &*other.big()).into()
    }
}

impl Sub for &Int {
    type Output = Int;

    fn sub(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_sub(*b)
        {
            return v.into();
        }
        (&*self.big() - &*other.big()).into()
    }
}

impl Mul for &Int {
    type Output = Int;

    fn mul(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            // Two values of 64 bits have a product that fits in 128, with no overflow test.
            if let (Ok(x), Ok(y)) = (i64::try_from(*a), i64::try_from(*b)) {
                return (i128::from(x) * i128::from(y)).into();
            }
            if let Some(v) = a.checked_mul(*b) {
                return v.into();
            }
        }
        mul_int(&self.big(), &other.big()).into()
    }
}

impl Neg for &Int {
    type Output = Int;

    fn neg(self) -> Int {
        if let Repr::Small(a) = self.0
            && let Some(v) = a.checked_neg()
        {
            return v.into();
        }
        (-&*self.big()).into()
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => a.cmp(b),
            (Repr::Big(a), Repr::Big(b)) => a.cmp(b),
            // A big value lies outside every small one.
            (Repr::Big(a), Repr::Small(_)) => {
                if a.sign() == Sign::Minus {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (Repr::Small(_), Repr::Big(b)) => {
                if b.sign() == Sign::Minus {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Repr::Small(v) => write!(f, "{v}"),
            Repr::Big(v) => write_decimal(f, v),
        }
    }
}

/// The form of a [`Num`]. A value that fits in `i64` is always `Small`; a value outside `i64`
/// is `Big`, or `Kept` when it was made from a power and lies outside `i128`. A `Big` and a
/// `Kept` may hold the same value, so equality and hashing go by value, not by form.
#[derive(Clone, Debug)]
enum Word {
    Small(i64),
    Big(Arc<BigInt>),
    Kept(Box<Kept>),
}

/// `(c_1 * core_1 + ... + c_n * core_n + d) / den`, kept unexpanded, where each core is a
/// product of powers of integers and of floor roots. A bound such as that of
/// `x ^ 100000000 + 1`, `3 ^ 100000000 + 5 ^ 99999999` or `floor(2 ^ (100000000 / 3))` is
/// then built and compared in time polynomial in the bits of the numbers written here, not in
/// the bits of the value. Invariants: `n >= 1`; the cores are in decreasing order of value and
/// no two are equal by [`Core::same`]; no `c_i` is zero; the terms whose cores are powers of
/// one integer are folded ([`fold`]); `den >= 1` divides the numerator; the `c_i`, `d` and
/// `den` have no common factor; the value lies outside `i128`, and `negative` is its sign.
/// Equal values may have different forms.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Kept {
    terms: Vec<(BigInt, Core)>,
    d: BigInt,
    den: BigUint,
    negative: bool,
}

/// A factor of a [`Core`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Atom {
    /// An integer at least 2.
    Int(BigUint),
    /// `floor(rad ^ (1 / k))`, with `k >= 2`, `rad` above zero with cores of `Int` atoms only,
    /// and the root at least `2^127`. A root of a root is one root of the first radicand, so
    /// the nesting stops here.
    Root {
        rad: Box<Kept>,
        k: BigUint,
        memo: Memo,
    },
}

/// The finest approximation of a root found so far, with its precision in bits. A root is
/// approximated by bisection, at a cost of `O(bits)` products per call, and one root is met by
/// many comparisons and sums, so each approximation is kept, shared by every copy of the atom,
/// and a coarser one is its truncation. It takes no part in the order or equality of atoms.
#[derive(Clone, Debug, Default)]
struct Memo(Arc<Mutex<Option<(u64, Approx)>>>);

impl Memo {
    fn get(&self) -> std::sync::MutexGuard<'_, Option<(u64, Approx)>> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

impl PartialEq for Memo {
    fn eq(&self, _: &Memo) -> bool {
        true
    }
}

impl Eq for Memo {}

impl PartialOrd for Memo {
    fn partial_cmp(&self, o: &Memo) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Memo {
    fn cmp(&self, _: &Memo) -> Ordering {
        Ordering::Equal
    }
}

/// `a_1 ^ e_1 * ... * a_m ^ e_m`, with `m >= 1`, the atoms distinct and in increasing order,
/// and every `e_i >= 1`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Core(Vec<(Atom, BigUint)>);

/// The sign of `x`, as a `bool` that holds for values below zero.
fn below_zero(x: &BigInt) -> bool {
    x.sign() == Sign::Minus
}

/// `x * 2^sx` against `y * 2^sy`, for magnitudes.
fn mag_scaled_cmp(x: &BigUint, sx: &BigInt, y: &BigUint, sy: &BigInt) -> Ordering {
    match (x.bits(), y.bits()) {
        (0, 0) => return Ordering::Equal,
        (0, _) => return Ordering::Less,
        (_, 0) => return Ordering::Greater,
        _ => {}
    }
    let (tx, ty) = (sx + x.bits(), sy + y.bits());
    if tx != ty {
        return tx.cmp(&ty);
    }
    // The totals are equal, so the difference of the shifts is at most the bits of x or y.
    if sx >= sy {
        let d = u64::try_from(&(sx - sy)).expect("at most the bits of y");
        (x << d).cmp(y)
    } else {
        let d = u64::try_from(&(sy - sx)).expect("at most the bits of x");
        x.cmp(&(y << d))
    }
}

/// `x * 2^sx` against `y * 2^sy`.
fn scaled_cmp(x: &BigInt, sx: &BigInt, y: &BigInt, sy: &BigInt) -> Ordering {
    match x.sign().cmp(&y.sign()) {
        Ordering::Equal => {}
        o => return o,
    }
    let o = mag_scaled_cmp(x.magnitude(), sx, y.magnitude(), sy);
    if below_zero(x) { o.reverse() } else { o }
}

/// `floor(x / 2^s)` for `s >= 0`. A shift past the bits of `x` gives -1 or 0 without
/// shifting, so `s` may be far larger than `x`.
fn floor_shr(x: &BigInt, s: &BigInt) -> BigInt {
    match u64::try_from(s) {
        Ok(s) if s <= x.bits() => x >> s,
        _ => BigInt::from(-i32::from(below_zero(x))),
    }
}

/// `ceil(x / 2^s)` for `s >= 0`.
fn ceil_shr(x: &BigInt, s: &BigInt) -> BigInt {
    -floor_shr(&-x, s)
}

/// A value to `bits` bits: it lies in `lo * 2^shift ..= hi * 2^shift`. It is exact when
/// `lo == hi`.
#[derive(Clone, Debug)]
struct Approx {
    lo: BigInt,
    hi: BigInt,
    shift: BigInt,
}

impl Approx {
    fn exact(v: BigInt) -> Approx {
        Approx {
            lo: v.clone(),
            hi: v,
            shift: BigInt::ZERO,
        }
    }

    /// `v` to `bits` bits: exact when `v` has at most `bits` bits. It reads only the bits it
    /// keeps, so its cost does not grow with the bits of `v`.
    fn of(v: &BigInt, bits: u64) -> Approx {
        let have = v.bits();
        if have <= bits {
            return Approx::exact(v.clone());
        }
        let t = have - bits;
        let lo = v >> t;
        let hi = if v.trailing_zeros().is_some_and(|z| z < t) {
            &lo + 1u32
        } else {
            lo.clone()
        };
        Approx {
            lo,
            hi,
            shift: BigInt::from(t),
        }
    }

    fn is_exact(&self) -> bool {
        self.lo == self.hi
    }

    /// Drops the low bits past `bits`, rounding `lo` down and `hi` up.
    fn truncate(mut self, bits: u64) -> Approx {
        let have = self.lo.bits().max(self.hi.bits());
        if have <= bits {
            return self;
        }
        let t = have - bits;
        let up = self.hi.trailing_zeros().is_some_and(|z| z < t);
        self.lo >>= t;
        self.hi >>= t;
        if up {
            self.hi += 1u32;
        }
        self.shift += t;
        self
    }

    /// The product, to `bits` bits.
    fn mul(&self, o: &Approx, bits: u64) -> Approx {
        let (lo, hi) = if !below_zero(&self.lo) && !below_zero(&o.lo) {
            (mul_int(&self.lo, &o.lo), mul_int(&self.hi, &o.hi))
        } else {
            let mut ps = [
                mul_int(&self.lo, &o.lo),
                mul_int(&self.lo, &o.hi),
                mul_int(&self.hi, &o.lo),
                mul_int(&self.hi, &o.hi),
            ];
            ps.sort();
            let [lo, _, _, hi] = ps;
            (lo, hi)
        };
        Approx {
            lo,
            hi,
            shift: &self.shift + &o.shift,
        }
        .truncate(bits)
    }

    /// The sum, to `bits` bits. When the shifts differ by at most `bits`, the operand with the
    /// larger shift is moved down to the other exactly; otherwise the one with the smaller
    /// shift is rounded outward to the larger, so a small term beside a huge one costs no
    /// more than the huge one's `bits`.
    fn add(&self, o: &Approx, bits: u64) -> Approx {
        let (a, b) = if self.shift >= o.shift {
            (self, o)
        } else {
            (o, self)
        };
        let diff = &a.shift - &b.shift;
        match u64::try_from(&diff) {
            Ok(d) if d <= bits => Approx {
                lo: (&a.lo << d) + &b.lo,
                hi: (&a.hi << d) + &b.hi,
                shift: b.shift.clone(),
            },
            _ => Approx {
                lo: &a.lo + floor_shr(&b.lo, &diff),
                hi: &a.hi + ceil_shr(&b.hi, &diff),
                shift: a.shift.clone(),
            },
        }
        .truncate(bits)
    }

    /// The quotient by `den >= 1`, to `bits` bits; exact when `self` is an exact multiple of
    /// `den`.
    fn div(self, den: &BigUint, bits: u64) -> Approx {
        if den.is_one() {
            return self;
        }
        let den = BigInt::from(den.clone());
        if self.is_exact() && self.shift.is_zero() && self.lo.is_multiple_of(&den) {
            return Approx::exact(self.lo / den);
        }
        let t = bits + den.bits();
        Approx {
            lo: Integer::div_floor(&(self.lo << t), &den),
            hi: Integer::div_ceil(&(self.hi << t), &den),
            shift: self.shift - t,
        }
        .truncate(bits)
    }

    /// `self ^ exp`, for `self >= 0`, by squaring: `O(bits of exp)` products. Each product
    /// adds a relative error of at most `2^-bits`, and a power multiplies the relative error
    /// by its exponent.
    fn pow(&self, exp: &BigUint, bits: u64) -> Approx {
        let mut r = Approx::exact(BigInt::from(1u32));
        for i in (0..exp.bits()).rev() {
            r = r.mul(&r, bits);
            if exp.bit(i) {
                r = r.mul(self, bits);
            }
        }
        r
    }

    /// Whether every value in `self` is below every value in `o`.
    fn below(&self, o: &Approx) -> bool {
        scaled_cmp(&self.hi, &self.shift, &o.lo, &o.shift) == Ordering::Less
    }

    /// Whether every value in `self` is at most `y * 2^sy`.
    fn hi_at_most(&self, y: &BigInt, sy: &BigInt) -> bool {
        scaled_cmp(&self.hi, &self.shift, y, sy) != Ordering::Greater
    }
}

/// `base ^ exp`, written out: its cost is that of the value's digits.
fn expand_pow(base: &BigUint, exp: &BigUint) -> BigUint {
    let mut m = BigUint::from(1u32);
    for i in (0..exp.bits()).rev() {
        m = mul_uint(&m, &m);
        if exp.bit(i) {
            m = mul_uint(&m, base);
        }
    }
    m
}

/// `(r, m)` with `b == r ^ m` and `r` not a perfect power, for `b >= 2`. Square roots are taken
/// while `b` is a square; then each odd prime `p` below the bits of `b` is tried as the index of
/// a root ([`OddPart::root`]), and tried again after it succeeds. A root found for a larger
/// prime is no power of a smaller one, since `b` would then have been. An index whose root
/// fits in a word costs `O(log p)` word operations; a wider one is first tested by residues
/// ([`OddPart::passes`], all from one remainder tree), and one that passes costs a 2-adic root
/// of `bits / p` bits. So the cost is at most `O(M(n) log n)` for `n` the bits of `b` and `M(n)`
/// the cost of a product of `n` bits, whatever the exponent `b` is raised to, and near `M(n)`
/// when the residues reject most indices; a found root, or an index that passes the filters
/// there without being one, adds one `p`-th power.
fn least_root(mut b: BigUint) -> (BigUint, BigUint) {
    let mut m = BigUint::from(1u32);
    // r >= 2, so r ^ p has at least p + 1 bits.
    while b.bits() > 2 {
        let r = b.sqrt();
        if mul_uint(&r, &r) != b {
            break;
        }
        b = r;
        m *= 2u32;
    }
    let prime = odd_primes_below(b.bits());
    let mut odd = OddPart::of(&b);
    let mut p = 3u64;
    while p < b.bits() {
        if prime[(p / 2) as usize]
            && let Some(r) = odd.root(p)
        {
            b = r;
            m *= p;
            odd = OddPart::of(&b);
        } else {
            p += 2;
        }
    }
    (b, m)
}

/// `prime[i]` holds when `2 * i + 1` is prime, for `2 * i + 1 < n`: a sieve of Eratosthenes over
/// the odd numbers, in `O(n log log n)`.
fn odd_primes_below(n: u64) -> Vec<bool> {
    let len = usize::try_from(n.div_ceil(2)).expect("the bits of a base held in memory");
    let mut prime = vec![true; len];
    if let Some(one) = prime.first_mut() {
        *one = false;
    }
    let mut i = 1;
    while (2 * i + 1) * (2 * i + 1) < 2 * len {
        if prime[i] {
            let q = 2 * i + 1;
            // Odd multiples of q from q * q.
            for j in ((q * q) / 2..len).step_by(q) {
                prime[j] = false;
            }
        }
        i += 1;
    }
    prime
}

/// Primes below `2^64` by which [`OddPart::root`] tests a candidate root before its power.
const TEST_PRIMES: [u64; 3] = [
    18_446_744_073_709_551_557,
    9_223_372_036_854_775_783,
    4_611_686_018_427_387_847,
];

/// The bound below the odd primes `q` by which [`OddPart::root`] rejects an index `p` dividing
/// `q - 1` before it looks for a root wider than one word: if `o == r ^ p` then
/// `o ^ ((q - 1) / p) == 1` modulo `q` unless `q` divides `o`, and a number that is no `p`-th
/// power passes one such `q` with chance about `1 / p`, since the `p`-th powers are one in `p`
/// of the units modulo `q`. No prime below it is 1 modulo an index above `FILTER_BOUND / 2`,
/// so each index wider than a word also gets the least prime that is 1 modulo it ([`Filter`]).
const FILTER_BOUND: u64 = 1024;

/// The residues of `o` by which [`OddPart::passes`] rejects an index: `(q, o mod q)` for each
/// odd prime `q` below [`FILTER_BOUND`], and `(p, q, o mod q)` for each index `p` whose root is
/// wider than one word, in increasing order of `p`, with `q` the least prime that is 1 modulo
/// `p`.
struct Filter {
    small: Vec<(u64, u64)>,
    wide: Vec<(u64, u64, u64)>,
}

/// `b = 2^v * o` with `o` odd, `o` modulo each of [`TEST_PRIMES`], and, once a root wider than
/// one word is looked for, the residues of `o` in a [`Filter`].
struct OddPart {
    v: u64,
    o: BigUint,
    residues: [u64; 3],
    filter: std::cell::OnceCell<Filter>,
}

impl OddPart {
    fn of(b: &BigUint) -> OddPart {
        let v = b.trailing_zeros().expect("a base is at least 2");
        let o = b >> v;
        let residues = TEST_PRIMES.map(|q| u64::try_from(&o % q).expect("below q"));
        OddPart {
            v,
            o,
            residues,
            filter: std::cell::OnceCell::new(),
        }
    }

    /// The [`Filter`] of `o`. The indices wider than a word are the odd primes `p` with
    /// `64 * p < n`, for `n` the bits of `o`, and the least prime `q = k * p + 1` is found by
    /// trying `k = 2, 4, ...`, about `ln q` tries ([`is_prime`]). All the residues come from
    /// one remainder tree ([`remainders`]): the primes, multiplied into words, are `O(n / 64)`
    /// bits together, so the tree costs `O(M(n))`, where one division of `o` per word cost
    /// `O(n)` per index and `O(n^2 / log n)` in all.
    fn filter(&self) -> &Filter {
        self.filter.get_or_init(|| {
            let prime = odd_primes_below(FILTER_BOUND);
            let small = (1..FILTER_BOUND / 2)
                .filter(|&i| prime[i as usize])
                .map(|i| 2 * i + 1);
            let n = self.o.bits();
            let index = odd_primes_below((n - 1) / 64 + 1);
            let wide: Vec<(u64, u64)> = (1..index.len() as u64)
                .filter(|&i| index[i as usize])
                .map(|i| {
                    let p = 2 * i + 1;
                    let q = (1u64..)
                        .map(|k| 2 * k * p + 1)
                        .find(|&q| is_prime(q))
                        .expect("a prime in each progression");
                    (p, q)
                })
                .collect();
            let qs: Vec<u64> = small.chain(wide.iter().map(|&(_, q)| q)).collect();
            // The primes multiplied into words: `ends[w]` is one past the last prime of word `w`.
            let (mut ms, mut ends) = (Vec::new(), Vec::new());
            let mut end = 0;
            while end < qs.len() {
                let mut m = 1u64;
                while let Some(next) = qs.get(end).and_then(|&q| m.checked_mul(q)) {
                    m = next;
                    end += 1;
                }
                ms.push(m);
                ends.push(end);
            }
            let mut rq = Vec::with_capacity(qs.len());
            for (end, om) in ends.into_iter().zip(remainders(&self.o, &ms)) {
                rq.extend(qs[rq.len()..end].iter().map(|&q| om % q));
            }
            let cut = qs.len() - wide.len();
            Filter {
                small: qs[..cut].iter().zip(&rq).map(|(&q, &r)| (q, r)).collect(),
                wide: wide
                    .iter()
                    .zip(&rq[cut..])
                    .map(|(&(p, q), &r)| (p, q, r))
                    .collect(),
            }
        })
    }

    /// Whether `o` is a `p`-th power residue modulo each prime of the [`Filter`] that is 1
    /// modulo `p` and does not divide `o`, as it is when `o` is a `p`-th power.
    fn passes(&self, p: u64) -> bool {
        let residue = |q: u64, oq: u64| oq == 0 || pow_mod(oq, (q - 1) / p, q) == 1;
        let filter = self.filter();
        filter
            .small
            .iter()
            .all(|&(q, oq)| !(q - 1).is_multiple_of(p) || residue(q, oq))
            && match filter.wide.binary_search_by_key(&p, |&(p, _, _)| p) {
                Ok(i) => {
                    let (_, q, oq) = filter.wide[i];
                    residue(q, oq)
                }
                Err(_) => true,
            }
    }

    /// The `r` with `r ^ p == 2^v * o`, for an odd prime `p`, when there is one. Such an `r`
    /// is `2^(v / p)` times the odd `p`-th root of `o`, which is below `2^s` for `s` the bits of
    /// `o` over `p`, rounded up, and so is the one odd `p`-th root of `o` modulo `2^s`
    /// ([`odd_root_mod_pow2`]). That candidate is checked by its bit count and modulo
    /// [`TEST_PRIMES`], in time of order its own bits, and only then by its `p`-th power.
    fn root(&self, p: u64) -> Option<BigUint> {
        if !self.v.is_multiple_of(p) {
            return None;
        }
        let shift = self.v / p;
        if self.o.is_one() {
            return Some(BigUint::from(1u32) << shift);
        }
        let n = self.o.bits();
        let s = n.div_ceil(p);
        if s <= 64 {
            // A root of at most 64 bits, as for every index above the bits over 64, is found
            // and filtered in one word, with nothing allocated: the root modulo `2^64` cut to
            // `s` bits is the one modulo `2^s`.
            let low = self.o.iter_u64_digits().next().expect("o is odd");
            let r = odd_root_mod_word(low, p) & (u64::MAX >> (64 - s));
            let rb = u64::from(u64::BITS - r.leading_zeros());
            if n <= p * (rb - 1) || n > p * rb {
                return None;
            }
            let agree = TEST_PRIMES
                .iter()
                .zip(&self.residues)
                .all(|(&q, &oq)| pow_mod(r % q, p, q) == oq);
            let r = BigUint::from(r);
            return (agree && pow_uint(&r, p) == self.o).then(|| r << shift);
        }
        if !self.passes(p) {
            return None;
        }
        let r = odd_root_mod_pow2(&self.o, p, s);
        // r ^ p has more than p * (bits(r) - 1) bits and at most p * bits(r).
        let rb = r.bits();
        if n <= p * (rb - 1) || n > p * rb {
            return None;
        }
        let agree = TEST_PRIMES.iter().zip(&self.residues).all(|(&q, &oq)| {
            let rq = u64::try_from(&r % q).expect("below q");
            pow_mod(rq, p, q) == oq
        });
        (agree && pow_uint(&r, p) == self.o).then(|| r << shift)
    }
}

/// `x mod m` for each `m` of `ms`, by a remainder tree (Bernstein, "Fast multiplication and
/// its applications", 2008): the `ms` are multiplied in pairs up to one product
/// `P`, `x` is reduced modulo `P` once, and each remainder is reduced modulo the two products
/// below it. For `B` the bits of `P` the cost is that of the one division and
/// `O(M(B) log B)`, where one division of `x` per `m` costs `O(bits of x)` each.
fn remainders(x: &BigUint, ms: &[u64]) -> Vec<u64> {
    // levels[0] holds the ms; each level above holds the products of pairs of the one below.
    // A level of odd length moves its last product up unchanged, so a product with no
    // partner is stored once, on the highest level it reaches.
    let mut levels: Vec<Vec<BigUint>> = vec![ms.iter().map(|&m| BigUint::from(m)).collect()];
    while let Some(below) = levels.last_mut()
        && below.len() > 1
    {
        let alone = (below.len() % 2 == 1).then(|| below.pop().expect("odd length"));
        let mut up: Vec<BigUint> = below
            .as_chunks::<2>()
            .0
            .iter()
            .map(|[a, b]| mul_uint(a, b))
            .collect();
        up.extend(alone);
        levels.push(up);
    }
    let Some(top) = levels.pop() else {
        return Vec::new();
    };
    let mut rems: Vec<BigUint> = top.iter().map(|t| div_rem_uint(x, t).1).collect();
    while let Some(nodes) = levels.pop() {
        let mut down = Vec::with_capacity(2 * rems.len());
        for (i, r) in rems.into_iter().enumerate() {
            match nodes.get(2 * i..2 * i + 2) {
                Some([a, b]) => {
                    down.push(div_rem_uint(&r, a).1);
                    down.push(div_rem_uint(&r, b).1);
                }
                // A product moved up from this level: `r` is already reduced modulo it.
                _ => down.push(r),
            }
        }
        rems = down;
    }
    rems.iter()
        .map(|r| u64::try_from(r).expect("below a word"))
        .collect()
}

/// `x ^ e` modulo `q`, for `q` below `2^64`.
fn pow_mod(x: u64, mut e: u64, q: u64) -> u64 {
    let mul = |a: u64, b: u64| (u128::from(a) * u128::from(b) % u128::from(q)) as u64;
    let (mut base, mut out) = (x % q, 1 % q);
    while e > 0 {
        if e & 1 == 1 {
            out = mul(out, base);
        }
        base = mul(base, base);
        e >>= 1;
    }
    out
}

/// The odd `x < 2^k` with `x ^ p == o` modulo `2^k`, for `o` odd, `p` an odd prime and
/// `k >= 1`. Since `p` is odd, `x -> x ^ p` permutes the odd residues modulo `2^k`, so there is
/// exactly one. Newton's method over the 2-adic integers finds it: `p * x ^ (p - 1)` is odd, so
/// each step doubles the bits that are right. The first 64 bits come from
/// [`odd_root_mod_word`], with the inverse of the derivative there, in one word; from there the
/// inverse of the derivative is carried from step to step and refined by one Newton step of
/// its own, so the cost is `O(M(k) log p)`, with `M(k)` that of a product of `k` bits, and a
/// root of `k` bits takes `log2(k / 64)` steps on numbers wider than a word, not `log2 k`.
fn odd_root_mod_pow2(o: &BigUint, p: u64, k: u64) -> BigUint {
    let low = o.iter_u64_digits().next().expect("o is odd");
    let word = odd_root_mod_word(low, p);
    if k <= 64 {
        return BigUint::from(word & (u64::MAX >> (64 - k)));
    }
    let mut x = BigUint::from(word);
    // The inverse of the derivative at `x`, right modulo 2^64.
    let mut z = BigUint::from(inverse_mod_word(pow_word(word, p - 1).wrapping_mul(p)));
    let mut j = 64;
    while j < k {
        j = (2 * j).min(k);
        let unit = BigUint::from(1u32) << j;
        let mask = &unit - 1u32;
        let y = pow_mod_pow2(&x, p - 1, &mask);
        // x ^ p - o, and the derivative p * x ^ (p - 1), modulo 2^j.
        let f = (mul_uint(&y, &x) + &unit - (o & &mask)) & &mask;
        let d = (y * p) & &mask;
        // `x` changed only above the bits that were right at the last step, so `z`, the
        // inverse of the last derivative to half of those bits, is that of this one too; one
        // step `z * (2 - d * z)` doubles them, past the `j - j / 2` bits the update reads.
        z = mul_uint(&z, &((&unit + 2u32 - (mul_uint(&d, &z) & &mask)) & &mask)) & &mask;
        let step = mul_uint(&f, &z) & &mask;
        x = (x + unit - step) & mask;
    }
    x
}

/// `b ^ e` modulo `2^64`.
fn pow_word(mut b: u64, mut e: u64) -> u64 {
    let mut out = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            out = out.wrapping_mul(b);
        }
        b = b.wrapping_mul(b);
        e >>= 1;
    }
    out
}

/// The inverse of an odd `d` modulo `2^64`: `d` is its own inverse modulo 8, and each step
/// `z * (2 - d * z)` doubles the bits that are right, so five steps make 96.
fn inverse_mod_word(d: u64) -> u64 {
    let mut z = d;
    for _ in 0..5 {
        z = z.wrapping_mul(2u64.wrapping_sub(d.wrapping_mul(z)));
    }
    z
}

/// [`odd_root_mod_pow2`] in one word: the odd `x` with `x ^ p == o` modulo `2^64`, for `o` odd
/// and `p` odd, by six Newton steps from `x = 1`, each doubling the bits that are right.
fn odd_root_mod_word(o: u64, p: u64) -> u64 {
    let mut x = 1u64;
    for _ in 0..6 {
        let y = pow_word(x, p - 1);
        let f = y.wrapping_mul(x).wrapping_sub(o);
        // The inverse of the odd derivative `p * x ^ (p - 1)`.
        x = x.wrapping_sub(f.wrapping_mul(inverse_mod_word(y.wrapping_mul(p))));
    }
    x
}

/// `x ^ e` modulo `mask + 1`, a power of 2.
fn pow_mod_pow2(x: &BigUint, e: u64, mask: &BigUint) -> BigUint {
    let mut out = BigUint::from(1u32);
    for i in (0..u64::BITS - e.leading_zeros()).rev() {
        out = mul_uint(&out, &out) & mask;
        if e >> i & 1 == 1 {
            out = mul_uint(&out, x) & mask;
        }
    }
    out
}

/// A coprime base of integers at least 2: integers at least 2, pairwise coprime, such that
/// each given integer is a product of their powers (for 4 and 8, the base 2; for 6, 2 and 3,
/// the base 2 and 3). An integer that shares a factor `g > 1` with an element of the base
/// replaces that element by `g` and the two parts of them prime to `g` ([`strip`], which takes
/// every power of `g` out at once, so `2^n * 3` against 2 is one replacement, not `n`), each to
/// be placed in turn. Each replacement divides the product of all the integers not yet placed
/// and the base by at least `g`, so there are at most as many as the bits of that product, and
/// in fact at most about as many as its distinct prime factors, each with one gcd per element.
fn coprime_base<'a>(xs: impl Iterator<Item = &'a BigUint>) -> Vec<BigUint> {
    let mut base: Vec<BigUint> = Vec::new();
    let mut todo: Vec<BigUint> = xs.cloned().collect();
    while let Some(mut x) = todo.pop() {
        if x.is_one() {
            continue;
        }
        let shared = base.iter().enumerate().find_map(|(i, b)| {
            let g = gcd_uint(b, &x);
            (!g.is_one()).then_some((i, g))
        });
        match shared {
            None => base.push(x),
            Some((i, g)) => {
                let mut b = base.swap_remove(i);
                strip(&mut b, &g);
                strip(&mut x, &g);
                todo.push(b);
                todo.push(x);
                todo.push(g);
            }
        }
    }
    base
}

/// The exponents of `∏ b ^ e` over a coprime `base` of which every `b` is a product of
/// powers, one per element of the base.
fn exponents_over<'a>(
    base: &[BigUint],
    powers: impl Iterator<Item = (&'a BigUint, &'a BigUint)>,
) -> Vec<BigUint> {
    let mut out = vec![BigUint::ZERO; base.len()];
    for (b, e) in powers {
        let mut rest = b.clone();
        for (c, x) in base.iter().zip(&mut out) {
            let k = strip(&mut rest, c);
            if k > 0 {
                *x += e * k;
            }
        }
        debug_assert!(rest.is_one(), "a coprime base of {b}");
    }
    out
}

/// The multiplicity `k` of `c >= 2` in `rest`, divided out of it. For `c` a power of 2, `2^t`,
/// `k` is the trailing zeros of `rest` over `t`, rounded down, taken out by one shift.
/// Otherwise, after one division by `c`, which ends it when `c` does not divide `rest`, the
/// powers `P_i = c ^ (2^i)` are built by squaring. A power is tested against `rest` by its
/// remainder when its bits are at least the square of the bits of the last one tested (`c`
/// first) and their square is at most the bits of `rest`. The squaring stops at the first
/// `P_J` that fails such a test or is above `rest`, with `x = rest mod P_J`, or at the last
/// `P_(J-1)` whose square is surely above `rest`, with
/// `x = rest`. Either way the multiplicity left is below `2^J`, `x` has it, and `x` is below
/// `P_J`. From `i = J - 1` down to 0, `x` is replaced by `x / P_i`, adding `2^i` to `k`, when
/// `P_i` divides it, and by `x mod P_i` when not, which has the same multiplicity, below `2^i`,
/// since `c` to that multiplicity plus one divides `P_i`; either way `x` is below `P_i` after,
/// so the widths halve. Last, `rest` is divided once by `c ^ k`, the product of the `P_i` of
/// the binary digits of `k`. With the kernel's arithmetic a test of `P_i` costs about
/// `n log d` for `n` bits of `rest` and `d` of `P_i`, and the tested `log d` at least double
/// and stay below `log n / 2`, so the tests cost O(n log n); the squares and the steps down cost O(M(w)) for `w` the bits of
/// `P_J`, at most `n` and at most about the square of the bits of `c ^ k`; and the last
/// division O(n log (k bits(c))). So `strip` costs O(M(n)) = O(n log n), and about O(n) for a
/// small `c ^ k` (item SCALE-fix-strip-odd). Dividing all of `rest` by each `P_i` on the way
/// up cost O(n log^2 n), and num-bigint's division made that O(n^2) for a small `c`; building
/// the powers up to the width of `rest` before any test cost O(M(n)) for every `k`, and grew
/// 85 times in bytes on `equality_over_a_wide_base_scales_with_its_bits`.
fn strip(rest: &mut BigUint, c: &BigUint) -> u64 {
    if c.count_ones() == 1 {
        let t = c.bits() - 1;
        let k = rest.trailing_zeros().expect("rest is at least 1") / t;
        *rest >>= k * t;
        return k;
    }
    let (q, r) = div_rem_uint(rest, c);
    if !r.is_zero() {
        return 0;
    }
    *rest = q;
    let mut pows: Vec<Cow<'_, BigUint>> = vec![Cow::Borrowed(c)];
    // The bits of the last power tested by its remainder.
    let mut tested = 0u64;
    let mut x: Cow<'_, BigUint> = loop {
        let top = pows.last().expect("the power left by the last step");
        if **top > *rest {
            pows.pop();
            break Cow::Borrowed(&*rest);
        }
        // Complexity tradeoff: a test by remainder costs about `n log d`, the kernel's division
        // of `n` bits by `d` (about ten products of `d` bits for each `d` bits of `rest`). It
        // ends the squaring early when `c ^ k` is small, which keeps `strip` near O(n) there;
        // above `d = sqrt(n)` the squares left cost less than a test, so none is made there.
        // Without tests the squares cost O(M(n)) whatever `k` (85 times the bytes from 65536 to
        // 524288 bits on `equality_over_a_wide_base_scales_with_its_bits`); with a test at
        // every width allowed by the first rule the odd-base test took 13.9 times the
        // instructions from 2^19 to 2^22 digits, against 11.1 (2026-11-07).
        if top.bits() >= tested * tested && top.bits() * top.bits() <= rest.bits() {
            tested = top.bits();
            let (_, r) = div_rem_uint(rest, top);
            if !r.is_zero() {
                pows.pop();
                break Cow::Owned(r);
            }
        }
        // `top ^ 2` is at least `2 ^ (2 (bits - 1))`.
        if 2 * (top.bits() - 1) >= rest.bits() {
            break Cow::Borrowed(&*rest);
        }
        let square = mul_uint(top, top);
        pows.push(Cow::Owned(square));
    };
    let mut more = 0u64;
    for (i, pw) in pows.iter().enumerate().rev() {
        let (q, r) = div_rem_uint(&x, pw);
        x = Cow::Owned(match r.is_zero() {
            true => {
                more += 1 << i;
                q
            }
            false => r,
        });
    }
    drop(x);
    // The smaller powers first, so that each product is of a number by a wider one.
    let divisor = pows
        .iter()
        .enumerate()
        .filter(|(i, _)| more >> i & 1 == 1)
        .map(|(_, pw)| pw)
        .fold(None, |acc: Option<Cow<'_, BigUint>>, pw| {
            Some(match acc {
                None => Cow::Borrowed(&**pw),
                Some(a) => Cow::Owned(mul_uint(&a, pw)),
            })
        });
    if let Some(d) = divisor {
        let (q, r) = div_rem_uint(rest, &d);
        debug_assert!(r.is_zero(), "c ^ {more} divides what is left");
        *rest = q;
    }
    1 + more
}

impl Atom {
    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        match self {
            Atom::Int(b) => Approx::of(&BigInt::from(b.clone()), bits),
            Atom::Root { rad, k, memo } => {
                if let Some((have, a)) = &*memo.get()
                    && *have >= bits
                {
                    return a.clone().truncate(bits);
                }
                let a = root_approx(rad, k, bits).0;
                *memo.get() = Some((bits, a.clone()));
                a
            }
        }
    }

    /// The value, written out: for a root, its cost is that of a root of the radicand's
    /// digits.
    fn expand(&self) -> BigUint {
        match self {
            Atom::Int(b) => b.clone(),
            Atom::Root { rad, k, .. } => rad.expand().into_parts().1.nth_root(
                u32::try_from(k).expect("a root of at least 2^127 of a radicand held in memory"),
            ),
        }
    }

    /// Bounds on the bits of the value and of the widest number [`Atom::expand`] builds.
    fn widths(&self) -> (BigUint, BigUint) {
        match self {
            Atom::Int(b) => (BigUint::from(b.bits()), BigUint::from(b.bits())),
            Atom::Root { rad, k, .. } => {
                let (value, widest) = rad.widths();
                (value / k + 1u32, widest)
            }
        }
    }
}

impl Core {
    /// `base ^ exp`, for `base >= 2`, over the least integer of which `base` is a power
    /// ([`least_root`]): `9 ^ e` is `3 ^ (2 * e)`, so that equal powers of integers are
    /// equal in form, and powers of one integer fold ([`fold`]).
    fn power(base: BigUint, exp: BigUint) -> Core {
        let (base, m) = least_root(base);
        Core(vec![(Atom::Int(base), exp * m)])
    }

    /// The base and exponent of a power of one integer.
    fn int_power(&self) -> Option<(&BigUint, &BigUint)> {
        match self.0.as_slice() {
            [(Atom::Int(b), e)] => Some((b, e)),
            _ => None,
        }
    }

    /// Whether every atom is an integer, so that the value has residues without its digits.
    fn is_int(&self) -> bool {
        self.0.iter().all(|(a, _)| matches!(a, Atom::Int(_)))
    }

    /// The greatest common divisor of the exponents: the value is a perfect power of it.
    fn exps_gcd(&self) -> BigUint {
        self.0
            .iter()
            .fold(BigUint::ZERO, |g, (_, e)| Integer::gcd(&g, e))
    }

    /// Whether two cores have one value. The atoms on which they differ in form are taken
    /// from both by one merge of their atom lists, with exponents less those of the other;
    /// the integers among them are written over a coprime base ([`coprime_base`]), on which a
    /// product of powers has one form, so `6 ^ e * 5 ^ f` and `2 ^ e * 3 ^ e * 5 ^ f`
    /// are found equal by 6, 2 and 3 alone. The cost is that of the coprime base of the
    /// integers written differently, nothing for the atoms the cores share.
    // Complexity tradeoff: two cores whose roots differ in form are taken to differ here,
    // though two roots of different radicands may have one value (the floor cube roots of
    // `2 ^ (3 * e + 1)` and of `2 ^ (3 * e + 1) + 1`), so such cores are found equal only by
    // `value_cmp` once the approximations are exact, at the bits of the value; the answer
    // stays exact. Why: whether two floor roots are equal is whether a `k`-th power lies
    // between their radicands, which needs the roots' digits. Trigger: a sum, difference or
    // comparison of kept values holding roots of different radicands with one floor. Test:
    // `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`
    // (the two cube roots above); COMPLEXITY.md S33. A complete solution would keep a root in
    // a form that a floor determines, as the least radicand with that floor, found as a kept
    // value: the open case of a root of a sum at `Kept::root`.
    fn same(&self, o: &Core) -> bool {
        if self == o {
            return true;
        }
        let mut l: Vec<(&Atom, Cow<'_, BigUint>)> = Vec::new();
        let mut r = Vec::new();
        let (mut i, mut j) = (self.0.iter().peekable(), o.0.iter().peekable());
        loop {
            match (i.peek(), j.peek()) {
                (Some((a, e)), Some((b, f))) => match a.cmp(b) {
                    Ordering::Less => {
                        l.push((a, Cow::Borrowed(e)));
                        i.next();
                    }
                    Ordering::Greater => {
                        r.push((b, Cow::Borrowed(f)));
                        j.next();
                    }
                    Ordering::Equal => {
                        match e.cmp(f) {
                            Ordering::Less => r.push((b, Cow::Owned(f - e))),
                            Ordering::Greater => l.push((a, Cow::Owned(e - f))),
                            Ordering::Equal => {}
                        }
                        i.next();
                        j.next();
                    }
                },
                (Some(_), None) => {
                    l.extend(i.map(|(a, e)| (a, Cow::Borrowed(e))));
                    break;
                }
                (None, _) => {
                    r.extend(j.map(|(b, f)| (b, Cow::Borrowed(f))));
                    break;
                }
            }
        }
        fn ints<'a>(
            v: &'a [(&'a Atom, Cow<'a, BigUint>)],
        ) -> Option<Vec<(&'a BigUint, &'a BigUint)>> {
            v.iter()
                .map(|(a, e)| match a {
                    Atom::Int(b) => Some((b, &**e)),
                    Atom::Root { .. } => None,
                })
                .collect()
        }
        let (Some(l), Some(r)) = (ints(&l), ints(&r)) else {
            return false;
        };
        // A product of powers of integers at least 2 is 1 only when it is empty.
        if l.is_empty() || r.is_empty() {
            return false;
        }
        let base = coprime_base(l.iter().chain(&r).map(|(b, _)| *b));
        exponents_over(&base, l.into_iter()) == exponents_over(&base, r.into_iter())
    }

    /// The order of the values: equal in form, else at 64 bits, else by [`Core::same`], else
    /// at twice as many bits and more until they are apart. Equal values agree at 64 bits, so
    /// `same` runs only for cores that do.
    fn value_cmp(&self, o: &Core) -> Ordering {
        if self == o {
            return Ordering::Equal;
        }
        let (a, b) = (self.approx(64), o.approx(64));
        if a.below(&b) {
            return Ordering::Less;
        }
        if b.below(&a) {
            return Ordering::Greater;
        }
        if self.same(o) {
            return Ordering::Equal;
        }
        approx_cmp(128, |bits| self.approx(bits), |bits| o.approx(bits))
    }

    /// The product.
    fn times(&self, o: &Core) -> Core {
        if let (Some((b1, e1)), Some((b2, e2))) = (self.int_power(), o.int_power())
            && e1 == e2
            && b1 != b2
        {
            return Core::power(b1 * b2, e1.clone());
        }
        // Both factor lists are in the order of their atoms: merge them, adding the exponents
        // of an atom both hold.
        let mut out = Vec::with_capacity(self.0.len() + o.0.len());
        let (mut i, mut j) = (self.0.iter().peekable(), o.0.iter().peekable());
        loop {
            match (i.peek(), j.peek()) {
                (Some((a, e)), Some((b, f))) => match a.cmp(b) {
                    Ordering::Less => {
                        out.push((a.clone(), e.clone()));
                        i.next();
                    }
                    Ordering::Greater => {
                        out.push((b.clone(), f.clone()));
                        j.next();
                    }
                    Ordering::Equal => {
                        out.push((a.clone(), e + f));
                        i.next();
                        j.next();
                    }
                },
                (Some(_), None) => {
                    out.extend(i.cloned());
                    break;
                }
                (None, _) => {
                    out.extend(j.cloned());
                    break;
                }
            }
        }
        Core(out)
    }

    /// `self ^ k`.
    fn pow(&self, k: &BigUint) -> Core {
        Core(self.0.iter().map(|(a, e)| (a.clone(), e * k)).collect())
    }

    /// `self ^ (1 / k)`, when `k` divides every exponent.
    fn exact_root(&self, k: &BigUint) -> Option<Core> {
        self.0
            .iter()
            .map(|(a, e)| e.is_multiple_of(k).then(|| (a.clone(), e / k)))
            .collect::<Option<Vec<_>>>()
            .map(Core)
    }

    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        self.0
            .iter()
            .map(|(a, e)| a.approx(bits).pow(e, bits))
            .reduce(|p, q| p.mul(&q, bits))
            .expect("a core has a factor")
    }

    /// The value, written out: its cost is that of the value's digits, and for a root that of
    /// a root of the radicand's digits.
    fn expand(&self) -> BigUint {
        self.0.iter().fold(BigUint::one(), |r, (a, e)| {
            mul_uint(&r, &expand_pow(&a.expand(), e))
        })
    }

    /// Bounds on the bits of the value and of the widest number [`Core::expand`] builds: each
    /// power and each partial product is at most the value, every factor being at least 1.
    fn widths(&self) -> (BigUint, BigUint) {
        let (mut value, mut widest) = (BigUint::ZERO, BigUint::ZERO);
        for (a, e) in &self.0 {
            let (v, w) = a.widths();
            value += e * v;
            widest = widest.max(w);
        }
        let widest = widest.max(value.clone());
        (value, widest)
    }

    /// The value modulo `n >= 1`, by `modpow`, or `None` when a factor is a root, whose
    /// digits are not known.
    fn residue(&self, n: &BigUint) -> Option<BigUint> {
        self.0
            .iter()
            .try_fold(BigUint::from(1u32) % n, |r, (a, e)| {
                let Atom::Int(b) = a else { return None };
                Some(r * b.modpow(e, n) % n)
            })
    }
}

/// `v = q * b ^ g + r` with `r` in `(-b ^ g / 2, b ^ g / 2]`, as `(r, q)`. When the bits of
/// `b` and `g` show that `b ^ g` exceeds `2 * |v|`, then `r = v` and `q = 0` with no power
/// computed, so a power is computed only when it has at most about twice the bits of `v`.
fn balance(v: BigInt, b: &BigUint, g: &BigUint) -> (BigInt, BigInt) {
    // 2 * |v| < 2^lim, and b ^ g >= 2^(g * (bits(b) - 1)).
    let lim = v.bits() + 1;
    let Some(g) = u64::try_from(g)
        .ok()
        .filter(|g| g.saturating_mul(b.bits() - 1) < lim)
    else {
        return (v, BigInt::ZERO);
    };
    let m = BigInt::from(expand_pow(b, &BigUint::from(g)));
    let mut r = Integer::mod_floor(&v, &m);
    if (&r << 1u32) > m {
        r -= &m;
    }
    let q = (v - &r) / m;
    (r, q)
}

/// Folds the terms whose cores are powers of one integer `b`: in increasing order of exponent,
/// each coefficient but the last is brought into `(-b ^ g / 2, b ^ g / 2]`, with `g` the gap
/// to the next exponent, and the rest carried to the next. The lower terms of such a group
/// then add to less than its top term in magnitude, so the group is zero exactly when it has
/// no terms left, has the sign of its top coefficient, and is at least a quarter of its top
/// term for `b >= 3` (for `b = 2`, at least `2^-n` of it with `n` terms). `3 ^ (e + 1) -
/// 3 * 3 ^ e` folds to nothing, and `3 ^ (e + 1) - 3 ^ e - 2 * 3 ^ e` likewise, so a
/// difference of equal values in such forms is found to be zero with no digits written out.
/// A power of an integer is kept as a power of its least root (`Core::power`), so `3 * 9 ^ e`
/// and `3 ^ (2 * e + 1)` are one group. The cost is one sort of the terms and, per term, a
/// power of `b` of at most about twice the bits of its coefficient.
// Complexity tradeoff: only powers of one integer are folded. Terms over products of powers of
// several integers, as `2 ^ (e + 1) * 5 ^ e` against `2 * 10 ^ e`, or over roots stay apart,
// so a sum of them that cancels in their high bits is found small, or zero, only once the
// approximations are exact, at the bits of the value; the answer stays exact. Why: a carry
// between two such terms runs along each integer of a coprime base of their cores at once,
// and the coefficients of a group then form a polynomial in several powers, not a number in
// one base; for a power of a root, the root's digits. Trigger: a sum or difference of kept
// values whose cores are products of powers of several integers, or powers of roots, and whose
// high bits cancel. Test:
// `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`;
// COMPLEXITY.md S33. A complete solution would write the cores of a sum over one coprime base
// of their integers (as `Core::same` does for two cores) and carry between terms along each
// base element, as `fold` does along one; a bound on the carries for terms whose exponents
// differ along several elements at once, which would make it exact, is not worked out.
fn fold(terms: &mut Vec<(BigInt, Core)>) {
    let mut idx: Vec<usize> = (0..terms.len())
        .filter(|&i| terms[i].1.int_power().is_some())
        .collect();
    idx.sort_by(|&i, &j| terms[i].1.int_power().cmp(&terms[j].1.int_power()));
    fn base(terms: &[(BigInt, Core)], i: usize) -> Option<&BigUint> {
        terms[i].1.int_power().map(|(b, _)| b)
    }
    let mut s = 0;
    while s < idx.len() {
        let mut t = s + 1;
        while t < idx.len() && base(terms, idx[t]) == base(terms, idx[s]) {
            t += 1;
        }
        let mut carry = BigInt::ZERO;
        for w in s..t {
            let i = idx[w];
            let v = std::mem::take(&mut terms[i].0) + carry;
            if w + 1 == t {
                terms[i].0 = v;
                carry = BigInt::ZERO;
                continue;
            }
            let (b, e) = terms[i].1.int_power().expect("a power");
            let (_, f) = terms[idx[w + 1]].1.int_power().expect("a power");
            let (r, q) = balance(v, b, &(f - e));
            terms[i].0 = r;
            carry = q;
        }
        s = t;
    }
    terms.retain(|(c, _)| !c.is_zero());
}

/// The terms in decreasing order of the values of their cores, with the coefficients of equal
/// cores added and zero ones dropped: `O(n log n)` comparisons of cores for `n` terms.
fn collect(mut terms: Vec<(BigInt, Core)>) -> Vec<(BigInt, Core)> {
    terms.sort_by(|a, b| b.1.value_cmp(&a.1));
    let mut out: Vec<(BigInt, Core)> = Vec::with_capacity(terms.len());
    for (c, core) in terms {
        match out.last_mut() {
            Some((c0, core0)) if core0.value_cmp(&core) == Ordering::Equal => *c0 += c,
            _ => out.push((c, core)),
        }
    }
    out.retain(|(c, _)| !c.is_zero());
    out
}

/// `floor(rad ^ (1 / k))` to `bits` bits, for `rad` above zero, with whether `rad` is a
/// perfect `k`-th power when that is decided at this precision. The root `y` is found to
/// `bits` bits as `r * 2^t` by bisection on `r`, each step comparing `(r * 2^t) ^ k` with
/// `rad` at `bits` bits, so the cost is `O(bits * bits of k)` products of `bits`-bit numbers,
/// whatever the size of `rad` or `k`. Only a step that both bounds certify moves a bound, so
/// the range always holds `y`. Once `bits` reaches the bits of `rad`, every comparison is
/// exact and `t` is 0, so the floor is found exactly.
// Complexity tradeoff: bisection takes `O(bits)` steps, so a root to `bits` bits costs
// `O(bits * bits of k)` products of `bits`-bit numbers, quadratic in `bits` where Newton's
// method would take `O(log bits)` steps; the answer is exact. Why: each bisection step needs
// only a power and a comparison, both certified in interval arithmetic, while a Newton step
// on intervals needs a division and a proof that the step keeps the root inside its range.
// Trigger: comparing a kept root with a value that agrees with it in many leading bits, as
// `5 ^ (k / 2)` against the square root of `3 ^ k + 5 ^ k`, which needs about `0.26 * k`
// bits. Test: `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
// (roots compared with their neighbors one apart); COMPLEXITY.md S33. A complete solution
// would refine the root by interval Newton steps from the bisection bracket, doubling the
// bits each step.
fn root_approx(rad: &Kept, k: &BigUint, bits: u64) -> (Approx, Option<bool>) {
    let a = rad.approx(bits);
    let k_int = BigInt::from(k.clone());
    // rad >= 2^l_min, and rad >= 1 since it is an integer above zero.
    let l_min = if a.lo.sign() == Sign::Plus {
        (&a.shift + (a.lo.bits() - 1)).max(BigInt::ZERO)
    } else {
        BigInt::ZERO
    };
    // rad < 2^l_max.
    let l_max = &a.shift + a.hi.bits();
    // 2^q_min <= y < 2^q_max.
    let q_min = Integer::div_floor(&l_min, &k_int);
    let q_max = Integer::div_ceil(&l_max, &k_int);
    let t = (&q_min - bits).max(BigInt::ZERO);
    let at = |q: &BigInt| {
        BigInt::from(1u32) << u64::try_from(&(q - &t)).expect("at most the bits of the bound")
    };
    let pow = |r: &BigInt| {
        Approx {
            lo: r.clone(),
            hi: r.clone(),
            shift: t.clone(),
        }
        .pow(k, bits)
    };
    // The largest r with (r * 2^t) ^ k <= rad certified: r_lo = at(q_min) holds by the
    // bound, and at(q_max) is past y.
    let (mut lo, mut hi) = (at(&q_min), at(&q_max));
    while &hi - &lo > BigInt::from(1u32) {
        let mid: BigInt = (&lo + &hi) >> 1u32;
        if pow(&mid).hi_at_most(&a.lo, &a.shift) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let r_lo = lo;
    // The least r with (r * 2^t) ^ k > rad certified.
    let (mut lo, mut hi) = (at(&q_min), at(&q_max));
    while &hi - &lo > BigInt::from(1u32) {
        let mid: BigInt = (&lo + &hi) >> 1u32;
        if a.below(&pow(&mid)) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let r_hi = hi;
    if t.is_zero() && r_hi == &r_lo + 1u32 {
        let p = pow(&r_lo);
        let perfect = if p.is_exact()
            && a.is_exact()
            && scaled_cmp(&p.lo, &p.shift, &a.lo, &a.shift) == Ordering::Equal
        {
            Some(true)
        } else if p.below(&a) {
            Some(false)
        } else {
            None
        };
        return (Approx::exact(r_lo), perfect);
    }
    (
        Approx {
            lo: r_lo,
            hi: r_hi,
            shift: t,
        },
        None,
    )
}

impl Kept {
    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        self.terms
            .iter()
            .fold(Approx::of(&self.d, bits), |s, (c, core)| {
                s.add(&Approx::of(c, bits).mul(&core.approx(bits), bits), bits)
            })
            .div(&self.den, bits)
    }

    /// The value, written out: its cost is that of the value's digits.
    fn expand(&self) -> BigInt {
        let num = self.terms.iter().fold(self.d.clone(), |s, (c, core)| {
            s + mul_int(c, &BigInt::from(core.expand()))
        });
        num / BigInt::from(self.den.clone())
    }

    /// Bounds on the bits of the value and of the widest number [`Kept::expand`] builds: a
    /// term `c * core` has at most the bits of both, and the sum of the terms and `d` at most
    /// the widest of them and one bit for each doubling of their count.
    fn widths(&self) -> (BigUint, BigUint) {
        let mut sum = BigUint::from(self.d.bits());
        let mut widest = BigUint::ZERO;
        for (c, core) in &self.terms {
            let (v, w) = core.widths();
            sum = sum.max(v + c.bits());
            widest = widest.max(w);
        }
        let count = self.terms.len() as u64 + 1;
        sum += 64 - u64::from(count.leading_zeros());
        let widest = widest.max(sum.clone());
        (sum, widest)
    }

    /// The negation of the form. Its value lies outside `i128` except when `self` is `2^127`,
    /// whose negation `i128::MIN` is a big value: so only `Neg for &Num`, which gives that
    /// value its form, calls this.
    fn neg(&self) -> Kept {
        Kept {
            terms: self
                .terms
                .iter()
                .map(|(c, core)| (-c, core.clone()))
                .collect(),
            d: -&self.d,
            den: self.den.clone(),
            negative: !self.negative,
        }
    }

    /// The core, when the value is `±core` alone.
    fn bare(&self) -> Option<&Core> {
        match self.terms.as_slice() {
            [(c, core)] if self.d.is_zero() && self.den.is_one() && c.magnitude().is_one() => {
                Some(core)
            }
            _ => None,
        }
    }

    /// Whether every core has integer atoms only, so that the value has residues.
    fn is_int(&self) -> bool {
        self.terms.iter().all(|(_, core)| core.is_int())
    }

    /// The value modulo `n >= 1`, in `0..n`, without its digits: each core modulo `den * n`
    /// by `modpow`. `None` when a core has a root, whose digits are not known.
    fn residue(&self, n: &BigUint) -> Option<BigUint> {
        let m = &self.den * n;
        let mut x = self.d.clone();
        for (c, core) in &self.terms {
            x += c * BigInt::from(core.residue(&m)?);
        }
        // The numerator is a multiple of den, and so is its residue modulo den * n.
        let x = Integer::mod_floor(&x, &BigInt::from(m));
        Some((x / BigInt::from(self.den.clone())).into_parts().1)
    }

    /// `floor(self / n)` for `n >= 1`, without the digits of `self`, or `None` when a core has
    /// a root.
    fn div_floor_by(&self, n: &BigUint) -> Option<Num> {
        let r = self.residue(n)?;
        Some(Num::kept(
            self.terms.clone(),
            &self.d - BigInt::from(r * &self.den),
            &self.den * n,
        ))
    }

    /// `floor(self ^ (1 / k))` or, when `up`, the ceiling, for `self` above zero and
    /// `k >= 2`.
    fn root(&self, k: &BigUint, up: bool) -> Num {
        if let Some(core) = self.bare() {
            if let Some(r) = core.exact_root(k) {
                return Num::kept(
                    vec![(BigInt::from(1u32), r)],
                    BigInt::ZERO,
                    BigUint::from(1u32),
                );
            }
            match core.0.as_slice() {
                [(Atom::Int(base), exp)] => {
                    // b ^ (e / k) = b ^ (e' / k') in lowest terms, with k' >= 2 since k does
                    // not divide e; b is not a perfect power (`Core::power`), so this is
                    // irrational, and its ceiling is one past its floor.
                    let g = Integer::gcd(exp, k);
                    let (e, k) = (exp / &g, k / &g);
                    let r = Num::power(false, base.clone(), e).root_floor(&k);
                    return if up { &r + &Num::ONE } else { r };
                }
                [(Atom::Root { rad, k: k1, .. }, exp)] if exp.is_one() && !up => {
                    // floor(floor(y) ^ (1 / k)) = floor(y ^ (1 / k)) for y >= 0.
                    return Num(Word::Kept(rad.clone())).root_floor(&(k1 * k));
                }
                _ => {}
            }
        }
        if self.is_int() {
            let r = Num(Word::Kept(Box::new(self.clone()))).root_floor(k);
            return if up && !is_perfect_power(self, k) {
                &r + &Num::ONE
            } else {
                r
            };
        }
        // Complexity tradeoff: a root of a kept value with a root among its cores, other than
        // an exact root or the floor root of a bare root, is the root of the value written
        // out, at the cost of its digits and a root of them; the answer is exact. Why: the
        // kept root needs the radicand's residues, which a root's digits decide, and the
        // ceiling of a root of a root needs to know whether a root is itself a perfect power.
        // Trigger: `floor_root` or `ceil_root` of a sum, multiple or product holding a kept
        // root, or the ceiling root of a bare root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
        // (roots 2 to 5 of multiples of kept roots); COMPLEXITY.md S33. A complete solution
        // would keep nested roots `floor(floor(r ^ (1 / k)) * c + d) ^ (1 / j)` as their own
        // atoms, compared by approximation as roots are now.
        Num::from(self.expand()).root_big(k, up)
    }

    /// The number of trailing zero binary digits, or `None` when a core holds a root, whose
    /// digits are not known. The numerator is a sum of parts `2^v * u` with `u` odd: for a term
    /// `c * core`, `v` is the trailing zeros of `c` plus those of each atom times its exponent,
    /// and `u` the product of the odd parts; `d` is one more part. With `m` the least `v`, the
    /// numerator over `2^m` is found modulo `2^j` from the residues of the odd parts (`modpow`),
    /// for `j` = 64 and then twice as many until it is not 0 there; a part with `v - m >= j` is 0
    /// modulo `2^j` and is not read, so no power of 2 past `2^j` is built. Less the trailing
    /// zeros of `den`, which divides the numerator, that is the answer, exact. For a bare power
    /// `b ^ e` it is `e` times the trailing zeros of `b`, found at `j` = 64. The cost is
    /// `O(n log e)` products of `j` bits for `n` terms and exponents of `log e` bits, with `j`
    /// at most twice the trailing zeros of the numerator over `2^m`: the low bits in which its
    /// parts cancel, not the bits of the value.
    fn trailing_zeros(&self) -> Option<BigUint> {
        /// A part `2^v * c * product(b ^ e)` of the numerator, with `c` and each `b` odd.
        struct Part<'a> {
            v: BigUint,
            c: BigInt,
            odd: Vec<(BigUint, &'a BigUint)>,
        }
        let mut parts = Vec::with_capacity(self.terms.len() + 1);
        for (c, core) in &self.terms {
            let tc = c.trailing_zeros().expect("no coefficient is zero");
            let mut v = BigUint::from(tc);
            let mut odd = Vec::with_capacity(core.0.len());
            for (a, e) in &core.0 {
                let Atom::Int(b) = a else { return None };
                let tb = b.trailing_zeros().expect("an atom is at least 2");
                v += e * tb;
                odd.push((b >> tb, e));
            }
            parts.push(Part { v, c: c >> tc, odd });
        }
        if let Some(td) = self.d.trailing_zeros() {
            parts.push(Part {
                v: BigUint::from(td),
                c: &self.d >> td,
                odd: Vec::new(),
            });
        }
        let m = parts
            .iter()
            .map(|p| &p.v)
            .min()
            .expect("a kept value has a term")
            .clone();
        let den_zeros = self.den.trailing_zeros().expect("den is at least 1");
        let mut j = 64u64;
        loop {
            let unit = BigUint::from(1u32) << j;
            let mask = &unit - 1u32;
            let modulus = BigInt::from(unit.clone());
            let mut r = BigUint::ZERO;
            for Part { v, c, odd } in &parts {
                let s = u64::try_from(&(v - &m)).ok().filter(|&s| s < j);
                let Some(s) = s else { continue };
                let u = odd.iter().fold(
                    Integer::mod_floor(c, &modulus).into_parts().1,
                    |x, (b, e)| (x * b.modpow(e, &unit)) & &mask,
                );
                r = (r + (u << s)) & &mask;
            }
            if let Some(z) = r.trailing_zeros() {
                return Some(m + z - den_zeros);
            }
            j *= 2;
        }
    }

    /// The exponent `k` when the value is `2 ^ k`.
    fn pow2_exponent(&self) -> Option<&BigUint> {
        match self.bare()?.int_power() {
            Some((b, k)) if !self.negative && *b == BigUint::from(2u32) => Some(k),
            _ => None,
        }
    }

    /// `floor(self / 2^k)`, for `den == 1`, when a term has `2^k` as a factor of its coefficient
    /// and its atom 2. Such a term over `2^k` is a term again, its exponent of 2 or its
    /// coefficient lowered, or a part of `d` when no atom is left; the other terms and `d` make
    /// `L`, and the answer is those terms plus `floor(L / 2^k)`, which is `floor(d / 2^k)` when
    /// no other term is left, by a shift. `None` when `den > 1` or no term has `2^k` as a
    /// factor. The cost is that of the terms, not of the value's digits.
    fn shr(&self, k: &BigUint) -> Option<Num> {
        if !self.den.is_one() {
            return None;
        }
        let two = Atom::Int(BigUint::from(2u32));
        let (mut high, mut low) = (Vec::new(), Vec::new());
        let mut d_high = BigInt::ZERO;
        for (c, core) in &self.terms {
            // The atoms are in increasing order, so 2 is the first when it is one.
            let f = match core.0.first() {
                Some((a, e)) if *a == two => e.clone(),
                _ => BigUint::ZERO,
            };
            let t = BigUint::from(c.trailing_zeros().expect("no coefficient is zero"));
            if &f + &t < *k {
                low.push((c.clone(), core.clone()));
                continue;
            }
            let (c, atoms) = if f >= *k {
                let mut atoms = core.0.clone();
                let left = &f - k;
                if left.is_zero() {
                    atoms.remove(0);
                } else {
                    atoms[0].1 = left;
                }
                (c.clone(), atoms)
            } else {
                let s = u64::try_from(&(k - &f)).expect("at most the trailing zeros of c");
                let rest = if f.is_zero() {
                    &core.0[..]
                } else {
                    &core.0[1..]
                };
                (c >> s, rest.to_vec())
            };
            if atoms.is_empty() {
                d_high += c;
            } else {
                high.push((c, Core(atoms)));
            }
        }
        if high.is_empty() && d_high.is_zero() {
            return None;
        }
        let rest = if low.is_empty() {
            Num::from(floor_shr(&self.d, &BigInt::from(k.clone())))
        } else {
            Num::kept(low, self.d.clone(), BigUint::from(1u32)).div_floor(&Num::power(
                false,
                BigUint::from(2u32),
                k.clone(),
            ))
        };
        Some(&Num::kept(high, d_high, BigUint::from(1u32)) + &rest)
    }
}

/// Whether `x`, above zero with integer atoms only, is a perfect `k`-th power. Each round
/// tests one more prime `p` with `g = gcd(k, p - 1) > 1`: a `k`-th power `a` not divisible by
/// `p` has `a ^ ((p - 1) / g) == 1` modulo `p`, so a failure proves `x` is not one, and for a
/// value that is not a `k`-th power about `1 - 1/g` of such primes show it. When the number
/// of primes tested reaches a power of two, `x` is also compared with the `k`-th power of its
/// root at twice the last precision, which decides a perfect power once the precision reaches
/// the bits of `x`. Each comparison then costs a constant factor more than the last, and the
/// residue tests cost one per prime. Doubling the precision for every prime instead reached
/// `2 ^ n` bits by the `n`-th prime, while a `k` whose prime factors are all large
/// (`2 ^ 32 + 1 = 641 * 6700417`) gets no residue test below the prime `2 * 641 + 1`, so
/// `3 ^ (2 ^ 32 + 1) + 1` did not finish.
// Complexity tradeoff: a value that is a perfect `k`-th power passes every prime, so it is
// decided only when the precision reaches the bits of `x`, at the cost of its digits and of
// one residue test for each 64 bits of `x`; the answer is exact. Why: a proof that a number
// given as a sum of powers is a perfect power needs its root in a closed form, and no general
// closed form is known for a root of a sum.
// Trigger: the ceiling root (`ceil_root`) of a kept value that is not a bare power and is a
// perfect `k`-th power, such as `(2 ^ 200 + 1) ^ 2` read as a sum. Test:
// `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`;
// COMPLEXITY.md S33. A complete solution would find the root as a kept value (a sum of
// powers whose `k`-th power is `x`, by matching the leading terms) and check it exactly.
fn is_perfect_power(x: &Kept, k: &BigUint) -> bool {
    let mut p: u64 = 2;
    let mut bits = 64;
    let mut tested: u64 = 0;
    loop {
        p = next_prime(p);
        tested += 1;
        let g = Integer::gcd(k, &BigUint::from(p - 1));
        if !g.is_one() {
            let n = BigUint::from(p);
            let a = x.residue(&n).expect("integer atoms have residues");
            if !a.is_zero() && !a.modpow(&(BigUint::from(p - 1) / &g), &n).is_one() {
                return false;
            }
        }
        if tested.is_power_of_two() {
            if let (_, Some(perfect)) = root_approx(x, k, bits) {
                return perfect;
            }
            bits *= 2;
        }
    }
}

/// The least prime above `p`.
fn next_prime(p: u64) -> u64 {
    let mut q = p + 1;
    while (2..)
        .take_while(|d| d * d <= q)
        .any(|d| q.is_multiple_of(d))
    {
        q += 1;
    }
    q
}

/// An unbounded integer held in one machine word while it fits in `i64`: an interval end
/// (`interval::End`). It is two words, as the kernel's `Value::Int` and `Value::Big` are, so
/// an end costs no more than an `i64` one did while every value fits, and no end is rounded
/// or dropped past `i64`. Arithmetic on two small values is done in `i128`, which holds every
/// sum, difference and product of two `i64` values.
#[derive(Clone, Debug)]
pub struct Num(Word);

impl From<i64> for Num {
    fn from(v: i64) -> Num {
        Num(Word::Small(v))
    }
}

impl From<i32> for Num {
    fn from(v: i32) -> Num {
        Num(Word::Small(i64::from(v)))
    }
}

impl From<u64> for Num {
    fn from(v: u64) -> Num {
        Num::from(i128::from(v))
    }
}

impl From<i128> for Num {
    fn from(v: i128) -> Num {
        Num(match i64::try_from(v) {
            Ok(s) => Word::Small(s),
            Err(_) => Word::Big(Arc::new(BigInt::from(v))),
        })
    }
}

impl From<&BigInt> for Num {
    fn from(v: &BigInt) -> Num {
        Num(match i64::try_from(v) {
            Ok(s) => Word::Small(s),
            Err(_) => Word::Big(Arc::new(v.clone())),
        })
    }
}

impl From<BigInt> for Num {
    fn from(v: BigInt) -> Num {
        Num(match i64::try_from(&v) {
            Ok(s) => Word::Small(s),
            Err(_) => Word::Big(Arc::new(v)),
        })
    }
}

impl From<&Int> for Num {
    fn from(v: &Int) -> Num {
        match &v.0 {
            Repr::Small(s) => Num::from(*s),
            Repr::Big(b) => Num::from((**b).clone()),
        }
    }
}

/// An integer of the kernel, kept as a power of each of its primes, which may be far past
/// what can be written out. It must be an integer.
impl From<&zed_kernel::num::Rat> for Num {
    fn from(v: &zed_kernel::num::Rat) -> Num {
        let (coeff, pows) = v.integer_factors();
        pows.iter().fold(Num::from(coeff), |n, (p, e)| {
            &n * &Num::power(false, BigUint::from(*p), e.magnitude().clone())
        })
    }
}

impl From<&Num> for zed_kernel::Value {
    fn from(v: &Num) -> zed_kernel::Value {
        match &v.0 {
            Word::Small(s) => zed_kernel::Value::Int(*s),
            Word::Big(b) => zed_kernel::Value::int((**b).clone()),
            Word::Kept(k) => zed_kernel::Value::int(k.expand()),
        }
    }
}

impl From<&Num> for Int {
    fn from(v: &Num) -> Int {
        match &v.0 {
            Word::Small(s) => Int::from(*s),
            Word::Big(b) => Int::from((**b).clone()),
            Word::Kept(k) => Int::from(k.expand()),
        }
    }
}

impl Num {
    /// Zero.
    pub const ZERO: Num = Num(Word::Small(0));
    /// One.
    pub const ONE: Num = Num(Word::Small(1));

    /// The value, written out when kept, once the system gives a byte for each bit of the
    /// widest number the writing builds (`Kept::widths`); [`TooLarge`] names that memory when
    /// it refuses. A value not kept is borrowed, or built from its one word.
    // Complexity tradeoff: the memory asked for is a byte for each bit of a bound on the widest
    // number built (each power, product, sum and radicand), the factor `Rat::built_parts`
    // asks, which `to_integer` measured at a peak of 5.49 times the width; this build was not
    // measured on its own. So a value needing less is refused when the free memory lies
    // between the two, and none aborts. Trigger: the canonical serialization of an interval end
    // or a class past `i64` (`canon::serial`). Test:
    // `l01_24_refinement_lattices::kept_serial` (refused at two widths, exact when given);
    // COMPLEXITY.md S33. A complete solution would ask each allocation of the build for its
    // own memory.
    pub fn built(&self) -> Result<Cow<'_, BigInt>, TooLarge> {
        if let Word::Kept(k) = &self.0 {
            room(k.widths().1 << 3u32)?;
        }
        Ok(self.big())
    }

    /// The value, written out when kept: its cost is then that of the value's digits.
    fn big(&self) -> Cow<'_, BigInt> {
        match &self.0 {
            Word::Small(v) => Cow::Owned(BigInt::from(*v)),
            Word::Big(v) => Cow::Borrowed(v),
            Word::Kept(k) => Cow::Owned(k.expand()),
        }
    }

    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        match &self.0 {
            Word::Kept(k) => k.approx(bits),
            _ => Approx::of(&self.big(), bits),
        }
    }

    /// The value, when it is not kept.
    fn scalar(&self) -> Option<Cow<'_, BigInt>> {
        match &self.0 {
            Word::Small(v) => Some(Cow::Owned(BigInt::from(*v))),
            Word::Big(v) => Some(Cow::Borrowed(v)),
            Word::Kept(_) => None,
        }
    }

    /// `(sum of c * core + d) / den` in its one form for a value inside `i128`, else kept. The
    /// terms are collected and folded first. The place of the value against `i128` is found at
    /// 64 bits and then at twice as many until it is decided; a value inside `i128` is then
    /// written out.
    // Complexity tradeoff: a value inside `i128` whose terms remain after collecting and
    // folding, because they cancel in forms that neither relates (see `Core::same` and
    // `fold`), is placed only once the approximations are exact, and written out, at the
    // cost of the digits of its cores; the answer is exact. Why: the terms cancel only by
    // carries between products of powers of several integers, or between roots, which `fold`
    // does not make. Trigger: a sum or difference of kept values in such forms whose value is
    // small, as `2 ^ (e + 1) * 5 ^ e + 1 - 2 * 10 ^ e`. Test:
    // `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`;
    // COMPLEXITY.md S33. A complete solution is that of `fold`, which would cancel these terms.
    fn kept(terms: Vec<(BigInt, Core)>, d: BigInt, den: BigUint) -> Num {
        let mut terms = collect(terms);
        fold(&mut terms);
        if terms.is_empty() {
            return Num::from(d / BigInt::from(den));
        }
        let g = terms
            .iter()
            .fold(Integer::gcd(&d, &BigInt::from(den.clone())), |g, (c, _)| {
                Integer::gcd(&g, c)
            });
        let (terms, d, den) = if g.is_one() {
            (terms, d, den)
        } else {
            let gu = g.magnitude();
            (
                terms.into_iter().map(|(c, core)| (c / &g, core)).collect(),
                d / &g,
                den / gu,
            )
        };
        let mut k = Kept {
            terms,
            d,
            den,
            negative: false,
        };
        let edge = BigInt::from(1u32) << 127u32;
        let zero = BigInt::ZERO;
        let mut bits = 64;
        loop {
            let a = k.approx(bits);
            if scaled_cmp(&a.lo, &a.shift, &edge, &zero) != Ordering::Less {
                return Num(Word::Kept(Box::new(k)));
            }
            if scaled_cmp(&a.hi, &a.shift, &-&edge, &zero) == Ordering::Less {
                k.negative = true;
                return Num(Word::Kept(Box::new(k)));
            }
            if scaled_cmp(&a.lo, &a.shift, &-&edge, &zero) != Ordering::Less
                && scaled_cmp(&a.hi, &a.shift, &edge, &zero) == Ordering::Less
            {
                return Num::from(k.expand());
            }
            bits *= 2;
        }
    }

    /// A bare kept value `±core`, for a core whose value is at least `2^127`.
    fn bare(negative: bool, core: Core) -> Num {
        Num(Word::Kept(Box::new(Kept {
            terms: vec![(BigInt::from(if negative { -1 } else { 1 }), core)],
            d: BigInt::ZERO,
            den: BigUint::from(1u32),
            negative,
        })))
    }

    /// The value, when it fits in `i64`.
    pub fn to_i64(&self) -> Option<i64> {
        match self.0 {
            Word::Small(v) => Some(v),
            _ => None,
        }
    }

    /// The value as an [`Int`], when it is written out: a kept power is not built, since that
    /// costs time and memory in its digits.
    pub fn to_int(&self) -> Option<Int> {
        self.scalar().map(|v| Int::from(v.into_owned()))
    }

    /// The value, when it fits in `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Word::Small(v) => Some(*v as i128),
            Word::Big(v) => i128::try_from(&**v).ok(),
            Word::Kept(_) => None,
        }
    }

    /// The sign: -1, 0 or 1.
    pub fn signum(&self) -> i8 {
        match &self.0 {
            Word::Small(v) => v.signum() as i8,
            Word::Big(v) => match v.sign() {
                Sign::Minus => -1,
                Sign::NoSign => 0,
                Sign::Plus => 1,
            },
            Word::Kept(k) => {
                if k.negative {
                    -1
                } else {
                    1
                }
            }
        }
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        matches!(self.0, Word::Small(0))
    }

    /// Whether the value is odd. A kept value is read by its residue modulo 2
    /// ([`Num::mod_floor`]), not written out.
    pub fn is_odd(&self) -> bool {
        match &self.0 {
            Word::Small(v) => v & 1 == 1,
            Word::Big(v) => v.is_odd(),
            Word::Kept(_) => !self.mod_floor(&Num::from(2)).is_zero(),
        }
    }

    /// The absolute value.
    pub fn abs(&self) -> Num {
        if self.signum() < 0 {
            -self
        } else {
            self.clone()
        }
    }

    /// The number of binary digits of `abs(self)`: the least `b >= 0` with `abs(self) < 2^b`.
    /// A kept value is not written out (`Num::kept_bits`).
    pub fn bits(&self) -> Num {
        match &self.0 {
            Word::Small(v) => Num::from(i64::from(64 - v.unsigned_abs().leading_zeros())),
            Word::Big(v) => Num::from(i128::from(v.bits())),
            Word::Kept(k) => Num::from(self.kept_bits(k)),
        }
    }

    /// The bits of the kept value `self`, whose form is `k`, from its approximation at 64 bits
    /// and then at twice as many. When the bounds `lo * 2^s` and `hi * 2^s` of `abs(self)`
    /// have one bit count, that is the answer: so for a bare power of 2 at once, since its
    /// approximation is exact, and for any other bare power `b ^ e` once the precision passes
    /// the bits of `e` and those on which `e * log2(b)` agrees with an integer. When the counts
    /// are `l` and `l + 1`, as for `2 ^ k - 1`, whose bounds lie on both sides of `2^k` at
    /// every precision short of its digits, one comparison of `abs(self)` with `2^l` decides,
    /// as the sign of a kept difference whose equal cores cancel. The answer is exact; the cost
    /// is that of the approximations and of that comparison, not of the value's digits.
    fn kept_bits(&self, k: &Kept) -> BigInt {
        let mut bits = 64;
        loop {
            let Approx { lo, hi, shift } = k.approx(bits);
            let (lo, hi) = if k.negative { (-hi, -lo) } else { (lo, hi) };
            if lo.sign() == Sign::Plus {
                let low = &shift + lo.bits();
                let high = &shift + hi.bits();
                if low == high {
                    return high;
                }
                if high == &low + 1u32 {
                    // abs(self) >= 2^(low - 1) and abs(self) < 2^high.
                    let edge = Num::power(false, BigUint::from(2u32), low.magnitude().clone());
                    let past = if k.negative {
                        *self <= -&edge
                    } else {
                        *self >= edge
                    };
                    return if past { high } else { low };
                }
            }
            bits *= 2;
        }
    }

    /// The number of trailing zero binary digits of a value other than 0. A kept value with
    /// integer cores is not written out (`Kept::trailing_zeros`).
    pub fn trailing_zeros(&self) -> Num {
        match &self.0 {
            Word::Small(v) => Num::from(i64::from(v.trailing_zeros())),
            Word::Big(v) => Num::from(i128::from(v.trailing_zeros().unwrap_or(0))),
            Word::Kept(k) => match k.trailing_zeros() {
                Some(z) => Num::from(BigInt::from(z)),
                // Complexity tradeoff: the trailing zeros of a kept value with a root among its
                // cores are those of the value written out, at the cost of its digits; the
                // answer is exact. Why: a floor root's low digits need the root to unit
                // precision, and so the radicand's digits. Trigger: `trailingZeros`, or a bit
                // word's rule reading one, on an end holding a kept root. Test:
                // `l01_39a_bit_words::kept_ends::the_trailing_zeros_of_a_kept_root_are_those_written_out`;
                // COMPLEXITY.md S33. A complete solution would keep the residue of a root modulo
                // a power of 2 in its atom's memo, found from the radicand's residue by a 2-adic
                // root where one exists.
                None => Num::from(i128::from(
                    self.big().trailing_zeros().expect("a kept value is not 0"),
                )),
            },
        }
    }

    /// `2 ^ e` for `e >= 0`, kept as a power when it does not fit in `i128`.
    // Complexity tradeoff: a kept `e` is written out, at the cost of its digits, since the
    // exponents of a core are written out; the answer is exact, and `2 ^ e` stays kept. Why:
    // a power whose exponent is itself kept needs an atom with a kept exponent, whose
    // approximation, residues and comparisons are not built. Trigger: `shl`, `bitNot`, `rotl`
    // or `rotr` with a count or width outside `i128`, or `bitOr`, `bitXor` or `trailingZeros`
    // on an operand of more than about `2^127` bits. Test:
    // `l01_39a_bit_words::kept_ends::a_power_of_2_by_a_kept_exponent_stays_kept`; COMPLEXITY.md
    // S33. A complete solution would keep `b ^ x` for a kept `x` as an atom, approximated by
    // `Approx::pow` on an approximation of `x`.
    pub fn pow2(e: &Num) -> Num {
        Num::power(false, BigUint::from(2u32), e.big().magnitude().clone())
    }

    /// `base ^ exp`, negated when `negative`, in its one form: in `i128` arithmetic when it
    /// fits there, else kept as a power. Finding whether it fits stops at the first product
    /// past `i128`, so it costs `O(bits of exp)` word operations.
    fn power(negative: bool, base: BigUint, exp: BigUint) -> Num {
        let sign = if negative { Sign::Minus } else { Sign::Plus };
        match exp.bits() {
            0 => return Num::ONE,
            1 => return BigInt::from_biguint(sign, base).into(),
            _ => {}
        }
        if let (Ok(b), Ok(e)) = (u128::try_from(&base), u32::try_from(&exp))
            && let Some(m) = b.checked_pow(e)
            && let Some(v) = if negative {
                0i128.checked_sub_unsigned(m)
            } else {
                i128::try_from(m).ok()
            }
        {
            return v.into();
        }
        Num::bare(negative, Core::power(base, exp))
    }

    /// `self ^ k`. A value that does not fit in `i128` is kept: a bare power or root as one
    /// with its exponents times `k`, other kept values by squaring, so the cost is that of
    /// the terms of the result (up to `C(n + k, k)` for `n` terms), not of its digits.
    pub fn pow(&self, k: u32) -> Num {
        if let Word::Small(a) = self.0
            && let Some(v) = (a as i128).checked_pow(k)
        {
            return v.into();
        }
        match k {
            0 => return Num::ONE,
            1 => return self.clone(),
            _ => {}
        }
        let negative = self.signum() < 0 && k % 2 == 1;
        match &self.0 {
            Word::Kept(x) => {
                if let Some(core) = x.bare() {
                    return match core.int_power() {
                        Some((base, exp)) => Num::power(negative, base.clone(), exp * k),
                        None => Num::bare(negative, core.pow(&BigUint::from(k))),
                    };
                }
                // Complexity tradeoff: a power of a kept value that is not bare is expanded into
                // its terms, up to `C(n + k - 1, k)` of them for `n` terms, so `(x ^ e + 1) **
                // 1000000` holds a million terms with coefficients of up to a million bits; the
                // answer is exact. Why: a kept power of a sum needs a new atom, a power of a kept
                // value, with its own approximation (`Approx::pow`), residues (`modpow` of the
                // sum's residue) and rules for collecting it with expanded terms. Trigger: an
                // exponent `k` on an interval whose end is a kept sum, as the bound of
                // `(x ^ e + 1) ^ k`. Test:
                // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
                // (squares of sums) and `ends::sums_of_unrelated_large_powers_keep_their_form`
                // (a cube of `2 ^ k + 1`); COMPLEXITY.md S33. A complete solution would keep
                // `s ^ k` as an atom for a kept sum `s`.
                let mut r = Num::ONE;
                for i in (0..u32::BITS - k.leading_zeros()).rev() {
                    r = &r * &r;
                    if (k >> i) & 1 == 1 {
                        r = &r * self;
                    }
                }
                r
            }
            Word::Small(_) | Word::Big(_) => {
                Num::power(negative, self.big().magnitude().clone(), BigUint::from(k))
            }
        }
    }

    /// `self ^ k` for `k >= 0` of any size, or `None` when no form holds it: when `k` is
    /// kept, or `self` is a kept value that is not bare and `k` is past `u32`. A power of a
    /// value that is not kept is kept as a power, with its exponent `k`, never written out.
    pub fn pow_by(&self, k: &Num) -> Option<Num> {
        if let Some(k) = k.to_i64().and_then(|k| u32::try_from(k).ok()) {
            return Some(self.pow(k));
        }
        let negative = self.signum() < 0 && k.is_odd();
        if self.abs() <= Num::ONE {
            // 0, 1 and -1 are read by the parity of `k`.
            return Some(if negative { Num::from(-1) } else { self.abs() });
        }
        let exp = k.scalar()?.magnitude().clone();
        match &self.0 {
            Word::Small(_) | Word::Big(_) => {
                Some(Num::power(negative, self.big().magnitude().clone(), exp))
            }
            // Complexity tradeoff: a kept value that is not bare raised past `u32` has no form;
            // it is `None` and the caller bounds outward. Why: expanding it squares its terms
            // about 32 times, past any memory. Trigger: `(2 ^ 200 + 1) ^ (2 ^ 40)`. Test:
            // `l01_24_refinement_lattices::past_i64::an_exponent_with_no_exact_form_bounds_outward`;
            // COMPLEXITY.md S36. A complete solution would keep `s ^ k` as an atom for a kept
            // sum `s`.
            Word::Kept(x) => {
                let core = x.bare()?;
                Some(match core.int_power() {
                    Some((base, e)) => Num::power(negative, base.clone(), e * exp),
                    None => Num::bare(negative, core.pow(&exp)),
                })
            }
        }
    }

    /// [`Num::floor_root`] with `k >= 1` of any size, or `None` when `k` is kept.
    pub fn floor_root_by(&self, k: &Num) -> Option<Num> {
        self.root_by(k, false)
    }

    /// [`Num::ceil_root`] with `k >= 1` of any size, or `None` when `k` is kept.
    pub fn ceil_root_by(&self, k: &Num) -> Option<Num> {
        self.root_by(k, true)
    }

    fn root_by(&self, k: &Num, up: bool) -> Option<Num> {
        if let Some(k) = k.to_i64().and_then(|k| u32::try_from(k).ok()) {
            return Some(self.root(k, up));
        }
        let k = k.scalar()?.magnitude().clone();
        Some(match &self.0 {
            Word::Small(_) | Word::Big(_) => self.root_big(&k, up),
            Word::Kept(x) => x.root(&k, up),
        })
    }

    /// The greatest `r >= 0` with `r ^ k <= self`, for `self >= 0` and `k >= 1`. The root of
    /// a kept value is kept, exact when the value is a power whose exponent `k` divides.
    pub fn floor_root(&self, k: u32) -> Num {
        self.root(k, false)
    }

    /// The least `r >= 0` with `r ^ k >= self`, for `self >= 0` and `k >= 1`.
    pub fn ceil_root(&self, k: u32) -> Num {
        self.root(k, true)
    }

    fn root(&self, k: u32, up: bool) -> Num {
        if k == 1 {
            return self.clone();
        }
        match &self.0 {
            Word::Small(_) | Word::Big(_) => self.root_big(&BigUint::from(k), up),
            Word::Kept(x) => x.root(&BigUint::from(k), up),
        }
    }

    /// The floor or ceiling of the `k`-th root of a value that is not kept, for `self >= 0`
    /// and `k >= 2`.
    fn root_big(&self, k: &BigUint, up: bool) -> Num {
        let v = self.big();
        if v.bits() <= 1 {
            // 0 and 1 are their own roots.
            return self.clone();
        }
        // For v >= 2 and k at least its bits, 1 ^ k <= v < 2 ^ k.
        let Some(k) = u32::try_from(k).ok().filter(|k| u64::from(*k) < v.bits()) else {
            return Num::from(if up { 2 } else { 1 });
        };
        let r = v.nth_root(k);
        if up && pow_uint(r.magnitude(), u64::from(k)) != *v.magnitude() {
            (r + 1u32).into()
        } else {
            r.into()
        }
    }

    /// `floor(self ^ (1 / k))` for `self` above zero with integer atoms only or not kept, and
    /// `k >= 2`: kept as a root when it is at least `2^127`, which holds exactly when
    /// `self >= 2 ^ (127 * k)`, else found by bisection on the 127 bits of the root.
    fn root_floor(&self, k: &BigUint) -> Num {
        let Word::Kept(x) = &self.0 else {
            return self.root_big(k, false);
        };
        if *self >= Num::power(false, BigUint::from(2u32), k * 127u32) {
            let root = Atom::Root {
                rad: x.clone(),
                k: k.clone(),
                memo: Memo::default(),
            };
            return Num::bare(false, Core(vec![(root, BigUint::from(1u32))]));
        }
        let (mut lo, mut hi) = (BigUint::ZERO, BigUint::from(1u32) << 127u32);
        while &hi - &lo > BigUint::from(1u32) {
            let mid: BigUint = (&lo + &hi) >> 1u32;
            if Num::power(false, mid.clone(), k.clone()) <= *self {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        BigInt::from(lo).into()
    }

    /// Whether `self <= other + 1`: whether no integer lies strictly between them, with
    /// `self` past `other`. It does not expand a kept value.
    pub fn at_most_succ(&self, other: &Num) -> bool {
        if self <= other {
            return true;
        }
        let perfect = |x: &Kept| {
            x.bare()
                .is_some_and(|c| c.exps_gcd() >= BigUint::from(2u32))
        };
        match (&self.0, &other.0) {
            // Two bare kept cores whose exponents share a factor are perfect powers with
            // exponents at least 2, both outside i128; by Mihailescu's theorem (Catalan's
            // conjecture) the only two such powers that differ by 1 are 8 and 9, so these
            // never do.
            (Word::Kept(a), Word::Kept(b)) if perfect(a) && perfect(b) => false,
            _ => *self <= other + &Num::ONE,
        }
    }

    /// `self / d` rounded down, for `d` not zero. A kept value over a value that is not kept
    /// uses residues of its cores and keeps its form; a value smaller in magnitude than a kept
    /// divisor gives 0 or -1 by one comparison.
    pub fn div_floor(&self, d: &Num) -> Num {
        match (&self.0, &d.0) {
            (Word::Small(a), Word::Small(b)) => {
                return Integer::div_floor(&(*a as i128), &(*b as i128)).into();
            }
            // floor(x / d) = floor(-x / -d), so a negative divisor is turned around by negating
            // both in their one forms: the negation of a kept 2^127 is i128::MIN, a big value,
            // and no kept form ever holds a value inside i128.
            (Word::Kept(_), Word::Small(_) | Word::Big(_)) if d.signum() < 0 => {
                return (-self).div_floor(&-d);
            }
            (Word::Kept(x), _) if let Some(s) = d.scalar() => {
                if let Some(q) = x.div_floor_by(s.magnitude()) {
                    return q;
                }
            }
            (_, Word::Kept(_)) if self.abs() < d.abs() => {
                return if self.is_zero() || self.signum() == d.signum() {
                    Num::ZERO
                } else {
                    Num::from(-1)
                };
            }
            // A shift right (`interval::bit_word`'s `shr`) by a count of at least 127.
            (Word::Kept(x), Word::Kept(y))
                if let Some(k) = y.pow2_exponent()
                    && let Some(q) = x.shr(k) =>
            {
                return q;
            }
            _ => {}
        }
        // Complexity tradeoff: the quotient of a kept value by a kept value at most its size,
        // and of a kept value with a root among its cores by any value, is that of the values
        // written out, at the cost of their digits; the answer is exact. By a power of 2, the
        // terms that have it as a factor are divided in their form (`Kept::shr`), and only the
        // other terms, when any is kept, are written out. Why: a quotient of two
        // sums of powers is not a sum of powers in general, and keeping it needs a new form
        // (a floor of a ratio) whose comparisons need its own approximation and residues; a
        // root has no residues without its digits. Trigger: `div` with a kept divisor no
        // larger than the dividend, or a dividend holding a kept root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
        // (every pair of 156 kept values) and, by a power of 2,
        // `l01_39a_bit_words::kept_ends::a_shift_right_of_a_kept_end_keeps_its_form`;
        // COMPLEXITY.md S33. A complete solution would keep `floor(a / b)` as an atom,
        // approximated as the quotient of the approximations.
        self.big().div_floor(&d.big()).into()
    }

    /// The remainder of [`Num::div_floor`], which has the sign of `d`.
    pub fn mod_floor(&self, d: &Num) -> Num {
        match (&self.0, &d.0) {
            (Word::Small(a), Word::Small(b)) => {
                return Integer::mod_floor(&(*a as i128), &(*b as i128)).into();
            }
            (Word::Kept(x), _) if let Some(s) = d.scalar() => {
                if let Some(r) = x.residue(s.magnitude()) {
                    let r = BigInt::from(r);
                    return if below_zero(&s) && !r.is_zero() {
                        (r + &*s).into()
                    } else {
                        r.into()
                    };
                }
            }
            (_, Word::Kept(_)) if self.abs() < d.abs() => {
                return if self.is_zero() || self.signum() == d.signum() {
                    self.clone()
                } else {
                    self + d
                };
            }
            _ => {}
        }
        // Complexity tradeoff: the remainder of a kept value by a kept value at most its size,
        // and of a kept value with a root among its cores by any value, is that of the values
        // written out, at the cost of their digits; the answer is exact. Why: the remainder is
        // the dividend less the divisor times the quotient, with the cost of the quotient at
        // `div_floor`. Trigger: `mod` with a kept divisor no larger than the dividend, or a
        // dividend holding a kept root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`;
        // COMPLEXITY.md S33. A complete solution would follow from a kept quotient, as at
        // `div_floor`.
        self.big().mod_floor(&d.big()).into()
    }

    /// The greatest common divisor, at least 0. With one kept operand and one that is not,
    /// it is the gcd of the latter with the former's residue modulo it.
    pub fn gcd(&self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => {
                return Integer::gcd(&(*a as i128), &(*b as i128)).into();
            }
            (Word::Kept(_), _) if other.scalar().is_some() => {
                if other.is_zero() {
                    return self.abs();
                }
                let s = other.abs();
                if let Word::Kept(x) = &self.0
                    && let Some(r) = x.residue(s.big().magnitude())
                {
                    return Integer::gcd(&BigInt::from(r), &*s.big()).into();
                }
            }
            (_, Word::Kept(_)) if self.scalar().is_some() => return other.gcd(self),
            _ => {}
        }
        // Complexity tradeoff: the gcd of two kept values, and of a kept value with a root
        // among its cores and any value, is that of the values written out, at the cost of
        // their digits; the answer is exact. Why: Euclid's algorithm on two kept values takes
        // remainders of kept values by kept values (see `mod_floor`), and the gcd of two
        // powers of unrelated bases has no form other than its value. Trigger: `gcd` of two
        // kept values, or of a kept value holding a root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`;
        // COMPLEXITY.md S33. A complete solution would factor out the common part of the cores
        // over a coprime base (as at `Core::value_cmp`) and take the gcd of the remaining
        // coefficients by residues.
        self.big().gcd(&other.big()).into()
    }

    /// The Euclidean quotient: `self = q * d + r` with `r` in `0..abs(d)`, for `d` not zero.
    pub fn div_euclid(&self, d: &Num) -> Num {
        let q = self.div_floor(&d.abs());
        if d.signum() < 0 { -&q } else { q }
    }

    /// The Euclidean remainder, in `0..abs(d)`, for `d` not zero.
    pub fn rem_euclid(&self, d: &Num) -> Num {
        self.mod_floor(&d.abs())
    }
}

impl Add for &Num {
    type Output = Num;

    /// A sum with a kept value is kept: the terms of both, over the least common multiple of
    /// their denominators, collected and folded.
    fn add(self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => (*a as i128 + *b as i128).into(),
            (Word::Kept(x), Word::Kept(y)) => {
                let den = Integer::lcm(&x.den, &y.den);
                let (sx, sy) = (BigInt::from(&den / &x.den), BigInt::from(&den / &y.den));
                let terms = x
                    .terms
                    .iter()
                    .map(|(c, core)| (c * &sx, core.clone()))
                    .chain(y.terms.iter().map(|(c, core)| (c * &sy, core.clone())))
                    .collect();
                Num::kept(terms, &x.d * &sx + &y.d * &sy, den)
            }
            (Word::Kept(x), _) if let Some(s) = other.scalar() => Num::kept(
                x.terms.clone(),
                &x.d + &*s * BigInt::from(x.den.clone()),
                x.den.clone(),
            ),
            (_, Word::Kept(_)) => other + self,
            // Neither is kept.
            _ => (&*self.big() + &*other.big()).into(),
        }
    }
}

impl Sub for &Num {
    type Output = Num;

    fn sub(self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => (*a as i128 - *b as i128).into(),
            _ => self + &-other,
        }
    }
}

impl Mul for &Num {
    type Output = Num;

    /// A product with a kept value is kept: with a value that is not kept, each coefficient
    /// times it; with a kept value, each pair of terms, a product of cores being one core.
    fn mul(self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => (*a as i128 * *b as i128).into(),
            (Word::Kept(x), _) if let Some(s) = other.scalar() => {
                if s.is_zero() {
                    return Num::ZERO;
                }
                let terms = x
                    .terms
                    .iter()
                    .map(|(c, core)| (c * &*s, core.clone()))
                    .collect();
                Num::kept(terms, &x.d * &*s, x.den.clone())
            }
            (_, Word::Kept(_)) if self.scalar().is_some() => other * self,
            (Word::Kept(x), Word::Kept(y)) => {
                let mut terms = Vec::with_capacity((x.terms.len() + 1) * (y.terms.len() + 1));
                for (a, p) in &x.terms {
                    for (b, q) in &y.terms {
                        terms.push((mul_int(a, b), p.times(q)));
                    }
                    if !y.d.is_zero() {
                        terms.push((mul_int(a, &y.d), p.clone()));
                    }
                }
                if !x.d.is_zero() {
                    for (b, q) in &y.terms {
                        terms.push((mul_int(&x.d, b), q.clone()));
                    }
                }
                Num::kept(terms, mul_int(&x.d, &y.d), mul_uint(&x.den, &y.den))
            }
            // Neither is kept.
            _ => mul_int(&self.big(), &other.big()).into(),
        }
    }
}

impl Neg for &Num {
    type Output = Num;

    fn neg(self) -> Num {
        match &self.0 {
            Word::Small(a) => (-(*a as i128)).into(),
            Word::Big(a) => (-&**a).into(),
            // A kept value is at least 2^127 or below -2^127, so its negation lies outside
            // i128 too, except for that of 2^127, which is i128::MIN and must be Big.
            Word::Kept(k) if !k.negative && *self == Num::from(BigInt::from(1u32) << 127u32) => {
                Num::from(i128::MIN)
            }
            Word::Kept(k) => Num(Word::Kept(Box::new(k.neg()))),
        }
    }
}

impl Ord for Num {
    /// Values of one sign outside `i64` compare by the sign of their difference, a kept value
    /// whose terms are collected and folded, so equal cores cancel; a root against the power
    /// it came from by `root_power_cmp`. The sign of a kept difference is found at 64 bits
    /// and then at twice as many until it is decided; for values that differ in their leading
    /// bits, as bounds nearly always do, the first pass decides. Equal values in forms that
    /// neither collecting nor folding relates are found equal only at the bits of the value
    /// (the tradeoffs at `Core::same` and `fold`).
    fn cmp(&self, other: &Num) -> Ordering {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => return a.cmp(b),
            (Word::Big(a), Word::Big(b)) => return a.cmp(b),
            // A value outside i64 lies outside every small one.
            (_, Word::Small(_)) => {
                return if self.signum() < 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
            }
            (Word::Small(_), _) => return other.cmp(self).reverse(),
            _ => {}
        }
        match self.signum().cmp(&other.signum()) {
            Ordering::Equal => {}
            o => return o,
        }
        if let (Word::Kept(x), Word::Kept(y)) = (&self.0, &other.0)
            && x == y
        {
            return Ordering::Equal;
        }
        if let Some(o) = root_power_cmp(self, other) {
            return o;
        }
        if let Some(o) = root_power_cmp(other, self) {
            return o.reverse();
        }
        // One pass at 64 bits decides values that differ in their leading bits, as bounds nearly
        // always do; the sign of the difference decides the rest.
        let (a, b) = (self.approx(64), other.approx(64));
        if a.below(&b) {
            return Ordering::Less;
        }
        if b.below(&a) {
            return Ordering::Greater;
        }
        (self - other).signum().cmp(&0)
    }
}

/// `a` against `b`, of one sign, when `a` is `±floor(rad ^ (1 / k)) ^ (m * k)` and `b` lies
/// at or past `±rad ^ m`: that power is at most `rad ^ m`, and below it unless `rad` is a
/// perfect `k`-th power, so no digits of the root are needed. This is the comparison of an
/// image of a root bound with the bound it came from, where approximations would agree to
/// every bit of the root.
fn root_power_cmp(a: &Num, b: &Num) -> Option<Ordering> {
    let Word::Kept(x) = &a.0 else {
        return None;
    };
    let [(Atom::Root { rad, k, .. }, exp)] = x.bare()?.0.as_slice() else {
        return None;
    };
    if !exp.is_multiple_of(k) {
        return None;
    }
    let m = exp / k;
    let bound = if m.is_one() {
        Num(Word::Kept(rad.clone()))
    } else {
        Num::bare(false, rad.bare()?.pow(&m))
    };
    let b = if x.negative { -b } else { b.clone() };
    let o = match bound.cmp(&b) {
        Ordering::Less => Ordering::Less,
        // A root of a bare power of one integer is kept only when it is irrational.
        Ordering::Equal
            if rad.bare().and_then(Core::int_power).is_some() || !is_perfect_power(rad, k) =>
        {
            Ordering::Less
        }
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => return None,
    };
    Some(if x.negative { o.reverse() } else { o })
}

/// Two values given to any precision, in order: at `bits` bits and then at twice as many
/// until their ranges are apart or both are exact.
fn approx_cmp(mut bits: u64, x: impl Fn(u64) -> Approx, y: impl Fn(u64) -> Approx) -> Ordering {
    loop {
        let (a, b) = (x(bits), y(bits));
        if a.below(&b) {
            return Ordering::Less;
        }
        if b.below(&a) {
            return Ordering::Greater;
        }
        if a.is_exact() && b.is_exact() {
            return scaled_cmp(&a.lo, &a.shift, &b.lo, &b.shift);
        }
        bits *= 2;
    }
}

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Num) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Num {
    fn eq(&self, other: &Num) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Num {}

impl Hash for Num {
    /// A value inside `i128` hashes as itself, and a value outside it by its sign alone. This
    /// agrees with equality for every pair of equal values, whatever their forms: a value in
    /// `i64` is always `Small`, a value in `i128` past `i64` always `Big` (a kept value lies
    /// outside `i128`), so a value inside `i128` has one form and hashes as itself; and two
    /// equal values outside `i128`, `Big` or kept, a sum of cores or a root, have one sign.
    // Complexity tradeoff: a hash table keyed by many values outside i128 puts them in one
    // bucket per sign, so a lookup among n of them costs n comparisons; the answers stay
    // exact. Why: a hash that agrees on equal values must be a function of the value alone,
    // computed alike from every form, and a big value may equal a kept root
    // (`floor(3 ^ (901 / 3))` written out and kept), whose residues, leading bits and bit
    // count each need the root's digits or, near a power of 2, the value's. Trigger: a hash
    // map or set holding many interval ends outside i128. Test:
    // `l01_24_refinement_lattices::ends::equal_values_in_different_forms_hash_alike`;
    // COMPLEXITY.md S33. A complete solution would hash every value outside `i128` by its
    // residue modulo a fixed prime: a big value by `%`, a kept value with integer cores by
    // `Kept::residue`, and a kept value holding a root by the residue of each root written
    // out once and kept in the atom's memo, at the cost of the root's digits; equal values
    // have one residue whatever their forms, so this agrees with equality.
    fn hash<H: Hasher>(&self, h: &mut H) {
        match &self.0 {
            Word::Small(v) => v.hash(h),
            Word::Big(v) if let Ok(s) = i128::try_from(&**v) => s.hash(h),
            Word::Big(_) | Word::Kept(_) => self.signum().hash(h),
        }
    }
}

impl std::str::FromStr for Num {
    type Err = num_bigint::ParseBigIntError;

    /// Decimal text, of any length, read as num-bigint reads it: an optional `-` or `+`, then a
    /// digit, then digits and `_`. The digits are read by halves (`zed_kernel::num::read_digits`),
    /// O(n log^2 n) for `n` digits, where num-bigint's reading is O(n^2).
    fn from_str(s: &str) -> Result<Num, Self::Err> {
        if let Ok(v) = s.parse::<i64>() {
            return Ok(Num::from(v));
        }
        // num-bigint takes off a `-` not followed by `+`, then a `+` not followed by `+`.
        let (sign, body) = match s.strip_prefix('-') {
            Some(tail) if !tail.starts_with('+') => (Sign::Minus, tail),
            _ => (Sign::Plus, s),
        };
        let body = match body.strip_prefix('+') {
            Some(tail) if !tail.starts_with('+') => tail,
            _ => body,
        };
        let digits = body.as_bytes().first().is_some_and(u8::is_ascii_digit)
            && body.bytes().all(|b| b.is_ascii_digit() || b == b'_');
        if !digits {
            // Not decimal digits: num-bigint finds the error, in one pass over the text.
            return s.parse::<BigInt>().map(Num::from);
        }
        let n = match body.contains('_') {
            true => read_digits(&body.replace('_', "")),
            false => read_digits(body),
        };
        Ok(Num::from(BigInt::from_biguint(sign, n)))
    }
}

impl fmt::Display for Num {
    // Complexity tradeoff: a kept value is shown in decimal, written out, at the cost of its
    // digits and their conversion to decimal. Why: a kept value has no shorter decimal text,
    // and the printed value must be one a user can write back. Trigger: printing or
    // serializing an interval end outside i128 made from a power (`canon::serial` writes ends
    // past i64 with this). Test:
    // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
    // (each value against its text); COMPLEXITY.md S33. A complete solution would print a
    // kept value in its own form, as Zed text such as `3 ^ 100000000 + 1`, which parses
    // back to the same value.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Word::Small(v) => write!(f, "{v}"),
            Word::Big(v) => write_decimal(f, v),
            Word::Kept(k) => write_decimal(f, &k.expand()),
        }
    }
}

/// `v` in decimal, as num-bigint writes it, the digits by [`to_decimal`]: O(n log^2 n) for `n`
/// words, against num-bigint's `n^1.5` (COMPLEXITY.md K81).
fn write_decimal(f: &mut fmt::Formatter<'_>, v: &BigInt) -> fmt::Result {
    if v.sign() == Sign::Minus {
        f.write_str("-")?;
    }
    f.write_str(&to_decimal(v.magnitude()))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The least root by trying every index from the largest down, written out.
    fn least_root_by_trial(b: u64) -> (u64, u64) {
        (2..64)
            .rev()
            .find_map(|m: u32| {
                let r = (b as f64).powf(1.0 / f64::from(m)).round() as u64;
                (r.max(2) - 1..=r + 1)
                    .find(|&r| r >= 2 && r.checked_pow(m) == Some(b))
                    .map(|r| (r, u64::from(m)))
            })
            .unwrap_or((b, 1))
    }

    #[test]
    fn least_roots_agree_with_trial_and_with_powers_of_large_bases() {
        for b in 2..50_000u64 {
            let (r, m) = least_root(BigUint::from(b));
            assert_eq!((r, m), {
                let (r, m) = least_root_by_trial(b);
                (BigUint::from(r), BigUint::from(m))
            });
        }
        // Powers of bases that are no powers, odd, even and with odd parts, to prime and
        // composite exponents, and their neighbors, which are no powers.
        let mersenne = (BigUint::from(1u32) << 127u32) - 1u32;
        let bases = [
            mersenne.clone(),
            &mersenne << 5u32,
            &mersenne * 6u32,
            BigUint::from(6u32),
            BigUint::from(10u32).pow(40) + 3u32,
        ];
        for r in &bases {
            for m in [2u32, 3, 5, 6, 7, 12, 31, 97, 210] {
                let b = r.pow(m);
                assert_eq!(least_root(b.clone()), (r.clone(), BigUint::from(m)));
                for d in [1u32, 2] {
                    let near = &b + d;
                    assert_eq!(least_root(near.clone()), (near, BigUint::from(1u32)));
                }
            }
        }
        // A power of 2 alone, whatever its exponent.
        assert_eq!(
            least_root(BigUint::from(1u32) << 4099u32),
            (BigUint::from(2u32), BigUint::from(4099u32))
        );
    }

    #[test]
    fn stripping_a_power_of_2_agrees_with_dividing_once_per_factor() {
        for t in [1u32, 2, 3, 7, 64, 65, 200] {
            let c = BigUint::from(1u32) << t;
            for (z, odd) in [
                (0u32, 1u32),
                (1, 3),
                (6, 5),
                (64, 7),
                (199, 1),
                (1000, 9),
                (1001, 1),
            ] {
                let mut rest = BigUint::from(odd) << z;
                let (mut want, mut k) = (rest.clone(), 0u64);
                while (&want % &c).is_zero() {
                    want /= &c;
                    k += 1;
                }
                assert_eq!(strip(&mut rest, &c), k, "t = {t}, z = {z}");
                assert_eq!(rest, want, "t = {t}, z = {z}");
            }
        }
    }

    /// Item SCALE-fix-strip-odd: `strip` by a factor that is not a power of 2, odd, even,
    /// composite, a power of another, or wider than a word, against dividing once per factor,
    /// on `c ^ k * u` for multiplicities `k` around powers of 2 and random `u`, some past the
    /// widths at which the kernel divides by a reciprocal.
    #[test]
    fn stripping_any_factor_agrees_with_dividing_once_per_factor() {
        let mut seed = 0x5eed_u64;
        let mut next = move || {
            seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let z = (seed ^ (seed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            let z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        let wide = BigUint::from_slice(&[0x8000_0001, 0x1234_5679, 0xdead_beef, 0x7]);
        let factors = [
            BigUint::from(3u32),
            BigUint::from(5u32),
            BigUint::from(6u32),
            BigUint::from(9u32),
            BigUint::from(15u32),
            BigUint::from(12u32),
            BigUint::from(u64::MAX),
            wide,
        ];
        for c in &factors {
            for k in [
                0u64, 1, 2, 3, 7, 8, 9, 63, 64, 65, 255, 1000, 4095, 4096, 6000,
            ] {
                if k * c.bits() > 20_000 {
                    continue;
                }
                for words in [1usize, 2, 40, 300] {
                    let u = BigUint::from_slice(
                        &(0..2 * words).map(|_| next() as u32).collect::<Vec<_>>(),
                    ) + 1u32;
                    let mut rest = c.pow(u32::try_from(k).unwrap()) * &u;
                    let (mut want, mut times) = (rest.clone(), 0u64);
                    while (&want % c).is_zero() {
                        want /= c;
                        times += 1;
                    }
                    assert_eq!(strip(&mut rest, c), times, "c = {c}, k = {k}, u = {u}");
                    assert_eq!(rest, want, "c = {c}, k = {k}, u = {u}");
                }
            }
        }
    }

    #[test]
    fn a_root_in_one_word_is_the_root_by_big_numbers() {
        let mut x = 7u64;
        for p in [3u64, 5, 7, 11, 13, 31, 61, 127, 509, 4093, 65_521] {
            for _ in 0..200 {
                x = x.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(1);
                let o = x | 1;
                let word = odd_root_mod_word(o, p);
                for k in [1u64, 2, 17, 63, 64] {
                    let mask = u64::MAX >> (64 - k);
                    let big = odd_root_mod_pow2(&BigUint::from(o), p, k);
                    assert_eq!(BigUint::from(word & mask), big, "o = {o}, p = {p}, k = {k}");
                    // The one odd root below 2^k.
                    let m = BigUint::from(1u32) << k;
                    assert!(big.bit(0) && big < m, "o = {o}, p = {p}, k = {k}");
                    assert_eq!(big.modpow(&BigUint::from(p), &m), BigUint::from(o) % &m);
                }
            }
        }
        // Wider roots, by the same test.
        for (p, k) in [(3u64, 65u64), (3, 1000), (5, 4097), (31, 300), (509, 129)] {
            for seed in 0..20u32 {
                let o = (BigUint::from(3u32).pow(2000 + seed) << 1u32) + 1u32;
                let r = odd_root_mod_pow2(&o, p, k);
                let m = BigUint::from(1u32) << k;
                assert!(r.bit(0) && r < m, "p = {p}, k = {k}");
                assert_eq!(r.modpow(&BigUint::from(p), &m), &o % &m, "p = {p}, k = {k}");
            }
        }
    }

    #[test]
    fn a_remainder_tree_gives_each_remainder() {
        let x = BigUint::from(3u32).pow(5000u32) + 12_345u32;
        // Lengths 0 to 9 take every shape of tree, with products moved up at odd lengths.
        let all: Vec<u64> = (0..9u64).map(|i| u64::MAX - 58 - 2 * i).collect();
        for len in 0..=all.len() {
            let ms = &all[..len];
            let want: Vec<u64> = ms
                .iter()
                .map(|&m| u64::try_from(&x % m).expect("below m"))
                .collect();
            assert_eq!(remainders(&x, ms), want, "{len} moduli");
        }
        // A number below the product of the moduli.
        assert_eq!(remainders(&BigUint::from(5u32), &[7, 11, 13]), [5, 5, 5]);
    }

    #[test]
    fn each_index_wider_than_a_word_has_its_least_prime() {
        let o = BigUint::from(3u32).pow(3000u32);
        let odd = OddPart::of(&o);
        let filter = odd.filter();
        // 3000 * log2(3) is 4755 bits: the indices wider than a word are the odd primes to 73.
        let ps: Vec<u64> = filter.wide.iter().map(|&(p, _, _)| p).collect();
        assert_eq!(
            ps,
            [
                3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73
            ]
        );
        for &(p, q, oq) in &filter.wide {
            assert!(is_prime(q) && (q - 1).is_multiple_of(p), "p = {p}, q = {q}");
            assert!(
                (1..q / p).all(|k| !is_prime(k * p + 1)),
                "{q} is the least prime 1 modulo {p}"
            );
            assert_eq!(BigUint::from(oq), &o % q, "p = {p}");
        }
        // 3 ^ 3000 is a 3rd and a 5th power, so it passes both indices.
        for p in [3u64, 5] {
            assert!(odd.passes(p), "p = {p}");
        }
    }

    #[test]
    fn values_past_i128_keep_their_order_and_come_back_small() {
        let max = Int::from(i128::MAX);
        let min = Int::from(i128::MIN);
        let past = &max + &Int::ONE;
        assert_eq!(past.to_i128(), None);
        assert_eq!((&past - &Int::ONE).to_i128(), Some(i128::MAX));
        assert!(past > max && min > &min - &Int::ONE);
        assert_eq!(-&past, min);
        assert!(past > min && &min - &Int::ONE < -&past);
        // -i128::MIN is past i128; negated again it is the small value, one form for one value.
        assert_eq!(-&(-&min), min);
        assert_eq!(min.abs(), &max + &Int::ONE);
        assert_eq!((&max * &max).div_floor(&max), max);
        assert_eq!((&(&max * &max) + &Int::from(5)).mod_floor(&max), 5.into());
    }

    #[test]
    fn division_rounds_down_and_the_gcd_is_never_negative() {
        let (a, m) = (Int::from(-7), Int::from(2));
        assert_eq!(a.div_floor(&m), Int::from(-4));
        assert_eq!(a.mod_floor(&m), Int::ONE);
        assert_eq!(Int::from(-12).gcd(&Int::from(18)), Int::from(6));
        // Both are powers of two, so the gcd of i128::MIN with itself does not fit in i128.
        let min = Int::from(i128::MIN);
        assert_eq!(min.gcd(&min), -&min);
        assert_eq!(Int::ZERO.gcd(&Int::from(-5)), Int::from(5));
    }

    /// The 64-bit, 128-bit and big paths of `div_floor` and `mod_floor` give the floor quotient
    /// and remainder of `BigInt` for every sign of each operand, at and across the ends of
    /// `i64` and `i128`, including `MIN / -1`, whose quotient does not fit.
    #[test]
    fn floor_division_agrees_on_every_path_for_every_sign() {
        let mut ends: Vec<BigInt> = [1, 2, 3, 7]
            .map(BigInt::from)
            .into_iter()
            .chain([i128::from(i64::MAX), i128::MAX].into_iter().flat_map(|v| {
                let v = BigInt::from(v);
                [&v - 1, v.clone(), &v + 1, &v + 2]
            }))
            .chain([BigInt::from(1) << 200])
            .collect();
        ends.extend(ends.clone().into_iter().map(|v| -v));
        let zero = BigInt::zero();
        for a in ends.iter().chain([&zero]) {
            for m in &ends {
                let (x, y) = (Int::from(a.clone()), Int::from(m.clone()));
                let want = (Int::from(a.div_floor(m)), Int::from(a.mod_floor(m)));
                assert_eq!((x.div_floor(&y), x.mod_floor(&y)), want, "{a} by {m}");
            }
        }
    }
}
