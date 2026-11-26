//! Rounding an exact quotient of integers to a whole number under a named rule ([`Rounding`],
//! [`div_round`]), and splitting a whole amount into weighted parts that add up to it exactly
//! ([`allocate`]) (plan row LIB-rat-round-scale, from PITH-VS-ZED.md, candidate "Named rounding
//! of `rat` to a scale, and `allocate`"). zed-kernel's `Rat::round_whole` and
//! `Rat::round_to_scale` take their rule from here; rounding to a scale of `s` decimal places is
//! rounding `x * 10^s` to a whole number, which the kernel does on its kept powers.
//!
//! No rule is a default here: every function takes its [`Rounding`]. The language's `round(x)`
//! means [`Rounding::TiesEven`] by DESIGN.md sec:facets, "Rounding to a whole number", and
//! that choice is made where the primitive is read (zed-kernel `words.rs`, `rounding_of`), not
//! here.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::Zero;

use crate::fast;

/// How a number that is not whole is rounded to a whole one: the rules of `round` (ties to
/// even), `round(x, ties: #away)`, `floor`, `ceil`, `trunc` and `awayFromZero` (DESIGN.md
/// sec:facets, "Rounding to a whole number"). Moved here from zed-kernel `num.rs` with
/// LIB-rat-round-scale, so that [`div_round`] and zed-kernel's `Rat::round_whole` decide by one
/// table, [`Rounding::rounds_up`].
// Source of the two names to the nearest: IEEE Std 754-2019, "IEEE Standard for Floating-Point
// Arithmetic", IEEE, 2019, doi:10.1109/IEEESTD.2019.8766229, section 4.3, "Rounding-direction
// attributes". Sketch: roundTiesToEven delivers the representable value nearest the exact
// result and, of two equally near, the one with an even least significant digit;
// roundTiesToAway delivers, of two equally near, the one larger in magnitude. Here the
// "representable values" are the whole numbers, so even means an even whole number. Read
// 2026-11-20 in the 2019 text (the copy named at the `sqrt` rule in zed-kernel `eval.rs`),
// 4.3.1, "Rounding-direction attributes to nearest", p. 27: roundTiesToEven, "the
// floating-point number nearest to the infinitely precise result shall be delivered; if the
// two nearest floating-point numbers bracketing an unrepresentable infinitely precise result
// are equally near, the one with an even least significant digit shall be delivered; if that
// is not possible, the one larger in magnitude shall be delivered"; roundTiesToAway, "if the
// two nearest ... are equally near, the one with larger magnitude shall be delivered". The case
// "if that is not possible" (two odd neighbors, for one-digit precision) cannot happen for
// whole numbers, of which one of any two neighbors is even. And 4.3.2, "Directed rounding
// attributes", p. 27: roundTowardPositive gives the number "closest to and no less than the
// infinitely precise result", roundTowardNegative the one "closest to and no greater than"
// it, roundTowardZero the one "closest to and no greater in magnitude than" it; these are
// `ceil`, `floor` and `trunc` here.
//
// Every one of these rules is monotone: x <= y gives round(x) <= round(y). The standard
// states this only for conversions to and from character sequences (5.12.2, NOTE 1, p. 46,
// "Conversions are monotonic"), so here is the proof from the definitions above, for any
// set of representable values (floats with their infinities, or whole numbers). Directed:
// roundTowardNegative(x) is the greatest value <= x, and every value <= x is <= y, so it is
// <= roundTowardNegative(y); roundTowardPositive is the mirror image, and roundTowardZero is
// roundTowardNegative on x >= 0 and roundTowardPositive on x <= 0, both monotone and both 0
// at 0. To nearest: let r = round(x), s = round(y), x <= y, and suppose s < r. Let f(t) =
// |t - s| - |t - r|; for s < r it is -(r - s) up to s, 2t - r - s between, r - s from r on,
// so f does not decrease. r nearest to x gives f(x) >= 0, s nearest to y gives f(y) <= 0, so
// 0 <= f(x) <= f(y) <= 0 and f(x) = f(y) = 0, which forces x = y = (r + s) / 2: one tie
// broken two ways. But both tie rules pick one of the two neighbors by a fixed property (even
// digit, or larger magnitude), so they pick the same one, r = s, a contradiction. Overflow:
// 4.3.1 sends every result of magnitude at least b^emax (b - b^(1-p) / 2) to the infinity of
// its sign. If y is at or past that bound, round(y) = +inf is above every value; if x is at
// or past its negative, round(x) = -inf is below every value; otherwise x and y both lie
// inside, where the nearest values are finite and the proof above applies. (Whole numbers
// have no largest one, so this case does not arise for whole-number rounding.) zedc-lattice
// `grade.rs` relies on this proof.
// Departure: the standard rounds to a float format; this rounds an exact rational to an
// integer, so no precision or overflow enters. Tests: `l01_18_scalar_interpreter::rounding`,
// which checks ties at both signs under both rules (it catches a tie sent the wrong way, not
// a misreading of the standard shared by the test and the code), and this module's
// `tests::each_rule_on_zero_signs_ties_and_huge_values` and
// `tests::quotients_round_as_the_nearer_neighbor_says`. Other sites that name these rules
// point here.
//
// Other implementations compared (P339, read 2026-11-26): Java `java.math.RoundingMode` has
// these six (HALF_EVEN, HALF_UP, FLOOR, CEILING, DOWN, UP) and also HALF_DOWN and UNNECESSARY;
// Python `decimal` has these six and also ROUND_HALF_DOWN and ROUND_05UP; Pith's
// `decimal.div` (docs/numbers.md at Pith 183a9199, "Division says how it rounds") has these
// six and `half_down`. A tie toward zero is in no rule of DESIGN, so it is not offered here.
// The known defects of those libraries are in their inputs, not their rules: Java's `new
// BigDecimal(0.1)` and Python's `round(2.675, 2) == 2.67` round the binary float, not the
// decimal written; a `rat` holds the decimal written exactly, so neither arises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rounding {
    /// To the nearest, a tie to the even neighbor (IEEE 754 roundTiesToEven).
    TiesEven,
    /// To the nearest, a tie away from zero (IEEE 754 roundTiesToAway).
    TiesAway,
    /// Toward −∞.
    Floor,
    /// Toward +∞.
    Ceil,
    /// Toward zero.
    Trunc,
    /// Away from zero.
    AwayFromZero,
}

impl Rounding {
    /// Whether a number `x` that is not whole rounds to `floor(x) + 1` rather than to
    /// `floor(x)`, given whether `x` is negative, whether `floor(x)` is odd, and `half`, the
    /// order of `2 (x - floor(x))` against 1 (so `Equal` is a tie). Every caller writes
    /// `x = N / D` with `D > 0`, and `half` is `2 (N mod D)` against `D`, `mod` Euclidean.
    ///
    /// Proof of each arm, for `x` not whole, so `floor(x) < x < floor(x) + 1`: `Floor` keeps
    /// `floor(x)` and `Ceil` takes `floor(x) + 1` by definition. `Trunc` is `Ceil` below zero
    /// and `Floor` above, and `AwayFromZero` the reverse. To the nearest, `x - floor(x)` above
    /// one half (`Greater`) is nearer `floor(x) + 1` and below (`Less`) nearer `floor(x)`; at
    /// a tie `TiesEven` takes the even one of the two neighbors, `floor(x) + 1` exactly when
    /// `floor(x)` is odd, and `TiesAway` the one of larger magnitude, `floor(x) + 1` exactly
    /// when `x > 0` (for `x < 0` both neighbors are at most 0, and `floor(x)` is the farther
    /// from 0).
    #[inline]
    pub fn rounds_up(self, negative: bool, floor_is_odd: bool, half: Ordering) -> bool {
        match self {
            Rounding::Floor => false,
            Rounding::Ceil => true,
            Rounding::Trunc => negative,
            Rounding::AwayFromZero => !negative,
            Rounding::TiesEven => match half {
                Ordering::Equal => floor_is_odd,
                o => o == Ordering::Greater,
            },
            Rounding::TiesAway => match half {
                Ordering::Equal => !negative,
                o => o == Ordering::Greater,
            },
        }
    }
}

/// `n / d` rounded to a whole number by `rule`; `d` must not be zero.
///
/// Method: `q, r = |n| divmod d` by [`fast::div_rem`]; with `r = 0` the quotient is `±q`.
/// Otherwise `floor(n / d)` is `q` with remainder `r` for `n > 0`, and `-(q + 1)` with
/// remainder `d - r` for `n < 0` (since `-|n| = -(q + 1) d + (d - r)` and `0 < d - r < d`),
/// and [`Rounding::rounds_up`] decides from the sign, the parity of the floor and twice that
/// remainder against `d`.
///
/// Complexity tradeoff: none given up. The naive method compares the distances to both
/// neighbors, `n - lo d` and `(lo + 1) d - n`, two products of the size of `n`; here one
/// division, O(M(b)) in the bits b of `n` past [`fast::div_rem`]'s crossover, and a shift and
/// a comparison linear in the size of `d`. Scaling test: `bench::rounded_quotients_scale`.
///
/// # Panics
///
/// When `d` is zero, as [`fast::div_rem`] does.
pub fn div_round(n: &BigInt, d: &BigUint, rule: Rounding) -> BigInt {
    let (q, r) = fast::div_rem(n.magnitude(), d);
    if r.is_zero() {
        // `from_biguint` gives zero no sign, so `-0 / d` is 0.
        return BigInt::from_biguint(n.sign(), q);
    }
    let negative = n.sign() == Sign::Minus;
    let (floor, rest) = match negative {
        true => (-BigInt::from(q + 1u32), d - r),
        false => (BigInt::from(q), r),
    };
    let half = (rest << 1u32).cmp(d);
    match rule.rounds_up(negative, floor.is_odd(), half) {
        true => floor + 1u32,
        false => floor,
    }
}

/// `total` split into one part for each weight, each part `total * w / W` rounded down or up,
/// so that the parts add up to `total` exactly; `W` is the sum of the weights. `None` when `W`
/// is zero (no weights, or all zero), since nothing can then receive the amount. The parts
/// have the sign of `total`.
///
/// Method: the largest remainder method (Hamilton's method of apportionment), on `|total|`.
/// Each part starts at `floor(|total| w_i / W)`, with remainder `r_i = |total| w_i mod W`;
/// the `k` units left over go one each to the `k` parts with the largest `r_i`, a tie to the
/// earlier part. The sign of `total` is put on every part at the end, so
/// `allocate(-t, w)` is `-allocate(t, w)`: the same parts take the extra unit whatever the sign.
///
/// Proof that the parts add up and each lies between the floor and the ceiling of its exact
/// share: `|total| W = sum_i |total| w_i = W sum_i q_i + sum_i r_i`, so
/// `sum_i r_i = W k` with `k = |total| - sum_i q_i`, and `k >= 0`. Each `r_i < W`, so
/// `W k = sum_i r_i < W m`, where `m` is the number of parts with `r_i > 0`: `k < m`. So the
/// `k` largest remainders are all positive, every part given a unit has a share that is not
/// whole (it goes from its floor to its ceiling), a part with `r_i = 0` (a zero weight among
/// them) gets exactly its share, and after the `k` units the parts add up to
/// `sum_i q_i + k = |total|`. The parts given a unit are those with the largest fractional
/// shares `r_i / W`, so the result is the one Hamilton's method gives, with ties broken by order.
///
/// Other implementations compared (P339, read 2026-11-26), and the defects not copied:
/// - moneyphp/money `Money::allocate` (github.com/moneyphp/money, `src/Money.php`, master,
///   read through its source text): also the largest remainder, but it ranks the fractions as
///   PHP floats, `(float) $ratio / $total * (float) $amount`, which are not exact once the
///   amount passes 2^53, so a large amount can give the unit to the wrong part; and its loop
///   runs only `while ($remainder > 0)`, so the leftover of a negative amount is not handed out
///   at all when the share rounds toward zero. Here the remainders are exact integers and the
///   sign is put on at the end. Tests: `tests::wide_totals_rank_remainders_exactly`,
///   `tests::a_negative_total_is_the_negated_split`.
/// - dinero.js `distribute` (github.com/dinerojs/dinero.js,
///   `packages/dinero.js/src/core/utils/distribute.ts` at 4486cb3e, read in full): it returns
///   the ratios themselves when they add up to zero, so the amount is lost without an error;
///   and it gives the leftover units by the largest *ratio*, not the largest remainder, so
///   `2` over `[2, 1, 1]` gives `[2, 0, 0]`, the first part twice its exact share 1 while the
///   other two, of share 1/2, get nothing. Its sort comparator never answers "equal", so the
///   order of equal ratios depends on the engine's sort. Here zero weights give `None`, and
///   that split is `[1, 1, 0]`. Tests: `tests::all_zero_weights_have_no_split`,
///   `tests::the_extra_units_go_by_remainder_not_by_weight`.
/// - Pith `decimal.allocate` (docs/numbers.md at Pith 183a9199, "Splitting an amount without
///   losing a cent"; its source was not read): integer weights, `10.00` over `[1, 1, 1]` is
///   `3.34, 3.33, 3.33`, which this gives (`tests::pith_and_the_usual_splits`).
/// - M. Fowler, *Patterns of Enterprise Application Architecture*, Addison-Wesley 2002, the
///   Money pattern's `allocate(long[] ratios)`, from memory, not checked: it hands the
///   leftover to the first parts in order, whatever their remainders, which gives a part of
///   weight 0 a unit (`1` over `[0, 1, 1]` gives `[1, 0, 0]`). Here it gives `[0, 1, 0]`.
///
/// Complexity tradeoff: none given up. The parts cost one product and one division each,
/// O(n M(b)) for n weights and b the bits of `|total| w_i`, and the ranking sorts the indices
/// of the positive remainders, O(n log n) comparisons of numbers smaller than `W`. Handing the
/// units out one at a time to the part of largest remaining fraction, as an oracle does, is
/// O(n k), quadratic when `k` is near n. Scaling test: `bench::allocations_scale`.
pub fn allocate(total: &BigInt, weights: &[BigUint]) -> Option<Vec<BigInt>> {
    let sum: BigUint = weights.iter().sum();
    if sum.is_zero() {
        return None;
    }
    let t = total.magnitude();
    let (mut parts, rems): (Vec<BigUint>, Vec<BigUint>) = weights
        .iter()
        .map(|w| fast::div_rem(&fast::mul(t, w), &sum))
        .unzip();
    let given: BigUint = parts.iter().sum();
    // `given <= |total|` and `|total| - given = k < m <= weights.len()` (proof above), so the
    // subtraction does not underflow and `k` fits in a usize.
    let k = usize::try_from(t - given).expect("k is below the number of parts (proof above)");
    let mut order: Vec<usize> = (0..rems.len()).filter(|&i| !rems[i].is_zero()).collect();
    // Unstable is enough: the keys `(r_i, i)` are distinct.
    order.sort_unstable_by(|&a, &b| rems[b].cmp(&rems[a]).then(a.cmp(&b)));
    for &i in &order[..k] {
        parts[i] += 1u32;
    }
    Some(
        parts
            .into_iter()
            .map(|p| BigInt::from_biguint(total.sign(), p))
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Signed};

    const RULES: [Rounding; 6] = [
        Rounding::TiesEven,
        Rounding::TiesAway,
        Rounding::Floor,
        Rounding::Ceil,
        Rounding::Trunc,
        Rounding::AwayFromZero,
    ];

    fn int(n: i64) -> BigInt {
        BigInt::from(n)
    }

    fn uint(n: u64) -> BigUint {
        BigUint::from(n)
    }

    /// The whole number each rule gives, from the nearer of the two whole numbers around
    /// `n / d` by their distances, with num-bigint's own floor division: no use of
    /// [`Rounding::rounds_up`] or of [`fast::div_rem`]. The same oracle as zed-kernel
    /// `num/units.rs` `rounded`, which tests `Rat::round_whole` through the kernel's kept
    /// powers.
    fn rounded(n: &BigInt, d: &BigInt, rule: Rounding) -> BigInt {
        let lo = n.div_floor(d);
        if &lo * d == *n {
            return lo;
        }
        let hi = &lo + 1;
        let (below, above) = (n - &lo * d, &hi * d - n);
        let neg = n.is_negative();
        let nearer = |tie: bool| match below.cmp(&above) {
            Ordering::Less => false,
            Ordering::Greater => true,
            Ordering::Equal => tie,
        };
        let up = match rule {
            Rounding::Floor => false,
            Rounding::Ceil => true,
            Rounding::Trunc => neg,
            Rounding::AwayFromZero => !neg,
            Rounding::TiesEven => nearer(lo.is_odd()),
            Rounding::TiesAway => nearer(!neg),
        };
        if up { hi } else { lo }
    }

    /// DESIGN.md's table of the six rules (sec:facets, "Rounding to a whole number": `0.5`,
    /// `1.5`, `2.5`, `-2.5`, `2.4`), zero, whole numbers of both signs, and a tie between
    /// numbers of 1,000 bits. Negative control, run once: `TiesEven`'s tie sent to the odd
    /// neighbor (`floor_is_odd` to `!floor_is_odd` in `rounds_up`), caught at 0.5 and 2.5.
    #[test]
    fn each_rule_on_zero_signs_ties_and_huge_values() {
        // (n, d, [TiesEven, TiesAway, Floor, Ceil, Trunc, AwayFromZero])
        let table: [(i64, u64, [i64; 6]); 9] = [
            (1, 2, [0, 1, 0, 1, 0, 1]),
            (3, 2, [2, 2, 1, 2, 1, 2]),
            (5, 2, [2, 3, 2, 3, 2, 3]),
            (-5, 2, [-2, -3, -3, -2, -2, -3]),
            (12, 5, [2, 2, 2, 3, 2, 3]),
            (-12, 5, [-2, -2, -3, -2, -2, -3]),
            (0, 7, [0; 6]),
            (-21, 7, [-3; 6]),
            (-1, 2, [0, -1, -1, 0, 0, -1]),
        ];
        for (n, d, want) in table {
            for (rule, w) in RULES.into_iter().zip(want) {
                assert_eq!(
                    div_round(&int(n), &uint(d), rule),
                    int(w),
                    "{n}/{d} {rule:?}"
                );
            }
        }
        // A tie of wide numbers: (2 m + 1) / 2 with m = 3^630 (999 bits), odd, so the even
        // neighbor is m + 1; and its negative, whose even neighbor is -(m + 1).
        let m = num_traits::pow(int(3), 630);
        let n = &m * 2 + 1;
        let two = uint(2);
        assert_eq!(div_round(&n, &two, Rounding::TiesEven), &m + 1);
        assert_eq!(div_round(&n, &two, Rounding::TiesAway), &m + 1);
        assert_eq!(div_round(&n, &two, Rounding::Trunc), m.clone());
        assert_eq!(div_round(&-&n, &two, Rounding::TiesEven), -(&m + 1));
        assert_eq!(div_round(&-&n, &two, Rounding::TiesAway), -(&m + 1));
        assert_eq!(div_round(&-&n, &two, Rounding::Ceil), -m.clone());
        // Huge over huge, not a tie: (m^2 + 1) / m is just above m.
        let d = m.magnitude().clone();
        let n = &m * &m + 1;
        for rule in RULES {
            let up = matches!(rule, Rounding::Ceil | Rounding::AwayFromZero);
            let want = if up { &m + 1 } else { m.clone() };
            assert_eq!(div_round(&n, &d, rule), want, "{rule:?}");
        }
    }

    /// [`div_round`] against [`rounded`] on random numerators of 0 to 300 bits of both signs
    /// and divisors of 1 to 200 bits, half of them built as ties (`n = q d + d / 2` for an even
    /// `d`), every rule. Each draw is a case the rule must meet, so the test holds on every
    /// seed.
    #[test]
    fn quotients_round_as_the_nearer_neighbor_says() {
        let mut rng = crate::seed::Rng::new(crate::seed::seed(
            "quotients_round_as_the_nearer_neighbor_says",
        ));
        for i in 0..2000 {
            let mut d = wide(&mut rng, 1, 200);
            if d.is_zero() {
                d = BigUint::one();
            }
            let n = match i % 2 {
                0 => BigInt::from(wide(&mut rng, 0, 300)),
                _ => {
                    d <<= 1u32;
                    BigInt::from(wide(&mut rng, 0, 100) * &d + (&d >> 1u32))
                }
            };
            let n = if rng.below(2) == 0 { -n } else { n };
            let di = BigInt::from(d.clone());
            for rule in RULES {
                assert_eq!(
                    div_round(&n, &d, rule),
                    rounded(&n, &di, rule),
                    "{n}/{d} {rule:?}"
                );
            }
        }
    }

    /// A random number of `lo` to `hi` bits (at most that many: the top bits may be zero).
    fn wide(rng: &mut crate::seed::Rng, lo: usize, hi: usize) -> BigUint {
        let bits = lo + rng.below(hi - lo + 1);
        let words: Vec<u32> = (0..bits.div_ceil(32))
            .map(|_| rng.next_u64() as u32)
            .collect();
        BigUint::from_slice(&words) >> (bits.div_ceil(32) * 32 - bits)
    }

    fn parts(total: i64, weights: &[u64]) -> Option<Vec<i64>> {
        let ws: Vec<BigUint> = weights.iter().map(|&w| uint(w)).collect();
        allocate(&int(total), &ws).map(|ps| {
            ps.iter()
                .map(|p| i64::try_from(p).expect("small"))
                .collect()
        })
    }

    #[test]
    fn pith_and_the_usual_splits() {
        assert_eq!(parts(1000, &[1, 1, 1]), Some(vec![334, 333, 333]));
        assert_eq!(parts(100, &[3, 7]), Some(vec![30, 70]));
        assert_eq!(parts(5, &[1, 1]), Some(vec![3, 2]));
        assert_eq!(parts(0, &[1, 2, 3]), Some(vec![0, 0, 0]));
        assert_eq!(parts(7, &[5]), Some(vec![7]));
        // Exact shares 3.5, 1.75, 1.75: the remainders are 2, 3, 3 (of 4), so the two units
        // go to the last two parts.
        assert_eq!(parts(7, &[2, 1, 1]), Some(vec![3, 2, 2]));
    }

    #[test]
    fn all_zero_weights_have_no_split() {
        assert_eq!(parts(10, &[0, 0]), None);
        assert_eq!(parts(10, &[]), None);
        assert_eq!(parts(0, &[]), None);
    }

    /// dinero.js gives `[2, 0, 0]` here and Fowler's method `[1, 0, 0]` on the second;
    /// a part of weight 0 never gets a unit.
    #[test]
    fn the_extra_units_go_by_remainder_not_by_weight() {
        assert_eq!(parts(2, &[2, 1, 1]), Some(vec![1, 1, 0]));
        assert_eq!(parts(1, &[0, 1, 1]), Some(vec![0, 1, 0]));
        assert_eq!(parts(3, &[0, 1, 0, 1, 0]), Some(vec![0, 2, 0, 1, 0]));
    }

    #[test]
    fn a_negative_total_is_the_negated_split() {
        assert_eq!(parts(-1000, &[1, 1, 1]), Some(vec![-334, -333, -333]));
        assert_eq!(parts(-2, &[2, 1, 1]), Some(vec![-1, -1, 0]));
        assert_eq!(parts(-1, &[1, 1, 1]), Some(vec![-1, 0, 0]));
    }

    /// Remainders that differ only past 2^53, where moneyphp's floats tie: `t = 2^80 + 1` over
    /// `[2^60 - 1, 2^60 + 1]`, `W = 2^61`. Then `t w_1 = 2^140 - 2^80 + 2^60 - 1`, so
    /// `q_1 = 2^79 - 2^19` and `r_1 = 2^60 - 1`; `t w_2 = 2^140 + 2^80 + 2^60 + 1`, so
    /// `q_2 = 2^79 + 2^19` and `r_2 = 2^60 + 1`; `k = 1`. The fractions `1/2 -+ 2^-61` are
    /// both 0.5 as doubles; exactly, the second is larger and takes the unit.
    #[test]
    fn wide_totals_rank_remainders_exactly() {
        let one = BigInt::one();
        let t = (&one << 80u32) + 1;
        let ws = [
            (BigUint::one() << 60u32) - 1u32,
            (BigUint::one() << 60u32) + 1u32,
        ];
        let got = allocate(&t, &ws).expect("weights");
        let want = vec![
            (&one << 79u32) - (&one << 19u32),
            (&one << 79u32) + (&one << 19u32) + 1,
        ];
        assert_eq!(got, want);
        assert_eq!(got, one_at_a_time(&t, &ws));
        assert_eq!(got.iter().sum::<BigInt>(), t);
        let big = num_traits::pow(int(10), 100) + 1;
        let got = allocate(&big, &[uint(1), uint(1)]).expect("weights");
        assert_eq!(got[0], &got[1] + 1);
    }

    /// The oracle: each part's floor by num-bigint's division, then one unit at a time to the
    /// part whose exact share exceeds its part the most, comparing `t w_i - W p_i` exactly, a
    /// tie to the earlier part, each part at most once; the sign put on at the end. O(n k).
    fn one_at_a_time(total: &BigInt, weights: &[BigUint]) -> Vec<BigInt> {
        let w: BigUint = weights.iter().sum();
        let t = total.magnitude();
        let mut ps: Vec<BigUint> = weights.iter().map(|wi| t * wi / &w).collect();
        let mut taken = vec![false; ps.len()];
        while ps.iter().sum::<BigUint>() < *t {
            let gap = |i: usize| BigInt::from(t * &weights[i]) - BigInt::from(&w * &ps[i]);
            let best = (0..ps.len())
                .filter(|&i| !taken[i])
                .fold(None::<usize>, |b, i| match b {
                    Some(j) if gap(j) >= gap(i) => Some(j),
                    _ => Some(i),
                })
                .expect("a part is left");
            ps[best] += 1u32;
            taken[best] = true;
        }
        ps.into_iter()
            .map(|p| BigInt::from_biguint(total.sign(), p))
            .collect()
    }

    /// [`allocate`] against [`one_at_a_time`] on random totals of 0 to 200 bits of both signs
    /// and 1 to 30 weights of 0 to 70 bits, a third of them zero; and on every draw the sum,
    /// each part between the floor and the ceiling of its share, zero weights getting zero,
    /// and the negated total giving the negated parts.
    #[test]
    fn allocations_agree_with_one_unit_at_a_time() {
        let mut rng = crate::seed::Rng::new(crate::seed::seed(
            "allocations_agree_with_one_unit_at_a_time",
        ));
        for _ in 0..1500 {
            let t = BigInt::from(wide(&mut rng, 0, 200));
            let t = if rng.below(2) == 0 { -t } else { t };
            let ws: Vec<BigUint> = (0..1 + rng.below(30))
                .map(|_| match rng.below(3) {
                    0 => BigUint::zero(),
                    _ => wide(&mut rng, 0, 70),
                })
                .collect();
            let w: BigUint = ws.iter().sum();
            let got = allocate(&t, &ws);
            if w.is_zero() {
                assert_eq!(got, None);
                continue;
            }
            let got = got.expect("weights");
            assert_eq!(got, one_at_a_time(&t, &ws), "{t} {ws:?}");
            assert_eq!(got.iter().sum::<BigInt>(), t);
            assert_eq!(allocate(&-&t, &ws), Some(got.iter().map(|p| -p).collect()));
            for (p, wi) in got.iter().zip(&ws) {
                let lo = t.magnitude() * wi / &w;
                let m = p.magnitude();
                assert!(*m == lo || *m == &lo + 1u32, "{p} {wi}");
                if wi.is_zero() {
                    assert!(p.is_zero());
                }
            }
        }
    }
}
