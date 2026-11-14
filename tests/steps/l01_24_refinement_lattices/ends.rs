//! Interval ends at and past the 64-bit range. An end is an unbounded integer, held in one
//! word while it fits in `i64`, so the arithmetic, the offsets and the hulls of the solver
//! are exact at every magnitude: an end past `i64` is neither rounded to infinity nor dropped.

use std::sync::Arc;

use num_bigint::BigInt;
use zedc::store::affine::{Affine, Bounds};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{Atom, Con, Formula, Lin, project};
use zedc::store::revision::{Op, backward, forward};

const MAX: i64 = i64::MAX;
const MIN: i64 = i64::MIN;

fn big(v: i128) -> End {
    End::Fin(Num::from(v))
}

fn point(v: i128) -> IntervalSet {
    IntervalSet::point(Num::from(v))
}

#[test]
fn the_ends_next_to_the_64_bit_range_are_exact() {
    // One past `i64::MAX` and one below `i64::MIN`, and back.
    let above = End::of(MAX).succ();
    let below = End::of(MIN).pred();
    assert_eq!(above, big(MAX as i128 + 1));
    assert_eq!(below, big(MIN as i128 - 1));
    assert_eq!(above.pred(), End::of(MAX));
    assert_eq!(below.succ(), End::of(MIN));
    assert_eq!(above.to_i64(), None);
    assert_eq!(above.pred().to_i64(), Some(MAX));
    // A value has one form: the same integer reached from a big one is equal to the word.
    assert_eq!(
        Num::from(BigInt::from(MAX) + 1 - 1),
        Num::from(MAX),
        "a big value back in range is a word"
    );
    // The order runs across the boundary.
    let ends = [
        End::NegInf,
        below.clone(),
        End::of(MIN),
        End::of(0),
        End::of(MAX),
        above.clone(),
        End::PosInf,
    ];
    assert!(ends.windows(2).all(|w| w[0] < w[1]), "{ends:?}");
    // A set holding both sides of each boundary prints each end exactly.
    let s = IntervalSet::range(below, End::of(MIN)).join(&IntervalSet::range(End::of(MAX), above));
    assert_eq!(
        s.to_string(),
        "[-9223372036854775809..=-9223372036854775808, \
         9223372036854775807..=9223372036854775808]"
    );
}

#[test]
fn sums_and_products_cross_the_boundary_in_both_directions() {
    let two32 = point(1 << 32);
    // Out of the range: `2^32 * 2^32` and `-2^32 * 2^32`, `MAX + 1` and `MIN - 1`.
    assert_eq!(forward(&Op::Mul, &two32, &two32), point(1 << 64));
    assert_eq!(forward(&Op::Mul, &two32.neg(), &two32), point(-(1 << 64)));
    let one = IntervalSet::single(1);
    assert_eq!(
        forward(&Op::Add, &IntervalSet::single(MAX), &one),
        point(MAX as i128 + 1)
    );
    assert_eq!(
        forward(&Op::Sub, &IntervalSet::single(MIN), &one),
        point(MIN as i128 - 1)
    );
    // Back into the range: `2^64 div 2^32`, `(MAX + 1) - 1`, and `-(MIN)` then its negation.
    assert_eq!(forward(&Op::Div, &point(1 << 64), &two32), two32);
    assert_eq!(
        forward(&Op::Sub, &point(MAX as i128 + 1), &one),
        IntervalSet::single(MAX)
    );
    let neg_min = forward(&Op::Neg, &IntervalSet::single(MIN), &IntervalSet::empty());
    assert_eq!(neg_min, point(-(MIN as i128)));
    assert_eq!(
        forward(&Op::Neg, &neg_min, &IntervalSet::empty()),
        IntervalSet::single(MIN)
    );
    // A range across the boundary: `[MAX - 1..=MAX] * [2..=3]` is `[2 MAX - 2..=3 MAX]`.
    let near = IntervalSet::of(MAX - 1, MAX);
    let product = forward(&Op::Mul, &near, &IntervalSet::of(2, 3));
    assert_eq!(
        product.bounds(),
        Some((&big(2 * (MAX as i128) - 2), &big(3 * MAX as i128)))
    );
    // `abs` of `MIN` is one past `MAX`.
    assert_eq!(
        forward(&Op::Abs, &IntervalSet::single(MIN), &IntervalSet::empty()),
        point(MAX as i128 + 1)
    );
}

#[test]
fn an_offset_past_the_range_moves_every_end_and_bound_exactly() {
    // `int[n + MAX..=MAX]` moved up by 5 and back: no bound is dropped on the way.
    let n = Affine::sym("n");
    let b = Bounds::range(Some(n.plus(MAX)), Some(Affine::constant(MAX)));
    let up = b.offset(5);
    assert_eq!(
        up.to_string(),
        "[n + 9223372036854775812..=9223372036854775812]"
    );
    assert_eq!(up.offset(-5), b);
    // The same below `i64::MIN`.
    let low = Bounds::range(Some(Affine::constant(MIN)), Some(n.plus(MIN)));
    let down = low.offset(-5);
    assert_eq!(
        down.to_string(),
        "[-9223372036854775813..=n - 9223372036854775813]"
    );
    assert_eq!(down.offset(5), low);
}

fn x() -> Atom {
    Atom::Sym(Arc::from("x"))
}

/// `a <= x <= b` as linear constraints.
fn between(a: &BigInt, b: &BigInt) -> Formula {
    let x = Lin::atom(x());
    Formula::and(vec![
        Formula::Con(Con::ge(&x, &Lin::constant(a.clone()))),
        Formula::Con(Con::ge(&Lin::constant(b.clone()), &x)),
    ])
}

#[test]
fn a_bound_of_2_to_the_200_is_kept_exactly() {
    let p = BigInt::from(1) << 200;
    // A closed range at 2^200, and its negation.
    let hull = project(&between(&p, &(&p + 3)), &x()).unwrap();
    assert_eq!(
        hull,
        IntervalSet::range(End::Fin(Num::from(&p)), End::Fin(Num::from(&p + 3)))
    );
    let (lo, hi) = (-(&p + BigInt::from(3)), -&p);
    let hull = project(&between(&lo, &hi), &x()).unwrap();
    assert_eq!(
        hull,
        IntervalSet::range(End::Fin(Num::from(&lo)), End::Fin(Num::from(&hi)))
    );
    // One side only: `x >= 2^200` is the ray from 2^200, not every integer.
    let ray = Formula::Con(Con::ge(&Lin::atom(x()), &Lin::constant(p.clone())));
    assert_eq!(
        project(&ray, &x()).unwrap(),
        IntervalSet::range(End::Fin(Num::from(&p)), End::PosInf)
    );
    // `2x == 2^200 + 1` has no integer point however far out it lies.
    let odd = Formula::Con(Con::eq(&Lin::atom(x()).times(2), &Lin::constant(&p + 1)));
    assert_eq!(project(&odd, &x()).unwrap(), IntervalSet::empty());
    // The interval arithmetic: `2^100 * 2^100`.
    let h = IntervalSet::point(Num::from(BigInt::from(1) << 100));
    assert_eq!(forward(&Op::Mul, &h, &h), IntervalSet::point(Num::from(&p)));
}

/// `n ^ k` as an end.
fn pow(n: i64, k: u32) -> Num {
    Num::from(n).pow(k)
}

fn hash_of(v: &Num) -> u64 {
    use std::hash::{BuildHasher, BuildHasherDefault};
    BuildHasherDefault::<std::collections::hash_map::DefaultHasher>::default().hash_one(v)
}

#[test]
fn the_bound_of_a_large_power_is_built_and_compared_without_its_digits() {
    // `x ^ 100000000` with x in 2..=3: 2^(10^8) ..= 3^(10^8), numbers of 10^8 and about
    // 1.6 * 10^8 bits, kept as powers so the check takes no time to write them out.
    let k = 100_000_000;
    zed_tests::without_digits("the bound of x^10^8", u64::from(k), || {
        let image = forward(
            &Op::Pow(k.into()),
            &IntervalSet::of(2, 3),
            &IntervalSet::of(2, 3),
        );
        assert_eq!(
            image,
            IntervalSet::range(End::Fin(pow(2, k)), End::Fin(pow(3, k)))
        );
        // The demand on x back from the image is 2..=3 again, and -3..=-2 for an even power.
        let back = backward(
            &Op::Pow(k.into()),
            0,
            &IntervalSet::top(),
            &IntervalSet::top(),
            &image,
        );
        assert_eq!(back, IntervalSet::of(-3, -2).join(&IntervalSet::of(2, 3)));
        // Exact order between powers of other bases: 3^(10^8) lies between 2^158496250 and
        // 2^158496251, since 10^8 * log2(3) = 158496250.07...
        let three = pow(3, k);
        assert!(pow(2, 158_496_250) < three && three < pow(2, 158_496_251));
        // The same value from other bases is equal, and hashes alike: 4^(5 * 10^7) = 2^(10^8).
        assert_eq!(pow(4, k / 2), pow(2, k));
        assert_eq!(hash_of(&pow(4, k / 2)), hash_of(&pow(2, k)));
        assert_eq!(pow(2, k).pow(3), pow(8, k));
        // A power of an odd exponent keeps the sign, and negation reverses the order.
        assert_eq!(Num::from(-2).pow(k + 1), -&pow(2, k + 1));
        assert!(-&three < -&pow(2, 158_496_250));
        assert!(-&three < Num::from(i64::MIN) && Num::from(i64::MAX) < three);
    });
}

#[test]
fn a_kept_power_equals_the_same_value_written_out() {
    // 2^200 written out and as a power: one value, one hash, one place in a set.
    let p = BigInt::from(1) << 200;
    assert_eq!(Num::from(&p), pow(2, 200));
    assert_eq!(hash_of(&Num::from(&p)), hash_of(&pow(2, 200)));
    assert_eq!(Num::from(-&p * 2), pow(-2, 201));
    assert_eq!(hash_of(&Num::from(-&p * 2)), hash_of(&pow(-2, 201)));
    assert!(Num::from(&p - 1) < pow(2, 200) && pow(2, 200) < Num::from(&p + 1));
    // Arithmetic on a power is exact.
    assert_eq!(&pow(2, 200) + &Num::ONE, Num::from(&p + 1));
    assert_eq!(pow(3, 300).floor_root(3), pow(3, 100));
    let (v, r) = (pow(3, 301), pow(3, 301).floor_root(3));
    assert!(r.pow(3) <= v && v < (&r + &Num::ONE).pow(3) && r > pow(3, 100));
    // Pieces that meet at a power merge: ..=2^200 - 1 and 2^200..
    let below = IntervalSet::range(End::of(0), End::Fin(Num::from(&p - 1)));
    let from = IntervalSet::range(End::Fin(pow(2, 200)), End::Fin(pow(3, 200)));
    assert_eq!(
        below.join(&from),
        IntervalSet::range(End::of(0), End::Fin(pow(3, 200)))
    );
    // A power just past i128 and its neighbors, and one that fits in i128 is not kept.
    assert_eq!(pow(2, 127).to_i128(), None);
    assert_eq!(pow(2, 126).to_i128(), Some(1 << 126));
    assert_eq!(pow(-2, 127).to_i128(), Some(i128::MIN));
    assert_eq!(
        pow(2, 127).to_string(),
        (BigInt::from(1) << 127u32).to_string()
    );
}

#[test]
fn kept_powers_order_and_hash_as_their_values_written_out() {
    // Powers of bases in -40..=40, many sharing a root (4, 8, 16, 27, ...), with exponents
    // up to 300, against the same values written out and against neighbors one apart.
    let mut rng = zed_tests::instances::Rng::new(29);
    let values: Vec<(Num, BigInt)> = (0..400)
        .map(|_| {
            let (b, k) = (rng.int(-40, 40), rng.int(0, 300) as u32);
            let exact = BigInt::from(b).pow(k);
            let near = rng.int(-1, 1);
            if near == 0 {
                (pow(b, k), exact)
            } else {
                (Num::from(&exact + near), exact + near)
            }
        })
        .collect();
    for (a, x) in &values {
        assert_eq!(*a, Num::from(x), "{x}");
        assert_eq!(hash_of(a), hash_of(&Num::from(x)), "{x}");
        assert_eq!(a.to_string(), x.to_string());
        for (b, y) in &values {
            assert_eq!(a.cmp(b), x.cmp(y), "{x} against {y}");
            assert_eq!(a == b, x == y, "{x} against {y}");
            let adjacent = End::Fin(a.clone()).at_most_succ(&End::Fin(b.clone()));
            assert_eq!(adjacent, *x <= y + 1, "{x} at most one past {y}");
        }
    }
}

/// Values in kept forms with the same values written out: `(c * b ^ k + d) div n` for each
/// base sharing roots, with exponents past i128 and every pairing of a coefficient and an
/// addend in or past i64; square and cube roots of powers that are kept as roots, exact and
/// not, and sums, products and powers of them; sums and products of powers of different
/// integers, and powers of sums; and neighbors one apart.
fn kept_values(rng: &mut zed_tests::instances::Rng) -> Vec<(Num, BigInt)> {
    use num_integer::Integer;
    let mut values = Vec::new();
    for (i, b) in [2, 3, 4, 6, -3, 8].into_iter().enumerate() {
        let k = rng.int(128, 200) as u32;
        // The coefficient lies past i64 for even `i` and the addend for `i` a multiple of 3,
        // so both, either and neither appear.
        let c =
            BigInt::from(rng.pick(&[-7, -2, -1, 1, 2, 3, 12, 50])) << (70 * u32::from(i % 2 == 0));
        let d = BigInt::from(rng.int(-1000, 1000)) << (90 * u32::from(i % 3 == 0));
        let n = BigInt::from(rng.int(1, 30));
        let v = &(&(&pow(b, k) * &Num::from(&c)) + &Num::from(&d));
        let exact = BigInt::from(b).pow(k) * &c + &d;
        values.push((v.div_floor(&Num::from(&n)), exact.div_floor(&n)));
    }
    for (b, r, whole) in [(4, 2, true), (2, 2, false), (3, 3, true), (2, 3, false)] {
        // Roots past 2^127: kept as roots of powers, exact when `r` divides `k`.
        let k = rng.int(390, 420) as u32;
        let k = k - k % r + u32::from(!whole);
        let root = pow(b, k).floor_root(r);
        let exact = BigInt::from(b).pow(k).nth_root(r);
        let c = BigInt::from(rng.pick(&[-3, -1, 1, 2]));
        let d = BigInt::from(rng.int(-5, 5));
        values.push((root.clone(), exact.clone()));
        values.push((&(&root * &Num::from(&c)) + &Num::from(&d), &exact * &c + &d));
        values.push((root.pow(r), exact.pow(r)));
        values.push((pow(b, k).ceil_root(r), {
            let up = BigInt::from(b).pow(k);
            if exact.pow(r) == up { exact } else { exact + 1 }
        }));
    }
    for (b1, b2) in [(2, 3), (5, -2), (-3, 10)] {
        // Sums and products of powers of different integers, and powers of sums.
        let (k1, k2) = (rng.int(128, 200) as u32, rng.int(128, 200) as u32);
        let c = BigInt::from(rng.pick(&[-5, -1, 1, 4]));
        let d = BigInt::from(rng.int(-50, 50));
        let (p1, p2) = (pow(b1, k1), pow(b2, k2));
        let (x1, x2) = (BigInt::from(b1).pow(k1), BigInt::from(b2).pow(k2));
        let sum = &(&p1 + &(&p2 * &Num::from(&c))) + &Num::from(&d);
        let exact = &x1 + &x2 * &c + &d;
        values.push((&sum * &Num::from(3), &exact * 3));
        values.push((&p1 * &p2, &x1 * &x2));
        values.push((sum.pow(2), exact.pow(2)));
    }
    let near: Vec<(Num, BigInt)> = values
        .iter()
        .step_by(4)
        .flat_map(|(v, x)| [-1, 1].map(|s| (v + &Num::from(s), x + s)))
        .collect();
    values.extend(near);
    values
}

/// TEST-bench-move-l0123, author P169: this ran 192 values (40 of the first kind with random
/// bases, 16 random root groups, 8 random sum groups, and the neighbors of every fourth) with
/// `Rng::new(31)`, the roots of index 2 to 5 of each, and the arithmetic over every pair: 18 s
/// alone at load 38, nine tenths of it in the products, sums and differences of the pairs. It
/// now runs each base, each pairing of coefficient and addend forms, each root kind and three
/// sum pairs once, 47 values with a fresh seed; the square root and one index of 3 to 5 drawn
/// for each value; the order over every pair; and the arithmetic of each value with itself
/// and with five others drawn at random.
#[test]
fn kept_forms_compute_as_their_values_written_out() {
    use num_integer::Integer;
    use num_traits::{Signed, Zero};
    let (mut rng, seed) = zed_tests::instances::Rng::fresh("kept forms");
    let at = format!("ZED_TEST_SEED={seed}");
    let values = kept_values(&mut rng);
    for (i, (a, x)) in values.iter().enumerate() {
        assert_eq!(*a, Num::from(x), "{x}, {at}");
        assert_eq!(hash_of(a), hash_of(&Num::from(x)), "{x}, {at}");
        assert_eq!(a.to_string(), x.to_string(), "{at}");
        assert_eq!(-a, Num::from(-x), "-{x}, {at}");
        assert_eq!(a.pow(3), Num::from(x.pow(3)), "{x}^3, {at}");
        for r in [2, rng.int(3, 5) as u32] {
            let m = x.abs();
            let (lo, hi) = (a.abs().floor_root(r), a.abs().ceil_root(r));
            let f = m.nth_root(r);
            let c = if f.pow(r) == m { f.clone() } else { &f + 1 };
            assert_eq!(
                (lo, hi),
                (Num::from(&f), Num::from(&c)),
                "roots {r} of {m}, {at}"
            );
        }
        for s in [1i64, -1, 2, 3, -7, 1000, 1 << 40, -(1 << 62)] {
            let (n, y) = (Num::from(s), BigInt::from(s));
            assert_eq!(
                a.div_floor(&n),
                Num::from(x.div_floor(&y)),
                "{x} div {s}, {at}"
            );
            assert_eq!(
                a.mod_floor(&n),
                Num::from(x.mod_floor(&y)),
                "{x} mod {s}, {at}"
            );
            assert_eq!(a.gcd(&n), Num::from(x.gcd(&y)), "gcd {x} {s}, {at}");
            assert_eq!(n.gcd(a), Num::from(x.gcd(&y)), "gcd {s} {x}, {at}");
            assert_eq!(&n * a, Num::from(&y * x), "{s} * {x}, {at}");
        }
        for (b, y) in &values {
            assert_eq!(a.cmp(b), x.cmp(y), "{x} against {y}, {at}");
            assert_eq!(a == b, x == y, "{x} against {y}, {at}");
            assert_eq!(
                a.at_most_succ(b),
                *x <= y + 1,
                "{x} at most one past {y}, {at}"
            );
        }
        let others = std::iter::once(i).chain((0..5).map(|_| rng.below(values.len())));
        for (b, y) in others.map(|j| &values[j]) {
            assert_eq!(a + b, Num::from(x + y), "{x} + {y}, {at}");
            assert_eq!(a - b, Num::from(x - y), "{x} - {y}, {at}");
            assert_eq!(a * b, Num::from(x * y), "{x} * {y}, {at}");
            if !y.is_zero() {
                assert_eq!(
                    a.div_floor(b),
                    Num::from(x.div_floor(y)),
                    "{x} div {y}, {at}"
                );
                assert_eq!(
                    a.mod_floor(b),
                    Num::from(x.mod_floor(y)),
                    "{x} mod {y}, {at}"
                );
            }
            assert_eq!(a.gcd(b), Num::from(x.gcd(y)), "gcd {x} {y}, {at}");
        }
    }
}

#[test]
fn arithmetic_and_roots_on_a_large_power_keep_its_form() {
    // `x ^ k + 1`, `k * x ^ k` and `x ^ k - 1` for x in 2..=3 and k = 10^8, and the cube
    // root of 2^k: kept forms, so each takes no time to write out its 10^8 bits.
    let k = 100_000_000;
    // The smallest value the test keeps is the fourth root of 2^k, of k / 4 + 1 bits.
    zed_tests::without_digits("arithmetic on 2^(10^8)", u64::from(k / 4), || {
        let x = IntervalSet::of(2, 3);
        let image = forward(&Op::Pow(k.into()), &x, &x);
        let one = IntervalSet::single(1);
        let (lo, hi) = (pow(2, k), pow(3, k));
        let plus = forward(&Op::Add, &image, &one);
        let range = |a: Num, b: Num| IntervalSet::range(End::Fin(a), End::Fin(b));
        assert_eq!(plus, range(&lo + &Num::ONE, &hi + &Num::ONE));
        assert_eq!(
            forward(&Op::Sub, &image, &one),
            range(&lo - &Num::ONE, &hi - &Num::ONE)
        );
        let times = forward(&Op::Mul, &IntervalSet::single(i64::from(k)), &image);
        assert_eq!(
            times,
            range(
                &lo * &Num::from(i64::from(k)),
                &hi * &Num::from(i64::from(k))
            )
        );
        // Exact order and residues: 2^k < 2^k + 1 < 2^k + 2; 2^k + 1 = 2 mod 3 for k even, and
        // 2^k - 1 is a multiple of 3 and 5 for k a multiple of 4.
        let next = &lo + &Num::ONE;
        assert!(lo < next && next < &lo + &Num::from(2) && next < hi);
        assert!(next.at_most_succ(&lo) && !(&next + &Num::ONE).at_most_succ(&lo));
        assert_eq!(next.mod_floor(&Num::from(3)), Num::from(2));
        assert_eq!((&lo - &Num::ONE).gcd(&Num::from(15)), Num::from(15));
        assert_eq!((&lo * &Num::from(3)).div_floor(&Num::from(3)), lo);
        assert_eq!(Num::from(5).div_floor(&next), Num::ZERO);
        assert_eq!(Num::from(-5).div_floor(&next), Num::from(-1));
        // The cube root of 2^k: k = 10^8 is not a multiple of 3, so the root is irrational and
        // its ceiling is one past its floor; its cube is below 2^k and lies past 2^(k - 1).
        let root = lo.floor_root(3);
        assert!(pow(2, k / 3) < root && root < pow(2, k / 3 + 1));
        assert_eq!(lo.ceil_root(3), &root + &Num::ONE);
        let cube = root.pow(3);
        assert!(cube < lo && pow(2, k - 1) < cube);
        // A root of an exact power is exact: the fourth root of 2^k is 2^(k / 4).
        assert_eq!(lo.floor_root(4), pow(2, k / 4));
        assert_eq!(lo.ceil_root(4), pow(2, k / 4));
    });
}

#[test]
fn sums_of_unrelated_large_powers_keep_their_form() {
    // Sums, differences and products of powers of different integers at k = 10^8: each is a
    // linear combination of kept cores, so none writes out a value of 10^8 bits.
    use num_bigint::BigUint;
    let k = 100_000_000u32;
    zed_tests::without_digits("sums of powers of 3 and 5 to 10^8", u64::from(k), || {
        let (three, five) = (pow(3, k), pow(5, k));
        let s = &three + &five;
        assert!(five < s && s < &five * &Num::from(2));
        assert_eq!(&s - &five, three);
        assert_eq!(&s - &three, five);
        assert!(&five - &three > Num::ZERO && &three - &five < Num::ZERO);
        assert!(&pow(2, k) + &five < s && s < &pow(4, k) + &five);
        // 3^(k + 1) - 3^k = 2 * 3^k: the powers of 3 fold, so the difference is exact.
        let d = &pow(3, k + 1) - &three;
        assert_eq!(d, &three * &Num::from(2));
        assert!((&d - &(&three * &Num::from(2))).is_zero());
        assert!((&(&pow(3, k + 1) - &three) - &(&three + &three)).is_zero());
        // Residues and division by small values come from the residues of each power.
        let m = BigUint::from(1_000_003u32);
        let r = (BigUint::from(3u32).modpow(&BigUint::from(k), &m)
            + BigUint::from(5u32).modpow(&BigUint::from(k), &m))
            % &m;
        assert_eq!(
            s.mod_floor(&Num::from(1_000_003)),
            Num::from(BigInt::from(r))
        );
        assert_eq!(s.gcd(&Num::from(2)), Num::from(2));
        let seven = Num::from(7);
        assert_eq!(&(&s.div_floor(&seven) * &seven) + &s.mod_floor(&seven), s);
        // A product of powers of different integers, and a power of a sum.
        let p = &pow(3, k) * &pow(5, k - 1);
        assert!(pow(15, k - 1) < p && p < pow(15, k));
        let two = pow(2, k);
        let cube = (&two + &Num::ONE).pow(3);
        let expanded = &(&(&pow(2, 3 * k) + &(&pow(2, 2 * k) * &Num::from(3)))
            + &(&two * &Num::from(3)))
            + &Num::ONE;
        assert_eq!(cube, expanded);
        assert!((&cube - &expanded).is_zero());
        // The square root of the sum is kept; its square lies at most at the sum, and the sum is
        // not a perfect square (it is 2 mod 4), so the ceiling is one past the floor.
        let root = s.floor_root(2);
        assert!(root.pow(2) <= s && pow(2, k) < root && root < pow(6, k / 2));
        assert_eq!(s.ceil_root(2), &root + &Num::ONE);
    });
}

#[test]
fn kept_values_with_no_kept_form_are_written_out() {
    // The cases the kept forms leave to the written-out value, at exponents of a few hundred so
    // that the digits are cheap: each answer must still be exact.
    use num_integer::Integer;
    let e = 300u32;
    let big = |b: i64, k: u32| BigInt::from(b).pow(k);
    // Equal cores in forms that are not related: 6^e and 2^e * 3^e, 2^e * 4^f and 2^(e + 2f),
    // 3 * 9^e and 3^(2e + 1).
    let six = pow(6, e);
    let two_three = &pow(2, e) * &pow(3, e);
    assert_eq!(six, two_three);
    assert!((&six - &two_three).is_zero());
    assert_eq!(&pow(2, e) * &pow(4, e + 1), pow(2, 3 * e + 2));
    let nine = &pow(9, e) * &Num::from(3);
    assert!((&nine - &pow(3, 2 * e + 1)).is_zero());
    assert_eq!(&(&nine + &Num::ONE) - &pow(3, 2 * e + 1), Num::ONE);
    // Terms over products of powers of several integers that cancel only by a carry between
    // them: 2^(e + 1) * 5^e + 1 - 2 * 10^e = 1.
    let carried = &(&pow(2, e + 1) * &pow(5, e)) + &Num::ONE;
    assert_eq!(&carried - &(&pow(10, e) * &Num::from(2)), Num::ONE);
    // Two floor roots of different radicands with one value: 2^(3e + 1) + 1 is no cube.
    let (r1, r2) = (
        pow(2, 3 * e + 1).floor_root(3),
        (&pow(2, 3 * e + 1) + &Num::ONE).floor_root(3),
    );
    assert_eq!(r1, r2);
    assert!((&r1 - &r2).is_zero());
    assert_eq!(r1, Num::from(big(2, 3 * e + 1).nth_root(3)));
    // Division, remainder and gcd of a kept value by a kept value.
    let a = &pow(3, e) + &pow(5, e - 20);
    let b = &pow(2, e) + &Num::from(7);
    let (x, y) = (big(3, e) + big(5, e - 20), big(2, e) + 7);
    assert_eq!(a.div_floor(&b), Num::from(x.div_floor(&y)));
    assert_eq!(a.mod_floor(&b), Num::from(x.mod_floor(&y)));
    assert_eq!(a.gcd(&b), Num::from(x.gcd(&y)));
    assert_eq!(pow(6, e).gcd(&pow(4, e)), Num::from(big(2, e)));
    // Roots of values that hold a root, and the ceiling root of a perfect power read as a sum.
    let root = pow(3, 3 * e + 1).floor_root(3);
    let r = big(3, 3 * e + 1).nth_root(3);
    let shifted = &(&root * &Num::from(5)) + &Num::from(2);
    let z: BigInt = &r * 5 + 2;
    assert_eq!(shifted.floor_root(2), Num::from(z.sqrt()));
    assert_eq!(shifted.ceil_root(2), Num::from(z.sqrt() + 1));
    assert_eq!(root.ceil_root(2), Num::from(r.sqrt() + 1));
    let square = (&pow(2, e) + &Num::ONE).pow(2);
    assert_eq!(square.ceil_root(2), &pow(2, e) + &Num::ONE);
    assert_eq!(
        (&square + &Num::ONE).ceil_root(2),
        &pow(2, e) + &Num::from(2)
    );
    // Hashing: a value inside i128 hashes as itself, whatever its form.
    let edge = Num::from(BigInt::from(i64::MAX) + 5);
    assert_eq!(hash_of(&edge), hash_of(&Num::from(i64::MAX as i128 + 5)));
}

/// `3 ^ e * 9 ^ (e + 1) - 3 ^ (3 * e + 2)`, which is zero, with the same value in other
/// forms: each a sum or product of powers of integers that share factors.
fn equal_cores(e: u32) {
    // 3^e * 9^(e + 1) = 3^(3e + 2): 9 is kept as 3^2, so the product is one power of 3 and the
    // difference cancels with no digits written out.
    let product = &pow(3, e) * &pow(9, e + 1);
    assert_eq!(product, pow(3, 3 * e + 2));
    assert!((&product - &pow(3, 3 * e + 2)).is_zero());
    // 3 * 9^e + 1 - 3^(2e + 1) = 1: the powers of 3 and of 9 fold as powers of one integer.
    let nine = &(&pow(9, e) * &Num::from(3)) + &Num::ONE;
    assert_eq!(&nine - &pow(3, 2 * e + 1), Num::ONE);
    // 6^e * 5^(e + 1) against 2^e * (3^e * 5^(e + 1)): cores over 6 and over 2 and 3, equal
    // over the coprime base 2, 3, 5 of their integers.
    let six = &pow(6, e) * &pow(5, e + 1);
    let apart = &pow(2, e) * &(&pow(3, e) * &pow(5, e + 1));
    assert_eq!(six, apart);
    assert!((&six - &apart).is_zero());
    assert_eq!(&(&six + &Num::from(7)) - &apart, Num::from(7));
    // 12^e against 4^e * 3^e (one power of 12) and against 2^(2e) * 3^e, and 8^e against 4^f
    // with 3e = 2f.
    let twelve = pow(12, e);
    assert_eq!(twelve, &pow(4, e) * &pow(3, e));
    assert_eq!(twelve, &pow(2, 2 * e) * &pow(3, e));
    assert_eq!(pow(8, 2 * e), pow(4, 3 * e));
    // Unequal cores close in value stay apart: 2^e * 3^(e + 1) is 3/2 of 6^e * 2.
    assert!(&pow(6, e) * &Num::from(2) < &pow(2, e) * &pow(3, e + 1));
}

#[test]
fn equal_cores_over_bases_that_share_factors_cancel_without_their_digits() {
    for e in [1_000_000, 8_000_000] {
        zed_tests::without_digits(&format!("equal cores at e = {e}"), u64::from(e), || {
            equal_cores(e)
        });
    }
    // The same at an exponent small enough to check against the values written out.
    equal_cores(300);
}

/// The negative control of [`zed_tests::without_digits`]: the product of
/// `equal_cores_over_bases_that_share_factors_cancel_without_their_digits` with its powers
/// written out, `3^e * 9^(e + 1)` at e = 10^6 (about 4.8 * 10^6 bits), fails the bound the kept
/// forms meet.
#[test]
fn a_power_written_out_fails_the_bound_on_bytes() {
    let e = 1_000_000u32;
    let written = std::panic::catch_unwind(|| {
        zed_tests::without_digits("3^e * 9^(e + 1) written out", u64::from(e), || {
            Num::from(BigInt::from(3).pow(e) * BigInt::from(9).pow(e + 1))
        })
    });
    assert!(written.is_err(), "the digits of 3^(3e + 2) met the bound");
}

#[test]
fn equal_values_in_different_forms_hash_alike() {
    let e = 300u32;
    let big = |b: i64, k: u32| BigInt::from(b).pow(k);
    let pairs: Vec<(Num, Num)> = vec![
        // A big value and a kept root of the same value.
        (
            pow(3, 3 * e + 1).floor_root(3),
            Num::from(big(3, 3 * e + 1).nth_root(3)),
        ),
        (
            -&pow(3, 3 * e + 1).floor_root(3),
            Num::from(-big(3, 3 * e + 1).nth_root(3)),
        ),
        // Kept sums and products against the value written out.
        (&pow(2, 200) + &Num::ONE, Num::from(big(2, 200) + 1)),
        (&pow(3, e) * &pow(5, e), Num::from(big(15, e))),
        (-&pow(7, e), Num::from(-big(7, e))),
        // Kept forms of one value over different bases.
        (pow(6, e), &pow(2, e) * &pow(3, e)),
        (&pow(9, e) * &Num::from(3), pow(3, 2 * e + 1)),
        // The negation of the kept value 2^127 is i128::MIN, inside i128: a big value.
        (-&pow(2, 127), Num::from(-(BigInt::from(1) << 127u32))),
        // Kept forms whose value comes back inside i128, against the small value.
        (&(&pow(2, 200) + &Num::from(5)) - &pow(2, 200), Num::from(5)),
        (
            &(&pow(3, e) - &Num::from(i64::MAX)) - &pow(3, e),
            Num::from(-i64::MAX),
        ),
        (
            &(&pow(3, e) + &Num::from(BigInt::from(1) << 100)) - &pow(3, e),
            Num::from(BigInt::from(1) << 100),
        ),
    ];
    assert_eq!((-&pow(2, 127)).to_i128(), Some(i128::MIN));
    for (a, b) in &pairs {
        assert_eq!(a, b, "{a} against {b}");
        assert_eq!(hash_of(a), hash_of(b), "{a} against {b}");
    }
    // Every pair hashes alike within a hash set: a value in one form finds the other.
    let set: std::collections::HashSet<Num> = pairs.iter().map(|(a, _)| a.clone()).collect();
    for (_, b) in &pairs {
        assert!(set.contains(b), "{b}");
    }
}

#[test]
fn a_wide_end_is_kept_as_a_power_of_its_least_root() {
    let n = 4096;
    let end: BigInt = (BigInt::from(1) << n) + 3;
    // 2^n + 3 is no perfect power: its cube is the cube written out, and the bound of x ^ 3
    // up to it.
    let cube = Num::from(end.clone()).pow(3);
    assert_eq!(cube, Num::from(end.pow(3)));
    let x = IntervalSet::range(End::Fin(Num::ZERO), End::Fin(Num::from(end.clone())));
    let image = forward(&Op::Pow(3u32.into()), &x, &x);
    assert_eq!(image.bounds().map(|(_, hi)| hi), Some(&End::Fin(cube)));
    // An end that is a perfect power of an odd, an even and a mixed base, to prime and to
    // composite indices: its powers fold with those of the least root, and its neighbor does
    // not.
    let mersenne: BigInt = (BigInt::from(1) << 127u32) - 1;
    for r in [mersenne.clone(), &mersenne << 5, &mersenne * 6] {
        for m in [3u32, 7, 12, 97] {
            let wide = Num::from(r.pow(m));
            let e = 1_000_000;
            let root_power = Num::from(r.clone()).pow(m * e);
            assert!((&wide.pow(e) - &root_power).is_zero(), "{r}^{m}");
            let near = Num::from(r.pow(m) + BigInt::from(1)).pow(3);
            assert_eq!(near, Num::from((r.pow(m) + BigInt::from(1)).pow(3)));
        }
    }
}
