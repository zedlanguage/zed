//! The tests of DESIGN step L1.17b (sec:domains, "Kept powers"; plan row KEPT-power-form) that
//! the kernel's exact numbers answer: equality by exponents with equal hashes, order with no
//! build, the corner cases of the paragraph and the `f64` corner cases. Each allocation bound is
//! measured on this thread with `zed_alloc_count::live`.

use num_bigint::BigInt;
use zed_kernel::Rat;
use zed_kernel::num::LiteralRounding;

fn int(n: i64) -> Rat {
    Rat::int(BigInt::from(n))
}

/// `b ^ e` for an `e` of one word.
fn pow(b: i64, e: u64) -> Rat {
    int(b).pow(&e.into()).expect("a kept power is not built")
}

/// `b ^ e` for an `e` of either sign, as Zed's `^` on a `rat` takes it.
fn pow_int(b: &Rat, e: &Rat) -> Option<Rat> {
    b.pow_int(e).expect("a kept power is not built")
}

const K: u64 = 1 << 40;

#[test]
fn equal_products_of_powers_are_equal_and_hash_alike() {
    let (six, two_three) = zed_alloc_count::live(|| {
        let six = pow(6, K);
        let two_three = pow(2, K).mul(&pow(3, K)).expect("kept");
        (six, two_three)
    })
    .0;
    assert!(six == two_three);
    assert_eq!(six.residues(), two_three.residues());
    let b = int(2).pow(&64u32.into()).unwrap().add(&int(13)).unwrap();
    let square = b.pow(&2u32.into()).unwrap();
    let product = b.mul(&b).unwrap();
    assert!(square == product);
    assert_eq!(square.residues(), product.residues());
}

/// An integer prints alike whichever way it was built (sec:diagnostics, "Types in a message";
/// plan row KEPT-power-form-print): `Rat::integer_text` reduces the coefficient with methods
/// of proved cost, so `4294967296 * 4294967296`, held as digits, prints `2^64`, as `2 ^ 64` and
/// the literal do. Arithmetic factors nothing: the product keeps its digits.
#[test]
fn an_integer_prints_alike_however_it_was_built() {
    let w = int(1 << 32);
    let square = w.mul(&w).unwrap();
    let literal = Rat::int("18446744073709551616".parse::<BigInt>().unwrap());
    // Negative control: the product is held as digits, no prime moved into its powers.
    assert!(square.kept().2.is_empty(), "{:?}", square.kept());
    assert!(!pow(2, 64).kept().2.is_empty());
    for built in [&square, &pow(2, 64), &literal] {
        assert!(*built == pow(2, 64));
        assert_eq!(built.integer_text(), "2^64");
    }
    // The sign stays on the numerator; `-6 * 2^62` is `-(3 * 2^63)`.
    let neg = int(-6).mul(&int(1 << 62)).unwrap();
    assert_eq!(neg.integer_text(), "-3*2^63");
    // A power of a wide odd base that is a prime word: `(2^61 - 1)^3`, by the least root.
    let m61 = (1i64 << 61) - 1;
    let cube = int(m61).mul(&int(m61)).unwrap().mul(&int(m61)).unwrap();
    assert_eq!(cube.integer_text(), "2305843009213693951^3");
    assert_eq!(pow(m61, 3).integer_text(), cube.integer_text());
    // A word that is the product of two primes above 2^31 has no prime that a method of proved
    // cost finds: it prints its digits.
    let (p, q) = (2147483659u64, 2147483693u64);
    assert!(zed_numtheory::is_prime(p) && zed_numtheory::is_prime(q));
    let hard = Rat::int(BigInt::from(p))
        .mul(&Rat::int(BigInt::from(q)))
        .unwrap();
    assert_eq!(hard.integer_text(), (p as u128 * q as u128).to_string());
    // 0, 1 and -1 print as they are; a word prints its digits where they are shorter, and the
    // power where it is, as the kept power does.
    assert_eq!(int(0).integer_text(), "0");
    assert_eq!(int(1).integer_text(), "1");
    assert_eq!(int(-1).integer_text(), "-1");
    assert_eq!(int(1000).integer_text(), "1000");
    assert_eq!(int(1 << 40).integer_text(), "2^40");
    assert_eq!(pow(2, 40).integer_text(), "2^40");
}

/// The text is a function of the value alone (plan row KEPT-print-value-canonical): `q * 3^50`,
/// `q` a prime above 2^44, prints `q*3^50` whether `3^50` is kept beside `q` or the product is
/// held as digits. On origin/main 80c93acf5 the digits printed as digits. `q` is the prime word
/// `2^61 - 1` and the wider prime `2^89 - 1`.
#[test]
fn a_wide_prime_times_a_power_prints_one_text_however_held() {
    let m89 = (BigInt::from(1) << 89u32) - 1;
    for (q, text) in [
        (BigInt::from((1i64 << 61) - 1), "2305843009213693951*3^50"),
        (m89, "618970019642690137449562111*3^50"),
    ] {
        let held = Rat::int(q.clone()).mul(&pow(3, 50)).unwrap();
        let digits = Rat::int(q * BigInt::from(3).pow(50u32));
        // Negative control: one is held with `3^50`, the other as digits only.
        assert_eq!(held.kept().2.len(), 1, "{:?}", held.kept());
        assert!(digits.kept().2.is_empty(), "{:?}", digits.kept());
        assert!(held == digits);
        assert_eq!(held.integer_text(), text);
        assert_eq!(digits.integer_text(), text);
    }
}

/// One value, `w * 3^50 * 1009^6 * 65537^4 * (2^61 - 1)^2` for each coefficient `w` of 1, a
/// prime word above 2^44 and the prime `2^89 - 1`, held with each of the 16 sets of those primes
/// listed and the rest in the coefficient, prints one text (plan row KEPT-print-value-canonical).
/// On origin/main 80c93acf5 the holds printed different texts.
#[test]
fn every_hold_of_one_value_prints_one_text() {
    let m61 = (1u64 << 61) - 1;
    let primes = [(3u64, 50u32), (1009, 6), (65537, 4), (m61, 2)];
    let q = zed_numtheory::next_prime(1 << 44).expect("a prime word above 2^44");
    let wide = (BigInt::from(1) << 89u32) - 1;
    for w in [BigInt::from(1), BigInt::from(q), wide] {
        let mut texts = Vec::new();
        for mask in 0..16u32 {
            let mut num = w.clone();
            let mut pows = Vec::new();
            for (i, &(p, e)) in primes.iter().enumerate() {
                match mask >> i & 1 == 1 {
                    true => pows.push((p, BigInt::from(e))),
                    false => num *= BigInt::from(p).pow(e),
                }
            }
            let held = Rat::from_kept(num, BigInt::from(1), pows).expect("a normal form");
            texts.push(held.integer_text());
        }
        assert!(texts.iter().all(|t| *t == texts[0]), "{w}: {texts:?}");
    }
}

#[test]
fn powers_far_apart_order_with_no_build() {
    let ((lt, gt), live) = zed_alloc_count::live(|| {
        let (a, b) = (pow(3, K), pow(2, 2 * K));
        (a < b, b > a)
    });
    assert!(lt && gt);
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    // `x < 3 ^ (2 ^ 40)` for `x` of 64 bits.
    let x = int(i64::MAX);
    let (lt, live) = zed_alloc_count::live(|| x < pow(3, K));
    assert!(lt);
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
}

/// `c * 3^e` and `(c + 1) * 3^e`, either side of `2^f`, with `three` = `3^e` built, `f` its bits
/// less 1 plus `k` and `c = floor(2^f / 3^e)`, of `k` bits: `3^e` does not divide `2^f`, so
/// `c 3^e < 2^f < (c + 1) 3^e`, and each side agrees with `2^f` to within `3^e / 2^f < 2^(1 - k)`
/// of it, so the order reads bounds of about `k` bits (DESIGN step L1.17b: the order measured at
/// 2^6 to 2^20 bits of precision). `k` is at least 2.
pub(super) fn close_pair(three: &BigInt, e: u64, k: u64) -> (Rat, Rat, Rat) {
    let f = three.bits() - 1 + k;
    let c = (BigInt::from(1) << f) / three;
    let kept = pow(3, e);
    let lo = Rat::int(c.clone()).mul(&kept).expect("nothing is built");
    let hi = Rat::int(c + 1).mul(&kept).expect("nothing is built");
    (lo, hi, pow(2, f))
}

/// [`close_pair`] at small sizes against the built numbers, at precisions from 2 bits to past
/// the width of `3^e`.
#[test]
fn close_products_order_as_the_built_numbers() {
    for e in [1u64, 2, 40, 1000] {
        let three = BigInt::from(3).pow(u32::try_from(e).expect("small"));
        for k in [2u64, 3, 63, 64, 65, 1000, 4096] {
            let (lo, hi, two) = close_pair(&three, e, k);
            let built = |x: &Rat| x.to_integer().expect("small");
            let (l, h, t) = (built(&lo), built(&hi), built(&two));
            assert!(l < t && t < h, "e {e}, k {k}");
            assert!(lo < two && two < hi && lo < hi, "e {e}, k {k}");
            assert!(two > lo && hi > two, "e {e}, k {k}");
        }
    }
}

#[test]
fn corner_cases_of_the_kept_power_paragraph() {
    // `0 ^ 0` is 1, as an int and as a rat.
    assert!(pow(0, 0) == int(1));
    assert!(pow_int(&int(0), &int(0)).expect("0^0 is defined") == int(1));
    // A negative base by the parity of its exponent, with no build.
    let (signs, live) = zed_alloc_count::live(|| {
        let even = pow(-3, K);
        let odd = pow(-3, K + 1);
        (
            even.is_negative(),
            odd.is_negative(),
            even > int(0),
            odd < int(0),
        )
    });
    assert_eq!(signs, (false, true, true, true));
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    // `2r ^ -(2 ^ 40)`, kept: below 1 and above 0.
    let tiny = pow_int(&int(2), &int(-(K as i64))).expect("2 is not zero");
    assert!(tiny > int(0) && tiny < int(1));
    assert!(tiny == int(1).div(&pow(2, K)).unwrap().expect("not zero"));
    // `0r ^ -1` has no value: Zed's `#divByZero`.
    assert!(pow_int(&int(0), &int(-1)).is_none());
}

#[test]
fn floats_of_kept_powers_round_once() {
    // `2^1024 - 2^970` is the tie above the largest `f64`: it rounds to even, an infinity.
    let top = pow(2, 1024).sub(&pow(2, 970)).unwrap();
    assert_eq!(top.to_f64(), Err(LiteralRounding::Infinite));
    // One below it rounds down to the largest finite `f64`.
    assert_eq!(top.sub(&int(1)).unwrap().to_f64(), Ok(f64::MAX));
    // `2^-1075`, half the least subnormal, a tie, rounds to the even zero.
    let half = pow_int(&int(2), &int(-1075)).unwrap();
    assert_eq!(half.to_f64(), Err(LiteralRounding::Zero));
    // A little above that half rounds up to the least subnormal.
    let above = half.add(&pow_int(&int(2), &int(-1200)).unwrap()).unwrap();
    assert_eq!(above.to_f64(), Ok(f64::from_bits(1)));
}
