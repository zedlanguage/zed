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

/// `(2^64 + 13)^(2^64)` is the atom `2^64 + 13` with the exponent `2^64` (DESIGN.md sec:domains
/// "Kept powers"), and a product, a quotient and an order of such powers build nothing: each
/// allocates under 1 KiB (DESIGN step L1.17b).
#[test]
fn a_wide_power_allocates_under_a_kibibyte() {
    let b = int(2).pow(&64u32.into()).unwrap().add(&int(13)).unwrap();
    let e = num_bigint::BigUint::from(1u32) << 64u32;
    let (p, live) = zed_alloc_count::live(|| b.pow(&e).expect("a kept power is not built"));
    assert!(live.peak < 1 << 10, "peak heap {} bytes", live.peak);
    assert_eq!(p.wide().len(), 1);
    let (square, product) = zed_alloc_count::live(|| p.mul(&p).expect("kept"));
    let (back, quotient) = zed_alloc_count::live(|| square.div(&p).expect("kept").expect("not 0"));
    let (same, equal) = zed_alloc_count::live(|| back == p);
    let (above, order) = zed_alloc_count::live(|| square > p && p > b);
    assert!(same && above);
    let peaks = [product.peak, quotient.peak, equal.peak, order.peak];
    assert!(
        peaks.iter().all(|&k| k < 1 << 10),
        "peak heap bytes of the product, quotient, equality and order: {peaks:?}"
    );
}

/// `Rat::pow` splits a part wider than a word into small primes and a least root after asking
/// the system for `SPLIT_ASK_BITS_A_BIT` bits a bit, four bytes; the
/// split itself must stay within that ask, or a process given the ask could still abort in it.
/// Checked here on built bases of 2^7 to 2^20 bits of four shapes: `2^s - 1`, which holds the
/// small primes 3, 5 and 17 at `s = 2^k`; an odd number with no small prime it is likely to
/// hold; and a square and a cube of such a number, whose least roots are found. The peak counts
/// the ask's own allocation, so the bound allowed is the ask plus 1 KiB for the exponents and
/// lists beside it.
#[test]
fn splitting_a_wide_part_stays_within_its_ask() {
    let a_bit = zed_kernel::num::SPLIT_ASK_BITS_A_BIT / 8;
    let mut over = Vec::new();
    for s in [1u64 << 7, 1 << 12, 1 << 16, 1 << 20] {
        let one = BigInt::from(1);
        let odd: BigInt = (&one << s) + BigInt::from(0x9e37_79b9_7f4a_7c15u64) * 2 + 1;
        let third: BigInt = (&one << (s / 3)) + 0x1234_5679;
        let bases = [
            ("2^s - 1", (&one << s) - 1),
            ("odd", odd.clone()),
            ("square", (&odd >> (s / 2)).pow(2)),
            ("cube", third.pow(3)),
        ];
        for (shape, b) in bases {
            let bits = b.bits();
            let x = Rat::int(b);
            let (p, live) = zed_alloc_count::live(|| x.pow(&7u32.into()).expect("given"));
            assert!(p != int(0));
            println!(
                "{shape} of {bits} bits: peak {} bytes, {:.3} a bit",
                live.peak,
                live.peak as f64 / bits as f64
            );
            if live.peak > a_bit * bits + 1024 {
                over.push(format!("{shape} at {bits} bits: peak {} bytes", live.peak));
            }
        }
    }
    assert!(over.is_empty(), "peaks over the ask: {over:?}");
}

/// A sum builds its part above the shared powers (DESIGN.md "Kept powers", *Sums*), for wide
/// atoms as for primes: `q^(2^64) + q^(2^64)` is `2 q^(2^64)` and `q^(2^64) - 3 q^(2^64 - 1)`
/// is `(q - 3) q^(2^64 - 1)`, each with nothing built past a few words.
#[test]
fn a_sum_of_equal_wide_powers_builds_nothing() {
    let q = int(2).pow(&64u32.into()).unwrap().add(&int(13)).unwrap();
    let e = num_bigint::BigUint::from(1u32) << 64u32;
    let p = q.pow(&e).unwrap();
    let below = q.pow(&(&e - 1u32)).unwrap();
    let (ok, live) = zed_alloc_count::live(|| {
        let twice = p.add(&p).expect("nothing is built");
        let rest = p
            .sub(&int(3).mul(&below).unwrap())
            .expect("nothing is built");
        let want = q.sub(&int(3)).unwrap().mul(&below).unwrap();
        twice == int(2).mul(&p).unwrap() && rest == want && p.sub(&p).unwrap() == int(0)
    });
    assert!(ok);
    assert!(live.peak < 1 << 12, "peak heap {} bytes", live.peak);
    // The size the checker reads (`Rat::sum_least`) factors out the same shared atoms, so it
    // names a few bits, not the 2^70 bits of the power: before, it named the power's own size.
    let three_below = int(3).mul(&below).unwrap();
    for (a, b) in [(&p, &p), (&p, &three_below)] {
        let least = a.sum_least(b).expect("nothing is moved out");
        assert!(least < num_bigint::BigUint::from(256u32), "{least}");
    }
    assert!(p.sum_least(&int(1)).unwrap() >= num_bigint::BigUint::from(1u32) << 70u32);
}

/// A side of a random pair: factors `(base, exponent)`, bases in `2..2^70` and exponents in
/// `0..2^20` (DESIGN step L1.17b), each exponent below `2^u` for `u` uniform in `0..=20`, so
/// that pairs small enough to build and pairs far past it both come up.
fn random_side(rng: &mut zed_tests::seed::Rng) -> Vec<(u128, u64)> {
    let factors = 1 + rng.below(3);
    (0..factors)
        .map(|_| {
            let bits = 2 + rng.below(69) as u32;
            let base =
                (u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64())) % (1u128 << bits);
            let u = rng.below(21) as u32;
            (base.max(2), rng.below_u64(1u64 << u))
        })
        .collect()
}

fn kept_side(side: &[(u128, u64)]) -> Rat {
    side.iter().fold(int(1), |acc, (b, e)| {
        let p = Rat::int(BigInt::from(*b)).pow(&(*e).into()).expect("kept");
        acc.mul(&p).expect("kept")
    })
}

/// `log2` of the side and the bits of the built side, at most.
fn side_size(side: &[(u128, u64)]) -> (f64, u64) {
    side.iter().fold((0.0, 0), |(l, n), (b, e)| {
        let bits = u64::from(zed_numtheory::BitLen::bit_len(*b));
        (l + *e as f64 * (*b as f64).log2(), n + bits * e)
    })
}

fn built_side(side: &[(u128, u64)]) -> num_bigint::BigUint {
    side.iter()
        .fold(num_bigint::BigUint::from(1u32), |acc, (b, e)| {
            acc * num_bigint::BigUint::from(*b).pow(u32::try_from(*e).expect("below 2^20"))
        })
}

/// DESIGN step L1.17b: 10,000 pairs of products of powers, bases below 2^70 and exponents below
/// 2^20, each order and equality against the built numbers'. A fourth of the pairs are one
/// value written two ways (`(b c)^e d^f` and `b^e c^e d^g d^(f - g)`), equal; a fourth are near
/// ties, `a^e` against `b^f` with `f` the floor or ceiling of `e log a / log b`; the rest are
/// independent. Building a side of 2^20 exponent costs 73 million bits, so a pair is built when
/// both sides are within 2^16 bits; past that the order is read from `f64` sums of `e log2 b`.
/// Each term is within 2^-49 of its value, relatively: the base rounded to `f64` moves its
/// `log2` by at most `2^-53 / ln 2` absolute, so relatively too, since `log2 b >= 1`; `log2`
/// is within one unit in the last place, 2^-52 relative; the product by `e < 2^53` and each sum
/// round once, 2^-53 each. With at most 4 terms the sums are within 2^-46 of the larger, so a
/// pair is counted only where they differ by more than 2^-30 of it, and else skipped. Every near
/// tie is drawn within 2^16 bits, so each is built. The test states how many pairs each way
/// decided, and fails if fewer than 3,000 were built (2,500 near ties and
/// the small independent pairs).
#[test]
fn random_products_of_powers_order_as_the_built_numbers() {
    let (mut rng, seed) = zed_tests::seed::Rng::fresh("random_products_of_powers_order");
    let (mut built, mut logs) = (0usize, 0usize);
    for i in 0..10_000 {
        let (x, y) = match i % 4 {
            0 => {
                let (b, c, d) = (2 + rng.below_u64(1 << 34), 2 + rng.below_u64(1 << 34), 3);
                let (e, f) = (rng.below_u64(1 << 20), rng.below_u64(1 << 20));
                let g = rng.below_u64(f + 1);
                let bc = u128::from(b) * u128::from(c);
                (
                    vec![(bc, e), (d, f)],
                    vec![(u128::from(b), e), (u128::from(c), e), (d, g), (d, f - g)],
                )
            }
            1 => {
                let a = 2 + u128::from(rng.next_u64() >> 1);
                let b = 2 + u128::from(rng.next_u64() >> 2);
                let e = 1 + rng.below_u64(1 << 9);
                let f = (e as f64 * (a as f64).log2() / (b as f64).log2()) as u64;
                (vec![(a, e)], vec![(b, f + rng.below_u64(2))])
            }
            _ => (random_side(&mut rng), random_side(&mut rng)),
        };
        let (kx, ky) = (kept_side(&x), kept_side(&y));
        let ((lx, nx), (ly, ny)) = (side_size(&x), side_size(&y));
        let want = if i % 4 == 0 {
            std::cmp::Ordering::Equal
        } else if nx.max(ny) <= 1 << 16 {
            built += 1;
            built_side(&x).cmp(&built_side(&y))
        } else if (lx - ly).abs() > lx.max(ly) * 2f64.powi(-30) {
            logs += 1;
            lx.partial_cmp(&ly).expect("finite")
        } else {
            continue;
        };
        if i % 4 == 0 && nx.max(ny) <= 1 << 16 {
            assert_eq!(built_side(&x), built_side(&y), "seed {seed}, pair {i}");
        }
        let what = format!("seed {seed}, pair {i}: {x:?} against {y:?}");
        assert_eq!(kx.partial_cmp(&ky), Some(want), "{what}");
        assert_eq!(kx == ky, want.is_eq(), "{what}");
        if want.is_eq() {
            assert_eq!(kx.residues(), ky.residues(), "{what}");
        }
    }
    eprintln!("{built} pairs decided by the built numbers, {logs} by f64 sums of logarithms");
    assert!(built >= 3_000, "{built} pairs built");
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
