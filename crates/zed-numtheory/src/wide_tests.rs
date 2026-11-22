//! Tests of `factor_u128`, `is_prime_u128` and Pratt certificates (FACTOR-u128, PRIME-u128).

use num_bigint::BigUint;

use super::*;
use crate::factor::Montgomery;
use crate::pratt::PrattError;
use crate::seed::Rng;
use crate::{is_prime, next_prime, odd_primes_below};

const BASES_12: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

/// The product of a factorization, checked for overflow.
fn product(f: &[(u128, u64)]) -> u128 {
    f.iter().fold(1u128, |acc, &(p, e)| {
        (0..e).fold(acc, |a, _| a.checked_mul(p).expect("the product fits"))
    })
}

/// `n` is prime by a checked certificate, and composite `n` has a factorization into at least two
/// primes, each with a checked certificate: the answer of `is_prime_u128` is confirmed by the
/// checker, which uses the base test only below `PSI_13`.
fn confirm(n: u128) -> bool {
    let prime = is_prime_u128(n);
    let cert = PrattCertificate::build(n);
    assert_eq!(
        cert.is_some(),
        prime,
        "{n}: build and is_prime_u128 disagree"
    );
    if let Some(c) = cert {
        assert_eq!(c.check(), Ok(()), "{n}: its certificate is refused");
        assert_eq!(factor_u128(n), vec![(n, 1)]);
    } else if n > 1 {
        let f = factor_u128(n);
        assert_eq!(product(&f), n, "{n}: {f:?}");
        assert!(f.len() > 1 || f[0].1 > 1, "{n}: composite, but {f:?}");
        for &(p, _) in &f {
            assert_eq!(
                PrattCertificate::build(p).map(|c| c.check()),
                Some(Ok(())),
                "{p}"
            );
        }
    }
    prime
}

#[test]
fn wide_montgomery_arithmetic_agrees_with_num_bigint() {
    let (mut rng, s) = Rng::fresh("wide_montgomery_arithmetic_agrees_with_num_bigint");
    let mut moduli = vec![
        3u128,
        u128::MAX,
        u128::MAX - 2,
        (1 << 64) + 1,
        (1 << 127) + 1,
        (1 << 127) - 1,
    ];
    for bits in [65, 80, 96, 112, 126, 127, 128] {
        for _ in 0..20 {
            let r = u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64());
            moduli.push((r >> (128 - bits)) | 1 | 1 << (bits - 1));
        }
    }
    for n in moduli {
        let m = Montgomery::new(n);
        let big_n = BigUint::from(n);
        let r_inv = BigUint::from(2u8)
            .pow(128)
            .modinv(&big_n)
            .expect("n is odd");
        let back = |x: u128| BigUint::from(x) * &r_inv % &big_n;
        for _ in 0..20 {
            let a = (u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64())) % n;
            let b = (u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64())) % n;
            let e = u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64());
            let (ba, bb) = (BigUint::from(a), BigUint::from(b));
            let (am, bm) = (m.to(a), m.to(b));
            assert!(am < n && bm < n, "seed {s}, n {n}");
            assert_eq!(back(am), ba, "to, seed {s}, n {n}");
            assert_eq!(
                back(m.mul(am, bm)),
                &ba * &bb % &big_n,
                "mul, seed {s}, n {n}"
            );
            assert_eq!(
                back(m.add(am, bm)),
                (&ba + &bb) % &big_n,
                "add, seed {s}, n {n}"
            );
            assert_eq!(
                back(m.sub(am, bm)),
                (&ba + &big_n - &bb) % &big_n,
                "sub, seed {s}, n {n}"
            );
            assert_eq!(
                back(m.pow(am, e)),
                ba.modpow(&BigUint::from(e), &big_n),
                "pow, seed {s}"
            );
            assert_eq!(back(m.one()), BigUint::from(1u8) % &big_n);
        }
    }
}

#[test]
fn psi_12_is_composite_and_passes_twelve_bases() {
    let (p, q) = (399_165_290_221u128, 798_330_580_441u128);
    let n = p * q;
    assert_eq!(n, 318_665_857_834_031_151_167_461);
    assert!(Montgomery::new(n).strong_probable_prime(&BASES_12));
    assert!(!is_prime_u128(n));
    assert_eq!(factor_u128(n), vec![(p, 1), (q, 1)]);
    assert!(confirm(p) && confirm(q));
}

#[test]
fn psi_13_is_composite_and_passes_twelve_bases() {
    let (p, q) = (1_287_836_182_261u128, 2_575_672_364_521u128);
    assert_eq!(p * q, PSI_13);
    // The misprinted second factorization in Sorenson and Webster's table (the note at PSI_13).
    assert_ne!(1_247_050_339_261u128 * 2_494_100_678_521, PSI_13);
    let mut bases = BASES_12.to_vec();
    assert!(Montgomery::new(PSI_13).strong_probable_prime(&bases));
    bases.push(41);
    assert!(
        Montgomery::new(PSI_13).strong_probable_prime(&bases),
        "a strong pseudoprime to 2..41"
    );
    assert!(!is_prime_u128(PSI_13));
    assert!(PrattCertificate::build(PSI_13).is_none());
    assert_eq!(factor_u128(PSI_13), vec![(p, 1), (q, 1)]);
}

/// Every number within 600 of `PSI_13`, so both methods decide (the base test below, the
/// certificate at and above), each answer confirmed by the checker.
#[test]
fn the_numbers_next_to_psi_13_are_decided_both_ways() {
    assert!(!is_prime_u128(PSI_13 - 2) || confirm(PSI_13 - 2));
    let (mut below, mut above) = (0, 0);
    for n in PSI_13 - 600..PSI_13 + 600 {
        if confirm(n) {
            if n < PSI_13 { below += 1 } else { above += 1 }
        }
    }
    // About `1200 / ln(PSI_13) = 21` primes; at least one on each side shows both paths ran.
    assert!(
        below > 0 && above > 0,
        "{below} primes below, {above} above"
    );
}

#[test]
fn the_mersenne_primes_89_107_127_have_checked_certificates() {
    for k in [89, 107, 127] {
        let p = (1u128 << k) - 1;
        assert!(is_prime_u128(p), "2^{k} - 1");
        let c = PrattCertificate::build(p).expect("a certificate");
        assert_eq!(c.check(), Ok(()), "2^{k} - 1");
    }
}

#[test]
fn the_mersenne_numbers_101_and_103_are_composite() {
    for (k, p, q) in [
        (101, 7_432_339_208_719u128, 341_117_531_003_194_129u128),
        (103, 2_550_183_799, 3_976_656_429_941_438_590_393),
    ] {
        let n = (1u128 << k) - 1;
        assert_eq!(p * q, n);
        assert!(!is_prime_u128(n), "2^{k} - 1");
        assert!(PrattCertificate::build(n).is_none());
        assert_eq!(factor_u128(n), vec![(p, 1), (q, 1)]);
        assert!(confirm(p) && confirm(q));
    }
}

/// The hard case of `split_u128`: two primes above `2^63`, found again, and a prime squared.
#[test]
fn products_of_two_64_bit_primes_are_composite_and_factored() {
    let (mut rng, s) = Rng::fresh("products_of_two_64_bit_primes_are_composite_and_factored");
    for _ in 0..3 {
        let p = next_prime(rng.next_u64() | 1 << 63).unwrap_or(18_446_744_073_709_551_557);
        let q = next_prime(rng.next_u64() | 1 << 63).unwrap_or(18_446_744_073_709_551_533);
        let n = u128::from(p) * u128::from(q);
        assert!(!is_prime_u128(n), "seed {s}: {p} * {q}");
        let mut want = vec![(u128::from(p.min(q)), 1), (u128::from(p.max(q)), 1)];
        if p == q {
            want = vec![(u128::from(p), 2)];
        }
        assert_eq!(factor_u128(n), want, "seed {s}");
    }
    let p = 18_446_744_073_709_551_557u128; // the largest prime below 2^64
    assert_eq!(factor_u128(p * p), vec![(p, 2)]);
}

#[test]
fn factor_u128_agrees_with_factor_below_2_64_and_multiplies_back() {
    let (mut rng, s) = Rng::fresh("factor_u128_agrees_with_factor_below_2_64_and_multiplies_back");
    for n in (0..200u64).chain((0..200).map(|_| rng.next_u64())) {
        let want: Vec<(u128, u64)> = factor(n)
            .into_iter()
            .map(|(p, e)| (u128::from(p), e))
            .collect();
        assert_eq!(factor_u128(u128::from(n)), want, "seed {s}, {n}");
        assert_eq!(is_prime_u128(u128::from(n)), is_prime(n), "seed {s}, {n}");
    }
    for bits in [65, 80, 96, 112, 128] {
        for _ in 0..4 {
            let r = u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64());
            let n = r >> (128 - bits) | 1 << (bits - 1);
            confirm(n);
        }
    }
    confirm(u128::MAX);
    confirm(u128::MAX - 158); // 2^128 - 159, the largest prime below 2^128
    assert!(is_prime_u128(u128::MAX - 158));
}

/// The windows of [`the_primes_above_2_64_agree_with_a_sieve`]: 8 windows of 4096 numbers at
/// `2^64 + offset`, `offset < 2^40`, from fixed seeds.
fn sieve_windows() -> Vec<u128> {
    let mut rng = Rng::new(0x5eed_2026_1121);
    (0..8)
        .map(|_| (1u128 << 64) + u128::from(rng.next_u64() >> 24))
        .collect()
}

/// Agreement with the sieve of Eratosthenes on 8 windows of 4096 numbers above `2^64`: every
/// prime up to `2^32 + 256`, past `sqrt(2^64 + 2^40 + 2^12)`, crosses out its multiples in each
/// window, and the numbers left are exactly the ones `is_prime_u128` calls prime. The primes up to
/// `2^32 + 256` come from a segmented sieve by the primes below `2^16` (a composite below `65537^2
/// > 2^32 + 256` has a prime below `2^16`), spread over 16 threads, and are not stored.
#[test]
fn the_primes_above_2_64_agree_with_a_sieve() {
    const WIDTH: usize = 4096;
    const TOP: u64 = (1 << 32) + 256;
    const SEGMENT: u64 = 1 << 20;
    let windows = &sieve_windows();
    let small_flags = odd_primes_below(1 << 16);
    let small: Vec<u64> = std::iter::once(2)
        .chain(
            (3..1 << 16)
                .step_by(2)
                .filter(|&p| small_flags[(p / 2) as usize]),
        )
        .collect();
    // `2^64 mod p` for the start of each window: `(2^64 - 1) mod p + 1`.
    let cross = |p: u64, crossed: &mut [Vec<bool>]| {
        let r64 = (u64::MAX % p + 1) % p;
        for (w, &start) in windows.iter().enumerate() {
            let off = (start - (1 << 64)) as u64;
            let rem = (r64 + off % p) % p;
            let mut i = ((p - rem) % p) as usize;
            while i < WIDTH {
                crossed[w][i] = true;
                i += p as usize;
            }
        }
    };
    let mut crossed = vec![vec![false; WIDTH]; windows.len()];
    for &p in &small {
        cross(p, &mut crossed);
    }
    let threads = 16u64;
    let parts: Vec<Vec<Vec<bool>>> = std::thread::scope(|sc| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let (small, cross) = (&small, &cross);
                sc.spawn(move || {
                    let mut mine = vec![vec![false; WIDTH]; windows.len()];
                    let mut seg = vec![false; SEGMENT as usize];
                    let mut lo = (1 << 16) + t * SEGMENT;
                    while lo < TOP {
                        let hi = (lo + SEGMENT).min(TOP);
                        seg.iter_mut().for_each(|x| *x = false);
                        for &p in small.iter().take_while(|&&p| p * p < hi) {
                            let mut m = lo.div_ceil(p) * p;
                            while m < hi {
                                seg[(m - lo) as usize] = true;
                                m += p;
                            }
                        }
                        for x in lo..hi {
                            if !seg[(x - lo) as usize] {
                                cross(x, &mut mine);
                            }
                        }
                        lo += threads * SEGMENT;
                    }
                    mine
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("a sieve thread"))
            .collect()
    });
    for part in parts {
        for (w, flags) in part.into_iter().enumerate() {
            for (i, f) in flags.into_iter().enumerate() {
                crossed[w][i] |= f;
            }
        }
    }
    let mut primes = 0;
    for (w, &start) in windows.iter().enumerate() {
        for (i, &composite) in crossed[w].iter().enumerate() {
            let n = start + i as u128;
            assert_eq!(is_prime_u128(n), !composite, "{n}");
            primes += usize::from(!composite);
        }
    }
    // About `8 * 4096 / ln(2^64) = 739` primes.
    assert!((600..900).contains(&primes), "{primes} primes");
}

/// A certificate of a prime whose `p - 1` has a prime at or above `PSI_13`: `p = 2 k q + 1` for
/// the least prime `q > PSI_13` and the least such `k`.
fn deep_certificate() -> PrattCertificate {
    let q = (PSI_13 + 1..).find(|&q| is_prime_u128(q)).expect("a prime");
    let p = (1u128..)
        .map(|k| 2 * k * q + 1)
        .find(|&p| is_prime_u128(p))
        .expect("a prime");
    PrattCertificate::build(p).expect("a certificate")
}

#[test]
fn a_certificate_above_psi_13_holds_the_certificate_of_its_large_prime() {
    let c = deep_certificate();
    assert_eq!(c.check(), Ok(()));
    let big = c
        .factors
        .iter()
        .find(|f| f.q >= PSI_13)
        .expect("a prime above PSI_13");
    assert_eq!(big.proof.as_ref().map(|d| d.check()), Some(Ok(())));
}

/// Negative controls: the checker refuses a certificate with a wrong factor, a wrong generator,
/// a missing prime, or a missing or misplaced proof.
#[test]
fn the_checker_refuses_broken_certificates() {
    let p = (1u128 << 89) - 1;
    let good = PrattCertificate::build(p).expect("a certificate");
    assert_eq!(good.check(), Ok(()));
    // A wrong factor: two primes of `p - 1` merged into their composite product, which keeps
    // the product `p - 1`.
    let mut bad = good.clone();
    let (a, b) = (bad.factors.remove(1), bad.factors.remove(1));
    assert_eq!((a.exponent, b.exponent), (1, 1), "{:?}", good.factors);
    bad.factors.push(PrattFactor {
        q: a.q * b.q,
        exponent: 1,
        proof: None,
    });
    bad.factors.sort_by_key(|f| f.q);
    assert_eq!(bad.check(), Err(PrattError::FactorNotPrime(a.q * b.q)));
    // A wrong prime with the wrong product.
    let mut bad = good.clone();
    let last = bad.factors.len() - 1;
    bad.factors[last].q = next_prime(bad.factors[last].q as u64).map_or(0, u128::from);
    assert_eq!(bad.check(), Err(PrattError::WrongProduct(p)));
    // A wrong generator: a square has order at most `(p - 1) / 2`.
    let mut bad = good.clone();
    bad.generator = 4;
    assert_eq!(bad.check(), Err(PrattError::OrderTooSmall(p, 2)));
    let mut bad = good.clone();
    bad.generator = p;
    assert_eq!(bad.check(), Err(PrattError::GeneratorOutOfRange(p)));
    // A missing prime.
    let mut bad = good.clone();
    bad.factors.pop();
    assert_eq!(bad.check(), Err(PrattError::WrongProduct(p)));
    // A composite claimed prime: `p` = 2^101 - 1, with the factors of 2^101 - 2.
    let n = (1u128 << 101) - 1;
    let mut bad = good.clone();
    bad.p = n;
    bad.factors = factor_u128(n - 1)
        .into_iter()
        .map(|(q, e)| PrattFactor {
            q,
            exponent: e as u32,
            proof: None,
        })
        .collect();
    assert!(matches!(
        bad.check(),
        Err(PrattError::NotFermat(_) | PrattError::OrderTooSmall(..))
    ));
    // A missing proof, and a proof of another number.
    let deep = deep_certificate();
    let i = deep
        .factors
        .iter()
        .position(|f| f.q >= PSI_13)
        .expect("a prime above PSI_13");
    let q = deep.factors[i].q;
    let mut bad = deep.clone();
    bad.factors[i].proof = None;
    assert_eq!(bad.check(), Err(PrattError::MissingProof(q)));
    let mut bad = deep.clone();
    bad.factors[i].proof = Some(good.clone());
    assert_eq!(bad.check(), Err(PrattError::ProofOfAnotherNumber(q, p)));
    // A broken certificate inside a good one.
    let mut bad = deep;
    if let Some(inner) = bad.factors[i].proof.as_mut() {
        inner.generator = 1;
    }
    assert!(matches!(bad.check(), Err(PrattError::OrderTooSmall(..))));
    // Too small, and a list out of order.
    let mut bad = good.clone();
    bad.p = 1;
    assert_eq!(bad.check(), Err(PrattError::TooSmall(1)));
    let mut bad = good;
    bad.factors.swap(0, 1);
    assert_eq!(bad.check(), Err(PrattError::BadFactorList(p)));
}

#[test]
fn small_primes_have_certificates_and_composites_do_not() {
    for n in 0..2000u128 {
        assert_eq!(
            PrattCertificate::build(n).map(|c| c.check()),
            is_prime(n as u64).then_some(Ok(())),
            "{n}"
        );
    }
}
