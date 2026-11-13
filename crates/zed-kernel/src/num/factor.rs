//! The prime factors of a 64-bit integer: Miller-Rabin with the bases that decide every
//! 64-bit number, and Pollard's rho in Brent's form to split a composite.

/// The prime factors of `n > 1` with their multiplicities, by prime.
pub(super) fn factor(n: u64) -> Vec<(u64, u64)> {
    let mut primes = Vec::new();
    let mut left = vec![n];
    while let Some(m) = left.pop() {
        if m == 1 {
            continue;
        }
        if m.is_multiple_of(2) {
            let z = m.trailing_zeros();
            primes.extend(std::iter::repeat_n(2, z as usize));
            left.push(m >> z);
        } else if is_prime(m) {
            primes.push(m);
        } else {
            let d = split(m);
            left.push(d);
            left.push(m / d);
        }
    }
    primes.sort_unstable();
    let mut out: Vec<(u64, u64)> = Vec::new();
    for p in primes {
        match out.last_mut() {
            Some((q, k)) if *q == p => *k += 1,
            _ => out.push((p, 1)),
        }
    }
    out
}

fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    (u128::from(a) * u128::from(b) % u128::from(m)) as u64
}

fn pow_mod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1 % m;
    a %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod(r, a, m);
        }
        a = mul_mod(a, a, m);
        e >>= 1;
    }
    r
}

/// Whether `n` is prime; exact for every 64-bit `n`, by the first twelve primes as bases.
pub fn is_prime(n: u64) -> bool {
    const BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    if n < 2 {
        return false;
    }
    for p in BASES {
        if n.is_multiple_of(p) {
            return n == p;
        }
    }
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    'bases: for a in BASES {
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = mul_mod(x, x, n);
            if x == n - 1 {
                continue 'bases;
            }
        }
        return false;
    }
    true
}

/// A factor of the odd composite `n` other than 1 and `n`.
fn split(n: u64) -> u64 {
    // Brent's cycle search on `x^2 + c`, with a new `c` when a cycle closes without a factor.
    for c in 1u64.. {
        let f = |x: u64| ((u128::from(mul_mod(x, x, n)) + u128::from(c)) % u128::from(n)) as u64;
        let (mut x, mut y, mut g, mut r) = (2u64, 2u64, 1u64, 1u64);
        let mut q = 1u64;
        let mut ys = y;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && g == 1 {
                ys = y;
                for _ in 0..128.min(r - k) {
                    y = f(y);
                    q = mul_mod(q, x.abs_diff(y), n);
                }
                g = gcd(q, n);
                k += 128;
            }
            r *= 2;
        }
        if g == n {
            loop {
                ys = f(ys);
                g = gcd(x.abs_diff(ys), n);
                if g > 1 {
                    break;
                }
            }
        }
        if g != n {
            return g;
        }
    }
    // Unreachable: each `c` ends (once `y` is in the cycle and `r` past its length, a
    // difference is 0, so `g = n`; the search back from `ys` then meets the difference of that
    // batch that shares a factor with `n`), and some `c` returns. The first comparison is of
    // `x = 2` with `f(f(2)) = 2 + (c + 2)(c + 7) mod n`, so it gives `g = gcd((c + 2)(c + 7), n)`.
    // For `p` the least prime factor of `n` (odd, so `p >= 3`) and `c = p - 2 >= 1`, that is
    // `gcd(p (p + 5), n)`: a multiple of `p`, and `n` only if the odd `n / p >= p` divides the
    // even `p + 5`, so `n / p <= (p + 5) / 2` and `p <= 5`, which leaves `n = 25` alone. So
    // every odd composite but 25 is split by `c = p - 2` at the latest, and 25 is split by a
    // smaller `c` (`factors_agree_with_trial_division`).
    unreachable!("some c splits a composite")
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The factors of `n` by trial division.
    fn by_trial(mut n: u64) -> Vec<(u64, u64)> {
        let mut out = Vec::new();
        let mut p = 2;
        while p * p <= n {
            let mut k = 0;
            while n.is_multiple_of(p) {
                n /= p;
                k += 1;
            }
            if k > 0 {
                out.push((p, k));
            }
            p += 1;
        }
        if n > 1 {
            out.push((n, 1));
        }
        out
    }

    /// NUM-expect-audit: `split` returns for every composite below `2^16`, 25 among them (the
    /// one odd composite its proof leaves to this test), and the factors are the primes trial
    /// division finds.
    #[test]
    fn factors_agree_with_trial_division() {
        for n in 2..1u64 << 16 {
            assert_eq!(factor(n), by_trial(n), "{n}");
            assert_eq!(is_prime(n), by_trial(n) == [(n, 1)], "{n}");
        }
    }

    /// NUM-expect-audit: the 64-bit corner cases: squares and products of the largest primes
    /// below `2^32`, Carmichael numbers and strong pseudoprimes to small bases, prime powers,
    /// `2^64 - 1` and the largest 64-bit prime.
    #[test]
    fn factors_of_wide_numbers_are_their_primes() {
        let (p, q) = (4_294_967_291u64, 4_294_967_279u64);
        let cases: [(u64, &[(u64, u64)]); 9] = [
            (p * p, &[(p, 2)]),
            (p * q, &[(q, 1), (p, 1)]),
            (561, &[(3, 1), (11, 1), (17, 1)]),
            (3_215_031_751, &[(151, 1), (751, 1), (28_351, 1)]),
            (
                3_825_123_056_546_413_051,
                &[(149_491, 1), (747_451, 1), (34_233_211, 1)],
            ),
            (3u64.pow(40), &[(3, 40)]),
            (1_000_003u64.pow(3), &[(1_000_003, 3)]),
            (
                u64::MAX,
                &[
                    (3, 1),
                    (5, 1),
                    (17, 1),
                    (257, 1),
                    (641, 1),
                    (65_537, 1),
                    (6_700_417, 1),
                ],
            ),
            (
                18_446_744_073_709_551_557,
                &[(18_446_744_073_709_551_557, 1)],
            ),
        ];
        for (n, want) in cases {
            assert_eq!(factor(n), want, "{n}");
        }
    }
}
