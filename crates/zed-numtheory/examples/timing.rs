//! Hand-run timings of the routines of zed-numtheory against the other forms they were chosen
//! over (DRY-number-theory, COMPLEXITY.md row DRY-number-theory): `zcargo run -j1 -p
//! zed-numtheory --example timing`. Each line prints the best of three runs at sizes n and 8n
//! and their ratio. Not a test: the tests check results, and times depend on the load.
//!
//! A form defined here can be inlined into its loop and a routine of the crate may not be, so
//! a comparison of two forms of one routine needs both defined in the same place: the trial of
//! a second loop for `gcd_u64` (lib.rs) went the other way once both were here.

use std::hint::black_box;
use std::time::Instant;

use zed_numtheory::{
    factor, gcd_u64, gcd_u128, is_prime, least_prime_factors, m61, odd_primes_below,
};

/// The shared test generator, for its fixed streams.
#[path = "../../../tests/src/seed.rs"]
#[allow(dead_code, reason = "the timings draw only words")]
mod seed;

/// A fixed stream of words from `s` (`seed::Rng::new`), the same on every run, so two runs time
/// the same inputs.
fn words(s: u64) -> impl FnMut() -> u64 {
    let mut rng = seed::Rng::new(s);
    move || rng.next_u64()
}

/// The best of three times of `f(n)`, in milliseconds.
fn best(n: usize, f: &dyn Fn(usize)) -> f64 {
    (0..3)
        .map(|_| {
            let t = Instant::now();
            f(n);
            t.elapsed().as_secs_f64() * 1e3
        })
        .fold(f64::INFINITY, f64::min)
}

/// Prints the times at n and 8n and their ratio.
fn time(what: &str, n: usize, f: &dyn Fn(usize)) {
    let (a, b) = (best(n, f), best(8 * n, f));
    println!(
        "{what:<44} n={n:<9} {a:>9.2} ms  8n {b:>9.2} ms  ratio {:.2}",
        b / a
    );
}

/// Euclid's gcd, the form Stein's replaced (Stein's algorithm is cited at `word.rs`).
fn euclid(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// `a * b mod P` by division, the form `m61::mul` replaced.
fn m61_by_division(a: u64, b: u64) -> u64 {
    (u128::from(a) * u128::from(b) % u128::from(m61::P)) as u64
}

/// Miller-Rabin with all twelve bases and products by division, the form `is_prime` had before
/// Montgomery products and fewer bases for small `n` (the sources are cited in `factor.rs`).
fn is_prime_by_division(n: u64) -> bool {
    use zed_numtheory::{mul_mod, pow_mod};
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

fn main() {
    let pairs = |n: usize, bits: u32| {
        let mut w = words(n as u64);
        (0..n)
            .map(|_| (w() >> (64 - bits), w() >> (64 - bits)))
            .collect::<Vec<_>>()
    };
    let n = 1 << 17;
    let p64: Vec<_> = pairs(8 * n, 64);
    time("gcd_u64, random words", n, &|m| {
        p64[..m].iter().for_each(|&(a, b)| {
            black_box(gcd_u64(a, b));
        })
    });
    time("Euclid, random words", n, &|m| {
        p64[..m].iter().for_each(|&(a, b)| {
            black_box(euclid(a, b));
        })
    });
    let p128: Vec<_> = p64
        .chunks(2)
        .map(|c| {
            (
                u128::from(c[0].0) << 64 | u128::from(c[0].1),
                u128::from(c[1].0) << 64 | u128::from(c[1].1),
            )
        })
        .collect();
    time("gcd_u128, random 128-bit words", n / 2, &|m| {
        p128[..m].iter().for_each(|&(a, b)| {
            black_box(gcd_u128(a, b));
        })
    });
    // A chain of `m` dependent products over 4096 residues, which stay in the cache, so the
    // time is the product's latency and not the memory's.
    let r61: Vec<u64> = p64[..4096].iter().map(|&(a, _)| a % m61::P).collect();
    time("m61::mul, dependent chain", n, &|m| {
        black_box(
            r61.iter()
                .cycle()
                .take(m)
                .fold(1, |acc, &a| m61::mul(acc, a)),
        );
    });
    time("a * b % P by division, dependent chain", n, &|m| {
        black_box(
            r61.iter()
                .cycle()
                .take(m)
                .fold(1, |acc, &a| m61_by_division(acc, a)),
        );
    });
    let odd: Vec<u64> = p64.iter().map(|&(a, _)| a | 1).collect();
    time("is_prime, random odd words", n / 8, &|m| {
        odd[..m].iter().for_each(|&a| {
            black_box(is_prime(a));
        })
    });
    let mut w = words(7);
    let primes: Vec<u64> = std::iter::from_fn(|| Some(w() | 1))
        .filter(|&q| is_prime(q))
        .take(8 * 4096)
        .collect();
    time("is_prime, 64-bit primes", 4096, &|m| {
        primes[..m].iter().for_each(|&q| {
            black_box(is_prime(q));
        })
    });
    time("is_prime by division, 64-bit primes", 4096, &|m| {
        primes[..m].iter().for_each(|&q| {
            black_box(is_prime_by_division(q));
        })
    });
    let small: Vec<u64> = p64.iter().map(|&(a, _)| (a >> 32) | 1).collect();
    time("is_prime, random odd 32-bit words", n / 8, &|m| {
        small[..m].iter().for_each(|&a| {
            black_box(is_prime(a));
        })
    });
    let below_psi3: Vec<u64> = (12_000_001..25_326_001)
        .step_by(2)
        .filter(|&q| is_prime(q))
        .take(8 * 4096)
        .collect();
    time("is_prime, primes below 25326001", 4096, &|m| {
        below_psi3[..m].iter().for_each(|&q| {
            black_box(is_prime(q));
        })
    });
    time("is_prime by division, primes below 25326001", 4096, &|m| {
        below_psi3[..m].iter().for_each(|&q| {
            black_box(is_prime_by_division(q));
        })
    });
    time("factor, random words", 256, &|m| {
        odd[..m].iter().for_each(|&a| {
            black_box(factor(a));
        })
    });
    let p32: Vec<u64> = std::iter::from_fn(|| Some((w() >> 32) | 1 << 31 | 1))
        .filter(|&q| is_prime(q))
        .take(2 * 8 * 64)
        .collect();
    let semis: Vec<u64> = p32.chunks(2).map(|c| c[0] * c[1]).collect();
    time("factor, products of two 32-bit primes", 64, &|m| {
        semis[..m].iter().for_each(|&a| {
            black_box(factor(a));
        })
    });
    time("odd_primes_below", 1 << 20, &|m| {
        black_box(odd_primes_below(m as u64));
    });
    time("least_prime_factors", 1 << 20, &|m| {
        black_box(least_prime_factors(m as u32));
    });
}
