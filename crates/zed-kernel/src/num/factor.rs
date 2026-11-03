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
pub(super) fn is_prime(n: u64) -> bool {
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
    unreachable!("some c splits a composite")
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}
