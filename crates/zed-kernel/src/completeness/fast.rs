//! Bezout's coefficients through `num::bezout_int` (plan row TEST-complete-kernel, author
//! P189). The other crossover tests of the fast arithmetic moved to zed-bignum's
//! `completeness.rs` with the module (DRY-bignum-crate-2026-11-26), where the unit build's
//! small leaves apply; this test stays here because it checks the signs the kernel's wrapper
//! adds.

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::num::bezout_int;
use crate::num::crossover;

/// Random words from `seed`, `words` of them, the top one not zero.
fn random(seed: u64, words: usize) -> BigUint {
    let mut rng = crate::seed::Rng::new(seed);
    let mut w: Vec<u64> = (0..words).map(|_| rng.next_u64()).collect();
    if let Some(top) = w.last_mut() {
        *top |= 1 << 63;
    }
    from_words(&w)
}

fn from_words(w: &[u64]) -> BigUint {
    BigUint::from_slice(
        &w.iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect::<Vec<_>>(),
    )
}

/// Bezout's coefficients `s a + t b = gcd(a, b)` at each lift, signs of `a` and `b` included
/// through `bezout_int`, and a zero operand.
#[test]
fn bezout_coefficients() {
    let f = random(1, 5);
    let cases = [
        (random(2, 3), random(3, 7)),
        (&f * random(4, 10), &f * random(5, 60)),
        (random(6, 60) << 70u32, random(7, 2) << 3u32),
        (BigUint::one(), random(8, 9)),
        (random(9, 4), random(9, 4)),
    ];
    for (i, (a, b)) in cases.iter().enumerate() {
        let want = a.gcd(b);
        for lift in [64, crossover::LIFT_BITS] {
            let (g, s, t) = crossover::bezout(a, b, lift);
            assert_eq!(g, want, "case {i}, lift {lift}");
            assert_eq!(
                s * BigInt::from(a.clone()) + t * BigInt::from(b.clone()),
                BigInt::from(g)
            );
        }
        for (sa, sb) in [(1, 1), (-1, 1), (1, -1), (-1, -1)] {
            let (a, b) = (BigInt::from(a.clone()) * sa, BigInt::from(b.clone()) * sb);
            let (g, s, t) = bezout_int(&a, &b).expect("coefficients");
            assert_eq!(g, BigInt::from(want.clone()), "case {i}, signs {sa} {sb}");
            assert_eq!(&s * &a + &t * &b, g, "case {i}, signs {sa} {sb}");
        }
    }
    let b = BigInt::from(random(10, 3));
    let (g, s, t) = bezout_int(&BigInt::zero(), &b).expect("coefficients");
    assert_eq!(
        (g.clone(), &s * BigInt::zero() + &t * &b),
        (b.clone(), b.clone())
    );
    let (g0, ..) = bezout_int(&-&b, &BigInt::zero()).expect("coefficients");
    assert_eq!(g0, b);
    let _ = (g, s);
}
