//! Pratt certificates of primality for `u128` (PRIME-u128), and the strong probable-prime test
//! to the 13 prime bases 2 to 41, which decides primality below `psi_13`.
//!
//! V. R. Pratt, "Every prime has a succinct certificate", SIAM J. Comput. 4(3):214-220, 1975,
//! doi:10.1137/0204018 (read 2026-11-21 in the SIAM PDF). The proof system, sec. 1, p. 214:
//! "AXIOM. (x, y, 1). INFERENCE RULES. R_1: (p, x, a), q |- (p, x, qa) provided x^((p-1)/q) !==
//! 1 (mod p) and q|(p - 1). R_2: (p, x, p - 1) |- p provided x^(p-1) == 1 (mod p). THEOREM 1. p
//! is a theorem == p is a prime." The proof of the "if" half (pp. 214-215) is Lucas's converse of
//! Fermat's theorem: "No number has multiplicative order p - 1 (mod p) when p is not a prime. If
//! such a p is proved, it must be by application of R_2 to (p, x, p - 1) where x^(p-1) == 1 (mod
//! p). Hence x^j == 1 (mod p) for some j < p - 1. Now j|p - 1, so x^((p-1)/q) == 1 (mod p) for
//! some prime q. But to prove (p, x, p - 1), we had to build up p - 1 as the product of primes q
//! which satisfied x^((p-1)/q) !== 1 (mod p)." So [`PrattCertificate::check`] accepts `p` when
//! `g^(p-1) = 1`, `p - 1 = prod q^e` over primes `q`, and `g^((p-1)/q) != 1` for each `q`: then
//! `g` has order `p - 1` modulo `p`, so `phi(p) >= p - 1` and `p` is prime. Each `q` is a prime
//! by its own certificate, or by the base test below `psi_13`. The "only if" half (p. 216): "If p
//! is prime, then p has a primitive root (mod p) [...] A proof of p may start with the axiom (p,
//! x, 1) for such a primitive root x", which is why [`PrattCertificate::build`] always finds a
//! generator for a prime. Theorem 2, p. 215: "If p is a theorem, then p has a proof of at most
//! ceil[4 log_2 p] lines."

use crate::factor::Montgomery;
use crate::is_prime;

/// `psi_13 = 3317044064679887385961981`, about `2^81.46`, the least strong pseudoprime to the 13
/// prime bases 2 to 41: every odd composite below it fails the strong test to one of them. J.
/// Sorenson and J. Webster, "Strong pseudoprimes to twelve prime bases", Math. Comp.
/// 86(304):985-1003, 2017, doi:10.1090/mcom/3134, arXiv:1509.00864 (read 2026-11-21 in the arXiv
/// LaTeX source, manybases-arxiv.tex). Abstract, line 87: "Let $\psi_m$ be the smallest strong
/// pseudoprime to the first $m$ prime bases." Theorem, lines 118-123: "\psi_{13} &= 33170\ 44064\
/// 67988\ 73859\ 61981." The proof is their exhaustive search, not a theorem of number theory,
/// and assumes nothing unproved (no generalized Riemann hypothesis). Their second table (lines
/// 766-775) lists this `n` twice, with the factorizations `1287836182261 * 2575672364521`, which
/// multiplies out to `psi_13`, and `1247050339261 * 2494100678521`, which multiplies out to
/// 3110269097300703345712981 and so is a misprint; the test
/// `psi_13_is_composite_and_passes_twelve_bases` checks the first.
pub const PSI_13: u128 = 3_317_044_064_679_887_385_961_981;

/// The 13 prime bases of [`PSI_13`].
const BASES_13: [u64; 13] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];

/// Whether `n < PSI_13` is prime: [`is_prime`] below `2^64`, the strong test to the 13 bases of
/// [`PSI_13`] above.
// Complexity tradeoff: 13 bases of at most `2 * 82` products each; trial division up to
// `sqrt(n)`, the naive method, would take up to `2^40` divisions. Given up: nothing, the test is
// exact below `PSI_13`.
pub(crate) fn is_prime_below_psi_13(n: u128) -> bool {
    debug_assert!(n < PSI_13);
    match u64::try_from(n) {
        Ok(small) => is_prime(small),
        Err(_) => n % 2 == 1 && Montgomery::new(n).strong_probable_prime(&BASES_13),
    }
}

/// Whether the odd `n > 2^64` passes the strong test to the 13 bases of [`PSI_13`].
pub(crate) fn passes_13_bases(n: u128) -> bool {
    Montgomery::new(n).strong_probable_prime(&BASES_13)
}

/// A Pratt certificate that `p` is prime: a generator of the multiplicative group modulo `p` and
/// the prime factorization of `p - 1`, each prime `q` of it at or above [`PSI_13`] with its own
/// certificate. Built by [`PrattCertificate::build`] and checked by
/// [`PrattCertificate::check`], which trusts nothing in it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrattCertificate {
    /// The prime certified.
    pub p: u128,
    /// An element of order `p - 1` modulo `p`.
    pub generator: u128,
    /// The primes of `p - 1`, increasing, with their exponents.
    pub factors: Vec<PrattFactor>,
}

/// A prime `q` of `p - 1`, its exponent, and its certificate when `q >= PSI_13`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrattFactor {
    /// The prime.
    pub q: u128,
    /// Its exponent in `p - 1`, at least 1.
    pub exponent: u32,
    /// The certificate of `q`; needed when `q >= PSI_13`, and checked when given.
    pub proof: Option<PrattCertificate>,
}

/// Why [`PrattCertificate::check`] refused a certificate; the `u128` is the `p` (or `q`) concerned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrattError {
    /// `p < 2`.
    TooSmall(u128),
    /// For `p`, the generator is 0 or not below `p`.
    GeneratorOutOfRange(u128),
    /// For `p`, `generator^(p - 1) != 1` modulo `p`.
    NotFermat(u128),
    /// For `p`, the primes are not increasing, an exponent is 0, or `p` is even and above 2.
    BadFactorList(u128),
    /// For `p`, the product of the `q^exponent` is not `p - 1`.
    WrongProduct(u128),
    /// For `p` and `q`, `generator^((p - 1) / q) = 1`, so the generator's order is below
    /// `p - 1`.
    OrderTooSmall(u128, u128),
    /// `q < PSI_13` is not prime.
    FactorNotPrime(u128),
    /// `q >= PSI_13` has no certificate.
    MissingProof(u128),
    /// The certificate given for `q` (the first) certifies another number (the second).
    ProofOfAnotherNumber(u128, u128),
}

impl PrattCertificate {
    /// Checks the certificate, and each certificate in it, in full: `Ok` means `p` is prime.
    // Complexity tradeoff: one power for the Fermat condition and one per prime of `p - 1`, each
    // O(log p) products, and the same for each certificate inside: Pratt's Theorem 2 bounds the
    // lines by `4 log2 p`, so O(log^2 p) products per level and O(log^3 p) in all, a few
    // thousand products at 128 bits. The base test below `PSI_13` stands in for certificates of
    // the small primes, which would cost the same per level and add depth.
    pub fn check(&self) -> Result<(), PrattError> {
        let p = self.p;
        let g = self.generator;
        if p < 2 {
            return Err(PrattError::TooSmall(p));
        }
        if g == 0 || g >= p {
            return Err(PrattError::GeneratorOutOfRange(p));
        }
        // The list: increasing primes, exponents at least 1, product `p - 1` without overflow
        // (each partial product divides `p - 1`, so a product past it is refused at once).
        let mut product: u128 = 1;
        let mut last = 1;
        for f in &self.factors {
            if f.q <= last || f.exponent == 0 {
                return Err(PrattError::BadFactorList(p));
            }
            last = f.q;
            for _ in 0..f.exponent {
                product = match product.checked_mul(f.q) {
                    Some(x) if x <= p - 1 => x,
                    _ => return Err(PrattError::WrongProduct(p)),
                };
            }
        }
        if product != p - 1 {
            return Err(PrattError::WrongProduct(p));
        }
        if p == 2 {
            // `p - 1 = 1`: no primes, the generator is 1, and 1 has order 1 = p - 1.
            return Ok(());
        }
        // Montgomery's form needs an odd modulus; an even `p > 2` is not prime.
        if p % 2 == 0 {
            return Err(PrattError::BadFactorList(p));
        }
        let m = Montgomery::new(p);
        let (one, gm) = (m.one(), m.to(g));
        if m.pow(gm, p - 1) != one {
            return Err(PrattError::NotFermat(p));
        }
        for f in &self.factors {
            if m.pow(gm, (p - 1) / f.q) == one {
                return Err(PrattError::OrderTooSmall(p, f.q));
            }
            match &f.proof {
                Some(c) if c.p != f.q => {
                    return Err(PrattError::ProofOfAnotherNumber(f.q, c.p));
                }
                Some(c) => c.check()?,
                None if f.q >= PSI_13 => return Err(PrattError::MissingProof(f.q)),
                None if !is_prime_below_psi_13(f.q) => {
                    return Err(PrattError::FactorNotPrime(f.q));
                }
                None => {}
            }
        }
        Ok(())
    }
}
