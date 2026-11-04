//! The truncation of hashes for the collision test of step L1.37a (DESIGN.md sec:theories, the
//! trusted base: a hash is never an identity).
//!
//! With the Cargo feature `short-addresses` on, every content address of zedc and every 64-bit
//! digest of this crate keeps only its low 8 bits, so that distinct values share an address
//! often. Each site where an address decides equality confirms it by comparing contents, so
//! the build with the feature gives the same verdicts and outputs as the build without it;
//! the step's tests run the corpus and the fences in both. With the feature off, both
//! functions are the identity.

/// Whether this build truncates addresses.
pub const SHORT: bool = cfg!(feature = "short-addresses");

/// `h` with all but its low 8 bits cleared under the feature, and `h` itself otherwise.
#[inline]
pub const fn short64(h: u64) -> u64 {
    if SHORT { h & 0xff } else { h }
}

/// Clears all but the first byte of `a` under the feature; leaves `a` alone otherwise.
#[inline]
pub fn short256(a: &mut [u8; 32]) {
    if SHORT {
        a[1..].fill(0);
    }
}
