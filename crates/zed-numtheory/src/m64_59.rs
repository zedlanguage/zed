//! Arithmetic modulo the prime `P = 2^64 - 59`, the largest below `2^64`: the field of
//! zed-kernel's treap priorities (`zed_kernel::priority`, whose module comment gives the
//! sources), moved here from there (DRY-num-words-2026-11-26) so that one copy of each
//! routine serves every crate, as [`crate::m61`] does for `2^61 - 1`.
//!
//! `#[inline]` on the routines: they are a few instructions each and run in the inner loops of
//! the priorities (Horner's rule in `Draw::at`, the stream hash in `Stream::symbol`), which a
//! call out of line into this crate would slow (the reason given at [`crate::m61`]).

/// The prime `2^64 - 59`, the largest below `2^64`. Test:
/// `tests::m64_59::p_is_the_largest_prime_below_2_to_the_64`.
pub const P: u64 = 0xffff_ffff_ffff_ffc5;

/// `a * b mod P`, for `a, b < P`. `2^64 = 59 (mod P)`, so the product `hi * 2^64 + lo` is
/// `hi * 59 + lo`; `hi < 2^64`, so that is below `2^70`. A second fold, of a high part below
/// 60, leaves it below `2^64 + 60 * 59 < 2P`, which one subtraction brings below `P`.
#[inline]
pub const fn mul(a: u64, b: u64) -> u64 {
    let x = (a as u128) * (b as u128);
    let x = (x >> 64) * 59 + (x & u64::MAX as u128);
    let x = (x >> 64) * 59 + (x & u64::MAX as u128);
    reduce(x)
}

/// `a + b mod P`, for `a, b < P`.
#[inline]
pub const fn add(a: u64, b: u64) -> u64 {
    reduce(a as u128 + b as u128)
}

/// `x mod P` for `x < 2 * P`.
#[inline]
const fn reduce(x: u128) -> u64 {
    let p = P as u128;
    // `as` is exact: the result is below `P`.
    (if x >= p { x - p } else { x }) as u64
}
