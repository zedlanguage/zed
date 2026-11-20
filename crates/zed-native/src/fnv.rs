//! The 64-bit FNV-1a hash, which `build.rs` compiles as a module of its own to hash the
//! compiler's flags into [`link::BUILD`](crate::link::BUILD). The library compiles it only for
//! its test, which checks the same file the build script runs.
//!
//! Source: G. Fowler, L. Noll, K.-P. Vo, D. Eastlake and T. Hansen, "The FNV Non-Cryptographic
//! Hash Algorithm", Internet-Draft draft-eastlake-fnv-35, June 2025,
//! https://datatracker.ietf.org/doc/draft-eastlake-fnv/. Section 2 gives FNV-1a as
//! "hash = offset_basis; for each octet_of_data to be hashed: hash = hash xor octet_of_data;
//! hash = hash * FNV_Prime mod 2**HashSize". Section 5 gives the 64-bit FNV_Prime as
//! 2**40 + 2**8 + 0xB3 = 0x00000100_000001B3 and the 64-bit offset_basis as 0xCBF29CE4_84222325.
//! The code follows it with no departure: `wrapping_mul` is the product mod 2^64.
//!
//! A second copy: zed-kernel's `types::bytes` is the same function. A build script can call
//! the kernel only by building all of it for the host as a build dependency, which this
//! three-line definition does not justify.
//!
//! Checked 2026-11-20: the constants against section 5 of the draft and the expected outputs
//! against `FNV64svalues` in its section 8.3 test code. Test: `tests::the_drafts_test_vectors`,
//! which catches a wrong constant or the FNV-1 order (multiply before xor). It does not check
//! that `build.rs` calls this function on the flags; a build that skipped the hash would still
//! pass it.

/// The 64-bit FNV-1a hash of `bytes`. O(n) for n bytes.
pub fn fnv1a_64(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, &b| {
        (hash ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The four strings of the draft's test code (section 8.3, `teststring`) and their 64-bit
    /// FNV-1a hashes (`FNV64svalues`), without a terminating zero byte.
    #[test]
    fn the_drafts_test_vectors() {
        for (text, want) in [
            (&b""[..], 0xcbf2_9ce4_8422_2325),
            (b"a", 0xaf63_dc4c_8601_ec8c),
            (b"foobar", 0x8594_4171_f739_67e8),
            (b"Hello!\x01\xFF\xED", 0xbd51_ea70_94ee_6fa1),
        ] {
            assert_eq!(fnv1a_64(text), want, "{}", text.escape_ascii());
        }
    }
}
