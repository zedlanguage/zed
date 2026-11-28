//! The two bit operations of a big-endian Patricia trie over `u32` keys: the prefix of a key
//! above a branching bit ([`mask`]) and the highest bit in which two keys differ
//! ([`branching_bit`]). Okasaki and Gill, "Fast Mergeable Integer Maps" (ML Workshop 1998), §5
//! "Big-endian Patricia Trees": "The only changes required are to the mask and branchingBit
//! functions"; the full citation, the departures from the paper and how it was checked are at
//! the head of zed-kernel `types/print/uses.rs`.
//!
//! Used by the three tries of the workspace that branch on these bits: zed-kernel
//! `types/print/uses.rs` (an `Rc` trie of the uses of a message's parts) and zedc-stage
//! `stage.rs`'s `Sets` and `Maps` (hash-consed tries in an arena, a node one number). The tries
//! themselves stay apart (DRY-persistent-trees-2026-11-26): stage's equal sets are one node,
//! found through its table of made nodes, with a memo of unions by pair of numbers, which an `Rc`
//! trie does not have, as zedc-preimage `divisors.rs` stays its own treap for the same reason.
//!
//! The fact the tries rely on, with its proof. Let `a != b` and `m = branching_bit(a, b)`.
//! (1) `m` is a power of two, the highest bit set in `a ^ b`, since `a ^ b != 0` has its highest
//! one at `ilog2(a ^ b)`. (2) `mask(a, m) == mask(b, m)`: `a ^ b` has no bit above `m`, so `a` and
//! `b` agree on every bit above `m`, and `mask` keeps only those bits. (3) `a & m != b & m`: bit
//! `m` is set in `a ^ b`. So a branch at `m` with prefix `mask(a, m)` holds both keys, `a` on the
//! side of its bit `m`. Test: `the_branching_bit_is_the_highest_bit_that_differs`.

/// `key` with the bit `bit` and every bit below it cleared: the bits of `key` above `bit`, its
/// prefix at a branch on `bit`. `bit` is a power of two (a [`branching_bit`]); at 0 it panics in
/// a debug build.
#[inline]
pub fn mask(key: u32, bit: u32) -> u32 {
    key & !(bit | (bit - 1))
}

/// The highest bit in which `a` and `b` differ, as a power of two. Requires `a != b`; for equal
/// keys it panics (`ilog2` of 0).
#[inline]
pub fn branching_bit(a: u32, b: u32) -> u32 {
    1 << (a ^ b).ilog2()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [`branching_bit`] and [`mask`] against their definitions bit by bit, for keys that differ
    /// only at each bit from 0 to 31, and for pairs spread across all 32 bits: the bit is the
    /// highest that differs, the two keys share the prefix above it, and they part at it. The
    /// top bit is among them, where a signed comparison of bits goes wrong (Midtgaard 2018, at
    /// uses.rs).
    #[test]
    fn the_branching_bit_is_the_highest_bit_that_differs() {
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        for k in 0..32 {
            for base in [0, u32::MAX, 0x5555_5555, 0xAAAA_AAAA] {
                pairs.push((base, base ^ (1 << k)));
                pairs.push((base & !((1 << k) - 1), base | ((1 << k) | ((1 << k) - 1))));
            }
        }
        let mut x: u32 = 0x9E37_79B9;
        for _ in 0..2000 {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            pairs.push((x, x.rotate_left(7) ^ 0x0F0F_0F0F));
        }
        for (a, b) in pairs.into_iter().filter(|(a, b)| a != b) {
            let top = (0..32)
                .rev()
                .find(|&i| (a >> i) & 1 != (b >> i) & 1)
                .unwrap();
            let m = branching_bit(a, b);
            assert_eq!(m, 1 << top, "branching_bit({a:#x}, {b:#x})");
            let above = |k: u32| (top + 1..32).fold(0, |p, i| p | (k & (1u32 << i)));
            assert_eq!(mask(a, m), above(a), "mask({a:#x}, {m:#x})");
            assert_eq!(mask(a, m), mask(b, m), "prefixes of {a:#x}, {b:#x}");
            assert_ne!(a & m, b & m, "{a:#x}, {b:#x} at {m:#x}");
        }
    }
}
