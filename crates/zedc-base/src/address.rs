//! Content addresses (DESIGN.md sec:keypaths and step M0.7): the BLAKE3-256 hash of a
//! definition's canonical ZIR serialization, printed as 64 lowercase hex digits. Addresses are
//! ordered by their bytes, which is the content-address order every tie-break uses.

use std::fmt;

/// A 256-bit content address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentAddress(pub [u8; 32]);

impl ContentAddress {
    /// The address printed as hex, parsed back; `None` unless `hex` is exactly 64 lowercase
    /// hex digits.
    pub fn parse(hex: &str) -> Option<Self> {
        let digits = hex.as_bytes();
        if digits.len() != 64 {
            return None;
        }
        let nibble = |c: u8| match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            _ => None,
        };
        let mut bytes = [0u8; 32];
        for (i, byte) in bytes.iter_mut().enumerate() {
            *byte = nibble(digits[2 * i])? << 4 | nibble(digits[2 * i + 1])?;
        }
        Some(ContentAddress(bytes))
    }

    /// The address `h` has hashed: its BLAKE3-256 digest, of which the build with zed-kernel's
    /// feature `short-addresses` keeps only the first byte, so that addresses collide (step
    /// L1.37a).
    pub fn hashed(h: &blake3::Hasher) -> Self {
        let mut bytes = *h.finalize().as_bytes();
        zed_kernel::address::short256(&mut bytes);
        ContentAddress(bytes)
    }
}

/// A BLAKE3 hash of a domain tag and then fields, each string field written after its length:
/// the form of every content address and digest the compiler makes (the export and unit
/// addresses of `zedc-zir`'s `canon`, a ZIR node's, a program's in `zedc::run`, the names
/// digests of `zedc-types`' `ty.rs`, the sources hash of `zed-native`).
///
/// Why lengths: two different lists of strings written bare can give the same bytes (`"ab", "c"`
/// and `"a", "bc"`); with each string after its length as 8 little-endian bytes they cannot, since
/// the reader of the bytes finds each string's end from its length. A count of items before
/// them does the same for lists. The tag, a fixed string ending in a zero byte, keeps the
/// hashes of different kinds of thing apart. The bytes written are the ones each site wrote by
/// hand before this type (DRY-hash-crate-2026-11-26), so every pinned address is unchanged;
/// `l01_32_canonical_zir::normal_form_pins` pins them.
pub struct Framed(blake3::Hasher);

impl Framed {
    /// A hash that starts with `tag`.
    pub fn new(tag: &[u8]) -> Framed {
        let mut h = blake3::Hasher::new();
        h.update(tag);
        Framed(h)
    }

    /// Writes `bytes` as they are: a digest, an address or a word of fixed length.
    pub fn raw(&mut self, bytes: &[u8]) -> &mut Framed {
        self.0.update(bytes);
        self
    }

    /// Writes the count `n` as 8 little-endian bytes.
    pub fn count(&mut self, n: usize) -> &mut Framed {
        self.raw(&(n as u64).to_le_bytes())
    }

    /// Writes `bytes` after their length ([`Framed::count`]).
    pub fn field(&mut self, bytes: &[u8]) -> &mut Framed {
        self.count(bytes.len()).raw(bytes)
    }

    /// The full BLAKE3-256 digest.
    pub fn digest(&self) -> [u8; 32] {
        *self.0.finalize().as_bytes()
    }

    /// The content address ([`ContentAddress::hashed`]).
    pub fn address(&self) -> ContentAddress {
        ContentAddress::hashed(&self.0)
    }
}

impl fmt::Display for ContentAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.iter().try_for_each(|b| write!(f, "{b:02x}"))
    }
}

impl fmt::Debug for ContentAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{self}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_round_trips_and_rejects_other_spellings() {
        let mut bytes = [0u8; 32];
        bytes[0] = 0xab;
        bytes[31] = 0x07;
        let a = ContentAddress(bytes);
        let hex = a.to_string();
        assert_eq!(hex.len(), 64);
        assert!(hex.starts_with("ab00") && hex.ends_with("0007"));
        assert_eq!(ContentAddress::parse(&hex), Some(a));
        assert_eq!(ContentAddress::parse(&hex.to_uppercase()), None);
        assert_eq!(ContentAddress::parse(&hex[1..]), None);
    }

    /// `Framed` writes the bytes the sites wrote by hand: against a `blake3::Hasher` fed the
    /// same tag, counts and length-prefixed fields, and two splits of one string told apart.
    #[test]
    fn framed_writes_lengths_before_fields() {
        let mut f = Framed::new(b"zed-test\0");
        f.count(2).field(b"ab").field(b"").raw(&[7; 32]);
        let mut h = blake3::Hasher::new();
        h.update(b"zed-test\0");
        h.update(&2u64.to_le_bytes());
        h.update(&2u64.to_le_bytes());
        h.update(b"ab");
        h.update(&0u64.to_le_bytes());
        h.update(&[7; 32]);
        assert_eq!(f.digest(), *h.finalize().as_bytes());
        assert_eq!(f.address(), ContentAddress::hashed(&h));
        let split = |a: &[u8], b: &[u8]| Framed::new(b"t\0").field(a).field(b).digest();
        assert_ne!(split(b"ab", b"c"), split(b"a", b"bc"));
    }

    #[test]
    fn order_is_byte_order() {
        let (mut lo, mut hi) = ([0u8; 32], [0u8; 32]);
        lo[31] = 0xff;
        hi[0] = 0x01;
        assert!(ContentAddress(lo) < ContentAddress(hi));
    }
}
