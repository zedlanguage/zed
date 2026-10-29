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

    #[test]
    fn order_is_byte_order() {
        let (mut lo, mut hi) = ([0u8; 32], [0u8; 32]);
        lo[31] = 0xff;
        hi[0] = 0x01;
        assert!(ContentAddress(lo) < ContentAddress(hi));
    }
}
