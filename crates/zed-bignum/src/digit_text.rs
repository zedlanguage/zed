//! Decimal digits read eight at a time: eight bytes of text loaded as one `u64`, little-endian,
//! are checked and valued with a few operations on the whole word in place of eight operations
//! on bytes (SWAR, "SIMD within a register", the method of fast float readers).

use num_bigint::BigUint;

/// The digits read into one `u64` before it joins the number: the most whose value always fits,
/// since `10^19 - 1 < 2^64 <= 10^20 - 1`.
const CHUNK_DIGITS: usize = 19;

/// `10^CHUNK_DIGITS`.
const CHUNK_BASE: u64 = 10_000_000_000_000_000_000;

/// Whether the eight bytes of `word` are all ASCII digits, `0x30` to `0x39`: each byte's high
/// nibble is 3, and stays 3 after adding 6, so its low nibble is at most 9. Adding 6 carries out
/// of a byte only when that byte is `0xFA` or above, which fails the test itself, so a carry
/// never makes another byte pass.
fn eight_digits(word: u64) -> bool {
    const HIGH: u64 = 0xF0F0_F0F0_F0F0_F0F0;
    let plus_six = word.wrapping_add(0x0606_0606_0606_0606);
    (word & HIGH) | ((plus_six & HIGH) >> 4) == 0x3333_3333_3333_3333
}

/// The value of eight ASCII digits loaded little-endian, so that the first and most significant
/// digit is the low byte. Three multiplications join neighbors: pairs of bytes into 16-bit lanes
/// (`10 * 2^8 + 1`), pairs of those into 32-bit lanes (`100 * 2^16 + 1`), then the two halves
/// (`10^4 * 2^32 + 1`); each leaves the joined value in the upper lane, below its width (99, 9999,
/// 99999999), so no lane carries into the next. The products' bits past 64 are not needed, so
/// the multiplications wrap.
fn eight_value(word: u64) -> u64 {
    let digits = word & 0x0F0F_0F0F_0F0F_0F0F;
    let pairs = (digits.wrapping_mul(10 << 8 | 1) >> 8) & 0x00FF_00FF_00FF_00FF;
    let quads = (pairs.wrapping_mul(100 << 16 | 1) >> 16) & 0x0000_FFFF_0000_FFFF;
    quads.wrapping_mul(10_000 << 32 | 1) >> 32
}

/// Whether `text` is all ASCII digits, eight bytes at a time.
//
// O(n): one word test for each eight bytes, then at most seven byte tests. The byte at a time
// test costs 2 to 5 times as many instructions (0.48 at 19 digits, 0.20 at 1024 and 0.19 at
// 10^6, EXP-swar-digits, 2026-11-12).
pub(super) fn all_digits(text: &[u8]) -> bool {
    let (eights, rest) = text.as_chunks::<8>();
    eights.iter().all(|e| eight_digits(u64::from_le_bytes(*e)))
        && rest.iter().all(u8::is_ascii_digit)
}

/// The value of at most `CHUNK_DIGITS` ASCII digits, O(1).
///
/// # Panics
///
/// When `chunk` holds anything but ASCII digits.
fn chunk_value(chunk: &[u8]) -> u64 {
    let (eights, rest) = chunk.as_chunks::<8>();
    let mut value = 0u64;
    for eight in eights {
        let word = u64::from_le_bytes(*eight);
        assert!(eight_digits(word), "ASCII decimal digits");
        value = value * 100_000_000 + eight_value(word);
    }
    for &byte in rest {
        assert!(byte.is_ascii_digit(), "ASCII decimal digits");
        value = value * 10 + u64::from(byte - b'0');
    }
    value
}

/// The value of a nonempty text of ASCII digits read whole, from the top, `CHUNK_DIGITS` at a
/// time: the first chunk takes what is left over, then for each further chunk the number so far
/// is multiplied by `10^19` and the chunk added. Called on texts of at most `LEAF_DIGITS`
/// digits, the leaves of the reading by halves.
///
/// # Panics
///
/// When `text` holds anything but ASCII digits.
//
// O(n^2) for n digits: each chunk is one pass over the words read so far, as in num-bigint's own
// reading, which also folds 19 digits into a word; this one takes eight digits a step and makes
// no copy of the text. On a leaf of 19 digits it costs 0.21 times num-bigint's instructions, at
// 1024 digits 0.66 times (EXP-swar-digits). Joining the chunks in a word vector of our own,
// each chunk the carry of one multiply-and-add pass, was 0.53 times at 1024 digits but 0.70 at
// 19, against 0.21 here, since it builds its own vector and then the number from it; taking it
// would need a switch on the length, so it is not used.
pub(super) fn read_whole(text: &[u8]) -> BigUint {
    let head = match text.len() % CHUNK_DIGITS {
        0 => CHUNK_DIGITS.min(text.len()),
        left => left,
    };
    let (head, tail) = text.split_at(head);
    // `tail` is a whole number of chunks, so nothing is left over.
    let (chunks, _) = tail.as_chunks::<CHUNK_DIGITS>();
    let mut number = BigUint::from(chunk_value(head));
    for chunk in chunks {
        number *= CHUNK_BASE;
        number += chunk_value(chunk);
    }
    number
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every byte value in each of the eight places, the other places digits: the word test
    /// accepts exactly the digits, and the value of eight digits is their number.
    #[test]
    fn eight_bytes_are_digits_exactly_when_each_byte_is() {
        for place in 0..8 {
            for byte in 0..=u8::MAX {
                let mut text = *b"31415926";
                text[place] = byte;
                let word = u64::from_le_bytes(text);
                let all = text.iter().all(u8::is_ascii_digit);
                assert_eq!(eight_digits(word), all, "{text:?}");
                assert_eq!(all_digits(&text), all, "{text:?}");
                if all {
                    let number: u64 = std::str::from_utf8(&text)
                        .expect("ASCII")
                        .parse()
                        .expect("digits");
                    assert_eq!(eight_value(word), number, "{text:?}");
                }
            }
        }
        for (text, number) in [
            (b"00000000", 0),
            (b"00000001", 1),
            (b"10000000", 10_000_000),
            (b"99999999", 99_999_999),
        ] {
            assert_eq!(eight_value(u64::from_le_bytes(*text)), number);
        }
    }

    /// Chunks of every length up to 19 digits, all nines and all zeros, read as num-bigint
    /// reads them, and a whole text of every length from 1 to 120 around the chunk edges.
    #[test]
    fn chunks_and_short_texts_read_their_number() {
        for len in 1..=CHUNK_DIGITS {
            for text in [
                "9".repeat(len),
                "0".repeat(len),
                "1234567890123456789"[..len].into(),
            ] {
                let number: u64 = text.parse().expect("digits");
                assert_eq!(chunk_value(text.as_bytes()), number, "{text}");
            }
        }
        for len in 1..=120 {
            for text in ["9".repeat(len), format!("1{}", "0".repeat(len - 1))] {
                let expected: BigUint = text.parse().expect("digits");
                assert_eq!(read_whole(text.as_bytes()), expected, "{text}");
            }
        }
    }

    /// A byte that is not a digit in a chunk stops the reading, in the part read eight at a
    /// time and in the rest.
    #[test]
    #[should_panic(expected = "ASCII decimal digits")]
    fn a_mark_in_the_eight_byte_part_stops_the_reading() {
        read_whole(b"1234_5678");
    }

    #[test]
    #[should_panic(expected = "ASCII decimal digits")]
    fn a_mark_in_the_rest_stops_the_reading() {
        read_whole(b"12345678901_");
    }
}
