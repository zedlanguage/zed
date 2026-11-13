//! The memory the system gives for building a number, and the errors of a number it refuses,
//! in a file of their own so that the bounds (`bound`) and the numbers (`num`) both reach them
//! without importing each other (step S.1f: no import cycle between files). The words a message
//! uses for those errors are here too: a number's size in digits and in bytes, and the memory
//! of the machine it is set against.

use std::sync::OnceLock;

use num_bigint::BigUint;
use num_traits::ToPrimitive;

/// A number the evaluator must build, read or compare, for which the system refused the memory
/// (DESIGN.md sec:domains): the number is a value of the language, and building it is the
/// machine's failure, not the program's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TooLarge {
    /// The size, in bits, of the number the step builds or reads in full: the result for an
    /// arithmetic operator, the number read for a cast from text, the digits two numbers are
    /// read to for a comparison. A message gives it in digits and bytes.
    pub size: BigUint,
    /// The memory asked for, in bits: a measured multiple of `size` the step's peak stays
    /// under, which a message names only when `size` alone would fit in the machine.
    pub ask: BigUint,
}

impl TooLarge {
    /// The words for the number this is about and the memory it needs, after "needs" in a
    /// message: `a number of about 3.6 × 10^20 digits (128 EiB); this machine has 125 GiB of
    /// memory`.
    pub fn number(&self) -> String {
        format!("a number of {}", self.amount(""))
    }

    /// The words for the digits this is about, followed by `of`, and the memory they need:
    /// `about 3.6 × 10^20 digits of them (128 EiB); this machine has 125 GiB of memory`.
    pub fn amount(&self, of: &str) -> String {
        format!(
            "about {} digits{of} ({}){}",
            about(&digits_of_bits(&self.size)),
            bytes_text(&bytes_of(&self.size)),
            memory_clause(&bytes_of(&self.size), &bytes_of(&self.ask))
        )
    }

    /// A refusal of `bytes` bytes of memory for a copy or a buffer of that size, which is both
    /// the size of what is written and the memory asked for.
    pub fn of_bytes(bytes: usize) -> TooLarge {
        let bits = BigUint::from(bytes) << 3u32;
        TooLarge {
            size: bits.clone(),
            ask: bits,
        }
    }

    /// The size of what this is about in bytes, and the memory it needs: `2.0 GiB; this run
    /// could not get that much memory, though this machine has 125 GiB`.
    pub fn memory(&self) -> String {
        format!(
            "{}{}",
            bytes_text(&bytes_of(&self.size)),
            memory_clause(&bytes_of(&self.size), &bytes_of(&self.ask))
        )
    }

    /// The words for the decimal text of the number this is about, a byte a digit, and the
    /// memory it needs: `about 3.6 × 10^20 digits (315 EiB); this machine has 125 GiB of
    /// memory`. The bytes are left out where they would repeat the count of digits, below
    /// 1 KiB and past 1024 YiB.
    pub fn text(&self) -> String {
        let digits = digits_of_bits(&self.size);
        let (count, bytes) = (about(&digits), bytes_text(&digits));
        let bytes = match bytes == format!("{count} bytes") {
            true => String::new(),
            false => format!(" ({bytes})"),
        };
        format!(
            "about {count} digits{bytes}{}",
            memory_clause(&digits, &bytes_of(&self.ask))
        )
    }
}

/// `bits` bits of memory in bytes, rounded up.
pub fn bytes_of(bits: &BigUint) -> BigUint {
    (bits + 7u32) >> 3u32
}

/// The number of decimal digits of a number `bits` bits wide, at most one off:
/// `floor(bits * log10 2) + 1`, with `log10 2` as `1233 / 4096`, which is below it by 2^-17.
pub fn digits_of_bits(bits: &BigUint) -> BigUint {
    ((bits * 1233u32) >> 12u32) + 1u32
}

/// The bits of a number of `digits` decimal digits, at most one more:
/// `ceil(digits * log2 10)`, with `log2 10` as `13607 / 4096`, which is above it by 2^-13.
pub fn bits_of_digits(digits: &BigUint) -> BigUint {
    ((digits * 13607u32) >> 12u32) + 1u32
}

/// `Ok` when the system gives `ask` bits of memory, asked of the allocator itself and freed at
/// once, so the answer is the machine's and the evaluator sets no limit; else [`TooLarge`]
/// naming `size`, the bits of the number the step builds, and `ask`. A build that would ask
/// for more than the system gives is reported before it starts, where num-bigint would abort
/// the process.
pub fn room(size: BigUint, ask: BigUint) -> Result<(), TooLarge> {
    match given(&ask) {
        true => Ok(()),
        false => Err(TooLarge { size, ask }),
    }
}

/// Whether the allocator gives `bits` bits at once, asked and freed at once.
fn given(bits: &BigUint) -> bool {
    let words = (bits + 63u32) >> 6u32;
    words
        .to_usize()
        .is_some_and(|w| Vec::<u64>::new().try_reserve_exact(w).is_ok())
}

/// The machine's memory in bytes, `MemTotal` of `/proc/meminfo`, read once; `None` where that
/// file is missing or unreadable, and a message then leaves the machine out.
pub fn machine_memory() -> Option<u64> {
    static MEMORY: OnceLock<Option<u64>> = OnceLock::new();
    *MEMORY.get_or_init(|| {
        let info = std::fs::read_to_string("/proc/meminfo").ok()?;
        let total = info.lines().find_map(|l| l.strip_prefix("MemTotal:"))?;
        let kib: u64 = total.trim().strip_suffix("kB")?.trim().parse().ok()?;
        kib.checked_mul(1024)
    })
}

/// The end of a message for a value of `size` bytes whose step asked for `ask` bytes and was
/// refused, set against the machine's memory ([`machine_memory`]):
/// `; this machine has 125 GiB of memory` when the value alone is larger;
/// `, and about 1 ZiB of memory to compute it; this machine has 125 GiB of memory` when only
/// the step's working memory is; and `…; this run could not get that much memory, though this
/// machine has 125 GiB` when neither is, as under a limit on the run's address space.
pub fn memory_clause(size: &BigUint, ask: &BigUint) -> String {
    let memory = machine_memory().map(BigUint::from);
    if let Some(m) = &memory
        && size > m
    {
        return format!("; this machine has {} of memory", bytes_text(m));
    }
    let mut out = String::new();
    if ask > size {
        out = format!(", and about {} of memory to compute it", bytes_text(ask));
    }
    match &memory {
        Some(m) if ask.max(size) > m => {
            out += &format!("; this machine has {} of memory", bytes_text(m));
        }
        Some(m) => {
            out += &format!(
                "; this run could not get that much memory, though this machine has {}",
                bytes_text(m)
            );
        }
        None => {}
    }
    out
}

/// `n` as a reader takes it in at a glance: `n` itself below a million, else with two
/// significant digits, `3.6 × 10^20`, from `n`'s leading 64 bits, O(1) word operations beside
/// the shift.
pub fn about(n: &BigUint) -> String {
    if *n < BigUint::from(1_000_000u32) {
        return n.to_string();
    }
    let shift = n.bits().saturating_sub(64);
    let top = (n >> shift).to_f64().expect("64 bits fit in an f64");
    let log = top.log10() + shift as f64 * std::f64::consts::LOG10_2;
    let mut k = log.floor();
    let mut m = 10f64.powf(log - k);
    // `9.96` shows as `10.0`; it is `1.0 × 10^(k+1)`.
    if (m * 10.0).round() >= 100.0 {
        m /= 10.0;
        k += 1.0;
    }
    format!("{m:.1} × 10^{k}")
}

/// `bytes` bytes in binary units, as the units of information are written (`B`, `KiB`, ...,
/// `YiB`): `1 byte`, `512 bytes`, `1.5 KiB`, `128 EiB`, one decimal below ten and none above;
/// beyond 1024 YiB, `1.6 × 10^29 bytes`, the count with two digits ([`about`]).
pub fn bytes_text(bytes: &BigUint) -> String {
    const UNITS: [&str; 8] = ["KiB", "MiB", "GiB", "TiB", "PiB", "EiB", "ZiB", "YiB"];
    if *bytes < BigUint::from(1024u32) {
        return match bytes.to_u32() {
            Some(1) => "1 byte".into(),
            _ => format!("{bytes} bytes"),
        };
    }
    let mut v = bytes
        .to_f64()
        .expect("a BigUint has an f64, perhaps infinite");
    for unit in UNITS {
        v /= 1024.0;
        if (v * 10.0).round() < 100.0 {
            return format!("{v:.1} {unit}");
        }
        if v.round() < 1024.0 {
            return format!("{v:.0} {unit}");
        }
    }
    format!("{} bytes", about(bytes))
}

/// Why a float literal has no value at a binary float carrier (DESIGN.md sec:domains), or why
/// a number could not be rounded to one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralRounding {
    /// It rounds to infinity: it is beyond the largest finite float.
    Infinite,
    /// It is not zero, but it rounds to zero: it is below half the least subnormal.
    Zero,
    /// It lies so near a rounding boundary that telling which side it is on needs more
    /// memory than the system gives.
    TooLarge(TooLarge),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_are_shown_whole_below_a_million_and_with_two_digits_above() {
        let n = |x: u128| about(&BigUint::from(x));
        assert_eq!(n(0), "0");
        assert_eq!(n(999_999), "999999");
        assert_eq!(n(1_000_000), "1.0 × 10^6");
        assert_eq!(n(354_000_000_000_000_000_000), "3.5 × 10^20");
        // 9.96 × 10^7 rounds up into the next power of ten.
        assert_eq!(n(99_600_000), "1.0 × 10^8");
        assert_eq!(n(u128::MAX), "3.4 × 10^38");
        // Past what an f64 holds: 2^4000 is 1.3 × 10^1204.
        assert_eq!(about(&(BigUint::from(1u32) << 4000u32)), "1.3 × 10^1204");
    }

    #[test]
    fn bytes_are_shown_in_binary_units() {
        let b = |x: u128| bytes_text(&BigUint::from(x));
        assert_eq!(b(0), "0 bytes");
        assert_eq!(b(1), "1 byte");
        assert_eq!(b(1023), "1023 bytes");
        assert_eq!(b(1024), "1.0 KiB");
        assert_eq!(b(1536), "1.5 KiB");
        assert_eq!(b(10 * 1024 - 1), "10 KiB");
        // Just under 1 MiB rounds to it, not to 1024 KiB.
        assert_eq!(b((1 << 20) - 1), "1.0 MiB");
        assert_eq!(b(125 << 30), "125 GiB");
        assert_eq!(b(1 << 67), "128 EiB");
        assert_eq!(b(1 << 89), "512 YiB");
        // Past 1024 YiB the count is shown as a power of ten: 2^100 bytes.
        assert_eq!(b(1 << 100), "1.3 × 10^30 bytes");
    }

    #[test]
    fn digits_follow_from_bits() {
        let d = |x: u32| digits_of_bits(&BigUint::from(x));
        // 2^64 has 20 digits, 2^65536 has 19729.
        assert_eq!(d(65), BigUint::from(20u32));
        assert_eq!(d(65537), BigUint::from(19729u32));
        assert_eq!(d(1), BigUint::from(1u32));
    }

    /// The machine clause follows the machine's memory; the three cases are set by sizes
    /// against it.
    #[test]
    fn the_memory_clause_names_what_does_not_fit() {
        let Some(m) = machine_memory() else {
            return;
        };
        let machine = bytes_text(&BigUint::from(m));
        let big = BigUint::from(m) * 2u32;
        let small = BigUint::from(1024u32);
        assert_eq!(
            memory_clause(&big, &(&big * 8u32)),
            format!("; this machine has {machine} of memory")
        );
        assert_eq!(
            memory_clause(&small, &big),
            format!(
                ", and about {} of memory to compute it; this machine has {machine} of memory",
                bytes_text(&big)
            )
        );
        assert_eq!(
            memory_clause(&small, &small),
            format!("; this run could not get that much memory, though this machine has {machine}")
        );
    }
}
