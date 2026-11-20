//! The fixed-width aliases `i8` … `i128` and `u8` … `u128` (DESIGN.md sec:domains, step L1.12):
//! each the name of an integer range, `ik = int[-2^(k-1)..<2^(k-1)]` and `uk = int[0..<2^k]` for
//! a width `k` of 8, 16, 32, 64 or 128 bits. The resolver and the checker read a written alias as
//! its range, and a printed range that is exactly an alias's prints as the alias (QUESTIONS A72;
//! sec:diagnostics, "Types in a message"), so these two maps must be inverse to each other, which
//! `each_alias_reads_back_as_its_name` checks.

use num_bigint::BigInt;
use zed_kernel::value::Value;

/// The widths of the aliases, in bits.
const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

/// The aliases, signed then unsigned, narrowest first.
pub const NAMES: [&str; 10] = [
    "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128",
];

/// Whether `name` is signed and its width, if it is an alias.
fn parts(name: &str) -> Option<(bool, u32)> {
    let (signed, digits) = match name.split_at_checked(1)? {
        ("i", d) => (true, d),
        ("u", d) => (false, d),
        _ => return None,
    };
    // `digits.parse` would take `i08` and `u+8`, which are names of no alias.
    let k = WIDTHS.into_iter().find(|k| k.to_string() == digits)?;
    Some((signed, k))
}

/// Whether `name` is one of the aliases.
pub fn is_alias(name: &str) -> bool {
    parts(name).is_some()
}

/// The least and the greatest int of the alias `name`, if it is one: `i64` gives -2^63 and
/// 2^63 - 1, `u8` gives 0 and 255.
pub fn range(name: &str) -> Option<(BigInt, BigInt)> {
    let (signed, k) = parts(name)?;
    let one = BigInt::from(1);
    Some(match signed {
        true => (-(&one << (k - 1)), (&one << (k - 1)) - 1),
        false => (BigInt::from(0), (one << k) - 1),
    })
}

/// The alias whose range is exactly `low ..= high`, if there is one. O(1): a range is an
/// alias's only when `high + 1` is a power of two `2^j` of at most 128 bits and `low` is 0
/// (`uj`, j a width) or `-2^j` (`i(j+1)`, j + 1 a width); each test reads the bit length, and
/// none walks the ten names.
pub fn name(low: &BigInt, high: &BigInt) -> Option<&'static str> {
    // 2^128 - 1 is the greatest end an alias has; a wider `high` is none.
    if high.bits() > 128 {
        return None;
    }
    let top: BigInt = high + 1u32;
    if top.sign() != num_bigint::Sign::Plus || top.magnitude().count_ones() != 1 {
        return None;
    }
    let j = u32::try_from(top.trailing_zeros()?).ok()?;
    let (signed, k) = if low.sign() == num_bigint::Sign::NoSign {
        (false, j)
    } else if -low == top {
        (true, j + 1)
    } else {
        return None;
    };
    if !WIDTHS.contains(&k) {
        return None;
    }
    let at = WIDTHS.iter().position(|&w| w == k)?;
    Some(NAMES[at + if signed { 0 } else { WIDTHS.len() }])
}

/// [`name`] for two int values. A value held as a kept power wider than 129 bits is no end of
/// an alias, so it is never written out: its bit count is bounded from above first
/// ([`zed_kernel::num::Rat::text_size`]), at the cost of its prime exponents, not its digits.
pub fn name_of(low: &Value, high: &Value) -> Option<&'static str> {
    let small = |v: &Value| match v {
        Value::Int(_) => true,
        Value::Big(r) => r.text_size().0 <= num_bigint::BigUint::from(129u32),
        _ => false,
    };
    if !small(low) || !small(high) {
        return None;
    }
    name(&low.to_bigint()?, &high.to_bigint()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_alias_reads_back_as_its_name() {
        for n in NAMES {
            let (l, h) = range(n).expect("an alias has a range");
            assert_eq!(name(&l, &h), Some(n), "{n}");
            assert_eq!(name_of(&Value::int(l), &Value::int(h)), Some(n), "{n}");
        }
    }

    #[test]
    fn the_ranges_of_two_aliases() {
        let b = |s: &str| s.parse::<BigInt>().expect("digits");
        assert_eq!(
            range("i64"),
            Some((b("-9223372036854775808"), b("9223372036854775807")))
        );
        assert_eq!(range("u8"), Some((b("0"), b("255"))));
        assert_eq!(
            range("u128"),
            Some((b("0"), b("340282366920938463463374607431768211455")))
        );
    }

    #[test]
    fn a_range_one_off_at_either_end_is_no_alias() {
        for n in NAMES {
            let (l, h) = range(n).expect("an alias has a range");
            let one = BigInt::from(1);
            for (l, h) in [
                (&l - &one, h.clone()),
                (&l + &one, h.clone()),
                (l.clone(), &h - &one),
                (l.clone(), &h + &one),
            ] {
                assert_eq!(name(&l, &h), None, "{n}: {l}..={h}");
            }
        }
    }

    #[test]
    fn other_names_and_ranges_are_no_alias() {
        for n in [
            "i0", "i1", "i9", "i08", "u+8", "u256", "i", "u", "int", "x64", "",
        ] {
            assert!(!is_alias(n), "{n}");
        }
        let b = BigInt::from;
        // Powers of two that are no width, an empty range, and a range of one value.
        assert_eq!(name(&b(0), &b(3)), None);
        assert_eq!(name(&b(-4), &b(3)), None);
        assert_eq!(name(&b(0), &b(-1)), None);
        assert_eq!(name(&b(0), &b(0)), None);
        let big = BigInt::from(1) << 256u32;
        assert_eq!(name(&b(0), &(&big - 1)), None);
        assert_eq!(name(&-(&big >> 1u32), &((&big >> 1u32) - 1)), None);
    }

    #[test]
    fn a_wide_kept_power_is_no_alias_and_is_not_written_out() {
        // 3^200000 is held as a kept power; `name_of` reads its bound, not its 95,425 digits.
        let three = zed_kernel::num::Rat::int(BigInt::from(3));
        let p = three
            .pow(&num_bigint::BigUint::from(200000u32))
            .expect("a kept power is built without its digits");
        assert!(!p.kept().2.is_empty(), "3^200000 is held as a kept power");
        let p = Value::integer(p);
        assert_eq!(name_of(&Value::int(BigInt::from(0)), &p), None);
        assert_eq!(name_of(&p, &p), None);
    }
}
