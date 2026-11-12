//! `utf8` and `fromUtf8` on the kernel's values: the encoding at every boundary of the ranges of
//! UTF-8 lengths, the round trip over every string of up to 4 scalars of 1, 2, 3 and 4 bytes, and
//! each form of bytes that is not well-formed UTF-8 (the Unicode Standard, table 3-7).

use zed_kernel::term::build::{lit, prim};
use zed_kernel::value::Family;
use zed_kernel::{KernelError, Prim, Value};

use super::{BOUNDARIES, from_one, from_zero, word};

fn bad() -> Value {
    Value::atom("badUtf8")
}

#[test]
fn every_boundary_round_trips_with_its_bytes() {
    for c in BOUNDARIES {
        let ch = char::from_u32(c).unwrap();
        let s = word(Prim::Scalar, Value::Int(i64::from(c)));
        assert_eq!(s, Value::str(&ch.to_string()), "{c:#x}");
        let want: Vec<i64> = ch.to_string().bytes().map(i64::from).collect();
        let b = word(Prim::Utf8, s.clone());
        assert_eq!(b, from_zero(&want), "{c:#x}");
        assert_eq!(word(Prim::FromUtf8, b), s, "{c:#x}");
        assert_eq!(word(Prim::CodePoint, s), Value::Int(i64::from(c)), "{c:#x}");
    }
}

#[test]
fn the_lengths_change_at_the_boundaries() {
    let len = |c: u32| match word(Prim::Utf8, word(Prim::Scalar, Value::Int(i64::from(c)))) {
        Value::Family(f) => f.len(),
        v => panic!("{v}"),
    };
    let lens: Vec<usize> = BOUNDARIES.iter().map(|&c| len(c)).collect();
    assert_eq!(lens, [1, 1, 2, 2, 3, 3, 3, 3, 4, 4]);
}

#[test]
fn every_string_of_up_to_four_scalars_round_trips() {
    // One scalar of each length in bytes.
    let alphabet = ['a', 'é', '€', '😀'];
    let mut strings = vec![String::new()];
    let mut last = vec![String::new()];
    for _ in 0..4 {
        last = last
            .iter()
            .flat_map(|s| alphabet.iter().map(move |c| format!("{s}{c}")))
            .collect();
        strings.extend(last.iter().cloned());
    }
    assert_eq!(strings.len(), 1 + 4 + 16 + 64 + 256);
    for s in &strings {
        // `fromUtf8(utf8(s)) == s`, as one term.
        let t = prim(
            Prim::Eq,
            vec![
                prim(
                    Prim::FromUtf8,
                    vec![prim(Prim::Utf8, vec![lit(s.as_str())])],
                ),
                lit(s.as_str()),
            ],
        );
        assert_eq!(zed_kernel::eval(&t).unwrap(), Value::Bool(true), "{s}");
    }
}

#[test]
fn every_scalar_at_a_stride_round_trips() {
    // Every 97th scalar value, and each one beside a boundary.
    let near = BOUNDARIES
        .iter()
        .flat_map(|&c| [c.saturating_sub(1), c, c + 1])
        .filter(|&c| c <= 0x10FFFF);
    for c in (0..=0x10FFFFu32).step_by(97).chain(near) {
        let s = word(Prim::Scalar, Value::Int(i64::from(c)));
        match char::from_u32(c) {
            Some(_) => {
                let b = word(Prim::Utf8, s.clone());
                assert_eq!(word(Prim::FromUtf8, b), s, "{c:#x}");
                assert_eq!(word(Prim::CodePoint, s), Value::Int(i64::from(c)));
            }
            None => assert_eq!(s, Value::atom("notScalar"), "{c:#x}"),
        }
    }
}

/// `utf8` keys each byte by its offset from 0, as an array and every other byte family are, so
/// the keys are exactly `0 ..< n` for `n` bytes, the first byte at key 0 and the last at `n - 1`.
#[test]
fn the_keys_are_the_byte_offsets_from_zero() {
    for s in ["", "a", "é", "a😀b", &"aé€😀".repeat(100)] {
        let f = match word(Prim::Utf8, Value::str(s)) {
            Value::Family(f) => f,
            v => panic!("{v}"),
        };
        let keys: Vec<Value> = f.iter().map(|(k, _)| k.clone()).collect();
        let offsets: Vec<Value> = (0..s.len()).map(|i| Value::Int(i as i64)).collect();
        assert_eq!(keys, offsets, "{s}");
        let bytes: Vec<i64> = s.bytes().map(i64::from).collect();
        assert_eq!(Value::Family(f), from_zero(&bytes), "{s}");
    }
}

#[test]
fn the_named_overlong_pair_is_bad() {
    // `fromUtf8([192, 128])`: the array display keys from 0; the bytes are read in key order.
    assert_eq!(word(Prim::FromUtf8, from_zero(&[192, 128])), bad());
    assert_eq!(word(Prim::FromUtf8, from_one(&[192, 128])), bad());
}

#[test]
fn bytes_are_read_in_key_order() {
    assert_eq!(
        word(Prim::FromUtf8, from_zero(&[104, 105])),
        Value::str("hi")
    );
    let gaps = Value::Family(Family::of([(3i64, 105i64), (-2, 104)]));
    assert_eq!(word(Prim::FromUtf8, gaps), Value::str("hi"));
}

#[test]
fn overlong_forms_are_bad() {
    for b in [
        &[0xC0, 0x80][..],
        &[0xC1, 0xBF],
        &[0xE0, 0x80, 0x80],
        &[0xE0, 0x9F, 0xBF],
        &[0xF0, 0x80, 0x80, 0x80],
        &[0xF0, 0x8F, 0xBF, 0xBF],
    ] {
        assert_eq!(word(Prim::FromUtf8, from_zero(b)), bad(), "{b:x?}");
    }
    // The shortest forms of the same ends are good.
    assert_eq!(
        word(Prim::FromUtf8, from_zero(&[0xC2, 0x80])),
        Value::str("\u{80}")
    );
    assert_eq!(
        word(Prim::FromUtf8, from_zero(&[0xE0, 0xA0, 0x80])),
        Value::str("\u{800}")
    );
    assert_eq!(
        word(Prim::FromUtf8, from_zero(&[0xF0, 0x90, 0x80, 0x80])),
        Value::str("\u{10000}")
    );
}

#[test]
fn surrogates_and_scalars_past_the_last_are_bad() {
    for b in [
        &[0xED, 0xA0, 0x80][..],
        &[0xED, 0xBF, 0xBF],
        &[0xF4, 0x90, 0x80, 0x80],
        &[0xF5, 0x80, 0x80, 0x80],
        &[0xFF],
        &[0xFE],
    ] {
        assert_eq!(word(Prim::FromUtf8, from_zero(b)), bad(), "{b:x?}");
    }
    assert_eq!(
        word(Prim::FromUtf8, from_zero(&[0xED, 0x9F, 0xBF])),
        Value::str("\u{D7FF}")
    );
    assert_eq!(
        word(Prim::FromUtf8, from_zero(&[0xF4, 0x8F, 0xBF, 0xBF])),
        Value::str("\u{10FFFF}")
    );
}

#[test]
fn truncated_and_stray_continuation_bytes_are_bad() {
    for b in [
        &[0xC3][..],
        &[0xE2, 0x82],
        &[0xF0, 0x9F, 0x98],
        &[0x61, 0xF0, 0x9F],
        &[0x80],
        &[0xBF],
        &[0x61, 0x80, 0x62],
        &[0xC3, 0xA9, 0xA9],
        &[0xC3, 0x41],
    ] {
        assert_eq!(word(Prim::FromUtf8, from_zero(b)), bad(), "{b:x?}");
    }
}

#[test]
fn an_int_that_is_not_a_byte_is_bad() {
    for b in [&[256][..], &[-1], &[97, 300]] {
        assert_eq!(word(Prim::FromUtf8, from_zero(b)), bad(), "{b:?}");
    }
    let big = Value::int(num_bigint::BigInt::from(1u8) << 80);
    let f = Value::Family(Family::of([(Value::Int(1), big)]));
    assert_eq!(word(Prim::FromUtf8, f), bad());
}

#[test]
fn the_empty_family_is_the_empty_string() {
    assert_eq!(word(Prim::FromUtf8, from_zero(&[])), Value::str(""));
    assert_eq!(word(Prim::Utf8, Value::str("")), from_zero(&[]));
}

#[test]
fn a_value_of_another_kind_is_a_type_error() {
    let t = |p: Prim, v: Value| {
        let t = prim(p, vec![zed_kernel::Term::Lit(v)]);
        zed_kernel::eval(&t)
    };
    let strings = Value::Family(Family::of([(1i64, "a")]));
    for (p, v) in [
        (Prim::FromUtf8, strings),
        (Prim::FromUtf8, Value::str("a")),
        (Prim::CodePoint, Value::Int(97)),
        (Prim::Scalar, Value::str("a")),
        (Prim::Scalar, Value::float(97.0)),
        (Prim::Utf8, Value::Int(1)),
    ] {
        let r = t(p, v);
        assert!(matches!(r, Err(KernelError::Type(_))), "{p:?}: {r:?}");
    }
}

#[test]
fn an_atom_passes_through() {
    for p in [Prim::CodePoint, Prim::Scalar, Prim::Utf8, Prim::FromUtf8] {
        assert_eq!(
            word(p, Value::atom("missing")),
            Value::atom("missing"),
            "{p:?}"
        );
    }
}
