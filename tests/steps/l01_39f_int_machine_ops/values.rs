//! The cases DESIGN.md step L1.39f names, through the surface, and each word at zero, all ones
//! and the top digit, with shift counts of 0 and `width - 1` and masks of zero and all ones.

use zed_kernel::{Prim, Value};

use super::{word, x};

#[test]
fn the_named_cases() {
    assert_eq!(x("mulHi(2 ^ 63, 4, width: 64)"), "2");
    assert_eq!(
        x("mulHi(2 ^ 64 - 1, 2 ^ 64 - 1, width: 64)"),
        (u128::from(u64::MAX) - 1).to_string()
    );
    assert_eq!(x("bitReverse(1, width: 8)"), "128");
    assert_eq!(x("byteSwap(0x0102, width: 16)"), "513");
    assert_eq!(x("pdep(0b101, 0b11010)"), "18");
    assert_eq!(x("pext(0b10010, 0b11010)"), "5");
    assert_eq!(x("funnelShl(1, 0, 0, width: 8)"), "1");
}

#[test]
fn a_receiver_is_the_first_operand() {
    assert_eq!(x("3.mulHi(2 ^ 63, width: 64)"), "1");
    assert_eq!(x("0x80.bitReverse(width: 8)"), "1");
    assert_eq!(x("0xA1B2.byteSwap(width: 16)"), "45729");
    assert_eq!(x("0b11.pdep(0b1001)"), "9");
    assert_eq!(x("0b1001.pext(0b1001)"), "3");
    assert_eq!(x("0xF0.funnelShr(0x0F, 4, width: 8)"), "0");
}

#[test]
fn bit_reverse_is_an_involution_and_pext_undoes_pdep() {
    for w in [1i64, 7, 8, 13, 16] {
        for v in [0i64, 1, 0b1011, (1 << w) - 1, 1 << (w - 1)] {
            if v >= 1 << w {
                continue;
            }
            let r = word(Prim::BitReverse, &[v, w]);
            let Value::Int(r) = r else { panic!("{r}") };
            assert_eq!(word(Prim::BitReverse, &[r, w]), Value::Int(v), "{v} {w}");
        }
    }
    for m in [0i64, 1, 0b11010, 0xF0F0, i64::MAX] {
        let ones = i64::from(m.count_ones());
        for v in [0i64, 1, 0b101, 0x7FFF] {
            // `pdep` keeps only the `popCount(m)` low digits of `v`.
            let kept = if ones >= 63 { v } else { v & ((1 << ones) - 1) };
            let Value::Int(d) = word(Prim::Pdep, &[v, m]) else {
                panic!("pdep of machine values")
            };
            assert_eq!(word(Prim::Pext, &[d, m]), Value::Int(kept), "{v} {m}");
        }
    }
}

#[test]
fn funnel_shl_of_one_word_twice_is_rotl() {
    for w in [1i64, 5, 8, 32, 63] {
        let top = 1i64 << (w - 1);
        for v in [0i64, 1, top, top | 1, (top - 1) | top] {
            for k in [0, 1.min(w - 1), w / 2, w - 1] {
                assert_eq!(
                    word(Prim::FunnelShl, &[v, v, k, w]),
                    word(Prim::Rotl, &[v, k, w]),
                    "{v} {k} {w}"
                );
                assert_eq!(
                    word(Prim::FunnelShr, &[v, v, k, w]),
                    word(Prim::Rotr, &[v, k, w]),
                    "{v} {k} {w}"
                );
            }
        }
    }
    assert_eq!(
        x("funnelShl(0b1011, 0b1011, 3, width: 4)"),
        x("rotl(0b1011, 3, width: 4)")
    );
}

#[test]
fn zero_all_ones_and_the_top_digit_through_the_surface() {
    let p64 = "18446744073709551615";
    for (e, v) in [
        ("mulHi(0, 2 ^ 64 - 1, width: 64)", "0"),
        ("mulHi(2 ^ 63, 2 ^ 63, width: 64)", "4611686018427387904"),
        ("mulHi(2 ^ 127, 2, width: 128)", "1"),
        ("bitReverse(0, width: 64)", "0"),
        ("bitReverse(2 ^ 64 - 1, width: 64)", p64),
        ("bitReverse(2 ^ 63, width: 64)", "1"),
        (
            "bitReverse(1, width: 128)",
            "170141183460469231731687303715884105728",
        ),
        ("byteSwap(0, width: 64)", "0"),
        ("byteSwap(2 ^ 64 - 1, width: 64)", p64),
        ("byteSwap(2 ^ 63, width: 64)", "128"),
        ("byteSwap(0, width: 0)", "0"),
        ("pdep(2 ^ 64 - 1, 0)", "0"),
        ("pdep(12345, 2 ^ 64 - 1)", "12345"),
        ("pdep(2 ^ 70 + 5, 2 ^ 64 - 1)", "5"),
        ("pext(2 ^ 64 - 1, 0)", "0"),
        ("pext(2 ^ 70 + 5, 2 ^ 64 - 1)", "5"),
        ("pext(2 ^ 63, 2 ^ 63)", "1"),
        ("funnelShl(2 ^ 63, 0, 1, width: 64)", "0"),
        ("funnelShl(0, 2 ^ 63, 1, width: 64)", "1"),
        (
            "funnelShl(2 ^ 64 - 1, 0, 63, width: 64)",
            "9223372036854775808",
        ),
        ("funnelShr(1, 0, 1, width: 64)", "9223372036854775808"),
        ("funnelShr(0, 2 ^ 64 - 1, 63, width: 64)", "1"),
        ("funnelShr(2 ^ 64 - 1, 2 ^ 64 - 1, 0, width: 64)", p64),
    ] {
        assert_eq!(x(e), v, "{e}");
    }
}

#[test]
fn byte_swap_reverses_the_bytes_of_a_word() {
    assert_eq!(
        x("byteSwap(0x0102030405060708, width: 64)"),
        "578437695752307201"
    );
    assert_eq!(x("byteSwap(0x0102, width: 32)"), "33619968");
}
