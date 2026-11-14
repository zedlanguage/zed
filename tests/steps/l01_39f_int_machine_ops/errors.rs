//! The type errors: a negative operand, an operand read as `width` digits that is not below
//! `2 ^ width`, a funnel shift's `k` that is not below `width`, and a width of `byteSwap` that
//! is not a multiple of 8. A rejection names the operand and shows its derivation; the kernel
//! rejects the same values at run time.

use zed_kernel::{KernelError, Prim, Value};

use super::{accepted, rejected};

#[test]
fn byte_swap_of_width_12_is_a_type_error_naming_the_width() {
    let out = rejected("x = byteSwap(0x0102, width: 12);\n");
    assert!(
        out.starts_with(
            "1:5: `byteSwap` takes `width` a multiple of 8 in int[0..]: \
             `byteSwap(0x0102, width: 12 : int)`. Try `byteSwap(0x0102, width: 16)` instead."
        ),
        "{out}"
    );
    assert!(out.contains("`width` is this operand, 12"), "{out}");
    assert!(accepted("x = byteSwap(0x0102, width: 16);\n"));
    // A width not shown to be a multiple of 8 is rejected too.
    let out = rejected("w = 8 + 4;\nx = byteSwap(1, width: w);\n");
    assert!(
        out.contains(
            "`byteSwap` takes `width` a multiple of 8 in int[0..]: `byteSwap(1, width: w : 12)`.\n"
        ),
        "{out}"
    );
    assert!(accepted("w = 8 * 3;\nx = byteSwap(1, width: w);\n"));
}

#[test]
fn a_funnel_shift_by_the_width_is_a_type_error_naming_k() {
    let out = rejected("x = funnelShl(3, 5, 8, width: 8);\n");
    assert!(
        out.starts_with(
            "1:5: `funnelShl` takes `k` in int[0..<8]: `funnelShl(3, 5, 8 : int, width: 8)`. \
             Try `funnelShl(3, 5, 8, width: 9)` instead."
        ),
        "{out}"
    );
    assert!(out.contains("`k` is this operand, 8"), "{out}");
    assert!(out.contains("`width` is this operand, 8"), "{out}");
    // Each with the width its repair writes, which is then accepted; a width of 0 holds no `k`,
    // so the domain is written at `width`.
    for (src, msg, fixed) in [
        (
            "x = funnelShr(3, 5, 9, width: 8);\n",
            "takes `k` in int[0..<8]: `funnelShr(3, 5, 9 : int, width: 8)`. \
             Try `funnelShr(3, 5, 9, width: 10)` instead.",
            "x = funnelShr(3, 5, 9, width: 10);\n",
        ),
        (
            "x = funnelShl(0, 0, 0, width: 0);\n",
            "takes `k` in int[0..<width]: `funnelShl(0, 0, 0 : int, width: 0)`. \
             Try `funnelShl(0, 0, 0, width: 1)` instead.",
            "x = funnelShl(0, 0, 0, width: 1);\n",
        ),
        (
            "k = 70;\nx = funnelShr(1, 1, k, width: 64);\n",
            "takes `k` in int[0..<64]: `funnelShr(1, 1, k : 70, width: 64)`. \
             Try `funnelShr(1, 1, k, width: 71)` instead.",
            "k = 70;\nx = funnelShr(1, 1, k, width: 71);\n",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(msg), "{src}: {out}");
        assert!(accepted(fixed), "{fixed}");
    }
    assert!(accepted("x = funnelShl(3, 5, 8, width: 9);\n"));
    assert!(accepted("x = funnelShl(3, 5, 7, width: 8);\n"));
    assert!(accepted("x = funnelShr(3, 5, 0, width: 8);\n"));
}

#[test]
fn each_operand_read_as_width_digits_is_checked() {
    for (src, msg) in [
        (
            "x = mulHi(2^64, 1, width: 64);\n",
            "`mulHi` takes `a` in int[0..<2^64]: `mulHi(2^64 : 18446744073709551616, 1, width: 64)`. \
             Try `mulHi(2^64, 1, width: 65)` instead.",
        ),
        (
            "x = mulHi(1, 256, width: 8);\n",
            "`mulHi` takes `b` in int[0..<2^8]: `mulHi(1, 256 : int, width: 8)`. \
             Try `mulHi(1, 256, width: 9)` instead.",
        ),
        (
            "x = bitReverse(256, width: 8);\n",
            "`bitReverse` takes `x` in int[0..<2^8]: `bitReverse(256 : int, width: 8)`. \
             Try `bitReverse(256, width: 9)` instead.",
        ),
        (
            "x = byteSwap(65536, width: 16);\n",
            "`byteSwap` takes `x` in int[0..<2^16]: `byteSwap(65536 : int, width: 16)`. \
             Try `byteSwap(65536, width: 32)` instead.",
        ),
        (
            "x = funnelShl(256, 0, 1, width: 8);\n",
            "`funnelShl` takes `hi` in int[0..<2^8]: `funnelShl(256 : int, 0, 1, width: 8)`. \
             Try `funnelShl(256, 0, 1, width: 9)` instead.",
        ),
        (
            "x = funnelShr(0, 256, 1, width: 8);\n",
            "`funnelShr` takes `lo` in int[0..<2^8]: `funnelShr(0, 256 : int, 1, width: 8)`. \
             Try `funnelShr(0, 256, 1, width: 9)` instead.",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(msg), "{src}: {out}");
        tried_is_accepted(&out);
    }
    assert!(accepted("x = mulHi(2^64 - 1, 2^64 - 1, width: 64);\n"));
    assert!(accepted("x = bitReverse(255, width: 8);\n"));
}

#[test]
fn a_negative_operand_is_rejected() {
    for (src, msg) in [
        (
            "x = mulHi(-1, 1, width: 8);\n",
            "`mulHi` takes `a` in int[0..<2^8]: `mulHi(-1 : int, 1, width: 8)`.\n",
        ),
        (
            "x = bitReverse(-1, width: 8);\n",
            "`bitReverse` takes `x` in int[0..<2^8]: `bitReverse(-1 : int, width: 8)`.\n",
        ),
        (
            "x = byteSwap(1, width: -8);\n",
            "`byteSwap` takes `width` a multiple of 8 in int[0..]: `byteSwap(1, width: -8 : int)`. \
             Try `byteSwap(1, width: 8)` instead.",
        ),
        (
            "x = pdep(-1, 3);\n",
            "`pdep` takes `x` in int[0..]: `pdep(-1 : int, 3)`.\n",
        ),
        (
            "x = pext(1, -3);\n",
            "`pext` takes `mask` in int[0..]: `pext(1, -3 : int)`.\n",
        ),
        (
            "x = funnelShl(1, 1, -1, width: 8);\n",
            "`funnelShl` takes `k` in int[0..<8]: `funnelShl(1, 1, -1 : int, width: 8)`.\n",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(msg), "{src}: {out}");
        tried_is_accepted(&out);
    }
}

#[test]
fn the_derivation_follows_a_name_to_its_definition() {
    let out = rejected("shift = 4 + 4;\nx = funnelShl(1, 2, shift, width: 8);\n");
    assert!(
        out.contains("`shift` is defined as this expression"),
        "{out}"
    );
}

#[test]
fn the_kernel_rejects_the_same_values_at_run_time() {
    let err = |p: Prim, args: &[i64]| {
        let vs: Vec<Value> = args.iter().map(|&a| Value::Int(a)).collect();
        match zed_kernel::bits::word(p, &vs) {
            Err(KernelError::Type(m)) => m,
            other => panic!("{p:?} {args:?} gave {other:?}"),
        }
    };
    assert_eq!(
        err(Prim::ByteSwap, &[1, 12]),
        "`byteSwap` needs `width` a multiple of 8, and it is not"
    );
    assert_eq!(
        err(Prim::FunnelShl, &[3, 5, 8, 8]),
        "`funnelShl` needs `k` in int[0..<width], and it is at least width"
    );
    assert_eq!(
        err(Prim::FunnelShr, &[3, 5, 1000, 8]),
        "`funnelShr` needs `k` in int[0..<width], and it is at least width"
    );
    assert_eq!(
        err(Prim::BitReverse, &[256, 8]),
        "`bitReverse` needs `x` in int[0..<2^width], and it is at least 2^width"
    );
    assert_eq!(
        err(Prim::Pext, &[1, -1]),
        "`pext` needs `mask` in int[0..], and it is negative"
    );
    // The exact path: an operand past `i64`.
    let big = Value::int(num_bigint::BigInt::from(1u128 << 64));
    let out = zed_kernel::bits::word(Prim::MulHi, &[big, Value::Int(1), Value::Int(64)]);
    assert!(
        matches!(&out, Err(KernelError::Type(m)) if m.contains("`a` in int[0..<2^width]")),
        "{out:?}"
    );
}

/// The call a headline's "Try `…` instead" writes, put back in place of `x = …;`, is accepted.
fn tried_is_accepted(out: &str) {
    if let Some(tried) = out.split("Try `").nth(1).and_then(|t| t.split('`').next()) {
        let fixed = format!("x = {tried};\n");
        assert!(accepted(&fixed), "{fixed}: {out}");
    }
}

/// DIAG-pdep-wrong-operand-note: where one operand of `pdep` or `pext` is of another kind,
/// the note naming the `/` that gives it lies at that operand, first or second, and the
/// carrier error that follows points at it too, never at the other operand.
#[test]
fn the_note_for_an_operand_of_another_kind_lies_at_that_operand() {
    for word in ["pdep", "pext"] {
        // `x = w(1, 1/2);`: the `/` starts after `x = `, the word, `(1, 1`.
        let second = 4 + word.len() + 5;
        let first = 4 + word.len() + 2;
        for (src, at, other) in [
            (format!("x = {word}(1, 1/2);\n"), second, first),
            (format!("x = {word}(1/2, 1);\n"), first, first + 5),
        ] {
            let m = rejected(&src);
            let note = format!("1:{at}: this `/`");
            assert!(m.contains(&note), "{src}: no note `{note}` in\n{m}");
            let wrong = format!("1:{other}: this `/`");
            assert!(
                !m.contains(&wrong),
                "{src}: a `/` note at the other operand in\n{m}"
            );
            let carrier = format!("\n1:{at}: Nothing gives the literal");
            assert!(m.contains(&carrier), "{src}: no `{carrier}` in\n{m}");
        }
    }
}
