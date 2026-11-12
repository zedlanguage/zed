//! The type errors: a negative operand, an `x` wider than its width, an operand not shown to
//! be in its domain, and a call that does not fit the word's parameters. A rejection names the
//! operand and shows its derivation; the kernel rejects the same values at run time.

use zed_kernel::{KernelError, Prim, Value};

use super::{accepted, rejected, x};

#[test]
fn a_negative_operand_is_rejected_and_the_derivation_names_it() {
    let out = rejected("x = bitAnd(-1, 1);\n");
    assert!(
        out.starts_with("1:5: `bitAnd` takes `a` in int[0..]: `bitAnd(-1 : int, 1)`.\n"),
        "{out}"
    );
    assert!(out.contains("`a` is this operand, -1"), "{out}");
    assert!(out.contains("1:12"), "the note is at the operand: {out}");
}

#[test]
fn the_derivation_follows_a_name_to_its_definition() {
    let out = rejected("offset = -8;\nx = shr(16, offset);\n");
    assert!(
        out.contains("`shr` takes `k` in int[0..]: `shr(16, offset : -8)`.\n"),
        "{out}"
    );
    assert!(
        out.contains("`offset` is defined as this expression"),
        "{out}"
    );
}

#[test]
fn each_operand_is_checked() {
    for (src, msg) in [
        ("x = bitOr(1, -2);\n", "`bitOr` takes `b` in int[0..]"),
        ("x = bitXor(-1, 0);\n", "`bitXor` takes `a` in int[0..]"),
        ("x = popCount(-3);\n", "`popCount` takes `x` in int[0..]"),
        ("x = shl(1, -1);\n", "`shl` takes `k` in int[0..]"),
        (
            "x = bitNot(1, width: -1);\n",
            "`bitNot` takes `width` in int[0..]",
        ),
        (
            "x = rotl(1, -1, width: 4);\n",
            "`rotl` takes `k` in int[0..]",
        ),
        (
            "x = leadingZeros(-1, width: 4);\n",
            "`leadingZeros` takes `x` in int[0..]",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(msg), "{src}: {out}");
    }
}

#[test]
fn an_x_wider_than_its_width_is_rejected() {
    let out = rejected("x = bitNot(8, width: 3);\n");
    assert!(
        out.contains("`bitNot` takes `x` in int[0..<2^width], and this `x` is 8 with `width` 3"),
        "{out}"
    );
    assert!(out.contains("`width` is this operand, 3"), "{out}");
    let out = rejected("x = rotr(2^64, 1, width: 64);\n");
    assert!(
        out.contains("`rotr` takes `x` in int[0..<2^width]"),
        "{out}"
    );
    assert!(accepted("x = rotr(2^64 - 1, 1, width: 64);\n"));
    assert!(accepted("x = trailingZeros(255, width: 8);\n"));
    assert!(!accepted("x = trailingZeros(256, width: 8);\n"));
}

#[test]
fn an_operand_not_shown_in_its_domain_is_rejected() {
    // `int(s)` may be any int, so it may be negative.
    let out = rejected(
        "main(m: MainArgs) {\n  n = int(m.stdin[0]) else 0;\n  \
         m.stdout <- String(popCount(n));\n}\n",
    );
    assert!(
        out.contains(
            "`popCount` takes `x` in int[0..]: `popCount(n : int)`. Try \
             `if n >= 0 { popCount(n) } else { … }` instead.\n"
        ),
        "{out}"
    );
    // A test narrows the operand in the arm where it holds (`narrowing`), and in the other arm
    // shows it is negative.
    let out = rejected(
        "main(m: MainArgs) {\n  n = int(m.stdin[0]) else 0;\n  \
         m.stdout <- if n >= 0 { \"\" } else { String(popCount(n)) };\n}\n",
    );
    assert!(
        out.contains("`popCount` takes `x` in int[0..]: `popCount(n : int[..=-1])`.\n"),
        "{out}"
    );
}

#[test]
fn shown_operands_are_accepted() {
    assert!(accepted("x = bitAnd(shl(1, 3), 5);\n"));
    assert!(accepted("x = popCount(2^64 + 1);\n"));
    assert!(accepted("x = shl(-5, 2);\nlow = shr(-5, 1);\n"));
    assert!(accepted("mask = 255;\nx = bitAnd(51966, mask);\n"));
    assert!(accepted("x = 12.bitAnd(10).bitXor(3);\n"));
}

#[test]
fn a_call_that_does_not_fit_is_rejected() {
    let out = rejected("x = bitNot(5, 3);\n");
    assert!(
        out.contains("one more than") || out.contains("is a named parameter"),
        "{out}"
    );
    let out = rejected("x = bitNot(5);\n");
    assert!(
        out.contains("gives no value to its parameter `width`"),
        "{out}"
    );
    let out = rejected("x = bitAnd(1, b: 2);\n");
    assert!(out.contains("`b` of"), "{out}");
    // A bare literal at an `f64` parameter is the `f64` it names (L1.26a); an int value is
    // rejected.
    assert_eq!(x("f64Bits(1)"), x("f64Bits(1.0)"));
    assert_eq!(x("f64Bits(1)"), "4607182418800017408");
    let out = rejected("i = 3 + 4;\nx = f64Bits(i);\n");
    assert!(out.contains("f64Bits"), "{out}");
    // A float literal is rejected at the literal, a float value at the call.
    let out = rejected("x = bitAnd(1.5, 1);\n");
    assert!(
        out.contains("A decimal literal is never an `int`: the literal `1.5`"),
        "{out}"
    );
    let out = rejected("f = 1.5f64;\nx = bitAnd(f, 1);\n");
    assert!(out.contains("bitAnd"), "{out}");
}

#[test]
fn the_kernel_rejects_values_outside_the_domain() {
    let err = |p: Prim, args: &[i64]| {
        let vs: Vec<Value> = args.iter().map(|&a| Value::Int(a)).collect();
        match zed_kernel::bits::word(p, &vs) {
            Err(KernelError::Type(m)) => m,
            other => panic!("{p:?} {args:?}: {other:?}"),
        }
    };
    assert_eq!(
        err(Prim::BitAnd, &[-1, 1]),
        "`bitAnd` needs `a` in int[0..], and it is negative"
    );
    assert_eq!(
        err(Prim::BitNot, &[8, 3]),
        "`bitNot` needs `x` in int[0..<2^width], and it is at least 2^width"
    );
    assert_eq!(
        err(Prim::Rotl, &[1, -1, 3]),
        "`rotl` needs `k` in int[0..], and it is negative"
    );
    assert_eq!(
        err(Prim::Shr, &[1, -1]),
        "`shr` needs `k` in int[0..], and it is negative"
    );
}

#[test]
fn a_name_carries_what_its_text_shows() {
    // `k` is bound to `2 + 1`, which its text shows is 3, and `low` to a bit word of known
    // operands; both are shown non-negative through the name.
    assert!(accepted(
        "k = 2 + 1;\nx = shr(1024, k);\nlow = bitAnd(x, 255);\ny = popCount(low);\n"
    ));
    assert!(accepted("k = 2 + 1;\ny = 2^k;\n"));
    let out = rejected("k = 2 - 3;\ny = popCount(k);\n");
    assert!(
        out.contains("`popCount` takes `x` in int[0..]: `popCount(k : -1)`.\n"),
        "{out}"
    );
    let out = rejected("w = 4 + 0;\ny = bitNot(16, width: w);\n");
    assert!(out.contains("and this `x` is 16 with `width` 4"), "{out}");
}

#[test]
fn bit_words_nested_in_each_other_are_each_checked_with_the_inner_values() {
    // Positional, named and receiver arguments that are themselves calls of bit words.
    assert!(accepted("x = bitAnd(bitOr(bitXor(6, 3), 1), 7);\n"));
    assert!(accepted(
        "x = leadingZeros(bitAnd(255, 15), width: bitOr(4, 4));\n"
    ));
    assert!(accepted("x = 6.bitOr(1).bitAnd(bitXor(2, 1));\n"));
    // `bitXor(6, 3)` is 5, so the outer `a` is -1.
    let out = rejected("x = bitAnd(bitXor(6, 3) - 6, 1);\n");
    assert!(
        out.starts_with(
            "1:5: `bitAnd` takes `a` in int[0..]: `bitAnd(bitXor(6, 3) - 6 : -1, 1)`.\n"
        ),
        "{out}"
    );
    // The width is 2, and 15 does not lie below `2 ^ 2`.
    let out = rejected("x = leadingZeros(bitAnd(255, 15), width: bitAnd(6, 3));\n");
    assert!(out.contains("takes `x` in int[0..<2^width]"), "{out}");
}
