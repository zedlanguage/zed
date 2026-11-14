//! The cases of COMPLETENESS.md that the other files leave open: each word in every syntactic
//! position (a function body under tests that bound its operands, a lambda, a tuple, an
//! interpolation, an argument of another word), the forms of its arguments, operands of other
//! kinds, and the bounds of DESIGN's forward transfer read back through the domain of a second
//! word. A refinement type such as `int[0..=255]` on a parameter is compiled from step L10.1,
//! so operands are bounded here by tests (DESIGN L1.39: a test narrows a scope).

use zed_kernel::{KernelError, Prim, Value};

use super::{accepted, rejected, x};

/// Whether every row of every table of `src` passes, and there is one.
fn rows_pass(src: &str) -> bool {
    let out = zedc::testing::test(src);
    !out.is_empty() && out.iter().all(|o| o.failure.is_none())
}

/// A function of `a` and `b` whose body is `body`, under the test that both are below `2^16`.
fn under_16_digits(body: &str) -> String {
    format!(
        "f(positional a: int, positional b: int) =\n  \
         if a >= 0 && a < 2^16 && b >= 0 && b < 2^16 {{ {body} }} else {{ 0 }};\n"
    )
}

#[test]
fn each_word_in_a_function_body_under_tests_of_its_operands() {
    for src in [
        "f(positional a: int, positional b: int) =\n  \
           if a >= 0 && a < 2^64 && b >= 0 && b < 2^64 { mulHi(a, b, width: 64) } else { 0 }\n\
         test { (2^63, 4) -> 2, (0, 7) -> 0, (-1, 1) -> 0 }\n",
        "f(positional x: int) = if x >= 0 && x < 256 { bitReverse(x, width: 8) } else { 0 }\n\
         test { 1 -> 128, 0 -> 0, 255 -> 255, -1 -> 0, 256 -> 0 }\n",
        "f(positional x: int) = if x >= 0 && x < 2^16 { byteSwap(x, width: 16) } else { 0 }\n\
         test { 0x0102 -> 0x0201, 0 -> 0 }\n",
        "f(positional x: int, positional m: int) = if x >= 0 && m >= 0 { pdep(x, m) } else { 0 }\n\
         test { (0b101, 0b11010) -> 0b10010, (5, 0) -> 0, (-5, 1) -> 0 }\n",
        "f(positional x: int, positional m: int) = if x >= 0 && m >= 0 { pext(x, m) } else { 0 }\n\
         test { (0b10010, 0b11010) -> 0b101, (5, 0) -> 0 }\n",
        "f(positional x: int) = if x < 0 { 0 } else { pdep(x, 0b11010) }\n\
         test { 0b101 -> 0b10010, -3 -> 0 }\n",
        "f(positional k: int) = if k >= 0 && k < 8 { funnelShl(1, 0x80, k, width: 8) } else { 0 }\n\
         test { 0 -> 1, 1 -> 3, 8 -> 0 }\n",
        "f(positional k: int) = if k >= 0 && k < 8 { funnelShr(1, 0, k, width: 8) } else { 0 }\n\
         test { 1 -> 0x80, 0 -> 0, -1 -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
}

#[test]
fn an_operand_not_bounded_by_its_tests_is_rejected_at_each_word() {
    for (src, msg) in [
        (
            "f(positional a: int) = mulHi(a, 1, width: 8);\n",
            "`mulHi` takes `a` in int[0..<2^8]: `mulHi(a : int, 1, width: 8)`",
        ),
        (
            "f(positional x: int) = bitReverse(x, width: 8);\n",
            "`bitReverse` takes `x` in int[0..<2^8]: `bitReverse(x : int, width: 8)`",
        ),
        (
            "f(positional x: int) = byteSwap(x, width: 16);\n",
            "`byteSwap` takes `x` in int[0..<2^16]: `byteSwap(x : int, width: 16)`",
        ),
        (
            "f(positional m: int) = pdep(1, m);\n",
            "`pdep` takes `mask` in int[0..]: `pdep(1, m : int)`",
        ),
        (
            "f(positional x: int) = pext(x, 3);\n",
            "`pext` takes `x` in int[0..]: `pext(x : int, 3)`",
        ),
        (
            "f(positional k: int) = funnelShr(1, 1, k, width: 8);\n",
            "`funnelShr` takes `k` in int[0..<8]: `funnelShr(1, 1, k : int, width: 8)`",
        ),
        // A test that bounds one end only, or the bound one past the width.
        (
            "f(positional x: int) = if x >= 0 { bitReverse(x, width: 8) } else { 0 };\n",
            "`bitReverse` takes `x` in int[0..<2^8]",
        ),
        (
            "f(positional x: int) = if x >= 0 && x <= 256 { bitReverse(x, width: 8) } else { 0 };\n",
            "`bitReverse` takes `x` in int[0..<2^8]",
        ),
        (
            "f(positional k: int) = if k >= 0 && k <= 8 { funnelShl(1, 1, k, width: 8) } else { 0 };\n",
            "`funnelShl` takes `k` in int[0..<8]",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(msg), "{src}: {out}");
    }
}

#[test]
fn each_word_in_other_positions() {
    // A tuple component, an interpolation, an argument of another word and of itself.
    assert_eq!(
        x("(bitReverse(1, width: 8), byteSwap(0x0102, width: 16))"),
        "(128, 513)"
    );
    assert_eq!(x("\"${mulHi(2^63, 4, width: 64)}\""), "\"2\"");
    assert_eq!(x("pext(pdep(0b101, 0b11010), 0b11010)"), "5");
    assert_eq!(x("bitReverse(bitReverse(6, width: 8), width: 8)"), "6");
    assert_eq!(x("byteSwap(byteSwap(0x0102, width: 16), width: 16)"), "258");
    assert_eq!(
        x("funnelShr(0, funnelShl(0, 0x80, 1, width: 8), 1, width: 8)"),
        "0"
    );
    assert_eq!(x("mulHi(bitReverse(1, width: 8), 2, width: 8)"), "1");
    // An operand that is an arithmetic expression, and the width a name.
    assert_eq!(x("bitReverse(2 + 2, width: 4)"), "2");
    assert!(accepted("w = 16;\nx = byteSwap(0x0102, width: w);\n"));
    // A lambda passes the need of its word on to its call (DESIGN sec:domains, a type error at
    // the call).
    let lambda = "rev = v -> bitReverse(v, width: 8);\n";
    assert_eq!(
        zed_tests::step_helpers::l01_16_elaboration::value(&format!("{lambda}x = rev(1);\n"), "x"),
        "128"
    );
    let out = rejected(&format!("{lambda}x = rev(256);\n"));
    assert!(out.contains("`rev` takes `v` in int[0..<2^8]"), "{out}");
}

#[test]
fn the_width_is_the_only_named_parameter() {
    for src in [
        // `width` missing, or written positionally.
        "x = bitReverse(1);\n",
        "x = bitReverse(1, 8);\n",
        "x = mulHi(1, 2);\n",
        "x = byteSwap(1, 16);\n",
        "x = funnelShl(1, 2, 3, 8);\n",
        // An operand written by name.
        "x = bitReverse(x: 1, width: 8);\n",
        "x = pdep(x: 1, mask: 3);\n",
        // A width given to a word that takes none, an unknown name, one operand too many or
        // too few, and `width` twice.
        "x = pdep(1, 3, width: 8);\n",
        "x = pext(1, 3, width: 8);\n",
        "x = bitReverse(1, w: 8);\n",
        "x = mulHi(1, 2, 3, width: 8);\n",
        "x = pext(1);\n",
        "x = funnelShr(1, 2, width: 8);\n",
        "x = bitReverse(1, width: 8, width: 8);\n",
    ] {
        // The word named in the message, and the repairs: `arity_message.rs`.
        let out = rejected(src);
        let named = out.contains("width") || out.contains("parameter") || out.contains("position");
        assert!(named, "{src}: {out}");
    }
}

#[test]
fn an_operand_of_another_kind_is_rejected() {
    for src in [
        "x = bitReverse(1/2, width: 8);\n",
        "x = bitReverse(1.0f64, width: 8);\n",
        "x = bitReverse(\"a\", width: 8);\n",
        "x = bitReverse(true, width: 8);\n",
        "x = bitReverse((1, 2), width: 8);\n",
        "x = mulHi(1, 2.5f64, width: 8);\n",
        "x = byteSwap(1, width: 16.0f64);\n",
        "x = pdep(1, 1/2);\n",
        "x = pext(\"a\", 3);\n",
        "x = funnelShl(1, 2, 1/2, width: 8);\n",
    ] {
        // A suffixed literal is rejected at the literal; every other operand at the word.
        let out = rejected(src);
        let word = &src[4..src.find('(').unwrap()];
        let at_word = out.contains(&format!("`{word}` does not take"));
        assert!(at_word || out.contains("f64`, never `int`"), "{src}: {out}");
    }
}

#[test]
fn the_bounds_of_forward_transfer_are_read_by_a_second_word() {
    // Each bound DESIGN names (L1.39f): `mulHi`, `bitReverse` and `byteSwap` below `2^w`,
    // `pdep` at most `mask` (`pext` below `2^popCount(mask)` is FAIL-pext-transfer-popcount).
    // The result is read as the `x` of `bitReverse`, whose domain `int[0..<2^v]` holds the bound
    // at the width `v` that fits it and not at the width one less.
    for (call, fits, narrower) in [
        ("mulHi(a, b, width: 16)", 16, 15),
        ("bitReverse(a, width: 16)", 16, 15),
        ("byteSwap(a, width: 16)", 16, 15),
        // 26 is 0b11010: at most 26 fits 5 digits and not 4.
        ("pdep(a, 26)", 5, 4),
    ] {
        let at = |v: u32| under_16_digits(&format!("bitReverse({call}, width: {v})"));
        assert!(accepted(&at(fits)), "{}", at(fits));
        let out = rejected(&at(narrower));
        assert!(
            out.contains(&format!("`bitReverse` takes `x` in int[0..<2^{narrower}]")),
            "{}: {out}",
            at(narrower)
        );
    }
}

#[test]
fn a_funnel_shift_gives_a_word_of_its_width() {
    // `funnelShl(hi, lo, k, width: w)` is the high `w` digits of `hi · 2^w + lo` shifted left
    // by `k`, and `funnelShr` the low `w` digits shifted right, so each is below `2^w`.
    for call in [
        "funnelShl(a, b, 3, width: 16)",
        "funnelShr(a, b, 3, width: 16)",
    ] {
        let src = under_16_digits(&format!("bitReverse({call}, width: 16)"));
        assert!(accepted(&src), "{src}");
    }
}

#[test]
fn a_word_at_width_zero_and_one() {
    // Width 0 holds only 0; width 1 holds 0 and 1.
    assert_eq!(x("bitReverse(0, width: 0)"), "0");
    assert_eq!(x("mulHi(0, 0, width: 0)"), "0");
    assert_eq!(x("byteSwap(0, width: 0)"), "0");
    assert_eq!(x("bitReverse(1, width: 1)"), "1");
    assert_eq!(x("mulHi(1, 1, width: 1)"), "0");
    let out = rejected("x = bitReverse(1, width: 0);\n");
    assert!(out.contains("`bitReverse` takes `x`"), "{out}");
    assert_eq!(x("funnelShl(1, 0, 0, width: 1)"), "1");
    assert_eq!(x("funnelShr(1, 0, 0, width: 1)"), "0");
    // An empty mask deposits and extracts nothing; a mask of all ones is the identity.
    assert_eq!(x("pdep(7, 0)"), "0");
    assert_eq!(x("pext(7, 0)"), "0");
    assert_eq!(x("pdep(5, 15)"), "5");
    assert_eq!(x("pext(5, 15)"), "5");
    // `pdep` drops the digits of `x` past `popCount(mask)`.
    assert_eq!(x("pdep(0b111, 0b101)"), "5");
}

#[test]
fn a_failure_passes_through_each_word() {
    // A failure atom as an operand is the word's value, as under every strict word, and `else`
    // replaces it.
    assert_eq!(x("mulHi(#oops, 1, width: 8)"), "#oops");
    assert_eq!(x("bitReverse(#oops, width: 8)"), "#oops");
    assert_eq!(x("byteSwap(1, width: #late)"), "#late");
    assert_eq!(x("pdep(1, #oops)"), "#oops");
    assert_eq!(x("pext(#oops, 3)"), "#oops");
    assert_eq!(x("funnelShr(1, 1, #late, width: 8)"), "#late");
    assert_eq!(x("funnelShl(#a, #b, 1, width: 8)"), x("#a + #b"));
    assert_eq!(x("bitReverse(#oops, width: 8) else 3"), "3");
}

#[test]
fn a_width_past_the_machine_words_takes_the_exact_path() {
    // Width 200 is past `u128`: 0 stays 0, and the one digit of 1 goes to the top.
    assert_eq!(x("bitReverse(0, width: 200)"), "0");
    assert_eq!(x("byteSwap(0, width: 200)"), "0");
    assert_eq!(x("bitReverse(1, width: 200) == 2^199"), "true");
    assert_eq!(x("byteSwap(1, width: 200) == 2^192"), "true");
    assert_eq!(x("mulHi(2^199, 2, width: 200)"), "1");
    assert_eq!(x("funnelShl(1, 0, 199, width: 200) == 2^199"), "true");
    assert_eq!(x("funnelShr(1, 0, 199, width: 200)"), "2");
    // A negative operand beside one past `i64` is found on the exact path.
    let big = Value::int(num_bigint::BigInt::from(1u128 << 70));
    for (p, args) in [
        (Prim::Pdep, vec![Value::Int(-1), big.clone()]),
        (Prim::Pext, vec![big.clone(), Value::Int(-3)]),
        (
            Prim::MulHi,
            vec![big.clone(), Value::Int(-1), Value::Int(80)],
        ),
    ] {
        let out = zed_kernel::bits::word(p, &args);
        assert!(
            matches!(&out, Err(KernelError::Type(m)) if m.contains("it is negative")),
            "{p:?}: {out:?}"
        );
    }
}

#[test]
fn a_word_curries_by_its_width_alone() {
    // Currying is by name only (sec:values_morphisms): every operand is positional, so `...`
    // leaves out `width` and nothing else.
    let value = zed_tests::step_helpers::l01_16_elaboration::value;
    assert_eq!(
        value("r = bitReverse(1, ...);\nx = r(width: 8);\n", "x"),
        "128"
    );
    assert_eq!(
        value("s = byteSwap(0x0102, ...);\nx = s(width: 16);\n", "x"),
        "513"
    );
    assert_eq!(
        value("h = mulHi(2^7, 2^7, ...);\nx = h(width: 8);\n", "x"),
        "64"
    );
    // The domain of a word reached through `...` is FAIL-bitword-curry-domain.
    for src in [
        // An operand left out, `width` given, and a word with no named parameter.
        "r = bitReverse(width: 8, ...);\n",
        "r = bitReverse(1, width: 8, ...);\n",
        "r = pdep(1, 3, ...);\n",
        "r = pext(1, ...);\n",
    ] {
        let out = rejected(src);
        assert!(out.contains("`...`"), "{src}: {out}");
    }
}

#[test]
fn the_kernel_refuses_an_operand_that_is_no_integer() {
    // The checker never passes one (each test above); the kernel still names the word.
    for (p, args) in [
        (Prim::BitReverse, vec![Value::str("a"), Value::Int(8)]),
        (
            Prim::MulHi,
            vec![Value::Int(1), Value::float(2.5), Value::Int(8)],
        ),
        (Prim::Pext, vec![Value::atom("oops"), Value::Int(3)]),
    ] {
        let out = zed_kernel::bits::word(p, &args);
        let name = p.written();
        assert!(
            matches!(&out, Err(KernelError::Type(m)) if m.contains(&format!("`{name}` takes ints"))),
            "{p:?}: {out:?}"
        );
    }
}
