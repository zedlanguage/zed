//! The cases of COMPLETENESS.md that the other files leave open: each word in a function body
//! under tests that bound its operands and in other syntactic positions, the forms of its
//! arguments, operands of other kinds, the bounds of DESIGN's forward transfer on ranges and
//! read back through the domain of a second word, and the kernel's refusals on its exact path.
//! A refinement type on a parameter is compiled from step L10.1, so operands are bounded here
//! by tests (DESIGN L1.39: a test narrows a scope).

use zed_kernel::{KernelError, Prim, Value};
use zedc::store::interval::{End, IntervalSet, bit_word};

use super::{accepted, rejected, x};

/// Whether every row of every table of `src` passes, and there is one.
fn rows_pass(src: &str) -> bool {
    let out = zedc::testing::test(src);
    !out.is_empty() && out.iter().all(|o| o.failure.is_none())
}

#[test]
fn each_word_in_a_function_body_under_tests_of_its_operands() {
    for src in [
        "f(positional a: int, positional b: int) = if a >= 0 && b >= 0 { bitAnd(a, b) } else { -1 }\n\
         test { (12, 10) -> 8, (0, 7) -> 0, (-1, 1) -> -1 }\n",
        "f(positional a: int, positional b: int) = if a >= 0 && b >= 0 { bitOr(a, b) } else { -1 }\n\
         test { (12, 10) -> 14, (0, 0) -> 0, (1, -1) -> -1 }\n",
        "f(positional a: int, positional b: int) = if a >= 0 && b >= 0 { bitXor(a, b) } else { -1 }\n\
         test { (12, 10) -> 6, (5, 5) -> 0 }\n",
        "f(positional x: int, positional k: int) = if k >= 0 { shl(x, k) } else { 0 }\n\
         test { (3, 2) -> 12, (-3, 2) -> -12, (1, 0) -> 1, (1, -1) -> 0 }\n",
        "f(positional x: int, positional k: int) = if k >= 0 { shr(x, k) } else { 0 }\n\
         test { (13, 2) -> 3, (-13, 2) -> -4, (-1, 100) -> -1 }\n",
        "f(positional x: int) = if x >= 0 { popCount(x) } else { -1 }\n\
         test { 0 -> 0, 255 -> 8, 2^64 + 1 -> 2, -1 -> -1 }\n",
        "f(positional x: int) = if x >= 0 && x < 256 { bitNot(x, width: 8) } else { -1 }\n\
         test { 0 -> 255, 255 -> 0, 5 -> 250, 256 -> -1 }\n",
        "f(positional x: int) = if x >= 0 && x < 256 { leadingZeros(x, width: 8) } else { -1 }\n\
         test { 0 -> 8, 1 -> 7, 128 -> 0 }\n",
        "f(positional x: int) = if x >= 0 && x < 256 { trailingZeros(x, width: 8) } else { -1 }\n\
         test { 0 -> 8, 1 -> 0, 128 -> 7, 12 -> 2 }\n",
        "f(positional x: int, positional k: int) =\n  \
           if x >= 0 && x < 16 && k >= 0 { rotl(x, k, width: 4) } else { -1 }\n\
         test { (8, 1) -> 1, (1, 4) -> 1, (1, 5) -> 2, (0, 3) -> 0 }\n",
        "f(positional x: int, positional k: int) =\n  \
           if x >= 0 && x < 16 && k >= 0 { rotr(x, k, width: 4) } else { -1 }\n\
         test { (1, 1) -> 8, (8, 4) -> 8, (8, 7) -> 1 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
}

#[test]
fn an_operand_not_bounded_by_its_tests_is_rejected_at_each_word() {
    for (src, word, param) in [
        ("f(positional a: int) = bitAnd(a, 1);\n", "bitAnd", "a"),
        ("f(positional b: int) = bitOr(1, b);\n", "bitOr", "b"),
        ("f(positional a: int) = bitXor(a, a);\n", "bitXor", "a"),
        ("f(positional k: int) = shl(1, k);\n", "shl", "k"),
        ("f(positional k: int) = shr(1, k);\n", "shr", "k"),
        ("f(positional x: int) = popCount(x);\n", "popCount", "x"),
        (
            "f(positional x: int) = bitNot(x, width: 8);\n",
            "bitNot",
            "x",
        ),
        (
            "f(positional x: int) = leadingZeros(x, width: 8);\n",
            "leadingZeros",
            "x",
        ),
        (
            "f(positional x: int) = trailingZeros(x, width: 8);\n",
            "trailingZeros",
            "x",
        ),
        (
            "f(positional x: int) = rotl(x, 1, width: 8);\n",
            "rotl",
            "x",
        ),
        (
            "f(positional k: int) = rotr(1, k, width: 8);\n",
            "rotr",
            "k",
        ),
        // A test that bounds one end only, or one digit too wide.
        (
            "f(positional x: int) = if x >= 0 { bitNot(x, width: 8) } else { 0 };\n",
            "bitNot",
            "x",
        ),
        (
            "f(positional x: int) = if x >= 0 && x <= 256 { rotl(x, 1, width: 8) } else { 0 };\n",
            "rotl",
            "x",
        ),
    ] {
        let out = rejected(src);
        assert!(
            out.contains(&format!("`{word}` takes `{param}` in int[0..")),
            "{src}: {out}"
        );
    }
}

#[test]
fn each_word_in_other_positions() {
    // A tuple, an interpolation, nested words, a receiver chain, an expression operand, a
    // lambda, and a comparison.
    assert_eq!(
        x("(bitAnd(12, 10), bitOr(12, 10), bitXor(12, 10))"),
        "(8, 14, 6)"
    );
    assert_eq!(x("\"${popCount(255)}/${shl(1, 3)}\""), "\"8/8\"");
    assert_eq!(x("bitNot(bitAnd(255, 15), width: 8)"), "240");
    assert_eq!(x("12.bitAnd(10).shl(1).popCount()"), "1");
    assert_eq!(x("shr(2^10 - 1, 2 + 3)"), "31");
    assert_eq!(x("trailingZeros(shl(1, 70), width: 71)"), "70");
    assert_eq!(x("rotr(rotl(9, 3, width: 4), 3, width: 4)"), "9");
    assert_eq!(x("leadingZeros(1, width: 64) == 63"), "true");
    assert!(accepted(
        "g = n -> if n >= 0 && n < 256 { bitNot(n, width: 8) } else { 0 };\ny = g(5);\n"
    ));
    // A lambda passes the need of its word to its caller.
    let out = rejected("g = n -> popCount(n);\ny = g(-1);\n");
    assert!(out.contains("`popCount`"), "{out}");
}

#[test]
fn the_width_is_the_only_named_parameter() {
    for src in [
        "x = bitNot(5, 3);\n",
        "x = bitNot(5);\n",
        "x = bitNot(x: 5, width: 3);\n",
        "x = bitAnd(a: 1, b: 2);\n",
        "x = bitAnd(1, 2, width: 8);\n",
        "x = popCount(1, 2);\n",
        "x = shl(1);\n",
        "x = rotl(1, 1, width: 4, width: 4);\n",
    ] {
        // The message names the signature, not the word, and has no repairs:
        // FAIL-bitword-arity-message holds the expected form.
        let out = rejected(src);
        assert!(
            out.contains("parameter") || out.contains("argument"),
            "{src}: {out}"
        );
    }
}

#[test]
fn an_operand_of_another_kind_is_rejected() {
    for src in [
        "x = bitAnd(1/2, 1);\n",
        "x = bitOr(1, 1.5f64);\n",
        "x = bitXor(true, 1);\n",
        "x = popCount(\"a\");\n",
        "x = shl((1, 2), 1);\n",
        "x = shr(1, 1/2);\n",
        "x = bitNot(1, width: 1/2);\n",
        "x = f64Bits(\"a\");\n",
        "x = f64Bits(true);\n",
    ] {
        let out = rejected(src);
        let word = &src[4..src.find('(').unwrap()];
        let at_word = out.contains(&format!("`{word}`"));
        assert!(at_word || out.contains("f64`, never `int`"), "{src}: {out}");
    }
}

#[test]
fn a_word_curries_by_its_width_alone() {
    assert_eq!(x("bitNot(5, ...)(width: 3)"), "2");
    assert_eq!(x("rotl(8, 1, ...)(width: 4)"), "1");
    assert_eq!(x("trailingZeros(0, ...)(width: 8)"), "8");
}

#[test]
fn the_bounds_of_forward_transfer_are_read_by_a_second_word() {
    // Each result is bounded as DESIGN's transfer states, so it lies in the domain of a word of
    // width 4 (below 16) or 8; a width one digit narrower is rejected.
    let fits = [
        ("bitAnd(x, 15)", 4),
        ("bitOr(bitAnd(x, 15), 7)", 4),
        ("bitXor(bitAnd(x, 15), bitAnd(x, 8))", 4),
        ("popCount(bitAnd(x, 255))", 4),
        ("leadingZeros(bitAnd(x, 255), width: 8)", 4),
        ("trailingZeros(bitAnd(x, 255), width: 8)", 4),
        ("shr(bitAnd(x, 255), 4)", 4),
        ("shl(bitAnd(x, 15), 4)", 8),
        ("bitNot(bitAnd(x, 15), width: 4)", 4),
        ("rotl(bitAnd(x, 15), 1, width: 4)", 4),
    ];
    for (inner, w) in fits {
        let src = |w: i64| {
            format!(
                "f(positional x: int) = if x >= 0 {{ bitNot({inner}, width: {w}) }} else {{ 0 }};\n"
            )
        };
        assert!(accepted(&src(w)), "{inner} at width {w}");
        let out = rejected(&src(w - 1));
        assert!(
            out.contains("`bitNot` takes `x`"),
            "{inner} at {}: {out}",
            w - 1
        );
    }
}

#[test]
fn the_bounds_design_states_on_ranges() {
    let r = |lo: i64, hi: i64| IntervalSet::of(lo, hi);
    // `bitAnd` at most the smaller upper bound.
    assert_eq!(bit_word(Prim::BitAnd, &[r(0, 100), r(0, 50)]), r(0, 50));
    assert_eq!(bit_word(Prim::BitAnd, &[r(3, 3), r(0, 1000)]), r(0, 3));
    // `bitOr` and `bitXor` below the least power of two above the larger upper bound.
    assert_eq!(bit_word(Prim::BitOr, &[r(0, 15), r(0, 15)]), r(0, 15));
    assert_eq!(bit_word(Prim::BitOr, &[r(0, 16), r(0, 1)]), r(0, 31));
    assert_eq!(bit_word(Prim::BitXor, &[r(0, 15), r(0, 7)]), r(0, 15));
    // `popCount`, `leadingZeros` and `trailingZeros` within `0..=w`.
    assert_eq!(bit_word(Prim::LeadingZeros, &[r(0, 255), r(8, 8)]), r(0, 8));
    assert_eq!(bit_word(Prim::LeadingZeros, &[r(0, 0), r(8, 8)]), r(8, 8));
    assert_eq!(bit_word(Prim::PopCount, &[r(0, 0)]), r(0, 0));
    // `shl` and `shr` as the product and the quotient.
    assert_eq!(bit_word(Prim::Shl, &[r(1, 3), r(2, 2)]), r(4, 12));
    assert_eq!(bit_word(Prim::Shr, &[r(16, 31), r(2, 3)]), r(2, 7));
    // A width past `i64` keeps the exact bound.
    let top = End::from((1i128 << 100) - 1);
    assert_eq!(
        bit_word(Prim::BitNot, &[r(0, 0), r(100, 100)]),
        IntervalSet::range(top.clone(), top)
    );
}

/// The kernel's type error for the word `p` on `args`.
fn kernel_refuses(p: Prim, args: &[Value]) -> String {
    match zed_kernel::bits::word(p, args) {
        Err(KernelError::Type(m)) => m,
        other => panic!("{p:?} {args:?}: {other:?}"),
    }
}

#[test]
fn the_kernel_refuses_each_operand_outside_its_domain_on_the_exact_path() {
    let big = Value::int(num_bigint::BigInt::from(1) << 70u32);
    // A negative operand beside one past `i64`.
    let out = kernel_refuses(Prim::BitAnd, &[Value::Int(-1), big.clone()]);
    assert!(out.contains("`bitAnd` needs `a` in int[0..]"), "{out}");
    // An `x` past `2^width`, given past `i64`.
    let out = kernel_refuses(Prim::BitNot, &[big.clone(), Value::Int(8)]);
    assert!(
        out.contains("`bitNot` needs `x` in int[0..<2^width]"),
        "{out}"
    );
    // An operand that is no integer.
    for v in [Value::str("a"), Value::float(1.5), Value::atom("none")] {
        let out = kernel_refuses(Prim::PopCount, &[v]);
        assert!(out.contains("`popCount` takes ints"), "{out}");
    }
    // `f64Bits` of anything but an f64.
    for v in [Value::Int(1), Value::str("a"), big] {
        let out = kernel_refuses(Prim::F64Bits, &[v]);
        assert!(out.contains("`f64Bits` takes an f64"), "{out}");
    }
}

#[test]
fn the_kernel_refuses_a_negative_operand_on_the_machine_path() {
    let out = kernel_refuses(Prim::BitAnd, &[Value::Int(-1), Value::Int(1)]);
    assert!(out.contains("`bitAnd` needs `a` in int[0..]"), "{out}");
    let out = kernel_refuses(Prim::Rotl, &[Value::Int(1), Value::Int(-1), Value::Int(8)]);
    assert!(out.contains("`rotl` needs `k` in int[0..]"), "{out}");
}

#[test]
fn the_domain_of_an_x_with_a_width_is_below_two_to_the_width() {
    use zed_kernel::bits::below_two_pow;
    let i = Value::Int;
    assert!(below_two_pow(&i(0), &i(0)));
    assert!(below_two_pow(&i(255), &i(8)));
    assert!(!below_two_pow(&i(256), &i(8)));
    assert!(!below_two_pow(&i(-1), &i(8)));
    assert!(!below_two_pow(&i(1), &i(-1)));
    assert!(!below_two_pow(&Value::str("a"), &i(8)));
    let big = Value::int(num_bigint::BigInt::from(1) << 70u32);
    assert!(below_two_pow(&big, &i(71)));
    assert!(!below_two_pow(&big, &i(70)));
}
