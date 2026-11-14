//! A bit word curried with `...` has its domains checked at each call of the function it gives
//! (FAIL-bitword-curry-domain, found by TEST-complete-reduced, author P189): before the fix the
//! checker accepted `r = bitReverse(256, ...); x = r(width: 8);` and the evaluator stopped with
//! "a bug in zedc itself". DESIGN: each word's domain (L1.39a, L1.39f) is checked statically
//! (author decision on static soundness: resolved at compile time, else an error).
use super::{accepted, rejected};

#[test]
fn a_word_curried_with_dots_checks_its_domain_at_compile_time() {
    for (src, needs) in [
        // `x` at least `2^width`.
        (
            "r = bitReverse(256, ...);\nx = r(width: 8);\n",
            "`x` in int[0..<2^8]",
        ),
        // `width` not a multiple of 8.
        (
            "r = byteSwap(1, ...);\nx = r(width: 12);\n",
            "multiple of 8",
        ),
        // A negative `width`.
        ("r = bitReverse(1, ...);\nx = r(width: -1);\n", "`width`"),
        // The words of L1.39a that take a width.
        (
            "r = bitNot(256, ...);\nx = r(width: 8);\n",
            "`x` in int[0..<2^8]",
        ),
        (
            "r = rotl(256, 1, ...);\nx = r(width: 8);\n",
            "`x` in int[0..<2^8]",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(needs), "{src}: {out}");
    }
    // The same calls in their domains are accepted.
    assert!(accepted("r = bitReverse(255, ...);\nx = r(width: 8);\n"));
    assert!(accepted("r = byteSwap(1, ...);\nx = r(width: 16);\n"));
}

#[test]
fn the_width_boundary_and_the_funnel_shift_k_are_checked_through_the_curried_function() {
    // `x` = 256 needs a width of 9: 8 is refused and names 9 as the repair, 9 is accepted.
    let out = rejected("r = bitReverse(256, ...);\nx = r(width: 8);\n");
    assert!(out.contains("Try `r(width: 9)` instead."), "{out}");
    assert!(accepted("r = bitReverse(256, ...);\nx = r(width: 9);\n"));
    // A funnel shift's `k` must lie below the width: 7 at width 7 is refused, at 8 accepted.
    let out = rejected("r = funnelShl(1, 2, 7, ...);\nx = r(width: 7);\n");
    assert!(out.contains("`funnelShl` takes `k` in int[0..<7]"), "{out}");
    assert!(accepted("r = funnelShl(1, 2, 7, ...);\nx = r(width: 8);\n"));
    // A negative `x` fits no width.
    let out = rejected("r = bitReverse(-1, ...);\nx = r(width: 8);\n");
    assert!(out.contains("`x` in int[0..<2^8]: `-1 : int`"), "{out}");
}

#[test]
fn the_curried_function_is_checked_when_it_is_renamed_returned_or_passed() {
    // Bound to another name.
    let out = rejected("r = bitReverse(256, ...);\ny = r;\nx = y(width: 8);\n");
    assert!(out.contains("`x` in int[0..<2^8]"), "{out}");
    assert!(accepted(
        "r = bitReverse(255, ...);\ny = r;\nx = y(width: 8);\n"
    ));
    // Returned by a function whose operand is any int.
    let src = "f(positional n: int) = bitReverse(n, ...);\nx = f(256)(width: 8);\n";
    assert!(rejected(src).contains("`x` in int[0..<2^8]: `n : int`"));
    // Passed to a function whose parameter takes every int width: the width it may be called
    // with is not shown to hold `x`.
    let src = "r = bitReverse(255, ...);\n\
               ap(positional g: (width: int) -> int) = g(width: 8);\nx = ap(r);\n";
    let out = rejected(src);
    assert!(
        out.contains("`bitReverse` takes `width` in int[8..]: `width : int`."),
        "{out}"
    );
}
