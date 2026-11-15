//! A chain of n infix calls, `0 ~plus~ 1 ~plus~ 1 …`, parses, builds and checks in O(n)
//! (DESIGN.md Part G): the parse is a left-recursive rule, the build looks at one edge node of
//! each operand, and the check of each call is that of `plus(…, 1)`. A chain whose last
//! operand opens with `*` is rejected, also in O(n). The benchmark in `bench/scaling.rs` holds
//! the times; here the chain passes at small sizes. A chain 4,000 deep, far
//! past what a recursive walk holds on a test thread's 2 MiB stack, is a benchmark too (author
//! P178: an unusual size is a benchmark).

use crate::front;

/// `x = 0 ~plus~ 1 ~plus~ 1 …;` with `n` calls, after `plus`.
pub(super) fn chain(n: usize) -> String {
    let mut t = String::from("plus(positional a: int, positional b: int) = a + b;\nx = 0");
    t += &" ~plus~ 1".repeat(n);
    t + ";\n"
}

/// [`chain`] with ` * 2` at its end: the last call is rejected.
pub(super) fn rejected_chain(n: usize) -> String {
    let t = chain(n);
    t.strip_suffix(";\n").unwrap().to_string() + " * 2;\n"
}

/// The chain of `n` calls checks, and its rejected form gives one error, at the `*`.
pub(super) fn pass(n: usize) {
    assert_eq!(front(&chain(n)), "ok", "{n}");
    let got = front(&rejected_chain(n));
    assert!(
        got.starts_with("2:") && got.contains("Infix call next to `*`"),
        "{n}: {got}"
    );
    assert_eq!(got.lines().count(), 1, "{n}: {got}");
}

#[test]
fn a_chain_of_infix_calls() {
    for n in [1, 2, 9, 100] {
        pass(n);
    }
    assert_eq!(
        zed_tests::step_helpers::l01_16_elaboration::value(&chain(100), "x"),
        "100"
    );
}
