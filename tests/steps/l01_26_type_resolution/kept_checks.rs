//! What the `@cryptosafe` rule for a secret `if` needs from the checker (DESIGN.md
//! sec:security, the first transformation; plan row XR-ct-enforce). Both arms of a secret
//! `if` run and a `ctselect` keeps one, so each arm is compiled without the facts its
//! selector gives it, and a check the selector would prove, such as `d != 0` before
//! `x div d`, is kept. The arm's failure can then happen only when the arm is not kept,
//! where the `ctselect` throws it away, so the function's type is still the one checked
//! with the facts. These tests pin the two types that rule tells apart, with the step
//! L1.24 narrowing the checker already does: the `if` checked with its facts has no
//! `#divByZero`, and the same two arms run first and then selected, which is what checking
//! without the facts gives, has it. A checker that typed the transformed form would add an
//! atom to the type of every such `@cryptosafe` function that its plain form lacks.

use super::sig;

/// The source form: the divisor is ruled out of zero by the selector.
const GUARDED: &str = "f(x: int, d: int) = if d != 0 { x div d } else { 0 };\n";

/// Both arms evaluated before the selection, as the transformation runs them: the division
/// is checked with no fact about `d`.
const BOTH_ARMS: &str = "f(x: int, d: int) = { q = x div d; if d != 0 { q } else { 0 } };\n";

#[test]
fn the_selector_proves_the_check_so_the_type_has_no_atom() {
    assert_eq!(sig(GUARDED, "f"), "(x: int, d: int) -> int");
}

#[test]
fn the_arm_checked_without_the_selector_has_the_atom() {
    assert_eq!(sig(BOTH_ARMS, "f"), "(x: int, d: int) -> int | #divByZero");
}
