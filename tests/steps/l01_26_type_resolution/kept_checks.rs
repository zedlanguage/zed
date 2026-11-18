//! What the `@cryptosafe` rule for a secret `if` needs from the checker (DESIGN.md
//! sec:security, the first transformation; plan row XR-ct-enforce). Both arms of a secret
//! `if` run and a `ctselect` keeps one, so each arm is compiled without the facts its
//! selector gives it, and a check the selector would prove, such as `d != 0` (with `d`
//! public, since a secret divisor is rejected) before
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

/// The `match` case of the same rule. In `match v { #d(0) -> 0, #d(n) -> x div n, #z -> 0 }`
/// the second arm knows `n != 0` from the arm before it, not from the payload type, so the
/// payload's least value, `0`, on which the arm runs when `v` holds `#z`, breaks that fact.
/// This zedc does not compile a `match`, an atom with a payload or `u8` yet, so the two tests
/// write the same arms with an `if` on an `int`: the arm typed with the earlier arm's fact has
/// no `#divByZero`, and the arm run on the least value, as the transformation runs it when
/// the member is absent, has it, so only typing with the facts keeps the plain type.
const EXCLUDED_BY_EARLIER_ARM: &str = "f(x: int, n: int) = if n == 0 { 0 } else { x div n };\n";

/// The arm run on the payload's least value before the selection, with `held` saying whether
/// the member is present.
const ARM_ON_LEAST_VALUE: &str =
    "f(x: int, held: bool) = { q = x div 0; if held { q } else { 0 } };\n";

#[test]
fn the_earlier_arm_proves_the_check_so_the_type_has_no_atom() {
    assert_eq!(sig(EXCLUDED_BY_EARLIER_ARM, "f"), "(x: int, n: int) -> int");
}

#[test]
fn the_arm_on_the_least_value_has_the_atom() {
    assert_eq!(
        sig(ARM_ON_LEAST_VALUE, "f"),
        "(x: int, held: bool) -> int | #divByZero"
    );
}

/// The form the spec's example now takes: the selector is a secret `s` joined to a test of a
/// public divisor, since a division by a secret divisor is rejected outright. The checker
/// narrows `d` through `&&`, so the arm typed with the selector's facts has no `#divByZero`.
const SECRET_AND_PUBLIC_GUARD: &str =
    "f(x: int, d: int, s: bool) = if s && d != 0 { x div d } else { 0 };\n";

#[test]
fn a_guard_joined_to_a_secret_by_and_still_proves_the_check() {
    assert_eq!(
        sig(SECRET_AND_PUBLIC_GUARD, "f"),
        "(x: int, d: int, s: bool) -> int"
    );
}
