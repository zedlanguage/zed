//! FAIL-check-arm-test-through-call, found by TEST-complete-reduced (author P189). Drop this
//! file into tests/steps/l01_39_reduced_product/ as a module (`mod arm_test_through_call;` in its
//! mod.rs) once the checker narrows an arm through a call in its test. DESIGN.md step L1.39:
//! "an arm whose test calls a definition of the unit is narrowed through the call (step L1.25):
//! in `let clamp = ...; if clamp(x) > 10 ...` where `clamp` never exceeds 10, the arm is
//! unreachable", and an unreachable arm leaves the program accepted. The store's walk
//! (`store::product::arms`, tests in helpers.rs) finds this; the checker's arm scopes
//! (crates/zedc-check/src/check/arms.rs) read a call, and a name bound to an `if`, as an
//! opaque int, so the arm is checked as if every int reached it.

use zedc::run::load;

fn check(src: &str) -> Option<String> {
    let src = format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n");
    load(src.as_bytes()).err()
}

#[test]
fn an_arm_whose_test_calls_a_definition_is_narrowed_through_the_call() {
    for src in [
        // The design's example, `clamp` a definition of the unit.
        "clamp(positional x: int) = if x > 10 { 10 } else { x };\n\
         f(positional x: int) = if clamp(x) > 10 { popCount(x - x - 1) } else { 0 };\n",
        // `clamp` bound by `let` in the body, as the design writes it.
        "f(positional x: int) {\n  clamp = y -> if y > 10 { 10 } else { y };\n  \
         return if clamp(x) > 10 { popCount(x - x - 1) } else { 0 };\n}\n",
        // The value of the call bound to a name first.
        "f(positional x: int) {\n  c = if x > 10 { 10 } else { x };\n  \
         return if c > 10 { popCount(x - x - 1) } else { 0 };\n}\n",
        // A reached arm narrowed through the call: `clamp(x) > 10` holds only for x >= 11.
        "clamp(positional x: int) = if x > 11 { 11 } else { x };\n\
         f(positional x: int) = if clamp(x) > 10 { popCount(x - 11) } else { 0 };\n",
    ] {
        if let Some(out) = check(src) {
            panic!("rejected:\n{src}{out}");
        }
    }
    // The control: a clamp at 11 lets x = 11 and above reach the arm, where x - x - 1 is -1.
    let reached = "clamp(positional x: int) = if x > 11 { 11 } else { x };\n\
                   f(positional x: int) = if clamp(x) > 10 { popCount(x - x - 1) } else { 0 };\n";
    assert!(check(reached).is_some(), "{reached}");
}

/// Each program is accepted.
fn accepted(srcs: &[&str]) {
    for src in srcs {
        if let Some(out) = check(src) {
            panic!("rejected:\n{src}{out}");
        }
    }
}

/// Each program is rejected.
fn rejected(srcs: &[&str]) {
    for src in srcs {
        assert!(check(src).is_some(), "accepted:\n{src}");
    }
}

#[test]
fn a_test_is_narrowed_through_calls_of_several_arguments_and_through_calls_in_a_body() {
    accepted(&[
        // A definition that calls another: `hi(x)` is at least 1.
        "lo(positional y: int) = if y < 0 { 0 } else { y };\n\
         hi(positional y: int) = lo(y) + 1;\n\
         f(positional x: int) = if hi(x) <= 0 { popCount(x - x - 1) } else { 0 };\n",
        // The call in the arm where the test fails.
        "clamp(positional x: int) = if x > 10 { 10 } else { x };\n\
         f(positional x: int) = if clamp(x) <= 10 { 0 } else { popCount(x - x - 1) };\n",
        // Two arguments: `least(x, 3)` is at most 3.
        "least(positional a: int, positional b: int) = if a < b { a } else { b };\n\
         f(positional x: int) = if least(x, 3) > 3 { popCount(x - x - 1) } else { 0 };\n",
        // `twice(x) > 10` holds for x >= 6 alone.
        "twice(positional y: int) = y * 2;\n\
         f(positional x: int) = if twice(x) > 10 { popCount(x - 6) } else { 0 };\n",
        // Two calls of one definition, each at its own argument: x >= 5 where both hold.
        "next(positional y: int) = y + 1;\n\
         f(positional x: int, positional z: int) = \
         if next(x) > 5 && next(z) < 0 { popCount(x - 5) } else { 0 };\n",
        // A name bound to an `if` holds the join of its arms: `c` is never below 0.
        "f(positional x: int) {\n  c = if x > 0 { x } else { -x };\n  \
         return if c < 0 { popCount(x - x - 1) } else { 0 };\n}\n",
    ]);
    rejected(&[
        // x = 6 reaches the arm, where x - 7 is -1.
        "twice(positional y: int) = y * 2;\n\
         f(positional x: int) = if twice(x) > 10 { popCount(x - 7) } else { 0 };\n",
        // z <= -2 where the test holds.
        "next(positional y: int) = y + 1;\n\
         f(positional x: int, positional z: int) = \
         if next(x) > 5 && next(z) < 0 { popCount(z) } else { 0 };\n",
        // A body that reads a name bound outside it is not followed: `g(x)` is any value.
        "f(positional x: int, positional k: int) {\n  g = y -> y + k;\n  \
         return if g(x) > 10 { popCount(x - x - 1) } else { 0 };\n}\n",
        // A body that calls itself is not followed.
        "r(positional y: int) = if y > 0 { r(y - 1) } else { 0 };\n\
         f(positional x: int) = if r(x) > 10 { popCount(x - x - 1) } else { 0 };\n",
    ]);
}
