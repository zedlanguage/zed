//! FAIL-check-arm-test-through-call, found by TEST-complete-reduced (author P189). Drop this
//! file into tests/steps/l01_39_reduced_product/ as a module (`mod arm_test_through_call;` in its
//! mod.rs) once the checker narrows an arm through a call in its test. DESIGN.md step L1.39:
//! "an arm whose test calls a definition of the unit is narrowed through the call (step L1.25):
//! in `let clamp = ...; if clamp(x) > 10 ...` where `clamp` never exceeds 10, the arm is
//! unreachable", and an unreachable arm leaves the program accepted. The store's walk
//! (`store::product::arms`, tests in helpers.rs) finds this; the checker's arm scopes
//! (crates/zedc-check/src/check/arms.rs) read a call, and a name bound to an `if`, as an
//! opaque int, so the arm is checked as if every int reached it.

use zed_tests::step_helpers::l01_26_type_resolution::sig;
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

/// A test is narrowed through a call on its spine, under `!`, `-`, `+`, `*` and as the argument
/// of another call (`Ck::term_for` in walk.rs, FAIL-check-arm-call-bench-hang).
#[test]
fn a_test_is_narrowed_through_a_call_under_the_operators_of_its_spine() {
    let clamp = "clamp(positional x: int) = if x > 10 { 10 } else { x };\n";
    let arm = "{ popCount(x - x - 1) } else { 0 };\n";
    let tests = [
        "clamp(x) + 1 > 11",
        "-clamp(x) < -10",
        "3 * clamp(x) > 30",
        "!(clamp(x) <= 10)",
        "clamp(clamp(x)) > 10",
        "clamp(x) > 10 || clamp(x) > 20",
    ];
    let srcs: Vec<String> = (tests.iter())
        .map(|t| format!("{clamp}f(positional x: int) = if {t} {arm}"))
        .collect();
    accepted(&srcs.iter().map(|s| s.as_str()).collect::<Vec<_>>());
    // The controls: a clamp at 11 lets x = 11 reach each arm.
    let srcs: Vec<String> = (tests.iter())
        .map(|t| {
            format!(
                "{}f(positional x: int) = if {t} {arm}",
                clamp.replace("10", "11")
            )
        })
        .collect();
    rejected(&srcs.iter().map(|s| s.as_str()).collect::<Vec<_>>());
}

/// An `if` written inside a test is read as its arms' values under its own test, as a name
/// bound to it is (CHECK-arm-test-if-and-operand-calls): `(if x > 0 { x } else { 0 }) > 10`
/// holds for x >= 11 alone, kept in place, and so does the test of an `if` with an `if` inside
/// it, a name of its own.
#[test]
fn a_test_is_narrowed_through_an_if_inside_it() {
    let at = |c: i32| {
        format!(
            "f(positional x: int) = \
             if (if x > 0 {{ x }} else {{ 0 }}) > 10 {{ popCount(x - {c}) }} else {{ 0 }};\n"
        )
    };
    let under = |c: i32| {
        format!(
            "f(positional x: int) = \
             if !((if x > 0 {{ x }} else {{ 0 }}) + 1 <= 11) {{ popCount(x - {c}) }} else {{ 0 }};\n"
        )
    };
    // An `if` with an `if` inside it, a name of its own (`Ck::term_for`): `x` above 5, else 5.
    let nested = |c: i32| {
        format!(
            "f(positional x: int) = \
             if (if x > 0 {{ if x > 5 {{ x }} else {{ 5 }} }} else {{ 0 }}) > 10 \
             {{ popCount(x - {c}) }} else {{ 0 }};\n"
        )
    };
    // The boundary: x = 11 reaches the arm, where x - 11 is 0; one past it, x - 12 is -1.
    accepted(&[&at(11), &under(11), &nested(11)]);
    rejected(&[&at(12), &under(12), &nested(12)]);
}

/// A call in an operand position the test's spine does not cover, the divisor of `div`, is
/// read through the callee (CHECK-arm-test-if-and-operand-calls): `t(x)` is `x` where `x > 0`,
/// so the divisor is not 0 in the arm and `f` gives no `#divByZero`; where `x = 0` reaches the
/// arm, `t(0)` is 0 and it does. (`div`, not `mod`: a modulus that may be 0 is refused, not
/// typed with `#divByZero`; QUESTIONS A174.)
#[test]
fn a_divisor_is_read_through_a_call() {
    let t = "t(positional y: int) = if y > 0 { y } else { 0 };\n";
    let at = |c: i32| {
        let src = format!("{t}f(x: int, n: int) = if x > {c} {{ n div t(x) }} else {{ 0 }};\n");
        sig(&src, "f")
    };
    assert_eq!(at(0), "(x: int, n: int) -> int");
    assert_eq!(at(-1), "(x: int, n: int) -> int | #divByZero");
}

/// A call read as the operand of an atom is read through the callee
/// (CHECK-arm-test-if-and-operand-calls): `t(x) - 1` is `x - 1` where `x > 0`, never below 0;
/// where `x = 0` reaches the arm it is -1.
#[test]
fn an_atom_reads_a_call_through_the_callee() {
    let t = "t(positional y: int) = if y > 0 { y } else { 0 };\n";
    let at = |c: i32| {
        format!("{t}f(positional x: int) = if x > {c} {{ popCount(t(x) - 1) }} else {{ 0 }};\n")
    };
    accepted(&[&at(0)]);
    rejected(&[&at(-1)]);
}

/// A name bound to a call of a summarized callee is summarized through the call
/// (CHECK-binder-call-summary): after `m = clamp(x)`, `m > 10` holds only for `x >= 11`, so
/// `popCount(x - 11)` is never given a negative int, as with the `if` written in place of the
/// call, and `popCount(x - 12)` is, at `x = 11`. Before, the binder's value kept the call as an
/// application, which its summary does not read, and the boundary was rejected too. The
/// binder read through a second binder, and a call of two arguments, are read alike.
#[test]
fn a_name_bound_to_a_call_is_summarized_through_the_callee() {
    let clamp = "clamp(positional y: int) = if y > 0 { y } else { 0 };\n";
    let one = |c: i32| {
        format!(
            "{clamp}f(positional x: int) {{\n  m = clamp(x);\n  \
             return if m > 10 {{ popCount(x - {c}) }} else {{ 0 }};\n}}\n"
        )
    };
    let chain = |c: i32| {
        format!(
            "{clamp}f(positional x: int) {{\n  m = clamp(x);\n  k = m + 1;\n  \
             return if k > 11 {{ popCount(x - {c}) }} else {{ 0 }};\n}}\n"
        )
    };
    let two = |c: i32| {
        format!(
            "least(positional a: int, positional b: int) = if a < b {{ a }} else {{ b }};\n\
             f(positional x: int) {{\n  m = least(x, 20);\n  \
             return if m > 10 {{ popCount(x - {c}) }} else {{ 0 }};\n}}\n"
        )
    };
    accepted(&[&one(11), &chain(11), &two(11)]);
    rejected(&[&one(12), &chain(12), &two(12)]);
}

mod bench;
