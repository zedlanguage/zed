//! The cases of COMPLETENESS.md that the other files leave open: the design's examples and
//! each reduction read through whole programs, the way a user meets them. The other files
//! check the scopes through the store's API ([`zedc::store::product::arms`]); here the
//! checker reads them. A bit word's domain reads the scope of its arm (DESIGN L1.39a:
//! `bitNot(x, width: w)` takes `x` in `int[0..<2^w]`), so a program accepted at width `w` and
//! rejected at `w - 1` shows the arm's upper bound exactly, and an arm whose body would be
//! rejected if any value reached it shows that the arm is unreachable (DESIGN L1.39: such an
//! arm is unreachable and the program is accepted).

use zedc::run::load;

/// `src` as a whole program: a `main` is added when it declares none.
fn program(src: &str) -> String {
    match src.contains("main(") {
        true => src.to_string(),
        false => format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n"),
    }
}

/// The rendered diagnostics of `src`, or `None` when it is accepted.
fn check(src: &str) -> Option<String> {
    load(program(src).as_bytes()).err()
}

/// Whether every row of every table of `src` passes, and there is one.
fn rows_pass(src: &str) -> bool {
    let out = zedc::testing::test(src);
    !out.is_empty() && out.iter().all(|o| o.failure.is_none())
}

/// `body` is accepted with `{w}` replaced by the width `w`, and rejected at `w - 1` at
/// `bitNot`: the arm around `bitNot` holds a value of exactly `w` binary digits at most.
fn fits_exactly(body: &str, w: u32) {
    let src = body.replace("{w}", &w.to_string());
    if let Some(out) = check(&src) {
        panic!("rejected at width {w}:\n{src}{out}");
    }
    let src = body.replace("{w}", &(w - 1).to_string());
    match check(&src) {
        None => panic!("accepted at width {}:\n{src}", w - 1),
        Some(out) => assert!(out.contains("`bitNot` takes `x`"), "{src}{out}"),
    }
}

/// `src` is accepted, and `reached`, the same program with a test that lets a value reach the
/// arm, is rejected at the arm's `popCount` of a value below 0.
fn unreachable_arm(src: &str, reached: &str) {
    if let Some(out) = check(src) {
        panic!("rejected:\n{src}{out}");
    }
    match check(reached) {
        None => panic!("accepted:\n{reached}"),
        Some(out) => assert!(
            out.contains("`popCount` takes `x` in int[0..]"),
            "{reached}{out}"
        ),
    }
}

#[test]
fn the_design_arm_of_n_mod_4_within_0_to_10_holds_9_at_most() {
    // `n` in `int[1..=9]`: 9 needs four binary digits.
    fits_exactly(
        "f(positional n: int) = if n >= 0 && n <= 10 && n mod 4 == 1 { bitNot(n, width: {w}) } else { 0 };\n",
        4,
    );
    assert!(rows_pass(
        "f(positional n: int) = if n >= 0 && n <= 10 && n mod 4 == 1 { n } else { 0 }\n\
         test { 1 -> 1, 5 -> 5, 9 -> 9, 13 -> 0, 3 -> 0, -3 -> 0, 10 -> 0 }\n"
    ));
}

#[test]
fn a_congruence_moves_the_ends_the_arm_reads() {
    // Odd `n` within `0..=16` is at most 15; even `n` reaches 16, which needs five digits.
    fits_exactly(
        "f(positional n: int) = if n >= 0 && n <= 16 && n mod 2 == 1 { bitNot(n, width: {w}) } else { 0 };\n",
        4,
    );
    fits_exactly(
        "f(positional n: int) = if n >= 0 && n <= 16 && n mod 2 == 0 { bitNot(n, width: {w}) } else { 0 };\n",
        5,
    );
}

#[test]
fn the_complement_of_an_exact_test_bounds_the_other_arm() {
    for (src, w) in [
        // The `else` of `n != 3` holds 3 alone.
        (
            "f(positional n: int) = if n != 3 { 0 } else { bitNot(n, width: {w}) };\n",
            2,
        ),
        // The `else` of a disjunction, and a negated test.
        (
            "f(positional n: int) = if n < 0 || n > 3 { 0 } else { bitNot(n, width: {w}) };\n",
            2,
        ),
        (
            "f(positional n: int) = if !(n < 0 || n > 3) { bitNot(n, width: {w}) } else { 0 };\n",
            2,
        ),
        // An `else if` chain.
        (
            "f(positional n: int) = if n < 0 { 0 } else if n > 15 { 0 } else { bitNot(n, width: {w}) };\n",
            4,
        ),
        // The `else` of `n mod 4 == 1` within `0..=10` keeps 10.
        (
            "f(positional n: int) = if n >= 0 && n <= 10 { if n mod 4 == 1 { 0 } else { bitNot(n, width: {w}) } } else { 0 };\n",
            4,
        ),
    ] {
        fits_exactly(src, w);
    }
}

#[test]
fn a_disjunction_a_relation_and_a_nest_each_bound_the_arm() {
    for (src, w) in [
        // The join of two ranges: 11 at most.
        (
            "f(positional n: int) = if (n >= 0 && n < 4) || (n >= 8 && n < 12) { bitNot(n, width: {w}) } else { 0 };\n",
            4,
        ),
        // `x < y` and `y <= 16`: `x` is 15 at most.
        (
            "f(positional x: int, positional y: int) = if x >= 0 && x < y && y <= 16 { bitNot(x, width: {w}) } else { 0 };\n",
            4,
        ),
        // Tests nested in `if`s.
        (
            "f(positional n: int) = if n >= 0 { if n <= 7 { bitNot(n, width: {w}) } else { 0 } } else { 0 };\n",
            3,
        ),
    ] {
        fits_exactly(src, w);
    }
}

#[test]
fn a_binding_a_typed_lambda_and_a_static_width_carry_the_arm_bound() {
    for (src, w) in [
        // A test of `k = n - 1` narrows `n` to `1..=15`.
        (
            "f(positional n: int) {\n  k = n - 1;\n  return if k >= 0 && k < 15 { bitNot(n, width: {w}) } else { 0 };\n}\n",
            4,
        ),
        // A lambda whose parameter is declared `int`.
        (
            "g = (positional n: int) -> if n >= 0 && n <= 7 { bitNot(n, width: {w}) } else { 0 };\n\
             f(positional n: int) = g(n);\n",
            3,
        ),
        // The width a static name of the unit.
        (
            "w = {w};\nf(positional n: int) = if n >= 0 && n <= 9 { bitNot(n, width: w) } else { 0 };\n",
            4,
        ),
    ] {
        fits_exactly(src, w);
    }
}

#[test]
fn an_arm_no_value_reaches_is_accepted_whatever_its_body() {
    // The design's unreachable arm; the control keeps 5, which reaches the arm.
    unreachable_arm(
        "f(positional n: int) = if n >= 2 && n <= 4 && n mod 4 == 1 { popCount(n - 100) } else { 0 };\n",
        "f(positional n: int) = if n >= 2 && n <= 5 && n mod 4 == 1 { popCount(n - 100) } else { 0 };\n",
    );
    // A static `if`: `debug` is `false` when the program is built.
    unreachable_arm(
        "debug = false;\nf(positional x: int) = if debug { popCount(x - x - 1) } else { x };\n",
        "debug = true;\nf(positional x: int) = if debug { popCount(x - x - 1) } else { x };\n",
    );
    // Two values of different parity made equal.
    unreachable_arm(
        "f(positional x: int, positional y: int) = if x == 2 * y + 1 && x == 2 * y { popCount(x - x - 1) } else { 0 };\n",
        "f(positional x: int, positional y: int) = if x == 2 * y + 1 && x == y { popCount(x - x - 1) } else { 0 };\n",
    );
    // A relation that contradicts itself.
    unreachable_arm(
        "f(positional x: int, positional y: int) = if x < y && y < x { popCount(x - x - 1) } else { 0 };\n",
        "f(positional x: int, positional y: int) = if x < y && y <= x + 1 { popCount(x - x - 1) } else { 0 };\n",
    );
    // The `else` of a test every value meets.
    unreachable_arm(
        "f(positional x: int) = if x >= 0 || x < 0 { 0 } else { popCount(x - x - 1) };\n",
        "f(positional x: int) = if x >= 0 || x < -1 { 0 } else { popCount(x - x - 1) };\n",
    );
}

#[test]
fn the_design_programs_run_as_their_arms_say() {
    // `debug = false; mode = if debug { 1 } else { 2 };` is accepted, and `mode` is 2.
    assert!(rows_pass(
        "debug = false;\nmode = if debug { 1 } else { 2 };\nf(positional x: int) = mode + x\ntest { 0 -> 2, 3 -> 5 }\n"
    ));
    // The arm of `clamp(x) > 10` is never taken.
    assert!(rows_pass(
        "clamp(positional x: int) = if x > 10 { 10 } else { x };\n\
         f(positional x: int) = if clamp(x) > 10 { 1 } else { 2 }\n\
         test { 100 -> 2, 11 -> 2, 10 -> 2, -5 -> 2 }\n"
    ));
}
