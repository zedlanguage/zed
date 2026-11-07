//! A test narrows the ints a bit word or `**` reads (DESIGN.md L1.39: a test narrows a scope;
//! L1.17: an exponent repaired by a test `n >= 0`). The checker reads an operand in the scope
//! of the reduced product that the tests it is under make: the arms of `if` and `else if`, the
//! second side of `&&` and `||`, and `!`. The arm a test does not narrow, a test on another
//! name, and a name bound again inside the arm are still rejected.

use super::{accepted, rejected};

/// Whether every row of every table of `src` passes, and there is one.
fn rows_pass(src: &str) -> bool {
    let out = zedc::testing::test(src);
    !out.is_empty() && out.iter().all(|o| o.failure.is_none())
}

#[test]
fn a_bit_word_under_a_test_that_its_operand_is_at_least_zero_is_accepted() {
    // The population count of a non-negative number, 0 for a negative one.
    assert!(rows_pass(
        "bits(positional n: int) = if n >= 0 { popCount(n) } else { 0 }\n\
         test { 3 -> 2, -1 -> 0 }\n"
    ));
}

#[test]
fn an_exponent_under_a_test_is_accepted() {
    // A power whose exponent a test shows is at least 0: in the arm where the test holds, in
    // the arm where its opposite fails, through `!`, and with the exponent computed from the
    // tested name.
    for src in [
        "power(positional x: int, positional n: int) = if n >= 0 { x ** n } else { 0 }\n\
         test { (2, 3) -> 8, (2, -1) -> 0 }\n",
        "power(positional x: int, positional n: int) = if n > 0 { x ** (n - 1) } else { 0 }\n\
         test { (2, 3) -> 4, (2, -1) -> 0 }\n",
        "power(positional x: int, positional n: int) = if n < 0 { 1 } else { x ** n }\n\
         test { (2, 3) -> 8, (2, -1) -> 1 }\n",
        "power(positional x: int, positional n: int) = if !(n < 0) { x ** n } else { 0 }\n\
         test { (2, 3) -> 8, (2, -1) -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
}

#[test]
fn each_arm_of_an_else_if_chain_holds_what_the_tests_before_it_show() {
    // A bucket by size: the last arm holds the failures of both tests before it.
    assert!(rows_pass(
        "bucket(positional n: int) =\n  \
           if n < 0 { 0 } else if n < 8 { popCount(n) } else { popCount(n) + 10 }\n\
         test { -3 -> 0, 5 -> 2, 8 -> 11 }\n"
    ));
    // An inner `if` holds what the outer one shows.
    assert!(rows_pass(
        "small(positional n: int) =\n  \
           if n >= 0 { if n < 100 { popCount(n) } else { 7 } } else { 0 }\n\
         test { 4 -> 1, 200 -> 7, -1 -> 0 }\n"
    ));
}

#[test]
fn the_sides_of_and_and_or_narrow() {
    for src in [
        // The second side of `&&` is read where the first holds.
        "many(positional n: int) = n >= 0 && popCount(n) > 1\n\
         test { 3 -> true, 1 -> false, -1 -> false }\n",
        // The second side of `||` is read where the first fails.
        "many(positional n: int) = n < 0 || popCount(n) > 1\n\
         test { 3 -> true, 1 -> false, -1 -> true }\n",
        // Both sides of a holding `&&` hold in the arm.
        "both(positional n: int, positional m: int) =\n  \
           if n >= 0 && m >= 0 { popCount(n) + popCount(m) } else { 0 }\n\
         test { (3, 1) -> 3, (-1, 1) -> 0 }\n",
        // Both sides of a failing `||` fail in the other arm.
        "both(positional n: int, positional m: int) =\n  \
           if n < 0 || m < 0 { 0 } else { popCount(n) + popCount(m) }\n\
         test { (3, 1) -> 3, (-1, 1) -> 0 }\n",
        // `!` of an `||` is the `&&` of the opposites.
        "within(positional n: int) = if !(n < 0 || n > 10) { popCount(n) } else { 0 }\n\
         test { 4 -> 1, 20 -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
}

#[test]
fn a_name_bound_in_an_arm_holds_what_the_test_shows_of_its_value() {
    // `k` is bound to `n - 1` where `n > 0`, so it is at least 0, and an inner test bounds it
    // above too.
    assert!(rows_pass(
        "below(positional n: int) = if n > 0 { k = n - 1; popCount(k) } else { 0 }\n\
         test { 4 -> 2, 0 -> 0 }\n"
    ));
    assert!(rows_pass(
        "below(positional n: int) =\n  \
           if n > 0 { k = n - 1; if k < 5 { popCount(k) } else { 0 } } else { 0 }\n\
         test { 4 -> 2, 0 -> 0, 9 -> 0 }\n"
    ));
    // An input read from a line and tested in `main`.
    assert!(accepted(
        "main(stdin: Lines) -> (stdout: Lines) {\n  n = int(stdin[1]) else 0;\n  \
         stdout <- if n >= 0 { String(popCount(n)) } else { \"\" };\n}\n"
    ));
}

#[test]
fn the_arm_where_the_test_gives_no_bound_is_rejected() {
    let out = rejected("bits(positional n: int) = if n >= 0 { 0 } else { popCount(n) };\n");
    assert!(
        out.contains("`popCount` takes `x` in int[0..], and this `x` is int[..=-1]"),
        "{out}"
    );
    assert!(out.contains("this test is false here"), "{out}");
    let out = rejected("many(positional n: int) = n < 0 && popCount(n) > 1;\n");
    assert!(out.contains("this `x` is int[..=-1]"), "{out}");
    assert!(out.contains("this test is true here"), "{out}");
}

#[test]
fn a_test_on_another_name_is_rejected() {
    let out = rejected(
        "bits(positional n: int, positional m: int) = if m >= 0 { popCount(n) } else { 0 };\n",
    );
    assert!(
        out.contains("`popCount` takes `x` in int[0..], and this `x` is int\n"),
        "{out}"
    );
    assert!(!out.contains("this test is"), "{out}");
}

#[test]
fn a_name_bound_again_in_the_arm_is_rejected() {
    // The inner `n` is `m`, which the test says nothing of.
    let out = rejected(
        "bits(positional n: int, positional m: int) =\n  \
           if n >= 0 { n = m; popCount(n) } else { 0 };\n",
    );
    assert!(out.contains("`popCount` takes `x` in int[0..]"), "{out}");
    // A value bound in the arm that the test does not bound below 0.
    let out =
        rejected("bits(positional n: int) = if n > 0 { k = n - 2; popCount(k) } else { 0 };\n");
    assert!(out.contains("this `x` is int[-1..]"), "{out}");
}

#[test]
fn a_test_that_bounds_too_little_is_rejected_with_the_bound_it_gives() {
    let out = rejected(
        "power(positional x: int, positional n: int) = if n > -3 { x ** n } else { 0 };\n",
    );
    assert!(
        out.contains("`**` on an int needs an exponent of at least 0, and this one is int[-2..]"),
        "{out}"
    );
    assert!(out.contains("this test is true here"), "{out}");
    // Either side of `||` may hold, so the arm holds the join of their cases.
    let out =
        rejected("bits(positional n: int) = if n >= 0 || n > -5 { popCount(n) } else { 0 };\n");
    assert!(out.contains("this `x` is int[-4..]"), "{out}");
    assert!(out.contains("this test is true in one case here"), "{out}");
}

#[test]
fn a_test_on_a_call_the_operand_repeats_is_rejected_and_its_named_value_accepted() {
    // Each call is a value of its own to the checker (arms.rs, C26), so the test on one says
    // nothing of the other; a name for the value carries the test to its read.
    let out = rejected(
        "g(positional n: int) = n - 3;\n\
         f(positional n: int) = if g(n) >= 0 { popCount(g(n)) } else { 0 };\n",
    );
    assert!(
        out.contains("`popCount` takes `x` in int[0..], and this `x` is int\n"),
        "{out}"
    );
    assert!(rows_pass(
        "g(positional n: int) = n - 3;\n\
         f(positional n: int) = { m = g(n); if m >= 0 { popCount(m) } else { 0 } }\n\
         test { 5 -> 1, 1 -> 0 }\n"
    ));
}

#[test]
fn a_case_no_value_reaches_adds_nothing_to_the_join() {
    for src in [
        // A size class where both tests on `n` fail: the case where the first holds and the
        // second fails is the one reached, the other (`n < 0` and `n >= 4`) none.
        "big(positional n: int, positional m: int) =\n  \
           if n < 0 && n < 4 { 0 } else { if m >= 0 || m == -2 { popCount(n) + m } else { 1 } }\n\
         test { (5, 1) -> 3, (-1, 1) -> 0, (5, -2) -> 0, (5, -9) -> 1 }\n",
        // An arm no value reaches reads every name as empty, so any read there is accepted.
        "never(positional n: int) = if n >= 0 { if n < 0 { popCount(n) } else { 1 } } else { 0 }\n\
         test { 3 -> 1, -1 -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
    // `m` is not narrowed by the tests on `n`: its read is rejected, with the tests that decide
    // where it is read.
    let out = rejected(
        "big(positional n: int, positional m: int) =\n  \
           if n < 0 && n < 4 { 0 } else { if m >= 0 || m == -2 { popCount(m) } else { 1 } };\n",
    );
    assert!(out.contains("this `x` is int[-2..=-2, 0..]"), "{out}");
    assert!(out.contains("this test is true in one case here"), "{out}");
    // Of two tests on two names, the failing `&&` leaves either name negative.
    let out = rejected(
        "big(positional n: int, positional m: int) =\n  \
           if n < 0 && m < 0 { 0 } else { popCount(n) };\n",
    );
    assert!(
        out.contains("`popCount` takes `x` in int[0..], and this `x` is int\n"),
        "{out}"
    );
}

#[test]
fn a_rejection_names_the_tests_that_bear_on_its_operand_and_no_others() {
    // A sensor reading `n` checked under a test on a mode `m`: the rejection of `popCount(n)`
    // names the test on `n` and not the one on `m`.
    let out = rejected(
        "f(positional n: int, positional m: int) =\n  \
           if m >= 0 {\n    if n >= -2 { popCount(n) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-2..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("3:8: this test is true here"), "{out}");
    // `a == b` relates `b` to the test on `a`, so both are named; the test on `c` is not.
    let out = rejected(
        "f(positional a: int, positional b: int, positional c: int) =\n  \
           if c > 5 {\n    if a == b {\n      if a >= -2 { popCount(b) } else { 0 }\n    \
           } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-2..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 2, "{out}");
    assert!(out.contains("4:10: this test is true here"), "{out}");
    assert!(out.contains("3:8: this test is true here"), "{out}");
    // A name bound in the arm brings in the test on the name its value reads.
    let out = rejected(
        "g(positional n: int, positional m: int) =\n  \
           if m > 1 {\n    if n > 0 { k = n - 2; popCount(k) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-1..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("3:8: this test is true here"), "{out}");
    // `a == b` and `b == c` carry the test on `c` to `a`: all three are named.
    let out = rejected(
        "f(positional a: int, positional b: int, positional c: int) =\n  \
           if a == b {\n    if b == c {\n      if c >= -2 { popCount(a) } else { 0 }\n    \
           } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-2..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 3, "{out}");
    for at in ["2:6", "3:8", "4:10"] {
        assert!(
            out.contains(&format!("{at}: this test is true here")),
            "{out}"
        );
    }
    // Three readings each checked against a threshold `n`, then `n >= -1`: the rejection of
    // `popCount(a0)` names `a0 >= n` and `n >= -1`, not the tests of `a1` and `a2` on `n`.
    let out = rejected(
        "f(positional n: int, positional a0: int, positional a1: int, positional a2: int) =\n  \
           if a0 >= n {\n    if a1 >= n {\n      if a2 >= n {\n        \
           if n >= -1 { popCount(a0) } else { 0 }\n      } else { 0 }\n    } else { 0 }\n  \
           } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-1..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 2, "{out}");
    for at in ["2:6", "5:12"] {
        assert!(
            out.contains(&format!("{at}: this test is true here")),
            "{out}"
        );
    }
    // The value of `k` is read where it was bound, so a test on `n` after the binding says
    // nothing of it and is not named.
    let out = rejected(
        "g(positional n: int) =\n  \
           if n > 0 {\n    k = n - 2;\n    if n > 5 { popCount(k) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-1..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("2:6: this test is true here"), "{out}");
    // A test on `n` that bounds it no further than the one around it is not named.
    let out = rejected(
        "f(positional n: int) =\n  \
           if n >= -1 {\n    if n >= -2 { popCount(n) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-1..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("2:6: this test is true here"), "{out}");
    // Under a join, each side of the `||` on `n` is named, the test on `m` around it not.
    let out = rejected(
        "h(positional n: int, positional m: int) =\n  \
           if m < 9 {\n    if n >= 0 || n > -5 { popCount(n) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains("this `x` is int[-4..]"), "{out}");
    assert_eq!(out.matches("this test is").count(), 3, "{out}");
    assert!(!out.contains("2:6: this test"), "{out}");
}
