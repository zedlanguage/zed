//! A test narrows the ints a bit word or `^` reads (DESIGN.md L1.39: a test narrows a scope;
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
        "power(positional x: int, positional n: int) = if n >= 0 { x^n } else { 0 }\n\
         test { (2, 3) -> 8, (2, -1) -> 0 }\n",
        "power(positional x: int, positional n: int) = if n > 0 { x^(n - 1) } else { 0 }\n\
         test { (2, 3) -> 4, (2, -1) -> 0 }\n",
        "power(positional x: int, positional n: int) = if n < 0 { 1 } else { x^n }\n\
         test { (2, 3) -> 8, (2, -1) -> 1 }\n",
        "power(positional x: int, positional n: int) = if !(n < 0) { x^n } else { 0 }\n\
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
        "main(m: MainArgs) {\n  n = int(m.stdin[0]) else 0;\n  \
         m.stdout <- if n >= 0 { String(popCount(n)) } else { \"\" };\n}\n"
    ));
}

#[test]
fn the_arm_where_the_test_gives_no_bound_is_rejected() {
    let out = rejected("bits(positional n: int) = if n >= 0 { 0 } else { popCount(n) };\n");
    assert!(
        out.contains("`popCount` takes `x` in int[0..]: `popCount(n : int[..=-1])`.\n"),
        "{out}"
    );
    assert!(out.contains("this test is false here"), "{out}");
    let out = rejected("many(positional n: int) = n < 0 && popCount(n) > 1;\n");
    assert!(out.contains(" : int[..=-1])`"), "{out}");
    assert!(out.contains("this test is true here"), "{out}");
}

#[test]
fn a_test_on_another_name_is_rejected() {
    let out = rejected(
        "bits(positional n: int, positional m: int) = if m >= 0 { popCount(n) } else { 0 };\n",
    );
    assert!(
        out.contains(
            "`popCount` takes `x` in int[0..]: `popCount(n : int)`. Try \
             `if n >= 0 { popCount(n) } else { … }` instead.\n"
        ),
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
    assert!(out.contains(" : int[-1..])`"), "{out}");
}

#[test]
fn a_test_that_bounds_too_little_is_rejected_with_the_bound_it_gives() {
    let out =
        rejected("power(positional x: int, positional n: int) = if n > -3 { x^n } else { 0 };\n");
    assert!(
        out.contains("Int power with an exponent that may be negative: `x : int ^ n : int[-2..]`"),
        "{out}"
    );
    assert!(out.contains("this test is true here"), "{out}");
    // Either side of `||` may hold, so the arm holds the join of their cases.
    let out =
        rejected("bits(positional n: int) = if n >= 0 || n > -5 { popCount(n) } else { 0 };\n");
    assert!(out.contains(" : int[-4..])`"), "{out}");
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
        out.contains(
            "`popCount` takes `x` in int[0..]: `popCount(g(n) : int)`. Try \
             `x = g(n); if x >= 0 { popCount(x) } else { … }` instead.\n"
        ),
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
    assert!(out.contains(" : int[-2..=-2, 0..])`"), "{out}");
    assert!(out.contains("this test is true in one case here"), "{out}");
    // Of two tests on two names, the failing `&&` leaves either name negative.
    let out = rejected(
        "big(positional n: int, positional m: int) =\n  \
           if n < 0 && m < 0 { 0 } else { popCount(n) };\n",
    );
    assert!(
        out.contains(
            "`popCount` takes `x` in int[0..]: `popCount(n : int)`. Try \
             `if n >= 0 { popCount(n) } else { … }` instead.\n"
        ),
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
    assert!(out.contains(" : int[-2..])`"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("3:8: this test is true here"), "{out}");
    // `a == b` relates `b` to the test on `a`, so both are named; the test on `c` is not.
    let out = rejected(
        "f(positional a: int, positional b: int, positional c: int) =\n  \
           if c > 5 {\n    if a == b {\n      if a >= -2 { popCount(b) } else { 0 }\n    \
           } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains(" : int[-2..])`"), "{out}");
    assert_eq!(out.matches("this test is").count(), 2, "{out}");
    assert!(out.contains("4:10: this test is true here"), "{out}");
    assert!(out.contains("3:8: this test is true here"), "{out}");
    // A name bound in the arm brings in the test on the name its value reads.
    let out = rejected(
        "g(positional n: int, positional m: int) =\n  \
           if m > 1 {\n    if n > 0 { k = n - 2; popCount(k) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains(" : int[-1..])`"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("3:8: this test is true here"), "{out}");
    // `a == b` and `b == c` carry the test on `c` to `a`: all three are named.
    let out = rejected(
        "f(positional a: int, positional b: int, positional c: int) =\n  \
           if a == b {\n    if b == c {\n      if c >= -2 { popCount(a) } else { 0 }\n    \
           } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains(" : int[-2..])`"), "{out}");
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
    assert!(out.contains(" : int[-1..])`"), "{out}");
    assert_eq!(out.matches("this test is").count(), 2, "{out}");
    for at in ["2:6", "5:12"] {
        assert!(
            out.contains(&format!("{at}: this test is true here")),
            "{out}"
        );
    }
    // `k` is read through its summary over `n` where it is read (item PA-let-narrow), so a
    // test on `n` after the binding bears on it and is named: `n > 1` shows `k >= -1`. Before,
    // `k` was read where it was bound, and `n > 5` here did not accept `popCount(k)`.
    assert!(accepted(
        "g(positional n: int) =\n  \
           if n > 0 {\n    k = n - 2;\n    if n > 5 { popCount(k) } else { 0 }\n  } else { 0 };\n",
    ));
    let out = rejected(
        "g(positional n: int) =\n  \
           if n > 0 {\n    k = n - 3;\n    if n > 1 { popCount(k) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains(" : int[-1..])`"), "{out}");
    assert!(out.contains("4:8: this test is true here"), "{out}");
    // A test on `n` that bounds it no further than the one around it is not named.
    let out = rejected(
        "f(positional n: int) =\n  \
           if n >= -1 {\n    if n >= -2 { popCount(n) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains(" : int[-1..])`"), "{out}");
    assert_eq!(out.matches("this test is").count(), 1, "{out}");
    assert!(out.contains("2:6: this test is true here"), "{out}");
    // Under a join, each side of the `||` on `n` is named, the test on `m` around it not.
    let out = rejected(
        "h(positional n: int, positional m: int) =\n  \
           if m < 9 {\n    if n >= 0 || n > -5 { popCount(n) } else { 0 }\n  } else { 0 };\n",
    );
    assert!(out.contains(" : int[-4..])`"), "{out}");
    assert_eq!(out.matches("this test is").count(), 3, "{out}");
    assert!(!out.contains("2:6: this test"), "{out}");
}

#[test]
fn a_test_of_a_name_bound_by_let_narrows_the_input_its_value_reads() {
    // The checker binds a name a test reads with the summary of its value over the one input
    // it reads (item PA-let-check), so the test narrows that input too. Before, the name was
    // read as a value of its own and each of these reads was rejected as any int.
    for src in [
        // A reading with an offset: `m >= 3` holds where `n >= 0`.
        "bits(positional n: int) = { m = n + 3; if m >= 3 { popCount(n) } else { 0 } }\n\
         test { 4 -> 1, -2 -> 0 }\n",
        // Through two bindings: `x` is `2 * n + 1`, at least 1 where `n >= 0`.
        "bits(positional n: int) = { y = n + 1; x = y + n; if x >= 1 { popCount(n) } else { 0 } }\n\
         test { 5 -> 2, -3 -> 0 }\n",
        // An exponent under a test of the steps left: `left <= 10` holds where `n >= 0`.
        "power(positional x: int, positional n: int) =\n  \
           { left = 10 - n; if left <= 10 { x^n } else { 0 } }\n\
         test { (2, 3) -> 8, (2, -1) -> 0 }\n",
        // A call's value named: the name is the input the next binding's summary reads.
        "g(positional n: int) = n - 3;\n\
         f(positional n: int) = { q = g(n); r = q + 1; if r >= 1 { popCount(q) } else { 0 } }\n\
         test { 7 -> 1, 1 -> 0 }\n",
        // A binding inside an arm, tested in an inner one.
        "f(positional n: int) =\n  \
           if n < 100 { m = 2 * n + 1; if m > 0 { popCount(n) } else { 0 } } else { 0 }\n\
         test { 3 -> 2, -4 -> 0, 200 -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
}

#[test]
fn a_test_of_a_name_bound_by_let_gives_its_input_the_bound_it_shows() {
    // `m >= 2` with `m = n + 3` holds where `n >= -1`: rejected with that bound, and the test
    // named.
    let out = rejected(
        "bits(positional n: int) = { m = n + 3; if m >= 2 { popCount(n) } else { 0 } };\n",
    );
    assert!(out.contains(" : int[-1..])`"), "{out}");
    assert!(out.contains("1:43: this test is true here"), "{out}");
    // A summary that decreases: `5 - n >= 0` holds where `n <= 5`.
    let out = rejected(
        "bits(positional n: int) = { m = 5 - n; if m >= 0 { popCount(n) } else { 0 } };\n",
    );
    assert!(out.contains(" : int[..=5])`"), "{out}");
}

#[test]
fn a_value_with_no_summary_or_an_unbounded_other_input_narrows_no_input() {
    // `n * n` has no summary over the ints, so the test narrows the name alone. `n + k` has a
    // summary over `n` and `k` (item PA-let-narrow), but `m >= 0` holds for every `n` with
    // some `k`, and `k` is any int: `n` stays any int.
    for src in [
        "bits(positional n: int) = { q = n * n; r = q + n; if r >= 0 { popCount(n) } else { 0 } };\n",
        "bits(positional n: int, positional k: int) =\n  \
           { m = n + k; if m >= 0 { popCount(n) } else { 0 } };\n",
    ] {
        let out = rejected(src);
        assert!(
            out.contains(
                "`popCount` takes `x` in int[0..]: `popCount(n : int)`. Try \
             `if n >= 0 { popCount(n) } else { … }` instead.\n"
            ),
            "{out}"
        );
    }
}

#[test]
fn a_name_its_tested_name_reads_is_narrowed_by_its_summary() {
    // With `y = n + 1; x = y + n`, a test of `x` narrows `n`, and `y`, read under the test,
    // lies where `n + 1` does over the narrowed `n` (item PA-let-narrow). Before, `y` was read
    // as its own value, any int, and each of these was rejected.
    for src in [
        // `x >= 1` holds where `n >= 0`, so `y >= 1`.
        "bits(positional n: int) =\n  \
           { y = n + 1; x = y + n; if x >= 1 { popCount(y) } else { 0 } }\n\
         test { 3 -> 1, -2 -> 0 }\n",
        // A chain: `c` is `4 * n + 3` through `a` and `b`; `c >= 3` shows `a >= 1`.
        "bits(positional n: int) =\n  \
           { a = n + 1; b = a + n; c = b + a + n; if c >= 3 { popCount(a) } else { 0 } }\n\
         test { 2 -> 2, -1 -> 0 }\n",
        // The steps left of a budget, where the spent steps are tested.
        "power(positional x: int, positional used: int) =\n  \
           { left = 10 - used; spent = used + 0;\n    \
             if spent >= 0 && spent <= 10 { x^left } else { 0 } }\n\
         test { (2, 7) -> 8, (2, 11) -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
    // The bound it gives, when too weak: `x >= -1` holds where `n >= -1`, so `y >= 0`, and
    // `y - 1` is int[-1..].
    let out = rejected(
        "bits(positional n: int) =\n  \
           { y = n + 1; x = y + n; if x >= -1 { popCount(y - 1) } else { 0 } };\n",
    );
    assert!(out.contains(" : int[-1..])`"), "{out}");
}

#[test]
fn a_parameter_narrowed_by_is_has_a_summary() {
    // A value bound where `is` has narrowed a parameter it reads has a summary over the
    // parameter's type there (item PA-let-narrow), so a test of the value narrows the
    // parameter. Before, the value had no summary and each of these was rejected.
    for src in [
        "bits(positional x: int | String) =\n  \
           if x is int { m = x + 3; if m >= 3 { popCount(x) } else { 0 } } else { 0 }\n\
         test { 4 -> 1, -2 -> 0, \"a\" -> 0 }\n",
        // Bound under the narrowing and read under a deeper test of the same parameter.
        "bits(positional x: int | String) =\n  \
           if x is int {\n    m = x + 3;\n    \
             if x is int { if m >= 3 { popCount(x) } else { 0 } } else { 0 }\n  \
           } else { 0 }\n\
         test { 4 -> 1, -2 -> 0, \"a\" -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
    // A test of the value narrows the parameter and no other name.
    let out = rejected(
        "bits(positional x: int | String, positional n: int) =\n  \
           if x is int { m = x + 3; if m >= 3 { popCount(n) } else { 0 } } else { 0 };\n",
    );
    assert!(
        out.contains(
            "`popCount` takes `x` in int[0..]: `popCount(n : int)`. Try \
             `if n >= 0 { popCount(n) } else { … }` instead.\n"
        ),
        "{out}"
    );
}

#[test]
fn a_value_over_two_inputs_narrows_both() {
    // `m = n + k` has a summary over `n` and `k` (item PA-let-narrow): a test of `m` narrows
    // each by the bounds of the other, `n >= 10 - k` with `k` at most 10 giving `n >= 0`.
    // Before, the value had no summary and each of these was rejected.
    for src in [
        "bits(positional n: int, positional k: int) =\n  \
           if k >= 0 && k <= 10 { m = n + k; if m >= 10 { popCount(n) } else { 0 } } else { 0 }\n\
         test { (12, 3) -> 2, (-1, 3) -> 0, (5, 11) -> 0 }\n",
        // The other input, read through a chain over both.
        "bits(positional n: int, positional k: int) =\n  \
           if n >= 0 && n <= 5 { a = k + 1; m = a + n; if m >= 6 { popCount(k) } else { 0 } }\n  \
           else { 0 }\n\
         test { (2, 6) -> 2, (2, -9) -> 0, (7, 1) -> 0 }\n",
        // Free space, `cap - used` with `used` at most 8, tested against what is asked.
        "bits(positional cap: int, positional used: int) =\n  \
           if used >= 0 && used <= 8 {\n    \
             free = cap - used;\n    \
             if free >= 8 { popCount(cap) } else { 0 }\n  \
           } else { 0 }\n\
         test { (20, 3) -> 2, (-4, 3) -> 0, (20, 9) -> 0 }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
    // The bound it gives: `m >= 7` with `k` at most 10 holds where `n >= -3`.
    let out = rejected(
        "bits(positional n: int, positional k: int) =\n  \
           if k >= 0 && k <= 10 { m = n + k; if m >= 7 { popCount(n) } else { 0 } } else { 0 };\n",
    );
    assert!(out.contains(" : int[-3..])`"), "{out}");
}

/// Formerly a known precision limit (COMPLEXITY.md S25, B4), closed by item ST-B4: where
/// `used + free >= 1 || used - free >= 30` holds, the test `used >= free` shows `used >= 1`, so
/// `used - 1` is at least 0, with the test on `cap` between them or without it. A new
/// inequality among the constraints a disjunction's part is projected with makes the part due
/// again (`split` in `product.rs`).
#[test]
fn a_test_between_two_names_after_a_disjunction_on_both_is_exact() {
    let src = "copied(positional used: int, positional free: int, positional cap: int) =\n  \
           if used >= -20 && used <= 20 && free >= -20 && free <= 20 {\n    \
             if used + free >= 1 || used - free >= 30 {\n      \
               if cap >= 0 {\n        \
                 if used >= free { last = used - 1; popCount(last) } else { 0 }\n      \
               } else { 0 }\n    \
             } else { 0 }\n  \
           } else { 0 }\n\
         test { (5, 3, 10) -> 1, (1, 4, 10) -> 0, (8, 0, 9) -> 3, (5, 3, -1) -> 0 }\n";
    assert!(accepted(src), "{}", rejected(src));
    assert!(rows_pass(src), "{src}");
    let without = "copied(positional used: int, positional free: int) =\n  \
           if used >= -20 && used <= 20 && free >= -20 && free <= 20 {\n    \
             if used + free >= 1 || used - free >= 30 {\n      \
               if used >= free { last = used - 1; popCount(last) } else { 0 }\n    \
             } else { 0 }\n  \
           } else { 0 }\n\
         test { (5, 3) -> 1, (1, 4) -> 0, (8, 0) -> 3 }\n";
    assert!(accepted(without), "{}", rejected(without));
    assert!(rows_pass(without), "{without}");
}

/// One random program of the soundness test below: a block of bindings, each a sum of earlier
/// names with small coefficients, a test `t >= c` or `t <= c` of one of them, and `popCount`
/// of another name in its arm. `guard` is `0` for none, `1` for `k` bounded by a test, `2` for
/// `n` narrowed from `int | String` by `is`.
struct Block {
    guard: usize,
    k_range: (i64, i64),
    /// Each binding's coefficients on `n`, `k` and the bindings before it, and its constant.
    lets: Vec<(Vec<i64>, i64)>,
    /// For each binding, `Some((i, m))` when it is `x mod m` of the name `i` (see `read`) in
    /// place of its sum.
    rems: Vec<Option<(usize, i64)>>,
    tested: usize,
    at_least: bool,
    bound: i64,
    /// The name `popCount` reads: `0` is `n`, `1` is `k`, `j + 2` is binding `j`.
    read: usize,
}

impl Block {
    fn random(rng: &mut zed_tests::instances::Rng) -> Block {
        let guard = rng.below(3);
        let lo = rng.int(-3, 3);
        let k_range = (lo, lo + rng.int(0, 6));
        let count = rng.int(1, 4) as usize;
        let lets: Vec<(Vec<i64>, i64)> = (0..count)
            .map(|j| {
                let mut c: Vec<i64> = (0..j + 2).map(|_| 0).collect();
                for _ in 0..rng.int(1, 2) {
                    let at = rng.below(j + 2);
                    c[at] = rng.pick(&[-2, -1, 1, 1, 2]);
                }
                (c, rng.int(-4, 4))
            })
            .collect();
        Block {
            guard,
            k_range,
            rems: vec![None; lets.len()],
            lets,
            tested: rng.below(count),
            at_least: rng.below(4) != 0,
            bound: rng.int(-6, 8),
            read: rng.below(count + 2),
        }
    }

    /// [`Block::random`] with each binding made a remainder `x mod m` of an earlier name, one
    /// time in three (item PA-let-multi).
    fn random_with_remainders(rng: &mut zed_tests::instances::Rng) -> Block {
        let mut block = Block::random(rng);
        for j in 0..block.lets.len() {
            if rng.below(3) == 0 {
                block.rems[j] = Some((rng.below(j + 2), rng.pick(&[2, 3, 4, 8])));
            }
        }
        block
    }

    fn name(i: usize) -> String {
        match i {
            0 => "n".into(),
            1 => "k".into(),
            j => format!("v{}", j - 2),
        }
    }

    /// The values of `n`, `k` and every binding.
    fn values(&self, n: i64, k: i64) -> Vec<i64> {
        let mut vs = vec![n, k];
        for ((c, b), rem) in self.lets.iter().zip(&self.rems) {
            let v = match rem {
                Some((i, m)) => vs[*i].rem_euclid(*m),
                None => c.iter().zip(&vs).map(|(c, v)| c * v).sum::<i64>() + b,
            };
            vs.push(v);
        }
        vs
    }

    /// Whether the arm runs at `(n, k)`, and the operand of `popCount` there.
    fn arm(&self, n: i64, k: i64) -> Option<i64> {
        if self.guard == 1 && !(self.k_range.0 <= k && k <= self.k_range.1) {
            return None;
        }
        let vs = self.values(n, k);
        let t = vs[self.tested + 2];
        let holds = if self.at_least {
            t >= self.bound
        } else {
            t <= self.bound
        };
        holds.then_some(vs[self.read])
    }

    fn source(&self, rows: &[(i64, i64)]) -> String {
        let mut body = String::new();
        for (j, (c, b)) in self.lets.iter().enumerate() {
            if let Some((i, m)) = self.rems[j] {
                body += &format!("v{j} = {} mod {m}; ", Block::name(i));
                continue;
            }
            let mut e = String::new();
            for (i, &c) in c.iter().enumerate().filter(|(_, c)| **c != 0) {
                let x = Block::name(i);
                let term = if c.abs() == 1 {
                    x
                } else {
                    format!("{} * {x}", c.abs())
                };
                e += &match (e.is_empty(), c < 0) {
                    (true, false) => term,
                    (true, true) => format!("0 - {term}"),
                    (false, false) => format!(" + {term}"),
                    (false, true) => format!(" - {term}"),
                };
            }
            if *b != 0 {
                e += &format!(" {} {}", if *b < 0 { "-" } else { "+" }, b.abs());
            }
            body += &format!("v{j} = {e}; ");
        }
        let op = if self.at_least { ">=" } else { "<=" };
        body = format!(
            "{{ {body}if v{} {op} {} {{ popCount({}) }} else {{ 0 }} }}",
            self.tested,
            self.bound,
            Block::name(self.read)
        );
        let (head, body) = match self.guard {
            1 => (
                "positional n: int, positional k: int",
                format!(
                    "if k >= {} && k <= {} {body} else {{ 0 }}",
                    self.k_range.0, self.k_range.1
                ),
            ),
            2 => (
                "positional n: int | String, positional k: int",
                format!("if n is int {body} else {{ 0 }}"),
            ),
            _ => ("positional n: int, positional k: int", body),
        };
        let mut table: Vec<String> = rows
            .iter()
            .map(|&(n, k)| {
                let out = self.arm(n, k).map_or(0, |v| v.count_ones());
                format!("({n}, {k}) -> {out}")
            })
            .collect();
        if self.guard == 2 {
            table.push("(\"a\", 0) -> 0".into());
        }
        if rows.is_empty() {
            format!("f({head}) =\n  {body};\n")
        } else {
            format!("f({head}) =\n  {body}\ntest {{ {} }}\n", table.join(", "))
        }
    }
}

#[test]
fn a_block_of_tested_lets_is_narrowed_soundly_against_the_interpreter() {
    // Random blocks of sums over `n` and `k` (item PA-let-narrow): where the checker accepts
    // `popCount` of a name in the arm of a test of another, no `(n, k)` of the grid
    // `-40..=40` squared that reaches the arm gives it a negative operand; and the rows the
    // interpreter runs give the values computed here. With coefficients at most 2 in size,
    // constants at most 8 and at most 4 bindings, a wrong bound shows within the grid.
    let mut rng = zed_tests::instances::Rng::new(0x5a1e_7e57);
    let (mut accepted_count, mut by_summary) = (0, 0);
    let mut by_guard = [0; 3];
    for _ in 0..400 {
        let block = Block::random(&mut rng);
        let src = block.source(&[]);
        if !super::accepted(&src) {
            continue;
        }
        accepted_count += 1;
        by_guard[block.guard] += 1;
        if block.read != block.tested + 2 {
            by_summary += 1;
        }
        check_against_the_interpreter(&block, &src);
    }
    // Not vacuous, and the item shows: measured 2026-11-07, 115 of the 400 are accepted, 74
    // reading a name other than the tested one, and 25, 64, 26 with no guard, a bound on `k`
    // and `is`; at base 4de1fa22, before the item, 96, 55 and 19, 59, 18.
    let counts = (accepted_count, by_summary, by_guard);
    assert!(
        accepted_count >= 110 && by_summary >= 70 && by_guard[2] >= 24,
        "{counts:?}"
    );
}

/// Where the checker accepted `block`, as `src` without rows: no `(n, k)` of the grid
/// `-40..=40` squared that reaches the arm gives `popCount` a negative operand, and the rows
/// the interpreter runs give the values computed here.
fn check_against_the_interpreter(block: &Block, src: &str) {
    let mut rows = Vec::new();
    for n in -40..=40 {
        for k in -40..=40 {
            if let Some(v) = block.arm(n, k) {
                assert!(v >= 0, "unsound at n = {n}, k = {k}, operand {v}:\n{src}");
                if rows.len() < 6 && (n + k) % 7 == 0 {
                    rows.push((n, k));
                }
            }
        }
    }
    rows.extend([(-3, 1), (0, 0), (5, -2)]);
    let with_rows = block.source(&rows);
    assert!(
        rows_pass(&with_rows),
        "rows differ from the interpreter:\n{with_rows}"
    );
}

#[test]
fn a_block_with_remainders_is_narrowed_soundly_and_keeps_what_it_accepted() {
    // Random blocks of sums and remainders `x mod m` over `n` and `k` (item PA-let-multi), as
    // in the test above. A remainder of a parameter now has the bounds of its modulus where a
    // summary reads it, so the checker accepts more; it must stay sound against the
    // interpreter and accept every block the checker before the item accepted (`BEFORE`, 171
    // of 400, measured at 691a4927). It accepts 193: the 22 more (62, 80, 92, 96, 132, 147,
    // 166, 167, 180, 191, 244, 256, 266, 281, 304, 315, 320, 329, 342, 356, 366, 367) were each
    // rejected with an operand of `int`, a remainder read as any integer. Of the blocks still
    // rejected, two name a narrower operand, both right: 93 (`v1 = k + v0 + 3 >= 8` with
    // `v0 = n mod 8`, so `k >= -2`) `int[-3..=0]` to `int[-2..=0]`, and 286
    // (`v2 = k + k mod 3` where `2 * k + 1 >= -1`) `int` to `int[-1..]`; the other 205 name
    // the same. The test above, of sums alone, accepts the same 115 of 400 as before.
    const BEFORE: [usize; 171] = [
        1, 3, 5, 6, 8, 9, 10, 11, 15, 18, 19, 23, 24, 27, 28, 29, 30, 35, 36, 37, 38, 41, 50, 51,
        52, 54, 55, 57, 59, 60, 63, 66, 67, 68, 70, 71, 76, 78, 79, 85, 86, 87, 88, 91, 95, 97, 98,
        100, 102, 104, 109, 111, 113, 116, 117, 119, 121, 124, 125, 128, 129, 130, 133, 135, 136,
        137, 140, 143, 144, 145, 146, 148, 150, 153, 155, 157, 160, 161, 162, 163, 165, 170, 171,
        172, 175, 177, 178, 179, 184, 195, 196, 198, 199, 201, 205, 206, 211, 213, 214, 215, 218,
        219, 221, 223, 225, 234, 235, 237, 239, 240, 242, 243, 251, 252, 254, 255, 258, 261, 262,
        264, 267, 268, 271, 274, 275, 276, 284, 290, 291, 296, 297, 298, 300, 303, 305, 306, 308,
        310, 316, 318, 319, 321, 323, 327, 330, 339, 340, 341, 343, 345, 348, 349, 350, 352, 358,
        360, 363, 369, 370, 374, 376, 379, 382, 385, 386, 387, 388, 391, 397, 398, 399,
    ];
    let mut rng = zed_tests::instances::Rng::new(0x7e3a_11d5);
    let mut accepted_count = 0;
    for id in 0..400 {
        let block = Block::random_with_remainders(&mut rng);
        let src = block.source(&[]);
        if !super::accepted(&src) {
            assert!(
                BEFORE.binary_search(&id).is_err(),
                "block {id} was accepted before item PA-let-multi:\n{src}\n{}",
                super::rejected(&src)
            );
            continue;
        }
        accepted_count += 1;
        check_against_the_interpreter(&block, &src);
    }
    assert!(accepted_count >= 193, "accepted {accepted_count} of 400");
}

/// The probe of item PA-let-multi: `x_0 = n`, then `q_k = n mod 4; x_k = x_(k-1) + q_k` for `k`
/// up to `d`, and a bit word on `n` where `x_d >= 3 d - slack`.
fn remainders_probe(d: usize, slack: usize) -> String {
    let mut body = String::from("x0 = n; ");
    for k in 1..=d {
        body += &format!("q{k} = n mod 4; x{k} = x{} + q{k}; ", k - 1);
    }
    format!(
        "f(positional n: int) =\n  {{ {body}if x{d} >= {} {{ popCount(n) }} else {{ 0 }} }}\n\
         test {{ 7 -> 3, -1 -> 0, -5 -> 0 }}\n",
        3 * d - slack
    )
}

#[test]
fn an_input_reached_through_a_summary_over_several_inputs_keeps_its_bounds() {
    // Each `q_k = n mod 4` lies in `0..=3`, so `x_d = n + q_1 + ... + q_d >= 3 d` gives
    // `n >= 0` (item PA-let-multi). Before, `q_k`'s product was taken in a scope that did not
    // have `n`, so it was any int, and every one of these was rejected, `d` = 1 too.
    for d in [1, 2, 3, 5, 16] {
        let src = remainders_probe(d, 0);
        assert!(rows_pass(&src), "d = {d}:\n{src}");
    }
    // The bound is the least it can be: `x_d >= 3 d - 1` holds at `n = -1`.
    let out = rejected(&remainders_probe(3, 1));
    assert!(out.contains("popCount"), "{out}");
}

/// A reading `a` checked against a threshold `n` or a constant, `a >= n || a >= 5`, and then
/// the threshold checked, `n >= 0`: either side gives `a >= 0`, so `popCount(a)` is accepted
/// whichever test comes first and whichever side of the `||` is written first (item
/// NARROW-or-order: with the `||` outermost, `a` stayed `int`).
#[test]
fn an_or_test_relating_two_names_narrows_in_any_order() {
    for src in [
        "f(positional a: int, positional n: int) =\n  \
           if a >= n || a >= 5 { if n >= 0 { popCount(a) } else { 0 } } else { 0 }\n\
         test { (3, 2) -> 2, (7, 4) -> 3, (7, -4) -> 0, (-3, 4) -> 0, (1, -2) -> 0 }\n",
        "f(positional a: int, positional n: int) =\n  \
           if a >= 5 || a >= n { if n >= 0 { popCount(a) } else { 0 } } else { 0 }\n\
         test { (3, 2) -> 2, (7, 4) -> 3, (7, -4) -> 0, (-3, 4) -> 0, (1, -2) -> 0 }\n",
        "f(positional a: int, positional n: int) =\n  \
           if n >= 0 { if a >= n || a >= 5 { popCount(a) } else { 0 } } else { 0 }\n\
         test { (3, 2) -> 2, (7, 4) -> 3, (7, -4) -> 0, (-3, 4) -> 0, (1, -2) -> 0 }\n",
        "f(positional a: int, positional n: int) =\n  \
           if n >= 0 { if a >= 5 || a >= n { popCount(a) } else { 0 } } else { 0 }\n\
         test { (3, 2) -> 2, (7, 4) -> 3, (7, -4) -> 0, (-3, 4) -> 0, (1, -2) -> 0 }\n",
    ] {
        assert!(accepted(src), "{src}\n{}", rejected(src));
        assert!(rows_pass(src), "{src}");
    }
}

/// The bound the `||` gives once the threshold is tested is the join of its two sides: with
/// `n >= -1`, `a >= n` gives `a >= -1` and `a >= 5` gives `a >= 5`, so `a` is `int[-1..]` in
/// either order, and the rejection names both tests that give the bound.
#[test]
fn an_or_test_relating_two_names_gives_the_join_of_its_sides_in_any_order() {
    for src in [
        "f(positional a: int, positional n: int) =\n  \
           if a >= n || a >= 5 { if n >= -1 { popCount(a) } else { 0 } } else { 0 };\n",
        "f(positional a: int, positional n: int) =\n  \
           if a >= 5 || a >= n { if n >= -1 { popCount(a) } else { 0 } } else { 0 };\n",
        "f(positional a: int, positional n: int) =\n  \
           if n >= -1 { if a >= n || a >= 5 { popCount(a) } else { 0 } } else { 0 };\n",
    ] {
        let out = rejected(src);
        assert!(out.contains("`popCount(a : int[-1..])`"), "{src}\n{out}");
        assert!(out.contains("n >= -1"), "{src}\n{out}");
    }
}
