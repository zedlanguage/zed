//! The benchmarks of `checker.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::checker::*;

#[test]
fn the_linear_questions_of_a_unit_scale() {
    // `n` functions of two linear tests each, every one asked whether it can hold and fail.
    let unit = |n: usize| {
        let mut src: String = (0..n)
            .map(|i| {
                format!("ok{i}(x: int, y: int) = 0 <= 3 * x + 5 * y && 2 * x - 7 * y <= {i};\n")
            })
            .collect();
        src.push_str(&program("", "x: a, y: a").replace("ok(", "ok0("));
        src
    };
    // The questions are timed alone, on a unit loaded before the timing (COMPLEXITY.md F85), and
    // only at the sizes this process runs (`check_inputs`): loaded at both before the first
    // run, under DynamoRIO, the first phase passed its limit of 20 s (rc 124 at 20.1 s on l43,
    // b22-tests8 job f2, FAIL-bench-pieces-past-limit-on-main).
    let load = |m: usize| {
        let src = unit(m);
        let program = zedc::run::load(src.as_bytes()).unwrap();
        let tokens = zedc::lex::lex_fence(&src).unwrap();
        (zed_tests::deep::statements(&src), tokens, program, src)
    };
    zed_tests::scaling::check_inputs("the linear questions of a unit", 410, load, |unit| {
        let (stmts, tokens, program, src) = unit;
        let refused = zedc::front::linear_questions(src, tokens, stmts, program.unit());
        assert!(refused.is_empty(), "{refused:?}");
    });
}

/// One body of n terms called by n functions of one `int` each: each caller's question read the
/// callee's whole body again (FAIL-linear-question-callee-per-caller, 59.5 times at 8n before).
#[test]
fn the_linear_questions_of_n_callers_of_one_long_body_scale() {
    let unit = |n: usize| {
        let mut src = String::from("many(t) = 0");
        for _ in 0..n {
            src.push_str(" + t[0]");
        }
        src.push_str(";\n");
        for i in 0..n {
            src.push_str(&format!("c{i}(y: int) = many(t: (y, {i}));\n"));
        }
        src.push_str("main(m: MainArgs) { m.stdout <- \"hello\"; }\n");
        src
    };
    let n = 100;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            let program = zedc::run::load(src.as_bytes()).unwrap();
            let tokens = zedc::lex::lex_fence(&src).unwrap();
            (m, (zed_tests::deep::statements(&src), tokens, program, src))
        })
        .collect();
    zed_tests::scaling::check(
        "the linear questions of n callers of one long body",
        n,
        |m| {
            let (stmts, tokens, program, src) = &units[&m];
            let refused = zedc::front::linear_questions(src, tokens, stmts, program.unit());
            assert!(refused.is_empty(), "{refused:?}");
        },
    );
}

/// The test form of `the_linear_questions_of_n_callers_of_one_long_body_scale`: the long body
/// is a test, `0 + t[0] + ... >= 0` (FAIL-linear-question-tuple-callee-per-caller).
#[test]
fn the_linear_questions_of_n_callers_of_one_long_test_scale() {
    let unit = |n: usize| {
        let mut src = String::from("many(t) = 0");
        for _ in 0..n {
            src.push_str(" + t[0]");
        }
        src.push_str(" >= 0;\n");
        for i in 0..n {
            src.push_str(&format!("c{i}(y: int) = many(t: (y, {i}));\n"));
        }
        src.push_str("main(m: MainArgs) { m.stdout <- \"hello\"; }\n");
        src
    };
    let n = 100;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            let program = zedc::run::load(src.as_bytes()).unwrap();
            let tokens = zedc::lex::lex_fence(&src).unwrap();
            (m, (zed_tests::deep::statements(&src), tokens, program, src))
        })
        .collect();
    zed_tests::scaling::check(
        "the linear questions of n callers of one long test",
        n,
        |m| {
            let (stmts, tokens, program, src) = &units[&m];
            let refused = zedc::front::linear_questions(src, tokens, stmts, program.unit());
            assert!(refused.is_empty(), "{refused:?}");
        },
    );
}

/// n callers of one long test body, each passing its own constant to a parameter the body
/// does not read (FAIL-linear-question-const-args-per-caller).
#[test]
fn the_linear_questions_of_n_callers_passing_constants_scale() {
    let unit = |n: usize| {
        let mut src = String::from("many(x, k) = 0");
        for _ in 0..n {
            src.push_str(" + x");
        }
        src.push_str(" >= 0;\n");
        for i in 0..n {
            src.push_str(&format!("c{i}(y: int) = many(x: y, k: {i});\n"));
        }
        src.push_str("main(m: MainArgs) { m.stdout <- \"hello\"; }\n");
        src
    };
    let n = 100;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            let program = zedc::run::load(src.as_bytes()).unwrap();
            let tokens = zedc::lex::lex_fence(&src).unwrap();
            (m, (zed_tests::deep::statements(&src), tokens, program, src))
        })
        .collect();
    zed_tests::scaling::check(
        "the linear questions of n callers passing constants",
        n,
        |m| {
            let (stmts, tokens, program, src) = &units[&m];
            let refused = zedc::front::linear_questions(src, tokens, stmts, program.unit());
            assert!(refused.is_empty(), "{refused:?}");
        },
    );
}
