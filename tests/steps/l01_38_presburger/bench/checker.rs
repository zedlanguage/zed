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
    // The questions are timed alone, on a unit loaded before the timing (COMPLEXITY.md F85).
    let units: std::collections::BTreeMap<usize, _> = [64, 64 * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            let program = zedc::run::load(src.as_bytes()).unwrap();
            let tokens = zedc::lex::lex_fence(&src).unwrap();
            (m, (zed_tests::deep::statements(&src), tokens, program, src))
        })
        .collect();
    zed_tests::scaling::check("the linear questions of a unit", 64, |m| {
        let (stmts, tokens, program, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, program.unit());
        assert!(refused.is_empty(), "{refused:?}");
    });
}
