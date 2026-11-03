//! The bound check of a morphism type `L .. U -> V` (its guarantee `L` within its permission
//! `U`) runs once for every written type, wherever it is written: a parameter, a lambda
//! parameter, a default, a test or an `is`. Loading a program, checking it alone and checking
//! it in a batch give the same message.

use zed_kernel::types::Refusal;
use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

const BAD: &str = "the guarantee (left of `..`) of this morphism type is not within its \
                   permission (right of `..`)";

/// The diagnostics of `src` through `zedc::run::load`, one per line.
fn through_load(src: &str) -> Vec<String> {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e.lines().map(str::to_string).collect(),
    }
}

/// The type errors of `src` through `zedc::check::check`, as `line:col: message`.
fn through_check(src: &str) -> Vec<String> {
    let tokens = lex_fence(src).unwrap();
    let tree = parse(src, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(src, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let info = zedc::check::check(&stmts, &res);
    info.errors
        .iter()
        .map(|e| {
            let before = &src[..e.span.start];
            let line = before.matches('\n').count() + 1;
            let col = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
            format!("{line}:{col}: {}", e.message)
        })
        .collect()
}

/// `src` is rejected with exactly `want` through load, through check, and in a batch: alone
/// on a fresh thread, after another program and after itself.
fn rejected_everywhere(src: &str, want: &[String]) {
    assert_eq!(through_load(src), want, "load: {src}");
    // The checker alone gives the bound errors; elaboration may add its own.
    let bound: Vec<String> = want.iter().filter(|w| w.contains(BAD)).cloned().collect();
    assert_eq!(through_check(src), bound, "check: {src}");
    let s = src.to_string();
    let alone = std::thread::spawn(move || through_load(&s)).join().unwrap();
    assert_eq!(alone, want, "alone: {src}");
    assert!(zedc::run::load(b"f(x: #a .. #a | #b -> int) = 0;\nmain() = 0;\n").is_ok());
    assert_eq!(through_load(src), want, "after another: {src}");
    assert_eq!(through_load(src), want, "again: {src}");
}

#[test]
fn a_parameter_whose_morphism_bound_fails_is_rejected_on_every_path() {
    rejected_everywhere(
        "f(x: #a .. #b -> int) = 0;\nmain() = 0;\n",
        &[format!("1:6: {BAD}")],
    );
    // Nested in a union and a tuple, and as a lambda parameter, a default and an `is`.
    rejected_everywhere(
        "f(x: (int, (#a | #b) .. #a -> int) | int) = 0;\nmain() = 0;\n",
        &[format!("1:12: {BAD}")],
    );
    rejected_everywhere(
        "main() = { g = (y: #a .. #b -> int) -> 0; 0 };\n",
        &[format!("1:20: {BAD}")],
    );
    rejected_everywhere(
        "f(x: int) = x is (#a .. #b -> int);\nmain() = 0;\n",
        &[
            "1:18: `is` cannot test a value against a function type at run time".to_string(),
            format!("1:18: {BAD}"),
        ],
    );
}

#[test]
fn a_parameter_whose_morphism_bound_holds_is_taken() {
    for src in [
        "f(x: #a .. #a | #b -> int) = 0;\nmain() = 0;\n",
        "f(x: (int, #a .. #a -> int)) = 0;\nmain() = 0;\n",
    ] {
        assert!(zedc::run::load(src.as_bytes()).is_ok(), "{src}");
        assert_eq!(through_check(src), Vec::<String>::new(), "{src}");
    }
}

#[test]
fn a_parameter_whose_morphism_bound_check_was_refused_says_why() {
    let src = "f(x: (int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int) = 0;\nmain() = 0;\n";
    rejected_everywhere(
        src,
        &[format!(
            "1:6: {BAD} (not decided: {})",
            Refusal::MorphismSplit.message()
        )],
    );
}

/// The walk is linear in the written types: `n` and `8n` parameters, each with a nested
/// bounded type, cost at most about 8 times as much (16 with noise).
#[test]
fn the_bound_walk_scales_linearly() {
    let program = |n: usize| {
        let params: Vec<String> = (0..n)
            .map(|i| format!("x{i}: (int, #a .. #a | #b -> int) | int"))
            .collect();
        format!("f({}) = 0;\nmain() = 0;\n", params.join(", "))
    };
    let time = |n: usize| {
        let src = program(n);
        let start = std::time::Instant::now();
        assert!(zedc::run::load(src.as_bytes()).is_ok());
        start.elapsed().as_secs_f64()
    };
    time(50);
    let (a, b) = (time(250), time(2000));
    assert!(b < 16.0 * a + 0.05, "250: {a:.4}s, 2000: {b:.4}s");
}
