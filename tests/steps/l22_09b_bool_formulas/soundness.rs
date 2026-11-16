//! The two rules every rewrite of `&&` and `||` keeps (plan row AUDIT-bool-rewrite-soundness;
//! DESIGN.md sec:symbolic, "Boolean formulas", and sec:failure: "The operands are not swapped:
//! `false && d` and `d && false` differ where `d` fails"):
//!
//! 1. No rewrite swaps, absorbs or reorders an operand of `&&` or `||` that can give an atom:
//!    `a && b` is `if a { b } else { false }` and `a || b` is `if a { true } else { b }`, so a
//!    failing left operand fails the term whatever the right one is, and a failing right one
//!    fails it only where the left one lets it be read.
//! 2. A rewrite that drops a comparison because of a binder's domain keeps the comparison
//!    wherever the domain does not prove it: `x > 3` is `true` for `x: int[4..]` and not for
//!    `x: int[3..]`.
//!
//! Each rule is tested at the checker, which gives the types (a failing operand read first
//! leaves its atom in the type; one never read leaves none), and at run time by `zedc run` and by
//! a built executable, which must agree with each other and with the rules. The constant
//! operand (`false`, `true`) is written as a literal, the case a constant fold or an absorption
//! law (`d && false` to `false`) would change. `d` is a build-stage constant that partial
//! evaluation (`zedc_stage::stage::mix`, which `zedc run` and `zedc build` both run first)
//! folds to `#divByZero`, as `partial_evaluation_folds_d_before_either_engine_runs` checks on
//! the staged program. In `constant_operands_keep_their_order` every operand is constant, so
//! partial evaluation evaluates each whole term with the kernel's evaluator and leaves both
//! engines only the printed text; that test checks the evaluator's order, not the mixing of
//! an `if`. In `mixed_operands_keep_their_order` the other operand is known only at run time,
//! so partial evaluation mixes the `if` of each `&&` and `||` itself, keeping the side it
//! knows and leaving the other to run: that is where it could swap the operands, and swapping
//! them there turns that test red (and `run_time_operands_agree_with_the_rules` too), while
//! `constant_operands_keep_their_order` stays green.

use std::ffi::OsString;

use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};
use zed_tests::step_helpers::l01_36a_executables::{Ran, built, dir, executable, interpreter};

/// The signature the checker finds for `f` in `src`, after checking that `src` has no type
/// errors.
fn sig_f(src: &str) -> String {
    let t = format!("{src}\n");
    assert_eq!(type_errors(&t), Vec::<String>::new(), "{src}");
    sig(&t, "f")
}

/// Checks each `(source, signature of f)`.
fn sigs(cases: &[(&str, &str)]) {
    for (src, want) in cases {
        assert_eq!(sig_f(src), *want, "{src}");
    }
}

#[test]
fn a_failing_operand_keeps_its_atom_where_it_is_read() {
    sigs(&[
        // A literal on the left decides the term: the right operand is never read.
        ("f(y: int) = false && (5 div y) > 0;", "(y: int) -> bool"),
        ("f(y: int) = true || (5 div y) > 0;", "(y: int) -> bool"),
        // The same literal on the right: the left operand is read first, and its atom stays.
        // An absorption law (`d && false` to `false`, `d || true` to `true`) would drop it.
        (
            "f(y: int) = (5 div y) > 0 && false;",
            "(y: int) -> bool | #divByZero",
        ),
        (
            "f(y: int) = (5 div y) > 0 || true;",
            "(y: int) -> bool | #divByZero",
        ),
        // Under `!` and nested: De Morgan's laws, or `(d || true) && true` to `true`, would drop it.
        (
            "f(y: int) = !((5 div y) > 0 && false);",
            "(y: int) -> bool | #divByZero",
        ),
        (
            "f(y: int) = ((5 div y) > 0 || true) && true;",
            "(y: int) -> bool | #divByZero",
        ),
        (
            "f(y: int) = if (5 div y) > 0 && false { 1 } else { 2 };",
            "(y: int) -> 2 | #divByZero",
        ),
        // `(d && b) || !b` is `true` wherever `d` is a bool, and still fails where `d` does.
        (
            "f(y: int, b: bool) = ((5 div y) > 0 && b) || !b;",
            "(y: int, b: bool) -> bool | #divByZero",
        ),
        (
            "f(y: int, b: bool) = b || ((5 div y) > 0 && !b);",
            "(y: int, b: bool) -> bool | #divByZero",
        ),
        // A guard: swapping the operands of the first would make it fail where `y == 0`.
        ("f(y: int) = y != 0 && (5 div y) > 0;", "(y: int) -> bool"),
        (
            "f(y: int) = (5 div y) > 0 && y != 0;",
            "(y: int) -> bool | #divByZero",
        ),
        (
            "f(y: int) = if y != 0 && (5 div y) > 0 { 10 div y } else { 1 };",
            "(y: int) -> int",
        ),
        (
            "f(y: int) = if y == 0 || (5 div y) < 0 { 10 div y } else { 1 };",
            "(y: int) -> int | #divByZero",
        ),
    ]);
}

#[test]
fn a_domain_drops_a_comparison_only_where_it_proves_it() {
    sigs(&[
        // `x > 3 && y` is `y` where the domain proves `x > 3`: the `else` arm then has
        // `y == false`, so `10 div k` is never read there. `int[4..]` is the least domain that
        // proves it; `int[3..]` holds 3 and `int` holds every int, so there the `else` arm is
        // also reached with `y` true and `x <= 3`.
        (
            "f(x: int[5..], y: bool, k: int) = if x > 3 && y { 1 } else { if y { 10 div k } else { 2 } };",
            "(x: int[5..], y: bool, k: int) -> 1 | 2",
        ),
        (
            "f(x: int[4..], y: bool, k: int) = if x > 3 && y { 1 } else { if y { 10 div k } else { 2 } };",
            "(x: int[4..], y: bool, k: int) -> 1 | 2",
        ),
        (
            "f(x: int[3..], y: bool, k: int) = if x > 3 && y { 1 } else { if y { 10 div k } else { 2 } };",
            "(x: int[3..], y: bool, k: int) -> int | #divByZero",
        ),
        (
            "f(x: int, y: bool, k: int) = if x > 3 && y { 1 } else { if y { 10 div k } else { 2 } };",
            "(x: int, y: bool, k: int) -> int | #divByZero",
        ),
        // The same with a comparison on the other operand.
        (
            "f(x: int[5..], y: int) = if x > 3 && y == 0 { 1 } else { 10 div y };",
            "(x: int[5..], y: int) -> int[-10..=10]",
        ),
        (
            "f(x: int[4..], y: int) = if x > 3 && y == 0 { 1 } else { 10 div y };",
            "(x: int[4..], y: int) -> int[-10..=10]",
        ),
        (
            "f(x: int[3..], y: int) = if x > 3 && y == 0 { 1 } else { 10 div y };",
            "(x: int[3..], y: int) -> int | #divByZero",
        ),
        (
            "f(x: int, y: int) = if x > 3 && y == 0 { 1 } else { 10 div y };",
            "(x: int, y: int) -> int | #divByZero",
        ),
        // `x > 3` is `false` for `x: int[-100..=3]`, so `x > 3 || y != 0` is `y != 0`; not for
        // `int[-100..=4]`.
        (
            "f(x: int[-100..=3], y: int) = if x > 3 || y != 0 { 10 div y } else { 1 };",
            "(x: int[-100..=3], y: int) -> int[-10..=10]",
        ),
        (
            "f(x: int[-100..=4], y: int) = if x > 3 || y != 0 { 10 div y } else { 1 };",
            "(x: int[-100..=4], y: int) -> int | #divByZero",
        ),
        // A comparison the domain decides, after a failing operand: `d && false` is not
        // `false`, and `d || true` is not `true`, so the atom of `d` stays (rule 1 inside rule 2).
        (
            "f(x: int[-100..=3], y: int) = (5 div y) > 0 && x > 3;",
            "(x: int[-100..=3], y: int) -> bool | #divByZero",
        ),
        (
            "f(x: int[5..], y: int) = (5 div y) > 0 || x > 3;",
            "(x: int[5..], y: int) -> bool | #divByZero",
        ),
        // Before it, the decided comparison decides the term and `d` is never read.
        (
            "f(x: int[-100..=3], y: int) = x > 3 && (5 div y) > 0;",
            "(x: int[-100..=3], y: int) -> bool",
        ),
        (
            "f(x: int[5..], y: int) = x > 3 || (5 div y) > 0;",
            "(x: int[5..], y: int) -> bool",
        ),
    ]);
}

/// `src` built into an executable, then run by `zedc run` and by the executable on each
/// `(arguments, expected line)`: both must print the line and exit 0.
fn both_engines(name: &str, src: &str, runs: &[(&[&str], &str)]) {
    let d = dir(&format!("l22_09b/{name}"));
    let (file, exe) = (d.join(format!("{name}.zed")), d.join(name));
    std::fs::write(&file, src).unwrap();
    built(&file, &exe);
    for (args, want) in runs {
        // `zedc run` and the executable take the program's own arguments after `--`.
        let after: Vec<OsString> = std::iter::once("--".into())
            .chain(args.iter().map(OsString::from))
            .collect();
        let expected = Ran {
            status: 0,
            stdout: format!("{want}\n"),
            stderr: String::new(),
        };
        assert_eq!(
            interpreter(&file, &after, b""),
            expected,
            "zedc run, {args:?}"
        );
        assert_eq!(
            executable(&exe, &after, b""),
            expected,
            "executable, {args:?}"
        );
    }
}

/// `d` is `#divByZero`, a constant of the build stage: `dz(k: 0)` has only constant arguments.
/// Each term prints 1 for `true`, 0 for `false` and 9 for `#divByZero`.
const CONSTANT_OPERANDS: &str = "\
dz(k: int) = (5 div k) > 0;

main(m: MainArgs) {
  d = dz(k: 0);
  m.stdout <- \"1 ${(if d && false { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"2 ${(if false && d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"3 ${(if d || true { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"4 ${(if true || d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"5 ${(if d && true { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"6 ${(if d || false { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"7 ${(if !(d && false) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"8 ${(if !d || true { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"9 ${(if d && d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"10 ${(if (d && false) || true { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"11 ${(if true || (d && false) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"12 ${(if false && (d || true) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"13 ${(if (d || true) && false { 1 } else { 0 }) else #divByZero -> 9}\";
}
";

#[test]
fn constant_operands_keep_their_order() {
    // `d` first fails the term whatever the literal; the literal first decides it.
    both_engines(
        "constant_operands",
        CONSTANT_OPERANDS,
        &[(
            &[],
            "1 9 2 0 3 9 4 1 5 9 6 9 7 9 8 9 9 9 10 9 11 1 12 0 13 9",
        )],
    );
}

/// The arguments are `y`, `x` and `k`. Terms 1 to 6 test domains (rule 2) with run-time
/// operands; terms 7 to 9 test the comparisons ZIR legalization writes with their operands
/// swapped (`a > b` as `b < a`, `a >= b` as `b <= a`), where both operands can fail with
/// different atoms: the result is the merged failure `#errs` in either order (printed 7), and
/// each single failure where only one fails.
const RUN_TIME_OPERANDS: &str = "\
hi(x: int[5..], y: int) = if x > 3 && y == 0 { 1 } else { 10 div y };
any(x: int, y: int) = if x > 3 && y == 0 { 1 } else { 10 div y };
lo(x: int[-100..=3], y: int) = (5 div y) > 0 && x > 3;
lo2(x: int[-100..=3], y: int) = x > 3 && (5 div y) > 0;
hi2(x: int[5..], y: int) = (5 div y) > 0 || x > 3;
hi3(x: int[5..], y: int) = x > 3 || (5 div y) > 0;
inv(k: int) = if k == 3 { k } else { #invalid };
sw(y: int, k: int) = (5 div y) > inv(k: k);
sw2(y: int, k: int) = (5 div y) >= inv(k: k);
sw3(y: int, k: int) = inv(k: k) > (5 div y);

main(m: MainArgs) {
  y = int(m.args[0] else \"\") else 1;
  x = int(m.args[1] else \"\") else 1;
  k = int(m.args[2] else \"\") else 0;
  m.stdout <- \"1 ${hi(x: 7, y: y)}\" ++ \" \" ++
  \"2 ${any(x: x, y: y) else #divByZero -> 9}\" ++ \" \" ++
  \"3 ${(if lo(x: 2, y: y) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"4 ${if lo2(x: 2, y: y) { 1 } else { 0 }}\" ++ \" \" ++
  \"5 ${(if hi2(x: 7, y: y) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"6 ${if hi3(x: 7, y: y) { 1 } else { 0 }}\" ++ \" \" ++
  \"7 ${(if sw(y: y, k: k) { 1 } else { 0 }) else #divByZero -> 9 else #invalid -> 8 else #errs -> 7}\" ++ \" \" ++
  \"8 ${(if sw2(y: y, k: k) { 1 } else { 0 }) else #divByZero -> 9 else #invalid -> 8 else #errs -> 7}\" ++ \" \" ++
  \"9 ${(if sw3(y: y, k: k) { 1 } else { 0 }) else #divByZero -> 9 else #invalid -> 8 else #errs -> 7}\";
}
";

#[test]
fn run_time_operands_agree_with_the_rules() {
    both_engines(
        "run_time_operands",
        RUN_TIME_OPERANDS,
        &[
            // `y == 0`, `x == 1`, `k == 0`: `5 div y` and `inv(k: k)` both fail.
            (&["0", "1", "0"], "1 1 2 9 3 9 4 0 5 9 6 1 7 7 8 7 9 7"),
            // `x == 9` makes `any` take `x > 3`.
            (&["0", "9", "0"], "1 1 2 1 3 9 4 0 5 9 6 1 7 7 8 7 9 7"),
            // `k == 3`: only `5 div y` fails.
            (&["0", "9", "3"], "1 1 2 1 3 9 4 0 5 9 6 1 7 9 8 9 9 9"),
            // `y == 1`: only `inv(k: k)` fails.
            (&["1", "1", "0"], "1 10 2 10 3 0 4 0 5 1 6 1 7 8 8 8 9 8"),
            // Control: nothing fails; 5 > 3, 5 >= 3, and not 3 > 5.
            (&["1", "9", "3"], "1 10 2 10 3 0 4 0 5 1 6 1 7 1 8 1 9 0"),
        ],
    );
}

/// `d` is `#divByZero`, a constant of the build stage, as in [`CONSTANT_OPERANDS`], and `b` is
/// read from the first argument, so it is known only at run time. Each `&&` and `||` here
/// has one operand of each stage: the term is not a build-stage term, and partial evaluation
/// mixes it as an `if` whose condition or arm it knows (`d` evaluated to `#divByZero`) and
/// whose other part it leaves to run.
const MIXED_OPERANDS: &str = "\
dz(k: int) = (5 div k) > 0;

main(m: MainArgs) {
  d = dz(k: 0);
  b = (m.args[0] else \"\") == \"t\";
  m.stdout <- \"1 ${(if d && b { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"2 ${(if b && d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"3 ${(if d || b { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"4 ${(if b || d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"5 ${(if !(d && b) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"6 ${(if (d && b) || true { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"7 ${(if true || (d && b) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"8 ${(if false && (d || b) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"9 ${(if (d || b) && false { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"10 ${(if (b && d) || !b { 1 } else { 0 }) else #divByZero -> 9}\";
}
";

/// The text of `main` in `src` after partial evaluation, the program `zedc run` runs and
/// `zedc build` compiles (`zedc::run::Program::stage`).
fn staged_main(src: &str) -> String {
    let (staged, _) = zedc::run::load(src.as_bytes()).unwrap().stage();
    let main = staged.unit().defs.iter().find(|d| d.name == "main");
    main.expect("main").term.to_string()
}

#[test]
fn partial_evaluation_folds_d_before_either_engine_runs() {
    // Each `${…}` of `CONSTANT_OPERANDS` reads only `d` and literals, so the build evaluates
    // it whole, by the kernel's evaluator, and both engines only push the text.
    let main = staged_main(CONSTANT_OPERANDS);
    assert!(!main.contains("dz("), "{main}");
    assert!(
        main.contains("\"1 9 2 0 3 9 4 1 5 9 6 9 7 9 8 9 9 9 10 9 11 1 12 0 13 9\""),
        "{main}"
    );
    // In `MIXED_OPERANDS` the build evaluates `d` and mixes each `if` the elaborator wrote for
    // an `&&` or `||` around it: `d && b` and `d || b` become `#divByZero`, while `b && d` and
    // `b || d` keep `b` first, to be read at run time.
    let main = staged_main(MIXED_OPERANDS);
    assert!(!main.contains("dz("), "{main}");
    assert!(
        main.contains("\"1 \" ++ String(match #divByZero {"),
        "{main}"
    );
    assert!(
        main.contains("\"3 \" ++ String(match #divByZero {"),
        "{main}"
    );
    assert!(
        main.contains("if b { #divByZero } else { false }"),
        "{main}"
    );
    assert!(main.contains("if b { true } else { #divByZero }"), "{main}");
}

#[test]
fn mixed_operands_keep_their_order() {
    // `d` first fails the term whatever `b` is; `b` first decides it where it decides it.
    both_engines(
        "mixed_operands",
        MIXED_OPERANDS,
        &[
            (&["t"], "1 9 2 9 3 9 4 1 5 9 6 9 7 1 8 0 9 9 10 9"),
            (&["f"], "1 9 2 0 3 9 4 9 5 9 6 9 7 1 8 0 9 9 10 1"),
        ],
    );
}
