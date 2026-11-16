//! The design's examples of step L1.39 written with a declared range (RANGE-L1): the arm of a
//! test starts from the parameter's range, not from every int.

use zed_tests::step_helpers::l01_39_reduced_product::{arm, ranged_function};
use zedc::store::product::arms;

/// `h(n: int[0..=10]) = if n mod 4 == 1 { n } else { 0 }`: the arm's `n` is `int[1..=9]`, the
/// members 1, 5 and 9, as when the range is written as a test (spec.rs).
#[test]
fn an_arm_of_a_declared_range_holds_what_the_test_keeps() {
    let (scope, body) = ranged_function("ok(n: int[0..=10]) = if n mod 4 == 1 { n } else { 0 };");
    let a = arms(&body, &scope);
    let n = arm(&a, "((n mod 4) == 1)", true).scope.get("n");
    assert_eq!(n.ints().hull().to_string(), "[1..=9]");
    assert_eq!(n.cell.congruence.element.to_string(), "1 mod 4");
    let other = arm(&a, "((n mod 4) == 1)", false).scope.get("n");
    assert_eq!(other.ints().to_string(), "[0..=0, 2..=4, 6..=8, 10..=10]");
}

/// A test that no member of the range passes leaves its arm unreached.
#[test]
fn a_test_outside_the_range_reaches_no_arm() {
    let (scope, body) = ranged_function("ok(n: int[1..]) = if n <= 0 { 1 } else { 2 };");
    let a = arms(&body, &scope);
    assert!(!arm(&a, "(n <= 0)", true).reachable());
    assert!(arm(&a, "(n <= 0)", false).reachable());
}

/// `src` with a `main`, so that `load` runs it as a program.
fn program(src: &str) -> String {
    format!("{src}main(m: MainArgs) -> int {{ m.stdout <- \"a\"; return 0; }}\n")
}

/// The first line of the diagnostics of the rejected program `src`, without the file's name.
fn headline(src: &str) -> String {
    let out = zed_tests::step_helpers::l01_29_diagnostics::rejected(&program(src));
    out.lines().next().unwrap_or("").to_string()
}

/// Whether the program `src` is accepted.
fn accepted(src: &str) -> bool {
    zedc::run::load(program(src).as_bytes()).is_ok()
}

/// DESIGN.md L1.39: `f(x: int[1..]) = x` rejects `f(0)` and accepts `f(1)`. The parameter is
/// named, so the call passes it by name (sec:values_morphisms); by position it is
/// `positional x: int[1..]`.
#[test]
fn a_call_outside_the_range_is_rejected_and_one_inside_is_accepted() {
    assert_eq!(
        headline("f(x: int[1..]) = x;\na = f(x: 0);\n"),
        "2:5: `f` takes `x` in int[1..]: `f(x: 0 : int)`."
    );
    assert!(accepted("f(x: int[1..]) = x;\na = f(x: 1);\n"));
    assert_eq!(
        headline("f(positional x: int[1..]) = x;\na = f(0);\n"),
        "2:5: `f` takes `x` in int[1..]: `f(0 : int)`."
    );
    assert!(accepted("f(positional x: int[1..]) = x;\na = f(1);\n"));
    // A value the caller has not tested may lie outside; one it has tested may not.
    assert_eq!(
        headline("f(x: int[1..]) = x;\ng(y: int) = f(x: y);\n"),
        "2:13: `f` takes `x` in int[1..]: `f(x: y : int)`. \
         Try `if y >= 1 { f(x: y) } else { … }` instead."
    );
    assert!(accepted(
        "f(x: int[1..]) = x;\ng(y: int) = if y >= 1 { f(x: y) } else { 0 };\n"
    ));
    // A range passed to a narrower range, and to a wider one.
    assert!(!accepted(
        "f(x: int[1..]) = x;\ng(y: int[0..=9]) = f(x: y);\n"
    ));
    assert!(accepted(
        "f(x: int[0..]) = x;\ng(y: int[1..=9]) = f(x: y);\n"
    ));
}

/// A range that holds no int is rejected where it is declared (DESIGN.md L1.39, the row
/// "Unsatisfiable declared constraints"), with the range between the same bounds as a repair.
#[test]
fn an_empty_range_is_rejected_at_its_parameter() {
    let out =
        zed_tests::step_helpers::l01_29_diagnostics::rejected(&program("f(x: int[5..=4]) = x;\n"));
    let lines: Vec<&str> = out.lines().take(2).collect();
    assert_eq!(
        lines,
        [
            "1:6: the parameter `x` is declared `int[5..=4]`, a range that holds no int, so no \
             call can pass it a value.",
            "  [1] 1:6: repair: write `x: int[4..=5]`, the range from the lesser bound through \
             the greater",
        ]
    );
    // `..<` at its low bound is empty too; one int is not.
    assert!(headline("f(y: int[5..<5]) = y;\n").contains("a range that holds no int"));
    assert!(accepted("f(y: int[5..=5]) = y;\n"));
}

/// A range is the parameter's ints where a prelude word reads them: `popCount` takes `int[0..]`.
#[test]
fn a_prelude_word_reads_the_range_of_its_argument() {
    assert!(accepted("f(x: int[0..=255]) = popCount(x);\n"));
    assert_eq!(
        headline("f(x: int[-1..=255]) = popCount(x);\n"),
        "1:23: `popCount` takes `x` in int[0..]: `popCount(x : int[-1..=255])`. \
         Try `if x >= 0 { popCount(x) } else { … }` instead."
    );
}

/// A function declared with a range is not a function of every int: passed where one is
/// expected, the message names its parameter, and says the domain is narrower than the
/// slot's (MSG-fn-domain-wider-repair, part 2); called on a value outside it, the value.
#[test]
fn a_ranged_function_passed_as_a_value_names_its_parameter() {
    assert_eq!(
        headline(
            "f(positional x: int[1..]) = x;\napply(g: (int) -> int) = g(1);\na = apply(g: f);\n"
        ),
        "3:14: `f` is `int[1..] -> int[1..]`, not `int -> int`: its domain is narrower than \
         `int -> int`'s, `x` in `int[1..]` where `int -> int` passes any `int`, and a function \
         passed as `int -> int` must take exactly that domain."
    );
    assert_eq!(
        headline("f(x: int[1..]) = x;\nh = f;\na = h(x: 0);\n"),
        "3:5: `h` takes `x` in int[1..]: `h(x: 0 : int)`."
    );
}
