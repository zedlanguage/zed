//! Failures of several operands of one application merge into `#errs` of the set of distinct
//! failures (DESIGN.md sec:failure): equal failures merge into one, and a singleton is the atom
//! itself, so `#errs` is in a type only where two operands can carry different failures.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

#[test]
fn different_failures_on_two_operands_merge_into_errs() {
    let t = "f(positional x: int | #notFound, positional y: int | #invalid) = x + y;\n";
    assert_eq!(
        sig(t, "f"),
        "type Part1 = #invalid | #notFound;\n(int | #notFound, int | #invalid) -> int | #errs(Part1 ->? Part1) | #invalid | #notFound"
    );
    let run = format!("{t}a = f(#notFound, #invalid);\nb = f(#invalid, 1);\n");
    assert_eq!(value(&run, "a"), "#errs({#invalid, #notFound})");
    assert_eq!(value(&run, "b"), "#invalid");
}

#[test]
fn the_same_failure_on_both_operands_is_that_failure() {
    // Both operands can only fail with `#notFound`, and two equal failures merge into one, so
    // the sum is a number or `#notFound` and never `#errs`.
    let t = "f(positional x: int | #notFound, positional y: int | #notFound) = x + y;\n";
    assert_eq!(
        sig(t, "f"),
        "type Part1 = int | #notFound;\n(Part1, Part1) -> Part1"
    );
    let run = format!("{t}a = f(#notFound, #notFound);\nb = f(1, #notFound);\nc = f(1, 2);\n");
    assert_eq!(value(&run, "a"), "#notFound");
    assert_eq!(value(&run, "b"), "#notFound");
    assert_eq!(value(&run, "c"), "3");
    // So does a chain of them.
    let three = "g(positional x: int | #notFound, positional y: int | #notFound, \
                 positional z: int | #notFound) = x + y * z;\n";
    assert_eq!(
        sig(three, "g"),
        "type Part1 = int | #notFound;\n(Part1, Part1, Part1) -> Part1"
    );
}

#[test]
fn one_operand_that_can_fail_two_ways_meets_one_of_them() {
    // `x` may be `#none` while `y` is `#notFound`: two different failures at once.
    let t = "f(positional x: int | #none | #notFound, positional y: int | #notFound) = x + y;\n";
    assert_eq!(
        sig(t, "f"),
        "type Part1 = #none | #notFound;\n(int | #none | #notFound, int | #notFound) -> int | #errs(Part1 ->? Part1) | #none | #notFound"
    );
    let run = format!("{t}a = f(#none, #notFound);\nb = f(#notFound, #notFound);\n");
    assert_eq!(value(&run, "a"), "#errs({#none, #notFound})");
    assert_eq!(value(&run, "b"), "#notFound");
}

#[test]
fn one_failing_operand_passes_its_failures_alone() {
    // Only `x` can fail: nothing to merge with, so no `#errs`.
    let t = "f(positional x: int | #none | #notFound, positional y: int) = x + y;\n";
    assert_eq!(
        sig(t, "f"),
        "type Part1 = int | #none | #notFound;\n(Part1, int) -> Part1"
    );
}

#[test]
fn the_same_failure_name_with_a_payload_can_differ() {
    // `#syntaxError(int)` has one value per position, so the two operands, each of which can
    // fail only with `#syntaxError`, can still carry different failures. (A written atom type
    // with a payload is compiled from step L2.5, so `p` builds the atoms.)
    let t = "p(positional n: int) = if n > 0 { n } else { #syntaxError(n) };\n\
             f(positional a: int, positional b: int) = p(a) + p(b);\n";
    assert!(type_errors(t).is_empty(), "{:?}", type_errors(t));
    assert_eq!(
        sig(t, "f"),
        "(int, int) -> int | #errs(#syntaxError(int) ->? #syntaxError(int)) | #syntaxError(int)"
    );
    let run = format!("{t}a = f(-3, -7);\nb = f(-3, -3);\n");
    assert_eq!(
        value(&run, "a"),
        "#errs({#syntaxError(-7), #syntaxError(-3)})"
    );
    assert_eq!(value(&run, "b"), "#syntaxError(-3)");
}

#[test]
fn a_nested_chain_merges_into_one_flat_set() {
    // The inner sum may already be `#errs`; the outer one adds its members, never a nested set,
    // and the type holds `#errs` once.
    let t = "f(positional x: int | #a, positional y: int | #b, positional z: int | #c) \
             = (x + y) + z;\n";
    assert_eq!(
        sig(t, "f"),
        "type Part1 = #a | #b | #c;\n(int | #a, int | #b, int | #c) -> int | #a | #b | #c | #errs(Part1 ->? Part1)"
    );
    let run = format!("{t}abc = f(#a, #b, #c);\nab = f(#a, #b, 1);\nac = f(#a, 1, #c);\n");
    assert_eq!(value(&run, "abc"), "#errs({#a, #b, #c})");
    assert_eq!(value(&run, "ab"), "#errs({#a, #b})");
    assert_eq!(value(&run, "ac"), "#errs({#a, #c})");
    // A failure already in the inner set is one member, not two.
    let again = "g(positional x: int | #a, positional y: int | #b, positional z: int | #a) \
                 = (x + y) + z;\n";
    assert_eq!(
        sig(again, "g"),
        "type Part1 = int | #a;\ntype Part2 = #a | #b;\n(Part1, int | #b, Part1) -> int | #a | #b | #errs(Part2 ->? Part2)"
    );
    assert_eq!(
        value(&format!("{again}v = g(#a, #b, #a);\n"), "v"),
        "#errs({#a, #b})"
    );
}

#[test]
fn else_handles_a_merged_failure_as_it_handles_one() {
    let t = "f(positional x: int | #notFound, positional y: int | #none) = (x + y) else 0;\n";
    assert_eq!(sig(t, "f"), "(int | #notFound, int | #none) -> int");
    let run = format!("{t}a = f(#notFound, #none);\nb = f(#notFound, 1);\nc = f(2, 3);\n");
    assert_eq!(value(&run, "a"), "0");
    assert_eq!(value(&run, "b"), "0");
    assert_eq!(value(&run, "c"), "5");
}

#[test]
fn the_readme_examples_give_these_values() {
    // README.md, step 3: two different failures meet, and `else` replaces the merged value.
    let step3 = "one = 1 * #notFound;\n\
                 both = (1 + #notFound) + #invalid;\n\
                 bothOrZero = ((1 + #notFound) + #invalid) else 0;\n";
    assert_eq!(value(step3, "one"), "#notFound");
    assert_eq!(value(step3, "both"), "#errs({#invalid, #notFound})");
    assert_eq!(value(step3, "bothOrZero"), "0");
    // README.md, the table of the orders of a merge's additions: both give one value.
    let orders = "first = (#notFound + 8) + #invalid;\nsecond = (#invalid + 8) + #notFound;\n";
    assert_eq!(value(orders, "first"), "#errs({#invalid, #notFound})");
    assert_eq!(value(orders, "second"), "#errs({#invalid, #notFound})");
}

/// An `#errs` the program writes itself, with a payload that is not a set of failures (a
/// number, two numbers, a function with one or two parameters, a prelude function of several
/// signatures, a generic function, a choice of two functions), has members the checker does
/// not know, so the merge of it with another failure is `#errs` with any payload, `#errs(..)`
/// (item TEST-types-unreached-paths). A payload that holds a function cannot go into the
/// merged `#errs`, which holds data only: the kernel stops such a run with "`+` given several
/// failures, one of which holds a function, which `#errs` cannot hold", so the checker refuses
/// the merge at that operand (row FIX-functions-in-tuples); the signature is the same.
#[test]
fn a_merge_with_an_errs_the_program_wrote_has_unknown_members() {
    // Each payload, with the type of the failure that holds it when it holds a function.
    for (payload, held) in [
        ("5", None),
        ("5, 6", None),
        ("g", Some("int -> int")),
        ("h", Some("(int, int) -> int")),
        (
            "min",
            Some(
                "((int, int) -> int) & ((f64, f64) -> f64) & ((rat, rat) -> rat) & \
                 ((f32, f32) -> f32)",
            ),
        ),
        (
            "abs",
            Some("(int -> int) & (f64 -> f64) & (rat -> rat) & (f32 -> f32)"),
        ),
        ("q", Some("T -> T")),
        ("if p { g } else { q }", Some("T -> T")),
    ] {
        let t = format!(
            "g(positional k: int) = k;\nh(positional k: int, positional j: int) = k;\nq(positional k) = k;\n\
             a(positional p: bool) = if p {{ 1 }} else {{ #errs({payload}) }};\n\
             c(positional p: bool) = if p {{ 2 }} else {{ #bad }};\n\
             x(positional p: bool) = a(p) + c(p);\n"
        );
        let errors = type_errors(&t);
        let want: Vec<String> = held
            .map(|f| {
                format!(
                    "Cannot merge a failure that may hold a function into `#errs`: `a(p) : \
                     #errs({f})`. [a(p)]"
                )
            })
            .into_iter()
            .collect();
        assert_eq!(errors, want, "{t}");
        assert_eq!(sig(&t, "x"), "bool -> int | #bad | #errs(..)", "{t}");
    }
}
