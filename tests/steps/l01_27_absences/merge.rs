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

/// The prelude fixes the payload type of `#errs` as `E ->? E`, `E` a union of loose atoms
/// (DESIGN.md sec:failure, row DOC-user-errs-payload): an `#errs` the program writes with any
/// other payload (a number, two numbers, a function with one or two parameters, a prelude
/// function of several signatures, a generic function, a choice of two functions) is rejected
/// at the atom, naming the payload's type and `E ->? E`. Checking goes on as if the payload
/// had that type, so the merge of it with another failure is not rejected again.
#[test]
fn an_errs_the_program_wrote_with_a_payload_that_is_no_set_of_failures_is_rejected() {
    // Each payload, with its type as the message shows it.
    let cases = [
        ("5", "5"),
        ("5, 6", "5, 6"),
        ("g", "g : int -> int"),
        ("h", "h : (int, int) -> int"),
        (
            "min",
            "min : ((int, int) -> int) & ((f64, f64) -> f64) & ((rat, rat) -> rat) & \
             ((f32, f32) -> f32)",
        ),
        (
            "abs",
            "abs : (int -> int) & (f64 -> f64) & (rat -> rat) & (f32 -> f32)",
        ),
        ("q", "q : T -> T"),
        ("if p { g } else { q }", "if p { g } else { q } : T -> T"),
    ];
    let program = |payload: &str| {
        format!(
            "g(positional k: int) = k;\nh(positional k: int, positional j: int) = k;\nq(positional k) = k;\n\
             a(positional p: bool) = if p {{ 1 }} else {{ #errs({payload}) }};\n\
             c(positional p: bool) = if p {{ 2 }} else {{ #bad }};\n\
             x(positional p: bool) = a(p) + c(p);\n"
        )
    };
    let got: Vec<Vec<String>> = cases
        .iter()
        .map(|(p, _)| type_errors(&program(p)))
        .collect();
    let want: Vec<Vec<String>> = (cases.iter())
        .map(|(payload, shown)| {
            vec![format!(
                "Invalid payload for `#errs`: `#errs({shown})`. Its payload has type `E ->? E`, \
                 `E` a union of loose atoms. [#errs({payload})]"
            )]
        })
        .collect();
    assert_eq!(got, want);
}

/// A payload given as a field is rejected, and so is the right type beside a second item.
/// (A set of a family's atoms, which are data, is rejected too: `families.rs`.)
#[test]
fn an_errs_with_a_field_or_two_items_is_rejected() {
    let head = "Invalid payload for `#errs`";
    for (body, shown) in [
        (
            "f(positional p: bool) = #errs(s: {#x});\n",
            "s: {#x} : #x -> #x",
        ),
        (
            "f(positional p: bool) = #errs({#x}, {#y});\n",
            "{#x} : #x -> #x, {#y} : #y -> #y",
        ),
    ] {
        let errors = type_errors(body);
        let [e] = &errors[..] else {
            panic!("{body}: {errors:?}")
        };
        assert!(
            e.starts_with(&format!("{head}: `#errs({shown})`")),
            "{body}: {e}"
        );
    }
}

/// A parameter of no written type given to `#errs` is narrowed to the values that are no
/// number, so a call that passes a number is rejected at the call (DESIGN.md sec:failure).
#[test]
fn an_errs_of_a_parameter_of_no_written_type_narrows_it() {
    let t = "f(positional e) = #errs(e);\n";
    assert_eq!(type_errors(t), Vec::<String>::new(), "{t}");
    let call = format!("{t}y = f(5);\n");
    assert!(!type_errors(&call).is_empty(), "{call}");
}

/// `#errs` with a family of loose failures, the payload the prelude fixes, is accepted, and a
/// merge with it adds its members (DESIGN.md sec:failure).
#[test]
fn an_errs_the_program_wrote_with_a_set_of_failures_is_accepted() {
    let t = "a(positional p: bool) = if p { 1 } else { #errs({#x, #y}) };\n\
             c(positional p: bool) = if p { 2 } else { #bad };\n\
             x(positional p: bool) = a(p) + c(p);\n";
    assert_eq!(type_errors(t), Vec::<String>::new(), "{t}");
    assert_eq!(
        sig(t, "x"),
        "type Part1 = #bad | #x | #y;\nbool -> int | #bad | #errs(Part1 ->? Part1)",
        "{t}"
    );
}
