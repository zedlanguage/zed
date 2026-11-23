//! The steps of a rejection name the type the program gives each operation there, and none
//! for an operation on literals alone that has met no carrier. DESIGN.md sec:diagnostics,
//! "A `/` of integer literals": "An operation on integer literals alone is a literal too and
//! takes the carrier of what it meets", "`1 + 2` adds two integer literals, so it is a literal
//! too and takes the carrier of what it meets; it meets only the `/`", and "Neither side is
//! typed on its own as an `int` before it meets the `/`". The type the checker kept for such
//! a `/` after rejecting it, `f64`, is not one the program gives it.

use super::{rejected, steps};

/// The step of an operation on literals alone that has met no carrier, `what` naming it.
fn open(what: &str) -> String {
    format!(
        "this `{what}` is an operation on literals alone, so it is a literal too and takes the \
         carrier of what it meets"
    )
}

/// The step of an operation on integer literals alone that nothing gives a carrier, so it is
/// an `int`, `what` naming it and `verb` what it does: DESIGN.md sec:diagnostics, "in
/// `y = (1 + 2) * "a";`, rejected at the `*`, the step for `1 + 2` reads "this `+` adds
/// integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is
/// an `int`"" (QUESTIONS A61).
fn uncarried(what: &str, verb: &str) -> String {
    format!(
        "this `{what}` {verb} integer literals alone, so it is a literal too; nothing here \
         gives it a carrier, so it is an `int`"
    )
}

/// The step of such a `/`.
fn open_div() -> String {
    open("/") + "; `/` has no arrow at `int`"
}

#[test]
fn a_division_of_divisions_of_literals_names_no_type_for_them() {
    let out = rejected("y = (1 / 2) / (3 / 4);\n");
    let d = open_div();
    let want = format!(
        "1:5: Nothing gives the integer literals a carrier, and `/` has none at `int`: \
         `y = (1 / 2) / (3 / 4)`. Try `y = (1r / 2) / (3 / 4)` instead.
  [1] 1:5: {d}
      1 | y = (1 / 2) / (3 / 4);
        |     ^^^^^^^ [2]    ^ [7]
        |     ^^^^^^^^^^^^^^^^^ [1]
        |      ^ [3]    ^^^^^^^ [5]
        |          ^ [4] ^ [6]
  [2] 1:5: {d}
  [3] 1:6: this literal, 1, is 1
  [4] 1:10: this literal, 2, is 2
  [5] 1:15: {d}
  [6] 1:16: this literal, 3, is 3
  [7] 1:20: this literal, 4, is 4
  fixes, each checked here:
    y = (1r / 2) / (3 / 4);        y is 2r/3r
    y = (1.0 / 2) / (3 / 4);       y is 0.6666666666666666
    y = (f64(1) / 2) / (3 / 4);    y is 0.6666666666666666"
    );
    // DESIGN's menu also lists `y: rat = …` and `y: f64 = …`. This zedc does not compile a
    // binding with a declared type, so it leaves them out: row LIT-declared-fix-call-arg.
    assert_eq!(out, want);
    assert!(!out.contains("gives f64"), "{out}");
}

/// A `/` of literals alone that holds a decimal never meets `int`, and at the top level its
/// steps are the ones a function body gives (MSG-f32-body-top-agree): `1e40 / 1e10` passed
/// beside an `f32` gives `f64 | rat`, and `1e40`, which no `f32` holds, is the literal that
/// narrows it. Before, the top level said "`/` has no arrow at `int`" and gave no reason, and
/// where an outer call gave the `/` its `f64` after the refusal, as in the row's program
/// `add(x: add(x: 1e40 / 1e10, y: 1.0f32), y: 1)`, it said "this `/` gives f64".
#[test]
fn a_division_of_literals_with_a_decimal_has_the_same_steps_at_the_top_level_as_in_a_body() {
    for call in [
        "add(x: 1e40 / 1e10, y: 1.0f32)",
        "add(x: add(x: 1e40 / 1e10, y: 1.0f32), y: 1)",
    ] {
        let messages = ["y = ", "g() = "].map(|head| {
            zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main(&format!(
                "add(x, y) = x + y;\n{head}{call};\n"
            ))
        });
        let [top, body] = messages.each_ref().map(|out| {
            let mut s = steps(out);
            s.sort_unstable();
            s
        });
        let headline =
            "`add` does not take (f64 | rat, 1.0f32): no arrow of `add` takes these types.";
        for out in &messages {
            assert!(
                out.lines().next().is_some_and(|l| l.ends_with(headline)),
                "{out}"
            );
            assert!(!out.contains("no arrow at `int`"), "{out}");
            assert!(out.contains("this `/` gives f64 | rat\n"), "{out}");
            assert!(out.contains(": the literal 1e40 takes f64 | rat"), "{out}");
        }
        assert_eq!(top, body, "{}\n{}", messages[0], messages[1]);
    }
}

#[test]
fn divisions_of_literals_nested_two_deep_name_no_type_for_any_of_them() {
    let out = rejected("y = ((1 / 2) / (3 / 4)) / (5 / 6);\n");
    let d = open_div();
    assert_eq!(
        steps(&out),
        [
            &*d,
            &d,
            &d,
            "this literal, 1, is 1",
            "this literal, 2, is 2",
            &d,
            "this literal, 3, is 3",
            "this literal, 4, is 4",
            &d,
            "this literal, 5, is 5",
            "this literal, 6, is 6",
        ],
        "{out}"
    );
}

#[test]
fn an_operand_of_a_division_of_literals_is_a_literal_too_and_not_an_int() {
    // The spec's own example: `1 + 2` and `3 + 4` meet only the `/`.
    let out = rejected("q = (1 + 2) / (3 + 4);\n");
    let (d, plus) = (open_div(), open("+"));
    assert_eq!(
        steps(&out),
        [
            &*d,
            &plus,
            "this literal, 1, is 1",
            "this literal, 2, is 2",
            &plus,
            "this literal, 3, is 3",
            "this literal, 4, is 4",
        ],
        "{out}"
    );
    // A `-` of a `/`, and a `^` under one, are literals in the same way.
    let out = rejected("y = -(1 / 2) * \"a\";\n");
    assert_eq!(steps(&out)[..2], [&*open("-"), &d], "{out}");
    let out = rejected("y = 0xFF / 2 ^ 2;\n");
    assert_eq!(steps(&out)[2], open("^"), "{out}");
}

#[test]
fn an_operation_on_literals_that_the_program_gives_a_type_keeps_it() {
    // Nothing gives `1 + 2` a carrier, and no `/` or decimal is in it, so it is the `int` the
    // program gives it: the type found and the program's agree, and the step names it with
    // why (QUESTIONS A61).
    let out = rejected("y = (1 + 2) * \"a\";\n");
    assert_eq!(
        steps(&out)[..4],
        [
            &*uncarried("+", "adds"),
            "this literal, 1, is 1",
            "this literal, 2, is 2",
            "this expression is \"a\"",
        ],
        "{out}"
    );
    // `1 + 2` meets `1.0f64` and takes `f64`, which the step names, not the `int` the walk
    // found for it before it met one.
    let out = rejected("y = ((1 + 2) * 1.0f64) * \"a\";\n");
    assert_eq!(
        steps(&out)[..2],
        ["this `*` gives f64", "this `+` gives f64"],
        "{out}"
    );
    // A `/` of literals that met a carrier is of that carrier.
    let out = rejected("y = (1.0f64 + 7 / 2) * \"a\";\n");
    assert_eq!(
        steps(&out)[..3],
        [
            "this `+` gives f64",
            "this literal, 1.0f64, is 1.0",
            "this `/` gives f64",
        ],
        "{out}"
    );
}

/// An operation on literals with no carrier, rejected beside a value it cannot meet, is shown
/// in the heading as the union of the carriers it can still take (QUESTIONS A60): DESIGN.md
/// sec:diagnostics, "in `y = (1 / 2) * "a";` the heading reads `(f64 | rat, "a")`". A name
/// defined as one is shown the same where it is read.
#[test]
fn an_operation_on_literals_with_no_carrier_is_shown_by_the_carriers_it_can_take() {
    let out = rejected("y = (1 / 2) * \"a\";\n");
    assert!(
        out.starts_with(
            "1:5: `*` does not take (f64 | rat, \"a\"): no arrow of `*` takes these types."
        ),
        "{out}"
    );
    let out = rejected("q = (1 + 2) / (3 + 4);\nz = q * \"a\";\n");
    let second = out.split_once("\n2:5: ").expect("a second rejection").1;
    assert!(
        second.starts_with("`*` does not take (f64 | rat, \"a\")"),
        "{out}"
    );
    assert!(!out.contains("(Never, \"a\")"), "{out}");
}

/// The step of a read of `name`, defined as an operation on literals alone that met no carrier.
fn read_open(name: &str) -> String {
    format!(
        "`{name}` is read here; it is defined as an operation on literals alone, so it takes the \
         carrier of what it meets"
    )
}

#[test]
fn a_name_defined_as_an_operation_on_literals_that_met_no_carrier_is_read_with_no_type() {
    // The spec's `q`, read once more: `q` was rejected, and the type the checker kept for it,
    // `Never`, is not one the program gives it, so no step names it.
    let out = rejected("q = (1 + 2) / (3 + 4);\nz = q * \"a\";\n");
    let (d, plus) = (open_div(), open("+"));
    let second = out.split_once("\n2:5: ").expect("a second rejection").1;
    assert_eq!(
        steps(second)[..4],
        [
            &*read_open("q"),
            "`q` is defined as this expression",
            &d,
            &plus,
        ],
        "{out}"
    );
    assert!(
        !second.contains("`q` is Never") && !second.contains("expression, Never"),
        "{out}"
    );
    // `q = 1 / 2` the same: the `f64` the checker kept for the `/` is not the program's.
    let out = rejected("q = 1 / 2;\nz = q * \"a\";\n");
    let second = out.split_once("\n2:5: ").expect("a second rejection").1;
    assert_eq!(
        steps(second)[..3],
        [&*read_open("q"), "`q` is defined as this expression", &d],
        "{out}"
    );
    assert!(
        !second.contains("`q` is f64") && !second.contains("expression, f64"),
        "{out}"
    );
}

#[test]
fn a_name_defined_as_an_operation_on_literals_of_a_type_is_read_with_its_type() {
    let out = rejected("q = 1 + 2;\nz = q * \"a\";\n");
    assert_eq!(
        steps(&out)[..3],
        [
            "`q` is int here",
            "`q` is defined as this expression, int",
            &*uncarried("+", "adds"),
        ],
        "{out}"
    );
}

/// QUESTIONS A61 for `-`, `*`, `^`, a unary `-` and a nest of them: each operation in the
/// value says why it is an `int`. One that meets a carrier says so by its type instead, and an
/// `int` operand gives an `int` the operation does not lack: `x * (1 + 2)` with `x: int` is
/// not one that nothing gives a carrier.
#[test]
fn each_operation_on_literals_with_no_carrier_says_why_it_is_an_int() {
    let out = rejected("y = ((2 - 1) * 3 ^ 2) * \"a\";\n");
    assert_eq!(
        steps(&out)[..6],
        [
            &*uncarried("*", "multiplies"),
            &*uncarried("-", "subtracts"),
            "this literal, 2, is 2",
            "this literal, 1, is 1",
            &*uncarried("^", "takes a power of"),
            "this literal, 3, is 3",
        ],
        "{out}"
    );
    let out = rejected("y = -(1 + 2) * \"a\";\n");
    assert_eq!(
        steps(&out)[..2],
        [&*uncarried("-", "negates"), &*uncarried("+", "adds")],
        "{out}"
    );
    let out = rejected("x = 4;\ny = (x * (1 + 2)) * \"a\";\n");
    assert!(!out.contains("nothing here gives it a carrier"), "{out}");
    assert!(steps(&out).contains(&"this `+` gives int"), "{out}");
}

/// MSG-wide-value-notes: an operation on literals that meets a use asks its class for a
/// carrier, so its values are what it computes, not the literals that joined the class. The
/// steps and the sentence give the carriers the class may still take, never the union of the
/// literals: `2 + 13` is `int | f32 | f64 | rat`, not `2 | 13`. A name bound to it is an `int`
/// where it is bound, in a body as outside every function (QUESTIONS A63, LIT-name-int-fixed).
#[test]
fn a_sum_of_literals_is_shown_by_its_carriers_not_by_its_literals() {
    let out = rejected("main(m: MainArgs) {\n  m.stdout <- (2 + 13) - \"a\";\n}\n");
    let s = steps(&out);
    assert!(
        out.starts_with("2:15: `-` does not take (int | f32 | f64 | rat, \"a\"): no arrow of `-` takes these types."),
        "{out}"
    );
    assert!(s.contains(&"this `+` gives int | f32 | f64 | rat"), "{out}");
    assert!(!out.contains("2 | 13"), "{out}");
    let out = rejected("main(m: MainArgs) {\n  b = 2 + 13;\n  m.stdout <- b - \"a\";\n}\n");
    let s = steps(&out);
    assert!(
        out.starts_with("3:15: `-` does not take (int, \"a\"): no arrow of `-` takes these types."),
        "{out}"
    );
    assert_eq!(
        s[..3],
        [
            "`b` is int here",
            "`b` is defined as this expression, int",
            &*uncarried("+", "adds"),
        ],
        "{out}"
    );
    assert!(!out.contains("2 | 13"), "{out}");
}

/// The same through a call: `f(2 + 13)` with `f(x) = x + 1` gives 16, so the literals `2 | 13`
/// are not its values either.
#[test]
fn a_call_on_a_sum_of_literals_is_shown_by_its_carriers() {
    let out = rejected(
        "f(positional x) = x + 1;\nmain(m: MainArgs) {\n  m.stdout <- f(2 + 13) - \"a\";\n}\n",
    );
    let s = steps(&out);
    assert!(
        out.starts_with("3:15: `-` does not take (int | f32 | f64 | rat, \"a\"): no arrow of `-` takes these types."),
        "{out}"
    );
    assert!(
        s.contains(&"this call of `f` gives int | f32 | f64 | rat"),
        "{out}"
    );
    assert!(!out.contains("2 | 13"), "{out}");
}

/// A choice between literals computes nothing: its values are the literals, so the steps
/// still give them, `2 | 13`.
#[test]
fn a_choice_between_literals_is_still_shown_by_its_literals() {
    let out = rejected("g(c: bool) = (if c { 2 } else { 13 }) - \"a\";\n");
    let s = steps(&out);
    assert!(s.contains(&"this `if` gives 2 | 13"), "{out}");
}

/// The repairs of a division by zero, in the order DESIGN gives them.
fn div_repairs(at: &str, dividend: &str) -> String {
    format!(
        "  [3] {at}: repair: divide by a value that can be other than 0, such as a parameter \
         `d: rat`: `{dividend} / d`
  [4] {at}: repair: write `#divByZero` in place of this division, where the failure is meant
  [5] {at}: repair: write `#bug(\"…\")` in place of this division, where it is never meant to \
         be reached"
    )
}

/// A `/` of literals whose divisor is zero at `rat` takes the carrier of what it meets, and
/// the one error is that it always fails (DESIGN.md sec:diagnostics, row "Operation that
/// always fails": "A literal takes its carrier before this check: in `y = 1r + 1 / 0;` [...]
/// the one error is that the `/` always gives `#divByZero`, with no error for a literal
/// without a carrier"; QUESTIONS A62). On origin/main the `/` kept no carrier, and zedc gave
/// two false errors: "The suffix makes the literal `1r` a `rat`, never `f64`" and "Nothing
/// gives the literal `1` a carrier".
#[test]
fn a_division_of_literals_by_zero_takes_rat_and_always_fails() {
    let out = rejected("y = 1r + 1 / 0;\n");
    let repairs = div_repairs("1:10", "1");
    let want = format!(
        "1:10: `/` here always fails with `#divByZero`: its divisor is the literal 0, so no \
         value that reaches it gives a rat.
  [1] 1:10: `1 / 0` meets a `rat`, so it is a `rat`
      1 | y = 1r + 1 / 0;
        |          ^^^^^ [1, 3, 4, 5]
        |              ^ [2]
  [2] 1:14: this divisor is always 0
{repairs}"
    );
    assert_eq!(out.trim_end(), want, "{out}");
}

/// The same where the divisor is an operation on literals that works out to zero, and where
/// the zero divisor is inside the divisor of another `/`: the error is at the `/` that
/// divides by zero, the inner one, since a run fails there first.
#[test]
fn a_division_by_a_folded_or_nested_zero_takes_rat_and_always_fails() {
    let out = rejected("y = 1r + (2 - 2 * 1) / (3 - 3);\n");
    assert!(
        out.starts_with(
            "1:10: `/` here always fails with `#divByZero`: its divisor is built from \
             constants and works out to 0, so no value that reaches it gives a rat.\n  [1] \
             1:10: `(2 - 2 * 1) / (3 - 3)` meets a `rat`, so it is a `rat`\n"
        ),
        "{out}"
    );
    let out2 = rejected("y = 1r + 1 / (1 / 0);\n");
    assert!(
        out2.starts_with(
            "1:14: `/` here always fails with `#divByZero`: its divisor is the literal 0, so \
             no value that reaches it gives a rat.\n  [1] 1:10: `1 / (1 / 0)` meets a `rat`, \
             so it is a `rat`\n"
        ),
        "{out2}"
    );
    for o in [&out, &out2] {
        assert_eq!(o.matches("always fails").count(), 1, "{o}");
        assert!(!o.contains("Nothing gives"), "{o}");
        assert!(!o.contains("The suffix makes"), "{o}");
    }
}

/// An operation on literals that met no carrier is printed as the union of its carriers, and
/// its repairs offer one conversion per carrier (DESIGN.md sec:diagnostics, "Types in a
/// message"; QUESTIONS A60): `1r` as well as `1.0f64`. On origin/main the `1r` fix was
/// dropped, since the `*` it is carried to is rejected at `rat` as it is at `f64`.
#[test]
fn an_operation_on_literals_with_no_carrier_offers_each_carrier() {
    let out = rejected("y = (1 / 2) * \"a\";\n");
    assert!(out.contains("    y = (1r / 2) * \"a\";"), "{out}");
    assert!(out.contains("    y = (1.0f64 / 2) * \"a\";"), "{out}");
}
