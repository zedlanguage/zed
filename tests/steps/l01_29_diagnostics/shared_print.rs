//! Row MSG-shared-print (QUESTIONS A3 and A4, COMPLEXITY F89): the rejection text is linear in
//! the derivation. A function held in tuples or atoms and compared with `==`, in five shapes: n
//! separate tuples, each an error of its own, whose shared step (the declaration of the
//! function) is printed in full once; and one error through n tuples written in one expression,
//! made by n bindings, n atoms, or n nested calls of a function that wraps its argument.

use zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main;

const SCALE: &str = "scale(positional x) = x * int(2);\n";

/// `n` tuples, each holding `scale`, each compared with `==`: `n` errors.
pub(super) fn many(n: usize) -> String {
    let mut text = SCALE.to_string();
    text.extend((0..n).map(|i| format!("t{i} = (scale, {i});\ns{i} = t{i} == #b;\n")));
    text
}

/// `scale` at the bottom of `n` tuples written in one expression, compared with `==`.
pub(super) fn deep(n: usize) -> String {
    format!(
        "{SCALE}t = {}scale{};\nsame = t == #b;\n",
        "(".repeat(n),
        ", 1)".repeat(n)
    )
}

/// `scale` at the bottom of `n + 1` tuples made by `n + 1` bindings, compared with `==`.
pub(super) fn bound(n: usize) -> String {
    let mut text = format!("{SCALE}t0 = (scale, 0);\n");
    text.extend((1..=n).map(|i| format!("t{i} = (t{}, {i});\n", i - 1)));
    text.push_str(&format!("same = t{n} == #b;\n"));
    text
}

/// `scale` at the bottom of `n` atoms written in one expression, compared with `==`.
pub(super) fn atoms(n: usize) -> String {
    format!(
        "{SCALE}t = {}scale{};\nsame = t == #b;\n",
        "#a(".repeat(n),
        ")".repeat(n)
    )
}

/// `scale` at the bottom of `n` nested calls of a function that wraps its argument in a tuple.
pub(super) fn calls(n: usize) -> String {
    format!(
        "{SCALE}wrap(positional x) = (x, 1);\nt = {}scale{};\nsame = t == #b;\n",
        "wrap(".repeat(n),
        ")".repeat(n)
    )
}

/// A shape of program by its name.
pub(super) type Shape = (&'static str, fn(usize) -> String);

/// The five shapes, by name.
pub(super) const SHAPES: [Shape; 5] = [
    ("many", many),
    ("deep", deep),
    ("bound", bound),
    ("atoms", atoms),
    ("calls", calls),
];

/// The rejection of the program `src`, with as many errors as `errors`.
pub(super) fn rejected_with(src: &str, errors: usize) -> String {
    let out = rejected_with_main(src);
    let n = out
        .matches("Cannot compare a value that may hold a function")
        .count();
    assert_eq!(n, errors, "{out}");
    out
}

/// The text at 50 and 400 grows within 24 times, the row's limit; measured 2026-11-23: 8.3, 7.1,
/// 8.3, 7.3 and 5.7 times.
#[test]
fn the_text_of_a_function_held_n_deep_or_n_times_is_linear_in_n() {
    for (name, f) in SHAPES {
        let errors = |n| if name == "many" { n } else { 1 };
        let small = rejected_with(&f(50), errors(50)).len();
        let large = rejected_with(&f(400), errors(400)).len();
        assert!(
            large <= 24 * small,
            "{name}: {small} bytes at 50, {large} at 400"
        );
    }
}

/// The second of two errors that share the declaration of `scale` prints it once, and names the
/// error that printed it.
#[test]
fn a_shared_declared_step_is_printed_once() {
    let out = rejected_with(&many(2), 2);
    assert_eq!(out.matches("1 | scale(positional x)").count(), 1, "{out}");
    assert!(
        out.contains(
            "[6] 1:1 to 1:33: `scale` is declared here; the error above gives the type the \
             checker found for `scale`\n      line 1 is shown above"
        ),
        "{out}"
    );
}

/// Tuples written one inside another give one note, naming the position of the function by a
/// path, in place of a note a level; one tuple gives the note as before.
#[test]
fn nested_tuples_are_one_note_with_a_path() {
    let out = rejected_with(&deep(3), 1);
    assert!(
        out.contains("this tuple holds the function at `.0.0.0`"),
        "{out}"
    );
    assert_eq!(
        out.matches("this tuple holds the function").count(),
        1,
        "{out}"
    );
    let out = rejected_with(
        &format!("{SCALE}t = ((1, (scale, 2)), 3);\nsame = t == #b;\n"),
        1,
    );
    assert!(
        out.contains("this tuple holds the function at `.0.1.0`"),
        "{out}"
    );
    let out = rejected_with(&deep(1), 1);
    assert!(out.contains(": this tuple holds the function\n"), "{out}");
}

/// Two errors through one binding: the second gives the first of the steps it shares with the
/// first error, names that error, and leaves out the others; its own last step, the note on its
/// comparison, stays.
#[test]
fn a_later_error_names_the_earlier_one_from_the_shared_step() {
    let src = format!("{SCALE}t = (scale, 1);\ns0 = t == #b;\ns1 = t == #c;\n");
    let out = rejected_with(&src, 2);
    assert_eq!(out.matches("`t` is defined here").count(), 2, "{out}");
    assert_eq!(
        out.matches("this tuple holds the function").count(),
        1,
        "{out}"
    );
    assert!(
        out.contains("`t` is defined here; the next 3 steps are as in the error at 3:6 above"),
        "{out}"
    );
    assert_eq!(out.matches("`scale` is declared here").count(), 1, "{out}");
}

/// `n` errors, each comparing the last of a chain of `n` names bound one to the next: each
/// derivation goes through the whole chain, which the first error prints and each later one
/// names, so the text at 50 and 400 grows within 24 times (as n², 64 times, when each error
/// printed the chain). The value is one tuple, so the type each message prints is short.
#[test]
fn n_errors_through_one_chain_of_n_bindings_print_it_once() {
    let text = |n: usize| {
        let mut text = format!("{SCALE}t0 = (scale, 0);\n");
        text.extend((1..=n).map(|i| format!("t{i} = t{};\n", i - 1)));
        text.extend((0..n).map(|i| format!("c{i} = t{n} == #c;\n")));
        rejected_with(&text, n).len()
    };
    let (small, large) = (text(50), text(400));
    assert!(large <= 24 * small, "{small} bytes at 50, {large} at 400");
}

/// At n = 1 each shape prints one error with the declaration its derivation reaches in full:
/// `scale`'s, or for the calls `wrap`'s, which gives the call's type.
#[test]
fn one_level_prints_the_declaration_in_full() {
    for (name, f) in SHAPES {
        let out = rejected_with(&f(1), 1);
        let declared = match name {
            "calls" => "2 | wrap(positional x) = (x, 1);",
            _ => "1 | scale(positional x) = x * int(2);",
        };
        assert!(out.contains(declared), "{name}: {out}");
        assert!(
            out.contains("data is a value that holds no function at any depth"),
            "{name}: {out}"
        );
    }
}
