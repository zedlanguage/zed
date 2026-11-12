//! A message prints a literal as the program writes it, and a computed value in a form the
//! program could write (DESIGN.md sec:diagnostics: a message speaks in the program's words).
//! The printer looks the value up among the literals the checker read, so the spelling is a
//! span of the program's text and no literal is read again or copied before it is printed.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// Each program's one message holds the literal as written there.
#[test]
fn a_message_prints_a_literal_as_it_is_written() {
    let cases = [
        // A `rat` literal: once printed `5e-1r`, a form the program never held.
        ("f(x: int) = x * 0.5r;\n", "literal `0.5r`"),
        ("f(x: int) = x * 0.50r;\n", "literal `0.50r`"),
        ("f(x: int) = x * 2.5e-3r;\n", "literal `2.5e-3r`"),
        ("k(x: int) = x;\ny = k(x: 0.5r);\n", "(0.5r)"),
        // A value read through a name prints as the literal that wrote it.
        ("h = 0.5r;\ny = h + \"a\";\n", "0.5r"),
        ("y = (0.5r, 1) + \"a\";\n", "((0.5r, 1), \"a\")"),
        // Integers in another base and with separators.
        ("f(x: String) = x + 0xFF;\n", "0xFF"),
        ("f(x: String) = x + 1_000;\n", "1_000"),
        ("f(x: String) = x + -0xFF;\n", "-0xFF"),
        // Decimals with an exponent, and with a float suffix.
        ("f(x: String) = x + 1e3;\n", "1e3"),
        ("f(x: String) = x + -1e3;\n", "-1e3"),
        ("f(x: String) = x * 1e3f64;\n", "1e3f64"),
        // An `if` whose branches are literals.
        (
            "g(positional c: bool) = if c { 1 } else { 2.50 };\ny = g(true) + \"a\";\n",
            "1 | 2.50",
        ),
    ];
    for (src, part) in cases {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            errors[0].contains(part),
            "{src}: {:?} lacks {part:?}",
            errors[0]
        );
    }
}

/// Two literals of one value written two ways: each message prints the one it is about.
#[test]
fn each_message_prints_its_own_spelling_of_a_value() {
    let errors = type_errors("f(x: int) = x * 2.5e-3r;\ng(x: int) = x * 0.0025r;\n");
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(errors[0].contains("literal `2.5e-3r`"), "{errors:?}");
    assert!(errors[1].contains("literal `0.0025r`"), "{errors:?}");
}

/// A computed value the program writes no literal for prints as its type, which the program
/// can write; the canonical form `meKr` is never printed for a value read from a literal.
#[test]
fn a_computed_value_prints_as_the_program_could_write_it() {
    let errors = type_errors("q = 1r / 3r;\nf(x: int) = x * q;\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("(int, rat)"), "{errors:?}");
    for src in ["f(x: int) = x * 0.5r;\n", "f(x: int) = x * 2.5e-3r;\n"] {
        let errors = type_errors(src);
        assert!(
            !errors[0].contains("e-1r") && !errors[0].contains("e-4r"),
            "{errors:?}"
        );
    }
}

/// `n` functions that each misuse a `rat` literal, of `n / 2` values each written two ways:
/// each message finds its own spelling among the `n` literals.
fn misuses(n: usize) -> String {
    (0..n)
        .map(|i| {
            let zeros = ["", "0"][i % 2];
            format!("misuse{i}(x: String) = x + {}.5{zeros}r;\n", i / 2)
        })
        .collect()
}

#[test]
fn printing_the_spellings_of_many_literals_scales() {
    let errors = type_errors(&misuses(4));
    for (e, part) in errors
        .iter()
        .zip(["(String, 0.5r)", "0.50r", "1.5r", "1.50r"])
    {
        assert!(e.contains(part), "{errors:?}");
    }
    let n = 200;
    let texts = scaling::inputs(n, misuses);
    scaling::check("checking n misused literals and printing each", n, |m| {
        assert_eq!(type_errors(&texts[&m]).len(), m);
    });
}

/// One misuse of a tuple of `n` `rat` literals of `n` values: its one message prints each.
fn tuple(n: usize) -> String {
    let items: Vec<String> = (0..n).map(|i| format!("{i}.50r")).collect();
    format!("f(x: String) = x + ({});\n", items.join(", "))
}

#[test]
fn printing_a_tuple_of_many_literals_scales() {
    assert!(type_errors(&tuple(2))[0].contains("(String, (0.50r, 1.50r))"));
    let n = 400;
    let texts = scaling::inputs(n, tuple);
    scaling::check("checking a tuple of n literals and printing it", n, |m| {
        let errors = type_errors(&texts[&m]);
        assert!(
            errors[0].contains(&format!("{}.50r))", m - 1)),
            "{errors:?}"
        );
    });
}
