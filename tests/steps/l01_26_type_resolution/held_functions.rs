//! A function held in a tuple is reported once, at the tuple expression that holds it, with
//! its derivation: not again at each tuple, binding or call it then flows through, each of
//! which meets the same value, so that fixing the one error fixes them all (CHK-held-cascade).
//! A function at the bottom of `n` nested tuples gave `n` errors, each with a derivation
//! `O(n)` notes long, and the checker walked each binding's type again to solve and name its
//! variables: `O(n^2)` in all.

use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{Resolved, type_errors};

const SCALE: &str = "scale(positional x) = x * 2;\n";

/// The one error a tuple expression holding `scale` gives, at `at`.
fn holds_scale(at: &str) -> String {
    format!("a tuple takes data, and this value may hold a function, `(int) -> int` [{at}]")
}

#[test]
fn a_function_in_nested_tuples_is_one_error() {
    let text = format!("{SCALE}settings = ((scale, 1), 2);\n");
    assert_eq!(type_errors(&text), [holds_scale("scale")]);
}

#[test]
fn a_function_in_a_tuple_named_and_nested_again_is_one_error() {
    let text = format!("{SCALE}pair = (scale, 1);\ntriple = (pair, 2);\nfour = (triple, 3);\n");
    assert_eq!(type_errors(&text), [holds_scale("scale")]);
}

#[test]
fn a_function_wrapped_in_tuples_by_calls_is_one_error() {
    // The tuple is made in `wrap`, from a variable, so the error is at the call that binds the
    // variable to a function; the outer call meets the same function and says nothing more.
    let wrap = "wrap(positional x) = (x, 1);\n";
    let once = format!("{SCALE}{wrap}boxed = wrap(scale);\n");
    let twice = format!("{SCALE}{wrap}boxed = wrap(wrap(scale));\n");
    assert_eq!(type_errors(&once), [holds_scale("wrap(scale)")]);
    assert_eq!(type_errors(&twice), [holds_scale("wrap(scale)")]);
    let data = format!("{wrap}boxed = wrap(wrap(2));\n");
    assert_eq!(type_errors(&data), Vec::<String>::new());
}

#[test]
fn two_functions_in_tuples_are_two_errors() {
    // One error for each function, at the tuple that holds it; the tuple of both adds none.
    let text = format!(
        "{SCALE}shift(positional x) = x + 1;\na = (scale, 1);\nb = (shift, 1);\nc = (a, b);\n"
    );
    let shift = "a tuple takes data, and this value may hold a function, `(int) -> int` [shift]";
    assert_eq!(
        type_errors(&text),
        [holds_scale("scale"), shift.to_string()]
    );
}

/// `scale` at the bottom of `n` tuples written in one expression.
fn in_one_expression(n: usize) -> String {
    format!("{SCALE}t = {}scale{};\n", "(".repeat(n), ", 1)".repeat(n))
}

/// `scale` in a tuple, then `n - 1` bindings each putting the last in a tuple.
fn in_named_steps(n: usize) -> String {
    let mut text = format!("{SCALE}t0 = (scale, 1);\n");
    text.extend((1..n).map(|i| format!("t{i} = (t{}, 1);\n", i - 1)));
    text
}

/// `scale` wrapped in a tuple by `n` nested calls of `wrap`.
fn in_calls(n: usize) -> String {
    let wrap = "wrap(positional x) = (x, 1);\n";
    format!(
        "{SCALE}{wrap}t = {}scale{};\n",
        "wrap(".repeat(n),
        ")".repeat(n)
    )
}

#[test]
fn a_function_in_many_nested_tuples_is_one_error_in_linear_time() {
    for (what, text) in [
        (
            "a function n tuples deep in one expression",
            in_one_expression as fn(usize) -> String,
        ),
        ("a function put in a tuple by n bindings", in_named_steps),
        ("a function put in a tuple by n nested calls", in_calls),
    ] {
        let one = type_errors(&text(3));
        assert_eq!(one.len(), 1, "{what}: {one:?}");
        scaling::on_a_thread(1 << 29, || {
            let units: std::collections::BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
                .into_iter()
                .map(|n| (n, Resolved::new(&text(n))))
                .collect();
            scaling::check_order(what, 500, 1, |n| {
                let info = units[&n].check();
                // One error with its two notes, whatever the depth.
                assert_eq!(info.errors.len(), 1, "{what} at {n}");
                assert_eq!(info.errors[0].notes.len(), 2, "{what} at {n}");
            });
        });
    }
}

/// `((… (T, T) …, T), T)`, `n` tuples deep, printed `((… (_, _) …, _), _)` as `T` is named by
/// no function around.
fn nested(n: usize) -> Ty {
    let t = Ty::var("T".into());
    (0..n).fold(t.clone(), |inner, _| Ty::tuple(vec![inner, t.clone()]))
}

#[test]
fn a_type_8000_tuples_deep_prints_and_drops_on_a_2_mib_stack() {
    // `Ty::write` recursed once a level and overflowed a 2 MiB stack below 8,000 deep, as did
    // the drop glue of the rows.
    assert_eq!(nested(2).to_string(), "((_, _), _)");
    scaling::on_a_thread(2 << 20, || {
        let n = 8000;
        let text = nested(n).to_string();
        assert_eq!(text, format!("{}_{}", "(".repeat(n), ", _)".repeat(n)));
    });
}

#[test]
fn a_type_a_million_tuples_deep_prints_and_drops_on_an_8_mib_stack() {
    scaling::on_a_thread(8 << 20, || {
        let n = 1_000_000;
        let text = nested(n).to_string();
        assert!(text == format!("{}_{}", "(".repeat(n), ", _)".repeat(n)));
    });
}
