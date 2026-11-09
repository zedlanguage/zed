//! A variable inside an atom's payload, inside a tuple, is held by the tuple: the tuple's row
//! keeps that it holds a variable, at any depth, in payloads too, so that a need on the
//! tuple (here the data `==` needs) reaches the parameter the variable stands for
//! (ATOM-payload-open). Before, a row read only its components' own variables and rows, so a
//! function passed to a generic function that put its parameter in a payload and compared
//! the result with `==` was accepted.

use zed_tests::scaling;

use super::{Resolved, type_errors};

const SCALE: &str = "scale(positional x) = x * 2;\n";

/// A generic function `g` that returns its parameter `n` atoms deep, in a row with `1`, and a
/// generic function `h` that compares what `g` returns with itself; `h` called with `arg`.
/// A tuple expression would check its components as data itself; a returned row does not, so
/// the need `==` puts on it must reach `h`'s parameter through the row.
fn in_atoms_in_a_tuple(n: usize, arg: &str) -> String {
    let mut text = format!("{SCALE}g(positional x) {{\n  t0 = #a(x);\n");
    text.extend((1..n).map(|i| format!("  t{i} = #a(t{});\n", i - 1)));
    text.push_str(&format!(
        "  return t{}, 1;\n}}\nh(positional x) {{ p = g(x); return p == p; }}\nsame = h({arg});\n",
        n - 1
    ));
    text
}

/// [`in_atoms_in_a_tuple`] with each atom holding the one below twice, so the payloads are
/// shared and their tree has `2^n` leaves.
fn in_atoms_twice_in_a_tuple(n: usize, arg: &str) -> String {
    let mut text = format!("{SCALE}g(positional x) {{\n  t0 = #a(x, x);\n");
    text.extend((1..n).map(|i| format!("  t{i} = #a(t{0}, t{0});\n", i - 1)));
    text.push_str(&format!(
        "  return t{}, 1;\n}}\nh(positional x) {{ p = g(x); return p == p; }}\nsame = h({arg});\n",
        n - 1
    ));
    text
}

/// The refusal of `same = h(scale)`, at the argument.
const REFUSED: &str = "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [h(scale)]";

#[test]
fn a_function_deep_in_a_payload_in_a_tuple_is_refused_by_equality() {
    type Family = fn(usize, &str) -> String;
    for text in [in_atoms_in_a_tuple as Family, in_atoms_twice_in_a_tuple] {
        assert_eq!(type_errors(&text(3, "scale")), [REFUSED]);
        assert_eq!(type_errors(&text(3, "2")), Vec::<String>::new());
    }
}

#[test]
fn a_variable_deep_in_a_payload_in_a_tuple_is_checked_in_linear_time() {
    // Each row and payload shape keeps whether it holds a variable at any depth, so the need
    // `==` puts on the tuple, the replacement of the parameter's variable at the call, and the
    // settling of the signature each enter a shared row or shape once: `O(n)` for `n` atoms,
    // and for the payload held twice too, whose tree has `2^n` leaves.
    type Family = fn(usize, &str) -> String;
    for (what, text, arg, errors) in [
        (
            "a function n atoms deep in a tuple",
            in_atoms_in_a_tuple as Family,
            "scale",
            1,
        ),
        (
            "an integer n atoms deep in a tuple",
            in_atoms_in_a_tuple,
            "2",
            0,
        ),
        (
            "a function put twice in an atom by n bindings, in a tuple",
            in_atoms_twice_in_a_tuple,
            "scale",
            1,
        ),
        (
            "an integer put twice in an atom by n bindings, in a tuple",
            in_atoms_twice_in_a_tuple,
            "2",
            0,
        ),
    ] {
        let units = scaling::inputs(500, |n| Resolved::new(&text(n, arg)));
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors, "{what} at {n}");
        });
    }
}
