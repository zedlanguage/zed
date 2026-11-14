//! A function held in a tuple is reported once, at the tuple expression that holds it, with
//! its derivation: not again at each tuple, binding or call it then flows through, each of
//! which meets the same value, so that fixing the one error fixes them all (CHK-held-cascade).
//! A function at the bottom of `n` nested tuples gave `n` errors, each with a derivation
//! `O(n)` notes long, and the checker walked each binding's type again to solve and name its
//! variables: `O(n^2)` in all.

use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{info, type_errors};

/// `int(2)`, not `2`: a bare `2` takes the carrier of `x` (steps L1.26a, L1.26b), so `scale`
/// would be generic, and a generic function held by `n` bindings checks in time quadratic in
/// `n`, on main too (follow-up GENERIC-nested-quadratic).
const SCALE: &str = "scale(positional x) = x * int(2);\n";

/// The one error a tuple expression holding `scale` gives, at `at`.
fn holds_scale(at: &str) -> String {
    format!(
        "a tuple takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth. [{at}]"
    )
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
    // One error for each function, at the tuple that holds it; the tuple of both adds none. A
    // bare `1` takes the carrier of `x`, so `shift` is generic.
    let text = format!(
        "{SCALE}shift(positional x) = x + 1;\na = (scale, 1);\nb = (shift, 1);\nc = (a, b);\n"
    );
    let shift = "a tuple takes data, and this value may hold a function, `(T) -> T for T in int | f32 | f64 | rat`: data is a value that holds no function at any depth. [shift]";
    assert_eq!(
        type_errors(&text),
        [holds_scale("scale"), shift.to_string()]
    );
}

/// `scale` at the bottom of `n` tuples written in one expression.
pub(super) fn in_one_expression(n: usize) -> String {
    format!("{SCALE}t = {}scale{};\n", "(".repeat(n), ", 1)".repeat(n))
}

/// `scale` in a tuple, then `n - 1` bindings each putting the last in a tuple.
pub(super) fn in_named_steps(n: usize) -> String {
    let mut text = format!("{SCALE}t0 = (scale, 1);\n");
    text.extend((1..n).map(|i| format!("t{i} = (t{}, 1);\n", i - 1)));
    text
}

/// `scale` wrapped in a tuple by `n` nested calls of `wrap`.
pub(super) fn in_calls(n: usize) -> String {
    let wrap = "wrap(positional x) = (x, 1);\n";
    format!(
        "{SCALE}{wrap}t = {}scale{};\n",
        "wrap(".repeat(n),
        ")".repeat(n)
    )
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
fn a_type_31250_tuples_deep_prints_and_drops_on_a_256_kib_stack() {
    // It ran a million tuples deep on an 8 MiB stack, about 8 bytes a level; this is the same
    // stack a level at a thirty-second of the depth.
    scaling::on_a_thread((8 << 20) / 32, || {
        let n = 1_000_000 / 32;
        let text = nested(n).to_string();
        assert!(text == format!("{}_{}", "(".repeat(n), ", _)".repeat(n)));
    });
}

/// `leaf` in an atom at the bottom of `n` levels of an atom around a tuple, compared with `==`.
pub(super) fn in_atoms_and_tuples(n: usize, leaf: &str) -> String {
    format!(
        "{SCALE}t = {}#a({leaf}){};\nsame = t == #b;\n",
        "#a((".repeat(n),
        ", 1))".repeat(n)
    )
}

/// `leaf` after `n` integers in the payload of one atom, compared with `==`.
pub(super) fn in_a_wide_payload(n: usize, leaf: &str) -> String {
    let items: String = (0..n).map(|i| format!("{i}, ")).collect();
    format!("{SCALE}t = #a({items}{leaf});\nsame = t == #b;\n")
}

#[test]
fn a_function_in_an_atom_s_payload_is_one_error() {
    // A payload may hold a function (DESIGN.md, `#atom(t)`), and `==` compares payloads: the
    // function is reported once, at the tuple that holds the atom, or else at the `==`.
    let at_tuple = "a tuple takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth. [#a(scale)]";
    let at_eq = "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth. [t == #b]";
    assert_eq!(type_errors(&in_atoms_and_tuples(3, "scale")), [at_tuple]);
    assert_eq!(type_errors(&in_a_wide_payload(3, "scale")), [at_eq]);
    assert_eq!(
        type_errors(&in_atoms_and_tuples(3, "1")),
        Vec::<String>::new()
    );
    assert_eq!(
        type_errors(&in_a_wide_payload(3, "1")),
        Vec::<String>::new()
    );
}

/// `leaf` at the bottom of `n` atoms nested directly in atoms in one expression, compared
/// with `==`.
pub(super) fn in_atoms(n: usize, leaf: &str) -> String {
    format!(
        "{SCALE}t = {}{leaf}{};\nsame = t == #b;\n",
        "#a(".repeat(n),
        ")".repeat(n)
    )
}

/// `leaf` in an atom, then `n - 1` bindings each putting the last in an atom, compared with
/// `==`.
pub(super) fn in_atoms_by_bindings(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}t0 = #a({leaf});\n");
    text.extend((1..n).map(|i| format!("t{i} = #a(t{});\n", i - 1)));
    text.push_str(&format!("same = t{} == #b;\n", n - 1));
    text
}

/// `leaf` put in an atom by `n` nested calls of `wrap`, compared with `==`.
pub(super) fn in_atoms_by_calls(n: usize, leaf: &str) -> String {
    format!(
        "{SCALE}wrap(positional x) = #a(x);\nt = {}{leaf}{};\nsame = t == #b;\n",
        "wrap(".repeat(n),
        ")".repeat(n)
    )
}

#[test]
fn a_function_in_atoms_nested_in_atoms_is_refused_by_equality() {
    // A payload may hold a function (DESIGN.md, `#atom(t)`), and `==` compares payloads.
    let at_eq = |at: &str| {
        format!(
            "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth. [{at}]"
        )
    };
    type Family = fn(usize, &str) -> String;
    for (text, at) in [
        (in_atoms as Family, "t == #b"),
        (in_atoms_by_bindings, "t2 == #b"),
        (in_atoms_by_calls, "t == #b"),
    ] {
        assert_eq!(type_errors(&text(3, "scale")), [at_eq(at)]);
        assert_eq!(type_errors(&text(3, "1")), Vec::<String>::new());
    }
}

/// `leaf` in an atom, then `n - 1` bindings each putting the last twice in an atom, so the
/// payloads are shared and their tree has `2^n` leaves, compared with `==`.
pub(super) fn in_atoms_twice(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}t0 = #a({leaf}, 1);\n");
    text.extend((1..n).map(|i| format!("t{i} = #a(t{0}, t{0});\n", i - 1)));
    text.push_str(&format!("same = t{} == #b;\n", n - 1));
    text
}

/// [`in_atoms_twice`] inside a generic function, on its parameter, then called with `leaf`:
/// the call replaces the parameter's variable in a type of `n` shapes with `2^n` paths
/// through them.
pub(super) fn in_atoms_twice_in_a_function(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}g(positional x) {{\n  t0 = #a(x, x);\n");
    text.extend((1..n).map(|i| format!("  t{i} = #a(t{0}, t{0});\n", i - 1)));
    text.push_str(&format!(
        "  return t{};\n}}\nt = g({leaf});\nsame = t == #b;\n",
        n - 1
    ));
    text
}

#[test]
fn a_function_in_nested_tuples_is_one_error_with_its_notes_and_repairs() {
    // A small instance of the benchmark
    // `bench::held_functions::a_function_in_many_nested_tuples_is_one_error_in_linear_time`.
    for text in [in_one_expression(3), in_named_steps(3), in_calls(3)] {
        let (i, _) = info(&text);
        // One error with its two notes and its two repairs.
        assert_eq!(i.errors.len(), 1, "{text}: {:?}", i.errors);
        assert_eq!(i.errors[0].notes.len(), 4, "{text}: {:?}", i.errors[0].notes);
    }
}

#[test]
fn an_integer_put_twice_in_atoms_is_data() {
    // A small instance of the benchmark
    // `bench::held_functions::atoms_nested_in_atoms_are_checked_in_linear_time`, whose other
    // programs `a_function_in_atoms_nested_in_atoms_is_refused_by_equality` checks.
    for text in [in_atoms_twice(3, "1"), in_atoms_twice_in_a_function(3, "1")] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
}
