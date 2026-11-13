//! A function held in a tuple is reported once, at the tuple expression that holds it, with
//! its derivation: not again at each tuple, binding or call it then flows through, each of
//! which meets the same value, so that fixing the one error fixes them all (CHK-held-cascade).
//! A function at the bottom of `n` nested tuples gave `n` errors, each with a derivation
//! `O(n)` notes long, and the checker walked each binding's type again to solve and name its
//! variables: `O(n^2)` in all.

use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{Resolved, type_errors};

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
        let units: std::collections::BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            // One error with its two notes and its two repairs, whatever the depth.
            assert_eq!(info.errors.len(), 1, "{what} at {n}");
            assert_eq!(info.errors[0].notes.len(), 4, "{what} at {n}");
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

/// `leaf` in an atom at the bottom of `n` levels of an atom around a tuple, compared with `==`.
fn in_atoms_and_tuples(n: usize, leaf: &str) -> String {
    format!(
        "{SCALE}t = {}#a({leaf}){};\nsame = t == #b;\n",
        "#a((".repeat(n),
        ", 1))".repeat(n)
    )
}

/// `leaf` after `n` integers in the payload of one atom, compared with `==`.
fn in_a_wide_payload(n: usize, leaf: &str) -> String {
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

#[test]
fn a_function_in_payloads_is_found_in_linear_time() {
    // Each level makes a row, which reads the payload below it once; the payload walk reads
    // a row and does not enter it. Atoms nested directly in atoms are tested by
    // `atoms_nested_in_atoms_are_checked_in_linear_time` (COMPLEXITY.md, ATOM-nested-sq).
    type Family = fn(usize, &str) -> String;
    for (what, text, leaf, errors) in [
        (
            "a function n atoms and tuples deep",
            in_atoms_and_tuples as Family,
            "scale",
            1,
        ),
        (
            "an integer n atoms and tuples deep",
            in_atoms_and_tuples,
            "1",
            0,
        ),
        (
            "a function after n integers in a payload",
            in_a_wide_payload,
            "scale",
            1,
        ),
        (
            "an integer after n integers in a payload",
            in_a_wide_payload,
            "1",
            0,
        ),
    ] {
        let units: std::collections::BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, leaf))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors, "{what} at {n}");
        });
    }
}

/// `leaf` at the bottom of `n` atoms nested directly in atoms in one expression, compared
/// with `==`.
fn in_atoms(n: usize, leaf: &str) -> String {
    format!(
        "{SCALE}t = {}{leaf}{};\nsame = t == #b;\n",
        "#a(".repeat(n),
        ")".repeat(n)
    )
}

/// `leaf` in an atom, then `n - 1` bindings each putting the last in an atom, compared with
/// `==`.
fn in_atoms_by_bindings(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}t0 = #a({leaf});\n");
    text.extend((1..n).map(|i| format!("t{i} = #a(t{});\n", i - 1)));
    text.push_str(&format!("same = t{} == #b;\n", n - 1));
    text
}

/// `leaf` put in an atom by `n` nested calls of `wrap`, compared with `==`.
fn in_atoms_by_calls(n: usize, leaf: &str) -> String {
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

#[test]
fn atoms_nested_in_atoms_are_checked_in_linear_time() {
    // The checker keeps the type of every expression it meets, and the type of the atom at
    // each level holds the level below as its payload: copying that payload at each level was
    // `O(n^2)`, and so were the walks that entered every payload at each level to find its
    // variables, replace them or find a function (ATOM-nested-sq). A payload is a shared
    // node now, copied in constant time, which keeps what it holds at any depth, so a walk
    // reads it and does not enter it; a payload holding the level below twice is a shared
    // node met twice, entered at most once, and made at most once where a call replaces the
    // variables it holds. The leaf is an integer: with a function there, the refusal of `==`
    // shows a note for each level with that level's type, `O(n^2)` characters of text, and
    // `2^n` for the payload held twice (COMPLEXITY.md, ATOM-nested-sq).
    type Family = fn(usize, &str) -> String;
    for (what, text) in [
        (
            "an integer n atoms deep in one expression",
            in_atoms as Family,
        ),
        (
            "an integer put in an atom by n bindings",
            in_atoms_by_bindings,
        ),
        (
            "an integer put in an atom by n nested calls",
            in_atoms_by_calls,
        ),
        (
            "an integer put twice in an atom by n bindings",
            in_atoms_twice,
        ),
        (
            "an integer put twice in an atom by n bindings in a generic function",
            in_atoms_twice_in_a_function,
        ),
    ] {
        let units: std::collections::BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, "1"))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{what} at {n}");
        });
    }
}

/// `leaf` in an atom, then `n - 1` bindings each putting the last twice in an atom, so the
/// payloads are shared and their tree has `2^n` leaves, compared with `==`.
fn in_atoms_twice(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}t0 = #a({leaf}, 1);\n");
    text.extend((1..n).map(|i| format!("t{i} = #a(t{0}, t{0});\n", i - 1)));
    text.push_str(&format!("same = t{} == #b;\n", n - 1));
    text
}

/// [`in_atoms_twice`] inside a generic function, on its parameter, then called with `leaf`:
/// the call replaces the parameter's variable in a type of `n` shapes with `2^n` paths
/// through them.
fn in_atoms_twice_in_a_function(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}g(positional x) {{\n  t0 = #a(x, x);\n");
    text.extend((1..n).map(|i| format!("  t{i} = #a(t{0}, t{0});\n", i - 1)));
    text.push_str(&format!(
        "  return t{};\n}}\nt = g({leaf});\nsame = t == #b;\n",
        n - 1
    ));
    text
}
