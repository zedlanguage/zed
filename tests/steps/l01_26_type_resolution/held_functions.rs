//! A tuple may hold a function at any depth, and building one is no error (DESIGN.md step
//! L1.17, QUESTIONS A43). A use that needs data, `==` here, is reported once, at that use, with
//! its derivation: not again at each tuple, binding or call the function flows through, each
//! of which meets the same value, so that fixing the one error fixes them all
//! (CHK-held-cascade). A function at the bottom of `n` nested tuples once gave `n` errors, each
//! with a derivation `O(n)` notes long, and the checker walked each binding's type again to
//! solve and name its variables: `O(n^2)` in all.

use zedc::check::ty::Ty;

use super::{info, type_errors};

/// `int(2)`, not `2`: a bare `2` takes the carrier of `x` (steps L1.26a, L1.26b), so `scale`
/// would be generic, and a generic function held by `n` bindings checks in time quadratic in
/// `n`, on main too (follow-up GENERIC-nested-quadratic).
const SCALE: &str = "scale(positional x) = x * int(2);\n";

/// The one error `==` on a value that holds `scale` gives, at `at`.
fn compares_scale(at: &str) -> String {
    format!(
        "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth. [{at}]"
    )
}

/// `text` with `same = t == #b;` added: an operand that is data, so the one error is the
/// other operand's.
fn compared(text: &str, t: &str) -> String {
    format!("{text}same = {t} == #b;\n")
}

#[test]
fn a_function_in_nested_tuples_is_one_error_where_it_is_compared() {
    let text = format!("{SCALE}settings = ((scale, 1), 2);\n");
    assert_eq!(type_errors(&text), Vec::<String>::new());
    assert_eq!(
        type_errors(&compared(&text, "settings")),
        [compares_scale("settings == #b")]
    );
}

#[test]
fn a_function_in_a_tuple_named_and_nested_again_is_one_error_where_it_is_compared() {
    let text = format!("{SCALE}pair = (scale, 1);\ntriple = (pair, 2);\nfour = (triple, 3);\n");
    assert_eq!(type_errors(&text), Vec::<String>::new());
    assert_eq!(
        type_errors(&compared(&text, "four")),
        [compares_scale("four == #b")]
    );
}

#[test]
fn a_function_wrapped_in_tuples_by_calls_is_one_error_where_it_is_compared() {
    // The tuple is made in `wrap`, from a variable, and the calls put the function in it; only
    // the `==` on the result needs data.
    let wrap = "wrap(positional x) = (x, 1);\n";
    let once = format!("{SCALE}{wrap}boxed = wrap(scale);\n");
    let twice = format!("{SCALE}{wrap}boxed = wrap(wrap(scale));\n");
    for text in [&once, &twice] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(
            type_errors(&compared(text, "boxed")),
            [compares_scale("boxed == #b")],
            "{text}"
        );
    }
    let data = format!("{wrap}boxed = wrap(wrap(2));\nsame = boxed == boxed;\n");
    assert_eq!(type_errors(&data), Vec::<String>::new());
}

#[test]
fn two_functions_in_tuples_are_one_error_where_they_are_compared() {
    // The tuples are no error; the `==` on the tuple of both is one. A bare `1` takes the
    // carrier of `x`, so `shift` is generic.
    let text = format!(
        "{SCALE}shift(positional x) = x + 1;\na = (scale, 1);\nb = (shift, 1);\nc = (a, b);\n"
    );
    assert_eq!(type_errors(&text), Vec::<String>::new());
    assert_eq!(type_errors(&compared(&text, "c")).len(), 1);
}

/// `scale` at the bottom of `n` tuples written in one expression, compared with `==`.
pub(super) fn in_one_expression(n: usize) -> String {
    let text = format!("{SCALE}t = {}scale{};\n", "(".repeat(n), ", 1)".repeat(n));
    compared(&text, "t")
}

/// `scale` in a tuple, then `n - 1` bindings each putting the last in a tuple, compared with
/// `==`.
pub(super) fn in_named_steps(n: usize) -> String {
    let mut text = format!("{SCALE}t0 = (scale, 1);\n");
    text.extend((1..n).map(|i| format!("t{i} = (t{}, 1);\n", i - 1)));
    compared(&text, &format!("t{}", n - 1))
}

/// `scale` wrapped in a tuple by `n` nested calls of `wrap`, compared with `==`.
pub(super) fn in_calls(n: usize) -> String {
    let wrap = "wrap(positional x) = (x, 1);\n";
    let text = format!(
        "{SCALE}{wrap}t = {}scale{};\n",
        "wrap(".repeat(n),
        ")".repeat(n)
    );
    compared(&text, "t")
}

/// `((… (T, T) …, T), T)`, `n` tuples deep, printed `((… (_, _) …, _), _)` as `T` is named by
/// no function around.
pub(super) fn nested(n: usize) -> Ty {
    let t = Ty::var("T".into());
    (0..n).fold(t.clone(), |inner, _| Ty::tuple(vec![inner, t.clone()]))
}

#[test]
fn a_type_a_few_tuples_deep_prints_its_variables_as_underscores() {
    // A small instance of the benchmarks
    // `bench::held_functions::a_type_8000_tuples_deep_prints_and_drops_on_a_2_mib_stack` and
    // `bench::held_functions::a_type_31250_tuples_deep_prints_and_drops_on_a_256_kib_stack`.
    assert_eq!(nested(0).to_string(), "_");
    assert_eq!(nested(2).to_string(), "((_, _), _)");
    let n = 5;
    assert_eq!(
        nested(n).to_string(),
        format!("{}_{}", "(".repeat(n), ", _)".repeat(n))
    );
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
    // A payload and a tuple may hold a function (DESIGN.md, `#atom(t)`, step L1.17), and `==`
    // compares payloads: the function is reported once, at the `==`.
    let at_eq = compares_scale("t == #b");
    assert_eq!(
        type_errors(&in_atoms_and_tuples(3, "scale")),
        std::slice::from_ref(&at_eq)
    );
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

/// The notes of the one error of `text`, each as the text it is at, then the note.
fn notes_of(text: &str) -> Vec<String> {
    let (i, _) = info(text);
    assert_eq!(i.errors.len(), 1, "{text}: {:?}", i.errors);
    i.errors[0]
        .notes
        .iter()
        .map(|n| format!("[{}] {}", &text[n.span.start..n.span.end], n.text))
        .collect()
}

/// The notes on `scale` and the two repairs at `at`, which end each derivation below.
fn scale_and_repairs(at: &str) -> [String; 4] {
    [
        "[scale] `scale` is (int) -> int here".into(),
        "[scale(positional x) = x * int(2);] `scale` is declared here with no type written for `x` or its result; the type the checker found for `scale` is `(int) -> int`".into(),
        format!("[{at}] repair: call the function before the value gets here, so that the value holds its result and not the function"),
        format!("[{at}] repair: keep the function under its own name, out of the value"),
    ]
}

/// The number of notes the one error of [`in_one_expression`] has: one for the name, one for
/// its definition, one for each tuple, and [`scale_and_repairs`].
pub(super) fn notes_in_one_expression(n: usize) -> usize {
    n + 6
}

/// The number of notes the one error of [`in_named_steps`] has: three for each binding, the
/// name, its definition and its tuple, and [`scale_and_repairs`].
pub(super) fn notes_in_named_steps(n: usize) -> usize {
    3 * n + 4
}

/// The number of notes the one error of [`in_calls`] has: the name, its definition, the
/// outer call with its type and the declaration of `wrap`, and the two repairs.
pub(super) fn notes_in_calls(_: usize) -> usize {
    6
}

#[test]
fn a_function_in_nested_tuples_is_one_error_with_the_path_to_it() {
    // A small instance of the benchmark
    // `bench::held_functions::a_function_in_many_nested_tuples_is_one_error_in_linear_time`.
    // Each tuple and name the function passes through to the `==` is a step with no type
    // printed, so the notes grow with the program and not with the types of its steps.
    let mut expected: Vec<String> = [
        "[t] `t` holds the function here",
        "[(((scale, 1), 1), 1)] `t` is defined here",
        "[(((scale, 1), 1), 1)] this tuple holds the function",
        "[((scale, 1), 1)] this tuple holds the function",
        "[(scale, 1)] this tuple holds the function",
    ]
    .map(String::from)
    .into();
    expected.extend(scale_and_repairs("t == #b"));
    assert_eq!(notes_of(&in_one_expression(3)), expected);
    let mut expected: Vec<String> = [
        "[t2] `t2` holds the function here",
        "[(t1, 1)] `t2` is defined here",
        "[(t1, 1)] this tuple holds the function",
        "[t1] `t1` holds the function here",
        "[(t0, 1)] `t1` is defined here",
        "[(t0, 1)] this tuple holds the function",
        "[t0] `t0` holds the function here",
        "[(scale, 1)] `t0` is defined here",
        "[(scale, 1)] this tuple holds the function",
    ]
    .map(String::from)
    .into();
    expected.extend(scale_and_repairs("t2 == #b"));
    assert_eq!(notes_of(&in_named_steps(3)), expected);
    for (text, count) in [
        (in_one_expression(3), notes_in_one_expression(3)),
        (in_named_steps(3), notes_in_named_steps(3)),
        (in_calls(3), notes_in_calls(3)),
    ] {
        assert_eq!(notes_of(&text).len(), count, "{text}");
    }
}

#[test]
fn a_function_in_an_atom_s_payload_is_shown_through_each_atom() {
    let mut expected: Vec<String> = [
        "[t1] `t1` holds the function here",
        "[#a(t0)] `t1` is defined here",
        "[#a(t0)] this atom `#a` holds the function in its payload",
        "[t0] `t0` holds the function here",
        "[#a(scale)] `t0` is defined here",
        "[#a(scale)] this atom `#a` holds the function in its payload",
    ]
    .map(String::from)
    .into();
    expected.extend(scale_and_repairs("t1 == #b"));
    assert_eq!(notes_of(&in_atoms_by_bindings(2, "scale")), expected);
}

#[test]
fn a_part_with_no_function_is_left_out_of_the_path() {
    // `(1, 2)` holds no function, so no step shows it; its literals get no note either.
    let text = format!("{SCALE}t = ((1, 2), (scale, 3));\nsame = t == #b;\n");
    let mut expected: Vec<String> = [
        "[t] `t` holds the function here",
        "[((1, 2), (scale, 3))] `t` is defined here",
        "[((1, 2), (scale, 3))] this tuple holds the function",
        "[(scale, 3)] this tuple holds the function",
    ]
    .map(String::from)
    .into();
    expected.extend(scale_and_repairs("t == #b"));
    assert_eq!(notes_of(&text), expected);
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

/// A choice between two generic functions hashes each one's signature with its needs
/// (`Sig::digest`, which reads every type of a need): an `Index` need (`d[k]`), an `Order`
/// need (`min` with a tuple), an `Into` need (an argument at a tuple parameter) and the
/// chain of calls of an `InDomain` need passed on by a wrapper (`2 ^ k`). Each program is
/// accepted (item TEST-types-unreached-paths).
#[test]
fn a_choice_between_generic_functions_with_needs_is_accepted() {
    for src in [
        "get(positional d, positional k) = d[k];\npick(positional b: bool) = if b { get } else { get };\n",
        "m(positional a) = min(a, (1, 2));\npick(positional b: bool) = if b { m } else { m };\n",
        "g(positional x: (int, int)) = x;\nf(positional y) = g(y);\npick(positional b: bool) = if b { f } else { f };\n",
        "w(positional k) = 2 ^ k;\nv(positional k) = w(k);\nu(positional k) = w(k);\npick(positional b: bool) = if b { v } else { u };\nx = pick(true)(3);\n",
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    }
}

/// A function that returns a generic function, passed where a function with a function result
/// is expected. With no need on the returned function, its signature fits as written. With a
/// need, the signatures are compared with each solved variable read as its type (`fits_in`
/// under `fits_sig_with`): `2 ^ k` needs `k` in `int[0..]` (an integer power by a negative
/// integer is refused), so it does not fit a result `(k: int) -> int` (item
/// TEST-types-unreached-paths).
#[test]
fn a_returned_generic_function_fits_a_function_result_by_its_needs() {
    for src in [
        "add(positional a, positional b) = a + b;\nf(x: int) = add;\nh(g: (x: int) -> ((positional a: int, positional b: int) -> int)) = 1;\ny = h(g: f);\n",
        "m(positional a, positional b) = min(a, b);\nf(x: int) = m;\nh(g: (x: int) -> ((positional a: int, positional b: int) -> int)) = 1;\ny = h(g: f);\n",
        "w(positional k) = k * k;\nf(x: int) = w;\nh(g: (x: int) -> ((positional k: f64) -> f64)) = 1;\ny = h(g: f);\n",
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    }
    assert_eq!(
        type_errors(
            "w(positional k) = 2 ^ k;\nf(x: int) = w;\nh(g: (x: int) -> ((k: int) -> int)) = 1;\ny = h(g: f);\n"
        ),
        [
            "`f` is `(x: int) -> ((T) -> T for T in int | f32 | f64)`, not `(x: int) -> (k: int) -> int`: it is passed where a function of that type is expected, and its own type does not fit that one. [f]"
        ]
    );
}
