//! The language's `==`: IEEE 754 at floats, at any depth, and structural elsewhere; and on
//! functions, an error until types give the domain to compare them on.

use zed_kernel::term::build::{lam, prim, var};
use zed_kernel::{Evaluator, F64, Prim, Value, World};

use zed_tests::step_helpers::l01_16_elaboration::{errors, value};

#[test]
fn float_equality_and_comparison_follow_ieee() {
    let src = "nan = 0.0 / 0.0;\na = nan == nan;\nb = nan != nan;\nc = 0.0 == -0.0;\n\
               d = nan < 1.0;\ne = nan >= 1.0;\nf = -0.0 < 0.0;\ng = 1.0 <= 1.0;\n";
    assert_eq!(value(src, "a"), "false");
    assert_eq!(value(src, "b"), "true");
    assert_eq!(value(src, "c"), "true");
    assert_eq!(value(src, "d"), "false");
    assert_eq!(value(src, "e"), "false");
    assert_eq!(value(src, "f"), "false");
    assert_eq!(value(src, "g"), "true");
}

#[test]
fn ieee_equality_reaches_inside_tuples_and_atoms() {
    let src = "nan = 0.0 / 0.0;\na = (1, nan) == (1, nan);\nb = (0.0, \"x\") == (-0.0, \"x\");\n\
               c = #at(-0.0) == #at(0.0);\nd = #at(x: nan) == #at(x: nan);\n";
    assert_eq!(value(src, "a"), "false");
    assert_eq!(value(src, "b"), "true");
    assert_eq!(value(src, "c"), "true");
    assert_eq!(value(src, "d"), "false");
}

#[test]
fn keys_still_tell_signed_zeros_apart_and_read_one_nan() {
    // The identity keys and the law catalog read is bitwise (sec:type_resolution), whatever `==` says.
    assert_ne!(Value::float(0.0), Value::float(-0.0));
    assert_eq!(Value::float(f64::NAN), Value::float(-f64::NAN));
    assert!(!Value::float(0.0).surface_eq(&Value::float(f64::NAN)));
    assert_eq!(F64::new(-f64::NAN).get().to_bits(), f64::NAN.to_bits());
}

#[test]
fn functions_compare_only_over_an_enumerable_domain() {
    // Until types give the domain to compare on, the checker rejects `==` on a value that may
    // hold a function, and the kernel stops on one.
    let src = "inc = x -> x + 1;\nalso = x -> 1 + x;\nsame = inc == also;\n";
    assert_eq!(
        errors(src),
        [
            "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [inc == also]"
        ]
    );
    let id = || lam(&["x"], var("x"));
    let got = Evaluator::new(World::new())
        .run(&prim(Prim::Eq, vec![id(), id()]))
        .expect_err("`==` on functions")
        .to_string();
    assert!(
        got.contains("`==` on functions compares them at every point of an enumerable domain"),
        "{got}"
    );
}

#[test]
fn a_function_deep_in_a_tuple_is_reported_once_where_it_is_written() {
    // Each tuple checks its own components, so a function two tuples deep gets one error, at
    // the inner tuple, and not one more at each tuple around it.
    let src = "inc = x -> x + 1;\npair = ((inc, 1), 2);\n";
    assert_eq!(
        errors(src),
        [
            "a tuple takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [inc]"
        ]
    );
}

#[test]
fn a_function_in_an_atom_s_payload_is_refused_by_equality() {
    // A payload may hold a function (DESIGN.md, `#atom(t)`), and `==` compares payloads, so
    // `==` on such an atom compares functions whose domain is not enumerable (Soundness).
    let src = "h = x -> x + 1;\nx = #a(h);\nsame = x == x;\n";
    assert_eq!(
        errors(src),
        [
            "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [x == x]"
        ]
    );
    let named = "h = x -> x + 1;\nx = #a(f: h, n: 1);\nsame = x != x;\n";
    assert_eq!(
        errors(named),
        [
            "`!=` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [x != x]"
        ]
    );
}

#[test]
fn a_function_nested_in_payloads_and_tuples_is_refused() {
    // Two atoms deep, the function is found by `==`; under a tuple, it is reported once, at the
    // tuple expression that holds it, as a function in a tuple is (CHK-held-cascade).
    let src = "h = x -> x + 1;\nx = #a(#b(h));\nsame = x == #c;\n";
    assert_eq!(
        errors(src),
        [
            "`==` takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [x == #c]"
        ]
    );
    let src = "h = x -> x + 1;\nx = #a((1, #b(f: h)));\nsame = x == #c;\n";
    assert_eq!(
        errors(src),
        [
            "a tuple takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [#b(f: h)]"
        ]
    );
}

#[test]
fn a_tuple_of_an_atom_whose_payload_holds_a_function_is_refused() {
    // A tuple takes data (L1.17), and an atom component's payload is part of it.
    let src = "h = x -> x + 1;\npair = (#a(h), 1);\n";
    assert_eq!(
        errors(src),
        [
            "a tuple takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [#a(h)]"
        ]
    );
}

#[test]
fn atoms_whose_payloads_are_data_still_compare() {
    let src = "x = #a(1, #b(n: 2.5), (3, \"s\"));\ny = #a(1, #b(n: 2.5), (3, \"t\"));\n\
               same = x == x;\ndiffer = x == y;\n";
    assert_eq!(value(src, "same"), "true");
    assert_eq!(value(src, "differ"), "false");
}

/// `scale`, a generic `wrap` that returns `body` with its parameter `x` in it, and `use`, which
/// compares what `wrap` gives with itself, called with `arg`.
fn compared_after_a_call(body: &str, arg: &str) -> String {
    format!(
        "scale(positional x) = x * 2;\nwrap(positional x) {{ return {body}; }}\n\
         use(positional x) {{ p = wrap(x); return p == p; }}\nsame = use({arg});\n"
    )
}

#[test]
fn a_function_reaching_a_payload_through_a_generic_call_is_refused_by_equality() {
    // `use` compares a tuple whose atom holds `use`'s parameter in its payload, so `==` needs
    // that parameter to be data, and `scale` is a function (ATOM-payload-open: the variable
    // inside the payload was not seen, so the call was accepted).
    // A tuple expression inside `wrap` checks its components as data, so there the need is
    // the tuple's.
    let refused = |what: &str| {
        [format!(
            "{what} takes data, and this value may hold a function, `(int) -> int`: data is a value that holds no function at any depth [use(scale)]"
        )]
    };
    for (body, what) in [
        ("#a(x), 1", "`==`"),
        ("1, #a(n: 1, f: x)", "`==`"),
        ("#a(#b(#c(x))), 1", "`==`"),
        ("(1, #a(x)), 1", "a tuple"),
        ("#a((x, 1)), 1", "a tuple"),
    ] {
        assert_eq!(
            errors(&compared_after_a_call(body, "scale")),
            refused(what),
            "{body}"
        );
    }
}

#[test]
fn data_reaching_a_payload_through_a_generic_call_still_compares() {
    // `value` panics on any error, so these are accepted.
    for body in ["#a(x), 1", "1, #a(n: 1, f: x)", "#a(#b(#c(x))), 1"] {
        let src = compared_after_a_call(body, "2");
        assert_eq!(value(&src, "same"), "true", "{body}");
    }
}
