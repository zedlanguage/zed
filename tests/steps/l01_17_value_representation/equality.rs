//! The language's `==`: IEEE 754 at floats, at any depth, and structural elsewhere; and on
//! functions, an error until types give the domain to compare them on.

use zed_kernel::term::build::{lam, prim, var};
use zed_kernel::{Evaluator, F64, Prim, Value, World};

use crate::l01_16_elaboration::{errors, value};

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
    // The identity keys and the law catalog read is bitwise (sec:keys), whatever `==` says.
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
        ["`==` takes data, and this value may hold a function, `(int) -> int` [inc == also]"]
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
        ["a tuple takes data, and this value may hold a function, `(int) -> int` [inc]"]
    );
}
