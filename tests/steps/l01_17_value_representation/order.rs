//! The natural order (DESIGN.md sec:keys): kinds in a fixed order, numbers by value across
//! `int`, `rat` and floats, an `int` before a `rat` before a float of equal value.

use zed_kernel::{Family, Value};

use crate::l01_16_elaboration::{elab, with_prelude};

/// The values of the definitions `names` of `src`.
fn values(src: &str, names: &[&str]) -> Vec<Value> {
    let u = elab(src).unwrap();
    names
        .iter()
        .map(|n| zed_kernel::eval(&with_prelude(u.get(n).unwrap())).unwrap())
        .collect()
}

#[test]
fn numbers_order_by_value_across_kinds() {
    let src = "a = 1;\nb = 1r;\nc = 1.0;\nd = 3r / 2r;\ne = 1.25;\nf = 2;\n\
               g = -100000000000000000000;\nh = 100000000000000000000;\ni = 0.0 / 0.0;\n\
               j = 1.0 / 0.0;\nk = -1.0 / 0.0;\n";
    let mut vs = values(
        src,
        &["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k"],
    );
    vs.sort();
    let shown: Vec<String> = vs.iter().map(|v| v.to_string()).collect();
    assert_eq!(
        shown,
        [
            "-inf",
            "-100000000000000000000",
            "1",
            "1r",
            "1.0",
            "1.25",
            "3r/2r",
            "2",
            "100000000000000000000",
            "inf",
            "nan"
        ]
    );
}

#[test]
fn kinds_order_atoms_bools_numbers_strings_tuples() {
    let src = "a = (1, 2);\nb = \"apple\";\nc = 7;\nd = true;\ne = #none;\nf = (1, 2, 3);\n\
               g = #err(code: 2);\nh = #err(1);\n";
    let mut vs = values(src, &["a", "b", "c", "d", "e", "f", "g", "h"]);
    vs.sort();
    let shown: Vec<String> = vs.iter().map(|v| v.to_string()).collect();
    assert_eq!(
        shown,
        [
            "#err(1)",
            "#err(code: 2)",
            "#none",
            "true",
            "7",
            "\"apple\"",
            "(1, 2)",
            "(1, 2, 3)"
        ]
    );
}

#[test]
fn a_family_keyed_by_mixed_numbers_visits_them_by_value() {
    let keys = ["10", "2r", "1.5", "100000000000000000000", "-3"];
    let src: String = keys
        .iter()
        .enumerate()
        .map(|(i, k)| format!("k{i} = {k};\n"))
        .collect();
    let names: Vec<String> = (0..keys.len()).map(|i| format!("k{i}")).collect();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let vs = values(&src, &names);
    let f = Family::of(vs.into_iter().map(|k| (k, Value::Bool(true))));
    let order: Vec<String> = f.iter().map(|(k, _)| k.to_string()).collect();
    assert_eq!(order, ["-3", "1.5", "2r", "10", "100000000000000000000"]);
}
