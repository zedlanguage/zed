//! A call outside every function whose tuple argument holds literals without a suffix has a
//! static type that holds every value the function computes from them (item
//! SOUND-top-literals). A literal component that a use in the body asks for a carrier, as `+`
//! does in `h(positional p) = p[0] + p[1]`, stands for any value of that carrier, as a
//! bounded variable does at a call (DESIGN.md step L1.26a): `r = h((1, 2))` is `int`, which
//! holds its value `3`. It was `1 | 2`, the literals the call passed, which does not. A
//! component no use asks for a carrier is only copied, and keeps its literal's own type:
//! `p[0]` of `(1, 2)` is `1`.

use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{info, type_errors};

/// The static type of `r` in `src` and its value, and whether the type holds the value; the
/// checker's errors must be none.
fn typed_value(src: &str) -> (String, String, bool) {
    let (i, _) = info(src);
    let errors: Vec<&str> = i.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(errors.is_empty(), "{src}\nerrors: {errors:?}");
    let ty = i
        .tops
        .get("r")
        .unwrap_or_else(|| panic!("{src}\nno type for `r`"));
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}\n{e:?}"));
    let term = unit.get("r").unwrap_or_else(|| panic!("{src}\nno `r`"));
    let v = zed_kernel::eval(&with_prelude(term)).unwrap_or_else(|e| panic!("{src}\n{e:?}"));
    let kernel = ty
        .kernel()
        .unwrap_or_else(|| panic!("{src}\n`{ty}` has no kernel type"));
    (ty.to_string(), v.to_string(), kernel.contains(&v))
}

/// Each program's `r` has the type and the value beside it, and the type holds the value.
/// The type before the fix is in the comment: none of them held the value.
#[test]
fn a_computed_result_has_the_carrier_and_not_the_literals_passed() {
    let cases = [
        // was `1 | 2`
        (
            "h(positional p) = p[0] + p[1];\nr = h((1, 2));\n",
            "int",
            "3",
        ),
        // a destructure; was `1 | 2`
        (
            "h(positional p) { a, b = p; return a + b; }\nr = h((1, 2));\n",
            "int",
            "3",
        ),
        // was `1`
        ("h(positional p) = p[0] * 3;\nr = h((1, 2));\n", "int", "3"),
        // was `1`
        ("h(positional p) = -p[0];\nr = h((1, 2));\n", "int", "-1"),
        // was `1 | 2`
        (
            "h(positional p) = p[0] - p[1];\nr = h((1, 2));\n",
            "int",
            "-1",
        ),
        // was `1`
        ("h(positional p) = p[0] + 1;\nr = h((1, 2));\n", "int", "2"),
        // was `3`
        ("h(positional p) = p[0] ^ 2;\nr = h((3, 2));\n", "int", "9"),
        // a nested tuple; was `1 | 2`
        (
            "h(positional p) = p[0][0] + p[1];\nr = h(((1, 5), 2));\n",
            "int",
            "3",
        ),
        // a nested call; was `1`
        (
            "g(positional x) = x + 1;\nh(positional p) = g(p[0]);\nr = h((1, 2));\n",
            "int",
            "2",
        ),
        // a lambda; was `1`
        (
            "h(positional f, positional p) = f(p[0]);\nr = h(x -> x + 1, (1, 2));\n",
            "int",
            "2",
        ),
        // a component of a returned tuple; was `1 | 2`
        (
            "h(positional p) = (p[0] + p[1], p[0]);\nr = h((1, 2))[0];\n",
            "int",
            "3",
        ),
        // an `if` of literals as a component; was `1 | 2 | 5`
        (
            "h(positional p) = p[0] + p[1];\nr = h((if 1 < 2 { 1 } else { 2 }, 5));\n",
            "int",
            "6",
        ),
        // a named parameter; was `1 | 2`
        ("h(p) = p[0] + p[1];\nr = h(p: (1, 2));\n", "int", "3"),
        // through a second function; was `1 | 2`
        (
            "h(positional p) = p[0] + p[1];\ng(positional p) = h(p);\nr = g((1, 2));\n",
            "int",
            "3",
        ),
        // a comparison asks for a carrier too, so a selection is the carrier: as `h(1, 2)` is
        // for `h(positional x, positional y) = if x < y { x } else { y }`; was `1 | 2`
        (
            "h(positional p) = if p[0] < p[1] { p[0] } else { p[1] };\nr = h((1, 2));\n",
            "int",
            "1",
        ),
        // was `1 | 2`
        (
            "h(positional p) = max(p[0], p[1]);\nr = h((1, 2));\n",
            "int",
            "2",
        ),
        // a suffix fixes the carrier, which the bare literal adopts
        (
            "h(positional p) = p[0] + p[1];\nr = h((1r, 2));\n",
            "rat",
            "3r",
        ),
        (
            "h(positional p) = p[0] + p[1];\nr = h((1, 2.5f64));\n",
            "f64",
            "3.5",
        ),
    ];
    check_all(&cases);
}

/// A component that no use asks for a carrier is copied, never computed on, and keeps its
/// literal's type: a fix that made every component its carrier would print `int` here.
#[test]
fn a_copied_component_keeps_its_literal_type() {
    let cases = [
        ("h(positional p) = p[0];\nr = h((1, 2));\n", "1", "1"),
        (
            "h(positional p) { x = p[0]; return x; }\nr = h((1, 2));\n",
            "1",
            "1",
        ),
        (
            "h(positional p) = (p[0], p[1]);\nr = h((1, 2));\n",
            "(1, 2)",
            "(1, 2)",
        ),
        ("h(positional p) = p[1];\nr = h((\"s\", 2));\n", "2", "2"),
    ];
    check_all(&cases);
}

/// Integer literals at a use with no `int`, as `/`, have no carrier to take: the call is
/// rejected as `h(1, 2)` is, at the first literal. It was accepted as `1 | 2 | #divByZero`,
/// and the run stopped on `/` of two `int`.
#[test]
fn integer_literals_at_a_use_without_int_are_rejected() {
    let errors = type_errors("h(positional p) = p[0] / p[1];\nr = h((1, 2));\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with(
            "Nothing gives the literal `1` a carrier of `f32 | f64 | rat`. Try `r = h((1.0f64, 2))` \
             instead."
        ),
        "{errors:?}"
    );
    // The repair it offers checks, and its type holds its value.
    let (t, v, holds) = typed_value("h(positional p) = p[0] / p[1];\nr = h((1.0f64, 2));\n");
    assert_eq!(
        (t.as_str(), v.as_str(), holds),
        ("f64 | #divByZero", "0.5", true)
    );
}

/// A decimal literal that nothing gives a carrier is rejected once, where the arguments are
/// read, and not again by the type of the call.
#[test]
fn a_decimal_component_is_rejected_once() {
    let errors = type_errors("h(positional p) = p[0] + p[1];\nr = h((1.5, 2));\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("Nothing gives the literal `1.5` a carrier."),
        "{errors:?}"
    );
}

/// The case of the item, by `zedc run`: the program prints `3`, and the checker's type of `r`
/// is `int`, which `++` with a string shows.
#[test]
fn the_program_of_the_item_prints_a_value_of_its_type() {
    let src = "h(positional p) = p[0] + p[1];\nr = h((1, 2));\n\
               main(m: MainArgs) { m.stdout <- \"${r}\"; }\n";
    let out = run("l01_26a_top_literals", src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "3\n");
    let errors = type_errors("h(positional p) = p[0] + p[1];\nr = h((1, 2));\nq = r ++ \"a\";\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`++` does not take (int, \"a\")"),
        "{errors:?}"
    );
}

/// Checks every case of `cases`, each a program, the type of its `r` and its value, and that
/// the type holds the value; the failures are all listed together.
fn check_all(cases: &[(&str, &str, &str)]) {
    let mut wrong = Vec::new();
    for &(src, ty, value) in cases {
        let (t, v, holds) = typed_value(src);
        if (t.as_str(), v.as_str()) != (ty, value) || !holds {
            wrong.push(format!("{src}  type {t}, value {v}, want {ty}, {value}"));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {}:\n{}",
        wrong.len(),
        cases.len(),
        wrong.join("\n")
    );
}
