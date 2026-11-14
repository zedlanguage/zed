//! An operation on literals alone passed as a call's argument at a parameter of a declared
//! carrier takes that carrier. DESIGN.md sec:domains: "A use fixes a literal's carrier as step
//! L1.26a describes: as an operand of an operator, the other operand's; at a declared type,
//! that type's; [...] An operation on literals alone, as `2 + 1`, is a literal too, and takes
//! the carrier of what it meets." Step L1.26a: "`x: f64 = 1 / 2` is `0.5`".

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The value of `y` in `src`, which the checker accepts.
fn y(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    value(src, "y")
}

const F64: &str = "f(x: f64) = x;\n";
const RAT: &str = "f(x: rat) = x;\n";

#[test]
fn a_division_of_literals_takes_the_carrier_of_the_parameter() {
    assert_eq!(y(&format!("{F64}y = f(x: 1 / 2);\n")), "0.5");
    assert_eq!(y(&format!("{RAT}y = f(x: 1 / 2);\n")), "1r/2r");
    assert_eq!(y(&format!("{F64}y = f(x: (1 / 2));\n")), "0.5");
    assert_eq!(y(&format!("{F64}y = f(x: -(1 / 2));\n")), "-0.5");
    assert_eq!(
        y(&format!("{F64}y = f(x: (1 + 2) / (3 + 4));\n")),
        "0.42857142857142855"
    );
    assert_eq!(y(&format!("{RAT}y = f(x: (1 + 2) / (3 + 4));\n")), "3r/7r");
}

#[test]
fn other_operations_on_literals_take_the_carrier_of_the_parameter() {
    assert_eq!(y(&format!("{F64}y = f(x: 1 + 2);\n")), "3.0");
    assert_eq!(y(&format!("{RAT}y = f(x: 1 + 2);\n")), "3r");
    assert_eq!(y(&format!("{F64}y = f(x: 0.5 * 3);\n")), "1.5");
    assert_eq!(y(&format!("{F64}y = f(x: 2 ^ 3);\n")), "8.0");
}

#[test]
fn each_argument_takes_the_carrier_of_its_own_parameter() {
    let g = "g(x: f64, y: rat) = (x, y);\n";
    assert_eq!(
        y(&format!("{g}y = g(x: 1 / 2, y: 1 / 3);\n")),
        "(0.5, 1r/3r)"
    );
    assert_eq!(
        y(&format!("{g}y = g(y: 1 / 3, x: 1 / 2);\n")),
        "(0.5, 1r/3r)"
    );
    let p = "g(positional x: f64, positional y: rat) = (x, y);\n";
    assert_eq!(y(&format!("{p}y = g(1 / 2, 1 / 3);\n")), "(0.5, 1r/3r)");
}

#[test]
fn a_division_of_literals_at_an_int_or_untyped_parameter_is_still_rejected() {
    // `/` has no arrow at `int`, and a parameter with no declared type fixes no carrier.
    for f in ["f(x: int) = x;\n", "f(x) = x + x;\n"] {
        let src = format!("{f}y = f(x: 1 / 2);\n");
        let errors = type_errors(&src);
        assert!(
            errors
                .iter()
                .any(|e| e.starts_with("Nothing gives the literal `1` a carrier")),
            "{src}: {errors:?}"
        );
    }
}

/// The checker does not build the rejection of an operation on literals alone whose call
/// gives it a carrier (`Ck::lit_spares`), since the call drops it. These programs come close
/// to that case, and each gives the same errors as before that change: an argument that
/// takes a carrier, one at a generic parameter of float formats, which takes none, a curried call, a `-` of a
/// division, nested divisions, a `^` at `rat`, a division by zero, a call in a function body,
/// an argument that is itself a call, and arguments the call refuses.
#[test]
fn a_rejection_a_call_drops_is_not_built_and_one_that_stands_is_unchanged() {
    let cases: &[(&str, &[&str])] = &[
        ("f(x: f64) = x;\ny = f(x: 1 / 0);\n", &[]),
        (
            "g(x) = sqrt(x);\ny = g(x: 1 / 2);\n",
            &[
                "Nothing gives the literal `1` a carrier of `f32 | f64 | rat`. Try `y = g(x: 1.0f64 / 2)` instead.\n  fixes, each checked here:\n    y = g(x: 1.0f64 / 2);    the literal is then the f64 1.0 [1]",
            ],
        ),
        ("f(x: rat) = x;\ny = f(x: (1 / 2) ^ 2);\n", &[]),
        ("f(x: rat) = x;\ny = f(x: 2 ^ -1);\n", &[]),
        ("f(x: f64) = x;\ny = f(x: -(1 / 2));\n", &[]),
        (
            "f(x: f64, z: f64) = x + z;\nh = f(x: 1 / 2, ...);\ny = h(z: 1.0);\n",
            &[],
        ),
        ("f(x: f64) = x;\ny = f(x: ((1 + 1) / 1 + 1) / 1);\n", &[]),
        (
            "f(x: f64) = x;\ny = f(x: 1 / 2, z: 3);\n",
            &[
                "this argument is passed by the name `z`, and `f` has no parameter of that name, so the argument has no parameter to go to. [3]",
            ],
        ),
        (
            "g(x: f64, z: int) = x;\ny = g(x: 1 / 2, z: \"a\");\n",
            &[
                "`g` does not take (f64, \"a\"): no arrow of `g` takes these types. [g(x: 1 / 2, z: \"a\")]",
            ],
        ),
        ("f(x: f64) = x;\nh() = f(x: 1 / 2);\ny = h();\n", &[]),
        ("f(x: f64) = x;\ny = f(x: f(x: 1 / 2) / 2);\n", &[]),
        (
            "f(x: int) = x;\ny = f(x: 1 / 2);\n",
            &[
                "`f` does not take (f64): no arrow of `f` takes these types. [f(x: 1 / 2)]",
                "Nothing gives the literal `1` a carrier of `f32 | f64 | rat`. Try `y = f(x: 1.0f64 / 2)` instead.\n  fixes, each checked here:\n    y = f(x: 1.0f64 / 2);    the literal is then the f64 1.0 [1]",
            ],
        ),
        ("f(x: f32) = x;\ny = f(x: 1 / 3);\n", &[]),
        ("f(x: f64) = x;\ny = f(x: 1 / 2) + 1 / 2;\n", &[]),
        (
            "y = 1 / 2;\n",
            &[
                "Nothing gives the integer literals a carrier, and `/` has none at `int`: `y = 1 / 2`. Try `y = 1.0f64 / 2` instead.\n  fixes, each checked here:\n    y = 1.0f64 / 2;    y is 0.5\n    y = 1r / 2;        y is 1r/2r\n    y = f64(1) / 2;    y is 0.5 [1 / 2]",
            ],
        ),
    ];
    let mut wrong = Vec::new();
    for &(src, want) in cases {
        let got = type_errors(src);
        if got != want {
            wrong.push(format!("{src:?}: {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
