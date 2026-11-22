//! An operation on literals alone passed as a call's argument at a parameter of a declared
//! carrier takes that carrier. DESIGN.md sec:domains: "A use fixes a literal's carrier as step
//! L1.26a describes: as an operand of an operator, the other operand's; at a declared type,
//! that type's; [...] An operation on literals alone, as `2 + 1`, is a literal too, and takes
//! the carrier of what it meets." Step L1.26a: "`x: f64 = 1 / 2` is `0.5`".

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
use zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main;

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

/// `f(x: int) = x;` and `n` calls `f(x: 1 / 2)`, each bound to a name at the top level, or
/// each the body of a function where `body` holds: `n` messages, one per call.
pub(super) fn int_param_divisions(n: usize, body: bool) -> String {
    let mut src = String::from("f(x: int) = x;\n");
    for i in 0..n {
        src += &match body {
            true => format!("g{i}() = f(x: 1 / 2);\n"),
            false => format!("y{i} = f(x: 1 / 2);\n"),
        };
    }
    src
}

#[test]
fn many_divisions_at_an_int_parameter_are_rejected_once_each() {
    // A small instance of `bench::call_arguments::divisions_at_an_int_parameter_scale`.
    for body in [false, true] {
        let errors = type_errors(&int_param_divisions(5, body));
        assert_eq!(errors.len(), 5, "{errors:?}");
        assert!(
            errors
                .iter()
                .all(|e| e.starts_with("`f` takes an `int` as `x`"))
        );
    }
}

#[test]
fn a_division_of_literals_at_an_int_or_untyped_parameter_is_still_rejected() {
    // A parameter with no declared type fixes no carrier.
    let src = "f(x) = x + x;\ny = f(x: 1 / 2);\n";
    let errors = type_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| e.starts_with("Nothing gives the literal `1` a carrier")),
        "{src}: {errors:?}"
    );
    // `/` has no arrow at `int`. DESIGN.md step L1.26b: "each fix its message offers is
    // applied in turn, and the file then checks", and at an `int` parameter no fix that keeps
    // the `/` checks (`1r / 2` and `1.0f64 / 2` are each refused by `f`), so the one message
    // names the `/` and the parameter's type and offers none, the same at the top level and in
    // a body (row LIT-call-int-param-fix-unchecked: zedc gave a second message, whose one fix,
    // `y = f(x: 1.0f64 / 2)`, `f` rejected in turn).
    let int = "`f` takes an `int` as `x`, and `/` has no arrow at `int`, so `1 / 2` cannot be \
               passed there. No fix is offered: a fix that keeps the `/` is rejected by `f` \
               too. [1 / 2]";
    for uses in ["y = f(x: 1 / 2);\n", "g() = f(x: 1 / 2);\n"] {
        let src = format!("f(x: int) = x;\n{uses}");
        assert_eq!(type_errors(&src), [int], "{src}");
        // A division by zero, which has no `rat` value, gets the same one message.
        let src = src.replace("1 / 2", "1 / 0");
        assert_eq!(type_errors(&src), [int.replace("1 / 2", "1 / 0")], "{src}");
    }
    for fixed in ["y = f(x: 1.0f64 / 2);\n", "y = f(x: 1r / 2);\n"] {
        let src = format!("f(x: int) = x;\n{fixed}");
        assert_eq!(type_errors(&src).len(), 1, "{src}");
    }
}

/// The checker does not build the rejection of an operation on literals alone whose call
/// gives it a carrier (`Ck::lit_spares`), since the call drops it. These programs come close
/// to that case, and each gives the same errors as before that change: an argument that
/// takes a carrier, one at a generic parameter of float formats, which takes none, a curried call,
/// a `-` of a division, nested divisions, a `^` at `rat`, a division by zero, a call in a function
/// body, an argument that is itself a call, and arguments the call refuses.
#[test]
fn a_rejection_a_call_drops_is_not_built_and_one_that_stands_is_unchanged() {
    let cases: &[(&str, &[&str])] = &[
        ("f(x: f64) = x;\ny = f(x: 1 / 0);\n", &[]),
        (
            "g(x) = sqrt(x);\ny = g(x: 1 / 2);\n",
            &[
                "Nothing gives the literal `1` a carrier. Try `y = g(x: 1.0f64 / 2)` instead.\n  fixes, each checked here:\n    y = g(x: 1.0f64 / 2);    the literal is then the f64 1.0 [1]",
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
        // A callee with a variable inside a function type is applied at its instance
        // (`Ck::instantiated`), which keeps the parameter `x: f64` the spare read; a call
        // whose other argument follows an error still gives its argument the carrier
        // (`Ck::lit_spares`, proof step 3).
        (
            "g(x: f64, xs: T, f: (T) -> T) = x;\ny = g(x: 1 / 2, xs: 3, f: (v) -> v + 1);\n",
            &[],
        ),
        (
            "f(x: f64, z: int) = x;\ny = f(x: 1 / 2, z: true + 1);\n",
            &["`+` does not take (true, 1): no arrow of `+` takes these types. [true + 1]"],
        ),
        ("f(x: f64) = x;\ny = f(x: f(x: 1 / 2) / 2);\n", &[]),
        // One message, no fix (row LIT-call-int-param-fix-unchecked;
        // `a_division_of_literals_at_an_int_or_untyped_parameter_is_still_rejected`).
        (
            "f(x: int) = x;\ny = f(x: 1 / 2);\n",
            &[
                "`f` takes an `int` as `x`, and `/` has no arrow at `int`, so `1 / 2` cannot be passed there. No fix is offered: a fix that keeps the `/` is rejected by `f` too. [1 / 2]",
            ],
        ),
        ("f(x: f32) = x;\ny = f(x: 1 / 3);\n", &[]),
        ("f(x: f64) = x;\ny = f(x: 1 / 2) + 1 / 2;\n", &[]),
        (
            "y = 1 / 2;\n",
            &[
                "Nothing gives the integer literals a carrier, and `/` has none at `int`: `y = 1 / 2`. Try `y = 1r / 2` instead.\n  fixes, each checked here:\n    y = 1r / 2;        y is 1r/2r\n    y = 1.0 / 2;       y is 0.5\n    y = f64(1) / 2;    y is 0.5 [1 / 2]",
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

/// Row FAIL-int-or-rat-param-division: at a parameter declared `int | rat`, `/` has an arrow at
/// `rat` alone among the parameter's carriers, so an operation on literals alone holding a `/`
/// takes `rat` there, at the top level and in a body alike, as it does at `f(x: rat)`; `+`, which
/// has an arrow at both, leaves the integer literals at `int`.
#[test]
fn a_division_of_literals_at_an_int_or_rat_parameter_takes_rat() {
    for uses in ["y = f(x: 1 / 2);\n", "g() = f(x: 1 / 2);\ny = g();\n"] {
        let src = format!("f(x: int | rat) = x;\n{uses}");
        assert_eq!(y(&src), "1r/2r", "{src}");
    }
    let src = "f(x: int | rat) = x;\ny = f(x: (1 + 2) / 4);\n";
    assert_eq!(y(src), "3r/4r");
    let src = "f(x: int | rat) = x;\ny = f(x: 1 + 2);\n";
    assert_eq!(y(src), "3");
}

#[test]
fn a_derivation_gives_a_generic_call_its_carrier_and_not_the_argument() {
    // `half(x: 3r)` is a rat, not the single value `3r` written as its argument (row
    // CALL-var-singleton), both where the call is an argument and where a name holds it.
    let out = rejected_with_main(
        "half(x) = x / 2;\nf(positional a: int) = a + 1;\ny = f(half(x: 3r));\n",
    );
    assert!(out.contains("this call of `half` gives rat\n"), "{out}");
    assert!(!out.contains("gives 3r"), "{out}");
    let out = rejected_with_main("half(x) = x / 2;\ny = half(x: 3r);\nz = popCount(y);\n");
    assert!(
        out.contains("`y` is defined as this expression, rat\n"),
        "{out}"
    );
    assert!(out.contains("this call of `half` gives rat\n"), "{out}");
    assert!(!out.contains("gives 3r"), "{out}");
}
