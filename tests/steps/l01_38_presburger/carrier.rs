//! Rung 2 reads `+`, `-`, `*`, `div`, `mod`, `-x` and the comparisons as integer arithmetic,
//! so it is given only the parameters that take `int`s alone (RUNG2-carrier; LADDER-study
//! finding D6, case B23-3). At `f64` those laws are false: addition and multiplication round,
//! so they are not associative, and `inf` and `NaN` break cancellation, `x == x` and the
//! trichotomy of the comparisons. Each test below states a claim that rung 2 proves over
//! integers, shows with the interpreter that it is false at a float point, and checks that
//! rung 2 does not prove it there: the parameter is outside the linear-relation domain, as a
//! float literal is. `div` and `mod` do not take `f64`s, so they cannot be confused.

use zed_kernel::value::F64;
use zed_kernel::{Shared, Term, Value, eval};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_25_preimage_catalog::function;
use zed_tests::step_helpers::l01_26_type_resolution::sig_of;
use zedc::store::presburger::Entailment;

use super::entailment::verdict;

/// The value of the body of `ok` in `src` with its parameters bound to `point`.
fn at_floats(src: &str, point: &[f64]) -> Value {
    let (ps, body) = function(src);
    let t = (ps.iter().zip(point).rev()).fold(body, |t, (n, &v)| {
        Term::Let(
            n.clone(),
            Shared::new(Term::Lit(Value::Float(F64::new(v)))),
            Shared::new(t),
        )
    });
    eval(&t).unwrap_or_else(|e| panic!("{src}: {e:?}"))
}

/// Rung 2 does not prove `goal` from `premise`, which the interpreter shows false at the float
/// point `point`: there `premise` is `true` and `goal` is not. Neither is read at all: their
/// parameters are outside the domain.
fn not_read_at_floats(premise: &str, goal: &str, point: &[f64]) {
    assert_eq!(
        at_floats(premise, point),
        Value::Bool(true),
        "{premise} at {point:?}"
    );
    assert_ne!(
        at_floats(goal, point),
        Value::Bool(true),
        "{goal} at {point:?}"
    );
    let v = verdict(premise, goal);
    assert!(
        !matches!(v, Some(Entailment::Proved(_))),
        "{premise} to {goal}: proved"
    );
    assert!(v.is_none(), "{premise} to {goal}: read as {v:?}");
}

/// Rung 2 proves `goal` from `premise`.
fn proved(premise: &str, goal: &str) {
    let v = verdict(premise, goal);
    assert!(
        matches!(v, Some(Entailment::Proved(_))),
        "{premise} to {goal}: {v:?}"
    );
}

/// `ok` with the parameters `names`, each of type `ty`, and the body `body`.
fn ok(names: &str, ty: &str, body: &str) -> String {
    let ps: Vec<String> = (names.split(", ")).map(|n| format!("{n}: {ty}")).collect();
    format!("ok({}) = {body};", ps.join(", "))
}

const ADD_ASSOC: &str = "(a + b) + c == a + (b + c)";
const MUL_ASSOC: &str = "(a * b) * c == a * (b * c)";
const DISTRIB: &str = "a * (b + c) == a * b + a * c";

#[test]
fn float_associativity_is_not_proved() {
    // B23-3: 0.1 + 0.2 rounds up, so (0.1 + 0.2) + 0.3 is 0.6000000000000001 and
    // 0.1 + (0.2 + 0.3) is 0.6; 10 * (0.1 + 0.2) is 3.0000000000000004 and 10 * 0.1 + 10 * 0.2
    // is 3.
    let t = ok("a, b, c", "f64", "true");
    not_read_at_floats(&t, &ok("a, b, c", "f64", ADD_ASSOC), &[0.1, 0.2, 0.3]);
    not_read_at_floats(&t, &ok("a, b, c", "f64", MUL_ASSOC), &[0.1, 0.2, 0.3]);
    not_read_at_floats(&t, &ok("a, b, c", "f64", DISTRIB), &[10.0, 0.1, 0.2]);
}

#[test]
fn integer_associativity_is_still_proved() {
    let t = ok("a, b, c", "int", "true");
    // A product of three factors is outside the domain at every carrier.
    assert!(verdict(&t, &ok("a, b, c", "int", MUL_ASSOC)).is_none());
    for law in [ADD_ASSOC, DISTRIB] {
        proved(&t, &ok("a, b, c", "int", law));
    }
    // An unannotated function whose integer literal makes its parameters `int`.
    proved(
        "ok(a, b, c) = a >= 0;",
        "ok(a, b, c) = (a + b) + c + 0 == a + (b + c);",
    );
}

#[test]
fn rational_and_generic_parameters_are_not_read_as_integers() {
    // A `rat` is not an integer. A parameter without a type or a literal ranges over
    // `int | f64 | rat`, and its laws are those of all three.
    let t = ok("a, b, c", "rat", "true");
    for law in [ADD_ASSOC, MUL_ASSOC, DISTRIB] {
        assert!(verdict(&t, &ok("a, b, c", "rat", law)).is_none(), "{law}");
    }
    let points = [[0.1, 0.2, 0.3], [0.1, 0.2, 0.3], [10.0, 0.1, 0.2]];
    for (law, point) in [ADD_ASSOC, MUL_ASSOC, DISTRIB].into_iter().zip(points) {
        let g = format!("ok(a, b, c) = {law};");
        assert!(verdict("ok(a, b, c) = true;", &g).is_none(), "{g}");
        // The float point where it is false, through the generic function.
        assert_ne!(at_floats(&g, &point), Value::Bool(true), "{g}");
    }
}

#[test]
fn float_subtraction_and_negation_are_not_read_as_integers() {
    let t2 = ok("a, b", "f64", "true");
    // inf - inf is NaN.
    let inf = f64::INFINITY;
    not_read_at_floats(&t2, &ok("a, b", "f64", "(a - b) + b == a"), &[1.0, inf]);
    not_read_at_floats(&t2, &ok("a, b", "f64", "a + (-a) == b - b"), &[inf, 0.0]);
    not_read_at_floats(
        &t2,
        &ok("a, b", "f64", "a - b == -(b - a)"),
        &[f64::NAN, 0.0],
    );
    let t1 = ok("a", "f64", "true");
    not_read_at_floats(&t1, &ok("a", "f64", "-(-a) == a"), &[f64::NAN]);
    // Each is proved at `int`.
    for law in ["(a - b) + b == a", "a + (-a) == b - b", "a - b == -(b - a)"] {
        proved(&ok("a, b", "int", "true"), &ok("a, b", "int", law));
    }
    proved(&ok("a", "int", "true"), &ok("a", "int", "-(-a) == a"));
}

#[test]
fn float_multiplication_is_not_read_as_integer_multiplication() {
    // NaN equals nothing, itself included.
    let t2 = ok("a, b", "f64", "true");
    not_read_at_floats(&t2, &ok("a, b", "f64", "a * b == b * a"), &[f64::NAN, 1.0]);
    // inf * 0 is NaN.
    not_read_at_floats(
        &t2,
        &ok("a, b", "f64", "a * (b - b) == b - b"),
        &[f64::INFINITY, 1.0],
    );
    for law in ["a * b == b * a", "a * (b - b) == b - b"] {
        proved(&ok("a, b", "int", "true"), &ok("a, b", "int", law));
    }
}

#[test]
fn float_comparisons_are_not_read_as_integer_comparisons() {
    let nan = f64::NAN;
    let t2 = ok("a, b", "f64", "true");
    // At NaN every comparison is false but `!=`.
    for law in [
        "a < b || a >= b",
        "a <= b || b <= a",
        "a == a",
        "a < b || a == b || a > b",
    ] {
        let p = if law.contains('b') {
            [nan, 1.0]
        } else {
            [nan, 0.0]
        };
        not_read_at_floats(&t2, &ok("a, b", "f64", law), &p);
        proved(&ok("a, b", "int", "true"), &ok("a, b", "int", law));
    }
    // An entailment: `a <= b` and `c = inf` with `a = -inf` give `a + c` NaN.
    let premise = ok("a, b, c", "f64", "a <= b");
    let goal = ok("a, b, c", "f64", "a + c <= b + c");
    not_read_at_floats(&premise, &goal, &[f64::NEG_INFINITY, 0.0, f64::INFINITY]);
    proved(
        &ok("a, b, c", "int", "a <= b"),
        &ok("a, b, c", "int", "a + c <= b + c"),
    );
}

#[test]
fn div_and_mod_do_not_take_floats() {
    for op in ["div", "mod"] {
        let src = ok("a, b", "f64", &format!("a {op} b == a {op} b"));
        let errors = elab(&src).expect_err(&src);
        assert!(
            errors[0].starts_with(&format!("`{op}` does not take (f64, f64)")),
            "{errors:?}"
        );
    }
}

#[test]
fn an_int_parameter_beside_a_float_one_is_read_where_the_float_is_not() {
    let t = "ok(n: int, x: f64) = true;";
    proved(t, "ok(n: int, x: f64) = (n + n) + n == n + (n + n);");
    // `x == x` is false at NaN; reading `x` would prove it.
    let goal = "ok(n: int, x: f64) = (n + n) + n == n + (n + n) && x == x;";
    assert!(!matches!(verdict(t, goal), Some(Entailment::Proved(_))));
}

#[test]
fn the_int_parameters_of_a_signature() {
    for (src, ints) in [
        ("ok(a: int, b: int) = a < b;", vec![true, true]),
        ("ok(a: f64, b: int) = a < a && b < b;", vec![false, true]),
        ("ok(a: rat) = a < a;", vec![false]),
        ("ok(a: bool, x: int) = a && x > 0;", vec![false, true]),
        // A type variable bounded by `int | f64 | rat`.
        ("ok(a, b) = a < b;", vec![false, false]),
        // The literal makes both `int`.
        ("ok(a, b) = a + 1 < b;", vec![true, true]),
        // A member atom: `#none + 1` is not an integer sum.
        ("ok(a: int | #none) = a == a;", vec![false]),
        // A parameter that is never read is generic and so not `int`.
        ("ok(a, n: int) = n > 0;", vec![false, true]),
    ] {
        assert_eq!(sig_of(src, "ok").int_params(), ints, "{src}");
    }
}

/// `ok` over `x, y, z, w` of type `ty`, or unannotated where `ty` is empty, whose four rows,
/// written without a literal, hold at no integer point the solver can find and are refused
/// at `int` (the growth rows of `checker.rs` with their constants dropped and `>=` made `>`),
/// and a `main` that calls it with `one` for each argument.
fn growth(ty: &str, one: &str) -> String {
    fn times(c: usize, v: &str) -> String {
        vec![v; c].join(" + ")
    }
    fn side(terms: Side) -> String {
        let ts: Vec<String> = terms.iter().map(|&(c, v)| times(c, v)).collect();
        ts.join(" + ")
    }
    /// A sum of variables, each repeated its count of times.
    type Side = &'static [(usize, &'static str)];
    let rows: [(Side, Side); 4] = [
        (&[(4, "x")], &[(12, "w"), (10, "y"), (12, "z")]),
        (&[(4, "w"), (10, "x")], &[(10, "y"), (11, "z")]),
        (&[(11, "w"), (4, "x"), (12, "z")], &[(1, "y")]),
        (&[(12, "y")], &[(8, "w"), (5, "x"), (1, "z")]),
    ];
    let body: Vec<String> = (rows.iter())
        .map(|(l, r)| format!("({}) > ({})", side(l), side(r)))
        .collect();
    let ps: Vec<String> = ["x", "y", "z", "w"]
        .iter()
        .map(|p| {
            if ty.is_empty() {
                p.to_string()
            } else {
                format!("{p}: {ty}")
            }
        })
        .collect();
    format!(
        "ok({}) = {};\nmain(stdin: Lines) -> (stdout: Lines) {{\n  r = if ok(x: {one}, y: {one}, \
         z: {one}, w: {one}) {{ \"in\" }} else {{ \"out\" }};\n  stdout <- \"${{r}}\";\n}}\n",
        ps.join(", "),
        body.join(" && ")
    )
}

#[test]
fn the_checker_asks_no_integer_question_of_a_float_function() {
    // At `int` the question is refused, which rejects the program; at `f64` and over a type
    // variable it is not an integer question, so nothing is asked and the program runs.
    let o = run("carrier-int", &growth("int", "1"), "", &[]);
    assert_eq!(o.status, 1, "{}", o.stderr);
    assert!(
        o.stderr.contains("whether `ok` can hold is not decided"),
        "{}",
        o.stderr
    );
    for (name, ty, one) in [("carrier-f64", "f64", "1.0"), ("carrier-generic", "", "1")] {
        let o = run(name, &growth(ty, one), "", &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, "out\n", ""),
            "{ty}"
        );
    }
}

#[test]
fn the_int_parameters_of_a_signature_scale() {
    // O(arrows × parameters): each parameter's type on each arrow is tested once.
    let sig = |k: usize| {
        let ps: Vec<String> = (0..k)
            .map(|i| format!("p{i}: {}", if i % 2 == 0 { "int" } else { "f64" }))
            .collect();
        sig_of(&format!("ok({}) = true;", ps.join(", ")), "ok")
    };
    let sigs = scaling::inputs(1024, sig);
    scaling::check(
        "the int parameters of a signature of n parameters",
        1024,
        |k| {
            let ints = sigs[&k].int_params();
            assert_eq!(ints.iter().filter(|&&i| i).count(), k / 2);
        },
    );
}

#[test]
fn a_float_times_zero_and_a_float_power_are_not_read_as_integers() {
    // The plan row's cases: `x * 0.0` is NaN at an infinity and at NaN, and `x ^ 2.0` is NaN
    // at NaN, so neither law holds over `f64`; over `int` rung 2 proves both. A power of an
    // `f64` takes an `f64` exponent, which rung 2 does not read (`Op::Pow` takes an integer
    // literal), so `^` was outside the domain at `f64` before the filter too.
    let t1 = ok("x", "f64", "true");
    not_read_at_floats(&t1, &ok("x", "f64", "x * 0.0 == 0.0"), &[f64::INFINITY]);
    not_read_at_floats(&t1, &ok("x", "f64", "x ^ 2.0 >= 0.0"), &[f64::NAN]);
    let t1 = ok("x", "int", "true");
    proved(&t1, &ok("x", "int", "x * 0 == 0"));
    proved(&t1, &ok("x", "int", "x ^ 2 == x * x"));
}

#[test]
fn a_refinement_of_int_is_read_as_int() {
    // `bitAnd` takes `int[0..]`, so `a` is a refinement of `int` with no literal beside it,
    // and its parameter counts as `int`.
    let src = "ok(a) = bitAnd(a, a) == a;";
    assert_eq!(sig_of(src, "ok").int_params(), [true]);
}
