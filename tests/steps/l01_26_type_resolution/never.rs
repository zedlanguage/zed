//! The empty type is the prelude type `Never` (DESIGN.md, the L1 row of "Defined words by
//! layer"): a program writes it from L1 on, and the checker prints a type with no value as
//! `Never`. A declared result type `-> Never` and a binding with a declared type `x: Never = 1`
//! are forms of layer L10, which zedc does not support yet, so these tests write `Never` where
//! L1 takes a type: a parameter's type and a function type's result.

use super::{info, sig, type_errors};

#[test]
fn a_function_type_may_declare_the_result_never() {
    let text = "apply(positional h: (int) -> Never, positional n: int) = h(n);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "apply"), "(int -> Never, int) -> Never");
}

#[test]
fn never_in_a_union_adds_nothing() {
    assert_eq!(
        sig("g(positional n: int | Never) = n;\n", "g"),
        "int -> int"
    );
}

#[test]
fn a_parameter_of_type_never_takes_no_argument() {
    let text = "take(positional x: Never) = x;\nr = take(1);\n";
    assert_eq!(
        type_errors(text),
        ["`take` does not take (1): no arrow of `take` takes these types. [take(1)]"]
    );
    assert_eq!(sig(text, "take"), "Never -> Never");
}

#[test]
fn a_test_against_never_is_accepted() {
    // `x is Never` holds of no value, so the first branch is unreachable: it is still
    // checked, and adds nothing to the result (DESIGN.md sec:constraints).
    let text = "h(positional x: int) = if x is Never { 1 } else { 2 };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "h"), "int -> 2");
}

/// A tuple with an empty component has no value, so its type is `Never`: written as a
/// parameter's type, nested, in a union, and made by a tuple expression.
#[test]
fn a_tuple_with_an_empty_component_is_never() {
    for (text, want) in [
        ("f(positional x: (Never, int)) = x;\n", "Never -> Never"),
        ("f(positional x: (int, Never)) = x;\n", "Never -> Never"),
        (
            "f(positional x: ((Never, int), bool)) = x;\n",
            "Never -> Never",
        ),
        (
            "f(positional x: (int, Never) | bool) = x;\n",
            "bool -> bool",
        ),
        ("f(positional x: Never) = (x, 1);\n", "Never -> Never"),
        (
            "f(positional x: Never) = { y = ((x, 1), true); y };\n",
            "Never -> Never",
        ),
        // An atom whose payload has no value has none either.
        ("f(positional x: Never) = #a(x);\n", "Never -> Never"),
        // A function whose result has no value returns no value.
        (
            "f(positional g: (int) -> (Never, int)) = g(1);\n",
            "(int -> Never) -> Never",
        ),
        // The empty tuple has one value, and is no `Never`.
        ("f(positional x: ()) = x;\n", "(()) -> ()"),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
}

/// A branch whose test narrows a name to a type with no value is unreachable and adds nothing
/// to the result; a test that may hold keeps both branches.
#[test]
fn an_unreachable_branch_adds_nothing_to_the_result() {
    for (text, want) in [
        (
            "f(positional x: int) = if x is bool { 1 } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: int) = if x is int { 1 } else { 2 };\n",
            "int -> 1",
        ),
        (
            "f(positional x: int) = if x is not int { 1 } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: int) = if x is not Never { 1 } else { 2 };\n",
            "int -> 1",
        ),
        (
            "f(positional x: int) = if x is (Never, int) { 1 } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: int | String) = if x is int { 1 } else if x is String { 2 } else \
             { 3 };\n",
            "(int | String) -> 1 | 2",
        ),
        // In the unreachable branch `x` is `Never`, so it adds nothing there either.
        (
            "f(positional x: int) = if x is Never { x } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: int) = { y = (x, 1); if x is bool { y } else { (1, 2) } };\n",
            "int -> (1, 2)",
        ),
        // A name of type `Never` makes both branches unreachable.
        (
            "f(positional x: Never) = if x is int { 1 } else { 2 };\n",
            "Never -> Never",
        ),
        // A test that may hold keeps both branches.
        (
            "f(positional x: int | bool) = if x is int { 1 } else { 2 };\n",
            "(int | bool) -> 1 | 2",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
}

/// An unreachable branch is still checked: an error in it is reported.
#[test]
fn an_unreachable_branch_is_still_checked() {
    let text = "f(positional x: int) = { y = (x, 1); if x is Never { y } else { y + 1 } };\n";
    assert_eq!(
        type_errors(text),
        ["`+` does not take ((int, 1), 1): no arrow of `+` takes these types. [y + 1]"]
    );
    // `x` is `Never` there, and `true` is still no operand of `+`.
    let text = "f(positional x: int) = if x is Never { x + true } else { 2 };\n";
    assert_eq!(
        type_errors(text),
        ["`+` does not take (Never, true): no arrow of `+` takes these types. [x + true]"]
    );
}

/// A branch whose tests contradict each other on the values of a name, so that no value of it
/// passes them all, is unreachable and adds nothing to the result, though the type of each
/// name there still lists values (DESIGN.md sec:constraints).
#[test]
fn a_branch_no_value_reaches_adds_nothing_to_the_result() {
    for (text, want) in [
        (
            "f(positional x: int) = if x > 0 && x < 0 { 1 } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: int) = if x > 0 { if x < 0 { 1 } else { 2 } } else { 3 };\n",
            "int -> 2 | 3",
        ),
        // The test holds of every value, so the second branch is the unreachable one.
        (
            "f(positional x: int) = if x >= 0 || x < 0 { 1 } else { 2 };\n",
            "int -> 1",
        ),
        (
            "f(positional x: int) = if !(x > 0 || x <= 0) { 1 } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: int) = if x > 5 { 1 } else if x > 3 { 2 } else if x > 4 { 3 } \
             else { 4 };\n",
            "int -> 1 | 2 | 4",
        ),
        (
            "f(positional x: int, positional b: bool) = if b && x > 0 && x < 0 { 1 } else \
             { 2 };\n",
            "(int, bool) -> 2",
        ),
        (
            "f(positional x: int) = if x > 0 && x < 0 { 1 } else if x == 3 { 2 } else \
             { 3 };\n",
            "int -> 2 | 3",
        ),
        // `x` is still `int` there, but the branch adds nothing.
        (
            "f(positional x: int) = if x > 0 && x < 0 { x } else { 2 };\n",
            "int -> 2",
        ),
        // A test whose type meets the name's in a type with no value, though each lists
        // values: the tuple types meet in components that do not.
        (
            "f(positional x: (int, int)) = if x is (bool, int) { 1 } else { 2 };\n",
            "((int, int)) -> 2",
        ),
        (
            "f(positional x: int) = if x is (int, int) & (bool, int) { 1 } else { 2 };\n",
            "int -> 2",
        ),
        (
            "f(positional x: ((bool, int), int)) = if x is ((int, int), int) { 1 } else \
             { 2 };\n",
            "(((bool, int), int)) -> 2",
        ),
        // Tests that may both hold keep both branches.
        (
            "f(positional x: int) = if x > 0 && x < 9 { 1 } else { 2 };\n",
            "int -> 1 | 2",
        ),
        // Inside an unreachable branch nothing more is unreachable: it is all unreachable.
        (
            "f(positional x: int) = if x > 0 && x < 0 { if x > 1 { 1 } else { 2 } } else \
             { 3 };\n",
            "int -> 3",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
    // Such a branch is still checked: an error in it is reported.
    let text = "f(positional x: int) = if x > 0 && x < 0 { x + true } else { 2 };\n";
    assert_eq!(
        type_errors(text),
        ["`+` does not take (int, true): no arrow of `+` takes these types. [x + true]"]
    );
}

/// A `bool` tested again on a path where an earlier test already decided it: the branch the
/// second test cannot take is unreachable and adds nothing to the result (DESIGN.md
/// sec:constraints), in a nested `if`, an `else if` chain, an `if` that is a call's argument and
/// one bound to a name. With a second, independent `bool` every branch can be taken, and the
/// result is the union of all three, printed in the fixed order of members (int, then f64,
/// then a type variable, then atoms). The first row is the finding CHK-nested-if-loses-f64
/// reported as a lost branch: in the `else` of `if c`, `c` is false, so `if c { f64(1) }` never
/// gives `f64(1)`.
#[test]
fn a_bool_tested_again_on_its_own_path_takes_one_branch() {
    let h = "h(positional y) = y;\n";
    for (text, want) in [
        (
            "f(positional c, positional x) = if c { int(1) } else { if c { f64(1) } else { x } \
             };\n"
                .to_string(),
            "(bool, T) -> int | T",
        ),
        (
            "f(positional c, positional x) = if c { int(1) } else if c { f64(1) } else { x };\n"
                .to_string(),
            "(bool, T) -> int | T",
        ),
        (
            format!(
                "{h}f(positional c, positional x) = h(if c {{ int(1) }} else {{ if c {{ \
                 f64(1) }} else {{ x }} }});\n"
            ),
            "(bool, T) -> int | T",
        ),
        (
            "f(positional c, positional x) = { y = if c { int(1) } else { if c { f64(1) } else \
             { x } }; y };\n"
                .to_string(),
            "(bool, T) -> int | T",
        ),
        // The same test in the `then` branch: there `c` is true, so the nested `else` is the
        // unreachable branch, and `x` reaches no result.
        (
            "f(positional c, positional x) = if c { if c { f64(1) } else { x } } else { int(1) \
             };\n"
                .to_string(),
            "(bool, _) -> int | f64",
        ),
        // The negated test holds wherever `c` is false.
        (
            "f(positional c, positional x) = if c { int(1) } else { if !c { f64(1) } else { x } \
             };\n"
                .to_string(),
            "(bool, _) -> int | f64",
        ),
        // Three levels: the innermost test of `c` is decided by the outermost.
        (
            "f(positional c, positional d, positional x) = if c { int(1) } else { if d { \
             f64(1) } else { if c { \"s\" } else { x } } };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T",
        ),
        // An independent test can go either way, so every branch is in the result.
        (
            "f(positional c, positional d, positional x) = if c { int(1) } else { if d { \
             f64(1) } else { x } };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T",
        ),
        (
            "f(positional c, positional d, positional x) = if c { int(1) } else if d { f64(1) \
             } else { x };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T",
        ),
        (
            format!(
                "{h}f(positional c, positional d, positional x) = h(if c {{ int(1) }} else {{ \
                 if d {{ f64(1) }} else {{ x }} }});\n"
            ),
            "(bool, bool, T) -> int | f64 | T",
        ),
        (
            "f(positional c, positional d, positional x) = if c { if d { f64(1) } else { x } } \
             else { int(1) };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T",
        ),
        (
            "f(positional c: bool, positional d: bool) = if c { int(1) } else { if d { f64(1) \
             } else { \"s\" } };\n"
                .to_string(),
            "(bool, bool) -> int | f64 | \"s\"",
        ),
        // A cast to a float format gives no atom, of a literal or of an int no test bounds.
        (
            "f(positional c, positional d, positional x, positional n: int) = if c { int(1) } \
             else { if d { f64(n) } else { x } };\n"
                .to_string(),
            "(bool, bool, T, int) -> int | f64 | T",
        ),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        // The members print in the fixed order of a union (DESIGN.md sec:diagnostics): a type
        // variable before the atoms.
        assert_eq!(sig(&text, "f"), want, "{text}");
    }
}

/// An atom whose payload has no value once a generic function's types are put in has no
/// value either: it is `Never`, alone or in a union, as a tuple is.
#[test]
fn an_atom_with_a_payload_of_no_value_after_substitution_is_never() {
    let call = |body: &str| {
        format!(
            "app(positional g, positional x) = {body};\nf(positional h: (int) -> Never) = \
             app(h, 1);\n"
        )
    };
    let bool_call = |body: &str| {
        format!(
            "app(positional g, positional x, positional b: bool) = {body};\nf(positional h: \
             (int) -> Never, positional b: bool) = app(h, 1, b);\n"
        )
    };
    for (text, want) in [
        (call("#a(g(x), 1)"), "(int -> Never) -> Never"),
        (call("#a((g(x), 1), 2)"), "(int -> Never) -> Never"),
        (call("#a(k: g(x))"), "(int -> Never) -> Never"),
        (
            bool_call("if b { #a(g(x)) } else { #a(2) }"),
            "(int -> Never, bool) -> #a(2)",
        ),
        (
            bool_call("if b { #a(g(x)) } else { #b }"),
            "(int -> Never, bool) -> #b",
        ),
        (
            bool_call("if b { #a } else { #a(g(x)) }"),
            "(int -> Never, bool) -> #a",
        ),
        // In a function's result.
        (
            "app(positional g) = (positional x: int) -> #a(g(x), 1);\nf(positional h: (int) -> \
             Never) = app(h);\n"
                .to_string(),
            "(int -> Never) -> int -> Never",
        ),
        // A payload that keeps a value is kept.
        (call("#a(g, x)"), "(int -> Never) -> #a(int -> Never, 1)"),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(&text, "f"), want, "{text}");
    }
}

/// An argument of type `Never` binds the variable of its parameter to `Never`: a need of the
/// generic function on that variable is checked on `Never`, which every use takes. The call
/// gives no value where its substituted result is `Never`, and its arrow's result elsewhere
/// (EMPTY-call-unused). No message names a type the program did not write.
#[test]
fn an_argument_of_type_never_binds_its_variable_to_never() {
    for (text, want) in [
        // The finding: `(x, 1)` needs `x` to hold no function, and `Never` holds none.
        (
            "pair(positional x) = (x, 1);\nf(positional n: Never) = pair(n);\n",
            "Never -> Never",
        ),
        // `Never` in one component of a tuple argument: the tuple is `Never`.
        (
            "pair(positional x) = (x, 1);\nf(positional n: Never) = pair((n, 2));\n",
            "Never -> Never",
        ),
        (
            "pair(positional x) = (x, 1);\nf(positional n: Never) = pair(pair(n));\n",
            "Never -> Never",
        ),
        (
            "sw(positional p) = { a, b = p; (b, a) };\nf(positional n: Never) = sw((n, 2));\n",
            "Never -> Never",
        ),
        // A call of the argument, and a component of it.
        (
            "app(positional g) = g(1);\nf(positional n: Never) = app(n);\n",
            "Never -> Never",
        ),
        (
            "first(positional p) = p[0];\nf(positional n: Never) = first(n);\n",
            "Never -> Never",
        ),
        (
            "ap(positional g, positional y) = g(y);\nf(positional n: Never) = ap(n, 1);\n",
            "Never -> Never",
        ),
        (
            "ap(positional g, positional y) = g(y);\nf(positional h: (int) -> int, positional \
             n: Never) = ap(h, n);\n",
            "(int -> int, Never) -> int",
        ),
        // One argument of no value in a tuple the body builds: the tuple is `Never`.
        (
            "two(positional x, positional y) = (x, y);\nf(positional n: Never) = two(n, 1);\n",
            "Never -> Never",
        ),
        // An argument that has no value only after a call.
        (
            "pair(positional x) = (x, 1);\nf(positional g: (int) -> Never) = pair(g(1));\n",
            "(int -> Never) -> Never",
        ),
        // A parameter with a declared type takes `Never`, which is below every type. The result is
        // the arrow's: the checker does not ask whether the body reads `x` on every path.
        (
            "g(positional x: int) = x + 1;\nf(positional n: Never) = g(n);\n",
            "Never -> int",
        ),
        (
            "g(positional x: (int, String)) = x;\nf(positional n: Never) = g(n);\n",
            "Never -> (int, String)",
        ),
        // `Never` in a union adds nothing: the variable is bound by the rest.
        (
            "pair(positional x) = (x, 1);\nf(positional n: int | Never) = pair(n);\n",
            "int -> (int, 1)",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
}

/// A generic function called with `Never` and with `int` in one program: each call binds its
/// own variable, in either order, and the function's signature is as without the calls.
#[test]
fn calls_with_never_and_with_int_do_not_meet() {
    let alone = "pair(positional x) = (x, 1);\n";
    let never = "f(positional n: Never) = pair(n);\n";
    let int = "h(positional m: int) = pair(m);\n";
    for text in [
        format!("{alone}{never}{int}"),
        format!("{alone}{int}{never}"),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(&text, "f"), "Never -> Never", "{text}");
        assert_eq!(sig(&text, "h"), "int -> (int, 1)", "{text}");
        assert_eq!(sig(&text, "pair"), sig(alone, "pair"), "{text}");
    }
}

/// An argument of type `Never` binds its parameter's variable alike before and after an
/// argument that is a function whose body has needs, `h` here, whose `(x, 1)` needs `x` to
/// hold no function: the need is checked as the parameter's type gives it in either order
/// (the proof at the binding of `Never` in zedc-check walk.rs `apply_one`). With `g` untyped,
/// `g` is a class and `apply_one` takes its class branch, so `Ck::fit_needs` is not reached
/// here (seen by counting its calls, 2026-11-20); the next test reaches it through a written
/// type `(T) -> ...`.
#[test]
fn an_argument_of_type_never_binds_alike_before_or_after_a_function_with_needs() {
    let h = "h(positional x) = (x, 1);\n";
    for text in [
        format!("ap(positional g, positional y) = g(y);\n{h}f(positional n: Never) = ap(h, n);\n"),
        format!("pa(positional y, positional g) = g(y);\n{h}f(positional n: Never) = pa(n, h);\n"),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(&text, "f"), "Never -> Never", "{text}");
    }
}

/// An argument of type `Never` binds its parameter's variable before an argument that is a
/// function whose body has needs is checked on it, in either order: `x(1)`, `x[0]` and `x == 1`
/// hold on `Never`, and `g`'s written type `(T) -> ...` makes the checker test `h` on the binding
/// of `T` (zedc-check walk.rs `Ck::fit_needs`). Before PROOF-never-bind-order-fit-needs the
/// order `ap(h, n)` checked `h` with `T` not yet bound, read as `_`, and rejected the call ("a call
/// of `x` does not take every value, and this value is `_`"), while `pa(n, h)` took it.
#[test]
fn an_argument_of_type_never_binds_before_a_function_with_needs_in_either_order() {
    for (body, ty, result) in [
        ("x(1)", "(T) -> T", "Never"),
        ("x(1)", "(T) -> int", "int"),
        ("x[0]", "(T) -> T", "Never"),
        ("x[0]", "(T) -> bool", "bool"),
        ("x == 1", "(T) -> bool", "bool"),
    ] {
        let h = format!("h(positional x) = {body};\n");
        for text in [
            format!(
                "ap(positional g: {ty}, positional y: T) = g(y);\n{h}f(positional n: Never) = ap(h, n);\n"
            ),
            format!(
                "pa(positional y: T, positional g: {ty}) = g(y);\n{h}f(positional n: Never) = pa(n, h);\n"
            ),
        ] {
            assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
            assert_eq!(sig(&text, "f"), format!("Never -> {result}"), "{text}");
        }
    }
}

/// Negative control of the test above: with an `int` in place of the argument of no value, the
/// needs are checked on `int`, and a need `int` does not meet rejects the call in both orders with
/// one message; a need it meets takes it in both.
#[test]
fn an_int_in_place_of_never_is_checked_alike_in_either_order() {
    for (body, ty, ok) in [
        ("x[0]", "(T) -> int", false),
        ("x(1)", "(T) -> int", false),
        ("x + 1", "(T) -> T", true),
        ("x == 1", "(T) -> bool", true),
    ] {
        let h = format!("h(positional x) = {body};\n");
        let [first, second] = [
            format!("ap(positional g: {ty}, positional y: T) = g(y);\n{h}f(positional n: int) = ap(h, n);\n"),
            format!("pa(positional y: T, positional g: {ty}) = g(y);\n{h}f(positional n: int) = pa(n, h);\n"),
        ]
        .map(|t| (type_errors(&t), t));
        assert_eq!(first.0.is_empty(), ok, "{}: {:?}", first.1, first.0);
        assert_eq!(first.0, second.0, "{}{}", first.1, second.1);
    }
}

/// With a third argument, an `int`, binding the same variable as the argument of no value, the
/// function's needs are checked on `int` in each of the six orders of the three arguments, with
/// one verdict and one message: binding `Never` before the arguments are checked
/// (PROOF-never-bind-order-fit-needs) does not make `h` be checked on `Never` where another
/// argument binds its variable. `x(1)` and `x[0]` are rejected at `int`, `x + 1` is taken.
#[test]
fn a_function_with_needs_is_checked_alike_beside_never_and_an_int_in_every_order() {
    let ps = [("g", "(T) -> T"), ("y", "T"), ("z", "T")];
    let orders = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    for (body, ok) in [("x(1)", false), ("x[0]", false), ("x + 1", true)] {
        let checked = orders.map(|o| {
            let params: Vec<String> = (o.iter())
                .map(|&k| format!("positional {}: {}", ps[k].0, ps[k].1))
                .collect();
            let args: Vec<&str> = o.iter().map(|&k| ["h", "n", "m"][k]).collect();
            let text = format!(
                "tri({}) = g(z);\nh(positional x) = {body};\n\
                 f(positional n: Never, positional m: int) = tri({});\n",
                params.join(", "),
                args.join(", ")
            );
            (type_errors(&text), sig(&text, "f"), text)
        });
        let (errors, sig_f, text) = &checked[0];
        assert_eq!(errors.is_empty(), ok, "{text}: {errors:?}");
        assert_eq!(sig_f, "(Never, int) -> int", "{text}");
        for (e, s, t) in &checked[1..] {
            assert_eq!((e, s), (errors, sig_f), "{text}{t}");
        }
    }
}

/// The orders of `(a0, …)`'s parameters, for the tests of order below: each permutation of
/// `0..n`, `n!` of them.
fn orders(n: usize) -> Vec<Vec<usize>> {
    if n == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for o in orders(n - 1) {
        for k in 0..=o.len() {
            let mut o = o.clone();
            o.insert(k, n - 1);
            out.push(o);
        }
    }
    out
}

/// The text of `f(positional n: Never) = q(…)` with `q`'s parameters `ps` in the order `o` and
/// the arguments `args` in the same order, after the declarations `decls`.
fn ordered(decls: &str, ps: &[(&str, &str)], args: &[&str], o: &[usize]) -> String {
    let params: Vec<String> = (o.iter())
        .map(|&k| format!("positional {}: {}", ps[k].0, ps[k].1))
        .collect();
    let args: Vec<&str> = o.iter().map(|&k| args[k]).collect();
    format!(
        "q({}) = 1;\n{decls}f(positional n: Never) = q({});\n",
        params.join(", "),
        args.join(", ")
    )
}

/// A literal at a parameter that holds `T` beside other types, `T | bool`, is bound to `T` by
/// the loop over the arguments, not before it (`Ck::instantiated` binds a literal only at a
/// parameter that is `T` alone), so the needs of `h` are checked on `T` = `1` whatever the
/// order: `x(1)` and `x[0]` cannot take `1`, and the call is refused in all six orders, with
/// one error. Before PROOF-bind-never-open-cases the needs were checked at `h`'s place in the
/// loop, on the binding of the arguments before it: `q(h, n, 1)`, `q(h, 1, n)` and `q(n, h,
/// 1)` checked `h` on `Never` and took the call, which runs `h(1)` and applies `1`; the other
/// three refused it. A `true` there falls in `bool` and binds nothing, so `h` is checked on
/// `Never` and taken in every order: the negative control.
#[test]
fn a_function_with_needs_is_checked_on_the_binding_of_every_argument_in_every_order() {
    for (other, body, lit, want) in [
        ("T | bool", "x(1)", "1", Some("`x` is 1, not a function")),
        ("T | #a", "x(1)", "1", Some("`x` is 1, not a function")),
        ("T | bool", "x[0]", "1", Some("`[0]` takes a tuple, not 1")),
        ("T | bool", "x(1)", "true", None),
        ("T | bool", "x[0]", "true", None),
    ] {
        let ps = [("g", "(T) -> T"), ("y", "T"), ("z", other)];
        let h = format!("h(positional x) = {body};\n");
        for o in orders(3) {
            let text = ordered(&h, &ps, &["h", "n", lit], &o);
            let errors = type_errors(&text);
            match want {
                Some(w) => assert!(
                    errors.len() == 1 && errors[0].starts_with(w),
                    "{text}: {errors:?}"
                ),
                None => assert_eq!(errors, Vec::<String>::new(), "{text}"),
            }
            assert_eq!(sig(&text, "f"), "Never -> 1", "{text}");
        }
    }
}

/// Two functions with needs, an argument of no value and a literal that binds the same
/// variable, in all 24 orders: one verdict, the same number of errors, and one type of `f`.
/// The needs of both are checked after the loop on the binding all four give; a call the loop
/// refuses (a bounded `x + 1` does not fit `(T) -> T` by itself) reports that refusal alone. Before
/// PROOF-bind-never-open-cases a function before the refused argument had its needs checked
/// on the binding so far, adding an error that hung on the order (`x` is 1, `_`, or none).
#[test]
fn two_functions_with_needs_are_checked_alike_in_every_order() {
    let ps = [
        ("g", "(T) -> T"),
        ("k", "(T) -> T"),
        ("y", "T"),
        ("z", "T | bool"),
    ];
    // A call refused by the loop is of type `Never`; one whose needs wrote their own errors is
    // taken, of `q`'s result `1`.
    for (b1, b2, lit, count, result) in [
        ("x(1)", "x[0]", "1", 2, "1"),
        ("x(1)", "x + 1", "1", 1, "Never"),
        ("x + 1", "x(1)", "1", 1, "Never"),
        ("x(1)", "x", "true", 0, "1"),
    ] {
        let decls = format!("h1(positional x) = {b1};\nh2(positional x) = {b2};\n");
        for o in orders(4) {
            let text = ordered(&decls, &ps, &["h1", "h2", "n", lit], &o);
            let errors = type_errors(&text);
            assert_eq!(errors.len(), count, "{text}: {errors:?}");
            assert_eq!(sig(&text, "f"), format!("Never -> {result}"), "{text}");
        }
    }
}

/// Evaluation is neither strict nor lazy, so an argument of type `Never` leaves a call of a
/// declared function without a value only where the substituted body needs it: the call's type
/// is the substituted result, with no rule that any argument of no value makes it `Never`
/// (EMPTY-call-unused).
#[test]
fn a_call_with_an_argument_of_no_value_has_its_substituted_result() {
    let k = "k(positional x, positional y) = y;\n";
    let sel = "sel(positional b: bool, positional x, positional y) = if b { x } else { y };\n";
    for (text, want) in [
        // An unused argument: the result is the other argument's.
        (
            format!("{k}f(positional n: Never) = k(n, 1);\n"),
            "Never -> 1",
        ),
        (
            format!("{k}f(positional n: Never) = k(n, #a);\n"),
            "Never -> #a",
        ),
        (
            format!("{k}f(positional n: Never) = n.k(1);\n"),
            "Never -> 1",
        ),
        (
            "c(positional x: int) = 7;\nf(positional n: Never) = c(n);\n".to_string(),
            "Never -> 7",
        ),
        // Used on one branch only: that branch adds nothing.
        (
            format!("{sel}f(positional b: bool, positional n: Never) = sel(b, n, 1);\n"),
            "(bool, Never) -> 1",
        ),
        // Used on every path: the result is `Never`.
        (
            format!("{k}f(positional n: Never) = k(1, n);\n"),
            "Never -> Never",
        ),
        (
            format!("{sel}f(positional b: bool, positional n: Never) = sel(b, n, n);\n"),
            "(bool, Never) -> Never",
        ),
        // Nested calls: each call has its own substituted result.
        (
            format!("{k}f(positional n: Never) = k(k(n, 1), 2);\n"),
            "Never -> 2",
        ),
        (
            format!("{k}f(positional n: Never) = k(1, k(2, n));\n"),
            "Never -> Never",
        ),
        (
            format!("{k}f(positional n: Never) = 1 + k(n, 2);\n"),
            "Never -> int",
        ),
        (
            format!("{k}pair(positional x) = (x, 1);\nf(positional n: Never) = pair(k(n, 3));\n"),
            "Never -> (3, 1)",
        ),
        (
            format!("{k}f(positional n: Never) = {{ z = k(n, 1); z + 1 }};\n"),
            "Never -> int",
        ),
        // `inc` is `(T) -> T for T in …` (bare literals are generic), so its result names the
        // parameter's variable `T`, which the argument binds to `Never`: the call is `Never`.
        (
            "inc(positional x) = x + 1;\nf(positional n: Never) = inc(n);\n".to_string(),
            "Never -> Never",
        ),
        // Used on every path but with a result that does not name `x`: the arrow's result
        // `bool`. Sound, as `Never` is below `bool`; finding `Never` here needs a demand analysis.
        (
            "pos(positional x) = x > 0;\nf(positional n: Never) = pos(n);\n".to_string(),
            "Never -> bool",
        ),
        // An operator needs every operand; `&&` needs only the first.
        (
            "f(positional n: Never) = n + 1;\n".to_string(),
            "Never -> Never",
        ),
        (
            "f(positional b: bool, positional n: Never) = b && n;\n".to_string(),
            "(bool, Never) -> bool",
        ),
        (
            "f(positional b: bool, positional n: Never) = b || n;\n".to_string(),
            "(bool, Never) -> bool",
        ),
        (
            "f(positional b: bool, positional n: Never) = n && b;\n".to_string(),
            "(bool, Never) -> Never",
        ),
        // A call through an argument function with several arrows.
        (
            "f(positional h: ((int) -> int) & ((bool) -> bool), positional n: Never) = h(n);\n"
                .to_string(),
            "((int -> int) & (bool -> bool), Never) -> int",
        ),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(&text, "f"), want, "{text}");
    }
}

/// The visible effect of the old rule, which typed `k(h(1), 1)` as `Never`: the branch that
/// returns 1 was dropped from the result, and a call that passes `"s"` on to an `int` parameter
/// was accepted.
#[test]
fn a_call_that_does_not_read_an_argument_of_no_value_keeps_its_value() {
    let k = "k(positional x, positional y) = y;\n";
    let text = format!(
        "{k}f(positional h: (int) -> Never, positional b: bool) = if b {{ k(h(1), 1) }} else {{ 2 }};\n"
    );
    assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    assert_eq!(sig(&text, "f"), "(int -> Never, bool) -> 1 | 2", "{text}");
    let text = format!(
        "{k}take(positional x: int) = x;\nf(positional h: (int) -> Never) = take(k(h(1), \"s\"));\n"
    );
    let errors = type_errors(&text);
    assert_eq!(errors.len(), 1, "{text}: {errors:?}");
    assert!(
        errors[0].starts_with("`take` does not take (\"s\")"),
        "{text}: {errors:?}"
    );
}

/// The rejection of the call that passes `"s"` through `k` to `take` shows where `k` is declared
/// with the type the checker found, saying that none was written: `(_, T) -> T` shows that `y`
/// and the result have the same type at each call, which `(_, _) -> _` did not
/// (MSG-declared-inferred-sig, UNDERSCORE-print).
#[test]
fn the_rejection_of_a_value_passed_on_past_an_argument_of_no_value_shows_where_it_goes() {
    let text = "k(positional x, positional y) = y;\ntake(positional x: int) = x;\n\
                f(positional h: (int) -> Never) = take(k(h(1), \"s\"));\n";
    let (info, _) = info(text);
    assert_eq!(info.errors.len(), 1, "{text}");
    let notes: Vec<&str> = info.errors[0].notes.iter().map(|n| &*n.text).collect();
    assert!(
        notes.contains(
            &"`k` is declared here with no type written for `x`, `y` or its result; the type the \
              checker found for `k` is `(_, T) -> T`"
        ),
        "{notes:?}"
    );
    assert!(
        notes.contains(
            &"`take` is declared here with no type written for its result; the type the checker \
              found for `take` is `int -> int`"
        ),
        "{notes:?}"
    );
}

/// A call of `n` functions with needs, each beside an argument of no value, and a `true` at
/// `T | bool`, all at parameters of one variable `T`: the loop keeps each function in `held`
/// and checks its needs after the loop, on `T` = `Never`.
pub(super) fn functions_beside_never(n: usize) -> String {
    let ps: String = (0..n)
        .map(|i| format!("positional g{i}: (T) -> T, positional y{i}: T, "))
        .collect();
    let args: String = (0..n).map(|_| "h, n, ").collect();
    format!(
        "q({ps}positional z: T | bool) = 1;\nh(positional x) = x(1);\n\
         f(positional n: Never) = q({args}true);\n"
    )
}

/// A small instance of the benchmark
/// `bench::never::functions_with_needs_beside_never_scale`: taken, of `q`'s result.
#[test]
fn functions_with_needs_beside_never_are_taken() {
    let text = functions_beside_never(3);
    assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    assert_eq!(sig(&text, "f"), "Never -> 1", "{text}");
}

/// `g` maps a function reading `.x` over a list of lambdas nested two deep, with no function
/// `x` in scope: `p(1)` is a list, `0 -> 0 -> (1, int)`.
fn nested_lambdas(x: &str) -> String {
    format!(
        "{x}h0(positional f, positional m) = m.map(f);\n\
         h1(positional f, positional m) = m.map(f);\n\
         g(positional a, positional b, positional c, positional d) = \
         (h0(p -> p(1).x, [(x -> h1(z -> [z], [(x, d)]))]), a, b, c, d + 1);\n"
    )
}

/// Row FAIL-never-return-nested-lambda-unchecked. With no function `x` in scope, `p(1).x`
/// reads a field of a list, which has none; elaboration refuses it, and the checker gives the
/// read no value, `Never`, so that no use of it reports that error again (zedc-check
/// `Ck::member_end`, at its last arm). The checker alone, as `type_errors` and `sig` run it, so
/// reports nothing and gives `g` the result `(0 -> Never, …)`: that is the type of the
/// refused read, and the program is refused all the same, by elaboration. The control with
/// `x` in scope is taken, of type `0 -> 7`, and the one whose `x` needs an `int` is refused by
/// the checker alone at the nested lambdas: their needs are checked.
#[test]
fn a_field_read_refused_in_nested_lambdas_gives_never_and_is_reported() {
    let text = nested_lambdas("");
    assert_eq!(type_errors(&text), Vec::<String>::new());
    assert_eq!(
        sig(&text, "g"),
        "(T, U, V, W) -> (0 -> Never, T, U, V, W) for W in int | f32 | f64 | rat"
    );
    assert_eq!(
        zed_tests::step_helpers::l01_16_elaboration::errors(&text),
        vec![
            "`x` is not a function in scope, and reading a field with `.x` is part of the Zed \
             language but is not supported by this version of zedc. Call a function in scope, or \
             correct the name if it is misspelled. [p(1).x]"
        ]
    );
    let with_x = nested_lambdas("x(positional v) = 7;\n");
    assert_eq!(type_errors(&with_x), Vec::<String>::new());
    assert_eq!(
        sig(&with_x, "g"),
        "(T, U, V, W) -> (0 -> 7, T, U, V, W) for W in int | f32 | f64 | rat"
    );
    assert!(zed_tests::step_helpers::l01_16_elaboration::elab(&with_x).is_ok());
    let int_x = nested_lambdas("x(positional v: int) = 7;\n");
    assert_eq!(
        type_errors(&int_x),
        vec![
            "the function given to `map` gives 0 -> 0 -> (1, _) here, which is not int: the use \
             requires a value of int. [h0(p -> p(1).x, [(x -> h1(z -> [z], [(x, d)]))])]"
        ]
    );
}

/// A call whose argument holds only values another part of its parameter takes, as `#nf` at
/// `x` of `r`, whose type is `$0 | #nf | #nf(..)` once `x else #nf -> 0` reads it: the
/// variable gets no value, `Never`, and its needs are met on `Never`. Before
/// MSG-takes-all-value-underscore it was left unbound, its need `Narrow(#nf)` was checked on
/// the unknown, and `r(#nf)` was refused ("this value is `_`").
#[test]
fn an_atom_alone_at_a_generic_parameter_meets_its_needs() {
    let r = "r(positional x) = if (x else #nf -> 0) == 0 { x } else { x + 1 };\n";
    for call in [
        "c = r(#nf);\n",
        "f(positional y: #nf) = r(y);\n",
        "a = r(3);\nc = r(#nf);\n",
        "c = r(#nf);\na = r(3);\n",
    ] {
        let text = format!("{r}{call}");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
    let text = format!("{r}f(positional y: #nf) = r(y);\n");
    assert_eq!(sig(&text, "f"), "#nf -> #nf | #nf(..)", "{text}");
    // Negative control: a value no part of `x` takes is still refused.
    let text = format!("{r}c = r(\"s\");\n");
    assert_ne!(type_errors(&text), Vec::<String>::new(), "{text}");
}
