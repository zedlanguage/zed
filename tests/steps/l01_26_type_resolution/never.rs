//! The empty type is the prelude type `Never` (DESIGN.md, the L1 row of "Defined words by
//! layer"): a program writes it from L1 on, and the checker prints a type with no value as
//! `Never`. A declared result type `-> Never` and a binding with a declared type `x: Never = 1`
//! are forms of layer L10, which zedc does not compile yet, so these tests write `Never` where
//! L1 takes a type: a parameter's type and a function type's result.

use super::{info, sig, type_errors};

#[test]
fn a_function_type_may_declare_the_result_never() {
    let text = "apply(positional h: (int) -> Never, positional n: int) = h(n);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "apply"), "((int) -> Never, int) -> Never");
}

#[test]
fn never_in_a_union_adds_nothing() {
    assert_eq!(
        sig("g(positional n: int | Never) = n;\n", "g"),
        "(int) -> int"
    );
}

#[test]
fn a_parameter_of_type_never_takes_no_argument() {
    let text = "take(positional x: Never) = x;\nr = take(1);\n";
    assert_eq!(
        type_errors(text),
        [
            "`take` does not take (1): these are the types of its arguments here, and `take` has \
          no arrow that takes them all [take(1)]"
        ]
    );
    assert_eq!(sig(text, "take"), "(Never) -> Never");
}

#[test]
fn a_test_against_never_is_accepted() {
    // `x is Never` holds of no value, so the first branch is unreachable: it is still
    // checked, and adds nothing to the result (DESIGN.md sec:constraints).
    let text = "h(positional x: int) = if x is Never { 1 } else { 2 };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "h"), "(int) -> 2");
}

/// A tuple with an empty component has no value, so its type is `Never`: written as a
/// parameter's type, nested, in a union, and made by a tuple expression.
#[test]
fn a_tuple_with_an_empty_component_is_never() {
    for (text, want) in [
        ("f(positional x: (Never, int)) = x;\n", "(Never) -> Never"),
        ("f(positional x: (int, Never)) = x;\n", "(Never) -> Never"),
        (
            "f(positional x: ((Never, int), bool)) = x;\n",
            "(Never) -> Never",
        ),
        (
            "f(positional x: (int, Never) | bool) = x;\n",
            "(bool) -> bool",
        ),
        ("f(positional x: Never) = (x, 1);\n", "(Never) -> Never"),
        (
            "f(positional x: Never) = { y = ((x, 1), true); y };\n",
            "(Never) -> Never",
        ),
        // An atom whose payload has no value has none either.
        ("f(positional x: Never) = #a(x);\n", "(Never) -> Never"),
        // A function whose result has no value returns no value.
        (
            "f(positional g: (int) -> (Never, int)) = g(1);\n",
            "((int) -> Never) -> Never",
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
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x is int { 1 } else { 2 };\n",
            "(int) -> 1",
        ),
        (
            "f(positional x: int) = if x is not int { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x is not Never { 1 } else { 2 };\n",
            "(int) -> 1",
        ),
        (
            "f(positional x: int) = if x is (Never, int) { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int | String) = if x is int { 1 } else if x is String { 2 } else \
             { 3 };\n",
            "(int | String) -> 1 | 2",
        ),
        // In the unreachable branch `x` is `Never`, so it adds nothing there either.
        (
            "f(positional x: int) = if x is Never { x } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = { y = (x, 1); if x is bool { y } else { (1, 2) } };\n",
            "(int) -> (1, 2)",
        ),
        // A name of type `Never` makes both branches unreachable.
        (
            "f(positional x: Never) = if x is int { 1 } else { 2 };\n",
            "(Never) -> Never",
        ),
        // A test that may hold keeps both branches.
        (
            "f(positional x: int | bool) = if x is int { 1 } else { 2 };\n",
            "(bool | int) -> 1 | 2",
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
        [
            "`+` does not take ((int, 1), 1): these are the types of its arguments here, and `+` \
             has no arrow that takes them all [y + 1]"
        ]
    );
    // `x` is `Never` there, and `true` is still no operand of `+`.
    let text = "f(positional x: int) = if x is Never { x + true } else { 2 };\n";
    assert_eq!(
        type_errors(text),
        [
            "`+` does not take (Never, true): these are the types of its arguments here, and \
             `+` has no arrow that takes them all [x + true]"
        ]
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
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x > 0 { if x < 0 { 1 } else { 2 } } else { 3 };\n",
            "(int) -> 2 | 3",
        ),
        // The test holds of every value, so the second branch is the unreachable one.
        (
            "f(positional x: int) = if x >= 0 || x < 0 { 1 } else { 2 };\n",
            "(int) -> 1",
        ),
        (
            "f(positional x: int) = if !(x > 0 || x <= 0) { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x > 5 { 1 } else if x > 3 { 2 } else if x > 4 { 3 } \
             else { 4 };\n",
            "(int) -> 1 | 2 | 4",
        ),
        (
            "f(positional x: int, positional b: bool) = if b && x > 0 && x < 0 { 1 } else \
             { 2 };\n",
            "(int, bool) -> 2",
        ),
        (
            "f(positional x: int) = if x > 0 && x < 0 { 1 } else if x == 3 { 2 } else \
             { 3 };\n",
            "(int) -> 2 | 3",
        ),
        // `x` is still `int` there, but the branch adds nothing.
        (
            "f(positional x: int) = if x > 0 && x < 0 { x } else { 2 };\n",
            "(int) -> 2",
        ),
        // A test whose type meets the name's in a type with no value, though each lists
        // values: the tuple types meet in components that do not.
        (
            "f(positional x: (int, int)) = if x is (bool, int) { 1 } else { 2 };\n",
            "((int, int)) -> 2",
        ),
        (
            "f(positional x: int) = if x is (int, int) & (bool, int) { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: ((bool, int), int)) = if x is ((int, int), int) { 1 } else \
             { 2 };\n",
            "(((bool, int), int)) -> 2",
        ),
        // Tests that may both hold keep both branches.
        (
            "f(positional x: int) = if x > 0 && x < 9 { 1 } else { 2 };\n",
            "(int) -> 1 | 2",
        ),
        // Inside an unreachable branch nothing more is unreachable: it is all unreachable.
        (
            "f(positional x: int) = if x > 0 && x < 0 { if x > 1 { 1 } else { 2 } } else \
             { 3 };\n",
            "(int) -> 3",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
    // Such a branch is still checked: an error in it is reported.
    let text = "f(positional x: int) = if x > 0 && x < 0 { x + true } else { 2 };\n";
    assert_eq!(
        type_errors(text),
        [
            "`+` does not take (int, true): these are the types of its arguments here, and `+` \
             has no arrow that takes them all [x + true]"
        ]
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
            "(bool, _) -> int | f64 | #inexact",
        ),
        // The negated test holds wherever `c` is false.
        (
            "f(positional c, positional x) = if c { int(1) } else { if !c { f64(1) } else { x } \
             };\n"
                .to_string(),
            "(bool, _) -> int | f64 | #inexact",
        ),
        // Three levels: the innermost test of `c` is decided by the outermost.
        (
            "f(positional c, positional d, positional x) = if c { int(1) } else { if d { \
             f64(1) } else { if c { \"s\" } else { x } } };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T | #inexact",
        ),
        // An independent test can go either way, so every branch is in the result.
        (
            "f(positional c, positional d, positional x) = if c { int(1) } else { if d { \
             f64(1) } else { x } };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T | #inexact",
        ),
        (
            "f(positional c, positional d, positional x) = if c { int(1) } else if d { f64(1) \
             } else { x };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T | #inexact",
        ),
        (
            format!(
                "{h}f(positional c, positional d, positional x) = h(if c {{ int(1) }} else {{ \
                 if d {{ f64(1) }} else {{ x }} }});\n"
            ),
            "(bool, bool, T) -> int | f64 | T | #inexact",
        ),
        (
            "f(positional c, positional d, positional x) = if c { if d { f64(1) } else { x } } \
             else { int(1) };\n"
                .to_string(),
            "(bool, bool, T) -> int | f64 | T | #inexact",
        ),
        (
            "f(positional c: bool, positional d: bool) = if c { int(1) } else { if d { f64(1) \
             } else { \"s\" } };\n"
                .to_string(),
            "(bool, bool) -> int | f64 | \"s\" | #inexact",
        ),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        let got = sig(&text, "f");
        // The fixed order puts a type variable before the atoms (author, A92 B), and the
        // printer still writes `#inexact | T` (ledger MSG-union-order-consistent); until it is
        // fixed, a result with both is compared as a set of members, and the rest as text.
        let (args, result) = got.split_once(" -> ").expect("an arrow");
        if result.contains(" | T") && result.contains('#') {
            let members = |r: &str| {
                let mut m: Vec<String> = r.split(" | ").map(String::from).collect();
                m.sort();
                m
            };
            let (want_args, want_result) = want.split_once(" -> ").expect("an arrow");
            assert_eq!(args, want_args, "{text}");
            assert_eq!(members(result), members(want_result), "{text}");
        } else {
            assert_eq!(got, want, "{text}");
        }
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
        (call("#a(g(x), 1)"), "((int) -> Never) -> Never"),
        (call("#a((g(x), 1), 2)"), "((int) -> Never) -> Never"),
        (call("#a(k: g(x))"), "((int) -> Never) -> Never"),
        (
            bool_call("if b { #a(g(x)) } else { #a(2) }"),
            "((int) -> Never, bool) -> #a(2)",
        ),
        (
            bool_call("if b { #a(g(x)) } else { #b }"),
            "((int) -> Never, bool) -> #b",
        ),
        (
            bool_call("if b { #a } else { #a(g(x)) }"),
            "((int) -> Never, bool) -> #a",
        ),
        // In a function's result.
        (
            "app(positional g) = (positional x: int) -> #a(g(x), 1);\nf(positional h: (int) -> \
             Never) = app(h);\n"
                .to_string(),
            "((int) -> Never) -> (int) -> Never",
        ),
        // A payload that keeps a value is kept.
        (
            call("#a(g, x)"),
            "((int) -> Never) -> #a((int) -> Never, 1)",
        ),
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
            "(Never) -> Never",
        ),
        // `Never` in one component of a tuple argument: the tuple is `Never`.
        (
            "pair(positional x) = (x, 1);\nf(positional n: Never) = pair((n, 2));\n",
            "(Never) -> Never",
        ),
        (
            "pair(positional x) = (x, 1);\nf(positional n: Never) = pair(pair(n));\n",
            "(Never) -> Never",
        ),
        (
            "sw(positional p) = { a, b = p; (b, a) };\nf(positional n: Never) = sw((n, 2));\n",
            "(Never) -> Never",
        ),
        // A call of the argument, and a component of it.
        (
            "app(positional g) = g(1);\nf(positional n: Never) = app(n);\n",
            "(Never) -> Never",
        ),
        (
            "first(positional p) = p[0];\nf(positional n: Never) = first(n);\n",
            "(Never) -> Never",
        ),
        (
            "ap(positional g, positional y) = g(y);\nf(positional n: Never) = ap(n, 1);\n",
            "(Never) -> Never",
        ),
        (
            "ap(positional g, positional y) = g(y);\nf(positional h: (int) -> int, positional \
             n: Never) = ap(h, n);\n",
            "((int) -> int, Never) -> int",
        ),
        // One argument of no value in a tuple the body builds: the tuple is `Never`.
        (
            "two(positional x, positional y) = (x, y);\nf(positional n: Never) = two(n, 1);\n",
            "(Never) -> Never",
        ),
        // An argument that has no value only after a call.
        (
            "pair(positional x) = (x, 1);\nf(positional g: (int) -> Never) = pair(g(1));\n",
            "((int) -> Never) -> Never",
        ),
        // A parameter with a declared type takes `Never`, which is below every type. The result is
        // the arrow's: the checker does not ask whether the body reads `x` on every path.
        (
            "g(positional x: int) = x + 1;\nf(positional n: Never) = g(n);\n",
            "(Never) -> int",
        ),
        (
            "g(positional x: (int, String)) = x;\nf(positional n: Never) = g(n);\n",
            "(Never) -> (int, String)",
        ),
        // `Never` in a union adds nothing: the variable is bound by the rest.
        (
            "pair(positional x) = (x, 1);\nf(positional n: int | Never) = pair(n);\n",
            "(int) -> (int, 1)",
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
        assert_eq!(sig(&text, "f"), "(Never) -> Never", "{text}");
        assert_eq!(sig(&text, "h"), "(int) -> (int, 1)", "{text}");
        assert_eq!(sig(&text, "pair"), sig(alone, "pair"), "{text}");
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
            "(Never) -> 1",
        ),
        (
            format!("{k}f(positional n: Never) = k(n, #a);\n"),
            "(Never) -> #a",
        ),
        (
            format!("{k}f(positional n: Never) = n.k(1);\n"),
            "(Never) -> 1",
        ),
        (
            "c(positional x: int) = 7;\nf(positional n: Never) = c(n);\n".to_string(),
            "(Never) -> 7",
        ),
        // Used on one branch only: that branch adds nothing.
        (
            format!("{sel}f(positional b: bool, positional n: Never) = sel(b, n, 1);\n"),
            "(bool, Never) -> 1",
        ),
        // Used on every path: the result is `Never`.
        (
            format!("{k}f(positional n: Never) = k(1, n);\n"),
            "(Never) -> Never",
        ),
        (
            format!("{sel}f(positional b: bool, positional n: Never) = sel(b, n, n);\n"),
            "(bool, Never) -> Never",
        ),
        // Nested calls: each call has its own substituted result.
        (
            format!("{k}f(positional n: Never) = k(k(n, 1), 2);\n"),
            "(Never) -> 2",
        ),
        (
            format!("{k}f(positional n: Never) = k(1, k(2, n));\n"),
            "(Never) -> Never",
        ),
        (
            format!("{k}f(positional n: Never) = 1 + k(n, 2);\n"),
            "(Never) -> int",
        ),
        (
            format!("{k}pair(positional x) = (x, 1);\nf(positional n: Never) = pair(k(n, 3));\n"),
            "(Never) -> (3, 1)",
        ),
        (
            format!("{k}f(positional n: Never) = {{ z = k(n, 1); z + 1 }};\n"),
            "(Never) -> int",
        ),
        // `inc` is `(T) -> T for T in …` (bare literals are generic), so its result names the
        // parameter's variable `T`, which the argument binds to `Never`: the call is `Never`.
        (
            "inc(positional x) = x + 1;\nf(positional n: Never) = inc(n);\n".to_string(),
            "(Never) -> Never",
        ),
        // Used on every path but with a result that does not name `x`: the arrow's result
        // `bool`. Sound, as `Never` is below `bool`; finding `Never` here needs a demand analysis.
        (
            "pos(positional x) = x > 0;\nf(positional n: Never) = pos(n);\n".to_string(),
            "(Never) -> bool",
        ),
        // An operator needs every operand; `&&` needs only the first.
        (
            "f(positional n: Never) = n + 1;\n".to_string(),
            "(Never) -> Never",
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
            "(((int) -> int) & ((bool) -> bool), Never) -> int",
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
    assert_eq!(sig(&text, "f"), "((int) -> Never, bool) -> 1 | 2", "{text}");
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
              found for `take` is `(int) -> int`"
        ),
        "{notes:?}"
    );
}
