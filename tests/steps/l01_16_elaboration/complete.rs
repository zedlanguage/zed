//! The cases COMPLETENESS.md lists that the other files of this group leave out: each form of
//! the L1 surface that step L1.16 elaborates, with its value under the interpreter, and each
//! error elaboration reports for a form, at each place the form can stand.

use super::{errors, term, value};

/// The value of `x` in `text`, for each `(text, value)` of `cases`.
fn values(cases: &[(&str, &str)]) {
    for (text, want) in cases {
        assert_eq!(value(text, "x"), *want, "{text}");
    }
}

/// The one error of `text`.
fn one(text: &str) -> String {
    let e = errors(text);
    assert_eq!(e.len(), 1, "{text}: {e:?}");
    e.into_iter().next().unwrap()
}

#[test]
fn each_binary_operator_elaborates_to_its_primitive_and_computes() {
    // DESIGN.md L1.16: `++` is its own primitive and `^` a power primitive; L1.18: `div` and
    // `mod` are Euclidean, so the remainder is never negative, whatever the signs.
    values(&[
        ("x = \"a\" ++ \"b\";", "\"ab\""),
        ("x = 1 != 2;", "true"),
        ("x = 1 == 2;", "false"),
        ("x = 3 < 2;", "false"),
        ("x = 3 <= 3;", "true"),
        ("x = 3 > 2;", "true"),
        ("x = 3 >= 4;", "false"),
        ("x = 7 div 2;", "3"),
        ("x = 7 mod 2;", "1"),
        ("x = 7 div -2;", "-3"),
        ("x = 7 mod -2;", "1"),
        ("x = -7 div -2;", "4"),
        ("x = -7 mod -2;", "1"),
        ("x = -(3);", "-3"),
        ("x = !true;", "false"),
        ("x = (-2) ^ 3;", "-8"),
        ("x = 2 ^ 0;", "1"),
        ("x = 0 ^ 0;", "1"),
    ]);
    assert_eq!(term("x = \"a\" ++ \"b\";", "x"), "(\"a\" ++ \"b\")");
    assert_eq!(term("x = 2 ^ 3;", "x"), "(2^3)");
}

#[test]
fn precedence_and_associativity_shape_the_term() {
    // `*` binds tighter than `+` and `-`, which group to the left; `^` binds tighter than `*`
    // and than a prefix `-`, so `-2 ^ 2` is `-(2 ^ 2)`.
    let cases = [
        ("x = 1 + 2 * 3 - 4;", "((1 + (2 * 3)) - 4)", "3"),
        ("x = 10 - 3 - 2;", "((10 - 3) - 2)", "5"),
        ("x = 2 * 3 ^ 2;", "(2 * (3^2))", "18"),
        ("x = -2 ^ 2;", "-(2^2)", "-4"),
        ("x = -(1 + 2) * 3;", "(-(1 + 2) * 3)", "-9"),
    ];
    for (text, shape, v) in cases {
        assert_eq!(term(text, "x"), shape, "{text}");
        assert_eq!(value(text, "x"), v, "{text}");
    }
    // `&&` and `||` nest as `if` forms, `&&` inside `||`.
    let text = "x = 1 < 2 && 2 < 3 || false;";
    assert_eq!(
        term(text, "x"),
        "if if (1 < 2) { (2 < 3) } else { false } { true } else { false }"
    );
    assert_eq!(value(text, "x"), "true");
}

#[test]
fn integers_widen_past_a_machine_word_in_every_operation() {
    // DESIGN.md L1.17: an integer is one word while it fits and a big integer beyond, so
    // arithmetic widens instead of failing.
    values(&[
        ("x = 9223372036854775807 + 1;", "9223372036854775808"),
        ("x = -9223372036854775807 - 2;", "-9223372036854775809"),
        ("x = 9223372036854775807 * 2;", "18446744073709551614"),
        ("x = -(-9223372036854775807 - 1);", "9223372036854775808"),
        (
            "x = (-9223372036854775807 - 1) * -1;",
            "9223372036854775808",
        ),
        ("x = abs(-9223372036854775807 - 1);", "9223372036854775808"),
        ("x = 2 ^ 64;", "18446744073709551616"),
        // A big result that comes back into a word is the small integer again.
        ("x = (2 ^ 64) - (2 ^ 64) + 1;", "1"),
    ]);
}

#[test]
fn an_int_power_with_a_negative_exponent_and_a_division_by_the_literal_zero_are_rejected() {
    // DESIGN.md L1.17: `x^n` on an integer requires `n : int[0..]`; a `rat` base takes any
    // `int` exponent.
    assert!(
        one("x = 2 ^ -1;").starts_with("Int power with a negative exponent: `2 : int ^ -1 : int`."),
    );
    assert_eq!(value("x = 2r ^ -2;", "x"), "1r/4r");
    assert_eq!(
        one("x = 1 div 0;"),
        "`div` here always fails with `#divByZero`: its divisor is the literal 0, so no value \
         that reaches it gives an int. [1 div 0]"
    );
}

#[test]
fn comparisons_take_one_kind_on_both_sides() {
    // DESIGN.md L1.17 and sec:order: strings by code point, a proper prefix first; tuples
    // component by component; `==` and `!=` compare atoms as data; `<` of two atoms passes
    // them through, merged.
    values(&[
        ("x = \"a\" < \"b\";", "true"),
        ("x = \"b\" > \"ab\";", "true"),
        ("x = \"é\" > \"z\";", "true"),
        ("x = \"a\" == \"a\";", "true"),
        ("x = (1, 2) == (1, 2);", "true"),
        ("x = (1, 2) < (1, 3);", "true"),
        ("x = (1, \"a\") < (1, \"b\");", "true"),
        ("x = #a == #a;", "true"),
        ("x = #a == #b;", "false"),
        ("x = #a != #a(1);", "true"),
        ("x = #a < #b;", "#errs({#a, #b})"),
    ]);
    assert!(
        one("x = \"a\" < 1;")
            .starts_with("`<` does not take (\"a\", 1): no arrow of `<` takes these types."),
    );
    assert_eq!(
        one("x = (1, 2) < (1, \"b\");"),
        "Cannot compare unequal types: component `[1]` of the left operand (`2`) with \
         component `[1]` of the right operand (`\"b\"`) in `(1, 2) < (1, \"b\")`. \
         [(1, 2) < (1, \"b\")]"
    );
    assert!(one("x = (1, 2) == (1, 2, 3);").starts_with(
        "No value is both `(int, int)` and `(int, int, int)`: the left operand compared by `==` \
         with the right operand is always `false`."
    ));
}

#[test]
fn concatenation_and_addition_take_their_own_operand_types() {
    assert_eq!(
        one("x = 1 ++ 2;"),
        "`++` does not take (1, 2): no arrow of `++` takes these types. [1 ++ 2]"
    );
    assert_eq!(
        one("x = \"a\" ++ 1;"),
        "`++` does not take (\"a\", 1): no arrow of `++` takes these types. [\"a\" ++ 1]"
    );
    assert_eq!(
        one("x = \"a\" + \"b\";"),
        "`+` does not take (\"a\", \"b\"): no arrow of `+` takes these types. [\"a\" + \"b\"]"
    );
    values(&[("x = \"\";", "\"\""), ("x = \"a\" ++ \"\";", "\"a\"")]);
}

#[test]
fn interpolation_shows_each_hole_and_passes_an_atom_through() {
    values(&[
        ("x = \"${1}${2}\";", "\"12\""),
        ("x = \"${\"a\"}\";", "\"a\""),
        ("x = \"${(1, 2)}\";", "\"(1, 2)\""),
        (
            "n = \"z\"; x = \"n is ${n} and ${n ++ n}\";",
            "\"n is z and zz\"",
        ),
        // DESIGN.md L1.18: an atom passes through every operation but `==` and `!=`.
        ("x = \"${#a}\";", "#a"),
    ]);
    assert_eq!(term("x = \"${1}${2}\";", "x"), "(String(1) ++ String(2))");
    // DESIGN.md L1.17: interpolation shows data, so a function is a type error there.
    assert_eq!(
        one("x = \"${f}\"; f(positional n) = n;"),
        "interpolation takes data, and this value may hold a function, `T -> T`: data is a \
         value that holds no function at any depth. [f]"
    );
}

#[test]
fn blocks_nest_and_each_binder_gets_its_own_kernel_name() {
    let text = "x = { a = 1; b = { a = 2; a }; a + b };";
    assert_eq!(
        term(text, "x"),
        "{ a@1 = 1; b = { a@2 = 2; a@2 }; (a@1 + b) }"
    );
    assert_eq!(value(text, "x"), "3");
    let text = "a = 1; x = { a = 2; a } + a;";
    assert_eq!(term(text, "x"), "({ a@2 = 2; a@2 } + a@1)");
    assert_eq!(value(text, "x"), "3");
    // `_` binds nothing, so it needs no name.
    values(&[("_ = 1; x = 2;", "2"), ("x = { y = 1; y + 1 };", "2")]);
}

#[test]
fn if_elaborates_each_branch_and_an_atom_condition_passes_through() {
    let text = "x = if 1 > 2 { \"a\" } else if 2 > 3 { \"b\" } else { \"c\" };";
    assert_eq!(
        term(text, "x"),
        "if (1 > 2) { \"a\" } else { if (2 > 3) { \"b\" } else { \"c\" } }"
    );
    values(&[
        (text, "\"c\""),
        ("x = if true { 1 } else { #a };", "1"),
        ("x = if #a { 1 } else { 2 };", "#a"),
    ]);
}

#[test]
fn else_matches_any_atom_or_the_atom_its_pattern_names() {
    // DESIGN.md L1.16: `e else d` matches any atom until L2's families enumerate them.
    values(&[
        ("x = #a else 7;", "7"),
        ("x = #a(1) else 7;", "7"),
        ("x = 5 else 7;", "5"),
        ("x = #a(p: 1) else #a(p:) -> p;", "1"),
        ("x = \"q\" else #a -> 1;", "\"q\""),
        ("x = #b else #a -> 1 else 2;", "2"),
        ("x = #a else #a -> 1 else 2;", "1"),
    ]);
    assert_eq!(
        term("x = #a(p: 1) else #a(p:) -> p;", "x"),
        "match #a(p: 1) { #a(p: p) -> p, $1 -> $1 }"
    );
    assert_eq!(
        term("x = #b else #a -> 1 else 2;", "x"),
        "match match #b { is #a | #a(..) -> 1, $1 -> $1 } { is #_ -> 2, $2 -> $2 }"
    );
}

#[test]
fn a_safe_member_passes_an_atom_and_calls_on_anything_else() {
    values(&[("x = \"abc\"?.len;", "3"), ("x = #a?.len;", "#a")]);
    assert_eq!(
        term("x = \"abc\"?.len;", "x"),
        "{ $1 = \"abc\"; match $1 { is #_ -> $1, _ -> len($1) } }"
    );
}

#[test]
fn a_member_is_a_call_with_or_without_parentheses_and_chains() {
    let cases = [
        ("x = \"abc\".len;", "len(\"abc\")", "3"),
        ("x = \"abc\".len();", "len(\"abc\")", "3"),
        ("x = \"abc\".upper.len;", "len(upper(\"abc\"))", "3"),
        ("x = \"a\".trim.upper;", "upper(trim(\"a\"))", "\"A\""),
        ("y = 3; x = y.abs();", "abs(y)", "3"),
        ("f(s) = s ++ \"!\"; x = \"a\".f;", "f(\"a\")", "\"a!\""),
        ("f(s) = s ++ \"!\"; x = \"a\".f();", "f(\"a\")", "\"a!\""),
        // The receiver fills the first parameter, named or `positional`.
        ("f(positional n) = n; x = 3.f;", "f(3)", "3"),
        ("f(n) = n; x = 3.f;", "f(3)", "3"),
    ];
    for (text, shape, v) in cases {
        assert_eq!(term(text, "x"), shape, "{text}");
        assert_eq!(value(text, "x"), v, "{text}");
    }
    // The receiver fills only the first parameter; a named second one is still passed by
    // name.
    assert_eq!(
        one("f(s, t) = s ++ t; x = \"a\".f(\"b\");"),
        "this argument is passed by position, and the parameter it reaches, `t` of `f`, is a \
         named parameter, which a call passes only by name, as `t: …`. [\"b\"]"
    );
}

#[test]
fn named_arguments_reach_their_parameters_and_a_missing_one_is_reported() {
    let cases = [
        ("x = f(n: 1); f(n) = n;", "f(1)", "1"),
        ("x = f(m: 1, n: 2); f(n, m) = n - m;", "f(2, 1)", "1"),
        ("f(a, b = 1) = a + b; x = f(b: 2, a: 1);", "f(1, 2)", "3"),
        ("x = f(); f() = 3;", "f()", "3"),
    ];
    for (text, shape, v) in cases {
        assert_eq!(term(text, "x"), shape, "{text}");
        assert_eq!(value(text, "x"), v, "{text}");
    }
    assert_eq!(
        one("f(a, b = 1) = a + b; x = f();"),
        "this call of `f` gives no value to its parameter `a`, and `a` has no default, so the \
         call cannot be made. [f()]"
    );
    assert_eq!(
        one("f(a: int = a) = a; x = f();"),
        "the defaults of `a` read each other in a cycle, so none of them can be computed first. \
         Write one of them without reading the others. [f()]"
    );
}

#[test]
fn a_lambda_is_called_by_position_with_exactly_its_arguments() {
    values(&[
        ("x = ((a, b) -> a ++ b)(\"x\", \"y\");", "\"xy\""),
        ("x = (y -> y + 1)(2);", "3"),
        ("k = 2; f = y -> y * k; x = f(3);", "6"),
        ("f = y -> z -> y + z; x = f(1)(2);", "3"),
        ("g = (a, b) -> a + b; x = g(1, 2);", "3"),
    ]);
    assert_eq!(term("f = y -> z -> y + z; x = f(1)(2);", "x"), "(f(1))(2)");
    let lambda = "(T, T) -> T for T in int | f32 | f64 | rat";
    assert_eq!(
        one("g = (a, b) -> a + b; x = g(1);"),
        format!(
            "this call of `{lambda}` gives no value to its parameter `b`, and `b` has no default, \
             so the call cannot be made. [g(1)]"
        )
    );
    assert_eq!(
        one("g = (a, b) -> a + b; x = g(1, 2, 3);"),
        format!(
            "this argument is one more than `{lambda}` takes: `{lambda}` takes 2 arguments by \
             position, and the arguments before this one already fill them all. [3]"
        )
    );
    assert_eq!(
        one("g = (a, b) -> a + b; x = g(a: 1, b: 2);"),
        format!(
            "this argument is passed by name, as `a: …`, and `a` of `{lambda}` is positional, so \
             a call passes it only by position. [1]"
        )
    );
}

#[test]
fn a_cycle_among_statements_is_an_error_whether_a_value_or_a_function() {
    // DESIGN.md L1.16: a cycle among a scope's statements, self-reference included, is an
    // error. A function that calls itself is recursion, which layer L6 adds; a value defined
    // by its own value has no value at any layer.
    assert_eq!(
        one("a = a + 1; x = a;"),
        "`a` is defined in terms of its own value. [a = a + 1;]"
    );
    assert_eq!(
        one("f(n) = f(n); x = 1;"),
        "`f` is defined in terms of itself, which is recursion: this version of zedc does not \
         compile it yet. [f(n) = f(n);]"
    );
    assert_eq!(
        one("f(n) = g(n: n); g(n) = f(n: n); x = f(n: 1);"),
        "`f`, `g` are defined in terms of each other, which is recursion: this version of zedc \
         does not compile it yet. [f(n) = g(n: n);]"
    );
    // An order of definitions that is not a cycle is fine whatever the written order.
    assert_eq!(value("a = b; b = 1; x = a;", "x"), "1");
}

#[test]
fn atoms_with_and_without_payloads_are_values() {
    values(&[
        ("x = #a;", "#a"),
        ("x = #a(1);", "#a(1)"),
        ("x = #a(p: 1, q: 2);", "#a(p: 1, q: 2)"),
        ("t = (1, (2, 3)); x = t;", "(1, (2, 3))"),
    ]);
}

#[test]
fn each_prelude_word_of_l1_computes_on_its_corner_cases() {
    // DESIGN.md L1.18 and sec:order: `len` counts code points, `lower`/`upper` map case in
    // full (`ß` upper-cases to `SS`), `trim` removes Unicode white space, `sum` of a tuple of
    // one kind is its total, an int beside a rat taking the rat.
    values(&[
        ("x = len(\"héllo\");", "5"),
        ("x = len(\"a\\u{301}\");", "2"),
        ("x = len(\"\");", "0"),
        ("x = lower(\"ÀB\");", "\"àb\""),
        ("x = upper(\"àb\");", "\"ÀB\""),
        ("x = upper(\"ß\");", "\"SS\""),
        ("x = trim(\"  a  \");", "\"a\""),
        ("x = trim(\"\\u{2003}a\\u{2003}\");", "\"a\""),
        ("x = abs(-3);", "3"),
        ("x = abs(-2r);", "2r"),
        ("x = sum((1, 2));", "3"),
        ("x = sum((1,));", "1"),
        ("x = sum((1r, 2r));", "3r"),
        ("x = sum((1, 2r));", "3r"),
        ("x = rat(1) / 3;", "1r/3r"),
        ("x = f64(1) / 3;", "0.3333333333333333"),
        ("x = rat(3);", "3r"),
        ("x = int(7);", "7"),
    ]);
}

#[test]
fn a_cast_from_a_string_reads_what_the_design_lists() {
    // DESIGN.md L1.18: `int(s)` reads an optional `-` and ASCII digits, leading zeros
    // included; `rat(s)` reads `1/3` and a decimal; `f64(s)` gives `-0.0` after `-`, and a
    // value too small for the format rounds to zero.
    values(&[
        ("x = int(\"007\");", "7"),
        ("x = int(\"-0\");", "0"),
        ("x = rat(\"1/3\");", "1r/3r"),
        ("x = rat(\"0.5\");", "1r/2r"),
        ("x = f64(\"-0\");", "-0.0"),
        ("x = f64(\"1e-400\");", "0.0"),
    ]);
    // A cast that can only fail is rejected where it stands.
    for (text, cast, operand, atom) in [
        ("x = int(\"+5\");", "int", "\"+5\"", "#invalid"),
        ("x = int(\"٤٢\");", "int", "\"٤٢\"", "#invalid"),
        ("x = rat(\"1/0\");", "rat", "\"1/0\"", "#invalid"),
        ("x = f64(\"1e400\");", "f64", "\"1e400\"", "#overflow"),
        ("x = f64(\"infinity\");", "f64", "\"infinity\"", "#invalid"),
    ] {
        let at = &text[4..text.len() - 1];
        assert_eq!(
            one(text),
            format!(
                "`{cast}` here always fails: its operand `{operand}` gives `{atom}`, so this call \
                 never gives a value. [{at}]"
            ),
            "{text}"
        );
    }
}

/// The head and notes of the report on the rejected program `src`, without the source lines
/// under each.
fn report(src: &str) -> Vec<String> {
    let Err(out) = zedc::run::load(src.as_bytes()) else {
        panic!("accepted:\n{src}")
    };
    out.lines()
        .filter(|l| !l.trim_start().starts_with('|') && !l.contains(" | "))
        .map(|l| l.trim_start().to_string())
        .collect()
}

#[test]
fn a_cycle_is_reported_for_each_form_its_statements_and_uses_take() {
    // A destructuring names both its binders, and reads with the plural verb.
    assert_eq!(
        report("main = { a, b = (b, 1); a };\n")[..2],
        [
            "1:10: `a` and `b` are defined in terms of their own values.",
            "[1] 1:18: `a` and `b` read `b` here",
        ]
    );
    // A member call, with parentheses or without, is a use of the function it names.
    for call in ["", "()"] {
        let src = format!(
            "f(positional n: int) = n.g{call};\ng(positional n: int) = n.f{call};\nmain = f(1);\n"
        );
        assert_eq!(
            report(&src),
            [
                "1:1: `f`, `g` are defined in terms of each other, which is recursion: this \
                 version of zedc does not compile it yet.",
                "[1] 1:24: `f` uses `g` here",
                "[2] 2:24: `g` uses `f` here",
                "[3] 1:1: repair: remove one of the uses shown, which ends the cycle",
            ],
            "{src}"
        );
    }
    // More uses than members: removing one use may leave a cycle.
    assert_eq!(
        report(
            "f(positional n: int) = g(n) + h(n);\ng(positional n: int) = f(n);\n\
             h(positional n: int) = f(n);\nmain = f(1);\n"
        ),
        [
            "1:1: `f`, `g`, `h` are defined in terms of each other, which is recursion: this \
             version of zedc does not compile it yet.",
            "[1] 1:24: `f` uses `g` here",
            "[2] 1:31: `f` uses `h` here",
            "[3] 2:24: `g` uses `f` here",
            "[4] 3:24: `h` uses `f` here",
            "[5] 1:1: repair: remove uses shown until no definition uses itself, directly or \
             through the others",
        ]
    );
}

#[test]
fn an_atom_payload_mixing_position_and_name_or_left_open_is_rejected() {
    // DESIGN.md L1.17: "An atom's payload is all by position or all by name". `...` leaves a
    // function's named parameters open, and an atom has none.
    for text in ["x = #e(1, code: 2);", "x = #e(code: 2, ...);"] {
        let e = one(text);
        assert!(e.contains("payload") || e.contains("`...`"), "{text}: {e}");
    }
    values(&[
        ("x = #e(code: 2);", "#e(code: 2)"),
        ("x = #e(1, 2);", "#e(1, 2)"),
    ]);
}

#[test]
fn a_float_literal_that_rounds_to_infinity_or_to_zero_is_rejected() {
    // DESIGN.md sec:corner_cases: "A decimal literal that rounds to infinity in the format its
    // use fixes, or a nonzero one that rounds to zero there, is a compile error, so `1e400` and
    // `1e-400` are rejected at `f64`". The suffix fixes the format here; `0.0` is zero.
    for text in [
        "x = 1e400f64;",
        "x = 1e-400f64;",
        "x = 1e39f32;",
        "x = 1e-46f32;",
    ] {
        let e = one(text);
        assert!(e.contains("rounds"), "{text}: {e}");
    }
    values(&[("x = 0.0f64;", "0.0"), ("x = 1e38f32;", "1.0e38f32")]);
}
