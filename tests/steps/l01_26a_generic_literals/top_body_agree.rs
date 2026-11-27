//! A line bound outside every function gets the verdict and the value the same line gets in a
//! function body (QUESTIONS A63; deterministic checking; plan row POW-top-body-agree). An
//! operation on literals alone whose operators and literals leave it the float formats alone
//! takes `f64` in both places (DESIGN.md step L1.26a: in `g() = 2^-1.0`, "`-1.0` is the `f64`
//! `-1.0` and `g()` is `0.5`"; author decision 2026-11-12, an unfixed decimal takes `f64`):
//! `y = 2^-1.0` was rejected at the top level while `g() = 2^-1.0` gave `0.5`. A line that
//! holds a `/` of integer literals alone, `(1/2)^2`, is rejected in every place; `0.5^2` and
//! `0.5 * 2`, rejected in every place before that decision, take `f64` in every place.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{menu, tried, type_errors};

/// Each line `e` bound in three places, as named values `y0`, `y1`, …: at the top level,
/// `y0 = e;`; as a function's value, `g0() = e;`; and as a name bound in a function's
/// block, `g0() = { z = e; z };`; each program printing the values on one line.
fn places(lines: &[&str]) -> [String; 3] {
    let shown: Vec<String> = (0..lines.len()).map(|i| format!("${{y{i}}}")).collect();
    let main = format!(
        "main(args: MainArgs) -> int = {{ args.stdout <- \"{}\"; 0 }};\n",
        shown.join(" ")
    );
    let each = |f: &dyn Fn(usize, &str) -> String| -> String {
        let defs: String = lines.iter().enumerate().map(|(i, e)| f(i, e)).collect();
        format!("{defs}{main}")
    };
    [
        each(&|i, e| format!("y{i} = {e};\n")),
        each(&|i, e| format!("g{i}() = {e};\ny{i} = g{i}();\n")),
        each(&|i, e| format!("g{i}() = {{ z = {e}; z }};\ny{i} = g{i}();\n")),
    ]
}

#[test]
fn a_line_that_takes_f64_in_a_body_takes_it_at_the_top_level() {
    // Each line and the value it takes in all three places.
    let cases = [
        ("2^-1.0", "0.5"),
        ("2^0.5", "1.4142135623730951"),
        ("1.5^2.0", "2.25"),
        ("2^2.0", "4.0"),
        ("0.5^0.5", "0.7071067811865476"),
        ("(2^-1.0) * 3", "1.5"),
        ("2^(-1.0 * 2)", "0.25"),
        ("-2^0.5", "-1.4142135623730951"),
        ("(1.5^2)^0.5", "1.5"),
        ("2^(2^0.5)", "2.665144142690225"),
        // A literal joined to it by `+` takes `f64` with it, `1/2` too.
        ("0.5 + 2^0.5", "1.9142135623730951"),
        ("2^0.5 + 1/2", "1.9142135623730951"),
        // A bare literal compared with it follows it.
        ("2^-1.0 == 0.5", "true"),
        ("2^(1/2) == 0.5", "false"),
        // Each side of `==` takes `f64` on its own.
        ("(1/2)^0.5 == 2^0.5", "false"),
        // A `/` of integer literals compared with an operation holding a decimal meets its
        // `f64` (DESIGN.md step L1.26b: the `f64` of a decimal is a carrier that such a `/`
        // meets wherever the two reach one class; item LIT-division-meets-default-decimal), as
        // it meets a bare decimal in `1 / 2 == 1.5`; pair by pair in tuples. These were
        // rejected in every place, though the menu of `y = 1 / 2 == 1 / 2` offered
        // `y = 1.0 / 2 == 1 / 2` as a fix that checks.
        ("2^0.5 == 1/2", "false"),
        ("1.0 / 2 == 1 / 2", "true"),
        ("0.5 + 1 != 3 / 2", "false"),
        ("(1.0 / 2, 0) == (1 / 2, 0)", "true"),
        ("(0, (1 / 2, 0.5 + 1)) != (0, (1.0 / 2, 3 / 2))", "false"),
        // `<` makes one class of its sides.
        ("2^0.5 < 1.5", "true"),
        ("1 < 2^0.5", "true"),
        ("0.5 > 2^(1/2)", "false"),
        ("2^0.5 < 0.5^2", "false"),
        // Tuples, and tuples compared pair by pair.
        ("(2^0.5, 1)", "(1.4142135623730951, 1)"),
        ("(2^0.5, 1) == (1.5, 1)", "false"),
        // The values IEEE 754 gives.
        ("0.0^-0.5", "inf"),
        ("(0 - 1)^0.5", "nan"),
        // An operation on literals that meets an `f64`: the base `0.5` took `rat` from `^`
        // with an `int` exponent as it was walked, and kept it, and the run stopped at `^`
        // applied to (`rat`, `f64`).
        ("0.5^(1 + 1) * 1.0f64", "0.25"),
        // Rejected in every place before a decimal that nothing fixes took `f64` (author
        // decision 2026-11-12).
        ("0.5^2", "0.25"),
        ("0.5 * 2", "1.0"),
        ("0.5 * 2 == 2^0.5", "false"),
        ("2^0.5 == 0.5^2", "false"),
        ("(2^0.5, 0.5) == (1.0, 0.5)", "false"),
        ("0.5 < 1 + 1", "true"),
        ("0.5^(1 + 1)", "0.25"),
        ("2^(1 + 1) < 0.5", "false"),
        // A decimal that nothing fixes takes `f64`, and an operation on literals that keeps
        // `int` compared with it follows it (DESIGN.md L1.26b; row LIT-f64-op-meets-int-op,
        // once rejected with "A decimal literal is never an `int`" in every place).
        ("2^(1 + 1) == 0.5", "false"),
        ("0.5 == 2^(1 + 1)", "false"),
        ("2^(1 + 1) != 0.5", "true"),
        ("4.0 == 2^(1 + 1)", "true"),
    ];
    let lines: Vec<&str> = cases.iter().map(|(e, _)| *e).collect();
    let want: Vec<&str> = cases.iter().map(|(_, v)| *v).collect();
    let want = format!("{}\n", want.join(" "));
    for (src, place) in places(&lines).iter().zip(["top", "body", "block"]) {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{place}:\n{src}");
        let out = run(&format!("l01_26a_top_body_agree_{place}"), src, "", &[]);
        assert_eq!(
            (out.status, out.stderr.as_str()),
            (0, ""),
            "{place}:\n{src}"
        );
        assert_eq!(out.stdout, want, "{place}:\n{src}");
    }
    // A line gets the same value and the same warnings in every place (plan rows
    // POW-top-body-agree, POW-body-widen-warning-top-agree). The exponent of `0.5^(…)`, an
    // operation on integer literals alone, is read at `f64` by its value, `3.0`, and computes
    // nothing at run time, so no `2^100` in it is an integer operation and none warns
    // (DESIGN.md sec:domains: the warning is raised at each integer operation that crosses);
    // a body and a block warned twice, the top level not at all. At `rat` the exponent keeps
    // `int` and is computed, and each `2^100` warns, in every place.
    for (e, v, warns) in [
        ("0.5^(2^100 - 2^100 + 3)", "0.125", 0),
        ("2^(2^100 - 2^100 + 3) + 2r", "10r", 2),
    ] {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            assert_eq!(type_errors(src), Vec::<String>::new(), "{place}:\n{src}");
            let out = run(
                &format!("l01_26a_top_body_agree_widen_{place}"),
                src,
                "",
                &[],
            );
            assert_eq!(
                (out.status, out.stdout.as_str()),
                (0, format!("{v}\n").as_str()),
                "{place}:\n{src}"
            );
            let warned = out.stderr.matches("widens past a machine word").count();
            assert_eq!(warned, warns, "{place}:\n{}", out.stderr);
        }
    }
}

#[test]
fn a_line_rejected_in_a_body_is_rejected_at_the_top_level() {
    // Each holds a `/` of integer literals alone, which is rejected under `/` (author decision
    // 2026-11-12), or an `int` to a negative power. The lines with a decimal that this test
    // rejected before that decision take `f64` and are in
    // `a_line_that_takes_f64_in_a_body_takes_it_at_the_top_level`, as does `2^0.5 == 1/2`,
    // whose `/` meets the `f64` of the decimal. Two `/`s with no decimal stay rejected.
    let lines = [
        "(1/2)^2",
        "(3/2)^-2",
        "2^-1",
        "1/2 == 1/2",
        "(1/2, 0) == (1/2, 1)",
    ];
    for e in lines {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            assert!(!type_errors(src).is_empty(), "{place}: accepted\n{src}");
        }
    }
    // A `/` of integer literals alone in the exponent of a power of an integer literal is
    // rejected in every place by the same rule, though it leaves the float formats alone: no
    // decimal is among its literals (DESIGN.md step L1.26b). The top level gives fixes that
    // check, which run to `1.4142135623730951` and `false`.
    for (e, fix, v) in [
        ("2^(1/2)", "y0 = 2.0^(1.0/2);", "1.4142135623730951"),
        ("2^(1/2) < 1/2", "y0 = 2.0^(1.0/2) < 1/2;", "false"),
    ] {
        let [top, body, block] = places(&[e]);
        let errors = type_errors(&top);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].starts_with(
                "Nothing gives the integer literals a carrier, `/` has none at `int`, and `^` \
                 none at `rat` with this exponent:"
            ) && errors[0].contains(&format!("\n    {fix}          y0 is {v}\n")),
            "{errors:?}"
        );
        let fixed = top.replacen(&format!("y0 = {e};"), fix, 1);
        let out = run("l01_26a_top_body_half_fix", &fixed, "", &[]);
        assert_eq!(
            (out.status, out.stdout.as_str(), out.stderr.as_str()),
            (0, format!("{v}\n").as_str(), ""),
            "{fixed}"
        );
        for (src, place) in [(body, "body"), (block, "block")] {
            assert!(!type_errors(&src).is_empty(), "{place}: accepted\n{src}");
        }
    }
}

#[test]
fn a_comparison_of_an_f64_with_an_int_is_rejected_in_every_place() {
    for e in ["2^0.5 == 1 + 1", "2^0.5 != 1 + 1", "1 + 1 == 2^-1.0"] {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            assert!(!type_errors(src).is_empty(), "{place}: accepted\n{src}");
        }
    }
    let named = "g() = { b = 1 + 1; 2^0.5 == b };\n";
    assert!(!type_errors(named).is_empty(), "accepted\n{named}");
}

#[test]
fn a_comparison_in_a_body_reads_its_operations_at_their_carriers() {
    // Rejected, with the words the top level gives the same line.
    for (src, want) in [
        (
            "g() = 2^0.5 == 1 + 1;\n",
            "No value is both `f64` and `int`: the left operand compared by `==` with the \
             right operand always gives the same answer. Try `f64(…)` around the right operand \
             to compare the numbers instead.",
        ),
        (
            "g() = { b = 1 + 1; 2^0.5 == b };\n",
            "No value is both `f64` and `int`: the left operand compared by `==` with \
             `b : int` always gives the same answer. Try `f64(…)` around the right operand to \
             compare the numbers instead.",
        ),
    ] {
        let errs = type_errors(src);
        assert!(errs.iter().any(|e| e.contains(want)), "{src}{errs:#?}");
    }
    for src in [
        "g() = (2^0.5, 1) == (1 + 1, 1);\n",
        "g() = 2^0.5 == 2r;\n",
        "g() = { a = 2; a == 2^0.5 };\n",
        "g() = (1 + 1) * 1 == 2^0.5;\n",
        "g() = 1 + 1 == \"a\";\n",
    ] {
        assert!(!type_errors(src).is_empty(), "accepted\n{src}");
    }
    // Accepted: sides of one carrier, a side that meets a value of one carrier other than
    // `int` and takes it, a float format the operation may take, and a bare literal, which
    // follows the other side.
    let cases = [
        ("1 + 1 == 2 * 1", "true"),
        ("2^0.5 != 2^0.5", "false"),
        ("(1 + 1, 2^0.5) == (2, 2^0.5)", "true"),
        ("{ a = 2.0f64; a == 1 + 1 }", "true"),
        ("{ a = 2r; a == 1 + 1 }", "true"),
        ("{ a = 1.5f32; a == 2^0.5 }", "false"),
        ("1/2 == 0.5r", "true"),
        ("2^0.5 == 1", "false"),
    ];
    let defs: String = (cases.iter().enumerate())
        .map(|(i, (e, _))| format!("g{i}() = {e};\n"))
        .collect();
    let shown: Vec<String> = (0..cases.len()).map(|i| format!("${{g{i}()}}")).collect();
    let src = format!(
        "{defs}main(args: MainArgs) -> int = {{ args.stdout <- \"{}\"; 0 }};\n",
        shown.join(" ")
    );
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    let out = run("l01_26a_top_body_agree_compare", &src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    let want: Vec<&str> = cases.iter().map(|(_, v)| *v).collect();
    assert_eq!(out.stdout, format!("{}\n", want.join(" ")), "{src}");
    // A parameter's class is left to the call.
    let src = "g(x: f64) = x == 1 + 1;\n\
               main(args: MainArgs) -> int = { args.stdout <- \"${g(x: 2.0f64)}\"; 0 };\n";
    let out = run("l01_26a_top_body_agree_compare_param", src, "", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "true\n"), "{src}");
}

/// A body of `n` comparisons of operations on literals alone, then one of two tuples of `n`
/// such operations each: `g() = { c0 = 0 + 1 == 1 * 1; …; (2^0.5, 1 + 1, …) == (…) };`.
pub(super) fn comparisons(n: usize) -> String {
    let lines: String = (0..n)
        .map(|i| format!("c{i} = {i} + 1 == {} * 1; ", i + 1))
        .collect();
    let items: Vec<&str> = (0..n)
        .map(|i| if i % 2 == 0 { "2^0.5" } else { "1 + 1" })
        .collect();
    let t = items.join(", ");
    format!("g() = {{ {lines}({t}) == ({t}) }};\n")
}

#[test]
fn a_closed_default_takes_f64_as_a_binding_does() {
    let src = "f(x = 2^-1.0) = x;\n\
               main(args: MainArgs) -> int = { args.stdout <- \"${f()}\"; 0 };\n";
    let out = run("l01_26a_top_body_agree_default", src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "0.5\n");
    // A decimal that nothing fixes takes `f64` in a default as in a binding (author decision
    // 2026-11-12); a `/` of integer literals alone is rejected in both.
    let src = "f(x = 0.5^2) = x;\n\
               main(args: MainArgs) -> int = { args.stdout <- \"${f()}\"; 0 };\n";
    let out = run("l01_26a_top_body_agree_default_decimal", src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "0.25\n");
    assert!(!type_errors("f(x = (1/2)^2) = x;\n").is_empty());
}

#[test]
fn a_name_bound_to_a_line_that_took_f64_is_an_f64() {
    // As in a body, the name is an `f64` and not a class a later use could narrow.
    for src in [
        "y = 2^0.5;\nz = y + 1.0f32;\n",
        "g() = { y = 2^0.5; y + 1.0f32 };\n",
    ] {
        assert!(!type_errors(src).is_empty(), "{src}");
    }
    assert_eq!(
        type_errors("y = 2^0.5;\nz = y + 1.0f64;\n"),
        Vec::<String>::new()
    );
}

/// A top-level binding of `n` powers that take `f64`, added, and compared by `<` with an
/// operation on literals alone: `y = 2^0.5 + 2^0.5 + … < 2^(1 + 1) + 0.5;`.
pub(super) fn powers(n: usize) -> String {
    let terms = vec!["2^0.5"; n].join(" + ");
    format!("y = {terms};\nz = {terms} < 2^(1 + 1) + 0.5;\n")
}

#[test]
fn a_power_whose_exponent_is_no_int_takes_no_rat_in_any_place() {
    // At `rat`, `^` takes an `int` exponent alone (DESIGN.md sec:lexical), so a `^` whose
    // exponent holds a decimal literal, a `/`, a `rat` literal or an `int` power with a
    // negative exponent is no `rat`, and an operand of `rat` beside it is rejected in every
    // place (plan row LIT-rat-decimal-exponent). The top level took each as a `rat`: the run
    // stopped at `^` applied to (`rat`, `f64`), at `/` applied to (`int`, `int`) or at `^`
    // applied to (`int`, `int`), and `y = 2^0.5 == 2r` gave `false`.
    let lines = [
        "2^0.5 + 2r",
        "2^0.5 < 2r",
        "2^0.5 == 2r",
        "2r * 2^-0.5",
        "2^(1/2) + 2r",
        "2^(1 + 0.5) - 2r",
        "2^(2^0.5) + 2r",
        "2^(1/2 + 1) < 2r",
        "(2^0.5, 1) == (2r, 1)",
        "2r * 2^(2^-1)",
        "2r * 2^(1 - 2^-1)",
    ];
    for e in lines {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            assert!(!type_errors(src).is_empty(), "{place}: accepted\n{src}");
        }
    }
    // The same beside a name bound to a `rat`.
    for e in [
        "a + 2^0.5",
        "a == 2^(1/2)",
        "a < 2^0.5",
        "a * 2^(1/2)",
        "a == 2^2r",
    ] {
        for (src, place) in [
            (format!("a = 2r;\ny = {e};\n"), "top"),
            (format!("g() = {{ a = 2r; {e} }};\n"), "block"),
        ] {
            assert!(!type_errors(&src).is_empty(), "{place}: accepted\n{src}");
        }
    }
    // An exponent that is an `int` literal keeps the power a `rat`: the same value in all
    // three places.
    let cases = [
        ("2^2 + 2r", "6r"),
        ("2^-1 + 2r", "5r/2r"),
        ("2^-1 == 1r/2r", "true"),
        ("(1/2)^2 < 2r", "true"),
    ];
    let lines: Vec<&str> = cases.iter().map(|(e, _)| *e).collect();
    let want: Vec<&str> = cases.iter().map(|(_, v)| *v).collect();
    let want = format!("{}\n", want.join(" "));
    for (src, place) in places(&lines).iter().zip(["top", "body", "block"]) {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{place}:\n{src}");
        let out = run(&format!("l01_26a_top_body_agree_rat_{place}"), src, "", &[]);
        assert_eq!(
            (out.status, out.stderr.as_str()),
            (0, ""),
            "{place}:\n{src}"
        );
        assert_eq!(out.stdout, want, "{place}:\n{src}");
    }
}

/// The lines of `cases` in the three places ([`places`]), each accepted, each place running
/// with status 0 and printing the values of `cases` on one line. The run's message that a
/// `^` widens past a machine word is allowed where `widens` (the `2^100` in an exponent, at
/// run time a big integer): each of the run's messages is that one, under the name of the place.
fn same_in_every_place(tag: &str, cases: &[(&str, &str)], widens: bool) {
    let lines: Vec<&str> = cases.iter().map(|(e, _)| *e).collect();
    let want: Vec<&str> = cases.iter().map(|(_, v)| *v).collect();
    let want = format!("{}\n", want.join(" "));
    let warning = "widens past a machine word: this `^` of an i8 and an i8 gives a big integer.";
    for (src, place) in places(&lines).iter().zip(["top", "body", "block"]) {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{place}:\n{src}");
        let out = run(
            &format!("l01_26a_top_body_agree_{tag}_{place}"),
            src,
            "",
            &[],
        );
        assert_eq!(out.status, 0, "{place}:\n{src}\n{}", out.stderr);
        let warned: Vec<&str> = (out.stderr.lines())
            .filter(|l| l.contains("prog.zed:"))
            .collect();
        match widens {
            true => assert!(
                !warned.is_empty() && warned.iter().all(|w| w.ends_with(warning)),
                "{place}:\n{src}\n{}",
                out.stderr
            ),
            false => assert_eq!(out.stderr, "", "{place}:\n{src}"),
        }
        assert_eq!(out.stdout, want, "{place}:\n{src}");
    }
}

#[test]
fn a_power_whose_exponent_is_an_int_operation_takes_rat_in_every_place() {
    // At `rat`, `^` takes any `int` exponent (DESIGN.md sec:lexical), and an operation on
    // integer literals alone is an `int` there as one integer literal is ("An integer
    // exponent stays an `int`"), so each line takes `rat` and gives the same value in all three
    // places (plan row LIT-rat-int-op-exponent). A body rejected each: "The suffix makes the
    // literal `2r` a `rat`, never `int | f32 | f64`".
    same_in_every_place(
        "int_op",
        &[
            ("2^(1 + 1) + 2r", "6r"),
            ("2^(1 + 1) == 4r", "true"),
            ("(1/2)^(3 - 1) * 2r", "1r/2r"),
        ],
        false,
    );
    same_in_every_place("int_op_big", &[("2r * 2^(2^100 - 2^100 + 3)", "16r")], true);
    // The corner cases: a negative exponent, which `rat` takes; an exponent that is itself a
    // power with such an exponent; one under `-`; the power meeting an `f64` or an `f32`,
    // where the exponent stays an `int` (`f32 ^ int`) or takes `f64` with the base; and the
    // power alone, an `int`.
    same_in_every_place(
        "int_op_corner",
        &[
            ("2^(-(1 + 1)) * 2r", "1r/2r"),
            ("2^(1 - 3) + 0r", "1r/4r"),
            ("2^(1^(1 + 1)) + 2r", "4r"),
            ("(2^(1 + 1))^(3 - 1) == 16r", "true"),
            ("-(2^(2 * 2)) + 1r", "-15r"),
            ("2^(1 + 1) + 0.5f64", "4.5"),
            ("2^(1 + 1) + 1.5f32", "5.5"),
            ("2^(1 + 1)", "4"),
            ("0.5^(1 + 1) * 1.0f64", "0.25"),
        ],
        false,
    );
}

#[test]
fn a_power_whose_exponent_is_an_int_operation_follows_a_parameter() {
    // In a function whose parameter is of no declared type, the power's class is a type
    // variable: at run time the exponent takes the carrier of the argument, as a literal
    // exponent does, `f64` at an `f64` (there is no `f64 ^ int`), and stays an `int` at a
    // `rat` and an `int`.
    for (arg, want) in [
        ("2r", "6r"),
        ("0.5f64", "4.5"),
        ("3", "7"),
        ("1.5f32", "5.5"),
    ] {
        let src = format!(
            "g(positional x) = 2^(1 + 1) + x;\n\
             main(args: MainArgs) -> int = {{ args.stdout <- \"${{g({arg})}}\"; 0 }};\n"
        );
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        let out = run("l01_26a_top_body_agree_int_op_param", &src, "", &[]);
        assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
        assert_eq!(out.stdout, format!("{want}\n"), "{src}");
    }
}

#[test]
fn a_power_whose_exponent_is_no_int_operation_stays_rejected() {
    // LIT-rat-decimal-exponent's rejections stand: an exponent holding a decimal, a `/` or a
    // `rat` literal, or an `int` power with a negative exponent, is no `int`.
    for e in [
        "2^(4/2) + 2r",
        "2^(1 + 1.0) + 2r",
        "2^(1 + 2r)",
        "2^(2^-1) + 2r",
        "2^(1 - 2^-1) == 2r",
    ] {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            assert!(!type_errors(src).is_empty(), "{place}: accepted\n{src}");
        }
    }
}

/// A top-level binding and a function's value, each `2r` times a power whose exponent is `n`
/// powers of `1` nested by `^` over `(1 + 1)`: `y = 2r * 2^1^1^…^(1 + 1);`. Its benchmark is
/// `bench::top_body_agree::nested_int_operation_exponents_are_read_in_linear_time`.
pub(super) fn nested_int_exponents(n: usize) -> String {
    let e = format!("2r * 2^{}(1 + 1)", "1^".repeat(n));
    format!("y = {e};\ng() = {e};\n")
}

#[test]
fn nested_int_operation_exponents_take_rat() {
    for n in [0, 1, 3] {
        assert_eq!(
            type_errors(&nested_int_exponents(n)),
            Vec::<String>::new(),
            "n = {n}"
        );
    }
}

#[test]
fn a_body_of_comparisons_of_operations_on_literals_checks() {
    // A small instance of the benchmark
    // `bench::top_body_agree::comparisons_in_a_body_are_checked_in_linear_time`.
    assert_eq!(type_errors(&comparisons(4)), Vec::<String>::new());
}

#[test]
fn a_top_level_line_of_powers_takes_f64() {
    // A small instance of the benchmark
    // `bench::top_body_agree::a_top_level_line_of_many_powers_takes_f64_in_linear_time`.
    assert_eq!(type_errors(&powers(3)), Vec::<String>::new());
}

/// The type errors of `e` in the three places of [`places`]: the top level, a body and a block.
fn messages_in_every_place(e: &str) -> [Vec<String>; 3] {
    places(&[e]).map(|src| type_errors(&src))
}

#[test]
fn an_exponent_no_float_format_holds_leaves_rat_alone_and_is_rejected_in_every_place() {
    // An `int` exponent that no float format holds exactly, a literal or an operation on
    // integer literals, leaves the integer literal base `rat` alone: `f32 ^ int` is for a base
    // that is already an `f32` (DESIGN.md L1.17), and `f64 ^ f64` and `f32 ^ f32` take no such
    // exponent. Nothing in the line asks for `rat`, so its integer literals stay `int`, which
    // `/` does not take, and the line is rejected in all three places with the exact `rat`
    // form as its first fix, and in a body its one fix (POW-domains; plan row
    // LIT-f32-inexact-exponent). A body listed `f32 | rat`, and the top level and a block
    // offered `y0 = 2.0f64 ^ … / 3`, which is rejected too, since the exponent is no `f64`.
    let big = "1267650600228229401496703205375";
    let ints = "Nothing gives the integer literals a carrier, and `/` has none at `int`";
    // Where every literal is rewritten, as `2.0 ^ (2.0^100 - 1) / 3` does, the `f64` forms
    // compile and stay offered at the top level and in a block, as `f64s` lists them.
    let pow = "2.0 ^ (2.0^100 - 1) / 3";
    let cast = "f64(2) ^ (f64(2)^100 - 1) / 3";
    for (e, rat, first, span, f64s, value) in [
        (
            format!("2 ^ {big} / 3"),
            format!("2r ^ {big} / 3"),
            "2",
            None,
            None,
            None,
        ),
        (
            "2 ^ (2^100 - 1) / 3".into(),
            "2r ^ (2^100 - 1) / 3".into(),
            "2",
            None,
            Some((pow, cast)),
            None,
        ),
        (
            format!("(1/2) ^ {big} * 0"),
            format!("(1r/2) ^ {big} * 0"),
            "1",
            Some("(1/2)"),
            None,
            None,
        ),
        // `9007199254740993` is no `f64` either, so no `f64` form is offered for it.
        (
            "1 / 9007199254740993".into(),
            "1r / 9007199254740993".into(),
            "1",
            None,
            None,
            Some("1r/9007199254740993r"),
        ),
    ] {
        let [top, body, block] = messages_in_every_place(&e);
        let fix = format!("g0() = {rat};");
        let holds = format!("the literal is then exactly {first}, a rat");
        let fixes = [(fix.as_str(), holds.as_str())];
        let head = format!("Nothing gives the literal `{first}` a carrier");
        let want = format!("{head}{}{} [{first}]", tried(&fixes), menu(&fixes));
        assert_eq!(body, vec![want], "body: {e}");
        let fixed = places(&[e.as_str()])[1].replace(&format!("g0() = {e};"), &fix);
        assert_eq!(
            type_errors(&fixed),
            Vec::<String>::new(),
            "body fix:\n{fixed}"
        );
        let [top_src, _, block_src] = places(&[e.as_str()]);
        let (top_line, block_line) = (format!("y0 = {e};"), format!("g0() = {{ z = {e}; z }};"));
        for (got, place, name, line, src, written) in [
            (
                top,
                "top",
                "y0",
                format!("y0 = {rat};"),
                &top_src,
                &top_line,
            ),
            (
                block,
                "block",
                "z",
                format!("g0() = {{ z = {rat}; z }};"),
                &block_src,
                &block_line,
            ),
        ] {
            let holds = format!("{name} is {}", value.unwrap_or(rat.as_str()));
            let mut owned = vec![(line.clone(), holds)];
            if let Some((pow, cast)) = f64s {
                let at = |f: &str| line.replace(&rat, f);
                owned.push((at(pow), format!("{name} is inf")));
                owned.push((at(cast), format!("{name} is inf")));
            }
            let fixes: Vec<(&str, &str)> = owned
                .iter()
                .map(|(l, h)| (l.as_str(), h.as_str()))
                .collect();
            let head = format!("{ints}: `{name} = {e}`");
            let at = span.unwrap_or(e.as_str());
            let want = format!("{head}{}{} [{at}]", tried(&fixes), menu(&fixes));
            assert_eq!(got, vec![want], "{place}: {e}");
            // Each fix the menu offers is a program the checker takes.
            for (fixed, _) in &fixes {
                let src = src.replace(written.as_str(), fixed);
                assert_eq!(
                    type_errors(&src),
                    Vec::<String>::new(),
                    "{place} fix:\n{src}"
                );
            }
        }
    }
}

#[test]
fn a_literal_base_takes_no_f32_through_f32_power_int() {
    // `f32 ^ int` is for a base that is already an `f32` (DESIGN.md L1.17): a literal base
    // with an `int` exponent no `f32` holds exactly takes `f32` in no place, while a base of
    // type `f32` keeps the arrow. A body read `x * 2 ^ …` at `f32` and gave `inf`.
    let big = "1267650600228229401496703205375";
    for src in [
        format!("g(positional x: f32) = x * 2 ^ {big};\n"),
        "g(positional x: f32) = x + (-1) ^ 16777217;\n".to_string(),
        format!("g() = 0.0f32 + 2 ^ {big};\n"),
        format!("g(positional x) = 2 ^ {big} + x;\ny = g(1.0f32);\n"),
        "g(positional x) = (-1) ^ 16777217 + x;\ny = g(0.0f32);\n".to_string(),
    ] {
        let errs = type_errors(&src);
        assert!(!errs.is_empty(), "accepted:\n{src}");
        assert!(
            errs.iter()
                .all(|m| !m.contains("f32 |") && !m.contains("| f32")),
            "{src}{errs:#?}"
        );
    }
    // A base of type `f32`, or an exponent `f32` holds exactly, keeps `f32`.
    for (src, want) in [
        (
            format!("g(positional x: f32) = x ^ {big};\ny = g(2.0f32);\n"),
            "inf",
        ),
        (
            "g(positional x: f32) = x ^ 16777217;\ny = g(-1.0f32);\n".into(),
            "-1.0",
        ),
        (
            "g(positional x: f32) = x * 2 ^ 3;\ny = g(1.5f32);\n".into(),
            "12.0",
        ),
        (
            "g(positional x) = (-1) ^ 16777217 + x;\ny = g(0.0f64);\n".into(),
            "-1.0",
        ),
        (
            "g(positional x) = 2 ^ 16777216 * x;\ny = g(0.0f32);\n".into(),
            "nan",
        ),
    ] {
        let src =
            format!("{src}main(args: MainArgs) -> int = {{ args.stdout <- \"${{y}}\"; 0 }};\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        let out = run("l01_26a_top_body_agree_f32_base", &src, "", &[]);
        assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
        assert_eq!(out.stdout, format!("{want}\n"), "{src}");
    }
}

#[test]
fn a_generic_body_warns_where_its_int_instance_crosses_the_word() {
    // DESIGN.md sec:domains: the widening warning is raised "at each integer operation ...
    // whose operands each have a domain within 128 bits while its result's domain is not".
    // The generic `g(positional x) = x + (2^100 - 2^100 + 3)` elaborates, at a call with an
    // `int`, to the `int` term of the typed `g(positional x: int) = …`, so it warns as the
    // typed one does; called only at `f64`, its `int` arm is reached by no call and nothing
    // computes `2^100`, so it warns not at all (row WIDEN-generic-literal-op-int-instance; the
    // last case is the f32 case of `a_literal_base_takes_no_f32_through_f32_power_int`). A
    // call at `int` and one at `f64` warn once per operation, as one call does.
    let main = "main(args: MainArgs) -> int = { args.stdout <- \"${y}\"; 0 };\n";
    let warned = |tag: &str, src: &str| {
        let out = run(tag, src, "", &[]);
        assert_eq!(out.status, 0, "{src}\n{}", out.stderr);
        out.stderr.matches("widens past a machine word").count()
    };
    for body in ["x + (2^100 - 2^100 + 3)", "x ^ (2^100 - 2^100 + 3)"] {
        let typed = format!("g(positional x: int) = {body};\ny = g(2);\n{main}");
        assert_eq!(warned("widen_generic_typed", &typed), 2, "{typed}");
        for (calls, want) in [
            ("y = g(2);\n", 2),
            ("y = g(2.0);\n", 0),
            ("z = g(2.0);\ny = g(2);\n", 2),
            // Through a generic caller: the carrier `h`'s call gives `z` reaches `g`'s `x`.
            ("h(positional z) = g(z);\ny = h(2);\n", 2),
            ("h(positional z) = g(z);\ny = h(2.0);\n", 0),
        ] {
            let generic = format!("g(positional x) = {body};\n{calls}{main}");
            assert_eq!(warned("widen_generic_free", &generic), want, "{generic}");
        }
    }
}

/// A chain of `n` generic functions, each adding a literal to what the one before gives,
/// `g1(positional z) = g0(z) + 1;`, from `g0(positional x) = x + 1;`, and one call of the last
/// at `int`: each literal follows its function's parameter, and the carrier the call gives
/// reaches every one of them back through the chain (`Ck::own_follows` in
/// crates/zedc-check/src/check/mod.rs).
pub(super) fn generic_literal_chain(n: usize) -> String {
    let mut s = String::from("g0(positional x) = x + 1;\n");
    for i in 1..=n {
        s.push_str(&format!("g{i}(positional z) = g{}(z) + 1;\n", i - 1));
    }
    s.push_str(&format!("y = g{n}(2);\n"));
    s
}

#[test]
fn a_chain_of_generic_functions_checks_at_int() {
    // The small instance of `bench::top_body_agree::a_chain_of_generic_literals_scales`.
    let src = generic_literal_chain(4);
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
}

/// A top-level binding of `n` nested powers of integer literals, which an `f64` form rewrites
/// all of, beside a divisor no exact `f64`, which it leaves:
/// `y = 1^(1^(…^(1+1)…)) / 3 + 1 / 9007199254740993;`, rejected with the `rat` form alone.
pub(super) fn nested_powers_by_an_inexact_divisor(n: usize) -> String {
    let powers = format!("{}1+1{}", "1^(".repeat(n), ")".repeat(n));
    format!("y = {powers} / 3 + 1 / 9007199254740993;\n")
}

#[test]
fn nested_powers_by_an_inexact_divisor_offer_no_f64_form() {
    // The menu leaves out the `f64` forms, since the divisor `9007199254740993` is left to take
    // `f64` and is no exact `f64` (plan row LIT-f32-inexact-exponent). Benchmark:
    // `bench::top_body_agree::nested_powers_by_an_inexact_divisor_are_rejected_in_linear_time`.
    let errs = type_errors(&nested_powers_by_an_inexact_divisor(3));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    let fix = "y = 1r^(1^(1^(1+1))) / 3 + 1 / 9007199254740993;";
    assert!(errs[0].contains(fix), "{}", errs[0]);
    assert!(!errs[0].contains("f64"), "{}", errs[0]);
}

/// `add(x, y) = x + y;` and `n` top-level bindings that each give an operation on literals
/// alone to a generic call beside a decimal, `add(x: 1 / 2, y: 1.5)` and `min(1 / 2, 1.5)`
/// by turns, and one whose operation is a sum of `n` divisions: each takes `f64`, with no
/// error.
pub(super) fn generic_ops(n: usize) -> String {
    let mut src = String::from("add(x, y) = x + y;\n");
    for i in 0..n {
        src += &match i % 2 {
            0 => format!("y{i} = add(x: 1 / 2, y: 1.5);\n"),
            _ => format!("y{i} = min(1 / 2, 1.5);\n"),
        };
    }
    let sum = vec!["1 / 2"; n].join(" + ");
    src + &format!("z = add(x: {sum}, y: 1.5);\nw = min({sum}, 1.5);\n")
}

/// One top-level `min` of two tuples of `n` components, the `i`th of the first an operation on
/// literals alone, `1 / (i + 2)`, and that of the second a decimal, `i.5`: each operation
/// takes `f64` beside its decimal, with no error (row FAIL-top-literal-op-nested-or-component).
pub(super) fn tuple_component_ops(n: usize) -> String {
    let ops: Vec<String> = (0..n).map(|i| format!("1 / {}", i + 2)).collect();
    let decimals: Vec<String> = (0..n).map(|i| format!("{i}.5")).collect();
    format!(
        "y = min(({}), ({}));\n",
        ops.join(", "),
        decimals.join(", ")
    )
}

#[test]
fn many_operations_in_tuple_components_take_f64() {
    assert_eq!(type_errors(&tuple_component_ops(20)), Vec::<String>::new());
}

/// One top-level binding `r` of an array of `n` parts, each an operation on literals that
/// takes `f64` inside a tuple display, an atom, a set or a map by turns, and of one array
/// nested `n` deep around such an operation: each takes `f64`, with no error.
pub(super) fn display_ops(n: usize) -> String {
    let parts: Vec<String> = (0..n)
        .map(|i| match i % 4 {
            0 => format!("({i}, 0.5 + 2*2)"),
            1 => format!("({i}, #a(0.5 + 2^2))"),
            2 => format!("({i}, {{0.5 + 2*2}})"),
            _ => format!("({i}, {{{i} -> 0.5 + 2*2}})"),
        })
        .collect();
    let deep = format!("{}0.5 + 2*2{}", "[".repeat(n), "]".repeat(n));
    format!("r = [{}];\ns = {deep};\n", parts.join(", "))
}

#[test]
fn a_display_of_many_parts_that_take_f64_is_accepted() {
    // A small instance of `bench::top_body_agree::displays_with_parts_that_take_f64_scale`.
    assert_eq!(type_errors(&display_ops(8)), Vec::<String>::new());
}

/// An operation on literals that takes `f64` inside an array, set or map display, or inside a
/// tuple display or an atom, gets the same verdict and value in every place. At the top
/// level the displays were rejected, "A decimal literal is never an `int`: `0.5` meets `+`,
/// which expects `int`", while a body took `f64`; and a tuple display or an atom was typed
/// `Never`, so a run found its value outside its type (the random program of seed
/// 4877959526508188689). The controls, `[2^2]` and `(1, 2^2)`, keep `int`.
#[test]
fn an_operation_that_takes_f64_inside_a_display_agrees_in_every_place() {
    let cases = [
        // An array prints as the map from its ranks it is.
        ("[0.5 + 2*2]", "{0 -> 4.5}"),
        ("[1.5, 0.5 + 2^2]", "{0 -> 1.5, 1 -> 4.5}"),
        ("{0.5 + 2*2}", "{4.5}"),
        ("{1 -> 0.5 + 2*2}", "{1 -> 4.5}"),
        ("{0.5 + 2*2 -> 1}", "{4.5 -> 1}"),
        ("[(1, 0.5 + 2^2)]", "{0 -> (1, 4.5)}"),
        ("(1, [0.5 + 2*2])", "(1, {0 -> 4.5})"),
        ("[[0.5 + 2*2]]", "{0 -> {0 -> 4.5}}"),
        ("(1, 0.5 + 2*2)", "(1, 4.5)"),
        ("(1, (2, 0.5 + 2*2))", "(1, (2, 4.5))"),
        // In a tuple: a loose atom interpolated would leave the string.
        ("(#a(0.5 + 2*2),)", "(#a(4.5),)"),
        ("(1, #a(x: 0.5 + 2*2))", "(1, #a(x: 4.5))"),
        ("[2^2]", "{0 -> 4}"),
        ("(1, 2^2)", "(1, 4)"),
    ];
    let lines: Vec<&str> = cases.iter().map(|(e, _)| *e).collect();
    let want: Vec<&str> = cases.iter().map(|(_, v)| *v).collect();
    let want = format!("{}\n", want.join(" "));
    for (src, place) in places(&lines).iter().zip(["top", "body", "block"]) {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{place}:\n{src}");
        let out = run(&format!("l01_26a_display_agree_{place}"), src, "", &[]);
        assert_eq!(
            (out.status, out.stderr.as_str()),
            (0, ""),
            "{place}:\n{src}"
        );
        assert_eq!(out.stdout, want, "{place}:\n{src}");
    }
}

#[test]
fn many_operations_at_generic_arguments_take_f64() {
    // A small instance of `bench::top_body_agree::operations_at_generic_arguments_scale`.
    assert_eq!(type_errors(&generic_ops(5)), Vec::<String>::new());
}

#[test]
fn an_operation_on_literals_at_a_generic_argument_follows_the_class_in_every_place() {
    // DESIGN.md step L1.26b: an operation on literals alone given as a call's argument at a
    // generic parameter, as an operand of `min`/`max`, or as a component of a tuple argument
    // takes the carrier of the class it joins there, the `f64` of a decimal literal that
    // nothing else fixes included, the same at the top level as in a body (row
    // FAIL-top-literal-op-at-generic-arg; the top level once settled the operation alone). An
    // operation inside a nested call's argument or inside a tuple component is row
    // FAIL-top-literal-op-nested-or-component.
    let pre = "add(x, y) = x + y;\n";
    let cases = [
        ("add(x: 1 / 2, y: 1.5)", "2.0"),
        ("add(x: 1.5, y: 1 / 2)", "2.0"),
        ("min(1 / 2, 1.5)", "0.5"),
        ("max(1.5, 1 / 2)", "1.5"),
        ("add(x: 1 / 2, y: 1.5f64)", "2.0"),
        ("min(1 / 2, 1.5f64)", "0.5"),
        ("add(x: 1 / 2, y: 0.5r)", "1r"),
        ("min(1 / 2, 0.5r)", "1r/2r"),
        ("add(x: 1 + 1, y: 1.5)", "3.5"),
        ("min(1 + 1, 1.5)", "1.5"),
        ("add(x: 1 + 1, y: 1.5f64)", "3.5"),
        ("1 / 2 == 1.5", "false"),
    ];
    let mut bad = Vec::new();
    for (e, want) in cases {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            let src = format!("{pre}{src}");
            let errs = type_errors(&src);
            if !errs.is_empty() {
                bad.push(format!("{e} {place}: rejected"));
                continue;
            }
            let out = run(
                &format!("l01_26a_top_literal_op_arg_{place}"),
                &src,
                "",
                &[],
            );
            if (out.status, out.stdout.as_str()) != (0, format!("{want}\n").as_str()) {
                bad.push(format!("{e} {place}: {:?}", out.stdout));
            }
        }
    }
    // A `/` of integer literals that meets no decimal and no carrier is rejected in every
    // place, at its `1`, once.
    let pre = "add(x, y) = x + y;\npair(x, y) = (x, y);\n";
    for e in ["add(x: 1 / 2, y: 1)", "pair(x: 1 / 2, y: 1.5)"] {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            let errs = type_errors(&format!("{pre}{src}"));
            if errs.len() != 1 || !errs[0].starts_with("Nothing gives the literal `1` a carrier.") {
                bad.push(format!("{e} {place}: {errs:?}"));
            }
        }
    }
    assert_eq!(bad, Vec::<String>::new());
}

#[test]
fn a_division_branch_beside_a_decimal_compared_is_rejected_whatever_names_the_condition() {
    // DESIGN.md step L1.26a settles each literal branch of an `if` as it would be alone, so the
    // `1 / 2` of `(if c { 1 / 2 } else { 1.5 }) == 0.5` meets no carrier and is rejected at its
    // `1`, whatever names `c`: a parameter, or a name bound at the top level (row
    // FAIL-branch-division-named-condition-body; a body once read the branch at the `f64` of the
    // `0.5` where `c` was bound at the top level).
    let e = "(if c { 1 / 2 } else { 1.5 }) == 0.5";
    let mut bad = Vec::new();
    for cdef in ["c = 1 > 0;\n", "c = true;\n"] {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            let errs = type_errors(&format!("{cdef}{src}"));
            if errs.len() != 1 || !errs[0].starts_with("Nothing gives the literal `1` a carrier.") {
                bad.push(format!("{cdef:?} {place}: {errs:?}"));
            }
        }
    }
    let src = format!(
        "g(positional c: bool) = {e};\ny0 = g(true);\nmain(args: MainArgs) -> int = {{ args.stdout <- \"${{y0}}\"; 0 }};\n"
    );
    let errs = type_errors(&src);
    if errs.len() != 1 || !errs[0].starts_with("Nothing gives the literal `1` a carrier.") {
        bad.push(format!("parameter: {errs:?}"));
    }
    assert_eq!(bad, Vec::<String>::new());
}

/// DESIGN step L1.26b: an operation on literals alone that reaches a class takes the class's
/// carrier, the same at the top level as in a body (row FAIL-top-literal-op-nested-or-component).
/// `min((1 / 2, 1), (1.5, 2))`, and the same one tuple deeper under `max`: an operation that is
/// a tuple component meets the other tuple's component (it was read as `Part::Other`, typed as
/// walked, and rejected at the top level only); `h((1 / 2, 1.5))`: it meets the other component
/// through `p`. The nested call of the same row is
/// `an_operation_on_literals_in_a_nested_call_follows_the_class`.
#[test]
fn an_operation_on_literals_in_a_tuple_component_follows_the_class() {
    let pre = "add(x, y) = x + y;\nh(positional p) = p[0] + p[1];\n";
    let cases = [
        ("min((1 / 2, 1), (1.5, 2))", "(0.5, 1)"),
        ("max(((1 / 2, 1), 2), ((1.5, 2), 3))", "((1.5, 2), 3)"),
        ("h((1 / 2, 1.5))", "2.0"),
    ];
    let mut bad = Vec::new();
    for (e, want) in cases {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            let src = format!("{pre}{src}");
            let errs = type_errors(&src);
            if !errs.is_empty() {
                bad.push(format!("{e} {place}: rejected: {errs:?}"));
                continue;
            }
            let out = run(
                &format!("l01_26a_top_literal_op_nested_{place}"),
                &src,
                "",
                &[],
            );
            if (out.status, out.stdout.as_str()) != (0, format!("{want}\n").as_str()) {
                bad.push(format!("{e} {place}: {:?}", out.stdout));
            }
        }
    }
    assert_eq!(bad, Vec::<String>::new());
}

/// DESIGN step L1.26b: an operation on literals alone that reaches a class takes the class's
/// carrier, the same at the top level as in a body (row FAIL-top-literal-op-nested-or-component).
/// In `add(x: add(x: 1 / 2, y: 1), y: 1.5)` the inner call's `1 / 2` meets only the `1` there,
/// and the outer call's `1.5` through the inner call's result: it takes `f64` as in a body. The
/// inner call was settled as it was walked, at the top level only, and its `1 / 2` rejected
/// there. The deeper nest and two nested calls side by side, whose classes meet only at the
/// outer call, are read alike; a nest with no decimal anywhere, whose `1 / 2` nothing fixes,
/// is rejected in all three places, as in a body before. Red before the fix: the top-level
/// cases only.
#[test]
fn an_operation_on_literals_in_a_nested_call_follows_the_class() {
    let pre = "add(x, y) = x + y;\n";
    let cases = [
        ("add(x: add(x: 1 / 2, y: 1), y: 1.5)", Some("3.0")),
        ("add(x: 1.5, y: add(x: 1, y: 1 / 2))", Some("3.0")),
        (
            "add(x: add(x: add(x: 1 / 2, y: 1), y: 1), y: 0.5)",
            Some("3.0"),
        ),
        ("add(x: add(x: 1 / 2, y: 1 / 2), y: 2.5)", Some("3.5")),
        (
            "add(x: add(x: 1 / 2, y: 1), y: add(x: 1, y: 0.5))",
            Some("3.0"),
        ),
        ("add(x: add(x: 1 / 2, y: 1), y: 1)", None),
    ];
    let mut bad = Vec::new();
    for (e, want) in cases {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            let src = format!("{pre}{src}");
            let errs = type_errors(&src);
            let Some(want) = want else {
                if errs.is_empty() {
                    bad.push(format!("{e} {place}: accepted"));
                }
                continue;
            };
            if !errs.is_empty() {
                bad.push(format!("{e} {place}: rejected: {errs:?}"));
                continue;
            }
            let out = run(
                &format!("l01_26a_top_literal_op_nested_call_{place}"),
                &src,
                "",
                &[],
            );
            if (out.status, out.stdout.as_str()) != (0, format!("{want}\n").as_str()) {
                bad.push(format!("{e} {place}: {:?}", out.stdout));
            }
        }
    }
    assert_eq!(bad, Vec::<String>::new());
}

/// A rejection kept from a nest of top-level calls carries the steps of every call it lay in.
/// The `1 / 2` of `first(p: (1, 1 / 2))` is in a tuple component that no use reaches, so its
/// class is not asked and nothing gives the `1` a carrier. Its rejection is parked while the
/// calls of `add` around it, at a parameter of bounded type variable, keep the class open
/// (`Ck::lit_park`, `Ck::top_nested_written`), and only the outermost call settles the class
/// and keeps the rejection (`Ck::resolve_top_parts`). The steps of the calls passed while it
/// was parked, `first`'s declaration, were lost before (row b22-checkwalk4, the first weak
/// point of handoff-b22-checkwalk3): it gave only `add`'s, where the same call alone gives
/// `first`'s. Each of the two fixes is still offered and checked as written.
#[test]
fn a_rejection_kept_from_nested_calls_has_the_steps_of_each_call() {
    use zed_tests::step_helpers::l01_26_type_resolution::info;
    let pre = "add(x, y) = x + y;\nfirst(p) = p[0];\n";
    let first = "`first` is declared here with no type written for `p` or its result; the type \
                 the checker found for `first` is `(p: 0 -> T) -> T`";
    let add = "`add` is declared here with no type written for `x`, `y` or its result; the type \
               the checker found for `add` is `(x: T, y: T) -> T for T in int | f32 | f64 | rat`";
    let mut e = "first(p: (1, 1 / 2))".to_string();
    for depth in 0..4 {
        let line = format!("z = {e};");
        let src = format!("{pre}{line}\n");
        let (i, _) = info(&src);
        assert_eq!(i.errors.len(), 1, "{src}");
        // `first`'s result prints `T` at every depth: each type names its variables apart, and
        // `add`'s `T`, bounded, is named in order of first place as `first`'s is (row
        // UNDERSCORE-print-followups; before, `add`'s `T` was a name given when its signature
        // opened, a word of the message, and `first`'s printed `(p: 0 -> U) -> U` inside calls of
        // `add`).
        let notes: Vec<String> = i.errors[0]
            .notes
            .iter()
            .map(|n| n.text.to_string())
            .collect();
        let want: Vec<&str> = match depth {
            0 => vec![first],
            _ => vec![first, add],
        };
        assert_eq!(notes, want, "{src}");
        let menu = &i.errors[0].menu;
        for fix in ["1r / 2", "1.0f64 / 2"] {
            let fixed = line.replacen("1 / 2", fix, 1);
            assert!(menu.contains(&fixed), "{src}: {menu}");
        }
        assert!(menu.contains("fixes, each checked here:"), "{src}: {menu}");
        e = format!("add(x: {e}, y: 1)");
    }
}

/// The same rejection in a function body, as the function's value or in a block, carries the
/// steps it carries at the top level (row MSG-body-notes-match-top). There the end of the
/// function gives the class its type, after every call around the literal ended, and the
/// steps of those calls were lost: `f() = first(p: (1, 1 / 2));` gave none, where
/// `z = first(p: (1, 1 / 2));` gives the step on `first`'s declaration. `id`, generic in its
/// parameter, is read alike. Red before the fix: every body and block case.
#[test]
fn a_rejection_in_a_body_has_the_steps_of_each_call_as_at_the_top_level() {
    use zed_tests::step_helpers::l01_26_type_resolution::info;
    let pre = "add(x, y) = x + y;\nfirst(p) = p[0];\nid(x) = x;\n";
    let mut bad = Vec::new();
    for inner in ["first(p: (1, 1 / 2))", "id(x: 1 / 2)"] {
        let mut e = inner.to_string();
        for _ in 0..3 {
            let lines = [
                format!("z = {e};"),
                format!("f() = {e};"),
                format!("f() = {{ z = {e}; z }};"),
            ];
            let found: Vec<(Vec<String>, String)> = (lines.iter())
                .map(|line| {
                    let (i, _) = info(&format!("{pre}{line}\n"));
                    assert_eq!(i.errors.len(), 1, "{line}: {:#?}", i.errors);
                    let notes = (i.errors[0].notes.iter()).map(|n| n.text.to_string());
                    (notes.collect(), i.errors[0].menu.clone())
                })
                .collect();
            for (line, (notes, menu)) in lines.iter().zip(&found).skip(1) {
                if *notes != found[0].0 {
                    bad.push(format!(
                        "{line}: {notes:#?} at the top level {:#?}",
                        found[0].0
                    ));
                }
                let fixed = line.replacen("1 / 2", "1r / 2", 1);
                if !menu.contains(&fixed) {
                    bad.push(format!("{line}: no fix {fixed} in {menu}"));
                }
            }
            e = format!("add(x: {e}, y: 1)");
        }
    }
    assert_eq!(bad, Vec::<String>::new());
    let src = body_call_notes(3);
    let (i, _) = info(&src);
    let notes: Vec<usize> = (i.errors.iter()).map(|e| e.notes.len()).collect();
    assert_eq!(notes, [2, 1], "{src}");
}

/// Two bodies, each rejecting the `1` of `first(p: (1, 1 / 2))`: in one it is nested in `n`
/// calls of `add`, and in the other it stands beside `n` calls of `id`. Each rejection gets
/// the steps of the calls it lies in, `first`'s and `add`'s, once each (row
/// MSG-body-notes-match-top).
pub(super) fn body_call_notes(n: usize) -> String {
    let nest = (0..n).fold(String::from("first(p: (1, 1 / 2))"), |e, _| {
        format!("add(x: {e}, y: 1)")
    });
    let ids: String = (0..n).map(|i| format!(", id(x: {i})")).collect();
    format!(
        "add(x, y) = x + y;\nfirst(p) = p[0];\nid(x) = x;\nf() = {nest};\ng() = (first(p: (1, 1 / 2)){ids});\n"
    )
}

/// `add(x, y) = x + y;`, `n` top-level bindings of a call nested in a call, the inner one given
/// `1 / 2` and the outer one a decimal, and one binding of a call nested `n` deep, each level
/// given `1 / 2` beside the call below and only the outermost a decimal: each operation takes
/// `f64` with its class, with no error (row FAIL-top-literal-op-nested-or-component).
pub(super) fn nested_call_ops(n: usize) -> String {
    let mut src = String::from("add(x, y) = x + y;\n");
    for i in 0..n {
        src += &format!("y{i} = add(x: add(x: 1 / 2, y: {i}), y: 1.5);\n");
    }
    let deep = (0..n).fold(String::from("1 / 2"), |e, _| {
        format!("add(x: {e}, y: 1 / 2)")
    });
    src + &format!("z = add(x: {deep}, y: 1.5);\n")
}

#[test]
fn many_operations_in_nested_calls_take_f64() {
    // A small instance of `bench::top_body_agree::operations_in_nested_calls_scale`.
    assert_eq!(type_errors(&nested_call_ops(8)), Vec::<String>::new());
}
