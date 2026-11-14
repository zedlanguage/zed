//! A line bound outside every function gets the verdict and the value the same line gets in a
//! function body (QUESTIONS A63; deterministic checking; plan row POW-top-body-agree). An
//! operation on literals alone whose operators and literals leave it the float formats alone
//! takes `f64` in both places (DESIGN.md step L1.26a: in `g() = 2^-1.0`, "`-1.0` is the `f64`
//! `-1.0` and `g()` is `0.5`"; author decision 2026-11-12, an unfixed decimal takes `f64`):
//! `y = 2^-1.0` was rejected at the top level while `g() = 2^-1.0` gave `0.5`. A line that
//! leaves `rat` among the carriers, `0.5^2` or `0.5 * 2`, is rejected in both places.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

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
        // An exponent that is no integer literal leaves the decimal base no `rat`.
        ("0.5^(1 + 1)", "0.25"),
        // A bare literal compared with it follows it.
        ("2^-1.0 == 0.5", "true"),
        ("2^(1/2) == 0.5", "false"),
        // Each side of `==` takes `f64` on its own.
        ("(1/2)^0.5 == 2^0.5", "false"),
        // `<` makes one class of its sides.
        ("2^0.5 < 1.5", "true"),
        ("1 < 2^0.5", "true"),
        ("2^(1 + 1) < 0.5", "false"),
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
}

#[test]
fn a_line_rejected_in_a_body_is_rejected_at_the_top_level() {
    // Each leaves `rat` or `int` among the carriers of a literal, or holds no decimal that
    // chooses among the float formats.
    let lines = [
        "0.5^2",
        "(1/2)^2",
        "(3/2)^-2",
        "0.5 * 2",
        "2^-1",
        "2^(1/2)",
        "2^(1/2) < 1/2",
        "0.5 * 2 == 2^0.5",
        "2^0.5 == 0.5^2",
        "2^0.5 == 1/2",
        "(2^0.5, 0.5) == (1.0, 0.5)",
        "2^(1 + 1) == 0.5",
        "0.5 < 1 + 1",
    ];
    for e in lines {
        for (src, place) in places(&[e]).iter().zip(["top", "body", "block"]) {
            assert!(!type_errors(src).is_empty(), "{place}: accepted\n{src}");
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
fn comparisons(n: usize) -> String {
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
fn comparisons_in_a_body_are_checked_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&comparisons(4)), Vec::<String>::new());
            let n = 1000;
            let srcs = [comparisons(n), comparisons(scaling::FACTOR * n)];
            scaling::check(
                "checking a body of n comparisons of operations on literals alone",
                n,
                |m| {
                    type_errors(&srcs[usize::from(m != n)]);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_closed_default_takes_f64_as_a_binding_does() {
    let src = "f(x = 2^-1.0) = x;\n\
               main(args: MainArgs) -> int = { args.stdout <- \"${f()}\"; 0 };\n";
    let out = run("l01_26a_top_body_agree_default", src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "0.5\n");
    assert!(!type_errors("f(x = 0.5^2) = x;\n").is_empty());
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
fn powers(n: usize) -> String {
    let terms = vec!["2^0.5"; n].join(" + ");
    format!("y = {terms};\nz = {terms} < 2^(1 + 1) + 0.5;\n")
}

#[test]
fn a_top_level_line_of_many_powers_takes_f64_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&powers(3)), Vec::<String>::new());
            let n = 500;
            let srcs = [powers(n), powers(scaling::FACTOR * n)];
            scaling::check(
                "checking a top-level line of n powers that take f64",
                n,
                |m| {
                    type_errors(&srcs[usize::from(m != n)]);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_power_whose_exponent_is_no_int_takes_no_rat_in_any_place() {
    // At `rat`, `^` takes an `int` exponent alone (DESIGN.md sec:operators), so a `^` whose
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
