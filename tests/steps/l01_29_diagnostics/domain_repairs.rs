//! The repairs of a value that may lie outside the ints its use takes, and of a value a
//! `Lines` port does not take, are the program's own code (MSG-domain-repairs-v): each names
//! the program's expression and never a value `v` the program does not have, and never a
//! refinement such as `is int[0..]`, which this zedc does not compile. Each repair the headline
//! offers is written into the program, and the program it gives is accepted.

use zed_tests::scaling;
use zedc::run::load;

/// `src` with a `main` added where it declares none, so that `load` checks its functions.
fn program(src: &str) -> String {
    match src.contains("main(m: MainArgs)") {
        true => src.to_string(),
        false => format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"a\";\n}}\n"),
    }
}

/// The rendered diagnostics of `src`, which must be rejected.
fn rejected(src: &str) -> String {
    super::rejected(&program(src))
}

/// Asserts that `src` checks.
fn checks(src: &str) {
    let src = program(src);
    load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}\n{e}"));
}

/// The repair the headline of `out` ends with, as in "Try `r` instead".
fn tried(out: &str) -> Option<&str> {
    let first = out.lines().next()?;
    let (_, rest) = first.split_once(" Try `")?;
    Some(&rest[..rest.find("` instead")?])
}

/// That no part of `out` names a value the program does not have or a refinement.
fn in_the_programs_words(out: &str) {
    assert!(!out.contains("`v`"), "{out}");
    assert!(!out.contains("${v}"), "{out}");
    assert!(!out.contains(" is int["), "{out}");
    assert!(!out.contains(": int[0.."), "{out}");
}

/// `src` with its one `call` replaced by the repair `r`, the branch left open filled with 0,
/// as a block where it binds a name (a block of one `if` alone would read as a set display).
fn repaired(src: &str, call: &str, r: &str) -> String {
    assert_eq!(src.matches(call).count(), 1, "{src}");
    let r = r.replace('…', "0");
    match r.contains(';') {
        true => src.replace(call, &format!("{{ {r} }}")),
        false => src.replace(call, &format!("({r})")),
    }
}

#[test]
fn a_tested_repair_holds_the_programs_code_and_is_accepted() {
    let cases = [
        // A name a test narrows is tested itself.
        (
            "f(positional n: int) = popCount(n);\n",
            "popCount(n)",
            "if n >= 0 { popCount(n) } else { … }",
        ),
        // An expression is bound to the parameter's name.
        (
            "f(positional n: int) = popCount(n - 1);\n",
            "popCount(n - 1)",
            "x = n - 1; if x >= 0 { popCount(x) } else { … }",
        ),
        // `x = x - 1` would define `x` in terms of itself, and `x = n - x` would read the new
        // `x`: the name takes the least number from 2 that the call does not write.
        (
            "f(positional x: int) = popCount(x - 1);\n",
            "popCount(x - 1)",
            "x2 = x - 1; if x2 >= 0 { popCount(x2) } else { … }",
        ),
        (
            "f(positional n: int) = { x = 3; x2 = 4; popCount(n - x - x2) };\n",
            "popCount(n - x - x2)",
            "x3 = n - x - x2; if x3 >= 0 { popCount(x3) } else { … }",
        ),
        // A width takes the operand below `2^width` as well.
        (
            "f(positional n: int) = bitNot(n, width: 8);\n",
            "bitNot(n, width: 8)",
            "if n >= 0 && n < 2^8 { bitNot(n, width: 8) } else { … }",
        ),
        (
            "f(positional n: int) = bitNot(n - 1, width: 8);\n",
            "bitNot(n - 1, width: 8)",
            "x = n - 1; if x >= 0 && x < 2^8 { bitNot(x, width: 8) } else { … }",
        ),
        // The call of a function whose parameter reaches a bit word.
        (
            "g(positional k) = popCount(k);\nf(positional n: int) = g(n + 2);\n",
            "g(n + 2)",
            "k = n + 2; if k >= 0 { g(k) } else { … }",
        ),
        // An int read from the input.
        (
            "main(m: MainArgs) {\n  m.stdout <- String(popCount(int(m.stdin[0]) else 0));\n}\n",
            "popCount(int(m.stdin[0]) else 0)",
            "x = int(m.stdin[0]) else 0; if x >= 0 { popCount(x) } else { … }",
        ),
        // The power's own repair names its value apart from the names the power writes.
        (
            "f(positional exponent: int) = 2^(exponent - 1);\n",
            "2^(exponent - 1)",
            "exponent2 = exponent - 1; if exponent2 >= 0 { 2^exponent2 } else { … }",
        ),
    ];
    for (src, call, want) in cases {
        let out = rejected(src);
        in_the_programs_words(&out);
        assert_eq!(tried(&out), Some(want), "{src}\n{out}");
        let fixed = repaired(src, call, want);
        checks(&fixed);
    }
}

#[test]
fn a_width_test_of_the_lower_bound_alone_is_not_enough() {
    // The control for the two-sided test above: with `n < 2^8` dropped, the repair would be
    // rejected again, since 256 is not below `2^8`.
    let fixed = "f(positional n: int) = if n >= 0 { bitNot(n, width: 8) } else { 0 };\n";
    let out = rejected(fixed);
    assert!(
        out.contains("`bitNot` takes `x` in int[0..<2^width]"),
        "{out}"
    );
}

#[test]
fn no_test_is_offered_where_no_value_or_no_test_of_the_operand_fits() {
    for src in [
        // No value of `-1` lies in int[0..], so a test of it would leave nothing to pass.
        "x = popCount(-1);\n",
        // A funnel shift's `k` lies below the width, not below `2^width`, and the width read
        // as the operand's digits bounds the width itself: no test of the operand alone fits.
        "f(positional n: int) = funnelShl(1, 2, n, width: 8);\n",
        "f(positional n: int) = bitNot(5, width: n);\n",
    ] {
        let out = rejected(src);
        in_the_programs_words(&out);
        assert!(
            out.lines().next().unwrap().contains(" takes `"),
            "{src}\n{out}"
        );
        assert_eq!(tried(&out), None, "{src}\n{out}");
    }
    // The control: the test a nonnegative operand takes, written for `k`, is rejected.
    let out = rejected(
        "f(positional n: int) = if n >= 0 && n < 2^8 { funnelShl(1, 2, n, width: 8) } else { 0 };\n",
    );
    assert!(out.contains("`funnelShl` takes `k`"), "{out}");
}

#[test]
fn a_generic_operand_names_its_expression_and_the_parameters_to_declare() {
    let out = rejected("f(positional x) = popCount(x);\ng(positional y) = f(y + 1);\n");
    in_the_programs_words(&out);
    assert_eq!(
        tried(&out),
        Some("x = y + 1; if x >= 0 { … } else { … }"),
        "{out}"
    );
    assert!(
        out.lines().next().unwrap().ends_with(
            "instead, with each parameter in `y + 1` declared `int` and `x` passed inside the \
             branch."
        ),
        "{out}"
    );
    // The repair as the headline says it: `y` declared `int` and `x` passed inside the branch.
    let fixed = "f(positional x) = popCount(x);\n\
                 g(positional y: int) = { x = y + 1; if x >= 0 { f(x) } else { 0 } };\n";
    checks(fixed);
}

/// A program that reads a line into `t` with `bind` and pushes `t` to the output.
fn pushing(bind: &str) -> String {
    format!("main(m: MainArgs) {{\n  {bind}\n  m.stdout <- t;\n}}\n")
}

#[test]
fn a_lines_port_repair_writes_the_programs_value() {
    for (bind, line) in [
        // An int: written into a string.
        ("t = int(m.stdin[0]) else 0;", "m.stdout <- \"${t}\";"),
        // A string that may be an atom: an empty line in place of each atom.
        ("t = m.stdin[0];", "m.stdout <- t else \"\";"),
        // An int that may be an atom: both.
        ("t = int(m.stdin[0]);", "m.stdout <- \"${t}\" else \"\";"),
    ] {
        let src = pushing(bind);
        let out = rejected(&src);
        in_the_programs_words(&out);
        assert!(out.contains(&format!(", as `{line}`")), "{src}\n{out}");
        let fixed = src.replace("m.stdout <- t;", line);
        checks(&fixed);
    }
    // The control for the catch-all: an `else` for one atom of several leaves the others, and
    // the port still refuses the value.
    let out = rejected(
        &pushing("t = m.stdin[0];")
            .replace("m.stdout <- t;", "m.stdout <- t else #outOfBounds -> \"\";"),
    );
    assert!(out.contains("a `Lines` port takes"), "{out}");
}

/// A function that binds `x2` to `x{n+1}` and passes `x` less all of them to `popCount`, so
/// that the repair's name is the first of `n + 2` numbers the call does not write.
fn crowded(n: usize) -> String {
    let names: Vec<String> = (2..n + 2).map(|i| format!("x{i}")).collect();
    let binds: String = names.iter().map(|x| format!("  {x} = 1;\n")).collect();
    format!(
        "f(positional x: int) = {{\n{binds}  popCount(x - {})\n}};\n",
        names.join(" - ")
    )
}

#[test]
fn naming_the_repairs_value_takes_time_linear_in_the_call() {
    // Each number tried is looked up among the call's words, collected once (COMPLEXITY.md,
    // `fresh`): trying each against the call's text afresh is quadratic in the names.
    scaling::check(
        "the name of a repair among n names the call writes",
        1000,
        |n| {
            let out = rejected(&crowded(n));
            let first = out.lines().next().expect("a message");
            assert!(
                first.contains(&format!("Try `x{} = x - ", n + 2)),
                "{first}"
            );
        },
    );
}
