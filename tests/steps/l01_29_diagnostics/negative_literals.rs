//! A negative numeric literal is reported as written, `-3`, not `3`: a rejection points at
//! its `-`, and the message, the forms of its menu (DESIGN.md sec:lexical, integer literal,
//! and sec:domains), each derivation step that shows it and each use that narrowed a class
//! by it name the signed literal.

use super::{rejected, steps};

/// The first line of the rejection of `src`: the place and the message.
fn head(src: &str) -> String {
    rejected(src).lines().next().unwrap().to_string()
}

#[test]
fn a_negative_integer_at_a_float_parameter_is_rejected_at_its_minus() {
    let out = rejected("scale(positional x: f64) = x * 2.5;\ny = scale(-3);\n");
    assert_eq!(
        out,
        "2:11: `-3` is an int where `f64` is expected; a literal takes no other carrier; \
write `-3.0` or `-3n`
  [1] 1:1: `scale` is declared here, `(f64) -> f64`
      1 | scale(positional x: f64) = x * 2.5;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
    );
}

#[test]
fn each_menu_names_the_signed_forms_the_type_holds() {
    let menu = |lit: &str, own: &str, want: &str, forms: &str| {
        format!(
            "2:7: `{lit}` is {own} where `{want}` is expected; a literal takes no other carrier{forms}"
        )
    };
    let cases = [
        (
            "f64",
            "-3",
            menu("-3", "an int", "f64", "; write `-3.0` or `-3n`"),
        ),
        (
            "rat",
            "-3",
            menu("-3", "an int", "rat", "; write `-3r` or `-3n`"),
        ),
        (
            "f64 | rat",
            "-3",
            menu("-3", "an int", "rat | f64", "; write `-3.0` or `-3r`"),
        ),
        (
            "f64",
            "-0xFF",
            menu("-0xFF", "an int", "f64", "; write `-0xFFn`"),
        ),
        (
            "rat",
            "-2.5",
            menu("-2.5", "an f64", "rat", "; write `-2.5r`"),
        ),
        (
            "rat",
            "-3.0",
            menu("-3.0", "an f64", "rat", "; write `-3.0r`"),
        ),
        ("int", "-3.0", menu("-3.0", "an f64", "int", "")),
        (
            "f64 | rat",
            "-3n",
            "2:7: `-3n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and \
             f64; write the one meant, as `-3r` or `-3.0`"
                .to_string(),
        ),
        (
            "f64",
            "-9007199254740993n",
            "2:7: `-9007199254740993n` is not an f64: a literal written with `n` takes the carrier \
             expected only when it is exactly a number of that carrier, and no f64 is exactly \
             this number; write a literal that is exactly an f64, or write the number followed \
             by `r` if the exact rational is meant"
                .to_string(),
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(t, lit, want)| {
            let got = head(&format!("f(positional x: {t}) = x;\ny = f({lit});\n"));
            (got != *want).then(|| format!("{lit} at {t}:\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn an_operand_and_an_argument_at_a_fixed_class_point_at_the_minus() {
    // An operand of `+` at a declared f64, and an argument at a parameter that `== 0.5`
    // fixed at f64.
    assert_eq!(
        head("offset(positional x: f64) = x + -3;\n"),
        "1:33: `-3` is an int where `f64` is expected; a literal takes no other carrier; \
         write `-3.0` or `-3n`"
    );
    assert_eq!(
        head("isHalf(positional x) = x == 0.5;\ny = isHalf(-3);\n"),
        "2:12: `-3` is an int where `f64` is expected; a literal takes no other carrier; \
         write `-3.0` or `-3n`"
    );
}

#[test]
fn a_derivation_step_shows_the_negative_literal_as_written() {
    let out = rejected("f(positional x: f64) = x;\ny = f(-3 + 1);\n");
    assert!(
        out.contains("  [2] 2:7: this literal, -3, is -3\n"),
        "{out}"
    );
    // The line is shown once, under its first step; the literal's underline is labeled [2].
    assert!(
        out.contains(
            "      2 | y = f(-3 + 1);
        |     ^^^^^^^^^ [4]
        |       ^^ [2]
"
        ),
        "{out}"
    );
    let out = rejected("y = (-3, 1) + \"a\";\n");
    assert!(steps(&out).contains(&"this literal, -3, is -3"), "{out}");
    let out = rejected("f(positional x: String) = x;\ny = f(-3);\n");
    assert!(steps(&out).contains(&"this literal, -3, is -3"), "{out}");
}

#[test]
fn a_use_that_narrowed_a_class_names_the_negative_literal() {
    let out = rejected(
        "badge(positional x) = \"#\" ++ x * -2n;
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- badge(3);
}
",
    );
    assert!(
        out.contains("  [7] 1:34: the literal -2n takes int | f64 | rat\n"),
        "{out}"
    );
    // The line is shown once, under its first step; the literal's underline is labeled [5, 7].
    assert!(
        out.contains(
            "      1 | badge(positional x) = \"#\" ++ x * -2n;
        |       ^^^^^^^^^^^^ [4]       ^ [3]
        |                       ^^^ [1]    ^^^ [5, 7]
"
        ),
        "{out}"
    );
}

/// `n` negative integers at an `f64` parameter, and `n` compared by `==` with a parameter
/// whose class `0.5` fixed at f64: each is rejected at its `-`, `2 n` errors in all.
fn negatives(n: usize) -> String {
    let calls: String = (0..n).map(|i| format!("y{i} = f(-{i});\n")).collect();
    let tests: Vec<String> = (0..n).map(|i| format!("x == -{i}")).collect();
    format!(
        "f(positional x: f64) = x;\n{calls}g(positional x) = x == 0.5 || {};\n",
        tests.join(" || ")
    )
}

#[test]
fn rejecting_negative_literals_at_their_minus_scales() {
    use zed_tests::deep::statements;
    use zed_tests::scaling;
    let n = 256;
    // The inputs are built before the timing.
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let src = negatives(m);
            let stmts = statements(&src);
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, src, stmts, res)
        })
        .collect();
    scaling::on_a_thread(1 << 29, || {
        scaling::check_order(
            "rejecting n negative literals at a parameter and n compared with a class",
            n,
            1,
            |m| {
                let (_, src, stmts, res) = units.iter().find(|(k, _, _, _)| *k == m).unwrap();
                let info = zedc::check::walk::check(stmts, res);
                assert_eq!(info.errors.len(), 2 * m);
                assert!(
                    info.errors.iter().all(
                        |e| e.message.starts_with("`-") && src[e.span.start..].starts_with('-')
                    )
                );
            },
        );
    });
}
