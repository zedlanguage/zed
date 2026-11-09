//! A negative numeric literal is reported as written, `-2.5`, not `2.5`: a rejection points at
//! its `-`, and the message, the forms of its menu (DESIGN.md sec:lexical, integer literal,
//! and sec:domains), each derivation step that shows it and each use that narrowed a class
//! by it name the signed literal. A bare literal takes the carrier of its use (L1.26a,
//! L1.26b), so a negative one is rejected only where no carrier of its use can hold it.

use super::{rejected, steps};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// The first line of the rejection of `src`: the place and the message.
fn head(src: &str) -> String {
    rejected(src).lines().next().unwrap().to_string()
}

#[test]
fn a_negative_decimal_at_an_int_parameter_is_rejected_at_its_minus() {
    let out = rejected("scale(positional x: int) = x * 2;\ny = scale(-2.5);\n");
    assert_eq!(
        out,
        "2:11: the literal `-2.5` is a decimal, and `int` is expected here; a decimal literal is \
never an `int`
  [1] 1:1: `scale` is declared here with no type written for its result; the type the checker found \
for `scale` is `(int) -> int`
      1 | scale(positional x: int) = x * 2;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
    );
}

#[test]
fn a_negative_literal_a_carrier_holds_takes_it() {
    let f = |t: &str, lit: &str| value(&format!("f(positional x: {t}) = x;\ny = f({lit});\n"), "y");
    assert_eq!(f("f64", "-3"), "-3.0");
    assert_eq!(f("rat", "-3"), "-3r");
    assert_eq!(f("f64", "-0xFF"), "-255.0");
    assert_eq!(f("rat", "-2.5"), "-5r/2r");
    assert_eq!(f("rat", "-3.0"), "-3r");
}

#[test]
fn each_menu_names_the_signed_forms_the_type_holds() {
    let decimal_at_int = |lit: &str, forms: &str| {
        format!(
            "2:7: the literal `{lit}` is a decimal, and `int` is expected here; a decimal literal \
             is never an `int`{forms}"
        )
    };
    let two_carriers = |lit: &str, forms: &str| {
        format!(
            "2:7: the literal `{lit}` can be a `rat` or an `f64` at `rat | f64`, and nothing here \
             chooses one; write {forms}"
        )
    };
    let no_exact = |lit: &str, forms: &str| {
        format!(
            "2:7: the literal `{lit}` has no exact `f64`, and `f64` is expected here; an integer \
             literal takes a carrier only where it is exact{forms}"
        )
    };
    let cases = [
        ("int", "-2.5", decimal_at_int("-2.5", "")),
        (
            "int",
            "-3.0",
            decimal_at_int("-3.0", ", even when its value is an integer; write `-3`"),
        ),
        (
            "rat",
            "-2.5f64",
            "2:7: the literal `-2.5f64` is an `f64` by its suffix, and `rat` is expected here; a \
             suffix fixes a literal's carrier; write `-2.5r`"
                .to_string(),
        ),
        ("f64 | rat", "-3", two_carriers("-3", "`-3r` or `-3.0f64`")),
        (
            "f64 | rat",
            "-2.5",
            two_carriers("-2.5", "`-2.5r` or `-2.5f64`"),
        ),
        (
            "f64",
            "-9007199254740993",
            no_exact("-9007199254740993", "; write `-9007199254740992`"),
        ),
        // A literal in another base gets no decimal form.
        (
            "f64",
            "-0x20000000000001",
            no_exact("-0x20000000000001", ""),
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
    // An operand of `+` at a declared `int`, and an argument at a parameter that `div` fixed
    // at `int`.
    assert_eq!(
        head("offset(positional x: int) = x + -2.5;\n"),
        "1:33: the literal `-2.5` is a decimal, and `+` expects `int`, the carrier of `x`; a \
         decimal literal is never an `int`; write `f64(x) + -2.5`"
    );
    assert_eq!(
        head("isTwo(positional x) = x div 2 == 1;\ny = isTwo(-2.5);\n"),
        "2:11: the literal `-2.5` is a decimal, and `int` is expected here; a decimal literal is \
         never an `int`"
    );
}

#[test]
fn a_derivation_step_shows_the_negative_literal_as_written() {
    let out = rejected("f(positional x: int) = x;\ny = f(-3 + 1.5);\n");
    assert!(
        out.contains("  [2] 2:7: this literal, -3, is -3\n"),
        "{out}"
    );
    // The line is shown once, under its first step; the literal's underline is labeled [2].
    assert!(
        out.contains(
            "      2 | y = f(-3 + 1.5);
        |     ^^^^^^^^^^^ [4]
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
        "badge(positional x) = \"#\" ++ x * -2;
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- badge(3);
}
",
    );
    assert!(
        out.contains("  [7] 1:34: the literal -2 takes int | f64 | rat\n"),
        "{out}"
    );
    // The line is shown once, under its first step; the literal's underline is labeled [5, 7].
    assert!(
        out.contains(
            "      1 | badge(positional x) = \"#\" ++ x * -2;
        |       ^^^^^^^^^^^^ [4]       ^ [3]
        |                       ^^^ [1]    ^^ [5, 7]
"
        ),
        "{out}"
    );
}

/// `n` negative decimals at an `int` parameter, and `n` compared by `==` with a parameter
/// whose class `div` fixed at `int`: each is rejected at its `-`, `2 n` errors in all.
fn negatives(n: usize) -> String {
    let calls: String = (0..n).map(|i| format!("y{i} = f(-{i}.5);\n")).collect();
    let tests: Vec<String> = (0..n).map(|i| format!("x == -{i}.5")).collect();
    format!(
        "f(positional x: int) = x;\n{calls}g(positional x) = x div 2 == 0 || {};\n",
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
                assert!(info.errors.iter().all(|e| {
                    e.message.starts_with("the literal `-") && src[e.span.start..].starts_with('-')
                }));
            },
        );
    });
}
