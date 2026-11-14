//! Two operands that each list values beside a part of one carrier, as `g(b, x) + g(b, x)`
//! with `g(b, x)` of type `1 | f64`: the operation is at that carrier, the one carrier of the
//! parts the operands hold whole, and every listed value of each operand, and a literal
//! beside them, is read at it (DESIGN.md step L1.26a, rule 3: "the literal `1` taking its
//! carrier where the result is used"). Where those parts are of two carriers, as `int` and
//! `f64`, the operation is refused as before. Item LIT-two-union-operands.
//!
//! An inline `if` whose decimal branches are literals with no suffix, read at `rat`, as
//! `h(if b { r } else { 2.5 })` with `h(positional z: rat)`: each such literal is exactly the
//! `rat` it writes, as alone at that parameter. A decimal a call gives, or one with a suffix,
//! is an `f64` and is still refused. Item LIT-if-decimal-at-rat.

use std::ffi::OsString;

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};

const G: &str = "g(positional c: bool, positional x: f64) = if c { x } else { 1 };\n\
                 gi(positional c: bool) = if c { 1 } else { 2 };\n\
                 gr(positional c: bool, positional r: rat) = if c { r } else { 1 };\n\
                 gd(positional c: bool) = if c { 1 } else { 2.5 };\n\
                 add(positional a, positional b) = a + b;\n\
                 h(positional z: f64) = z;\n\
                 hr(positional z: rat) = z;\n";

/// `G`, then `k(b, x, n, r) = <body>`, and `k` applied with `b` true and false as `t` and `f`,
/// `x` 2.5, `n` 3 and `r` 1/2.
fn with(body: &str) -> String {
    format!(
        "{G}k(positional b: bool, positional x: f64, positional n: int, positional r: rat) = {body};\n\
         t = k(true, 2.5f64, 3, 0.5r);\nf = k(false, 2.5f64, 3, 0.5r);\n"
    )
}

/// `body` is accepted, `k` gives `result`, and `k` with `b` true and false gives `t` and `f`.
fn accepted(body: &str, result: &str, t: &str, f: &str) {
    let src = with(body);
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{body}");
    assert_eq!(
        sig(&src, "k"),
        format!("(bool, f64, int, rat) -> {result}"),
        "{body}"
    );
    assert_eq!(
        (value(&src, "t").as_str(), value(&src, "f").as_str()),
        (t, f),
        "{body}"
    );
}

#[test]
fn two_operands_of_type_1_or_f64_are_read_at_f64() {
    // The item's own example, at each operator and word that takes two numbers.
    accepted("g(b, x) + g(b, x)", "f64", "5.0", "2.0");
    accepted("g(b, x) * g(b, x) + x", "f64", "8.75", "3.5");
    accepted("max(g(b, x), g(b, x))", "f64", "2.5", "1.0");
    accepted("h(g(b, x) + g(b, x))", "f64", "5.0", "2.0");
    accepted("g(b, x) / gi(b)", "f64", "2.5", "0.5");
    accepted("gi(b) + g(b, x) + gi(b)", "f64", "4.5", "5.0");
    // The comparisons give a `bool`, so they stand as the condition of an `if`.
    accepted(
        "h(if g(b, x) < g(!b, x) { 1.0f64 } else { 0.0f64 })",
        "f64",
        "0.0",
        "1.0",
    );
    accepted(
        "h(if g(b, x) == g(!b, x) { 1.0f64 } else { 0.0f64 })",
        "f64",
        "0.0",
        "0.0",
    );
    // A generic procedure of two operands, as the operator in it.
    accepted("add(g(b, x), g(b, x))", "f64", "5.0", "2.0");
}

#[test]
fn a_literal_beside_an_operand_of_type_1_or_f64_takes_f64() {
    accepted("g(b, x) + 2", "f64", "4.5", "3.0");
    accepted("g(b, x) + 2.5", "f64", "5.0", "3.5");
    accepted("g(b, x) - (if b { 1 } else { 2 })", "f64", "1.5", "-1.0");
}

#[test]
fn operands_of_type_1_or_rat_are_read_at_rat() {
    accepted("gr(b, r) + gr(b, r)", "rat", "1r", "2r");
    accepted("gr(b, r) + 0.5", "rat", "1r", "3r/2r");
}

#[test]
fn operands_of_listed_integers_alone_stay_int() {
    // No part of either operand is held whole, so nothing reads them: `int`, as before.
    accepted("gi(b) * gi(b)", "int", "1", "4");
}

#[test]
fn whole_parts_of_two_carriers_are_still_refused() {
    // `f64` and `int`, and `f64` and `rat`: no one carrier holds both.
    let errors = type_errors(&with("g(b, x) + n"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`+` does not take (f64, int)"),
        "{errors:?}"
    );
    let errors = type_errors(&with("g(b, x) + gr(b, r)"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].starts_with("`+` does not take ("), "{errors:?}");
}

/// The one error of `k` with the body `body`, with its menu and the text it stands at.
fn refused(body: &str) -> String {
    let errors = type_errors(&with(body));
    assert_eq!(errors.len(), 1, "{body}: {errors:?}");
    errors[0].clone()
}

#[test]
fn whole_parts_of_two_carriers_are_named_in_the_headline() {
    // The headline names the carriers each operand holds whole, `f64` and `rat`, at which
    // their listed `1`s are read, not the `1` a check of each value apart meets first; no
    // cast is offered, since neither `f64(r)` nor `rat(x)` is exact (item
    // LIT-two-union-headline).
    let no_arrow = |op: &str, shown: &str, at: &str| {
        format!("{op} does not take ({shown}): no arrow of {op} takes these types. [{at}]")
    };
    for (body, op, shown) in [
        ("g(b, x) + gr(b, r)", "`+`", "f64, rat"),
        ("gr(b, r) + g(b, x)", "`+`", "rat, f64"),
        ("g(b, x) - gr(b, r)", "`-`", "f64, rat"),
        ("g(b, x) + r", "`+`", "f64, rat"),
        ("x + gr(b, r)", "`+`", "f64, rat"),
        ("max(g(b, x), gr(b, r))", "`max`", "f64, rat"),
        ("add(g(b, x), gr(b, r))", "`add`", "f64, rat"),
    ] {
        assert_eq!(refused(body), no_arrow(op, shown, body), "{body}");
    }
    // An ordering gets the message of two numbers that do not compare, as `x < r` does.
    for (body, pair) in [
        ("g(b, x) < gr(b, r)", "g(b, x) : f64 < gr(b, r) : rat"),
        ("g(b, x) < r", "g(b, x) : f64 < r : rat"),
        ("x < gr(b, r)", "x : f64 < gr(b, r) : rat"),
    ] {
        assert_eq!(
            refused(body),
            format!("Cannot compare unequal types: `{pair}`. [{body}]"),
            "{body}"
        );
    }
    // Where a widening cast exists, it is still offered: `rat(n)` beside a `rat`.
    let r = Resolved::new(&with("gr(b, r) + n"));
    let errors = r.check().errors;
    assert_eq!(errors.len(), 1);
    assert_eq!(
        errors[0].message,
        "`+` does not take (rat, int): no arrow of `+` takes these types. Try `gr(b, r) + rat(n)` instead."
    );
    assert!(
        (errors[0].notes.iter())
            .any(|n| n.text == "repair: write `rat(n)`; the checker accepts that"),
        "{:?}",
        errors[0].notes
    );
}

const GB: &str = "gb(positional c: bool, positional x: f64) = if c { x } else { 9007199254740993 };\n\
                  gq(positional c: bool) = if c { 1 } else { 9007199254740993 };\n";

#[test]
fn an_integer_a_call_gives_with_no_exact_f64_is_named_in_the_headline() {
    // As the literal `9007199254740993` beside `g(b, x)` is: no `f64` equals it, whichever
    // operand gives the `f64` (item LIT-two-union-unread-wording).
    for (body, call) in [
        ("gb(b, x) + gb(b, x)", "gb(b, x)"),
        ("gq(b) + x", "gq(b)"),
        ("x * gq(b)", "gq(b)"),
        ("add(gb(b, x), gb(b, x))", "gb(b, x)"),
        ("h(gq(b))", "gq(b)"),
    ] {
        let errors = type_errors(&format!("{GB}{}", with(body)));
        assert_eq!(
            errors,
            [format!(
                "No `f64` equals 9007199254740993, which `{call}` may give. [{body}]"
            )],
            "{body}"
        );
    }
}

#[test]
fn an_integer_with_no_exact_f64_is_still_refused() {
    let errors = type_errors(&with("g(b, x) + 9007199254740993"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("No `f64` equals the literal `9007199254740993`."),
        "{errors:?}"
    );
}

#[test]
fn decimal_literals_of_an_inline_if_are_read_at_rat() {
    accepted("hr(if b { r } else { 2.5 })", "rat", "1r/2r", "5r/2r");
    accepted("hr(if b { 1 } else { 2.5 })", "rat", "1r", "5r/2r");
    // Exactly one tenth, not the `f64` nearest it; nested, and under `-`.
    accepted(
        "hr(if b { r } else { if b { 1 } else { 0.1 } })",
        "rat",
        "1r/2r",
        "1r/10r",
    );
    accepted("hr(if b { r } else { -0.1 })", "rat", "1r/2r", "-1r/10r");
    // Beside a `rat` operand, and at a generic procedure.
    accepted("r + (if b { r } else { 2.5 })", "rat", "1r", "3r");
    accepted("add(r, if b { r } else { 0.1 })", "rat", "1r", "3r/5r");
}

#[test]
fn a_decimal_from_a_call_or_with_a_suffix_is_still_refused_at_rat() {
    // `gd(b)` gives the `f64` 2.5, which no `rat` is read as.
    assert_eq!(
        type_errors(&with("hr(if b { gd(b) } else { 2.5 })")),
        [
            "`hr` does not take (1 | 2.5): the `if` may give the decimal 2.5, an `f64` where it \
             is written, and no `f64` is read as a `rat`. Write 2.5r where it is written, or \
             give this parameter of `hr` the type `f64`. Try \
             `hr(rat(if b { gd(b) } else { 2.5 }))` instead. [hr(if b { gd(b) } else { 2.5 })]"
        ]
    );
    // `1` and `2.5` each convert to a `rat` exactly, so that `rat(…)` gives no atom and `hr`
    // takes it (item CAST-literal-exact).
    assert!(type_errors(&with("hr(rat(if b { gd(b) } else { 2.5 }))")).is_empty());
    assert_eq!(
        type_errors(&with("hr(if b { r } else { 2.5f64 })")),
        [
            "`hr` does not take (2.5f64 | rat): the `if` may give the decimal 2.5, an `f64` \
             where it is written, and no `f64` is read as a `rat`. Write 2.5r where it is \
             written, or give this parameter of `hr` the type `f64`. \
             [hr(if b { r } else { 2.5f64 })]"
        ]
    );
}

const PROGRAM: &str = "\
g(positional c: bool, positional x: f64) = if c { x } else { 1 };
hr(positional z: rat) = z;
kr(positional b: bool, positional r: rat) = \"${hr(if b { r } else { 0.1 })} ${r + (if b { r } else { 2.5 })}\";

main(m: MainArgs) {
  x = f64(m.args[0] else \"\") else 0.0;
  b = x < 0.0;
  m.stdout <- \"${g(b, x) + g(b, x)} ${g(b, x) + 2} ${kr(b, if b { 1r } else { 3r })}\";
}
";

#[test]
fn the_executable_prints_the_interpreter_s_values() {
    let d = dir("two_union_operands");
    let src = d.join("two_union.zed");
    std::fs::write(&src, PROGRAM).unwrap();
    let exe = d.join("two_union");
    built(&src, &exe);
    for (x, want) in [
        ("-2.5", "-5.0 -0.5 1r 2r\n"),
        ("4.0", "2.0 3.0 1r/10r 11r/2r\n"),
    ] {
        let words: Vec<OsString> = vec!["--".into(), x.into()];
        let native = executable(&exe, &words, b"");
        assert_eq!(native, interpreter(&src, &words, b""), "{x}");
        assert_eq!((native.status, native.stdout.as_str()), (0, want), "{x}");
    }
}

/// `n` nested `if`s whose branches are, in turn, `x` and an integer literal: `f` returns
/// them, so its type lists about n/2 integers beside `f64`; `k` adds two calls of `f`, whose
/// pairs of values number about n²/4, and reads at `rat` an inline `if` of n branches, each a
/// decimal literal or `r`.
pub(super) fn nest(n: usize) -> String {
    let mut body = String::new();
    let mut decimals = String::new();
    for i in 0..n {
        let leaf = match i % 2 {
            0 => "x".to_string(),
            _ => format!("{i}"),
        };
        body += &format!("if c == {i} {{ {leaf} }} else ");
        let leaf = match i % 2 {
            0 => "r".to_string(),
            _ => format!("{i}.5"),
        };
        decimals += &format!("if c == {i} {{ {leaf} }} else ");
    }
    body += &format!("{{ {n} }}");
    decimals += &format!("{{ {n}.25 }}");
    format!(
        "{G}f(positional c: int, positional x: f64) = {body};\n\
         k(positional c: int, positional x: f64) = f(c, x) + f(c, x);\n\
         kr(positional c: int, positional r: rat) = hr({decimals});\n"
    )
}

#[test]
fn two_calls_of_many_listed_values_and_an_if_of_many_decimals_check() {
    // A small instance of the benchmark `bench::two_union_operands::scaling`.
    assert_eq!(type_errors(&nest(5)), Vec::<String>::new());
    assert_eq!(sig(&nest(5), "f"), "(int, f64) -> 1 | 3 | 5 | f64");
    assert_eq!(sig(&nest(5), "k"), "(int, f64) -> f64");
    assert_eq!(sig(&nest(5), "kr"), "(int, rat) -> rat");
}
