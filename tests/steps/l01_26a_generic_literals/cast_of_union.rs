//! A cast of a call whose type lists literal values (item LIT-cast-of-literal-union). With
//! `g(positional c: bool) = if c { 1 } else { 2.5f64 }`, `f64(g(c))` takes the `1` at the
//! `int` arrow of `f64` and the `2.5` at its `f64` arrow, as `f64(if c { 1 } else { 2.5f64 })`
//! does; it was rejected because the `int` arrow, which reads nothing, was the one arrow kept.
//! With the `2.5` written with no suffix, nothing gives it a carrier at a cast, whose arrows
//! take both `f64` and `rat`, so the call is rejected at the `2.5`, as `f64(0.5)` is (DESIGN.md
//! L1.26b: "Where nothing fixes its carrier a decimal literal is rejected"), and so is an `if`
//! of literals there. A value with no arrow of the cast, `true`, is still rejected, and named.
//! Each repair a rejection offers checks as written: a wrap is tried as the checker applies
//! it where it is written, so `int(g(c))`, which the unfixed `2.5` makes fail, is not offered,
//! nor is `int(b)` where `b` is the String `"x"`, which always fails. `String`, which takes
//! every carrier, gives none either: `String(g(c))` is rejected at the `2.5`, as `String(0.5)`
//! is.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, info, type_errors};

use super::tuple_rest::{fixes_check, unfixed};

const FORCED: &str = "g(positional c: bool) = if c { 1 } else { 2.5f64 };";
const BARE: &str = "g(positional c: bool) = if c { 1 } else { 2.5 };";
const RAT: &str = "g(positional c: bool) = if c { 1 } else { 2.5r };";

/// The type of `y` in `src`, which checks with no error.
fn y_type(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    let (i, _) = info(src);
    i.tops.get("y").expect("a binding `y`").to_string()
}

/// Every repair the rejections of `src` offer, each written into `src`: a wrap,
/// "wrap this in `w(…)`", puts `w(` and `)` around the place it names, and "write `t`" puts
/// `t` in its place. Each gives a program with no error.
fn repairs_check(src: &str) -> usize {
    let (i, _) = info(src);
    let mut n = 0;
    for e in &i.errors {
        for note in &e.notes {
            let at = &src[note.span.start..note.span.end];
            let text = if let Some(w) = note.text.strip_prefix("repair: wrap this in `") {
                let w = w.split_once("(…)`").expect("a wrap names its word").0;
                format!("{w}({at})")
            } else if let Some(t) = note.text.strip_prefix("repair: write `") {
                t.split_once('`')
                    .expect("a rewrite in backquotes")
                    .0
                    .to_string()
            } else {
                continue;
            };
            let fixed = format!("{}{text}{}", &src[..note.span.start], &src[note.span.end..]);
            assert_eq!(
                type_errors(&fixed),
                Vec::<String>::new(),
                "{}: {fixed}",
                note.text
            );
            n += 1;
        }
    }
    n
}

#[test]
fn a_cast_takes_each_value_of_a_call_at_its_own_arrow() {
    // The case of the item: `f64` has arrows at `int` and at `f64`, and each value has one.
    for (c, f, i) in [("true", "1.0", "1"), ("false", "2.5", "#inexact")] {
        let src = format!("{FORCED}\ny = f64(g({c}));\n");
        assert_eq!(y_type(&src), "f64");
        assert_eq!(value(&src, "y"), f);
        let src = format!("{FORCED}\ny = int(g({c}));\n");
        assert_eq!(y_type(&src), "int | #inexact | #invalid");
        assert_eq!(value(&src, "y"), i);
    }
    // As the `if` itself is, and as a `rat` value is at the `rat` arrow.
    assert_eq!(y_type("y = f64(if true { 1 } else { 2.5f64 });\n"), "f64");
    let src = format!("{RAT}\ny = f64(g(false));\n");
    assert_eq!(y_type(&src), "f64 | #inexact");
    assert_eq!(value(&src, "y"), "2.5");
    // Integer values alone stay at the `int` arrow, as before; an `int` within ±2^53 casts exactly.
    let src = "g(positional c: bool) = if c { 1 } else { 2 };\ny = f64(g(false));\n";
    assert_eq!(y_type(src), "f64");
    assert_eq!(value(src, "y"), "2.0");
}

#[test]
fn a_call_beside_an_operand_of_one_carrier_is_still_read_at_it() {
    // The `1` of `g(c)` has no `f64` arrow of `+` to itself: it is read at `f64`.
    let src = format!("{FORCED}\ny = 1.0f64 + g(true);\n");
    assert_eq!(y_type(&src), "f64");
    assert_eq!(value(&src, "y"), "2.0");
    let src = format!("{BARE}\nx = 2.0f64;\ny = x * g(true);\n");
    assert_eq!(y_type(&src), "f64");
    assert_eq!(value(&src, "y"), "2.0");
    let src = format!("{FORCED}\nh(positional z: f64) = z;\ny = h(g(true));\n");
    assert_eq!(y_type(&src), "f64");
    assert_eq!(value(&src, "y"), "1.0");
}

#[test]
fn a_cast_gives_no_carrier_to_a_decimal_a_call_returns() {
    let (f64, rat) = (FORCED, RAT);
    for word in ["f64", "int", "abs", "String"] {
        let src = format!("{BARE}\ny = {word}(g(true));\n");
        assert_eq!(
            type_errors(&src),
            [unfixed("2.5", f64, rat, Some("g"))],
            "{word}"
        );
        fixes_check(&src, BARE, [f64, rat]);
    }
    // Beside an integer literal, which fixes nothing either, one message names the decimal.
    let src = format!("{BARE}\ny = 1 + g(true);\n");
    assert_eq!(type_errors(&src), [unfixed("2.5", f64, rat, Some("g"))]);
    // Inside a function too: its result fixes nothing for the `2.5` in `g`.
    let src = format!("{BARE}\nk(positional d: bool) = f64(g(d));\n");
    assert_eq!(type_errors(&src), [unfixed("2.5", f64, rat, Some("g"))]);
    fixes_check(&src, BARE, [f64, rat]);
    // A decimal that joins a parameter's class takes the carrier the call gives it there.
    let src = "g(positional c: bool, positional x) = if c { x } else { 0.5 };\n\
               k(positional d: bool) = f64(g(d, 1.0f64));\ny = k(false);\n";
    assert_eq!(y_type(src), "f64");
    assert_eq!(value(src, "y"), "0.5");
}

#[test]
fn a_cast_gives_no_carrier_to_a_decimal_branch() {
    for word in ["f64", "abs", "String"] {
        let old = format!("y = {word}(if true {{ 1 }} else {{ 2.5 }});");
        let f64 = format!("y = {word}(if true {{ 1 }} else {{ 2.5f64 }});");
        let rat = format!("y = {word}(if true {{ 1 }} else {{ 2.5r }});");
        let src = format!("{old}\n");
        assert_eq!(
            type_errors(&src),
            [unfixed("2.5", &f64, &rat, None)],
            "{word}"
        );
        fixes_check(&src, &old, [&f64, &rat]);
    }
    // An integer literal is an `int` there, as alone.
    assert_eq!(y_type("y = f64(if true { 1 } else { 2 });\n"), "f64");
}

#[test]
fn a_value_no_arrow_of_the_cast_takes_is_rejected_and_named() {
    let g = "g(positional c: bool) = if c { 1 } else { true };";
    for word in ["f64", "int"] {
        let src = format!("{g}\ny = {word}(g(true));\n");
        assert_eq!(
            type_errors(&src),
            [format!(
                "`{word}` does not take (true): no arrow of `{word}` takes these types. [{word}(g(true))]"
            )]
        );
        // The one repair, a wrap in `String`, checks.
        assert_eq!(repairs_check(&src), 1, "{src}");
    }
}

#[test]
fn every_repair_offered_checks_as_written() {
    // `scalar` takes an `int`. `int(g(true))` is rejected at the `2.5`, so it is not offered;
    // the type alone, whose values `1` and `2.5` each have an arrow of `int`, said it checks.
    let src = format!("{BARE}\ny = scalar(g(true));\n");
    let (i, _) = info(&src);
    assert!(!i.errors.is_empty(), "{src}");
    assert_eq!(repairs_check(&src), 0, "{src}");
    // With the suffix `int(g(true))` checks. Whether it is offered is not pinned: it can give
    // `#inexact`, and a cast that can fail is not to be offered (author, 2026-11-12; follow-up
    // MSG-concise-style). Whatever is offered checks.
    let src = format!("{FORCED}\ny = scalar(g(true));\n");
    repairs_check(&src);
    assert!(type_errors(&format!("{FORCED}\ny = scalar(int(g(true)));\n")).is_empty());
    // `String` takes every carrier, so it gives the `2.5` none: `String(g(true))` is rejected
    // as `String(0.5)` is, and the wrap in `String` is offered only with the suffix.
    let src = format!("{BARE}\nh(positional z: String) = z;\ny = h(g(true));\n");
    assert_eq!(repairs_check(&src), 0, "{src}");
    let src = format!("{FORCED}\nh(positional z: String) = z;\ny = h(g(true));\n");
    assert_eq!(repairs_check(&src), 1, "{src}");
    // A call of type `1 | f64` beside an `f64`: whatever is offered checks (the count is not
    // pinned, as above).
    let src = "g(positional c: bool, positional x: f64) = if c { x } else { 1 };\n\
               y = 1.0f64 + g(false, 2.5f64);\n";
    repairs_check(src);
    // A wrap that always fails is not offered: `int(b)` with `b` the String "x".
    let src = "p = (1, \"x\");\na, b = p;\nc = a + b;\n";
    assert_eq!(repairs_check(src), 0, "{src}");
    assert_eq!(
        type_errors("p = (1, \"x\");\na, b = p;\nc = a + int(b);\n"),
        [
            "`int` here always fails: its operand `\"x\"` gives `#invalid`, so this call never \
          gives a value. [int(b)]"
        ]
    );
}

/// A function `g` of `values` branches, each giving an integer, and one more giving `2.5`
/// written `last`, and `casts` bindings each casting a call of it with `word`.
fn many(values: usize, casts: usize, last: &str, word: &str) -> String {
    let mut src = String::from("g(positional k: int) = if k == 0 { 0 }");
    for i in 1..values {
        src += &format!(" else if k == {i} {{ {i} }}");
    }
    src += &format!(" else {{ {last} }};\n");
    for i in 0..casts {
        src += &format!("y{i} = {word}(g({i}));\n");
    }
    src
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time() {
    // A cast splits the values of the call among the arrows, or reads the body for the `2.5`,
    // or tries the four wraps as written: linear in the values, at each cast.
    scaling::on_a_thread(1 << 28, || {
        assert!(type_errors(&many(3, 3, "2.5f64", "f64")).is_empty());
        assert_eq!(
            type_errors(&many(3, 3, "2.5", "f64")).len(),
            1,
            "one literal, one error"
        );
        assert_eq!(type_errors(&many(3, 3, "2.5", "scalar")).len(), 3);
        let n = 200;
        for (last, word) in [("2.5f64", "f64"), ("2.5", "f64"), ("2.5", "scalar")] {
            let units = scaling::inputs(n, |m| Resolved::new(&many(m, 1, last, word)));
            scaling::check(
                &format!("checking `{word}(g(0))`, `g` of n values and {last}"),
                n,
                |m| {
                    units[&m].check();
                },
            );
            let units = scaling::inputs(n, |m| Resolved::new(&many(2, m, last, word)));
            scaling::check(
                &format!("checking n casts `{word}(g(k))`, `g` of two values and {last}"),
                n,
                |m| {
                    units[&m].check();
                },
            );
        }
    });
}
