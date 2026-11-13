//! A decimal literal with no suffix is rejected wherever nothing gives it a carrier (DESIGN.md
//! L1.26b, "Where nothing fixes its carrier a decimal literal is rejected"), in the places item
//! LIT-tuple-rest adds to those of item MSG-literal-tuple: a tuple passed to `min` or `max`, the
//! payload of an atom in a call's argument, a part of a tuple display that reaches a variable
//! the display's other parts fix nothing for, the branches of an `if`, the value of a block,
//! the body of a called function (DESIGN.md L1.26a, "`y = g(c)` is rejected at the `2.5`,
//! which nothing fixes"), an indexed tuple display, and a string hole that holds any of these.
//! Several decimals of one value are rejected in one message, which prints their line once:
//! the bytes printed grow with the line, not with its square. A literal that a carrier reaches
//! stays accepted: `x: 1r` gives the `2` of `p: (2, 1)` its carrier in `f(x, p) = x + p[0]`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

/// The rejection of the one decimal literal `lit` that nothing gives a carrier, whose fixes
/// write it as an `f64`, the line `f64`, and as a `rat`, the line `rat`, each naming the value
/// the literal then is; `call` names the function whose body holds the literal, where the
/// value holds it through a call.
pub(super) fn unfixed(lit: &str, f64: &str, rat: &str, call: Option<&str>) -> String {
    let through = call.map_or(String::new(), |c| {
        format!("; the value holds it through a call of `{c}`")
    });
    let w = f64.len().max(rat.len()) + 4;
    format!(
        "Nothing gives the literal `{lit}` a carrier{through}. Try `{}` instead.\n  fixes, each checked here:\n    \
         {f64:w$}the literal is then the f64 {lit}\n    {rat:w$}the literal is then exactly {lit}, \
         a rat [{lit}]",
        f64.trim_end_matches(';')
    )
}

/// Each fix of the one rejection of `src`, written as `f64` and as `rat`, gives a program with
/// no error: `src` with its line `old` replaced by the fix.
pub(super) fn fixes_check(src: &str, old: &str, fixes: [&str; 2]) {
    for fix in fixes {
        let fixed = src.replace(old, fix);
        assert_ne!(fixed, src, "{old:?} is not a line of {src:?}");
        assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
    }
}

#[test]
fn a_decimal_in_a_tuple_passed_to_min_or_max_is_rejected() {
    // As `min(0.5, 1)` is: the other tuple's `1` gives the `0.5` no carrier.
    for (word, old, f64, rat) in [
        (
            "min",
            "x = min((0.5, 1), (1, 2));",
            "x = min((0.5f64, 1), (1, 2));",
            "x = min((0.5r, 1), (1, 2));",
        ),
        (
            "max",
            "x = max((1, 2), (0.5, 1));",
            "x = max((1, 2), (0.5f64, 1));",
            "x = max((1, 2), (0.5r, 1));",
        ),
    ] {
        let src = format!("{old}\n");
        assert_eq!(
            type_errors(&src),
            [unfixed("0.5", f64, rat, None)],
            "{word}"
        );
        fixes_check(&src, old, [f64, rat]);
    }
    assert_eq!(value("x = min((0.5f64, 1), (1, 2));\n", "x"), "(0.5, 1)");
    // The `1` compared with `0.5r` takes its carrier; the `2` meets only `1` and stays `int`.
    assert_eq!(value("x = max((1, 2), (0.5r, 1));\n", "x"), "(1r, 2)");
}

#[test]
fn a_decimal_in_a_payload_of_an_argument_is_rejected() {
    let src = "id(x) = x;\ny = id(x: #bad(0.5));\n";
    let (f64, rat) = ("y = id(x: #bad(0.5f64));", "y = id(x: #bad(0.5r));");
    assert_eq!(type_errors(src), [unfixed("0.5", f64, rat, None)]);
    fixes_check(src, "y = id(x: #bad(0.5));", [f64, rat]);
    assert_eq!(
        value("id(x) = x;\ny = id(x: #bad(0.5r));\n", "y"),
        "#bad(1r/2r)"
    );
}

#[test]
fn the_parts_of_a_tuple_that_reach_one_variable_fix_nothing_for_each_other() {
    // The display reaches `x` whole, and its components are apart: the `0.5f64` gives the
    // second `0.5` no carrier.
    let src = "id(x) = x;\ny = id(x: (0.5f64, 0.5));\n";
    let (f64, rat) = ("y = id(x: (0.5f64, 0.5f64));", "y = id(x: (0.5f64, 0.5r));");
    assert_eq!(type_errors(src), [unfixed("0.5", f64, rat, None)]);
    assert_eq!(rejected_at(src), [src.rfind("0.5)").unwrap()]);
    fixes_check(src, "y = id(x: (0.5f64, 0.5));", [f64, rat]);
    assert_eq!(
        value("id(x) = x;\ny = id(x: (0.5f64, 0.5r));\n", "y"),
        "(0.5, 1r/2r)"
    );
}

/// The byte offset of each rejection of `src`.
fn rejected_at(src: &str) -> Vec<usize> {
    let r = Resolved::new(src);
    r.check().errors.iter().map(|e| e.span.start).collect()
}

#[test]
fn an_argument_of_a_carrier_fixes_the_literals_of_a_tuple_part() {
    // `x: 1r` reaches `p[0]` through `+`: the `2`, and a decimal there, are `rat`s.
    let f = "f(x, p) = x + p[0];\n";
    for (call, v) in [
        ("y = f(x: 1r, p: (2, 1));", "3r"),
        ("y = f(x: 1r, p: (0.5, 1));", "3r/2r"),
        ("y = f(x: 1.0f64, p: (2, 1));", "3.0"),
    ] {
        let src = format!("{f}{call}\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{call}");
        assert_eq!(value(&src, "y"), v, "{call}");
    }
}

#[test]
fn a_decimal_bound_to_several_names_through_a_call_or_an_if_is_rejected() {
    let src = "id(x) = x;\na, b = id(x: (0.5, 1));\n";
    let (f64, rat) = ("a, b = id(x: (0.5f64, 1));", "a, b = id(x: (0.5r, 1));");
    assert_eq!(type_errors(src), [unfixed("0.5", f64, rat, None)]);
    fixes_check(src, "a, b = id(x: (0.5, 1));", [f64, rat]);
    let src = "c = true;\na, b = if c { (0.5, 1) } else { (1, 2) };\n";
    let (f64, rat) = (
        "a, b = if c { (0.5f64, 1) } else { (1, 2) };",
        "a, b = if c { (0.5r, 1) } else { (1, 2) };",
    );
    assert_eq!(type_errors(src), [unfixed("0.5", f64, rat, None)]);
    fixes_check(src, "a, b = if c { (0.5, 1) } else { (1, 2) };", [f64, rat]);
}

#[test]
fn a_decimal_a_branch_or_a_block_ends_in_is_rejected() {
    let cases = [
        (
            "y = if c { 0.5 } else { 1 };",
            "y = if c { 0.5f64 } else { 1 };",
            "y = if c { 0.5r } else { 1 };",
        ),
        (
            "y = if c { (0.5, 1) } else { (1, 1) };",
            "y = if c { (0.5f64, 1) } else { (1, 1) };",
            "y = if c { (0.5r, 1) } else { (1, 1) };",
        ),
        (
            "y = if c { #bad(0.5) } else { 1 };",
            "y = if c { #bad(0.5f64) } else { 1 };",
            "y = if c { #bad(0.5r) } else { 1 };",
        ),
        (
            "y = (if c { 0.5 } else { 1 }, 2);",
            "y = (if c { 0.5f64 } else { 1 }, 2);",
            "y = (if c { 0.5r } else { 1 }, 2);",
        ),
        (
            "y = { q = 1; (q, 0.5) };",
            "y = { q = 1; (q, 0.5f64) };",
            "y = { q = 1; (q, 0.5r) };",
        ),
        // A component that the index does not select is rejected all the same: nothing
        // gives it a carrier, wherever it stands.
        (
            "y = (0.5, 1)[1];",
            "y = (0.5f64, 1)[1];",
            "y = (0.5r, 1)[1];",
        ),
    ];
    for (old, f64, rat) in cases {
        let src = format!("c = true;\n{old}\n");
        assert_eq!(type_errors(&src), [unfixed("0.5", f64, rat, None)], "{old}");
        fixes_check(&src, old, [f64, rat]);
    }
    assert_eq!(
        value("c = true;\ny = if c { 0.5r } else { 1 };\n", "y"),
        "1r/2r"
    );
}

#[test]
fn a_decimal_a_string_hole_ends_in_is_rejected() {
    let cases = [
        (
            "y = \"a${(0.5, 1)[0]}\";",
            "y = \"a${(0.5f64, 1)[0]}\";",
            "y = \"a${(0.5r, 1)[0]}\";",
        ),
        (
            "y = \"${if c { 0.5 } else { 1 }}\";",
            "y = \"${if c { 0.5f64 } else { 1 }}\";",
            "y = \"${if c { 0.5r } else { 1 }}\";",
        ),
    ];
    for (old, f64, rat) in cases {
        let src = format!("c = true;\n{old}\n");
        assert_eq!(type_errors(&src), [unfixed("0.5", f64, rat, None)], "{old}");
        fixes_check(&src, old, [f64, rat]);
    }
    assert_eq!(
        value("c = true;\ny = \"a${(0.5r, 1)[0]}\";\n", "y"),
        "\"a1r/2r\""
    );
}

#[test]
fn a_decimal_a_called_function_returns_is_rejected() {
    // DESIGN.md L1.26a: "`g(positional c: bool) = if c { 1 } else { 2.5 }` is `(bool) -> 1 |
    // 2.5`, ... and `y = g(c)` is rejected at the `2.5`, which nothing fixes".
    let g = "g(positional c: bool) = if c { 1 } else { 2.5 };";
    let src = format!("{g}\nc = true;\ny = g(c);\n");
    assert_eq!(sig(&src, "g"), "(bool) -> 1 | 2.5");
    let (f64, rat) = (
        "g(positional c: bool) = if c { 1 } else { 2.5f64 };",
        "g(positional c: bool) = if c { 1 } else { 2.5r };",
    );
    assert_eq!(type_errors(&src), [unfixed("2.5", f64, rat, Some("g"))]);
    fixes_check(&src, g, [f64, rat]);
    // A body that is the decimal, one that returns it in a tuple, one that calls a function
    // that returns it, and bodies that return it in a payload, which nothing fixes, as at
    // `y = #bad(0.5)`: the message names the call the value is bound to.
    for (defs, call, name) in [
        ("f() = 0.5;\n", "y = f();", "f"),
        ("f(x: int) = (x, 0.5);\n", "y = f(x: 1);", "f"),
        ("f() = 0.5;\ng() = f();\n", "y = g();", "g"),
        ("f() = #bad(0.5);\n", "y = f();", "f"),
        ("f() = (1, #bad(0.5));\n", "y = f();", "f"),
        (
            "f(positional c: bool) = if c { #bad(0.5) } else { #ok };\n",
            "y = f(true);",
            "f",
        ),
        (
            "f(x) = if x > 0 { #bad(x) } else { #bad(0.5) };\n",
            "y = f(x: 1.0f64);",
            "f",
        ),
    ] {
        let src = format!("{defs}{call}\n");
        let line = defs.lines().next().unwrap();
        let f64 = line.replace("0.5", "0.5f64");
        let rat = line.replace("0.5", "0.5r");
        assert_eq!(
            type_errors(&src),
            [unfixed("0.5", &f64, &rat, Some(name))],
            "{src}"
        );
        fixes_check(&src, line, [&f64, &rat]);
    }
    assert_eq!(value("f() = 0.5r;\ny = f();\n", "y"), "1r/2r");
    assert_eq!(value("f() = #bad(0.5r);\ny = f();\n", "y"), "#bad(1r/2r)");
}

#[test]
fn a_binding_of_a_call_with_a_literal_argument_keeps_no_unfixed_decimal() {
    // Item LIT-unfixed-decimal-binding, the program of its note: `y = g(true)` with `g` of type
    // `(bool) -> 1 | 2.5` was accepted as `1`. DESIGN.md L1.26a: "`y = g(c)` is rejected at the
    // `2.5`, which nothing fixes". The argument's value does not matter: the type of `g(true)`
    // is the type of `g`'s result, which keeps the `2.5`.
    let g = "g(positional c: bool) = if c { 1 } else { 2.5 };";
    let (f64, rat) = (
        "g(positional c: bool) = if c { 1 } else { 2.5f64 };",
        "g(positional c: bool) = if c { 1 } else { 2.5r };",
    );
    for (defs, call, name) in [
        ("", "y = g(true);", "g"),
        ("", "y = g(false);", "g"),
        // Through a nested call: the message names the call the value is bound to, and the
        // fixes still rewrite the line that writes the decimal.
        ("k(positional c: bool) = g(c);\n", "y = k(true);", "k"),
        (
            "k(positional c: bool) = g(c);\nm(positional c: bool) = k(c);\n",
            "y = m(false);",
            "m",
        ),
    ] {
        let src = format!("{g}\n{defs}{call}\n");
        assert_eq!(
            type_errors(&src),
            [unfixed("2.5", f64, rat, Some(name))],
            "{src}"
        );
        fixes_check(&src, g, [f64, rat]);
    }
    // The fixes give these values: the `1` meets no carrier and is the `int` 1, and the
    // decimal is the carrier its suffix names.
    let at = |line: &str, call: &str| format!("{line}\n{call}\n");
    assert_eq!(value(&at(f64, "y = g(true);"), "y"), "1");
    assert_eq!(value(&at(f64, "y = g(false);"), "y"), "2.5");
    assert_eq!(value(&at(rat, "y = g(false);"), "y"), "5r/2r");
    // A carrier at the use fixes both values, so nothing is rejected: an `f64` parameter
    // reads the `1` as 1.0. (A declared binding, `y: f64 = g(true);`, is the other fix DESIGN
    // names; this zedc does not compile a declared binding yet.)
    let fixed = format!("{g}\nh(positional z: f64) = z;\na = h(g(true));\nb = h(g(false));\n");
    assert_eq!(type_errors(&fixed), Vec::<String>::new());
    assert_eq!(value(&fixed, "a"), "1.0");
    assert_eq!(value(&fixed, "b"), "2.5");
}

#[test]
fn a_decimal_a_call_gives_a_carrier_stays_accepted() {
    // The literal has a suffix; it joins the class of the parameter, which the argument
    // fixes; and it joins the class beside an atom the other branch may give.
    let cases = [
        ("f() = 0.5f64;\ny = f();\n", "0.5"),
        ("f() = #bad(0.5f64);\ny = f();\n", "#bad(0.5)"),
        ("f(x) = #bad(x);\ny = f(x: 1.0f64);\n", "#bad(1.0)"),
        (
            "g(x) = if x > 0 { x } else { 0.5 };\ny = g(x: 1.0f64);\n",
            "1.0",
        ),
        (
            "g(x) = if x > 0 { x } else { 0.5 };\ny = g(x: -1r);\n",
            "1r/2r",
        ),
        (
            "f(positional x) = if x > 0 { 1 / x } else { -1.5 };\ny = f(2r);\n",
            "1r/2r",
        ),
    ];
    for (src, v) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), v, "{src}");
    }
}

#[test]
fn a_literal_branch_joins_a_class_beside_atoms() {
    // DESIGN.md L1.26a: a literal joins the class of a parameter "as a branch of an `if` whose
    // other branch is of a class"; the other branch may also give `#divByZero`.
    assert_eq!(
        sig("f(positional x) = if x > 0 { 1 / x } else { -1.5 };\n", "f"),
        "(T) -> T | #divByZero for T in f32 | f64 | rat"
    );
    assert_eq!(
        sig(
            "f(positional x) = if x > 0 { x / x } else { 1 + 1 };\n",
            "f"
        ),
        "(T) -> T | #divByZero for T in f32 | f64 | rat"
    );
}

#[test]
fn the_decimals_a_value_ends_in_are_rejected_in_one_message() {
    let src = "c = true;\ny = (if c { 0.5 } else { 1 }, if c { 0.25 } else { 2 });\n";
    assert_eq!(
        type_errors(src),
        [
            "2 parts of the value of `y` are literals that nothing here gives a carrier, and Zed \
             does not choose one for them; the steps below give each one. Try `y = (if c { 0.5f64 \
             } else { 1 }, if c { 0.25f64 } else { 2 })` instead.\n  fixes, each checked \
             here:\n    y = (if c { 0.5f64 } else { 1 }, if c { 0.25f64 } else { 2 });    the \
             literal is then the f64 0.5; the literal is then the f64 0.25\n    y = (if c { 0.5r } \
             else { 1 }, if c { 0.25r } else { 2 });        the literal is then exactly 0.5, a \
             rat; the literal is then exactly 0.25, a rat [0.5]"
        ]
    );
    let old = "y = (if c { 0.5 } else { 1 }, if c { 0.25 } else { 2 });";
    fixes_check(
        src,
        old,
        [
            "y = (if c { 0.5f64 } else { 1 }, if c { 0.25f64 } else { 2 });",
            "y = (if c { 0.5r } else { 1 }, if c { 0.25r } else { 2 });",
        ],
    );
}

/// `y = (0.5, 1.5, …);`, `n` decimals on one line.
fn decimals(n: usize) -> String {
    let parts: Vec<String> = (0..n).map(|i| format!("{i}.5")).collect();
    format!("y = ({});\n", parts.join(", "))
}

/// The diagnostics `zedc` prints for `src`, which it rejects.
fn printed(src: &str) -> String {
    zedc::run::load(src.as_bytes()).err().expect("rejected")
}

#[test]
fn many_decimals_on_one_line_print_the_line_once() {
    // Negative control (run once, not committed): one message for each decimal, each quoting
    // the line, as before this item, printed 16.2 times the bytes for 4 times the decimals
    // (964335 bytes for n = 200, 15605535 for 800), and failed the bound below. One message
    // prints 4.0 times (zedc: 51340 bytes for 200, 207641 for 800).
    scaling::on_a_thread(1 << 28, || {
        let n = 200;
        let out: Vec<usize> = [n, 4 * n].map(|m| printed(&decimals(m)).len()).into();
        let ratio = out[1] as f64 / out[0] as f64;
        assert!(
            ratio < 5.0,
            "{n} decimals print {} bytes, {} print {}: {ratio:.1} times",
            out[0],
            4 * n,
            out[1]
        );
        assert_eq!(
            printed(&decimals(n)).matches(&decimals(n)[..20]).count(),
            1,
            "the line is printed once"
        );
        let units = scaling::inputs(n, decimals);
        scaling::check_order(
            "printing the rejection of n decimals on one line",
            n,
            1,
            |m| {
                std::hint::black_box(printed(&units[&m]));
            },
        );
    });
}

/// A chain of `n` functions, each returning a call of the one before, the first returning
/// `0.5`, and `n` bindings, each a call of the last.
fn chain(n: usize) -> String {
    let mut src = String::from("c0() = 0.5;\n");
    for k in 1..=n {
        src += &format!("c{k}() = c{}();\n", k - 1);
    }
    for i in 0..n {
        src += &format!("y{i} = c{n}();\n");
    }
    src
}

#[test]
fn many_calls_of_a_long_chain_check_in_linear_time() {
    scaling::on_a_thread(1 << 28, || {
        let errors = type_errors(&chain(2));
        assert_eq!(errors.len(), 1, "{errors:?}");
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&chain(m)));
        scaling::check(
            "checking n calls of a chain of n functions that returns a decimal",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
