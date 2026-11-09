//! Type soundness (DESIGN.md rule 4): a program the checker accepts never meets a kernel type
//! error at run time. Each program here once passed the checker and then failed in the kernel;
//! each is now rejected before it runs, and each control, its well-typed twin, still runs.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Lookup;
use zedc::run::load;

/// What one wave of the program `src` writes to `stdout` on `stdin`, or its run error.
fn run(src: &str, stdin: &str) -> String {
    let p = load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}: rejected: {e}"));
    let mut lines = BTreeMap::new();
    lines.insert("stdin".to_string(), Arc::from(stdin.as_bytes()));
    let files = |_: &str| -> Arc<dyn Lookup> { unreachable!("no `Files` port") };
    match p.run(&lines, files) {
        Ok(w) => w
            .writes
            .iter()
            .map(|(_, b)| String::from_utf8_lossy(b).into_owned())
            .collect(),
        Err(e) => format!("error: {e}"),
    }
}

/// Checks that the program with these definitions and this `stdout` expression is rejected.
fn rejected(defs: &str, out: &str) {
    let src = format!("{defs}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- {out};\n}}\n");
    if let Ok(p) = load(src.as_bytes()) {
        let _ = p;
        panic!(
            "accepted, and on input 7 it gives {:?}:\n{src}",
            run(&src, "7")
        );
    }
}

/// The program with these definitions and this `stdout` expression, run on `stdin`.
fn runs(defs: &str, out: &str, stdin: &str) -> String {
    let src = format!("{defs}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- {out};\n}}\n");
    run(&src, stdin)
}

const FIRST: &str = "first(positional p) = p[0];";
const APP: &str = "app(positional f) = f(1);";
const EQ: &str = "eq(positional a, positional b) = a == b;";
const INC: &str = "inc(positional x) = x + 1;";

#[test]
fn a_tuple_index_of_a_non_tuple_is_rejected() {
    rejected(FIRST, r#""${first(5)}""#);
    assert_eq!(runs(FIRST, r#""${first((5, 6))}""#, ""), "5\n");
}

#[test]
fn a_call_of_a_non_function_is_rejected() {
    rejected(APP, r#""${app(5)}""#);
    assert_eq!(runs(APP, r#""${app(x -> x + 1)}""#, ""), "2\n");
}

#[test]
fn a_function_argument_of_the_wrong_arity_is_rejected() {
    rejected(
        "f(positional x: int, positional y: int) = x + y;\ng(positional h) = h(1);",
        r#""${g(f)}""#,
    );
    rejected(
        "g(positional h) = h(1, 2);\ninc(positional x: int) = x + 1;",
        r#""${g(inc)}""#,
    );
}

#[test]
fn a_lambda_parameter_must_take_what_it_is_passed() {
    rejected(
        "app(positional f) = f(\"a\");",
        r#""${app((x: int) -> x + 1)}""#,
    );
    assert_eq!(runs(APP, r#""${app((x: int) -> x + 1)}""#, ""), "2\n");
}

#[test]
fn functions_are_not_compared_with_equals() {
    rejected(&format!("{EQ}\n{INC}"), r#""${eq(inc, inc)}""#);
    rejected(INC, r#""${inc == inc}""#);
    assert_eq!(runs(EQ, r#""${eq(1, 1)}""#, ""), "true\n");
}

#[test]
fn one_bounded_variable_takes_one_carrier() {
    let add = "add(positional a, positional b) = a + b;\nk(positional x: int) = x;";
    rejected(add, r#""${add(k(3), 2.5)}""#);
    assert_eq!(runs(add, r#""${add(k(3), 4)}""#, ""), "7\n");
}

#[test]
fn a_comparison_of_two_kinds_is_rejected() {
    rejected(
        "lt(positional a, positional b) = a < b;",
        r#""${lt(1, "b")}""#,
    );
    rejected("", r#""${(1, "a") < ("b", 2)}""#);
    rejected(INC, r#""${(inc, 1) < (inc, 2)}""#);
    assert_eq!(runs("", r#""${(1, "a") < (1, "b")}""#, ""), "true\n");
}

#[test]
fn a_line_of_a_lines_port_is_a_string_or_an_error() {
    rejected("", r#""${stdin[1] + 1}""#);
    assert_eq!(runs("", r#""${len(stdin[1]) else 0}""#, "abc"), "3\n");
}

#[test]
fn an_int_power_needs_an_exponent_of_at_least_zero() {
    rejected("", r#""${2 ^ -1}""#);
    rejected("", r#""${(2 ^ (int(stdin[1]) else 0)) div 1}""#);
    assert_eq!(runs("", r#""${2 ^ 3}""#, ""), "8\n");
}

#[test]
fn a_prelude_word_takes_its_number_of_arguments() {
    rejected("", r#""${len("ab", "c") + 1}""#);
}

#[test]
fn a_function_is_not_shown_and_not_put_in_a_tuple() {
    rejected(INC, r#""${inc}""#);
    rejected(INC, "String(inc)");
    rejected(INC, r#""${(inc, 1)[1]}""#);
    rejected(
        &format!("pair(positional a, positional b) = (a, b);\n{INC}"),
        r#""${pair(inc, 2)[1]}""#,
    );
}

#[test]
fn a_lambda_is_checked_at_each_call() {
    rejected("", r#""${(x -> x + 1)("a")}""#);
    assert_eq!(runs("", r#""${(x -> x + 1)(2)}""#, ""), "3\n");
    let f = "f = x -> x[0];";
    rejected(f, r#""${f(5)}""#);
    assert_eq!(runs(f, r#""${f((5, 6))}""#, ""), "5\n");
}

#[test]
fn a_need_passes_through_a_generic_call() {
    let hg = "h(positional t: (int, int)) = t[0];\ng(positional t) = h(t);";
    rejected(hg, r#""${g(5)}""#);
    rejected(hg, r#""${g((1, "x"))}""#);
    assert_eq!(runs(hg, r#""${g((1, 2))}""#, ""), "1\n");
    let ka = format!("{APP}\nk(positional g) = app(g);");
    rejected(&ka, r#""${k(5)}""#);
    assert_eq!(runs(&ka, r#""${k(x -> x * 2)}""#, ""), "2\n");
    let m = "map2(positional f, positional t) = (f(t[0]), f(t[1]));";
    rejected(m, r#""${map2(x -> x + 1, (1, "a"))}""#);
    assert_eq!(runs(m, r#""${map2(x -> x + 1, (1, 2))}""#, ""), "(2, 3)\n");
}

#[test]
fn the_results_of_two_uses_under_one_bound_take_one_carrier() {
    let h = "h(positional t) = t[0] + t[1];";
    let k = format!("{h}\nk(positional t) = h(t);\nr(positional x: f64) = x;");
    let cat = "h(positional t) = t[0] ++ t[1];";
    rejected(h, r#""${h((1, 2.5))}""#);
    rejected(&k, r#""${k((1, r(2.5)))}""#);
    rejected(cat, r#""${h(("a", 2))}""#);
    assert_eq!(runs(h, r#""${h((1, 2))}""#, ""), "3\n");
    assert_eq!(runs(&k, r#""${k((r(1.5), r(2.5)))}""#, ""), "4.0\n");
    assert_eq!(runs(cat, r#""${h(("a", "b"))}""#, ""), "ab\n");
    // What a use gives joins a variable an argument binds too.
    let f = "f(positional c: bool, positional t, positional x) = if c { t[0] } else { x };";
    assert_eq!(runs(f, r#""${f(true, (1, 2), "a")}""#, ""), "1\n");
}

#[test]
fn a_function_applied_to_itself_is_checked_once() {
    // `w(w)` meets the need of `w` again inside its own check, on the same type: it holds.
    let src = "w(positional f) = f(f);\nspin = w(w);\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n";
    if let Err(e) = load(src.as_bytes()) {
        panic!("{src}: rejected: {e}");
    }
    rejected("w(positional f) = f(f);", r#""${w(5)}""#);
}

/// The program with these definitions and this body of `main`.
fn program(defs: &str, body: &str) -> String {
    format!("{defs}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  {body}\n}}\n")
}

/// Checks that the program `src` is rejected.
fn refused(src: &str) {
    if load(src.as_bytes()).is_ok() {
        panic!(
            "accepted, and on input 7 it gives {:?}:\n{src}",
            run(src, "7")
        );
    }
}

#[test]
fn a_section_or_a_curried_call_checks_what_it_leaves_out_when_it_is_called() {
    let add = "add(positional a, positional b) = a + b;";
    assert_eq!(
        run(&program(add, r#"f = add[1]; stdout <- "${f(2)}";"#), ""),
        "3\n"
    );
    refused(&program(add, r#"f = add[1]; stdout <- "${f("x")}";"#));
    let first = "first(positional t, positional u) = t[0];";
    refused(&program(first, r#"f = first[5]; stdout <- "${f(1)}";"#));
    let pick = "pick(positional t, positional i) = t[i];";
    // A tuple takes a computed key (DESIGN.md sec:types, the `m[k]` row), so `f(0)` reads
    // the first component; the key `5` selects none, which the call checks.
    assert_eq!(
        run(
            &program(pick, r#"f = pick[(1, 2)]; stdout <- "${f(0)}";"#),
            ""
        ),
        "1\n"
    );
    refused(&program(pick, r#"f = pick[(1, 2)]; stdout <- "${f(5)}";"#));
    let greet = r#"greet(positional name, punct = "!", lead = "hi") = "${lead}, ${name}${punct}";"#;
    let body = r#"h = greet("Al", lead: "yo", ...); stdout <- h(punct: "?");"#;
    assert_eq!(run(&program(greet, body), ""), "yo, Al?\n");
    refused(&program(
        greet,
        r#"h = greet("Al", lead: "yo", ...); stdout <- h(punct: 5);"#,
    ));
}

#[test]
fn a_returned_function_carries_the_needs_of_its_parameters() {
    let defs = "inc = x -> x + 1;\n\
                compose(positional f, positional g) = x -> f(g(x));\n\
                twice(positional f) = compose(f, f);\n\
                len2(positional s) = len(s);";
    assert_eq!(
        run(&program(defs, r#"stdout <- "${twice(inc)(3)}";"#), ""),
        "5\n"
    );
    refused(&program(defs, r#"stdout <- "${twice(inc)("a")}";"#));
    refused(&program(defs, r#"stdout <- "${twice(len2)("abc")}";"#));
    let bang = r#"h = twice(x -> x ++ "!"); stdout <- h("a");"#;
    assert_eq!(run(&program(defs, bang), ""), "a!!\n");
    let ok = r#"h = compose(x -> x * 2, x -> x + 1); stdout <- "${h(4)}";"#;
    assert_eq!(run(&program(defs, ok), ""), "10\n");
    refused(&program(
        defs,
        r#"h = compose(x -> x * 2, x -> x ++ "s"); stdout <- "${h("a")}";"#,
    ));
}

#[test]
fn a_name_an_else_pattern_binds_has_the_type_of_its_payload() {
    let parse =
        r#"parse(positional text) = if text == "" { #parseError(line: 1, col: 0) } else { 42 };"#;
    let both = r#"both = parse("") else #parseError(line:, col:) -> line * 100 + col; stdout <- "${both}" else "?";"#;
    assert_eq!(run(&program(parse, both), ""), "100\n");
    let wrap = "wrap(positional v) = #w(v: v);";
    let five = r#"r = wrap(5) else #w(v:) -> v + 1; stdout <- "${r}" else "?";"#;
    assert_eq!(run(&program(wrap, five), ""), "6\n");
    refused(&program(
        wrap,
        r#"r = wrap("a") else #w(v:) -> v + 1; stdout <- "${r}";"#,
    ));
    refused(&program(
        "",
        r#"r = #e(x: "a") else #e(x:) -> x + 1; stdout <- "${r}";"#,
    ));
    // Of two shapes, the name has the union of both.
    let pick = r#"pick(positional c: bool) = if c { #e(x: 1) } else { #e(x: "a") };"#;
    refused(&program(
        pick,
        r#"r = pick(true) else #e(x:) -> x + 1; stdout <- "${r}";"#,
    ));
    let pick = "pick(positional c: bool) = if c { #e(x: 1) } else { #e(x: 2, y: 3) };";
    let y = r#"r = pick(false) else #e(y:) -> y + 1; stdout <- "${r}" else "?";"#;
    assert_eq!(run(&program(pick, y), ""), "4\n");
    let nested = r#"r = #o(i: #e(x: 2)) else #o(i: #e(x:)) -> x * 3; stdout <- "${r}" else "?";"#;
    assert_eq!(run(&program("", nested), ""), "6\n");
    let v = "v = #e(code: 5) else #e(code:) -> code;";
    assert_eq!(
        run(&program(v, r#"stdout <- String(v + 1) else "z";"#), ""),
        "6\n"
    );
    refused(&program(
        &format!("{FIRST}\n{v}"),
        r#"stdout <- String(first(v)) else "z";"#,
    ));
    refused(&program(v, r#"stdout <- String(v ++ "a") else "z";"#));
    refused(&program(
        &format!("{APP}\n{v}"),
        r#"stdout <- String(app(v)) else "z";"#,
    ));
}

#[test]
fn a_generic_else_pattern_binds_the_payload_each_call_passes() {
    let g = "g(positional e) = e else #e(code:) -> code;";
    assert_eq!(
        run(
            &program(g, r#"stdout <- String(g(#e(code: 5)) + 1) else "z";"#),
            ""
        ),
        "6\n"
    );
    assert_eq!(
        run(&program(g, r#"stdout <- String(g(3) + 1) else "z";"#), ""),
        "4\n"
    );
    refused(&program(
        g,
        r#"stdout <- String(g(#e(code: "a")) + 1) else "z";"#,
    ));
    refused(&program(
        &format!("{g}\n{FIRST}"),
        r#"stdout <- String(first(g(#e(code: 5)))) else "z";"#,
    ));
    let h = "h(positional e) = e else #o(i: #e(x:)) -> x;";
    assert_eq!(
        run(
            &program(h, r#"stdout <- String(h(#o(i: #e(x: 2))) * 3) else "z";"#),
            ""
        ),
        "6\n"
    );
    refused(&program(
        h,
        r#"stdout <- String(h(#o(i: #e(x: "s"))) * 3) else "z";"#,
    ));
}

#[test]
fn a_self_application_takes_the_least_settled_result() {
    // Inside `w(w)` the inner use first gives nothing; the outer then gives 1, which settles.
    let settles = "w(positional f) = if true { 1 } else { f(f) + 1 };\nspin = w(w);";
    assert_eq!(
        run(&program(settles, r#"stdout <- String(spin) else "z";"#), ""),
        "1\n"
    );
    // Here the inner use must give a string, and the outer gives 1 | String: not settled.
    let grows = "w(positional f) = if true { 1 } else { f(f) ++ \"a\" };\nspin = w(w);";
    refused(&program(grows, r#"stdout <- "x";"#));
}

/// `f` takes a pair and gives its first component; `g` passes its argument on to `f`; `pick`
/// gives a pair or `5`.
const PAIR: &str = "f(positional p) {\n  a, b = p;\n  return a;\n}\n\
                    g(positional x) = f(x);\n\
                    pick(positional c: bool) = if c { (1, 2) } else { 5 };";

/// The error that rejects the program with `PAIR` whose `stdout` is `"int"` or `"other"` as
/// the value of `call` is an `int` or not. The `is` test takes a value of any type, so only the
/// destructuring can reject the program.
fn kind_refused(call: &str) -> String {
    let src = program(
        PAIR,
        &format!(r#"stdout <- if {call} is int {{ "int" }} else {{ "other" }};"#),
    );
    match load(src.as_bytes()) {
        Ok(_) => panic!(
            "accepted, and on input 7 it gives {:?}:\n{src}",
            run(&src, "7")
        ),
        Err(e) => e.to_string(),
    }
}

#[test]
fn a_destructured_parameter_takes_only_a_tuple_of_its_length() {
    // Each was accepted, and failed at run time: `type error: TupleGet applied to int, int`.
    for (call, given) in [
        ("f(5)", "5"),
        ("f((1, 2, 3))", "(1, 2, 3)"),
        ("f(pick(true))", "5"),
    ] {
        let e = kind_refused(call);
        assert!(
            e.contains(&format!("this value is {given}, not a tuple of 2")),
            "{e}"
        );
        assert!(e.contains("`f` needs this of its argument here"), "{e}");
        assert!(e.contains("a, b = p;"), "{e}");
    }
    // Through a function that passes its argument on, the need is `g`'s.
    let e = kind_refused("g(5)");
    assert!(e.contains("this value is 5, not a tuple of 2"), "{e}");
    assert!(e.contains("`g` needs this of its argument here"), "{e}");
    // A pair passes, of any component types, and gives its first component's type.
    let is = r#"stdout <- if f((1, 2)) is int { "int" } else { "other" };"#;
    assert_eq!(run(&program(PAIR, is), ""), "int\n");
    let is = r#"stdout <- if g(("x", 2)) is int { "int" } else { "other" };"#;
    assert_eq!(run(&program(PAIR, is), ""), "other\n");
    assert_eq!(runs(PAIR, r#""${f((1, "x"))}""#, ""), "1\n");
}

#[test]
fn a_tuple_default_used_as_a_number_is_rejected() {
    // The default `(x, 1)` flows a tuple into the class of `y`, which then takes no carrier
    // `+` takes.
    let f = "f(positional x, y = (x, 1)) = y + 1;";
    assert_eq!(
        super::type_errors(f),
        [
            "`+` does not take (_, 1): these are the types of its arguments here, and `+` has no arrow that takes them all [y + 1]"
        ]
    );
    rejected(f, r#"String(f(1)) else "atom""#);
    let ok = "f(positional x, y = x) = y + 1;";
    assert_eq!(runs(ok, r#"String(f(1)) else "atom""#, ""), "2\n");
}

#[test]
fn a_tuple_default_of_a_nested_function_used_as_a_number_is_rejected() {
    let outer =
        "outer(positional x) = {\n  inner(positional y, w = (y, 1)) = w + 1;\n  inner(x)\n};";
    assert_eq!(
        super::type_errors(outer),
        [
            "`+` does not take (_, 1): these are the types of its arguments here, and `+` has no arrow that takes them all [w + 1]"
        ]
    );
    rejected(outer, r#"String(outer(1)) else "atom""#);
    let ok = "outer(positional x) = {\n  inner(positional y, w = y) = w + 1;\n  inner(x)\n};";
    assert_eq!(runs(ok, r#"String(outer(1)) else "atom""#, ""), "2\n");
}
