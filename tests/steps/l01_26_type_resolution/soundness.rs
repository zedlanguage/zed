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
    lines.insert("m.stdin".to_string(), Arc::from(stdin.as_bytes()));
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

/// The diagnostics of the program with these definitions and this `stdout` expression, which
/// must be rejected.
fn rejected(defs: &str, out: &str) -> String {
    let src = format!("{defs}\nmain(m: MainArgs) {{\n  m.stdout <- {out};\n}}\n");
    match load(src.as_bytes()) {
        Err(e) => e,
        Ok(_) => panic!(
            "accepted, and on input 7 it gives {:?}:\n{src}",
            run(&src, "7")
        ),
    }
}

/// The program with these definitions and this `stdout` expression, run on `stdin`.
fn runs(defs: &str, out: &str, stdin: &str) -> String {
    let src = format!("{defs}\nmain(m: MainArgs) {{\n  m.stdout <- {out};\n}}\n");
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
    rejected("", r#""${m.stdin[0] + 1}""#);
    assert_eq!(runs("", r#""${len(m.stdin[0]) else 0}""#, "abc"), "3\n");
}

#[test]
fn an_int_power_needs_an_exponent_of_at_least_zero() {
    rejected("", r#""${2^-1}""#);
    rejected("", r#""${(2^(int(m.stdin[0]) else 0)) div 1}""#);
    assert_eq!(runs("", r#""${2^3}""#, ""), "8\n");
}

#[test]
fn an_int_power_rejection_shows_the_negative_exponent() {
    let out = rejected("", r#""${2^-1}""#);
    // The first line names the exponent, in the power's code annotated with types.
    assert!(
        out.contains(
            "Int power with a negative exponent: `2 : int ^ -1 : int`. Try `2.0f64^-1` instead."
        ),
        "{out}"
    );
    assert!(out.contains("the base `2` is int here"), "{out}");
    assert!(!out.contains("`v"), "{out}");
    // Each repair is the power rewritten in full, and each runs.
    for fix in ["2.0f64^-1", "2^-1.0"] {
        assert!(out.contains(&format!("repair: `{fix}`")), "{out}");
        assert_eq!(runs("", &format!(r#""${{{fix}}}""#), ""), "0.5\n");
    }
    // The exact `rat` power, last (POW-rat).
    assert!(out.contains("repair: `2r^-1`"), "{out}");
    assert_eq!(runs("", r#""${2r^-1}""#, ""), "1r/2r\n");
    // Every value of the exponent is below 0, so no test of it is offered.
    assert!(!out.contains("repair: `if"), "{out}");
}

/// The diagnostics of the program whose `main` has the body `body` after `defs`, which must
/// be rejected, and the program with `body` in place of the fixes in `fixed`, each run on
/// its input with the output it must give. No repair names a value the program does not
/// have, and none casts an int to a float, a cast that may fail with `#inexact`.
fn power_case(defs: &str, body: &str, fixed: &[(&str, &str, &str)]) -> String {
    let main = |body: &str| format!("{defs}\nmain(m: MainArgs) {{\n{body}\n}}\n");
    let src = main(body);
    let out = match load(src.as_bytes()) {
        Err(e) => e,
        Ok(_) => panic!("accepted:\n{src}"),
    };
    assert!(!out.contains("`v"), "{out}");
    assert!(!out.contains("`n: int[0..]`"), "{out}");
    assert!(!out.contains("f64("), "{out}");
    for (b, stdin, want) in fixed {
        assert_eq!(run(&main(b), stdin), *want, "{b}");
    }
    out
}

/// An int power under a negative exponent through a name (POW-rat): `2.0f64^k` is no repair,
/// as `k` is an int, and `f64(k)` or `f64(x)` may fail with `#inexact`, so the one repair is
/// the exact `rat` power, `2r^k` for a literal base and `rat(x)^-1` for a name, each printed
/// as the headline's `Try`, and each runs to `1r/2r` as printed. Before, neither had a repair.
#[test]
fn an_int_power_rejection_through_a_name_shows_its_value() {
    let out = power_case(
        "",
        "  k = -1;\n  m.stdout <- \"${2^k}\";",
        &[("  k = -1;\n  m.stdout <- \"${2r^k}\";", "", "1r/2r\n")],
    );
    assert_eq!(
        out,
        r#"4:18: Int power with a negative exponent: `2 : int ^ k : -1`. Try `2r^k` instead.
  [1] 4:20: `k` is -1 here
      4 |   m.stdout <- "${2^k}";
        |                  ^^^ [5]
        |                    ^ [1]
  [2] 3:7: `k` is defined as this expression, -1
      3 |   k = -1;
        |       ^^ [2, 3]
        |        ^ [4]
  [3] 3:7: this `-` gives -1
  [4] 3:8: this literal, 1, is 1
  [5] 4:18: repair: `2r^k`"#
    );
    // A name of the top level, the same.
    let top = rejected("k = -1;", r#""${2^k}""#);
    assert!(
        top.contains("`2 : int ^ k : -1`. Try `2r^k` instead."),
        "{top}"
    );
    assert_eq!(runs("k = -1;", r#""${2r^k}""#, ""), "1r/2r\n");
    // An int base that is a name: its derivation, and `rat(x)`, a cast that cannot fail.
    let out = power_case(
        "",
        "  x = 2;\n  m.stdout <- \"${x^-1}\";",
        &[("  x = 2;\n  m.stdout <- \"${rat(x)^-1}\";", "", "1r/2r\n")],
    );
    assert_eq!(
        out,
        r#"4:18: Int power with a negative exponent: `x : 2 ^ -1 : int`. Try `rat(x)^-1` instead.
  [1] 4:18: `x` is 2 here
      4 |   m.stdout <- "${x^-1}";
        |                  ^ [1]
        |                  ^^^^ [4]
  [2] 3:7: `x` is defined as this expression, 2
      3 |   x = 2;
        |       ^
  [3] 3:7: this expression is 2
  [4] 4:18: repair: `rat(x)^-1`"#
    );
}

#[test]
fn an_int_power_rejection_through_an_expression_shows_its_derivation() {
    let out = rejected("", r#""${2^(1 - 3)}""#);
    assert!(
        out.contains("Int power with an exponent that may be negative: `2 : int ^ (1 - 3) : int`. Try `2.0f64^(1 - 3)` instead."),
        "{out}"
    );
    assert!(out.contains("this `-` gives int"), "{out}");
    assert!(out.contains("repair: `2.0f64^(1 - 3)`"), "{out}");
    assert!(!out.contains("`v"), "{out}");
    assert_eq!(runs("", r#""${2.0f64^(1 - 3)}""#, ""), "0.25\n");
    // An expression of an int that may be at least 0: a test of a name that holds it, and
    // no float, which only a cast that may fail would give.
    let read = "  n = int(m.stdin[0]) else 0;\n";
    let named = format!(
        "{read}  exponent = n - 5;\n  m.stdout <- \"${{if exponent >= 0 {{ 2^exponent }} else {{ 0 }}}}\";"
    );
    let out = power_case(
        "",
        &format!("{read}  m.stdout <- \"${{2^(n - 5)}}\";"),
        &[(&named, "7", "4\n"), (&named, "3", "0\n")],
    );
    assert!(out.contains("`2 : int ^ (n - 5) : int`"), "{out}");
    assert!(out.contains("this `-` gives int"), "{out}");
    assert!(
        out.contains("repair: `exponent = n - 5; if exponent >= 0 { 2^exponent } else { … }`"),
        "{out}"
    );
    assert!(!out.contains("repair: `2.0f64"), "{out}");
}

#[test]
fn an_int_power_whose_exponent_may_be_below_zero_offers_a_test_of_it() {
    let read = "  k = int(m.stdin[0]) else 0;\n";
    let tested = format!("{read}  m.stdout <- \"${{if k >= 0 {{ 2^k }} else {{ 0 }}}}\";");
    let out = power_case(
        "",
        &format!("{read}  m.stdout <- \"${{2^k}}\";"),
        &[(&tested, "3", "8\n"), (&tested, "-3", "0\n")],
    );
    assert!(
        out.contains("Int power with an exponent that may be negative: `2 : int ^ k : int`. Try `if k >= 0 { 2^k } else { … }` instead."),
        "{out}"
    );
    assert!(out.contains("`k` is int here"), "{out}");
    assert!(
        out.contains("repair: `if k >= 0 { 2^k } else { … }`"),
        "{out}"
    );
    // A parameter declared `int`: the same test, of the parameter.
    let out = power_case(
        "f(positional n: int) = 2^n;",
        "  m.stdout <- \"${f(-2)}\";",
        &[],
    );
    assert!(out.contains("`2 : int ^ n : int`"), "{out}");
    assert!(
        out.contains("repair: `if n >= 0 { 2^n } else { … }`"),
        "{out}"
    );
    assert_eq!(
        runs(
            "f(positional n: int) = if n >= 0 { 2^n } else { 0 };",
            r#""${f(-2)} ${f(3)}""#,
            ""
        ),
        "0 8\n"
    );
    // The power of a parameter of no declared type, at a call: the test of the argument,
    // around the call.
    let p = "p(positional b, positional e) = b ^ e;";
    let tested = format!("{read}  m.stdout <- \"${{if k >= 0 {{ p(2, k) }} else {{ 0 }}}}\";");
    let out = power_case(
        p,
        &format!("{read}  m.stdout <- \"${{p(2, k)}}\";"),
        &[(&tested, "3", "8\n"), (&tested, "-3", "0\n")],
    );
    assert!(
        out.contains("repair: `if k >= 0 { p(2, k) } else { … }`"),
        "{out}"
    );
    // An expression as the argument: a new name, `e`, holds it.
    let named =
        format!("{read}  e = k - 1;\n  m.stdout <- \"${{if e >= 0 {{ p(2, e) }} else {{ 0 }}}}\";");
    let out = power_case(
        p,
        &format!("{read}  m.stdout <- \"${{p(2, k - 1)}}\";"),
        &[(&named, "4", "8\n"), (&named, "0", "0\n")],
    );
    assert!(
        out.contains("repair: `e = k - 1; if e >= 0 { p(2, e) } else { … }`"),
        "{out}"
    );
    let out = rejected(p, r#""${p(2, -1)}""#);
    assert!(out.contains(": `p(2, -1 : int)`.\n"), "{out}");
    assert!(
        out.contains("repair: pass as `e` a value in int[0..]"),
        "{out}"
    );
    assert!(!out.contains("repair: `if"), "{out}");
    assert!(!out.contains("`v"), "{out}");
}

#[test]
fn a_power_of_a_parameter_under_a_negative_exponent_takes_no_int() {
    // The base takes no int at all: a base whose ints are all at least 0 is refused too, as
    // `2 ^ -1` is a fraction. This program once passed and stopped in the evaluator.
    let p = "p(positional b) = b ^ -1;";
    for (arg, shown) in [("c", "2"), ("2", "int")] {
        let out = rejected(&format!("{p}\nc = 2;"), &format!(r#""${{p({arg})}}""#));
        assert!(
            out.contains(&format!(
                "Int power with a negative exponent: `b : {shown} ^ -1 : int`. Try `b: f64` instead, and pass a float as `b` at each call."
            )),
            "{out}"
        );
        assert!(
            out.contains(&format!("the base `b` is {shown} here")),
            "{out}"
        );
        assert!(
            out.contains("repair: `b: f64`, and pass a float as `b` at each call"),
            "{out}"
        );
        assert!(
            out.contains("repair: `b ^ -1.0`, and pass a float as `b` at each call"),
            "{out}"
        );
        assert!(!out.contains("`v"), "{out}");
        assert!(!out.contains("f64("), "{out}");
    }
    let fixed = [
        "p(positional b: f64) = b ^ -1;\nc = 2.0f64;",
        "p(positional b) = b ^ -1.0;\nc = 2.0f64;",
    ];
    for f in fixed {
        assert_eq!(runs(f, r#""${p(c)}""#, ""), "0.5\n", "{f}");
    }
    // A float argument passes as it is.
    assert_eq!(runs(p, r#""${p(2.0f64)}""#, ""), "0.5\n");
}

#[test]
fn a_prelude_word_takes_its_number_of_arguments() {
    rejected("", r#""${len("ab", "c") + 1}""#);
}

#[test]
fn a_function_is_not_shown_and_not_put_in_a_tuple() {
    rejected(INC, r#""${inc}""#);
    assert_eq!(
        rejected(INC, "String(inc)"),
        "3:15: `String` takes data, and this value may hold a function, `(T) -> T for T in int \
         | f64 | rat`: data is a value that holds no function at any depth.\n  \
         [1] 3:22: `inc` is (T) -> T for T in int | f64 | rat here\n      \
         3 |   m.stdout <- String(inc);\n        \
         |               ^^^^^^^^^^^ [3, 4]\n        \
         |                      ^^^ [1]\n  \
         [2] 1:1: `inc` is declared here with no type written for `x` or its result; the type \
         the checker found for `inc` is `(T) -> T for T in int | f64 | rat`\n      \
         1 | inc(positional x) = x + 1;\n        \
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^\n  \
         [3] 3:15: repair: call the function before the value gets here, so that the value \
         holds its result and not the function\n  \
         [4] 3:15: repair: keep the function under its own name, out of the value"
    );
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
    rejected(h, r#""${h((int(1), 2.5f64))}""#);
    rejected(&k, r#""${k((int(1), r(2.5)))}""#);
    // A literal without a suffix takes the carrier of the other component (step L1.26a).
    assert_eq!(runs(&k, r#""${k((1, r(2.5)))}""#, ""), "3.5\n");
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
               main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n";
    if let Err(e) = load(src.as_bytes()) {
        panic!("{src}: rejected: {e}");
    }
    rejected("w(positional f) = f(f);", r#""${w(5)}""#);
}

#[test]
fn a_type_variable_left_by_a_rejected_call_ends_the_check() {
    // `h((0, 1))` is rejected, and its result keeps the type variable of `h`'s result, which
    // stands for itself; `sum` and `^` on it once read the variable as its own type without
    // end, and the checker overflowed its stack.
    let h = "h(positional p) = p(len(p));";
    for out in [r#""${sum(h((0, 1)))}""#, r#""${2^h((0, 1))}""#] {
        let e = rejected(h, out);
        assert!(e.contains("`h` does not take ((0, 1))"), "{e}");
    }
    // A class not yet given a type still takes `sum` and `^` as needs.
    let s = "s(positional t) = sum(t);\npw(positional n) = 2^n;";
    rejected(s, r#""${s(("a", 1))}""#);
    rejected(s, r#""${pw(-1)}""#);
    assert_eq!(runs(s, r#""${s((1, 2))} ${pw(3)}""#, ""), "3 8\n");
}

/// The program with these definitions and this body of `main`.
fn program(defs: &str, body: &str) -> String {
    format!("{defs}\nmain(m: MainArgs) {{\n  {body}\n}}\n")
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
        run(&program(add, r#"f = add[1]; m.stdout <- "${f(2)}";"#), ""),
        "3\n"
    );
    refused(&program(add, r#"f = add[1]; m.stdout <- "${f("x")}";"#));
    let first = "first(positional t, positional u) = t[0];";
    refused(&program(first, r#"f = first[5]; m.stdout <- "${f(1)}";"#));
    let pick = "pick(positional t, positional i) = t[i];";
    // A tuple takes a computed key (DESIGN.md sec:types, the `m[k]` row), so `f(0)` reads
    // the first component; the key `5` selects none, which the call checks.
    assert_eq!(
        run(
            &program(pick, r#"f = pick[(1, 2)]; m.stdout <- "${f(0)}";"#),
            ""
        ),
        "1\n"
    );
    refused(&program(
        pick,
        r#"f = pick[(1, 2)]; m.stdout <- "${f(5)}";"#,
    ));
    let greet = r#"greet(positional name, punct = "!", lead = "hi") = "${lead}, ${name}${punct}";"#;
    let body = r#"h = greet("Al", lead: "yo", ...); m.stdout <- h(punct: "?");"#;
    assert_eq!(run(&program(greet, body), ""), "yo, Al?\n");
    refused(&program(
        greet,
        r#"h = greet("Al", lead: "yo", ...); m.stdout <- h(punct: 5);"#,
    ));
}

#[test]
fn a_returned_function_carries_the_needs_of_its_parameters() {
    let defs = "inc = x -> x + 1;\n\
                compose(positional f, positional g) = x -> f(g(x));\n\
                twice(positional f) = compose(f, f);\n\
                len2(positional s) = len(s);";
    assert_eq!(
        run(&program(defs, r#"m.stdout <- "${twice(inc)(3)}";"#), ""),
        "5\n"
    );
    refused(&program(defs, r#"m.stdout <- "${twice(inc)("a")}";"#));
    refused(&program(defs, r#"m.stdout <- "${twice(len2)("abc")}";"#));
    let bang = r#"h = twice(x -> x ++ "!"); m.stdout <- h("a");"#;
    assert_eq!(run(&program(defs, bang), ""), "a!!\n");
    let ok = r#"h = compose(x -> x * 2, x -> x + 1); m.stdout <- "${h(4)}";"#;
    assert_eq!(run(&program(defs, ok), ""), "10\n");
    refused(&program(
        defs,
        r#"h = compose(x -> x * 2, x -> x ++ "s"); m.stdout <- "${h("a")}";"#,
    ));
}

#[test]
fn a_name_an_else_pattern_binds_has_the_type_of_its_payload() {
    let parse =
        r#"parse(positional text) = if text == "" { #parseError(line: 1, col: 0) } else { 42 };"#;
    let both = r#"both = parse("") else #parseError(line:, col:) -> line * 100 + col; m.stdout <- "${both}" else "?";"#;
    assert_eq!(run(&program(parse, both), ""), "100\n");
    let wrap = "wrap(positional v) = #w(v: v);";
    let five = r#"r = wrap(5) else #w(v:) -> v + 1; m.stdout <- "${r}" else "?";"#;
    assert_eq!(run(&program(wrap, five), ""), "6\n");
    refused(&program(
        wrap,
        r#"r = wrap("a") else #w(v:) -> v + 1; m.stdout <- "${r}";"#,
    ));
    refused(&program(
        "",
        r#"r = #e(x: "a") else #e(x:) -> x + 1; m.stdout <- "${r}";"#,
    ));
    // Of two shapes, the name has the union of both.
    let pick = r#"pick(positional c: bool) = if c { #e(x: 1) } else { #e(x: "a") };"#;
    refused(&program(
        pick,
        r#"r = pick(true) else #e(x:) -> x + 1; m.stdout <- "${r}";"#,
    ));
    let pick = "pick(positional c: bool) = if c { #e(x: 1) } else { #e(x: 2, y: 3) };";
    let y = r#"r = pick(false) else #e(y:) -> y + 1; m.stdout <- "${r}" else "?";"#;
    assert_eq!(run(&program(pick, y), ""), "4\n");
    let nested = r#"r = #o(i: #e(x: 2)) else #o(i: #e(x:)) -> x * 3; m.stdout <- "${r}" else "?";"#;
    assert_eq!(run(&program("", nested), ""), "6\n");
    let v = "v = #e(code: 5) else #e(code:) -> code;";
    assert_eq!(
        run(&program(v, r#"m.stdout <- String(v + 1) else "z";"#), ""),
        "6\n"
    );
    refused(&program(
        &format!("{FIRST}\n{v}"),
        r#"m.stdout <- String(first(v)) else "z";"#,
    ));
    refused(&program(v, r#"m.stdout <- String(v ++ "a") else "z";"#));
    refused(&program(
        &format!("{APP}\n{v}"),
        r#"m.stdout <- String(app(v)) else "z";"#,
    ));
}

#[test]
fn a_generic_else_pattern_binds_the_payload_each_call_passes() {
    let g = "g(positional e) = e else #e(code:) -> code;";
    assert_eq!(
        run(
            &program(g, r#"m.stdout <- String(g(#e(code: 5)) + 1) else "z";"#),
            ""
        ),
        "6\n"
    );
    assert_eq!(
        run(&program(g, r#"m.stdout <- String(g(3) + 1) else "z";"#), ""),
        "4\n"
    );
    refused(&program(
        g,
        r#"m.stdout <- String(g(#e(code: "a")) + 1) else "z";"#,
    ));
    refused(&program(
        &format!("{g}\n{FIRST}"),
        r#"m.stdout <- String(first(g(#e(code: 5)))) else "z";"#,
    ));
    let h = "h(positional e) = e else #o(i: #e(x:)) -> x;";
    assert_eq!(
        run(
            &program(h, r#"m.stdout <- String(h(#o(i: #e(x: 2))) * 3) else "z";"#),
            ""
        ),
        "6\n"
    );
    refused(&program(
        h,
        r#"m.stdout <- String(h(#o(i: #e(x: "s"))) * 3) else "z";"#,
    ));
}

#[test]
fn a_self_application_takes_the_least_settled_result() {
    // Inside `w(w)` the inner use first gives nothing; the outer then gives 1, which settles.
    let settles = "w(positional f) = if true { 1 } else { f(f) + 1 };\nspin = w(w);";
    assert_eq!(
        run(
            &program(settles, r#"m.stdout <- String(spin) else "z";"#),
            ""
        ),
        "1\n"
    );
    // Here the inner use must give a string, and the outer gives 1 | String: not settled.
    let grows = "w(positional f) = if true { 1 } else { f(f) ++ \"a\" };\nspin = w(w);";
    refused(&program(grows, r#"m.stdout <- "x";"#));
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
        &format!(r#"m.stdout <- if {call} is int {{ "int" }} else {{ "other" }};"#),
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
            e.contains(&format!(
                " : {given}` apart into 2 names: it is not a tuple of 2"
            )),
            "{e}"
        );
        assert!(e.contains("`f` needs this of its argument here"), "{e}");
        assert!(e.contains("a, b = p;"), "{e}");
    }
    // Through a function that passes its argument on, the need is `g`'s.
    let e = kind_refused("g(5)");
    assert!(
        e.contains(" : 5` apart into 2 names: it is not a tuple of 2"),
        "{e}"
    );
    assert!(e.contains("`g` needs this of its argument here"), "{e}");
    // A pair passes, of any component types, and gives its first component's type.
    let is = r#"m.stdout <- if f((1, 2)) is int { "int" } else { "other" };"#;
    assert_eq!(run(&program(PAIR, is), ""), "int\n");
    let is = r#"m.stdout <- if g(("x", 2)) is int { "int" } else { "other" };"#;
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
        ["`+` does not take (_, 1): no arrow of `+` takes these types. [y + 1]"]
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
        ["`+` does not take (_, 1): no arrow of `+` takes these types. [w + 1]"]
    );
    rejected(outer, r#"String(outer(1)) else "atom""#);
    let ok = "outer(positional x) = {\n  inner(positional y, w = y) = w + 1;\n  inner(x)\n};";
    assert_eq!(runs(ok, r#"String(outer(1)) else "atom""#, ""), "2\n");
}

/// Through `zedc run` (POW-rat): `k = -1; 2^k` and `x = 2; x^-1` are refused with the exact
/// `rat` power as the repair, and each repair, applied as printed, runs. A `rat` power of a
/// value with no `0r` is no `#divByZero`, so `rat(x)^-1` reaches the port as text; `rat(n)`
/// under `n > 0` holds no `0r`, and under `n >= 0` it does, so that power is refused at the
/// port; `r ^ k` of a `rat` parameter may be `#divByZero`, which `else` handles at run time.
#[test]
fn zedc_run_offers_and_runs_the_exact_rat_power() {
    use zed_tests::step_helpers::l01_19_whole_file_ports::run as zedc_run;
    let program = |body: &str| format!("main(m: MainArgs) {{\n{body}\n}}\n");
    for (name, bad, fixed, message) in [
        (
            "pow_rat_k",
            "  k = -1;\n  m.stdout <- \"${2^k}\";",
            "  k = -1;\n  m.stdout <- \"${2r^k}\";",
            "3:18: Int power with a negative exponent: `2 : int ^ k : -1`. Try `2r^k` instead.\n",
        ),
        (
            "pow_rat_x",
            "  x = 2;\n  m.stdout <- \"${x^-1}\";",
            "  x = 2;\n  m.stdout <- \"${rat(x)^-1}\";",
            "3:18: Int power with a negative exponent: `x : 2 ^ -1 : int`. Try `rat(x)^-1` instead.\n",
        ),
    ] {
        let out = zedc_run(name, &program(bad), "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{}", out.stderr);
        assert!(out.stderr.contains(message), "{}", out.stderr);
        let out = zedc_run(name, &program(fixed), "", &[]);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, "1r/2r\n"),
            "{}",
            out.stderr
        );
    }
    let src = "inv(positional r: rat, positional k: int) = r ^ k;\n\
               main(m: MainArgs) {\n  n = int(m.stdin[0]) else 0;\n  \
               m.stdout <- \"${inv(2r/3r, -2) else #divByZero -> 0r} \
               ${inv(0r, -1) else #divByZero -> 7r} ${inv(-2r, n) else #divByZero -> 0r} \
               ${if n > 0 { rat(n)^-1 } else { 0r }}\";\n}\n";
    for (stdin, want) in [
        ("-3", "9r/4r 7r -1r/8r 0r\n"),
        ("4", "9r/4r 7r 16r 1r/4r\n"),
        ("0", "9r/4r 7r 1r 0r\n"),
    ] {
        let out = zedc_run("pow_rat_inv", src, stdin, &[]);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, want),
            "{}",
            out.stderr
        );
    }
    let out = zedc_run(
        "pow_rat_zero",
        &program(
            "  n = int(m.stdin[0]) else 0;\n  m.stdout <- \"${if n >= 0 { rat(n)^-1 } else { 0r }}\";",
        ),
        "1",
        &[],
    );
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(
        out.stderr.contains("not String | #divByZero"),
        "{}",
        out.stderr
    );
    // `rat` of an int with no 0 holds no `0r`, so a division by it cannot fail either; and a
    // decimal under `^` with an int exponent takes `rat`, the one arrow that fits.
    for (name, body, want) in [
        (
            "pow_rat_div",
            "  x = 2;\n  m.stdout <- \"${1r / rat(x)}\";",
            "1r/2r\n",
        ),
        (
            "pow_rat_dec",
            "  n = -2;\n  m.stdout <- \"${0.5 ^ n}\";",
            "4r\n",
        ),
    ] {
        let out = zedc_run(name, &program(body), "", &[]);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, want),
            "{}",
            out.stderr
        );
    }
}
