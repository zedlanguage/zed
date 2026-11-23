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
    assert_eq!(
        runs(
            "",
            r#""${len(m.stdin[0]) else #ioError -> 0 else #outOfBounds -> 0}""#,
            "abc"
        ),
        "3\n"
    );
}

#[test]
fn an_int_power_needs_an_exponent_of_at_least_zero() {
    rejected("", r#""${2^-1}""#);
    rejected(
        "",
        r#""${(2^(int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0)) div 1}""#,
    );
    assert_eq!(runs("", r#""${2^3}""#, ""), "8\n");
}

#[test]
fn an_int_power_rejection_shows_the_negative_exponent() {
    let out = rejected("", r#""${2^-1}""#);
    // The first line names the exponent, in the power's code annotated with types.
    assert!(
        out.contains(
            "Int power with a negative exponent: `2 : int ^ -1 : int`. Try `2r^-1` instead."
        ),
        "{out}"
    );
    assert!(out.contains("the base `2` is int here"), "{out}");
    assert!(!out.contains("`v"), "{out}");
    // Each repair is the power rewritten in full, and each runs.
    for fix in ["2.0f64^-1", "2^-1.0f64"] {
        assert!(out.contains(&format!("repair: `{fix}`")), "{out}");
        assert_eq!(runs("", &format!(r#""${{{fix}}}""#), ""), "0.5\n");
    }
    // The exact `rat` power, first (POW-rat, POW-rat-first-repair).
    assert!(out.contains("repair: `2r^-1`"), "{out}");
    assert_eq!(runs("", r#""${2r^-1}""#, ""), "1r/2r\n");
    // Every value of the exponent is below 0, so no test of it is offered.
    assert!(!out.contains("repair: `if"), "{out}");
}

/// The diagnostics of the program whose `main` has the body `body` after `defs`, which must
/// be rejected, and the program with `body` in place of the fixes in `fixed`, each run on
/// its input with the output it must give. No repair names a value the program does not
/// have, and none casts an int to a float, a cast that rounds above 2^53 in magnitude.
fn power_case(defs: &str, body: &str, fixed: &[(&str, &str, &str)]) -> String {
    let main = |body: &str| format!("{defs}\nmain(m: MainArgs) {{\n{body}\n}}\n");
    let src = main(body);
    let out = match load(src.as_bytes()) {
        Err(e) => e,
        Ok(_) => panic!("accepted:\n{src}"),
    };
    assert!(!out.contains("`v"), "{out}");
    assert!(!out.contains("`n: int[0..]`"), "{out}");
    // An `f64(…)` cast of the exponent is offered only where the headline shows the exponent
    // as one int within ±2^53, where the cast is exact (MSG-power-f64-repair).
    if out.contains("f64(") {
        let head = out.lines().next().unwrap_or("");
        let shown = head.rsplit(" : ").next().and_then(|s| s.split('`').next());
        let v: i64 = (shown.and_then(|s| s.parse().ok()))
            .unwrap_or_else(|| panic!("an f64 cast of an exponent not shown as an int:\n{out}"));
        assert!(v.unsigned_abs() <= 1 << 53, "{out}");
    }
    for (b, stdin, want) in fixed {
        assert_eq!(run(&main(b), stdin), *want, "{b}");
    }
    out
}

/// An int power under a negative exponent through a name (POW-rat): `2.0f64^k` is no repair,
/// as `k` is an int, and `f64(k)` or `f64(x)` rounds above 2^53 in magnitude, so the one repair is
/// the exact `rat` power, `2r^k` for a literal base and `rat(x)^-1` for a name, each printed
/// as the headline's `Try`, and each runs to `1r/2r` as printed. Before, neither had a repair.
/// Where the checker shows `k` as one int within ±2^53, `f64(k)` is exact, and
/// `2.0f64^f64(k)` is offered too (MSG-power-f64-repair).
#[test]
fn an_int_power_rejection_through_a_name_shows_its_value() {
    let out = power_case(
        "",
        "  k = -1;\n  m.stdout <- \"${2^k}\";",
        &[
            ("  k = -1;\n  m.stdout <- \"${2r^k}\";", "", "1r/2r\n"),
            (
                "  k = -1;\n  m.stdout <- \"${2.0f64^f64(k)}\";",
                "",
                "0.5\n",
            ),
        ],
    );
    assert_eq!(
        out,
        r#"4:18: Int power with a negative exponent: `2 : int ^ k : -1`. Try `2r^k` instead.
  [1] 4:20: `k` is -1 here
      4 |   m.stdout <- "${2^k}";
        |                  ^^^ [5, 6]
        |                    ^ [1]
  [2] 3:7: `k` is defined as this expression, -1
      3 |   k = -1;
        |       ^^ [2, 3]
        |        ^ [4]
  [3] 3:7: this `-` gives -1
  [4] 3:8: this literal, 1, is 1
  [5] 4:18: repair: `2r^k`
  [6] 4:18: repair: `2.0f64^f64(k)`"#
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
    // An exponent that is an operation on integer literals alone is an `int` known as its
    // value, as one integer literal is (plan row LIT-rat-int-op-exponent), so the note gives
    // -2 and the exact `rat` power is a repair too.
    let out = rejected("", r#""${2^(1 - 3)}""#);
    assert!(
        out.contains("Int power with a negative exponent: `2 : int ^ (1 - 3) : -2`. Try `2r^(1 - 3)` instead."),
        "{out}"
    );
    assert!(out.contains("this `-` gives -2"), "{out}");
    assert!(out.contains("repair: `2.0f64^(1 - 3)`"), "{out}");
    assert!(out.contains("repair: `2r^(1 - 3)`"), "{out}");
    assert!(!out.contains("`v"), "{out}");
    assert_eq!(runs("", r#""${2.0f64^(1 - 3)}""#, ""), "0.25\n");
    assert_eq!(runs("", r#""${2r^(1 - 3)}""#, ""), "1r/4r\n");
    // An expression of an int that may be at least 0: a test of a name that holds it, and
    // no float, which only a cast that may fail would give.
    let read =
        "  n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n";
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
fn an_int_power_rejection_at_the_top_level_shows_the_value_of_a_literal_exponent() {
    // Outside a body, the exponent of literals alone was shown by its class, `int`, with
    // "this `-` gives int" (plan row MSG-power-literal-derivation); its value is shown, as in a
    // body, and at each operation of a nested exponent.
    let out = rejected("x = 2^(1 - 3);", r#""${x}""#);
    assert!(
        out.contains("Int power with a negative exponent: `2 : int ^ (1 - 3) : -2`."),
        "{out}"
    );
    assert!(out.contains("this `-` gives -2"), "{out}");
    assert!(!out.contains("gives int"), "{out}");
    let out = rejected("x = 2^((1 - 3) * 2 + 1);", r#""${x}""#);
    assert!(out.contains("`2 : int ^ ((1 - 3) * 2 + 1) : -3`"), "{out}");
    for step in [
        "this `+` gives -3",
        "this `*` gives -4",
        "this `-` gives -2",
    ] {
        assert!(out.contains(step), "{step}: {out}");
    }
    // A name in the exponent gives no one value: it is shown by what is known of it.
    let out = rejected("k = -2;\nx = 2^(k + 0);", r#""${x}""#);
    assert!(out.contains("Int power with a negative exponent"), "{out}");
}

#[test]
fn an_int_power_whose_exponent_may_be_below_zero_offers_a_test_of_it() {
    let read =
        "  k = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n";
    let tested = format!("{read}  m.stdout <- \"${{if k >= 0 {{ 2^k }} else {{ 0 }}}}\";");
    let out = power_case(
        "",
        &format!("{read}  m.stdout <- \"${{2^k}}\";"),
        &[(&tested, "3", "8\n"), (&tested, "-3", "0\n")],
    );
    assert!(
        out.contains("Int power with an exponent that may be negative: `2 : int ^ k : int`. Try `2r^k` instead."),
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
            out.contains("repair: `b ^ -1.0f64`, and pass a float as `b` at each call"),
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
fn a_function_is_not_shown_and_may_be_held_in_a_tuple() {
    rejected(INC, r#""${inc}""#);
    assert_eq!(
        rejected(INC, "String(inc)"),
        "3:15: Cannot show a value that may hold a function: `inc : T -> T for T in int | f32 \
         | f64 | rat` in `String(inc)`.\n  \
         [1] 3:22: `inc` is T -> T for T in int | f32 | f64 | rat here\n      \
         3 |   m.stdout <- String(inc);\n        \
         |               ^^^^^^^^^^^ [3]\n        \
         |                      ^^^ [1]\n  \
         [2] 1:1: `inc` is declared here with no type written for `x` or its result; the type \
         the checker found for `inc` is `T -> T for T in int | f32 | f64 | rat`\n      \
         1 | inc(positional x) = x + 1;\n        \
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^\n  \
         [3] 3:15: data is a value that holds no function at any depth"
    );
    // A tuple may hold a function (DESIGN.md step L1.17, QUESTIONS A43): building one is no
    // error, a component that is data is shown, and showing the tuple itself is refused.
    assert_eq!(runs(INC, r#""${(inc, 1)[1]}""#, ""), "1\n");
    let pair = format!("pair(positional a, positional b) = (a, b);\n{INC}");
    assert_eq!(runs(&pair, r#""${pair(inc, 2)[1]}""#, ""), "2\n");
    rejected(INC, r#""${(inc, 1)}""#);
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
    let both = r#"both = parse("") else #parseError(line:, col:) -> line * 100 + col; m.stdout <- "${both}";"#;
    assert_eq!(run(&program(parse, both), ""), "100\n");
    let wrap = "wrap(positional v) = #w(v: v);";
    let five = r#"r = wrap(5) else #w(v:) -> v + 1; m.stdout <- "${r}";"#;
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
    let y = r#"r = pick(false) else #e(y:) -> y + 1; m.stdout <- "${r}" else #e -> "?";"#;
    assert_eq!(run(&program(pick, y), ""), "4\n");
    let nested =
        r#"r = #o(i: #e(x: 2)) else #o(i: #e(x:)) -> x * 3; m.stdout <- "${r}" else #o -> "?";"#;
    assert_eq!(run(&program("", nested), ""), "6\n");
    let v = "v = #e(code: 5) else #e(code:) -> code;";
    assert_eq!(run(&program(v, r#"m.stdout <- String(v + 1);"#), ""), "6\n");
    refused(&program(
        &format!("{FIRST}\n{v}"),
        r#"m.stdout <- String(first(v));"#,
    ));
    refused(&program(v, r#"m.stdout <- String(v ++ "a");"#));
    refused(&program(
        &format!("{APP}\n{v}"),
        r#"m.stdout <- String(app(v));"#,
    ));
}

#[test]
fn a_generic_else_pattern_binds_the_payload_each_call_passes() {
    let g = "g(positional e) = e else #e(code:) -> code;";
    assert_eq!(
        run(
            &program(
                g,
                r#"m.stdout <- String(g(#e(code: 5)) + 1) else #e -> "z";"#
            ),
            ""
        ),
        "6\n"
    );
    assert_eq!(
        run(&program(g, r#"m.stdout <- String(g(3) + 1);"#), ""),
        "4\n"
    );
    refused(&program(
        g,
        r#"m.stdout <- String(g(#e(code: "a")) + 1) else #e -> "z";"#,
    ));
    refused(&program(
        &format!("{g}\n{FIRST}"),
        r#"m.stdout <- String(first(g(#e(code: 5)))) else #e -> "z";"#,
    ));
    let h = "h(positional e) = e else #o(i: #e(x:)) -> x;";
    assert_eq!(
        run(
            &program(
                h,
                r#"m.stdout <- String(h(#o(i: #e(x: 2))) * 3) else #o -> "z";"#
            ),
            ""
        ),
        "6\n"
    );
    refused(&program(
        h,
        r#"m.stdout <- String(h(#o(i: #e(x: "s"))) * 3) else #o -> "z";"#,
    ));
}

// An `else` pattern with parts takes from the type each payload it is sure to match, at any
// depth of its field patterns (DESIGN.md, step L1, "Where this document does not say": "The
// pattern form `e else p -> d` removes from the type the values of the atom that its pattern
// `p` matches, as a `match` arm with the same pattern would take them"; "A payload pattern
// keeps in the type each payload the type holds that it can fail to match, so the atom stays
// where such a payload remains"). Before ELSE-explicit-atoms x2, a field pattern with a
// pattern of its own, and any field pattern on a type variable, took nothing.

#[test]
fn an_else_pattern_with_nested_parts_takes_each_payload_it_matches() {
    // Matched exactly: no `#o` is left, so the write needs no `else`.
    let nested = r#"r = #o(i: #e(x: 2)) else #o(i: #e(x:)) -> x * 3; m.stdout <- "${r}";"#;
    assert_eq!(run(&program("", nested), ""), "6\n");
    let deeper =
        r#"r = #o(i: #p(j: #e(x: 2))) else #o(i: #p(j: #e(x:))) -> x * 3; m.stdout <- "${r}";"#;
    assert_eq!(run(&program("", deeper), ""), "6\n");
    // A bare atom as a field's pattern takes the bare atom, and `#e()` the atom whose payload
    // is the empty tuple.
    let bare = r#"r = #o(i: #e) else #o(i: #e) -> 7; m.stdout <- "${r}";"#;
    assert_eq!(run(&program("", bare), ""), "7\n");
    let empty = r#"r = #o(i: #e()) else #o(i: #e()) -> 8; m.stdout <- "${r}";"#;
    assert_eq!(run(&program("", empty), ""), "8\n");
    // Nested, `#e` matches the bare atom only when the program runs (the elaborator gives it
    // the kernel pattern `Atom(e, [])`, zedc-elab state.rs `pattern_open`), so `#e(x: 2)`
    // passes it by, and the checker keeps `#o`: taking it would let the atom reach the write.
    let payload = r#"r = #o(i: #e(x: 2)) else #o(i: #e) -> 7;"#;
    refused(&program("", &format!(r#"{payload} m.stdout <- "${{r}}";"#)));
    assert_eq!(
        run(
            &program(
                "",
                &format!(r#"{payload} m.stdout <- "${{r}}" else #o -> "?";"#)
            ),
            ""
        ),
        "?\n"
    );
    // Two fields, one matched by name, one by a nested pattern.
    let two = r#"r = #o(a: 1, i: #e(x: 2)) else #o(a:, i: #e(x:)) -> a + x; m.stdout <- "${r}";"#;
    assert_eq!(run(&program("", two), ""), "3\n");
}

#[test]
fn an_else_pattern_with_nested_parts_keeps_each_payload_it_can_fail_to_match() {
    // `#o(i: #f)` and `#o(j: 1)` are not matched by `#o(i: #e(x:))`, so `#o` stays and the
    // write is refused; handled, it runs.
    let pick = "pick(positional c: int) = if c == 0 { #o(i: #e(x: 2)) } else if c == 1 { #o(i: #f) } else { #o(j: 1) };";
    let take = r#"r = pick(0) else #o(i: #e(x:)) -> x * 3;"#;
    refused(&program(pick, &format!(r#"{take} m.stdout <- "${{r}}";"#)));
    assert_eq!(
        run(
            &program(
                pick,
                &format!(r#"{take} m.stdout <- "${{r}}" else #o -> "?";"#)
            ),
            ""
        ),
        "6\n"
    );
    // A field whose type holds a value the field's pattern does not match keeps the payload.
    let mixed = "mixed(positional c: bool) = #o(i: if c { #e(x: 2) } else { 5 });";
    refused(&program(
        mixed,
        r#"r = mixed(true) else #o(i: #e(x:)) -> x * 3; m.stdout <- "${r}";"#,
    ));
    // The atom inside the field lacks the field `x` the nested pattern names.
    refused(&program(
        "",
        r#"r = #o(i: #e(y: 2)) else #o(i: #e(x:)) -> x * 3; m.stdout <- "${r}";"#,
    ));
    // A literal as a field's pattern can fail, and is kept whole (the checker does not compare
    // literals here).
    refused(&program(
        "",
        r#"r = #o(i: 2) else #o(i: 2) -> 3; m.stdout <- "${r}";"#,
    ));
}

#[test]
fn a_generic_else_pattern_with_parts_takes_from_each_call_s_argument() {
    // The difference is taken where the call puts the argument's type for the variable
    // (DESIGN.md sec:type_language: "specialized at each call by putting the argument types for
    // the variables and simplifying").
    let g = "g(positional e) = e else #e(code:) -> code;";
    assert_eq!(
        run(
            &program(g, r#"m.stdout <- String(g(#e(code: 5)) + 1);"#),
            ""
        ),
        "6\n"
    );
    let h = "h(positional e) = e else #o(i: #e(x:)) -> x;";
    assert_eq!(
        run(
            &program(h, r#"m.stdout <- String(h(#o(i: #e(x: 2))) * 3);"#),
            ""
        ),
        "6\n"
    );
    // An argument the pattern can fail to match keeps its atom.
    refused(&program(h, r#"m.stdout <- String(h(#o(i: #f)) * 3);"#));
    refused(&program(g, r#"m.stdout <- String(g(#e(other: 5)) + 1);"#));
    assert_eq!(
        run(&program(h, r#"m.stdout <- String(h(3) * 3);"#), ""),
        "9\n"
    );
}

/// A `main` whose `else` takes an atom of `n` fields, each an atom `#e(xi: i)` matched by the
/// nested pattern `#e(xi:)`: every payload matched, so the write needs no `else`.
pub(super) fn else_of_many_nested_fields(n: usize) -> String {
    let value: Vec<String> = (0..n).map(|i| format!("f{i}: #e(x{i}: {i})")).collect();
    let pat: Vec<String> = (0..n).map(|i| format!("f{i}: #e(x{i}:)")).collect();
    let body = format!(
        r#"r = #o({}) else #o({}) -> x0; m.stdout <- "${{r}}";"#,
        value.join(", "),
        pat.join(", ")
    );
    program("", &body)
}

/// A `main` whose `else` takes an atom nested `d` deep, `#o(i: #o(i: … #e(x: 2)))`, by the
/// pattern of the same shape: matched exactly, so the write needs no `else`.
pub(super) fn else_nested_deep(d: usize) -> String {
    let value = format!("{}#e(x: 2){}", "#o(i: ".repeat(d), ")".repeat(d));
    let pat = format!("{}#e(x:){}", "#o(i: ".repeat(d), ")".repeat(d));
    program(
        "",
        &format!(r#"r = {value} else {pat} -> x; m.stdout <- "${{r}}";"#),
    )
}

#[test]
fn an_else_of_many_nested_fields_takes_them_all() {
    // Small instances of the benchmarks `bench::soundness::an_else_of_many_nested_fields_scales`
    // and `bench::soundness::an_else_nested_deep_scales`.
    assert_eq!(run(&else_of_many_nested_fields(4), ""), "0\n");
    assert_eq!(run(&else_nested_deep(4), ""), "2\n");
}

#[test]
fn a_self_application_takes_the_least_settled_result() {
    // Inside `w(w)` the inner use first gives nothing; the outer then gives 1, which settles.
    let settles = "w(positional f) = if true { 1 } else { f(f) + 1 };\nspin = w(w);";
    assert_eq!(
        run(&program(settles, r#"m.stdout <- String(spin);"#), ""),
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

/// The errors of `f(p)` whose body is the statements `uses` in this order and then
/// `return 0;`: each headline with the code it points at, then each note with the code it
/// points at.
fn destructure_errors(uses: &[&str]) -> Vec<String> {
    let text = format!("f(p) {{\n  {}\n  return 0;\n}}\n", uses.join("\n  "));
    let at = |s: zedc::lex::Span| &text[s.start..s.end];
    let (info, _) = zed_tests::step_helpers::l01_26_type_resolution::info(&text);
    (info.errors.iter())
        .map(|e| {
            let notes: Vec<String> = (e.notes.iter())
                .map(|n| format!("{} [{}]", n.text, at(n.span)))
                .collect();
            format!("{} [{}] {}", e.message, at(e.span), notes.join("; "))
        })
        .collect()
}

/// The written order of a parameter's uses fixes nothing (DESIGN.md sec:premise; row
/// CHECK-destructure-order): a parameter taken apart into a pair and used as a number is
/// refused in either order, with one error that names both uses, the destructuring in its
/// headline and the arithmetic's literal in a note. Before, `a, b = p; y = p + 1;` was
/// accepted: the class lost its tuples after the destructuring's need was recorded, and
/// nothing checked the need again. With three uses, each of the six orders gives that one
/// error, its note naming the literal of the arithmetic written first, which removed the
/// tuples.
#[test]
fn a_parameter_taken_apart_and_used_as_a_number_is_refused_in_either_order() {
    let headline = "Cannot take `p : int | f32 | f64 | rat` apart into 2 names: it is not a \
                    tuple of 2. [p]";
    let first = destructure_errors(&["a, b = p;", "y = p + 1;"]);
    let second = destructure_errors(&["y = p + 1;", "a, b = p;"]);
    assert_eq!(first, second);
    assert_eq!(first.len(), 1, "{first:?}");
    assert!(first[0].starts_with(headline), "{first:?}");
    assert!(
        first[0].contains("the literal 1 takes int | f32 | f64 | rat [1]"),
        "{first:?}"
    );
    let uses = ["a, b = p;", "y = p + 1;", "z = p * 2;"];
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let written = order.map(|i| uses[i]);
        let e = destructure_errors(&written);
        assert_eq!(e.len(), 1, "{written:?}: {e:?}");
        assert!(e[0].starts_with(headline), "{written:?}: {e:?}");
        let arithmetic = match written.iter().position(|u| u.contains('+')) {
            Some(i) if written[..i].iter().any(|u| u.contains('*')) => {
                "the literal 2 takes int | f32 | f64 | rat [2]"
            }
            _ => "the literal 1 takes int | f32 | f64 | rat [1]",
        };
        assert!(e[0].contains(arithmetic), "{written:?}: {e:?}");
    }
    // An index and a call of a value used as a number are refused in either order too, each
    // with the message it has where the arithmetic comes first.
    for (taken, headline) in [
        (
            "c = p[0];",
            "`[0]` takes a tuple, not int | f32 | f64 | rat: an index picks a component of a \
             tuple or an entry of a family, and int | f32 | f64 | rat has neither. [p[0]]",
        ),
        (
            "c = p(1);",
            "`p` is int | f32 | f64 | rat, not a function: this call applies `p` to arguments, \
             and a value of type int | f32 | f64 | rat cannot be applied. [p(1)]",
        ),
    ] {
        let first = destructure_errors(&[taken, "y = p + 1;"]);
        let second = destructure_errors(&["y = p + 1;", taken]);
        assert_eq!(first, second, "{taken}");
        assert_eq!(first.len(), 1, "{first:?}");
        assert!(first[0].starts_with(headline), "{first:?}");
    }
    // Controls, accepted in either order: `p` held in a tuple, an index of `p` used as a
    // number, and a tuple compared whole.
    for uses in [
        ["a, b = p;", "y = (p, 1);"],
        ["y = p[0] + 1;", "a, b = p;"],
        ["a, b = p;", "y = p == (1, 2);"],
    ] {
        let mut back = uses;
        back.reverse();
        assert_eq!(destructure_errors(&uses), Vec::<String>::new(), "{uses:?}");
        assert_eq!(destructure_errors(&back), Vec::<String>::new(), "{back:?}");
    }
}

/// Equal destructurings of one parameter used as a number give one error each, whatever the
/// written order (DESIGN.md sec:premise; row CHECK-destructure-order-repeats). A later use
/// equal to a recorded one records no need of its own, so before, with the arithmetic
/// written last, only the first destructuring was refused, and with it written first each
/// was. Two and three equal destructurings, each placed before, between and after the
/// arithmetic.
#[test]
fn equal_destructurings_are_each_refused_in_every_order() {
    let headline = "Cannot take `p : int | f32 | f64 | rat` apart into 2 names: it is not a \
                    tuple of 2. [p]";
    for k in [2, 3] {
        let mut lists = Vec::new();
        for at in 0..=k {
            let mut uses = ["a, b = p;", "c, d = p;", "e, g = p;"][..k].to_vec();
            uses.insert(at, "y = p + 1;");
            let mut e = destructure_errors(&uses);
            e.sort();
            assert_eq!(e.len(), k, "{uses:?}: {e:?}");
            assert!(e.iter().all(|m| m.starts_with(headline)), "{uses:?}: {e:?}");
            lists.push((uses, e));
        }
        for (uses, e) in &lists[1..] {
            assert_eq!(e, &lists[0].1, "{uses:?} against {:?}", lists[0].0);
        }
    }
    // An index and a call repeated, each refused at every place in either order.
    for [c, d] in [["c = p[0];", "d = p[0];"], ["c = p(1);", "d = p(1);"]] {
        let first = destructure_errors(&[c, d, "y = p + 1;"]);
        let second = destructure_errors(&["y = p + 1;", c, d]);
        assert_eq!(first.len(), 2, "{first:?}");
        assert_eq!(first, second, "{c}");
    }
}

/// The `stdout` expression that is `"int"` or `"other"` as the value of `call` is an `int` or
/// not. The `is` test takes a value of any type, so only the uses in the functions called can
/// reject the program.
fn kind_of(call: &str) -> String {
    format!(r#"if {call} is int {{ "int" }} else {{ "other" }}"#)
}

/// The type errors of the definitions `defs` with `r = call;`, as the random programs of
/// `random.rs` are checked.
fn r_errors(defs: &str, call: &str) -> Vec<String> {
    super::type_errors(&format!("{defs}\nr = {call};\n"))
}

/// `h0` takes its first argument apart into three; `h1` takes a pair apart and passes on one
/// of its components, `on`, to `h0`.
fn passed(on: &str) -> String {
    format!(
        "h0(positional p, positional q) {{\n  a, b, c = p;\n  return c;\n}}\n\
         h1(positional p) {{\n  a, b = p;\n  return h0({on}, 1);\n}}"
    )
}

/// The error of taking `call`'s value of type `given` apart into `n` names.
fn not_a_tuple(call: &str, given: &str, n: usize) -> Vec<String> {
    vec![format!(
        "Cannot take `{call} : {given}` apart into {n} names: it is not a tuple of {n}. [{call}]"
    )]
}

#[test]
fn a_literal_component_passed_on_is_not_taken_apart() {
    // The checker accepted each, and the kernel then raised "type error: `[i]` applied to
    // `int`, `int`": the literal `3` of `(1, 3)` is a value of a class of numbers, which the
    // need of `h0` met as a variable that may yet hold a tuple.
    for (on, call) in [("b", "h1((1, 3))"), ("a", "h1((3, 1))")] {
        assert_eq!(r_errors(&passed(on), call), not_a_tuple(call, "3", 3));
    }
    // The program the random test found (seed 15010587807169152550 of
    // `random::accepted_random_programs_raise_no_type_error`).
    let found = "h0(positional p, positional q) {\n  a, b, c = p;\n  return c;\n}\n\
                 h1(positional p) {\n  a, b = p;\n  return h0(b, ((p, a), (-3, b)));\n}";
    let call = r#"h1(((3, -2, "s"), 3))"#;
    assert_eq!(r_errors(found, call), not_a_tuple(call, "3", 3));
    // The program's error names the call that passes the component on.
    let e = rejected(&passed("b"), &kind_of("h1((1, 3))"));
    assert!(e.contains("`h1` needs this of its argument here"), "{e}");
    assert!(e.contains("return h0(b, 1);"), "{e}");
    // A component that is a tuple of three passes, of any component types.
    assert_eq!(
        runs(&passed("b"), &kind_of("h1((1, (1, 2, 3)))"), ""),
        "int\n"
    );
    assert_eq!(
        runs(&passed("a"), &kind_of(r#"h1((("x", 2, "y"), 1))"#), ""),
        "other\n"
    );
}

/// `h` takes a pair apart, and then its second component.
const NESTED: &str = "h(positional p) {\n  a, b = p;\n  c, d = b;\n  return c;\n}";

#[test]
fn a_literal_component_is_not_taken_apart_again() {
    let wrapped = format!("{NESTED}\nw(positional z) = h((1, z));");
    for (defs, call, given) in [
        (NESTED, "h((1, 3))", "3"),
        (NESTED, "h((1, 2.5))", "2.5"),
        (NESTED, "h((1, -4))", "-4"),
        // Through a parameter of a function that passes it on in a pair: the need is `w`'s.
        (&*wrapped, "w(3)", "3"),
    ] {
        assert_eq!(r_errors(defs, call), not_a_tuple(call, given, 2), "{call}");
    }
    let e = rejected(NESTED, &kind_of("h((1, 3))"));
    assert!(e.contains("`h` needs this of its argument here"), "{e}");
    assert!(e.contains("c, d = b;"), "{e}");
    assert_eq!(runs(NESTED, &kind_of("h((1, (2, 3)))"), ""), "int\n");
    assert_eq!(runs(NESTED, &kind_of(r#"h((1, ("s", 3)))"#), ""), "other\n");
}

#[test]
fn a_literal_component_is_not_indexed() {
    // Each was accepted, and failed at run time, as destructuring did: an index, literal or
    // computed, of a class of carriers alone met the need as a variable that may yet hold a
    // tuple or a family.
    let call = "h((1, 3))";
    let literal = format!(
        "`[1]` takes a tuple, not 1: an index picks a component of a tuple or an entry of a \
         family, and 1 has neither. [{call}]"
    );
    let computed = format!(
        "this value is 1, not a function: this call applies it to an argument, and a value of \
         type 1 cannot be applied. [{call}]"
    );
    for (defs, error) in [
        ("h(positional p) = p[0][1];", &literal),
        (
            "h(positional p) {\n  a, b = p;\n  return a[1];\n}",
            &literal,
        ),
        (
            "h(positional p) {\n  k = 1;\n  return p[0][k];\n}",
            &computed,
        ),
    ] {
        assert_eq!(r_errors(defs, call), std::slice::from_ref(error), "{defs}");
        assert_eq!(
            runs(defs, &kind_of("h(((1, 2), 3))"), ""),
            "int\n",
            "{defs}"
        );
    }
}

#[test]
fn a_literal_component_is_not_summed() {
    // FAIL-random-f64-destructured-family: the checker accepted each, and the kernel then
    // raised "type error: expected a family, found a value of type `f64`": `sum` of a class
    // of carriers alone met the need as a variable that may yet hold a family, as an index
    // did before FAIL-random-int-destructured-accepted.
    let defs = "h(positional p) {\n  a, b = p;\n  return sum(a);\n}";
    for call in ["h((-2.5, (3, 3, -2)))", "h((2.5, 1))", "h((3, 1))"] {
        let errors = r_errors(defs, call);
        assert_eq!(errors.len(), 1, "{call}: {errors:?}");
        assert!(errors[0].contains("sum"), "{call}: {errors:?}");
    }
    // The program the random test found (seed 11135536357509542642 of
    // `random::accepted_random_programs_raise_no_type_error`).
    let found = "h0(positional p) {\n  a, b = p;\n  return sum(a);\n}\n\
                 h1(positional p) = (3 * p[0]);\n\
                 h2(positional p, positional q) = h0(p);";
    assert_eq!(r_errors(found, "h0((-2.5, (3, 3, -2)))").len(), 1);
    // Through one and two calls that pass the pair on.
    let h1 = "h1(positional p) {\n  a, b = p;\n  return sum(a);\n}";
    for depth in [2, 3] {
        let defs = wrapped(h1, depth);
        for call in [format!("h{depth}((2.5, 1))"), format!("h{depth}((3, 1))")] {
            assert_eq!(r_errors(&defs, &call).len(), 1, "{call}");
        }
        let ok = kind_of(&format!("h{depth}(([1, 2], 3))"));
        assert_eq!(runs(&defs, &ok, ""), "int\n", "{depth}");
    }
    // A family or a tuple there is summed.
    assert_eq!(runs(defs, &kind_of("h(([1, 2], 3))"), ""), "int\n");
    assert_eq!(runs(defs, &kind_of("h(((1, 2), 3))"), ""), "int\n");
}

#[test]
fn a_rat_or_int_literal_component_is_not_summed() {
    // TEST-sum-literal-rat-path: `a_literal_component_is_not_summed` reaches `sum_beside`'s
    // `carriers_only` refusal with f64 literals and one int; here the rat and int literals, in
    // either place of the pair, directly and through one and two calls that pass it on.
    let first = "h1(positional p) {\n  a, b = p;\n  return sum(a);\n}";
    let second = "h1(positional p) {\n  a, b = p;\n  return sum(b);\n}";
    for depth in [1, 2, 3] {
        for (h1, literal_first) in [(first, true), (second, false)] {
            let defs = wrapped(h1, depth);
            for literal in ["1r", "-1r", "3r/2", "0r", "7", "-7", "0"] {
                let pair = if literal_first {
                    format!("({literal}, [1, 2])")
                } else {
                    format!("([1, 2], {literal})")
                };
                let call = format!("h{depth}({pair})");
                let errors = r_errors(&defs, &call);
                assert_eq!(errors.len(), 1, "{defs}\n{call}: {errors:?}");
                assert!(errors[0].contains("sum"), "{defs}\n{call}: {errors:?}");
            }
            // A family of rats or ints in that place is summed.
            for (family, kind) in [("[1r, 3r/2]", "rat"), ("[1, 2]", "int")] {
                let pair = if literal_first {
                    format!("({family}, 3)")
                } else {
                    format!("(3, {family})")
                };
                let ok =
                    format!(r#"if h{depth}({pair}) is {kind} {{ "{kind}" }} else {{ "other" }}"#);
                assert_eq!(runs(&defs, &ok, ""), format!("{kind}\n"), "{defs}\n{pair}");
            }
        }
    }
}

/// `n` functions, each raising 2 to the first component of its tuple argument, each called
/// once with that component at least 0 and once with it below 0 (CHK-pow-component-bound).
/// The calls below 0 are the `n` errors. The time is measured in `bench::soundness`.
pub(super) fn component_exponents(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "h{i}(positional p) {{\n  a, b = p;\n  return 2^a;\n}}\nb{i} = h{i}(({i}, 0));\nc{i} = h{i}((-{}, 0));\n",
                i + 1
            )
        })
        .collect()
}

/// `n` functions, each comparing the first component of its tuple argument, called with a
/// decimal literal there, and `n` generic functions: `n` classes outside every function whose
/// uses are left met by their mask, and `n` signatures with needs, all accepted. What the end
/// of the walk reads (CHK-obligation-sweep), its time measured in `bench::soundness`.
pub(super) fn uses_left_on_classes(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "h{i}(positional p) = if p[0] < 5 {{ p[0] }} else {{ 0 }};\nr{i} = h{i}(({i}.5, 2));\ng{i}(positional x) = x + {i};\n"
            )
        })
        .collect()
}

/// One function taking apart a tuple nested `d` deep and raising 2 to the innermost
/// component, called once with it at least 0 and once below 0: the path of the exponent's
/// bound is `d` steps long (CHK-pow-component-bound). The call below 0 is the one error.
pub(super) fn nested_component_exponent(d: usize) -> String {
    let mut text = String::from("h(positional p) {\n  a0, b0 = p;\n");
    for k in 1..d {
        text += &format!("  a{k}, b{k} = a{};\n", k - 1);
    }
    text += &format!("  return 2^a{};\n}}\n", d - 1);
    let nested = |v: &str| (0..d).fold(v.to_string(), |t, _| format!("({t}, 0)"));
    text += &format!("b = h({});\nc = h({});\n", nested("3"), nested("-3"));
    text
}

#[test]
fn component_exponents_give_one_error_per_call_below_zero() {
    // Small instances of the benchmarks in `bench::soundness`.
    let errors = super::type_errors(&component_exponents(3));
    assert_eq!(errors.len(), 3, "{errors:#?}");
    for depth in [1, 2, 5] {
        let errors = super::type_errors(&nested_component_exponent(depth));
        assert_eq!(errors.len(), 1, "{depth}: {errors:#?}");
        assert!(errors[0].contains("int[0..]"), "{depth}: {errors:#?}");
    }
}

#[test]
fn a_literal_component_is_no_negative_int_exponent() {
    // FAIL-random-pow-destructured-literal: the checker accepted each, and the kernel then
    // raised "type error: `^` applied to `int`, `int`": the exponent need of `^` was recorded
    // on the class of the literal `-3` of a call's tuple argument outside every function, and
    // that class took its type with no recorded need checked on it.
    let taken_apart = "h1(positional p) {\n  a, b = p;\n  return (0)^a;\n}";
    let indexed = "h1(positional p) = 2^p[0];";
    for h1 in [taken_apart, indexed] {
        for depth in [1, 2, 3] {
            let defs = wrapped(h1, depth);
            for literal in ["-3", "-1"] {
                let call = format!("h{depth}(({literal}, 0))");
                let errors = r_errors(&defs, &call);
                assert_eq!(errors.len(), 1, "{defs}\n{call}: {errors:?}");
                // The call is refused on the part of the argument the `^` takes.
                assert!(errors[0].contains("`p[0]`"), "{defs}\n{call}: {errors:?}");
                assert!(errors[0].contains("int[0..]"), "{defs}\n{call}: {errors:?}");
                // The same call inside a function gets the same verdict.
                let inside = format!("{defs}\ng() = {call};");
                let errors = r_errors(&inside, "g()");
                assert_eq!(errors.len(), 1, "{inside}: {errors:?}");
                assert!(errors[0].contains("int[0..]"), "{inside}: {errors:?}");
            }
            // CHK-pow-component-bound: the exponent's bound is carried through the component
            // into the signature, as `h1(x) = 2^x` takes `x` in `int[0..]`, so a component at
            // least 0 is accepted, inside a function and outside every function.
            let call = format!("h{depth}((3, 0))");
            assert_eq!(runs(&defs, &kind_of(&call), ""), "int\n", "{defs}\n{call}");
            let inside = format!("{defs}\ng() = {call};");
            assert_eq!(runs(&inside, &kind_of("g()"), ""), "int\n", "{inside}");
        }
    }
    // The bound of a component is the component's alone: `a - 5` lies in the class of the
    // literal `3` of `h1((3, 0))`, which takes its whole carrier `int`, so `0^(a - 5)` stays
    // refused, as `popCount(a - 5)` does on the class (the need `NoInt` checked when the
    // class takes its type outside every function).
    for body in ["0^(a - 5)", "popCount(a - 5)"] {
        let defs = format!("h1(positional p) {{\n  a, b = p;\n  return {body};\n}}");
        let word = if body.starts_with('0') {
            "^"
        } else {
            "popCount"
        };
        let errors = r_errors(&defs, "h1((3, 0))");
        assert_eq!(errors.len(), 1, "{defs}: {errors:?}");
        assert!(errors[0].contains(word), "{defs}: {errors:?}");
        let inside = format!("{defs}\ng() = h1((3, 0));");
        assert_eq!(r_errors(&inside, "g()").len(), 1, "{inside}");
    }
    // A component read by `popCount` takes its bound the same way.
    let pop = "h1(positional p) {\n  a, b = p;\n  return popCount(a);\n}";
    assert_eq!(runs(pop, &kind_of("h1((3, 0))"), ""), "int\n");
    let errors = r_errors(pop, "h1((-3, 0))");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("`p[0]`"), "{errors:?}");
    // A test on the parameter, or on the component, narrows it where the `^` is.
    let whole = "h1(x) = if x >= 0 { 0^x } else { 0 };";
    assert_eq!(runs(whole, &kind_of("h1(x: -3)"), ""), "int\n");
    assert_eq!(runs(whole, &kind_of("h1(x: 3)"), ""), "int\n");
    let narrowed = "h1(positional p) {\n  a, b = p;\n  return if a >= 0 { 0^a } else { 0 };\n}";
    assert_eq!(runs(narrowed, &kind_of("h1((-3, 0))"), ""), "int\n");
    // A component of a component, and a name bound to the argument in the caller.
    let nested = "h1(positional p) {\n  a, b = p;\n  c, d = a;\n  return 2^d;\n}";
    assert_eq!(runs(nested, &kind_of("h1(((0, 3), 0))"), ""), "int\n");
    assert_eq!(r_errors(nested, "h1(((0, -3), 0))").len(), 1);
    let named = "h1(positional p) = 2^p[1];\ng() {\n  t = (0, -2);\n  return h1(t);\n}";
    assert_eq!(r_errors(named, "g()").len(), 1);
    // A base that is no int takes any int exponent, and a parameter or a literal taken apart
    // inside the function is bounded where the `^` is.
    let rat_base = "h1(positional p) {\n  a, b = p;\n  return 2r^a;\n}";
    let ok = r#"if h1((-3, 0)) is rat { "rat" } else { "other" }"#;
    assert_eq!(runs(rat_base, ok, ""), "rat\n");
    assert_eq!(runs("h1(x) = 2^x;", &kind_of("h1(x: 3)"), ""), "int\n");
    assert_eq!(r_errors("h1(x) = 2^x;", "h1(x: -3)").len(), 1);
    let local = "g() {\n  a, b = (3, 0);\n  return 0^a;\n}";
    assert_eq!(runs(local, &kind_of("g()"), ""), "int\n");
    // The program the random test found (seed 5371329205760031685 of
    // `random::accepted_random_programs_raise_no_type_error`).
    let found = "h0(positional p) {\n  a, b = p;\n  return (0)^a;\n}\n\
                 h1(positional p) = (p[1] - p[1]);";
    let errors = r_errors(found, "h0((-3, if 0 < 3 { 0 } else { 0 }))");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

/// `defs` with `h2` … `h{depth}` added, each passing its argument on to the one before:
/// `h2(positional p) = h1(p);`.
fn wrapped(defs: &str, depth: usize) -> String {
    let mut s = defs.to_string();
    for k in 2..=depth {
        s.push_str(&format!("\nh{k}(positional p) = h{}(p);", k - 1));
    }
    s
}

/// Asserts that the error `e` writes, in this order, the note "`h{k}` needs this of its
/// argument here" for each `k` from `depth` down to 0, each followed by the line at `lines[k]`
/// (from `lines`, the line of `h0` first, then that of `h1`; a wrapper's line is its call
/// `h{k-1}(p)`), and no other such note.
fn chain_notes(e: &str, depth: usize, lines: [&str; 2]) {
    let mut from = 0;
    for k in (0..=depth).rev() {
        let note = format!("`h{k}` needs this of its argument here");
        let at = e[from..]
            .find(&note)
            .unwrap_or_else(|| panic!("no note `{note}` after byte {from}:\n{e}"));
        from += at + note.len();
        let line = match k {
            0 | 1 => lines[k].to_string(),
            _ => format!("h{}(p)", k - 1),
        };
        // The note's own lines: up to the next note.
        let tail = &e[from..];
        let block = &tail[..tail.find("\n  [").unwrap_or(tail.len())];
        assert!(
            block.contains(&line),
            "the note for `h{k}` shows `{line}`:\n{e}"
        );
        assert_eq!(e.matches(&note).count(), 1, "one note `{note}`:\n{e}");
    }
    assert!(
        !e.contains(&format!("`h{}` needs this", depth + 1)),
        "no note past the call:\n{e}"
    );
}

/// Plan row DIAG-call-chain-full (L1.29, error-messages-derivation): a rejection at a call
/// whose need came through calls names every call on the path from the argument to the line
/// that needs it, outermost first, one note each: the destructuring, the index and the call of
/// a component passed on through one, two and three calls.
#[test]
fn a_rejection_at_a_call_names_each_call_on_the_path() {
    let destructured = passed("b");
    let indexed = "h0(positional p) = p[0][1];\n\
                   h1(positional p) {\n  a, b = p;\n  return h0((b, 1));\n}";
    let called = "h0(positional f) = f(1);\n\
                  h1(positional p) {\n  a, b = p;\n  return h0(b);\n}";
    for (defs, lines) in [
        (&*destructured, ["a, b, c = p;", "return h0(b, 1);"]),
        (indexed, ["p[0][1]", "return h0((b, 1));"]),
        (called, ["f(1)", "return h0(b);"]),
    ] {
        for depth in 1..=3 {
            let defs = wrapped(defs, depth);
            let e = rejected(&defs, &kind_of(&format!("h{depth}((1, 3))")));
            chain_notes(&e, depth, lines);
        }
    }
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
    rejected(f, r#"String(f(1))"#);
    let ok = "f(positional x, y = x) = y + 1;";
    assert_eq!(runs(ok, r#"String(f(1))"#, ""), "2\n");
}

#[test]
fn a_tuple_default_of_a_nested_function_used_as_a_number_is_rejected() {
    let outer =
        "outer(positional x) = {\n  inner(positional y, w = (y, 1)) = w + 1;\n  inner(x)\n};";
    assert_eq!(
        super::type_errors(outer),
        ["`+` does not take (_, 1): no arrow of `+` takes these types. [w + 1]"]
    );
    rejected(outer, r#"String(outer(1))"#);
    let ok = "outer(positional x) = {\n  inner(positional y, w = y) = w + 1;\n  inner(x)\n};";
    assert_eq!(runs(ok, r#"String(outer(1))"#, ""), "2\n");
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
               main(m: MainArgs) {\n  n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n  \
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
            "  n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n  m.stdout <- \"${if n >= 0 { rat(n)^-1 } else { 0r }}\";",
        ),
        "1",
        &[],
    );
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(
        out.stderr.contains(": String | #divByZero`"),
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

/// An operation on literals alone whose divisor or base is no zero is pushed to a port with
/// no `else`: `(2r/3r)^-2` and `1r / (2r/3r)` carry no `#divByZero`, though `rat` holds `0r`
/// (POW-rat-literal-ops). Before, the port refused each as `String | #divByZero`. A divisor or
/// base that is zero keeps the atom, and the port refuses it.
#[test]
fn a_port_takes_an_operation_on_literals_whose_divisor_is_no_zero() {
    for (e, want) in [
        ("(2r/3r)^-2", "9r/4r"),
        ("1r / (2r/3r)", "3r/2r"),
        ("(3/2)^-2 * 1r", "4r/9r"),
        ("-(3/2)^-3 * 1r", "-8r/27r"),
        ("(1/2)^-1 * 2r", "4r"),
        ("(3/2)^-2 * 2.0f64", "0.8888888888888888"),
    ] {
        assert_eq!(
            runs("", &format!("\"${{{e}}}\""), ""),
            format!("{want}\n"),
            "{e}"
        );
    }
    for e in [
        "(0r)^-1",
        "1r / (1r - 1r)",
        "(1 - 1)^-1 * 1r",
        "1r / (1 - 1)",
    ] {
        let out = rejected("", &format!("\"${{{e}}}\""));
        let refused = format!(
            "A `Lines` port takes a `String` or a family of strings: \
             `m.stdout <- \"${{{e}}}\" : String | #divByZero`."
        );
        assert!(out.contains(&refused), "{e}: {out}");
        let handled = format!("\"${{{e} else #divByZero -> 0r}}\"");
        assert_eq!(runs("", &handled, ""), "0r\n", "{e}");
    }
    // An integer exponent keeps `int`, so `2 ^ -1` is an `int` power with a negative exponent,
    // and the menu offers the exact `rat` power beside the float ones; each repair runs.
    let out = rejected("", "\"${2 ^ -1}\"");
    assert!(
        out.contains("Int power with a negative exponent: `2 : int ^ -1 : int`."),
        "{out}"
    );
    for (repair, want) in [
        ("2.0f64 ^ -1", "0.5"),
        ("2 ^ -1.0f64", "0.5"),
        ("2r ^ -1", "1r/2r"),
    ] {
        assert!(
            out.contains(&format!("repair: `{repair}`")),
            "{repair}: {out}"
        );
        assert_eq!(
            runs("", &format!("\"${{{repair}}}\""), ""),
            format!("{want}\n"),
            "{repair}"
        );
    }
    // A parameter is no operation on literals: its value is not in the text, so the literal
    // exponent stays in the parameter's class, and `p` takes no `rat`, whose `^` would need
    // the exponent at `int` and could give `#divByZero` at `0r`.
    let out = rejected("p(positional b) = b ^ -1;", "\"${p(2r)}\"");
    assert!(
        out.contains("`p` takes T -> T for T in int | f32 | f64"),
        "{out}"
    );
}

/// A `/` of integer literals under a `^` is refused at `/`, which has no arrow at `int`, and
/// not taken as `f64`: the menu offers the exact `rat` power first, which runs as printed
/// (POW-rat-literal-ops).
#[test]
fn a_power_of_a_division_of_integer_literals_is_refused_with_the_exact_fix() {
    let out = power_case(
        "",
        "  m.stdout <- \"${(3/2)^-2}\";",
        &[("  m.stdout <- \"${(3r/2)^-2}\";", "", "4r/9r\n")],
    );
    assert_eq!(
        out.trim_end(),
        "3:19: Nothing gives the literal `3` a carrier. Try \
         `m.stdout <- \"${(3r/2)^-2}\"` instead.\n  \
         fixes, each checked here:\n    \
         m.stdout <- \"${(3r/2)^-2}\";        the literal is then exactly 3, a rat\n    \
         m.stdout <- \"${(3.0f64/2)^-2}\";    the literal is then the f64 3.0"
    );
    assert_eq!(
        runs("", r#""${(3.0f64/2)^-2}""#, ""),
        "0.4444444444444444\n"
    );
}

/// The two seeds the random test found (FAIL-random-f64-destructured-family,
/// FAIL-random-pow-destructured-literal), each with the specific fix that refuses it turned
/// off (`obligation_test_modes`, TEST-random-sweep-off): with the end-of-walk check off too,
/// each is accepted, the fault the kernel then met (red); with it on, each is refused, by the
/// check of the use no step discharged (green, CHK-obligation-sweep). With the fixes on each
/// is refused once too; the power seed's message then names `p[0]` at the call
/// (CHK-pow-component-bound), where the end-of-walk check names the `^`.
#[test]
fn the_end_of_walk_check_alone_refuses_both_seeds() {
    use zedc::check::obligation_test_modes::set;
    let summed = "h0(positional p) {\n  a, b = p;\n  return sum(a);\n}";
    let power = "h1(positional p) {\n  a, b = p;\n  return (0)^a;\n}";
    for (defs, call) in [(summed, "h0((-2.5, (3, 3, -2)))"), (power, "h1((-3, 0))")] {
        set(true, true);
        let red = r_errors(defs, call);
        set(true, false);
        let green = r_errors(defs, call);
        set(false, false);
        assert!(red.is_empty(), "{defs}\n{call}: {red:?}");
        assert_eq!(green.len(), 1, "{defs}\n{call}: {green:?}");
        assert_eq!(r_errors(defs, call).len(), 1, "{defs}\n{call}");
    }
}
