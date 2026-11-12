//! A value of type `1 | f64`, the result of a call such as `g(c, x) = if c { x } else { 1 }`
//! or an inline `if`, is read at an `f64` parameter and beside an `f64` operand of an
//! operator, each value as it would be alone: the `f64` as it is and the integer `1` at `f64`
//! (DESIGN.md step L1.26a, rule 3: "`if c { 1 } else { 2.5f64 }` is `1 | f64` ... the
//! literal `1` taking its carrier where the result is used"). The same per-value split as a
//! cast of such a union (LIT-cast-of-literal-union). A value with no exact `f64`, or a member
//! that is no number, is still refused; a name bound to such a value is fixed at its binding
//! and not read. Item LIT-call-union-at-f64.

use std::ffi::OsString;

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};

const G: &str = "g(positional c: bool, positional x: f64) = if c { x } else { 1 };\n\
                 h(positional z: f64) = z;\n";

/// `G`, then `k(b, x) = <body>` and `k` applied to `(true, 2.5)` and `(false, 2.5)` as `t`
/// and `f`.
fn with(body: &str) -> String {
    format!(
        "{G}k(positional b: bool, positional x: f64) = {body};\n\
         t = k(true, 2.5f64);\nf = k(false, 2.5f64);\n"
    )
}

/// `body` is accepted, `k` gives an `f64`, and `k(true, 2.5)` and `k(false, 2.5)` give `t`
/// and `f`.
fn accepted(body: &str, t: &str, f: &str) {
    let src = with(body);
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{body}");
    assert_eq!(sig(&src, "k"), "(bool, f64) -> f64", "{body}");
    assert_eq!(
        (value(&src, "t").as_str(), value(&src, "f").as_str()),
        (t, f),
        "{body}"
    );
}

#[test]
fn a_call_of_type_1_or_f64_is_read_at_an_f64_parameter() {
    assert_eq!(sig(G, "g"), "(bool, f64) -> 1 | f64");
    accepted("h(g(b, x))", "2.5", "1.0");
}

#[test]
fn a_call_of_type_1_or_f64_is_read_beside_an_f64_operand() {
    // Each operator with an `f64` beside the call, on either side; the comparisons give a
    // `bool`, so they stand as the condition of an `if` passed to `h`.
    accepted("x + g(b, x)", "5.0", "3.5");
    accepted("g(b, x) + x", "5.0", "3.5");
    accepted("x * g(b, x)", "6.25", "2.5");
    accepted("1.0f64 + g(b, x)", "3.5", "2.0");
    accepted("max(g(b, x), x)", "2.5", "2.5");
    accepted(
        "h(if g(b, x) == x { 1.0f64 } else { 0.0f64 })",
        "1.0",
        "0.0",
    );
    accepted("h(if g(b, x) < x { 1.0f64 } else { 0.0f64 })", "0.0", "1.0");
}

#[test]
fn an_inline_if_of_type_1_or_f64_is_read_at_an_f64_parameter() {
    // The DESIGN.md example itself, and branches that are calls of `g` beside a literal.
    accepted("h(if b { x } else { 1 })", "2.5", "1.0");
    accepted("x + (if b { x } else { 1 })", "5.0", "3.5");
    accepted("h(if b { g(b, x) } else { 3 })", "2.5", "3.0");
    accepted("h(if b { x } else { 2.5 })", "2.5", "2.5");
}

#[test]
fn nested_ifs_of_calls_and_literals_are_read_at_f64() {
    // Nested at the use and in the body of the called procedure.
    accepted("h(if b { if b { x } else { 1 } } else { 2 })", "2.5", "2.0");
    accepted(
        "h(if b { g(b, x) } else { if b { 3 } else { g(b, x) } })",
        "2.5",
        "1.0",
    );
    let src = format!(
        "{G}n(positional b: bool, positional x: f64) = if b {{ if b {{ x }} else {{ 1 }} }} else {{ g(b, x) }};\n\
         k(positional b: bool, positional x: f64) = h(n(b, x)) + n(b, x);\n\
         t = k(true, 2.5f64);\nf = k(false, 2.5f64);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "n"), "(bool, f64) -> 1 | f64");
    assert_eq!(
        (value(&src, "t").as_str(), value(&src, "f").as_str()),
        ("5.0", "2.0")
    );
}

#[test]
fn an_integer_with_no_exact_f64_is_still_refused() {
    // 2^53 + 1 has no exact `f64`, so the branch is not read at `f64`, as `h(9007199254740993)`
    // is not. The `if` is named, not written out again: the message stands at it.
    assert_eq!(
        type_errors(&with("h(if b { x } else { 9007199254740993 })")),
        [
            "No `f64` equals 9007199254740993, which the `if` may give. \
             [h(if b { x } else { 9007199254740993 })]"
        ]
    );
}

#[test]
fn a_member_that_is_no_number_is_still_refused() {
    // The value no arrow takes is named in place of the type (MSG-call-union-headline).
    assert_eq!(
        type_errors(&with("h(if b { x } else { true })")),
        [
            "`h` does not take (true): no arrow of `h` takes these types. [h(if b { x } else { true })]"
        ]
    );
}

#[test]
fn a_name_bound_to_the_call_is_fixed_at_its_binding() {
    // DESIGN.md step L1.26a: a name bound alone is fixed at its binding; `y` is `1 | f64`
    // there and is not read again where it is used.
    assert_eq!(
        type_errors(&with("{ y = g(b, x); h(y) }")),
        ["`h` does not take (1): no arrow of `h` takes these types. [h(y)]"]
    );
}

const PROGRAM: &str = "\
g(positional c: bool, positional x: f64) = if c { x } else { 1 };
h(positional z: f64) = z;

main(m: MainArgs) {
  x = f64(m.args[0] else \"\") else 0.0;
  b = x < 0.0;
  m.stdout <- \"${h(g(b, x))} ${x + g(b, x)} ${h(if b { g(b, x) } else { if b { 3 } else { 2 } })}\";
}
";

#[test]
fn the_executable_prints_the_interpreter_s_values() {
    let d = dir("call_union_at_f64");
    let src = d.join("call_union.zed");
    std::fs::write(&src, PROGRAM).unwrap();
    let exe = d.join("call_union");
    built(&src, &exe);
    for (x, want) in [("-2.5", "-2.5 -5.0 -2.5\n"), ("4.0", "1.0 5.0 2.0\n")] {
        let words: Vec<OsString> = vec!["--".into(), x.into()];
        let native = executable(&exe, &words, b"");
        assert_eq!(native, interpreter(&src, &words, b""), "{x}");
        assert_eq!((native.status, native.stdout.as_str()), (0, want), "{x}");
    }
}

/// `n` nested `if`s whose branches are, in turn, `x`, a call of `g` and an integer literal:
/// `f` returns them, so its type lists about n/3 integers beside `f64`, and `k` reads `f`'s
/// result at an `f64` parameter and beside an `f64` operand, and the `if`s themselves at `h`.
fn nest(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        let leaf = match i % 3 {
            0 => "x".to_string(),
            1 => "g(b, x)".to_string(),
            _ => format!("{i}"),
        };
        body += &format!("if c == {i} {{ {leaf} }} else ");
    }
    body += &format!("{{ {n} }}");
    format!(
        "{G}f(positional c: int, positional b: bool, positional x: f64) = {body};\n\
         k(positional c: int, positional b: bool, positional x: f64) = \
         h(f(c, b, x)) + x * f(c, b, x) + h({body});\n"
    )
}

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): whether an argument may be read is found by
    // one walk over the branches of its `if`s, each visited once, O(n); then the values of
    // its type outside `f64` are listed once, each is cast once, and the parts are joined in
    // pairs, as for a cast of the union, O(n log n). Listing them again for each value, or
    // walking the branches again for each, would be O(n^2).
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&nest(5)), Vec::<String>::new());
            assert_eq!(sig(&nest(5), "f"), "(int, bool, f64) -> 1 | 2 | 5 | f64");
            assert_eq!(sig(&nest(5), "k"), "(int, bool, f64) -> f64");
            let n = 250;
            let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
            scaling::check(
                "reading a call of n listed values and an `if` of n branches at `f64`",
                n,
                |m| {
                    units[&m].check();
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
