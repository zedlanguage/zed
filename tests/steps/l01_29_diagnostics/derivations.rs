//! What a derivation contains: the chain from the rejected term back to the declarations its
//! types come from.

use super::{rejected, steps};

#[test]
fn a_report_line_that_concatenates_a_number_shows_the_chain_back_to_the_input_port() {
    let out = rejected(
        "main(stdin: Lines) -> (stdout: Lines) {
  n = int(stdin[1]) else 0;
  total = n * 2;
  stdout <- \"total: \" ++ total;
}
",
    );
    assert_eq!(
        out,
        r#"4:13: `++` does not take ("total: ", int): these are the types of its arguments here, and `++` has no arrow that takes them all
  [1]  4:13: this expression is "total: "
       4 |   stdout <- "total: " ++ total;
         |             ^^^^^^^^^ [1]
         |             ^^^^^^^^^^^^^^^^^^ [14]
         |                          ^^^^^ [2, 15]
  [2]  4:26: `total` is int here
  [3]  3:11: `total` is defined as this expression, int
       3 |   total = n * 2;
         |           ^ [5]
         |           ^^^^^ [3, 4]
         |               ^ [13]
  [4]  3:11: this `*` gives int
  [5]  3:11: `n` is int here
  [6]  2:7: `n` is defined as this expression, int
       2 |   n = int(stdin[1]) else 0;
         |       ^^^^^^^^^^^^^^^^^^^^ [6, 7]
         |           ^^^^^ [10]     ^ [12]
         |           ^^^^^^^^ [9]
         |       ^-----------^ [8]
  [7]  2:7: this `else` gives int
  [8]  2:7: this call of `int` gives int | #invalid | #notFound | #ioError(op: String, path: String, why: String)
  [9]  2:11: this expression gives String | #notFound | #ioError(op: String, path: String, why: String)
  [10] 2:11: `stdin` is (int) -> String | #notFound | #ioError(op: String, path: String, why: String) here
  [11] 1:6: `stdin` is declared `Lines`
       1 | main(stdin: Lines) -> (stdout: Lines) {
         |      ^^^^^^^^^^^^
  [12] 2:26: this literal, 0, is 0
  [13] 3:15: this literal, 2, is 2
  [14] 4:13: `++` takes (String, String) -> String
  [15] 4:26: repair: write `String(total)`; the checker accepts that"#
    );
}

#[test]
fn a_call_of_a_declared_function_shows_the_declaration_and_its_signature() {
    let out = rejected(
        "discount(price: int, tier) = if tier == #gold { price * 8 } else { price * 10 };
main(stdin: Lines) -> (stdout: Lines) {
  p = discount(price: \"12\", tier: #gold);
  stdout <- String(p);
}
",
    );
    assert_eq!(
        steps(&out),
        [
            "this expression is \"12\"",
            "this expression is #gold",
            "`discount` takes (price: int, tier: _) -> int",
            "`discount` is declared here, `(price: int, tier: _) -> int`",
        ]
    );
}

#[test]
fn a_test_that_narrows_a_parameter_is_a_step_with_the_parameter_it_narrowed() {
    let out = rejected(
        "label(positional v) = if v is int { \"n\" ++ v } else { \"s\" };
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- label(3);
}
",
    );
    let s = steps(&out);
    let narrowed = s
        .iter()
        .position(|t| *t == "`v` is narrowed to int where this test decides")
        .unwrap_or_else(|| panic!("{out}"));
    assert_eq!(s[narrowed - 1], "`v` is int here");
    assert!(
        s[narrowed + 1] == "`v` has no declared type; its uses give it _",
        "{out}"
    );
}

#[test]
fn a_rebinding_points_at_the_first_binding() {
    let out = rejected(
        "main(stdin: Lines) -> (stdout: Lines) {
  rate = 3;
  rate = 4;
  stdout <- \"x\";
}
",
    );
    assert_eq!(
        out,
        "3:3: `rate` is already bound in this scope, and a scope binds each name once
  [1] 2:3: the first binding of `rate`
      2 |   rate = 3;
        |   ^^^^^^^^^
  [2] 3:3: repair: give this binding a new name
      3 |   rate = 4;
        |   ^^^^^^^^^
  [3] 3:3: repair: move this binding into a nested block, where it shadows the first"
    );
}

#[test]
fn an_error_in_a_function_is_at_the_use_that_leaves_its_parameter_no_carrier() {
    let out = rejected(
        "badge(positional x) = \"#\" ++ x * 2;
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- badge(3);
}
",
    );
    let first = out.lines().next().unwrap();
    assert_eq!(
        first,
        "1:23: `++` does not take (\"#\", int | f64 | rat): these are the types of its arguments here, and `++` has no arrow that takes them all"
    );
    let s = steps(&out);
    for step in [
        "this `*` gives int | f64 | rat",
        "`x` is int | f64 | rat here",
        "the literal 2 takes int | f64 | rat",
        "`++` takes (String, String) -> String",
    ] {
        assert!(s.contains(&step), "{step}\n{out}");
    }
}

#[test]
fn an_error_over_several_parameters_is_one_error_with_the_use_that_joined_them() {
    // The search this replaces tried 25 combinations of carriers and showed 12.
    let out = rejected(
        "area(positional w, positional h) = \"#\" ++ w * h;
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- area(2, 3);
}
",
    );
    assert_eq!(
        out.lines().next().unwrap(),
        "1:36: `++` does not take (\"#\", int | f64 | rat): these are the types of its arguments here, and `++` has no arrow that takes them all"
    );
    let s = steps(&out);
    for step in [
        "`w` is int | f64 | rat here",
        "`h` is int | f64 | rat here",
        "`*` gives these values one carrier",
        "`*` takes int | f64 | rat",
    ] {
        assert!(s.contains(&step), "{step}\n{out}");
    }
    assert!(!s.iter().any(|t| t.starts_with("with ")), "{out}");
}

#[test]
fn a_function_whose_search_succeeded_shows_its_signature_not_the_abandoned_runs() {
    let out = rejected(
        "twice(positional x) = x * int(2);
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- \"a\" ++ twice(3);
}
",
    );
    assert_eq!(
        steps(&out),
        [
            "this expression is \"a\"",
            "this call of `twice` gives int",
            "`twice` is declared here, `(int) -> int`",
            "`++` takes (String, String) -> String",
            "repair: wrap this in `String(…)`; the checker accepts that",
        ]
    );
}

#[test]
fn a_long_chain_is_shown_whole_back_to_its_first_binding() {
    let mut src = String::from("main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n");
    for i in 1..25 {
        src += &format!("  a{i} = a{} + 1;\n", i - 1);
    }
    src += "  stdout <- \"x\" ++ a24;\n}\n";
    let out = rejected(&src);
    let s = steps(&out);
    assert!(!out.contains("goes back further"), "{out}");
    for i in 1..25 {
        let t = format!("`a{i}` is int here");
        assert_eq!(s.iter().filter(|x| **x == t).count(), 1, "{t}: {out}");
    }
    assert!(s.contains(&"`a0` is 1 here"), "{out}");
    assert!(
        s.contains(&"`a0` is defined as this expression, 1"),
        "{out}"
    );
}

#[test]
fn a_value_read_twice_is_derived_once() {
    // Each `a{i}` reads `a{i-1}` twice; without a visited set the derivation doubles at each
    // binding.
    let mut src = String::from("main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n");
    for i in 1..40 {
        src += &format!("  a{i} = a{p} + a{p};\n", p = i - 1);
    }
    src += "  stdout <- \"x\" ++ a39;\n}\n";
    let out = rejected(&src);
    let s = steps(&out);
    assert!(
        s.contains(&"`a0` is defined as this expression, 1"),
        "{out}"
    );
    for i in 1..40 {
        let t = format!("`a{i}` is defined as this expression, int");
        assert_eq!(s.iter().filter(|x| **x == t).count(), 1, "{t}: {out}");
    }
}

#[test]
fn a_body_reading_a_top_level_value_shows_that_value_s_whole_chain() {
    let out = rejected(
        "base = 4;
rate = base * 3;
tag(positional x) = \"rate \" ++ rate;
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- tag(1);
}
",
    );
    assert_eq!(
        steps(&out),
        [
            "this expression is \"rate \"",
            "`rate` is int here",
            "`rate` is defined as this expression, int",
            "this `*` gives int",
            "`base` is 4 here",
            "`base` is defined as this expression, 4",
            "this expression is 4",
            "this literal, 3, is 3",
            "`++` takes (String, String) -> String",
            "repair: write `String(rate)`; the checker accepts that",
        ]
    );
}

#[test]
fn a_rejected_nested_tuple_shows_each_tuple_and_its_type() {
    // A tuple keeps no type of its own as the checker walks; its derivation finds it from its
    // components, at any depth.
    let out = rejected("x = \"pair: \" ++ ((1, 2.5), \"a\");\n");
    assert_eq!(
        out,
        r#"1:5: `++` does not take ("pair: ", ((1, 2.5), "a")): these are the types of its arguments here, and `++` has no arrow that takes them all
  [1] 1:5: this expression is "pair: "
      1 | x = "pair: " ++ ((1, 2.5), "a");
        |     ^^^^^^^^ [1] ^^^^^^^^ [3]
        |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^ [7]
        |                   ^ [4]    ^^^ [6]
        |                      ^^^ [5]
        |                 ^-------------^ [2, 8]
  [2] 1:17: this expression gives ((1, 2.5), "a")
  [3] 1:18: this expression gives (1, 2.5)
  [4] 1:19: this literal, 1, is 1
  [5] 1:22: this literal, 2.5, is 2.5
  [6] 1:28: this expression is "a"
  [7] 1:5: `++` takes (String, String) -> String
  [8] 1:17: repair: wrap this in `String(…)`; the checker accepts that"#
    );
}

/// A use that leaves a class only values other than carriers, as a comparison with a tuple
/// does, is listed with what it takes as type syntax: `_`, the type of every value, since
/// `int | _` is `_` (DESIGN.md L1.26; BOUNDS-other).
#[test]
fn a_use_that_takes_other_values_is_listed_as_taking_every_value() {
    let out = rejected(
        "twice(positional p) = if p < (1, 2) { p * 2 } else { 0 };
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- \"x\";
}
",
    );
    assert!(steps(&out).contains(&"`<` takes _"), "{out}");
    assert!(!out.contains("other values"), "{out}");
}

#[test]
fn equality_on_an_atom_whose_payload_holds_a_function_shows_where_the_function_came_from() {
    // A payload may hold a function (DESIGN.md, `#atom(t)`), and `==` compares payloads, so
    // the refusal follows the value back through the atom to the function it holds.
    let out = rejected("inc = x -> x + 1;\nboxed = #box(inc);\nsame = boxed == boxed;\n");
    assert_eq!(
        out,
        "3:8: `==` takes data, and this value may hold a function, `(T) -> T for T in int | f64 | rat`: data is a value that holds no function at any depth
  [1] 3:8: `boxed` is #box((T) -> T for T in int | f64 | rat) here
      3 | same = boxed == boxed;
        |        ^^^^^ [1]
        |        ^^^^^^^^^^^^^^ [7, 8]
  [2] 2:9: `boxed` is defined as this expression, #box((T) -> T for T in int | f64 | rat)
      2 | boxed = #box(inc);
        |         ^^^^^^^^^ [2, 3]
        |              ^^^ [4]
  [3] 2:9: this atom `#box` with its payload gives #box((T) -> T for T in int | f64 | rat)
  [4] 2:14: `inc` is (T) -> T for T in int | f64 | rat here
  [5] 1:7: `inc` is defined as this expression, (T) -> T for T in int | f64 | rat
      1 | inc = x -> x + 1;
        |       ^^^^^^^^^^
  [6] 1:7: this expression is (T) -> T for T in int | f64 | rat
  [7] 3:8: repair: call the function before the value gets here, so that the value holds its result and not the function
  [8] 3:8: repair: keep the function under its own name, out of the value"
    );
}

#[test]
fn equality_on_a_payload_that_holds_a_parameter_shows_the_need_it_puts_on_the_argument() {
    // `g` compares a tuple whose atom's payload holds `g`'s parameter, so `==` needs the
    // parameter to be data; the call with a function is refused, with the need's place and
    // the declaration of `g` (ATOM-payload-open: the variable in the payload was not seen).
    let out = rejected(
        "h(positional x) = x * 2;
f(positional x) { return #a(x), 1; }
g(positional x) { p = f(x); return p == p; }
s = g(h);
",
    );
    assert_eq!(
        out,
        "4:5: `==` takes data, and this value may hold a function, `(T) -> T for T in int | f64 | rat`: data is a value that holds no function at any depth
  [1] 3:36: `g` needs this of its argument here
      3 | g(positional x) { p = f(x); return p == p; }
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]
        |                                    ^^^^^^ [1]
  [2] 3:1: `g` is declared here, `(_) -> bool`
  [3] 4:5: repair: call the function before the value gets here, so that the value holds its result and not the function
      4 | s = g(h);
        |     ^^^^
  [4] 4:5: repair: keep the function under its own name, out of the value"
    );
}
