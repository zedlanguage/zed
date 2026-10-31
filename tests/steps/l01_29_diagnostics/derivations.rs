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
        r#"4:13: `++` does not take ("total: ", int)
  [1]  4:13: this expression is "total: "
       4 |   stdout <- "total: " ++ total;
         |             ^^^^^^^^^
  [2]  4:26: `total` is int | _ here
       4 |   stdout <- "total: " ++ total;
         |                          ^^^^^
  [3]  3:11: `total` is defined as this expression, int | _
       3 |   total = n * 2;
         |           ^^^^^
  [4]  3:11: this `*` gives int | _
  [5]  3:11: `n` is 0 | _ here
       3 |   total = n * 2;
         |           ^
  [6]  2:7: `n` is defined as this expression, 0 | _
       2 |   n = int(stdin[1]) else 0;
         |       ^^^^^^^^^^^^^^^^^^^^
  [7]  2:7: this `else` gives 0 | _
  [8]  2:7: this call of `int` gives _
       2 |   n = int(stdin[1]) else 0;
         |       ^^^^^^^^^^^^^
  [9]  2:11: this expression gives _
       2 |   n = int(stdin[1]) else 0;
         |           ^^^^^^^^
  [10] 2:11: `stdin` is _ here
       2 |   n = int(stdin[1]) else 0;
         |           ^^^^^
  [11] 1:6: `stdin` is declared `Lines`, whose values the checker does not track: it takes `stdin` as unknown, _
       1 | main(stdin: Lines) -> (stdout: Lines) {
         |      ^^^^^^^^^^^^
  [12] 2:26: this literal, 0, is 0
       2 |   n = int(stdin[1]) else 0;
         |                          ^
  [13] 3:15: this literal, 2, is 2
       3 |   total = n * 2;
         |               ^
  [14] 4:13: `++` takes (String, String) -> String
       4 |   stdout <- "total: " ++ total;
         |             ^^^^^^^^^^^^^^^^^^
  [15] 4:26: repair: wrap this in `String(…)`; the checker accepts that
       4 |   stdout <- "total: " ++ total;
         |                          ^^^^^"#
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
            "`discount` takes (price: int, tier: T) -> int",
            "`discount` is declared here, `(price: int, tier: T) -> int`",
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
        s[narrowed + 1] == "`v` has no declared type; its uses give it T",
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
        "3:3: `rate` is already bound in this scope
  [1] 2:3: the first binding of `rate`
      2 |   rate = 3;
        |   ^^^^^^^^^"
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
    assert_eq!(first, "1:23: `++` does not take (\"#\", int | f64 | rat)");
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
        "1:36: `++` does not take (\"#\", int | f64 | rat)"
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
        "twice(positional x) = x * 2;
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
            "repair: wrap this in `String(…)`; the checker accepts that",
        ]
    );
}
