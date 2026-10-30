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
        s[narrowed + 1].starts_with("`v` has no declared type; the signature search checks"),
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
fn a_failed_signature_search_lists_each_combination_with_its_own_derivation() {
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
        "1:1: `badge` checks at no type of `x`: with `x`: int, `++` does not take (\"#\", int)"
    );
    let s = steps(&out);
    let with: Vec<&&str> = s.iter().filter(|t| t.starts_with("with ")).collect();
    assert_eq!(
        with,
        [
            &"with `x`: int, `++` does not take (\"#\", int)",
            &"with `x`: f64, `++` does not take (\"#\", f64)",
            &"with `x`: rat, `++` does not take (\"#\", rat)",
            &"with `x`: String, `*` does not take (String, 2)",
            &"with `x`: bool, `*` does not take (bool, 2)",
        ]
    );
    for c in ["int", "f64", "rat", "String", "bool"] {
        let taken = format!("`x` has no declared type; the signature search takes it as {c}");
        assert!(s.contains(&taken.as_str()), "{taken}\n{out}");
    }
    assert!(s.contains(&"`*` takes (int, int) -> int"), "{out}");
}

#[test]
fn a_search_over_many_combinations_shows_twelve_and_counts_the_rest() {
    let out = rejected(
        "area(positional w, positional h) = \"#\" ++ w * h;
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- area(2, 3);
}
",
    );
    let s = steps(&out);
    assert_eq!(s.iter().filter(|t| t.starts_with("with ")).count(), 12);
    assert_eq!(
        s.last(),
        Some(&"13 more combinations fail; the first 12 are shown")
    );
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
fn a_long_chain_is_cut_after_sixteen_steps_back_and_says_so() {
    let mut src = String::from("main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n");
    for i in 1..25 {
        src += &format!("  a{i} = a{} + 1;\n", i - 1);
    }
    src += "  stdout <- \"x\" ++ a24;\n}\n";
    let out = rejected(&src);
    let s = steps(&out);
    assert_eq!(
        s.iter().filter(|t| t.contains("goes back further")).count(),
        1,
        "{out}"
    );
    assert!(
        out.contains("18:9: this is int; its derivation goes back further than 16 steps"),
        "{out}"
    );
    assert!(!s.iter().any(|t| t.starts_with("`a0`")), "{out}");
    assert!(s.contains(&"`a24` is int here"));
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
