//! Messages no other test produced (test audit 2026-11-08, row 10; item
//! TESTS-messages-never-produced): for each, the shortest program that produces it, with the
//! whole message pinned.

use super::rejected;

/// The rejection of `src`, without the line end after its last line.
fn shown(src: &str) -> String {
    rejected(src).trim_end().to_string()
}

#[test]
fn a_default_whose_type_its_uses_exclude_is_rejected() {
    // A parameter with no declared type takes the type its uses give it; its default must be
    // of that type.
    assert_eq!(
        shown("f(positional y = (y + 1, 2)) = y;\n"),
        r#"1:18: the default of `y` is (_, 2), not int | f64 | rat: a default is a value of its parameter's type.
  [1] 1:18: this expression gives (_, 2)
      1 | f(positional y = (y + 1, 2)) = y;
        |   ^^^^^^^^^^^^^^^^^^^^^^^^^ [4]
        |                   ^ [3]  ^ [6]
        |                   ^^^^^ [2]
        |                       ^ [5, 7]
        |                  ^--------^ [1, 8, 9]
  [2] 1:19: this `+` gives int | f64 | rat
  [3] 1:19: `y` is int | f64 | rat here
  [4] 1:3: `y` has no declared type; its uses give it _
  [5] 1:23: this literal, 1, is 1
  [6] 1:26: this literal, 2, is 2
  [7] 1:23: the literal 1 takes int | f64 | rat
  [8] 1:18: repair: write a default of type int | f64 | rat
  [9] 1:18: repair: declare `y` with a type that holds (_, 2) as well, as `y: int | f64 | rat | (_, 2)`"#
    );
}

#[test]
fn a_default_the_checker_cannot_place_in_a_range_is_rejected_at_the_call() {
    assert_eq!(
        shown("f(positional a, positional b = a) = bitAnd(b, 1);\nmain = f(1);\n"),
        r#"2:8: `f` takes `b` in int[0..], and this call leaves `b` out, so `b` takes its default, which the checker cannot show lies in int[0..].
  [1] 1:37: `bitAnd` takes `a` in int[0..] here
      1 | f(positional a, positional b = a) = bitAnd(b, 1);
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]
        |                                     ^^^^^^^^^^^^ [1]
  [2] 1:1: `f` is declared here with no type written for `a`, `b` or its result; the type the checker found for `f` is `(int, int) -> int`
  [3] 2:8: repair: pass `b` in this call, with a value in int[0..]
      2 | main = f(1);
        |        ^^^^
  [4] 2:8: repair: give `b` a default in int[0..]"#
    );
}

#[test]
fn an_argument_forwarded_to_a_function_parameter_is_checked_against_its_range() {
    // The repair names the argument `-1` of the call at 3:8, not `a`, which belongs to `h`
    // (MSG-forwarded-repair); step [1] shows where `-1` is passed.
    assert_eq!(
        shown(
            "ap(positional g, positional v) = g(v);\nh(positional a) = bitAnd(a, 1);\n\
             main = ap(h, -1);\n"
        ),
        r#"3:8: `g` takes `a` in int[0..], and this call passes `-1` on to it as `a`: a value outside int[0..] would reach a use that does not take it.
  [1] 3:14: `-1` reaches `g` as `a`
      3 | main = ap(h, -1);
        |        ^^^^^^^^^ [5]
        |              ^^ [1]
  [2] 2:19: `bitAnd` takes `a` in int[0..] here
      2 | h(positional a) = bitAnd(a, 1);
        |                   ^^^^^^^^^^^^
  [3] 1:34: `ap` needs this of its argument here
      1 | ap(positional g, positional v) = g(v);
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [4]
        |                                  ^^^^ [3]
  [4] 1:1: `ap` is declared here with no type written for `g`, `v` or its result; the type the checker found for `ap` is `(_, _) -> _`
  [5] 3:8: repair: pass a value in int[0..] where this call passes `-1`"#
    );
}

#[test]
fn sum_of_a_value_that_is_not_a_tuple_is_rejected() {
    assert_eq!(
        shown("x = sum(3);\n"),
        r#"1:5: `sum` does not take (3): it adds only numbers.
  [1] 1:5: repair: pass a tuple whose components are all numbers, as `sum((1, 2, 3))`
      1 | x = sum(3);
        |     ^^^^^^"#
    );
}

#[test]
fn a_component_of_a_destructured_tuple_is_named_with_its_place() {
    // Before, step [2] read "`a` is component 0 of this, 1", which did not say what "this"
    // is or which of the two is the type.
    // No repair is offered: `int(b)` always fails, at `#invalid`, so `c = a + int(b)` is
    // rejected.
    assert_eq!(
        shown("p = (1, \"x\");\na, b = p;\nc = a + b;\n"),
        r#"3:5: `+` does not take (1, "x"): no arrow of `+` takes these types.
  [1]  3:5: `a` is 1 here
       3 | c = a + b;
         |     ^ [1]
         |     ^^^^^ [10, 11, 12]
         |         ^ [8]
  [2]  2:8: `a` is 1, component 0 of this tuple
       2 | a, b = p;
         |        ^
  [3]  2:8: `p` is (1, "x") here
  [4]  1:5: `p` is defined as this expression, (1, "x")
       1 | p = (1, "x");
         |     ^^^^^^^^ [4, 5]
         |      ^ [6]
         |         ^^^ [7]
  [5]  1:5: this expression gives (1, "x")
  [6]  1:6: this literal, 1, is 1
  [7]  1:9: this expression is "x"
  [8]  3:9: `b` is "x" here
  [9]  2:8: `b` is "x", component 1 of this tuple
  [10] 3:5: `+` takes (int, int) -> int
  [11] 3:5: `+` takes (f64, f64) -> f64
  [12] 3:5: `+` takes (rat, rat) -> rat"#
    );
}

#[test]
fn a_parameter_typed_by_its_default_says_so() {
    // Before, step [2] read "`n` is String, the carrier of its default".
    assert_eq!(
        shown("f(positional n = \"a\") = n + 1;\n"),
        r#"1:25: `+` does not take (String, 1): no arrow of `+` takes these types.
  [1] 1:25: `n` is String here
      1 | f(positional n = "a") = n + 1;
        |   ^^^^^^^^^^^^^^^^^^ [2]    ^ [3]
        |                         ^ [1]
        |                         ^^^^^ [4, 5, 6]
  [2] 1:3: `n` is String, the type of its default
  [3] 1:29: this literal, 1, is 1
  [4] 1:25: `+` takes (int, int) -> int
  [5] 1:25: `+` takes (f64, f64) -> f64
  [6] 1:25: `+` takes (rat, rat) -> rat"#
    );
}

#[test]
#[ignore = "MSG-flow-origin: the derivation leaves out where \"s\" comes from (the lambda at 4:9) and the default `h = g` at 3:20 that makes `h` and `g` one value; open"]
fn a_value_that_flows_into_a_class_another_use_fixed_shows_its_origin() {
    let out = shown(
        "f(positional g) {\n  a = g(1) + 1;\n  k(positional h = g) = h(2);\n  b = k(x -> \"s\");\n  \
         return a;\n}\n",
    );
    // Today:
    // 2:7: this use gives "s", not int | f64 | rat: its result flows into a value that other uses have already made int | f64 | rat
    //   [1] 2:7: this call of `g` gives int | f64 | rat
    //       2 |   a = g(1) + 1;
    //         |       ^^^^ [1, 3, 5]
    //         |         ^ [2]
    //   [2] 2:9: this literal, 1, is 1
    //   [3] 2:7: this use needs it here
    //   [4] 3:3: `k` is declared here with no type written for `h` or its result; the type the checker found for `k` is `(_) -> _`
    //       3 |   k(positional h = g) = h(2);
    //         |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //   [5] 2:7: repair: declare the types of the values this use reads, so that it is checked where it is written
    assert!(out.lines().any(|l| l.contains(" 4:9: ")), "{out}");
    assert!(out.lines().any(|l| l.contains(" 3:20: ")), "{out}");
}
