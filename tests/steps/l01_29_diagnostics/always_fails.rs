//! Items ALWAYS-atom-div, ALWAYS-atom-cast and ALWAYS-atom-lookup: the rendered rejection of an
//! operation that always fails (DESIGN.md sec:failure, row "Operation that always fails", and
//! R11, row "Key outside the permission bound"). Each shows what the checker worked out, the
//! chain from the operand to the failure, and a menu of repairs; each offered repair, applied,
//! makes the program check.

use super::rejected;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The rendered rejection of `src`, without its trailing newline.
fn shown(src: &str) -> String {
    rejected(src).trim_end().to_string()
}

#[test]
fn a_divisor_that_cancels_shows_the_divisor_and_the_menu() {
    assert_eq!(
        shown("f(positional x: int) = x mod (x - x);\n"),
        "\
1:24: `mod` here always fails with `#divByZero`: its divisor adds `x` as often as it subtracts it, which makes it 0 for every value of `x`, so no value that reaches it gives an int
  [1] 1:30: this divisor is always 0
      1 | f(positional x: int) = x mod (x - x);
        |   ^^^^^^^^^^^^^^^^^ [4]      ^^^^^^^ [1, 2]
        |                        ^^^^^^^^^^^^^ [6, 7, 8]
        |                               ^ [3]
        |                                   ^ [5]
  [2] 1:30: this `-` gives int
  [3] 1:31: `x` is int here
  [4] 1:3: `x` is declared `int`
  [5] 1:35: `x` is int here
  [6] 1:24: repair: divide by a value that can be other than 0, such as a parameter `d: int`: `x mod d`
  [7] 1:24: repair: write `#divByZero` in place of this division, where the failure is meant
  [8] 1:24: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

#[test]
fn a_cast_of_a_literal_shows_the_operand_and_the_menu() {
    assert_eq!(
        shown("f(positional x: int) = int(\"n/a\");\n"),
        "\
1:24: `int` here always fails: its operand `\"n/a\"` gives `#invalid`, so this call never gives a value
  [1] 1:28: `int` cannot convert this operand
      1 | f(positional x: int) = int(\"n/a\");
        |                        ^^^^^^^^^^ [3, 4, 5]
        |                            ^^^^^ [1, 2]
  [2] 1:28: this expression is \"n/a\"
  [3] 1:24: repair: convert a value known only when the program runs, such as a parameter `s: String`: `int(s)` gives the result where `s` converts and `#invalid` where it does not
  [4] 1:24: repair: write `#invalid` in place of this call, where the failure is meant
  [5] 1:24: repair: write `#bug(\"…\")` in place of this call, where it is never meant to be reached
"
        .trim_end()
    );
}

#[test]
fn a_key_outside_the_keys_shows_both_types_and_the_menu() {
    assert_eq!(
        shown("f(m: int .. int | String -> bool, k: bool) = m[k];\n"),
        "\
1:46: this read can never find its key: the key is `bool` and the map's keys are `int | String`, which share no value, so the read can only give `#notFound`
  [1] 1:46: this map has the keys `int | String`, which hold no `bool`
      1 | f(m: int .. int | String -> bool, k: bool) = m[k];
        |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [5]         ^ [1, 4]
        |                                   ^^^^^^^ [3]  ^ [2]
        |                                              ^^^^ [6, 7, 8, 9]
  [2] 1:48: `k` is bool here
  [3] 1:35: `k` is declared `bool`
  [4] 1:46: `m` is int .. int | String -> bool here
  [5] 1:3: `m` is declared `int .. int | String -> bool`
  [6] 1:46: repair: read the map with a key in `int | String`
  [7] 1:46: repair: declare the map with the wider keys `bool | int | String ->? bool`, and handle `#notFound` where the key is missing
  [8] 1:46: repair: write `#notFound` in place of this read, where the miss is meant
  [9] 1:46: repair: write `#bug(\"…\")` in place of this read, where it is never meant to be reached
"
        .trim_end()
    );
}

#[test]
fn each_offered_repair_applied_makes_the_program_check() {
    let cases = [
        // `x mod d`, `d` a parameter declared `int`.
        "f(positional x: int, d: int) = x mod d;\n",
        "f(positional x: int) = #divByZero;\n",
        "f(positional x: int) = #bug(\"never reached\");\n",
        // `int(s)`, `s` a parameter declared `String`.
        "f(positional x: int, s: String) = int(s);\n",
        "f(positional x: int) = #invalid;\n",
        // A key in `int | String`, or the map declared with the wider keys.
        "f(m: int .. int | String -> bool, k: int) = m[k];\n",
        "f(m: bool | int | String ->? bool, k: bool) = m[k];\n",
        "f(m: int .. int | String -> bool, k: bool) = #notFound;\n",
    ];
    for src in cases {
        assert!(type_errors(src).is_empty(), "{src}\n{:?}", type_errors(src));
    }
}

/// Item MSG-neg-zero-rat: the divisor prints as `-0r`, the literal the program wrote, though
/// rat zero has no sign (DESIGN.md step L1.26a: "A literal in a printed type prints as it was
/// written, ... and so does a literal in a diagnostic").
#[test]
fn a_negated_zero_rat_divisor_prints_as_written() {
    assert_eq!(
        shown("f(x: rat) = x / -0r;\n"),
        "\
1:13: `/` here always fails with `#divByZero`: its divisor is the literal -0r, so no value that reaches it gives a rat
  [1] 1:17: this divisor is always 0
      1 | f(x: rat) = x / -0r;
        |             ^^^^^^^ [4, 5, 6]
        |                 ^^^ [1, 2]
        |                  ^^ [3]
  [2] 1:17: this `-` gives -0r
  [3] 1:18: this expression is 0r
  [4] 1:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [5] 1:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [6] 1:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// `-(0r)` prints as `-0r`, the sign and the literal the program wrote.
#[test]
fn a_negated_zero_rat_in_parentheses_prints_as_written() {
    assert_eq!(
        shown("f(x: rat) = x / -(0r);\n"),
        "\
1:13: `/` here always fails with `#divByZero`: its divisor is the literal -0r, so no value that reaches it gives a rat
  [1] 1:17: this divisor is always 0
      1 | f(x: rat) = x / -(0r);
        |             ^^^^^^^^^ [4, 5, 6]
        |                 ^^^^^ [1, 2]
        |                  ^^^^ [3]
  [2] 1:17: this `-` gives -0r
  [3] 1:18: this expression is 0r
  [4] 1:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [5] 1:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [6] 1:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// A name defined as `-0r` prints its type as `-0r` in the headline and at each step.
#[test]
fn a_constant_defined_as_a_negated_zero_rat_prints_as_written() {
    assert_eq!(
        shown("z = -0r;\nf(x: rat) = x / z;\n"),
        "\
2:13: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose only value is 0, so no value that reaches it gives a rat
  [1] 2:17: this divisor is always 0
      2 | f(x: rat) = x / z;
        |             ^^^^^ [6, 7, 8]
        |                 ^ [1, 2]
  [2] 2:17: `z` is -0r here
  [3] 1:5: `z` is defined as this expression, -0r
      1 | z = -0r;
        |     ^^^ [3, 4]
        |      ^^ [5]
  [4] 1:5: this `-` gives -0r
  [5] 1:6: this expression is 0r
  [6] 2:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [7] 2:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [8] 2:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// A name defined as `0r` prints `0r`, though `-0r`, the same value, is written earlier in the
/// text.
#[test]
fn a_constant_defined_as_zero_rat_prints_its_own_literal() {
    assert_eq!(
        shown("a = -0r;\nz = 0r;\nf(x: rat) = x / z;\n"),
        "\
3:13: `/` here always fails with `#divByZero`: its divisor has the type `0r`, whose only value is 0, so no value that reaches it gives a rat
  [1] 3:17: this divisor is always 0
      3 | f(x: rat) = x / z;
        |             ^^^^^ [5, 6, 7]
        |                 ^ [1, 2]
  [2] 3:17: `z` is 0r here
  [3] 2:5: `z` is defined as this expression, 0r
      2 | z = 0r;
        |     ^^
  [4] 2:5: this expression is 0r
  [5] 3:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [6] 3:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [7] 3:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// `-0r` and `0r` are one value, so the branch's type has one member. It prints as the first
/// literal of that value written in the divisor, and each branch's step prints its own literal.
#[test]
fn a_branch_of_two_zero_rat_spellings_prints_the_first_written() {
    assert_eq!(
        shown("f(x: rat, c: bool) = x / (if c { -0r } else { 0r });\n"),
        "\
1:22: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose only value is 0, so no value that reaches it gives a rat
  [1]  1:26: this divisor is always 0
       1 | f(x: rat, c: bool) = x / (if c { -0r } else { 0r });
         |           ^^^^^^^ [4]    ^^^^^^^^^^^^^^^^^^^^^^^^^^ [1, 2]
         |                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [10, 11, 12]
         |                              ^ [3]          ^^^^^^ [8]
         |                                ^^^^^^^ [5]
         |                                  ^^^ [6]      ^^ [9]
         |                                   ^^ [7]
  [2]  1:26: this `if` gives -0r
  [3]  1:30: `c` is bool here
  [4]  1:11: `c` is declared `bool`
  [5]  1:32: this block gives -0r
  [6]  1:34: this `-` gives -0r
  [7]  1:35: this expression is 0r
  [8]  1:45: this block gives 0r
  [9]  1:47: this expression is 0r
  [10] 1:22: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [11] 1:22: repair: write `#divByZero` in place of this division, where the failure is meant
  [12] 1:22: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// The same branch with its literals swapped prints `0r`, the first one written in the divisor.
#[test]
fn a_branch_of_two_zero_rat_spellings_in_the_other_order() {
    assert_eq!(
        shown("f(x: rat, c: bool) = x / (if c { 0r } else { -0r });\n"),
        "\
1:22: `/` here always fails with `#divByZero`: its divisor has the type `0r`, whose only value is 0, so no value that reaches it gives a rat
  [1]  1:26: this divisor is always 0
       1 | f(x: rat, c: bool) = x / (if c { 0r } else { -0r });
         |           ^^^^^^^ [4]    ^^^^^^^^^^^^^^^^^^^^^^^^^^ [1, 2]
         |                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [10, 11, 12]
         |                              ^ [3]         ^^^^^^^ [7]
         |                                ^^^^^^ [5]     ^^ [9]
         |                                  ^^ [6]      ^^^ [8]
  [2]  1:26: this `if` gives 0r
  [3]  1:30: `c` is bool here
  [4]  1:11: `c` is declared `bool`
  [5]  1:32: this block gives 0r
  [6]  1:34: this expression is 0r
  [7]  1:44: this block gives -0r
  [8]  1:46: this `-` gives -0r
  [9]  1:47: this expression is 0r
  [10] 1:22: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [11] 1:22: repair: write `#divByZero` in place of this division, where the failure is meant
  [12] 1:22: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}
