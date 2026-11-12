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
  [7] 1:46: repair: declare the map with the wider keys `int | bool | String ->? bool`, and handle `#notFound` where the key is missing
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

/// Item MSG-neg-zero-chain: a name defined as a name defined as `-0r` prints `-0r` in the
/// headline and at each step, though `0r`, the same value, is written earlier in the text: the
/// literal is found by following the chain of definitions from the divisor to the end.
#[test]
fn a_chain_of_two_names_to_a_negated_zero_rat_prints_as_written() {
    assert_eq!(
        shown("a = 0r;\ny = -0r;\nz = y;\nf(x: rat) = x / z;\n"),
        "\
4:13: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose only value is 0, so no value that reaches it gives a rat
  [1]  4:17: this divisor is always 0
       4 | f(x: rat) = x / z;
         |             ^^^^^ [8, 9, 10]
         |                 ^ [1, 2]
  [2]  4:17: `z` is -0r here
  [3]  3:5: `z` is defined as this expression, -0r
       3 | z = y;
         |     ^
  [4]  3:5: `y` is -0r here
  [5]  2:5: `y` is defined as this expression, -0r
       2 | y = -0r;
         |     ^^^ [5, 6]
         |      ^^ [7]
  [6]  2:5: this `-` gives -0r
  [7]  2:6: this expression is 0r
  [8]  4:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [9]  4:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [10] 4:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// A chain of three names to `-0r` prints `-0r` at every step.
#[test]
fn a_chain_of_three_names_to_a_negated_zero_rat_prints_as_written() {
    assert_eq!(
        shown("a = 0r;\nw = -0r;\ny = w;\nz = y;\nf(x: rat) = x / z;\n"),
        "\
5:13: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose only value is 0, so no value that reaches it gives a rat
  [1]  5:17: this divisor is always 0
       5 | f(x: rat) = x / z;
         |             ^^^^^ [10, 11, 12]
         |                 ^ [1, 2]
  [2]  5:17: `z` is -0r here
  [3]  4:5: `z` is defined as this expression, -0r
       4 | z = y;
         |     ^
  [4]  4:5: `y` is -0r here
  [5]  3:5: `y` is defined as this expression, -0r
       3 | y = w;
         |     ^
  [6]  3:5: `w` is -0r here
  [7]  2:5: `w` is defined as this expression, -0r
       2 | w = -0r;
         |     ^^^ [7, 8]
         |      ^^ [9]
  [8]  2:5: this `-` gives -0r
  [9]  2:6: this expression is 0r
  [10] 5:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [11] 5:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [12] 5:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// A chain to `0r` prints `0r`, with no `-`, though `-0r` is written earlier in the text.
#[test]
fn a_chain_of_names_to_zero_rat_prints_its_own_literal() {
    assert_eq!(
        shown("a = -0r;\ny = 0r;\nz = y;\nf(x: rat) = x / z;\n"),
        "\
4:13: `/` here always fails with `#divByZero`: its divisor has the type `0r`, whose only value is 0, so no value that reaches it gives a rat
  [1] 4:17: this divisor is always 0
      4 | f(x: rat) = x / z;
        |             ^^^^^ [7, 8, 9]
        |                 ^ [1, 2]
  [2] 4:17: `z` is 0r here
  [3] 3:5: `z` is defined as this expression, 0r
      3 | z = y;
        |     ^
  [4] 3:5: `y` is 0r here
  [5] 2:5: `y` is defined as this expression, 0r
      2 | y = 0r;
        |     ^^
  [6] 2:5: this expression is 0r
  [7] 4:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [8] 4:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [9] 4:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// Two chains: the earlier ends in `0r` and reaches nothing; the later ends in `-0r` and reaches
/// the divisor, which prints `-0r`.
#[test]
fn of_two_chains_the_one_that_reaches_the_divisor_prints() {
    assert_eq!(
        shown("b = 0r;\nc = b;\ny = -0r;\nz = y;\nf(x: rat) = x / z;\n"),
        "\
5:13: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose only value is 0, so no value that reaches it gives a rat
  [1]  5:17: this divisor is always 0
       5 | f(x: rat) = x / z;
         |             ^^^^^ [8, 9, 10]
         |                 ^ [1, 2]
  [2]  5:17: `z` is -0r here
  [3]  4:5: `z` is defined as this expression, -0r
       4 | z = y;
         |     ^
  [4]  4:5: `y` is -0r here
  [5]  3:5: `y` is defined as this expression, -0r
       3 | y = -0r;
         |     ^^^ [5, 6]
         |      ^^ [7]
  [6]  3:5: this `-` gives -0r
  [7]  3:6: this expression is 0r
  [8]  5:13: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [9]  5:13: repair: write `#divByZero` in place of this division, where the failure is meant
  [10] 5:13: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// A name that shadows an earlier one of the same spelling: the chain `y` (inner), `z`, `y`
/// (outer) is followed by binding, not by spelling, and ends at `-0r`.
#[test]
fn a_chain_through_a_shadowed_name_prints_as_written() {
    assert_eq!(
        shown(
            "a = 0r;\nf(x: rat) = {\n  y = -0r;\n  {\n    z = y;\n    {\n      y = z;\n      \
             return x / y;\n    }\n  }\n};\n"
        ),
        "\
8:14: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose only value is 0, so no value that reaches it gives a rat
  [1]  8:18: this divisor is always 0
       8 |       return x / y;
         |              ^^^^^ [10, 11, 12]
         |                  ^ [1, 2]
  [2]  8:18: `y` is -0r here
  [3]  7:11: `y` is defined as this expression, -0r
       7 |       y = z;
         |           ^
  [4]  7:11: `z` is -0r here
  [5]  5:9: `z` is defined as this expression, -0r
       5 |     z = y;
         |         ^
  [6]  5:9: `y` is -0r here
  [7]  3:7: `y` is defined as this expression, -0r
       3 |   y = -0r;
         |       ^^^ [7, 8]
         |        ^^ [9]
  [8]  3:7: this `-` gives -0r
  [9]  3:8: this expression is 0r
  [10] 8:14: repair: divide by a value that can be other than 0, such as a parameter `d: rat`: `x / d`
  [11] 8:14: repair: write `#divByZero` in place of this division, where the failure is meant
  [12] 8:14: repair: write `#bug(\"…\")` in place of this division, where it is never meant to be reached
"
        .trim_end()
    );
}

/// A name taken apart from a tuple written out, `q` of `p, q = (0r, -0r)`, read through `z`:
/// the chain goes from `z` to `q` to the tuple's second item, `-0r`. Checked line by line: the
/// step for the tuple as a whole prints both of its zeros as the first written in it.
#[test]
fn a_chain_through_a_tuple_component_prints_the_component_as_written() {
    let out = shown("a = 0r;\nf(x: rat) = {\n  p, q = (0r, -0r);\n  z = q;\n  return x / z;\n};\n");
    for line in [
        "5:10: `/` here always fails with `#divByZero`: its divisor has the type `-0r`, whose \
         only value is 0, so no value that reaches it gives a rat",
        "  [2]  5:14: `z` is -0r here",
        "  [3]  4:7: `z` is defined as this expression, -0r",
        "  [4]  4:7: `q` is -0r here",
        "  [5]  3:10: `q` is -0r, component 1 of this tuple",
        "  [8]  3:15: this `-` gives -0r",
    ] {
        assert!(out.lines().any(|l| l == line), "{line}\nnot in\n{out}");
    }
}

/// The first component of the same tuple prints `0r`, its own literal.
#[test]
fn the_other_tuple_component_prints_its_own_literal() {
    let out = shown("a = -0r;\nf(x: rat) = {\n  p, q = (0r, -0r);\n  return x / p;\n};\n");
    for line in [
        "4:10: `/` here always fails with `#divByZero`: its divisor has the type `0r`, whose \
         only value is 0, so no value that reaches it gives a rat",
        "  [2]  4:14: `p` is 0r here",
        "  [3]  3:10: `p` is 0r, component 0 of this tuple",
    ] {
        assert!(out.lines().any(|l| l == line), "{line}\nnot in\n{out}");
    }
}
