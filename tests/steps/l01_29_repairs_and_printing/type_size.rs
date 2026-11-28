//! The types a rejection's derivation prints grow with the program, not with the paths of the
//! types (MSG-derive-type-size; DESIGN sec:diagnostics, "Types in a message"). A tuple holding
//! a part of its own is named `Tk` when the message writes it twice, once inside another part,
//! and the sentence writes each of its types whole at the top level. Before,
//! `t_i = (t_{i-1}, t_{i-1})` over n levels printed 2^n components in each of its steps, and a
//! chain of n names, each holding the one before, printed the type at each of its n links in
//! full, O(n²) in all. Each step now takes the parts an earlier step printed by their names
//! rather than print them again, so printing them is linear in n too
//! (MSG-derive-print-per-message).

use super::rejected;

/// `t0 = (1, 1);` and `t_i = (t_{i-1}, t_{i-1})` up to `t_n`, then `u = t_n + 1;`.
pub(super) fn doubling(n: usize) -> String {
    let mut src = "t0 = (1, 1);\n".to_string();
    for i in 1..=n {
        src += &format!("t{i} = (t{0}, t{0});\n", i - 1);
    }
    src + &format!("u = t{n} + 1;\n")
}

/// The chains of [`doubling`] from `(1, 1)` and from `(1, true)`, then `u = t_n < s_n;`.
pub(super) fn compared(n: usize) -> String {
    let mut src = "t0 = (1, 1);\ns0 = (1, true);\n".to_string();
    for i in 1..=n {
        src += &format!("t{i} = (t{0}, t{0});\ns{i} = (s{0}, s{0});\n", i - 1);
    }
    src + &format!("u = t{n} < s{n};\n")
}

/// `a0 = (0, 0);` and `a_i = (a_{i-1}, i)` up to `a_n`, then `u = a_n + 1;`: each name holds
/// the one before.
pub(super) fn growing(n: usize) -> String {
    let mut src = "a0 = (0, 0);\n".to_string();
    for i in 1..=n {
        src += &format!("a{i} = (a{}, {i});\n", i - 1);
    }
    src + &format!("u = a{n} + 1;\n")
}

/// `x0` a tuple of `m` components and `x_i = x_{i-1}` up to `x_n`, then `u = x_n + 1;`: each
/// step of the chain has the one type.
pub(super) fn same(n: usize, m: usize) -> String {
    let parts: Vec<String> = (0..m).map(|i| i.to_string()).collect();
    let mut src = format!("x0 = ({});\n", parts.join(", "));
    for i in 1..=n {
        src += &format!("x{i} = x{};\n", i - 1);
    }
    src + &format!("u = x{n} + 1;\n")
}

#[test]
fn a_tuple_doubled_at_each_level_is_named_once_per_level() {
    assert_eq!(
        rejected(&doubling(6)),
        r#"8:5: `+` does not take ((Part5, Part5), 1): no arrow of `+` takes these types.
  Part1, Part2, Part3, Part4 and Part5 stand for parts written more than once:
    type Part1 = ((1, 1), (1, 1));
    type Part2 = (Part1, Part1);
    type Part3 = (Part2, Part2);
    type Part4 = (Part3, Part3);
    type Part5 = (Part4, Part4);
  [1]  8:5: `t6` is (Part5, Part5) here
       8 | u = t6 + 1;
         |     ^^ [1]
         |     ^^^^^^ [20, 21, 22, 23]
         |          ^ [18, 19]
  [2]  7:6: `t6` is defined as this expression, (Part5, Part5)
       7 | t6 = (t5, t5);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [17]
  [3]  7:6: this expression gives (Part5, Part5)
  [4]  7:7: `t5` is Part5 here
  [5]  6:6: `t5` is defined as this expression, Part5
       6 | t5 = (t4, t4);
         |      ^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^ [16]
  [6]  6:6: this expression gives Part5
  [7]  6:7: `t4` is Part4 here
  [8]  5:6: `t4` is defined as this expression, Part4
       5 | t4 = (t3, t3);
         |      ^^^^^^^^ [8, 9]
         |       ^^ [10]
         |           ^^ [15]
  [9]  5:6: this expression gives Part4
  [10] 5:7: `t3` is Part3 here
  [11] 4:6: `t3` is defined as this expression, Part3
       4 | t3 = (t2, t2);
         |      ^^^^^^^^ [11, 12]
         |       ^^ [13]
         |           ^^ [14]
  [12] 4:6: this expression gives Part3
  [13] 4:7: `t2` is Part2 here
  [14] 4:11: `t2` is Part2 here
  [15] 5:11: `t3` is Part3 here
  [16] 6:11: `t4` is Part4 here
  [17] 7:11: `t5` is Part5 here
  [18] 8:10: this literal, 1, is 1
  [19] 8:10: ... (additional lines not shown: 3)
  [20] 8:5: `+` takes (int, int) -> int
  [21] 8:5: `+` takes (f64, f64) -> f64
  [22] 8:5: `+` takes (rat, rat) -> rat
  [23] 8:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn comparing_two_doubled_tuples_names_each_level_once() {
    assert_eq!(
        rejected(&compared(6)),
        r#"15:5: Cannot compare unequal types: `t6[1][1][1][1][1][1][1] : 1 < s6[1][1][1][1][1][1][1] : true` in `t6 < s6`.
  Part1, Part2, Part3, Part4, Part5, Part6, Part7, Part8, Part9 and Part10 stand for parts written more than once:
    type Part1 = ((1, 1), (1, 1));
    type Part2 = (Part1, Part1);
    type Part3 = (Part2, Part2);
    type Part4 = (Part3, Part3);
    type Part5 = (Part4, Part4);
    type Part6 = ((1, true), (1, true));
    type Part7 = (Part6, Part6);
    type Part8 = (Part7, Part7);
    type Part9 = (Part8, Part8);
    type Part10 = (Part9, Part9);
  [1]  15:5: `t6` is (Part5, Part5) here
       15 | u = t6 < s6;
          |     ^^ [1]
          |     ^^^^^^^ [20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
          |          ^^ [10]
  [2]  13:6: `t6` is defined as this expression, (Part5, Part5)
       13 | t6 = (t5, t5);
          |      ^^^^^^^^ [2, 3]
          |       ^^ [4]
          |           ^^ [9]
  [3]  13:6: this expression gives (Part5, Part5)
  [4]  13:7: `t5` is Part5 here
  [5]  11:6: `t5` is defined as this expression, Part5
       11 | t5 = (t4, t4);
          |      ^^^^^^^^ [5, 6]
          |       ^^ [7]
          |           ^^ [8]
  [6]  11:6: this expression gives Part5
  [7]  11:7: `t4` is Part4 here
  [8]  11:11: `t4` is Part4 here
  [9]  13:11: `t5` is Part5 here
  [10] 15:10: `s6` is (Part10, Part10) here
  [11] 14:6: `s6` is defined as this expression, (Part10, Part10)
       14 | s6 = (s5, s5);
          |      ^^^^^^^^ [11, 12]
          |       ^^ [13]
          |           ^^ [18, 19]
  [12] 14:6: this expression gives (Part10, Part10)
  [13] 14:7: `s5` is Part10 here
  [14] 12:6: `s5` is defined as this expression, Part10
       12 | s5 = (s4, s4);
          |      ^^^^^^^^ [14, 15]
          |       ^^ [16]
          |           ^^ [17]
  [15] 12:6: this expression gives Part10
  [16] 12:7: `s4` is Part9 here
  [17] 12:11: `s4` is Part9 here
  [18] 14:11: `s5` is Part10 here
  [19] 14:11: ... (additional lines not shown: 10)
  [20] 15:5: `<` compares two tuples component by component, as far as the shorter goes
  [21] 15:5: components `[1]` are tuples, compared the same way
  [22] 15:5: components `[1]` are tuples, compared the same way
  [23] 15:5: components `[1]` are tuples, compared the same way
  [24] 15:5: components `[1]` are tuples, compared the same way
  [25] 15:5: components `[1]` are tuples, compared the same way
  [26] 15:5: components `[1]` are tuples, compared the same way
  [27] 15:5: `<` compares components `[1]`: `t6[1][1][1][1][1][1][1] : 1` with `s6[1][1][1][1][1][1][1] : true`
  [28] 15:5: `<` compares only two numbers of one kind or two values of one other kind
  [29] 15:5: repair: change the type of `t6` or `s6` so that `t6[1][1][1][1][1][1][1]` and `s6[1][1][1][1][1][1][1]` compare"#
    );
}

#[test]
fn a_chain_of_names_each_holding_the_one_before_names_each_link() {
    assert_eq!(
        rejected(&growing(4)),
        r#"6:5: `+` does not take ((Part3, 4), 1): no arrow of `+` takes these types.
  Part1, Part2 and Part3 stand for parts written more than once:
    type Part1 = ((0, 0), 1);
    type Part2 = (Part1, 2);
    type Part3 = (Part2, 3);
  [1]  6:5: `a4` is (Part3, 4) here
       6 | u = a4 + 1;
         |     ^^ [1]
         |     ^^^^^^ [20, 21, 22, 23]
         |          ^ [18, 19]
  [2]  5:6: `a4` is defined as this expression, (Part3, 4)
       5 | a4 = (a3, 4);
         |      ^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^ [17]
  [3]  5:6: this expression gives (Part3, 4)
  [4]  5:7: `a3` is Part3 here
  [5]  4:6: `a3` is defined as this expression, Part3
       4 | a3 = (a2, 3);
         |      ^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^ [16]
  [6]  4:6: this expression gives Part3
  [7]  4:7: `a2` is Part2 here
  [8]  3:6: `a2` is defined as this expression, Part2
       3 | a2 = (a1, 2);
         |      ^^^^^^^ [8, 9]
         |       ^^ [10]
         |           ^ [15]
  [9]  3:6: this expression gives Part2
  [10] 3:7: `a1` is Part1 here
  [11] 2:6: `a1` is defined as this expression, Part1
       2 | a1 = (a0, 1);
         |      ^^^^^^^ [11, 12]
         |       ^^ [13]
         |           ^ [14]
  [12] 2:6: this expression gives Part1
  [13] 2:7: `a0` is (0, 0) here
  [14] 2:11: this literal, 1, is 1
  [15] 3:11: this literal, 2, is 2
  [16] 4:11: this literal, 3, is 3
  [17] 5:11: this literal, 4, is 4
  [18] 6:10: this literal, 1, is 1
  [19] 6:10: ... (additional lines not shown: 1)
  [20] 6:5: `+` takes (int, int) -> int
  [21] 6:5: `+` takes (f64, f64) -> f64
  [22] 6:5: `+` takes (rat, rat) -> rat
  [23] 6:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_chain_of_names_of_one_type_writes_the_type_once() {
    // A step whose whole type an earlier step wrote writes `the same type as step k` when the
    // type is longer than those words, so a chain of n names of one type of m components
    // writes the type once (MSG-derive-same-chain; DESIGN sec:diagnostics, "Types in a
    // message").
    assert_eq!(
        rejected(&same(4, 9)),
        r#"6:5: `+` does not take ((0, 1, 2, 3, 4, 5, 6, 7, 8), 1): no arrow of `+` takes these types.
  [1]  6:5: `x4` is (0, 1, 2, 3, 4, 5, 6, 7, 8) here
       6 | u = x4 + 1;
         |     ^^ [1]
         |     ^^^^^^ [12, 13, 14, 15]
         |          ^ [10, 11]
  [2]  5:6: `x4` is defined as this expression, the same type as step 1
       5 | x4 = x3;
         |      ^^
  [3]  5:6: `x3` is the same type as step 1 here
  [4]  4:6: `x3` is defined as this expression, the same type as step 1
       4 | x3 = x2;
         |      ^^
  [5]  4:6: `x2` is the same type as step 1 here
  [6]  3:6: `x2` is defined as this expression, the same type as step 1
       3 | x2 = x1;
         |      ^^
  [7]  3:6: `x1` is the same type as step 1 here
  [8]  2:6: `x1` is defined as this expression, the same type as step 1
       2 | x1 = x0;
         |      ^^
  [9]  2:6: `x0` is the same type as step 1 here
  [10] 6:10: this literal, 1, is 1
  [11] 6:10: ... (additional lines not shown: 1)
  [12] 6:5: `+` takes (int, int) -> int
  [13] 6:5: `+` takes (f64, f64) -> f64
  [14] 6:5: `+` takes (rat, rat) -> rat
  [15] 6:5: `+` takes (f32, f32) -> f32"#
    );
}

// A part a step takes from an earlier step's print is the text a print anew would give it
// (MSG-derive-print-per-message). The texts below are those each step printing its type alone
// gave.

#[test]
fn a_value_written_in_two_ways_is_written_as_each_step_writes_it() {
    // `31` is `0x1F` where `a0` is written and `31` where `a1` is: the steps that show `a1`
    // write it as `a1`'s line does, though `a0`'s type was printed before them.
    assert_eq!(
        rejected("a0 = (0x1F, 1);\na1 = (a0, 31);\na2 = (a1, a1);\nu = a2 + 1;\n"),
        r#"4:5: `+` does not take ((Part1, Part1), 1): no arrow of `+` takes these types.
  Part1 stands for a part written more than once:
    type Part1 = ((0x1F, 1), 0x1F);
  [1]  4:5: `a2` is (Part1, Part1) here
       4 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [15, 16, 17, 18]
         |          ^ [14]
  [2]  3:6: `a2` is defined as this expression, (Part1, Part1)
       3 | a2 = (a1, a1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [13]
  [3]  3:6: this expression gives (Part1, Part1)
  [4]  3:7: `a1` is ((31, 1), 31) here
  [5]  2:6: `a1` is defined as this expression, ((31, 1), 31)
       2 | a1 = (a0, 31);
         |      ^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^ [12]
  [6]  2:6: this expression gives ((31, 1), 31)
  [7]  2:7: `a0` is (0x1F, 1) here
  [8]  1:6: `a0` is defined as this expression, (0x1F, 1)
       1 | a0 = (0x1F, 1);
         |      ^^^^^^^^^ [8, 9]
         |       ^^^^ [10]
         |             ^ [11]
  [9]  1:6: this expression gives (0x1F, 1)
  [10] 1:7: this literal, 0x1F, is 31
  [11] 1:13: this literal, 1, is 1
  [12] 2:11: this literal, 31, is 31
  [13] 3:11: `a1` is ((31, 1), 31) here
  [14] 4:10: this literal, 1, is 1
  [15] 4:5: `+` takes (int, int) -> int
  [16] 4:5: `+` takes (f64, f64) -> f64
  [17] 4:5: `+` takes (rat, rat) -> rat
  [18] 4:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_zero_written_with_and_without_its_sign_is_written_as_each_step_writes_it() {
    // `-0r` and `0r` are one value, written with its sign where `a0` is and without it where
    // `a1` is.
    assert_eq!(
        rejected("a0 = (-0r, 1);\na1 = (a0, 0r);\na2 = (a1, a1);\nu = a2 + 1;\n"),
        r#"4:5: `+` does not take ((Part1, Part1), 1): no arrow of `+` takes these types.
  Part1 stands for a part written more than once:
    type Part1 = ((-0r, 1), -0r);
  [1]  4:5: `a2` is (Part1, Part1) here
       4 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [16, 17, 18, 19]
         |          ^ [15]
  [2]  3:6: `a2` is defined as this expression, (Part1, Part1)
       3 | a2 = (a1, a1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [14]
  [3]  3:6: this expression gives (Part1, Part1)
  [4]  3:7: `a1` is ((0r, 1), 0r) here
  [5]  2:6: `a1` is defined as this expression, ((0r, 1), 0r)
       2 | a1 = (a0, 0r);
         |      ^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^ [13]
  [6]  2:6: this expression gives ((0r, 1), 0r)
  [7]  2:7: `a0` is (-0r, 1) here
  [8]  1:6: `a0` is defined as this expression, (-0r, 1)
       1 | a0 = (-0r, 1);
         |      ^^^^^^^^ [8, 9]
         |       ^^^ [10]
         |        ^^ [11]
         |            ^ [12]
  [9]  1:6: this expression gives (-0r, 1)
  [10] 1:7: this `-` gives -0r
  [11] 1:8: this expression is 0r
  [12] 1:12: this literal, 1, is 1
  [13] 2:11: this expression is 0r
  [14] 3:11: `a1` is ((0r, 1), 0r) here
  [15] 4:10: this literal, 1, is 1
  [16] 4:5: `+` takes (int, int) -> int
  [17] 4:5: `+` takes (f64, f64) -> f64
  [18] 4:5: `+` takes (rat, rat) -> rat
  [19] 4:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_union_of_tuples_printed_before_keeps_the_order_of_its_members() {
    // The members of the union `g` gives are ordered by their contents, which the tuples `x`
    // and `b0` printed in earlier steps would hide behind their references.
    assert_eq!(
        rejected(
            "b0 = (9, \"z\");\na0 = (1, true);\nx = (b0, a0);\n\
             g(positional c: bool) = if c { (x, b0) } else { (x, a0) };\n\
             v = (g(true), x);\nw = (v, v);\nu = w + 1;\n"
        ),
        r#"7:5: `+` does not take ((Part3, Part3), 1): no arrow of `+` takes these types.
  Part1, Part2 and Part3 stand for parts written more than once:
    type Part1 = (1, true);
    type Part2 = ((9, "z"), Part1);
    type Part3 = ((Part2, Part1) | (Part2, (9, "z")), Part2);
  [1]  7:5: `w` is (Part3, Part3) here
       7 | u = w + 1;
         |     ^ [1]
         |     ^^^^^ [17, 18, 19, 20]
         |         ^ [15, 16]
  [2]  6:5: `w` is defined as this expression, (Part3, Part3)
       6 | w = (v, v);
         |     ^^^^^^ [2, 3]
         |      ^ [4]
         |         ^ [14]
  [3]  6:5: this expression gives (Part3, Part3)
  [4]  6:6: `v` is Part3 here
  [5]  5:5: `v` is defined as this expression, Part3
       5 | v = (g(true), x);
         |     ^^^^^^^^^^^^ [5, 6]
         |      ^^^^^^^ [7]
         |               ^ [9]
  [6]  5:5: this expression gives Part3
  [7]  5:6: this call of `g` gives (Part2, (9, "z")) | (Part2, Part1)
  [8]  4:1: `g` is declared here with no type written for its result; the type the checker found for `g` is `bool -> (Part2, (9, "z")) | (Part2, Part1)`
       4 | g(positional c: bool) = if c { (x, b0) } else { (x, a0) };
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [9]  5:15: `x` is Part2 here
  [10] 3:5: `x` is defined as this expression, Part2
       3 | x = (b0, a0);
         |     ^^^^^^^^ [10, 11]
         |      ^^ [12]
         |          ^^ [13]
  [11] 3:5: this expression gives Part2
  [12] 3:6: `b0` is (9, "z") here
  [13] 3:10: `a0` is Part1 here
  [14] 6:9: `v` is Part3 here
  [15] 7:9: this literal, 1, is 1
  [16] 7:9: ... (additional lines not shown: 2)
  [17] 7:5: `+` takes (int, int) -> int
  [18] 7:5: `+` takes (f64, f64) -> f64
  [19] 7:5: `+` takes (rat, rat) -> rat
  [20] 7:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_union_inside_a_tuple_printed_before_is_named_from_the_first_step_that_uses_it_twice() {
    // `1 | 2` is written twice in the sentence's type, so it is `Part1` from the sentence on,
    // and `a0`'s steps, which use it once, write `Part1` too (MSG-derive-print-union-names).
    // Before, a union was named by how often each type used it, and `a0`'s steps wrote
    // `(1 | 2, 3)`. With `Part1` a part of it, `(Part1, 3)`, written inside `Part3` and in `a0`'s
    // steps, is named as any tuple holding a named part is.
    assert_eq!(
        rejected(
            "g(positional c: bool) = if c { 1 } else { 2 };\na0 = (g(true), 3);\n\
             a1 = (a0, g(false));\na2 = (a1, a1);\nu = a2 + 1;\n"
        ),
        r#"5:5: `+` does not take ((Part3, Part3), 1): no arrow of `+` takes these types.
  Part1, Part2 and Part3 stand for parts written more than once:
    type Part1 = 1 | 2;
    type Part2 = (Part1, 3);
    type Part3 = (Part2, Part1);
  [1]  5:5: `a2` is (Part3, Part3) here
       5 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [16, 17, 18, 19]
         |          ^ [15]
  [2]  4:6: `a2` is defined as this expression, (Part3, Part3)
       4 | a2 = (a1, a1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [14]
  [3]  4:6: this expression gives (Part3, Part3)
  [4]  4:7: `a1` is Part3 here
  [5]  3:6: `a1` is defined as this expression, Part3
       3 | a1 = (a0, g(false));
         |      ^^^^^^^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^^^^^^^ [13]
  [6]  3:6: this expression gives Part3
  [7]  3:7: `a0` is Part2 here
  [8]  2:6: `a0` is defined as this expression, Part2
       2 | a0 = (g(true), 3);
         |      ^^^^^^^^^^^^ [8, 9]
         |       ^^^^^^^ [10]
         |                ^ [12]
  [9]  2:6: this expression gives Part2
  [10] 2:7: this call of `g` gives Part1
  [11] 1:1: `g` is declared here with no type written for its result; the type the checker found for `g` is `bool -> Part1`
       1 | g(positional c: bool) = if c { 1 } else { 2 };
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [12] 2:16: this literal, 3, is 3
  [13] 3:11: this call of `g` gives Part1
  [14] 4:11: `a1` is Part3 here
  [15] 5:10: this literal, 1, is 1
  [16] 5:5: `+` takes (int, int) -> int
  [17] 5:5: `+` takes (f64, f64) -> f64
  [18] 5:5: `+` takes (rat, rat) -> rat
  [19] 5:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_union_is_written_in_full_until_a_step_uses_it_twice_and_named_in_every_step_after() {
    // The sentence and steps [1] to [3] use `#a | #b` once and write it; step [4] uses it
    // twice and names it `Part1`; step [6] uses it once and keeps the name.
    assert_eq!(
        rejected(
            "k(positional p: #a | #b) = (p, 0);\nm(positional p: #a | #b) = 0;\n\
             a0 = k(#a);\nu = a0 + m(#b);\n"
        ),
        r#"4:5: `+` does not take ((#a | #b, 0), 0): no arrow of `+` takes these types.
  Part1 stands for a part written more than once:
    type Part1 = #a | #b;
  [1]  4:5: `a0` is (#a | #b, 0) here
       4 | u = a0 + m(#b);
         |     ^^ [1]
         |     ^^^^^^^^^^ [7, 8, 9, 10]
         |          ^^^^^ [5]
  [2]  3:6: `a0` is defined as this expression, (#a | #b, 0)
       3 | a0 = k(#a);
         |      ^^^^^
  [3]  3:6: this call of `k` gives (#a | #b, 0)
  [4]  1:1: `k` is declared here with no type written for its result; the type the checker found for `k` is `Part1 -> (Part1, 0)`
       1 | k(positional p: #a | #b) = (p, 0);
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [5]  4:10: this call of `m` gives 0
  [6]  2:1: `m` is declared here with no type written for its result; the type the checker found for `m` is `Part1 -> 0`
       2 | m(positional p: #a | #b) = 0;
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [7]  4:5: `+` takes (int, int) -> int
  [8]  4:5: `+` takes (f64, f64) -> f64
  [9]  4:5: `+` takes (rat, rat) -> rat
  [10] 4:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_union_the_sentence_uses_twice_is_named_in_every_step() {
    // The sentence writes `#a | #b` twice, so step [2], which uses it once, writes `Part1`.
    assert_eq!(
        rejected(
            "k(positional p: #a | #b) = (p, p);\nm(positional p: #a | #b) = 0;\n\
             u = m(#b) + k(#a);\n"
        ),
        r#"3:5: `+` does not take (0, (Part1, Part1)): no arrow of `+` takes these types.
  Part1 stands for a part written more than once:
    type Part1 = #a | #b;
  [1] 3:5: this call of `m` gives 0
      3 | u = m(#b) + k(#a);
        |     ^^^^^ [1]
        |     ^^^^^^^^^^^^^ [5, 6, 7, 8]
        |             ^^^^^ [3]
  [2] 2:1: `m` is declared here with no type written for its result; the type the checker found for `m` is `Part1 -> 0`
      2 | m(positional p: #a | #b) = 0;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [3] 3:13: this call of `k` gives (Part1, Part1)
  [4] 1:1: `k` is declared here with no type written for its result; the type the checker found for `k` is `Part1 -> (Part1, Part1)`
      1 | k(positional p: #a | #b) = (p, p);
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [5] 3:5: `+` takes (int, int) -> int
  [6] 3:5: `+` takes (f64, f64) -> f64
  [7] 3:5: `+` takes (rat, rat) -> rat
  [8] 3:5: `+` takes (f32, f32) -> f32"#
    );
}

// A part holding a union is taken again by later steps (MSG-derive-print-unions). A union is
// named from the first step of the message that uses it twice and in every step after, so a
// part's text does not depend on the type it stands in, and each part is printed once for the
// message (MSG-derive-print-union-names, option (1) of COMPLEXITY.md row K110).
// Before, no part holding a union was kept, and a chain of n links each holding one printed
// each link's whole type at each of its steps, O(n²) (COMPLEXITY.md row K110).

/// `g` gives `1 | 2`, `a0 = (g(true), 0);` and `a_i = (a_{i-1}, g(false))` up to `a_n`, then
/// `u = a_n < 1;`: each link holds the union, and from `a1` on uses it twice.
pub(super) fn unions(n: usize) -> String {
    let mut src =
        "g(positional c: bool) = if c { 1 } else { 2 };\na0 = (g(true), 0);\n".to_string();
    for i in 1..=n {
        src += &format!("a{i} = (a{}, g(false));\n", i - 1);
    }
    src + &format!("u = a{n} < 1;\n")
}

/// [`unions`] with a union of its own at each link: `g_i` gives `i | i + 1`.
pub(super) fn unions_each_its_own(n: usize) -> String {
    let mut src =
        "g0(positional c: bool) = if c { 0 } else { 1 };\na0 = (g0(true), 0);\n".to_string();
    for i in 1..=n {
        src += &format!(
            "g{i}(positional c: bool) = if c {{ {i} }} else {{ {} }};\na{i} = (a{}, g{i}(false));\n",
            i + 1,
            i - 1
        );
    }
    src + &format!("u = a{n} < 1;\n")
}

/// `a_i = (a_{i-1}, 0)` holds the union of `a0` once, deep inside, `d_i = (a_i, g(false))`
/// uses it twice, and `e_i = (e_{i-1}, d_i)` holds every `d_i`, then `u = e_n < 1;`: each
/// `a_i` is printed where the union is used once and inside a `d_i`, where it is used twice.
pub(super) fn unions_inside(n: usize) -> String {
    let mut src = "g(positional c: bool) = if c { 1 } else { 2 };\na0 = (g(true), 0);\n\
                   d0 = (a0, g(false));\ne0 = (d0, 0);\n"
        .to_string();
    for i in 1..=n {
        src += &format!(
            "a{i} = (a{}, 0);\nd{i} = (a{i}, g(false));\ne{i} = (e{}, d{i});\n",
            i - 1,
            i - 1
        );
    }
    src + &format!("u = e{n} < 1;\n")
}

/// [`unions_inside`] with each `e_i = (d_i, e_{i-1})`: the step of `e_i` meets the steps of
/// `d_i` first, and those of `e_{i-1}`, most of them already met inside `d_i`, second.
pub(super) fn unions_inside_reversed(n: usize) -> String {
    let mut src = "g(positional c: bool) = if c { 1 } else { 2 };\na0 = (g(true), 0);\n\
                   d0 = (a0, g(false));\ne0 = (d0, 0);\n"
        .to_string();
    for i in 1..=n {
        src += &format!(
            "a{i} = (a{}, 0);\nd{i} = (a{i}, g(false));\ne{i} = (d{i}, e{});\n",
            i - 1,
            i - 1
        );
    }
    src + &format!("u = e{n} < 1;\n")
}

/// `a_n` holds `n` unions once each, `g_i` giving `2i | 2i + 1` in `a_i = (a_{i-1}, g_i(true))`,
/// and `e_0 = (a_n, 0); e_k = (e_{k-1}, g_k(false))` uses one more of them twice at each link,
/// then `u = e_n < 1;` (MSG-derive-print-union-names).
pub(super) fn unions_named_one_by_one(n: usize) -> String {
    let mut src = String::new();
    for i in 1..=n {
        src += &format!(
            "g{i}(positional c: bool) = if c {{ {} }} else {{ {} }};\n",
            2 * i,
            2 * i + 1
        );
    }
    src += "a1 = (g1(true), 0);\n";
    for i in 2..=n {
        src += &format!("a{i} = (a{}, g{i}(true));\n", i - 1);
    }
    src += &format!("e0 = (a{n}, 0);\n");
    for k in 1..=n {
        src += &format!("e{k} = (e{}, g{k}(false));\n", k - 1);
    }
    src + &format!("u = e{n} < 1;\n")
}

/// `src` with its last line's `+ 1` made `< 1`. The derivation is the one `+` gives, but `<`
/// tries no repair, so the tests that use it measure the derivation alone; the repair of
/// `t_n + 1`, which lists the values of `t_n` (`Type::values_listed`), is measured by the tests
/// that add 1.
pub(super) fn compared_with_1(src: String) -> String {
    let at = src.rfind(" + 1;").expect("the last line adds 1");
    src[..at].to_string() + " < 1;\n"
}

/// The `type Part… = …;` lines of the rejection `out`, each its right side.
fn declared_parts(out: &str) -> Vec<&str> {
    out.lines()
        .filter_map(|l| l.trim_start().strip_prefix("type Part"))
        .filter_map(|l| Some(l.split_once(" = ")?.1.trim_end_matches(';')))
        .collect()
}

/// Each chain of unions of `bench::type_size` at 1, 2 and 3 links: each part is declared once,
/// each union of [`unions`] and [`unions_named_one_by_one`] is a part of its own, and the text
/// at 16 links is at most 3 × 8 times the text at 2 (the benchmarks time 40 and 320 links).
#[test]
fn rejecting_short_chains_of_names_holding_unions() {
    type Maker = (&'static str, fn(usize) -> String);
    let makers: [Maker; 5] = [
        ("unions", unions),
        ("unions_each_its_own", unions_each_its_own),
        ("unions_inside", unions_inside),
        ("unions_inside_reversed", unions_inside_reversed),
        ("unions_named_one_by_one", unions_named_one_by_one),
    ];
    for (name, make) in makers {
        for n in [1, 2, 3] {
            let out = rejected(&make(n));
            let parts = declared_parts(&out);
            let distinct: std::collections::BTreeSet<&&str> = parts.iter().collect();
            assert_eq!(distinct.len(), parts.len(), "{name} {n}:\n{out}");
            let unions: Vec<String> = parts
                .iter()
                .filter(|p| !p.starts_with('('))
                .map(|p| p.to_string())
                .collect();
            let want: Vec<String> = match name {
                "unions" | "unions_inside" | "unions_inside_reversed" => vec!["1 | 2".into()],
                "unions_named_one_by_one" => (1..=n)
                    .map(|i| format!("{} | {}", 2 * i, 2 * i + 1))
                    .collect(),
                _ => vec![],
            };
            assert_eq!(unions, want, "{name} {n}:\n{out}");
        }
        let (small, large) = (rejected(&make(2)).len(), rejected(&make(16)).len());
        assert!(
            large <= 3 * 8 * small,
            "{name}: {small} at 2, {large} at 16"
        );
    }
}
