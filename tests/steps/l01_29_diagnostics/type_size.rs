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
fn doubling(n: usize) -> String {
    let mut src = "t0 = (1, 1);\n".to_string();
    for i in 1..=n {
        src += &format!("t{i} = (t{0}, t{0});\n", i - 1);
    }
    src + &format!("u = t{n} + 1;\n")
}

/// The chains of [`doubling`] from `(1, 1)` and from `(1, true)`, then `u = t_n < s_n;`.
fn compared(n: usize) -> String {
    let mut src = "t0 = (1, 1);\ns0 = (1, true);\n".to_string();
    for i in 1..=n {
        src += &format!("t{i} = (t{0}, t{0});\ns{i} = (s{0}, s{0});\n", i - 1);
    }
    src + &format!("u = t{n} < s{n};\n")
}

/// `a0 = (0, 0);` and `a_i = (a_{i-1}, i)` up to `a_n`, then `u = a_n + 1;`: each name holds
/// the one before.
fn growing(n: usize) -> String {
    let mut src = "a0 = (0, 0);\n".to_string();
    for i in 1..=n {
        src += &format!("a{i} = (a{}, {i});\n", i - 1);
    }
    src + &format!("u = a{n} + 1;\n")
}

/// `x0` a tuple of `m` components and `x_i = x_{i-1}` up to `x_n`, then `u = x_n + 1;`: each
/// step of the chain has the one type.
fn same(n: usize, m: usize) -> String {
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
        r#"8:5: `+` does not take ((T5, T5), 1): no arrow of `+` takes these types.
  T1, T2, T3, T4 and T5 stand for parts written more than once:
    type T1 = ((1, 1), (1, 1));
    type T2 = (T1, T1);
    type T3 = (T2, T2);
    type T4 = (T3, T3);
    type T5 = (T4, T4);
  [1]  8:5: `t6` is (T5, T5) here
       8 | u = t6 + 1;
         |     ^^ [1]
         |     ^^^^^^ [31, 32, 33, 34]
         |          ^ [30]
  [2]  7:6: `t6` is defined as this expression, (T5, T5)
       7 | t6 = (t5, t5);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [29]
  [3]  7:6: this expression gives (T5, T5)
  [4]  7:7: `t5` is T5 here
  [5]  6:6: `t5` is defined as this expression, T5
       6 | t5 = (t4, t4);
         |      ^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^ [28]
  [6]  6:6: this expression gives T5
  [7]  6:7: `t4` is T4 here
  [8]  5:6: `t4` is defined as this expression, T4
       5 | t4 = (t3, t3);
         |      ^^^^^^^^ [8, 9]
         |       ^^ [10]
         |           ^^ [27]
  [9]  5:6: this expression gives T4
  [10] 5:7: `t3` is T3 here
  [11] 4:6: `t3` is defined as this expression, T3
       4 | t3 = (t2, t2);
         |      ^^^^^^^^ [11, 12]
         |       ^^ [13]
         |           ^^ [26]
  [12] 4:6: this expression gives T3
  [13] 4:7: `t2` is T2 here
  [14] 3:6: `t2` is defined as this expression, T2
       3 | t2 = (t1, t1);
         |      ^^^^^^^^ [14, 15]
         |       ^^ [16]
         |           ^^ [25]
  [15] 3:6: this expression gives T2
  [16] 3:7: `t1` is T1 here
  [17] 2:6: `t1` is defined as this expression, T1
       2 | t1 = (t0, t0);
         |      ^^^^^^^^ [17, 18]
         |       ^^ [19]
         |           ^^ [24]
  [18] 2:6: this expression gives T1
  [19] 2:7: `t0` is (1, 1) here
  [20] 1:6: `t0` is defined as this expression, (1, 1)
       1 | t0 = (1, 1);
         |      ^^^^^^ [20, 21]
         |       ^ [22]
         |          ^ [23]
  [21] 1:6: this expression gives (1, 1)
  [22] 1:7: this literal, 1, is 1
  [23] 1:10: this literal, 1, is 1
  [24] 2:11: `t0` is (1, 1) here
  [25] 3:11: `t1` is T1 here
  [26] 4:11: `t2` is T2 here
  [27] 5:11: `t3` is T3 here
  [28] 6:11: `t4` is T4 here
  [29] 7:11: `t5` is T5 here
  [30] 8:10: this literal, 1, is 1
  [31] 8:5: `+` takes (int, int) -> int
  [32] 8:5: `+` takes (f64, f64) -> f64
  [33] 8:5: `+` takes (rat, rat) -> rat
  [34] 8:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn comparing_two_doubled_tuples_names_each_level_once() {
    assert_eq!(
        rejected(&compared(6)),
        r#"15:5: Cannot compare unequal types: `t6[1][1][1][1][1][1][1] : 1 < s6[1][1][1][1][1][1][1] : true` in `t6 < s6`.
  T1, T2, T3, T4, T5, T6, T7, T8, T9 and T10 stand for parts written more than once:
    type T1 = ((1, 1), (1, 1));
    type T2 = (T1, T1);
    type T3 = (T2, T2);
    type T4 = (T3, T3);
    type T5 = (T4, T4);
    type T6 = ((1, true), (1, true));
    type T7 = (T6, T6);
    type T8 = (T7, T7);
    type T9 = (T8, T8);
    type T10 = (T9, T9);
  [1]  15:5: `t6` is (T5, T5) here
       15 | u = t6 < s6;
          |     ^^ [1]
          |     ^^^^^^^ [59, 60, 61, 62, 63, 64, 65, 66, 67, 68]
          |          ^^ [30]
  [2]  13:6: `t6` is defined as this expression, (T5, T5)
       13 | t6 = (t5, t5);
          |      ^^^^^^^^ [2, 3]
          |       ^^ [4]
          |           ^^ [29]
  [3]  13:6: this expression gives (T5, T5)
  [4]  13:7: `t5` is T5 here
  [5]  11:6: `t5` is defined as this expression, T5
       11 | t5 = (t4, t4);
          |      ^^^^^^^^ [5, 6]
          |       ^^ [7]
          |           ^^ [28]
  [6]  11:6: this expression gives T5
  [7]  11:7: `t4` is T4 here
  [8]  9:6: `t4` is defined as this expression, T4
        9 | t4 = (t3, t3);
          |      ^^^^^^^^ [8, 9]
          |       ^^ [10]
          |           ^^ [27]
  [9]  9:6: this expression gives T4
  [10] 9:7: `t3` is T3 here
  [11] 7:6: `t3` is defined as this expression, T3
        7 | t3 = (t2, t2);
          |      ^^^^^^^^ [11, 12]
          |       ^^ [13]
          |           ^^ [26]
  [12] 7:6: this expression gives T3
  [13] 7:7: `t2` is T2 here
  [14] 5:6: `t2` is defined as this expression, T2
        5 | t2 = (t1, t1);
          |      ^^^^^^^^ [14, 15]
          |       ^^ [16]
          |           ^^ [25]
  [15] 5:6: this expression gives T2
  [16] 5:7: `t1` is T1 here
  [17] 3:6: `t1` is defined as this expression, T1
        3 | t1 = (t0, t0);
          |      ^^^^^^^^ [17, 18]
          |       ^^ [19]
          |           ^^ [24]
  [18] 3:6: this expression gives T1
  [19] 3:7: `t0` is (1, 1) here
  [20] 1:6: `t0` is defined as this expression, (1, 1)
        1 | t0 = (1, 1);
          |      ^^^^^^ [20, 21]
          |       ^ [22]
          |          ^ [23]
  [21] 1:6: this expression gives (1, 1)
  [22] 1:7: this literal, 1, is 1
  [23] 1:10: this literal, 1, is 1
  [24] 3:11: `t0` is (1, 1) here
  [25] 5:11: `t1` is T1 here
  [26] 7:11: `t2` is T2 here
  [27] 9:11: `t3` is T3 here
  [28] 11:11: `t4` is T4 here
  [29] 13:11: `t5` is T5 here
  [30] 15:10: `s6` is (T10, T10) here
  [31] 14:6: `s6` is defined as this expression, (T10, T10)
       14 | s6 = (s5, s5);
          |      ^^^^^^^^ [31, 32]
          |       ^^ [33]
          |           ^^ [58]
  [32] 14:6: this expression gives (T10, T10)
  [33] 14:7: `s5` is T10 here
  [34] 12:6: `s5` is defined as this expression, T10
       12 | s5 = (s4, s4);
          |      ^^^^^^^^ [34, 35]
          |       ^^ [36]
          |           ^^ [57]
  [35] 12:6: this expression gives T10
  [36] 12:7: `s4` is T9 here
  [37] 10:6: `s4` is defined as this expression, T9
       10 | s4 = (s3, s3);
          |      ^^^^^^^^ [37, 38]
          |       ^^ [39]
          |           ^^ [56]
  [38] 10:6: this expression gives T9
  [39] 10:7: `s3` is T8 here
  [40] 8:6: `s3` is defined as this expression, T8
        8 | s3 = (s2, s2);
          |      ^^^^^^^^ [40, 41]
          |       ^^ [42]
          |           ^^ [55]
  [41] 8:6: this expression gives T8
  [42] 8:7: `s2` is T7 here
  [43] 6:6: `s2` is defined as this expression, T7
        6 | s2 = (s1, s1);
          |      ^^^^^^^^ [43, 44]
          |       ^^ [45]
          |           ^^ [54]
  [44] 6:6: this expression gives T7
  [45] 6:7: `s1` is T6 here
  [46] 4:6: `s1` is defined as this expression, T6
        4 | s1 = (s0, s0);
          |      ^^^^^^^^ [46, 47]
          |       ^^ [48]
          |           ^^ [53]
  [47] 4:6: this expression gives T6
  [48] 4:7: `s0` is (1, true) here
  [49] 2:6: `s0` is defined as this expression, (1, true)
        2 | s0 = (1, true);
          |      ^^^^^^^^^ [49, 50]
          |       ^ [51]
          |          ^^^^ [52]
  [50] 2:6: this expression gives (1, true)
  [51] 2:7: this literal, 1, is 1
  [52] 2:10: this expression is true
  [53] 4:11: `s0` is (1, true) here
  [54] 6:11: `s1` is T6 here
  [55] 8:11: `s2` is T7 here
  [56] 10:11: `s3` is T8 here
  [57] 12:11: `s4` is T9 here
  [58] 14:11: `s5` is T10 here
  [59] 15:5: `<` compares two tuples component by component, as far as the shorter goes
  [60] 15:5: components `[1]` are tuples, compared the same way
  [61] 15:5: components `[1]` are tuples, compared the same way
  [62] 15:5: components `[1]` are tuples, compared the same way
  [63] 15:5: components `[1]` are tuples, compared the same way
  [64] 15:5: components `[1]` are tuples, compared the same way
  [65] 15:5: components `[1]` are tuples, compared the same way
  [66] 15:5: `<` compares components `[1]`: `t6[1][1][1][1][1][1][1] : 1` with `s6[1][1][1][1][1][1][1] : true`
  [67] 15:5: `<` compares only two numbers of one kind or two values of one other kind
  [68] 15:5: repair: change the type of `t6` or `s6` so that `t6[1][1][1][1][1][1][1]` and `s6[1][1][1][1][1][1][1]` compare"#
    );
}

#[test]
fn a_chain_of_names_each_holding_the_one_before_names_each_link() {
    assert_eq!(
        rejected(&growing(4)),
        r#"6:5: `+` does not take ((T3, 4), 1): no arrow of `+` takes these types.
  T1, T2 and T3 stand for parts written more than once:
    type T1 = ((0, 0), 1);
    type T2 = (T1, 2);
    type T3 = (T2, 3);
  [1]  6:5: `a4` is (T3, 4) here
       6 | u = a4 + 1;
         |     ^^ [1]
         |     ^^^^^^ [23, 24, 25, 26]
         |          ^ [22]
  [2]  5:6: `a4` is defined as this expression, (T3, 4)
       5 | a4 = (a3, 4);
         |      ^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^ [21]
  [3]  5:6: this expression gives (T3, 4)
  [4]  5:7: `a3` is T3 here
  [5]  4:6: `a3` is defined as this expression, T3
       4 | a3 = (a2, 3);
         |      ^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^ [20]
  [6]  4:6: this expression gives T3
  [7]  4:7: `a2` is T2 here
  [8]  3:6: `a2` is defined as this expression, T2
       3 | a2 = (a1, 2);
         |      ^^^^^^^ [8, 9]
         |       ^^ [10]
         |           ^ [19]
  [9]  3:6: this expression gives T2
  [10] 3:7: `a1` is T1 here
  [11] 2:6: `a1` is defined as this expression, T1
       2 | a1 = (a0, 1);
         |      ^^^^^^^ [11, 12]
         |       ^^ [13]
         |           ^ [18]
  [12] 2:6: this expression gives T1
  [13] 2:7: `a0` is (0, 0) here
  [14] 1:6: `a0` is defined as this expression, (0, 0)
       1 | a0 = (0, 0);
         |      ^^^^^^ [14, 15]
         |       ^ [16]
         |          ^ [17]
  [15] 1:6: this expression gives (0, 0)
  [16] 1:7: this literal, 0, is 0
  [17] 1:10: this literal, 0, is 0
  [18] 2:11: this literal, 1, is 1
  [19] 3:11: this literal, 2, is 2
  [20] 4:11: this literal, 3, is 3
  [21] 5:11: this literal, 4, is 4
  [22] 6:10: this literal, 1, is 1
  [23] 6:5: `+` takes (int, int) -> int
  [24] 6:5: `+` takes (f64, f64) -> f64
  [25] 6:5: `+` takes (rat, rat) -> rat
  [26] 6:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_chain_of_names_of_one_type_writes_the_type_whole_at_each_link() {
    // A whole type in a step is written in full, so a chain of n names of one type of m
    // components writes n × m (COMPLEXITY.md row MSG-derive-same-chain).
    assert_eq!(
        rejected(&same(4, 5)),
        r#"6:5: `+` does not take ((0, 1, 2, 3, 4), 1): no arrow of `+` takes these types.
  [1]  6:5: `x4` is (0, 1, 2, 3, 4) here
       6 | u = x4 + 1;
         |     ^^ [1]
         |     ^^^^^^ [18, 19, 20, 21]
         |          ^ [17]
  [2]  5:6: `x4` is defined as this expression, (0, 1, 2, 3, 4)
       5 | x4 = x3;
         |      ^^
  [3]  5:6: `x3` is (0, 1, 2, 3, 4) here
  [4]  4:6: `x3` is defined as this expression, (0, 1, 2, 3, 4)
       4 | x3 = x2;
         |      ^^
  [5]  4:6: `x2` is (0, 1, 2, 3, 4) here
  [6]  3:6: `x2` is defined as this expression, (0, 1, 2, 3, 4)
       3 | x2 = x1;
         |      ^^
  [7]  3:6: `x1` is (0, 1, 2, 3, 4) here
  [8]  2:6: `x1` is defined as this expression, (0, 1, 2, 3, 4)
       2 | x1 = x0;
         |      ^^
  [9]  2:6: `x0` is (0, 1, 2, 3, 4) here
  [10] 1:6: `x0` is defined as this expression, (0, 1, 2, 3, 4)
       1 | x0 = (0, 1, 2, 3, 4);
         |      ^^^^^^^^^^^^^^^ [10, 11]
         |       ^ [12]   ^ [15]
         |          ^ [13]   ^ [16]
         |             ^ [14]
  [11] 1:6: this expression gives (0, 1, 2, 3, 4)
  [12] 1:7: this literal, 0, is 0
  [13] 1:10: this literal, 1, is 1
  [14] 1:13: this literal, 2, is 2
  [15] 1:16: this literal, 3, is 3
  [16] 1:19: this literal, 4, is 4
  [17] 6:10: this literal, 1, is 1
  [18] 6:5: `+` takes (int, int) -> int
  [19] 6:5: `+` takes (f64, f64) -> f64
  [20] 6:5: `+` takes (rat, rat) -> rat
  [21] 6:5: `+` takes (f32, f32) -> f32"#
    );
}

/// Checks that the rejection of `make(8n)` is at most about 8 times as long as that of
/// `make(n)`. [`works`] holds the work to the same order, on the same derivations without the
/// repair of `+` ([`compared_with_1`]).
fn scales(what: &str, n: usize, make: fn(usize) -> String) {
    use zed_tests::scaling;
    let large = scaling::FACTOR * n;
    let bytes = |k: usize| rejected(&make(k)).len();
    let (ratio, limit) = (
        bytes(large) as f64 / bytes(n) as f64,
        scaling::limit(n, large, 1),
    );
    assert!(
        ratio <= limit,
        "{what}: {ratio} times the bytes, more than {limit}"
    );
}

#[test]
fn rejecting_a_tuple_doubled_n_times_writes_a_text_linear_in_n() {
    scales("rejecting a tuple doubled n times", 40, doubling);
}

#[test]
fn rejecting_a_comparison_of_tuples_doubled_n_times_writes_a_text_linear_in_n() {
    scales(
        "rejecting a comparison of tuples doubled n times",
        40,
        compared,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_the_one_before_writes_a_text_linear_in_n() {
    scales(
        "rejecting a chain of n names each holding the one before",
        40,
        growing,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_of_one_type_writes_a_text_linear_in_n() {
    // A type of five components at each link. A type as wide as the chain is long is written
    // whole at each link, n × m in all (COMPLEXITY.md row MSG-derive-same-chain).
    scales(
        "rejecting a chain of n names of one type of five components",
        40,
        |n| same(n, 5),
    );
}

/// Checks that rejecting `make(8n)` does at most about 8 times the work and allocates at most
/// about 8 times the bytes of rejecting `make(n)`: the derivation prints the parts of its types
/// once per message, not once per step (MSG-derive-print-per-message).
fn works(what: &str, n: usize, make: fn(usize) -> String) {
    use zed_tests::scaling;
    let srcs = scaling::inputs(n, make);
    scaling::check(what, n, |k| {
        rejected(&srcs[&k]);
    });
}

/// `src` with its last line's `+ 1` made `< 1`. The derivation is the one `+` gives, but `<`
/// tries no repair, so these tests measure the derivation alone; the repair of `t_n + 1`, which
/// lists the values of `t_n` (`Type::values_listed`), is measured by the tests that add 1.
fn compared_with_1(src: String) -> String {
    let at = src.rfind(" + 1;").expect("the last line adds 1");
    src[..at].to_string() + " < 1;\n"
}

#[test]
fn rejecting_a_comparison_of_a_tuple_doubled_n_times_with_1_does_work_linear_in_n() {
    works(
        "rejecting a comparison of a tuple doubled n times with 1",
        40,
        |n| compared_with_1(doubling(n)),
    );
}

#[test]
fn rejecting_a_comparison_of_tuples_doubled_n_times_does_work_linear_in_n() {
    works(
        "rejecting a comparison of tuples doubled n times",
        40,
        compared,
    );
}

#[test]
fn rejecting_a_comparison_of_a_chain_of_n_names_each_holding_the_one_before_with_1_does_work_linear_in_n()
 {
    works(
        "rejecting a comparison of a chain of n names each holding the one before with 1",
        40,
        |n| compared_with_1(growing(n)),
    );
}

// The repair of `t_n + 1` lists the one value of `t_n`. Its maker files the first components
// of each type once for the whole listing; before, each level's maker walked every level below
// it again, O(n²) in a chain of n levels (COMPLEXITY.md row K109, MAKER-file-chain).

#[test]
fn rejecting_a_tuple_doubled_n_times_with_1_added_does_work_linear_in_n() {
    works(
        "rejecting a tuple doubled n times with 1 added",
        40,
        doubling,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_the_one_before_with_1_added_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each holding the one before with 1 added",
        40,
        growing,
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
        r#"4:5: `+` does not take ((T1, T1), 1): no arrow of `+` takes these types.
  T1 stands for a part written more than once:
    type T1 = ((0x1F, 1), 0x1F);
  [1]  4:5: `a2` is (T1, T1) here
       4 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [15, 16, 17, 18]
         |          ^ [14]
  [2]  3:6: `a2` is defined as this expression, (T1, T1)
       3 | a2 = (a1, a1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [13]
  [3]  3:6: this expression gives (T1, T1)
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
        r#"4:5: `+` does not take ((T1, T1), 1): no arrow of `+` takes these types.
  T1 stands for a part written more than once:
    type T1 = ((-0r, 1), -0r);
  [1]  4:5: `a2` is (T1, T1) here
       4 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [16, 17, 18, 19]
         |          ^ [15]
  [2]  3:6: `a2` is defined as this expression, (T1, T1)
       3 | a2 = (a1, a1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [14]
  [3]  3:6: this expression gives (T1, T1)
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
        r#"7:5: `+` does not take ((T3, T3), 1): no arrow of `+` takes these types.
  T1, T2 and T3 stand for parts written more than once:
    type T1 = (1, true);
    type T2 = ((9, "z"), T1);
    type T3 = ((T2, T1) | (T2, (9, "z")), T2);
  [1]  7:5: `w` is (T3, T3) here
       7 | u = w + 1;
         |     ^ [1]
         |     ^^^^^ [24, 25, 26, 27]
         |         ^ [23]
  [2]  6:5: `w` is defined as this expression, (T3, T3)
       6 | w = (v, v);
         |     ^^^^^^ [2, 3]
         |      ^ [4]
         |         ^ [22]
  [3]  6:5: this expression gives (T3, T3)
  [4]  6:6: `v` is T3 here
  [5]  5:5: `v` is defined as this expression, T3
       5 | v = (g(true), x);
         |     ^^^^^^^^^^^^ [5, 6]
         |      ^^^^^^^ [7]
         |               ^ [9]
  [6]  5:5: this expression gives T3
  [7]  5:6: this call of `g` gives (T2, (9, "z")) | (T2, T1)
  [8]  4:1: `g` is declared here with no type written for its result; the type the checker found for `g` is `(bool) -> (T2, (9, "z")) | (T2, T1)`
       4 | g(positional c: bool) = if c { (x, b0) } else { (x, a0) };
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [9]  5:15: `x` is T2 here
  [10] 3:5: `x` is defined as this expression, T2
       3 | x = (b0, a0);
         |     ^^^^^^^^ [10, 11]
         |      ^^ [12]
         |          ^^ [17]
  [11] 3:5: this expression gives T2
  [12] 3:6: `b0` is (9, "z") here
  [13] 1:6: `b0` is defined as this expression, (9, "z")
       1 | b0 = (9, "z");
         |      ^^^^^^^^ [13, 14]
         |       ^ [15]
         |          ^^^ [16]
  [14] 1:6: this expression gives (9, "z")
  [15] 1:7: this literal, 9, is 9
  [16] 1:10: this expression is "z"
  [17] 3:10: `a0` is T1 here
  [18] 2:6: `a0` is defined as this expression, T1
       2 | a0 = (1, true);
         |      ^^^^^^^^^ [18, 19]
         |       ^ [20]
         |          ^^^^ [21]
  [19] 2:6: this expression gives T1
  [20] 2:7: this literal, 1, is 1
  [21] 2:10: this expression is true
  [22] 6:9: `v` is T3 here
  [23] 7:9: this literal, 1, is 1
  [24] 7:5: `+` takes (int, int) -> int
  [25] 7:5: `+` takes (f64, f64) -> f64
  [26] 7:5: `+` takes (rat, rat) -> rat
  [27] 7:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_union_inside_a_tuple_printed_before_is_named_as_the_later_type_uses_it() {
    // `1 | 2` is written once in `a0`'s type and twice in `a1`'s, so `a1`'s steps name it,
    // and `a0`'s tuple inside `a1` is written with that name, not as `a0`'s steps wrote it.
    assert_eq!(
        rejected(
            "g(positional c: bool) = if c { 1 } else { 2 };\na0 = (g(true), 3);\n\
             a1 = (a0, g(false));\na2 = (a1, a1);\nu = a2 + 1;\n"
        ),
        r#"5:5: `+` does not take ((T2, T2), 1): no arrow of `+` takes these types.
  T1 and T2 stand for parts written more than once:
    type T1 = 1 | 2;
    type T2 = ((T1, 3), T1);
  [1]  5:5: `a2` is (T2, T2) here
       5 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [16, 17, 18, 19]
         |          ^ [15]
  [2]  4:6: `a2` is defined as this expression, (T2, T2)
       4 | a2 = (a1, a1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [14]
  [3]  4:6: this expression gives (T2, T2)
  [4]  4:7: `a1` is T2 here
  [5]  3:6: `a1` is defined as this expression, T2
       3 | a1 = (a0, g(false));
         |      ^^^^^^^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^^^^^^^ [13]
  [6]  3:6: this expression gives T2
  [7]  3:7: `a0` is (1 | 2, 3) here
  [8]  2:6: `a0` is defined as this expression, (1 | 2, 3)
       2 | a0 = (g(true), 3);
         |      ^^^^^^^^^^^^ [8, 9]
         |       ^^^^^^^ [10]
         |                ^ [12]
  [9]  2:6: this expression gives (1 | 2, 3)
  [10] 2:7: this call of `g` gives 1 | 2
  [11] 1:1: `g` is declared here with no type written for its result; the type the checker found for `g` is `(bool) -> 1 | 2`
       1 | g(positional c: bool) = if c { 1 } else { 2 };
         | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [12] 2:16: this literal, 3, is 3
  [13] 3:11: this call of `g` gives 1 | 2
  [14] 4:11: `a1` is T2 here
  [15] 5:10: this literal, 1, is 1
  [16] 5:5: `+` takes (int, int) -> int
  [17] 5:5: `+` takes (f64, f64) -> f64
  [18] 5:5: `+` takes (rat, rat) -> rat
  [19] 5:5: `+` takes (f32, f32) -> f32"#
    );
}

// A part holding a union is taken again by later steps where it writes the union as the type
// it stands in does (MSG-derive-print-unions). A union is named by how often the whole type
// uses it, so a part printed before, where the union was used once and written out, is not the
// text it has in a type that uses the union twice; each kept part carries how often it uses
// each such inner part, and is taken again only where those uses agree with the type's.
// Before, no part holding a union was kept, and a chain of n links each holding one printed
// each link's whole type at each of its steps, O(n²) (COMPLEXITY.md row K110).

/// `g` gives `1 | 2`, `a0 = (g(true), 0);` and `a_i = (a_{i-1}, g(false))` up to `a_n`, then
/// `u = a_n < 1;`: each link holds the union, and from `a1` on uses it twice.
fn unions(n: usize) -> String {
    let mut src =
        "g(positional c: bool) = if c { 1 } else { 2 };\na0 = (g(true), 0);\n".to_string();
    for i in 1..=n {
        src += &format!("a{i} = (a{}, g(false));\n", i - 1);
    }
    src + &format!("u = a{n} < 1;\n")
}

/// [`unions`] with a union of its own at each link: `g_i` gives `i | i + 1`.
fn unions_each_its_own(n: usize) -> String {
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
fn unions_inside(n: usize) -> String {
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

#[test]
fn rejecting_a_chain_of_n_names_each_holding_a_union_writes_a_text_linear_in_n() {
    scales(
        "rejecting a chain of n names each holding a union",
        40,
        unions,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_a_union_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each holding a union",
        40,
        unions,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_a_union_of_its_own_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each holding a union of its own",
        40,
        unions_each_its_own,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_using_a_union_once_and_twice_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each using a union once and twice",
        40,
        unions_inside,
    );
}
