//! The machine-word widening notice (DESIGN.md sec:domains): a warning, which does not stop
//! the build, at each integer operation whose operands fit in a machine word while its
//! result may not. It names the value, the operands' widths and the interval the operation
//! gives, and derives each operand's interval from its literals and bindings.

use zed_tests::scaling;
use zedc::run::load;

/// The rendered warnings of the accepted program `src`, one after another.
fn warned(src: &str) -> String {
    let program = load(src.as_bytes()).unwrap_or_else(|e| panic!("rejected:\n{e}\n{src}"));
    let ws: Vec<String> = program.warnings().iter().map(|w| w.to_string()).collect();
    ws.join("\n")
}

/// The first line of each warning of `src`.
fn messages(src: &str) -> Vec<String> {
    let program = load(src.as_bytes()).unwrap_or_else(|e| panic!("rejected:\n{e}\n{src}"));
    program
        .warnings()
        .iter()
        .map(|w| format!("{}:{}: {}", w.line, w.col, w.message))
        .collect()
}

/// A `main` whose body binds `lines` and reports `out`.
fn main_with(lines: &str, out: &str) -> String {
    format!("main(stdin: Lines) -> (stdout: Lines) {{\n{lines}  stdout <- String({out});\n}}\n")
}

#[test]
fn the_area_of_a_large_square_warns_with_its_derivation() {
    let src = main_with("  side = 3037000500;\n  area = side * side;\n", "area");
    assert_eq!(
        warned(&src),
        "\
3:10: `area` widens past a machine word: this `*` of an i64 and an i64 gives a big integer
  [1] 3:10: this `*` gives 9223372037000250000, past i64
      3 |   area = side * side;
        |          ^^^^^^^^^^^
  [2] 3:10: `side` is 3037000500 here
      3 |   area = side * side;
        |          ^^^^
  [3] 2:10: `side` is defined as this expression, 3037000500
      2 |   side = 3037000500;
        |          ^^^^^^^^^^
  [4] 2:10: this literal is 3037000500
  [5] 3:17: `side` is 3037000500 here
      3 |   area = side * side;
        |                 ^^^^
  [6] 3:10: repair: if wrapping arithmetic is meant, reduce the value with `mod 2 ^ k`, k at most 64
      3 |   area = side * side;
        |          ^^^^^^^^^^^"
    );
}

#[test]
fn values_that_stay_in_a_word_do_not_warn() {
    // 3037000499 is the largest integer whose square is below 2^63, and twice
    // 4611686018427387903 is the largest i64 less one.
    let src = main_with(
        "  side = 3037000499;\n  area = side * side;\n  half = 4611686018427387903 * 2;\n  \
         byte = 255 * 255;\n  cents = 1999 * 100 + 99;\n",
        "byte + cents",
    );
    assert_eq!(messages(&src), Vec::<String>::new());
}

#[test]
fn the_exact_boundary_of_the_word() {
    // The largest and smallest i64 are reached without a warning.
    let inside = main_with(
        "  top = 9223372036854775806 + 1;\n  bottom = -9223372036854775807 - 1;\n  \
         back = -(-9223372036854775807);\n",
        "0",
    );
    assert_eq!(messages(&inside), Vec::<String>::new());
    // One step past either end warns, and so does negating the smallest i64.
    let past = main_with(
        "  over = 9223372036854775807 + 1;\n  under = -9223372036854775808 - 1;\n  \
         flip = -(-9223372036854775808);\n",
        "0",
    );
    assert_eq!(
        messages(&past),
        [
            "2:10: `over` widens past a machine word: this `+` of an i64 and an i8 gives a big \
             integer",
            "3:11: `under` widens past a machine word: this `-` of an i64 and an i8 gives a big \
             integer",
            "4:10: `flip` widens past a machine word: this `-` of an i64 gives a big integer",
        ]
    );
    let shown = warned(&past);
    assert!(shown.contains("this `+` gives 9223372036854775808, past i64"));
    assert!(shown.contains("this `-` gives -9223372036854775809, past i64"));
}

#[test]
fn each_operand_width_is_named() {
    let src = main_with(
        "  a = 127 ^ 10;\n  b = 32767 ^ 5;\n  c = 2147483647 ^ 3;\n  \
         d = 4294967296 * 4294967296;\n  e = 128 * 72057594037927936;\n  \
         f = -128 * 72057594037927937;\n",
        "0",
    );
    assert_eq!(
        messages(&src),
        [
            "2:7: `a` widens past a machine word: this `^` of an i8 and an i8 gives a big integer",
            "3:7: `b` widens past a machine word: this `^` of an i16 and an i8 gives a big integer",
            "4:7: `c` widens past a machine word: this `^` of an i32 and an i8 gives a big integer",
            "5:7: `d` widens past a machine word: this `*` of an i64 and an i64 gives a big integer",
            "6:7: `e` widens past a machine word: this `*` of an i16 and an i64 gives a big integer",
            "7:7: `f` widens past a machine word: this `*` of an i8 and an i64 gives a big integer",
        ]
    );
    let shown = warned(&src);
    assert!(shown.contains("this `^` gives 1091533853073393531649, past i64"));
    assert!(shown.contains("this `*` gives 18446744073709551616, past i64"));
}

#[test]
fn wrapping_arithmetic_reduced_by_a_power_of_two_does_not_warn() {
    // A hash step: the product leaves the word, the reduction brings it back, and the
    // intermediates may wrap (sec:domains), so there is nothing to warn about.
    let src = main_with(
        "  h = (3037000500 * 3037000500 + 7) mod 18446744073709551616;\n  \
         low = (3037000500 * 3037000500) mod 4294967296;\n  \
         k = ((3037000500 * 3037000500) mod 2 ^ 64) else 0;\n",
        "low",
    );
    assert_eq!(messages(&src), Vec::<String>::new());
}

#[test]
fn a_reduction_that_does_not_wrap_still_warns() {
    // `div` and a modulus that is not a power of two do not commute with wrapping. A
    // parenthesized operation is placed at its opening parenthesis.
    let src = main_with(
        "  half = (3037000500 * 3037000500) div 2;\n  \
         last = (3037000500 * 3037000500) mod 1000;\n",
        "0",
    );
    assert_eq!(
        messages(&src),
        [
            "2:10: `half` widens past a machine word: this `*` of an i64 and an i64 gives a big \
             integer",
            "3:10: `last` widens past a machine word: this `*` of an i64 and an i64 gives a big \
             integer",
        ]
    );
}

#[test]
fn a_power_or_a_quotient_inside_a_wrapping_reduction_still_warns() {
    // Only `+`, `-`, `*`, unary `-` and literals wrap under `mod 2 ^ k`; a `^` or a `div`
    // there is computed exactly first, so its crossing is reported.
    let src = main_with(
        "  a = (3 ^ 50 + 1) mod 2 ^ 64;\n  \
         c = (3 ^ 50) mod 2 ^ 64;\n  \
         b = ((-9223372036854775807 - 1) div -1) mod 2 ^ 64;\n",
        "0",
    );
    assert_eq!(
        messages(&src),
        [
            "2:8: `a` widens past a machine word: this `^` of an i8 and an i8 gives a big \
             integer",
            "3:7: `c` widens past a machine word: this `^` of an i8 and an i8 gives a big \
             integer",
            "4:7: `b` widens past a machine word: this `div` of an i64 and an i8 gives a big \
             integer",
        ]
    );
}

#[test]
fn a_value_already_past_the_word_warns_once() {
    let src = main_with(
        "  big = 9223372036854775807 + 1;\n  more = big * 2;\n  most = more + big;\n",
        "most",
    );
    assert_eq!(
        messages(&src),
        ["2:9: `big` widens past a machine word: this `+` of an i64 and an i8 gives a big integer"]
    );
    // A literal past the word is a big integer already.
    let lit = main_with("  big = 9223372036854775808;\n  more = big * 2;\n", "more");
    assert_eq!(messages(&lit), Vec::<String>::new());
}

#[test]
fn an_if_gives_the_interval_of_its_branches() {
    let src = main_with(
        "  n = if stdin[1] == \"x\" { 10 } else { 3037000500 };\n  sq = n * n;\n",
        "sq",
    );
    assert_eq!(
        warned(&src),
        "\
3:8: `sq` widens past a machine word: this `*` of an i64 and an i64 gives a big integer
  [1]  3:8: this `*` gives int[100..=9223372037000250000], past i64
       3 |   sq = n * n;
         |        ^^^^^
  [2]  3:8: `n` is int[10..=3037000500] here
       3 |   sq = n * n;
         |        ^
  [3]  2:7: `n` is defined as this expression, int[10..=3037000500]
       2 |   n = if stdin[1] == \"x\" { 10 } else { 3037000500 };
         |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [4]  2:7: this `if` gives int[10..=3037000500]
  [5]  2:26: this block gives 10
       2 |   n = if stdin[1] == \"x\" { 10 } else { 3037000500 };
         |                          ^^^^^^
  [6]  2:28: this literal is 10
       2 |   n = if stdin[1] == \"x\" { 10 } else { 3037000500 };
         |                            ^^
  [7]  2:38: this block gives 3037000500
       2 |   n = if stdin[1] == \"x\" { 10 } else { 3037000500 };
         |                                      ^^^^^^^^^^^^^^
  [8]  2:40: this literal is 3037000500
       2 |   n = if stdin[1] == \"x\" { 10 } else { 3037000500 };
         |                                        ^^^^^^^^^^
  [9]  3:12: `n` is int[10..=3037000500] here
       3 |   sq = n * n;
         |            ^
  [10] 3:8: repair: if wrapping arithmetic is meant, reduce the value with `mod 2 ^ k`, k at most 64
       3 |   sq = n * n;
         |        ^^^^^"
    );
}

#[test]
fn top_level_definitions_are_read_in_any_order() {
    let src = "area = side * side;\nside = 3037000500;\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- String(area);\n}\n";
    assert_eq!(
        messages(src),
        [
            "1:8: `area` widens past a machine word: this `*` of an i64 and an i64 gives a big integer"
        ]
    );
    assert!(warned(src).contains("2:8: `side` is defined as this expression, 3037000500"));
}

#[test]
fn a_float_product_does_not_warn() {
    // The generic integer literals take `f64`, so no integer operation is made.
    let src = main_with("  f = 1.5 * 3037000500n * 3037000500n;\n", "f");
    assert_eq!(messages(&src), Vec::<String>::new());
}

#[test]
fn a_parameter_is_not_bounded_and_does_not_warn() {
    // Until step L1.40b the domains come from literals and bindings: a parameter is any
    // `int`, so its square is not reported, even at a call with a large argument.
    let src = "sq(x: int) = x * x;\nmain(stdin: Lines) -> (stdout: Lines) {\n  \
               stdout <- String(sq(x: 3037000500));\n}\n";
    assert_eq!(messages(src), Vec::<String>::new());
}

#[test]
fn a_difference_of_a_value_with_itself_is_read_as_a_range() {
    // The interval does not see that both operands are one value: x - x is read as
    // int[-10..=10] here, and near the ends of the word that range leaves it, so the
    // warning is given although the value is 0.
    let small = main_with(
        "  x = if stdin[1] == \"x\" { 0 } else { 10 };\n  y = x - x;\n",
        "y",
    );
    assert_eq!(messages(&small), Vec::<String>::new());
    let large = main_with(
        "  x = if stdin[1] == \"x\" { -9223372036854775807 } else { 9223372036854775807 };\n  \
         y = x - x;\n",
        "y",
    );
    assert_eq!(
        messages(&large),
        ["3:7: `y` widens past a machine word: this `-` of an i64 and an i64 gives a big integer"]
    );
}

#[test]
fn zedc_run_prints_the_warning_and_runs_the_program() {
    let src = main_with("  side = 3037000500;\n  area = side * side;\n", "area");
    let out = zed_tests::step_helpers::l01_19_whole_file_ports::run("widen_area", &src, "", &[]);
    assert_eq!(out.status, 0, "{}", out.stderr);
    assert_eq!(out.stdout, "9223372037000250000\n");
    let first = out.stderr.lines().next().unwrap_or_default();
    assert!(
        first.ends_with(
            "prog.zed:3:10: `area` widens past a machine word: this `*` of an i64 and an i64 \
             gives a big integer"
        ),
        "{}",
        out.stderr
    );
}

/// `n` bindings, each squaring a large literal.
fn many_squares(n: usize) -> String {
    let lines: String = (0..n)
        .map(|i| format!("  a{i} = {} * 3037000500;\n", 3037000500 + i))
        .collect();
    main_with(&lines, "0")
}

/// A chain of `n` bindings, each one more than the last, and one square at its end.
fn long_chain(n: usize) -> String {
    let mut lines = String::from("  x0 = 3037000500;\n");
    for i in 1..=n {
        lines.push_str(&format!("  x{i} = x{} + 1;\n", i - 1));
    }
    lines.push_str(&format!("  sq = x{n} * x{n};\n"));
    main_with(&lines, "sq")
}

/// A unit parsed, resolved and checked, ready for the widening pass.
struct Ready {
    stmts: Vec<zedc::ast::Stmt>,
    res: zedc::resolve::Resolution,
    info: zedc::check::Info,
}

fn ready(text: &str) -> Ready {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    let info = zedc::check::walk::check(&stmts, &res);
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    Ready { stmts, res, info }
}

/// The widening pass alone on units of `n` built by `unit`, each made before timing, with
/// `count` checking what each gives.
fn pass_scales(what: &str, unit: fn(usize) -> String, count: fn(usize, &[zedc::ast::Error])) {
    let n = 1000;
    let (small, large) = (ready(&unit(n)), ready(&unit(scaling::FACTOR * n)));
    let run = |r: &Ready, n: usize| {
        let ws = zedc::check::widen::of(&r.stmts, &r.res, &r.info);
        count(n, &ws);
    };
    scaling::check(what, n, |size| {
        if size == n {
            run(&small, n)
        } else {
            run(&large, size)
        }
    });
}

/// n warnings in a unit of O(n) nodes: the derivations share one mark vector, so a pass that
/// allocated a fresh one per warning would allocate O(n²) bytes, which this test counts.
#[test]
fn many_warnings_scale() {
    assert_eq!(messages(&many_squares(3)).len(), 3);
    pass_scales("n bindings that each widen", many_squares, |n, ws| {
        assert_eq!(ws.len(), n)
    });
}

#[test]
fn a_long_derivation_scales() {
    assert!(warned(&long_chain(3)).contains("`x0` is defined as this expression, 3037000500"));
    pass_scales(
        "a chain of n bindings ending in a widening",
        long_chain,
        |n, ws| {
            assert_eq!(ws.len(), 1);
            assert!(ws[0].notes.len() > 2 * n);
        },
    );
}
