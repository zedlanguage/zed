//! Steps L1.26a and L1.26b: a literal is notation for a number, and it takes the carrier of
//! its use. An integer literal is that integer in whichever numeric carrier its use needs and
//! holds it exactly, and is `int` where nothing fixes its carrier; a decimal literal takes a
//! float format or `rat`, never `int`, and is rejected where nothing fixes its carrier, as is
//! a `/` of integer literals alone (DESIGN.md L1.26a, L1.26b, sec:domains).
//!
//! The carriers here are `int`, `f64` and `rat`: `bf16`, `f16` and `f32` join the bounds of
//! these signatures with item FLOAT-f32.

mod call_arguments;
mod design_menus;
mod fixes;
mod lazy_carrier;
mod lit_branch_ops;
mod lit_branches;
mod parts_type;
mod scaling;
mod spelling;
mod tuple_rest;
mod tuples;
mod written;

use zed_tests::tokens;
use zedc::lex::lex_fence;

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

const INC: &str = "inc(x) = x + 1;\n";

/// `scale` multiplies its arguments; `double` passes it its parameter and a literal, which
/// joins the class of `x` at the call; `percent` passes its own parameters on, and `tenth`
/// gives `percent` a literal first and its parameter second.
const SCALE: &str = "scale(x, by) = x * by;\n\
                     double(x) = scale(x: x, by: 2);\n\
                     percent(p, x) = scale(x: x, by: p) / 100;\n\
                     tenth(x) = percent(p: 10, x: x);\n";

/// A rectifier, zero below zero; and the sum of a pair, given a parameter and a literal.
const RELU_NEXT: &str = "relu(x) = if x < 0 { 0 } else { x };\n\
                         sumPair(p) = p[0] + p[1];\n\
                         next(x) = sumPair(p: (x, 1));\n";

const T: &str = "(x: T) -> T for T in int | f64 | rat";
const T_NO_INT: &str = "(x: T) -> T for T in f64 | rat";

#[test]
fn an_integer_literal_leaves_the_parameter_generic() {
    assert_eq!(sig(INC, "inc"), T);
    assert_eq!(sig("inc(x) = x + 1 + 1;\n", "inc"), T);
    assert_eq!(sig("f(x) = 2 * x - 1;\n", "f"), T);
    assert_eq!(sig("half(x) = x / 2;\n", "half"), T_NO_INT);
}

#[test]
fn a_generic_function_fits_a_slot_of_two_arrows() {
    let both = "both(f: ((x: int) -> int) & ((x: f64) -> f64)) = (f(x: 2), f(x: 2.5f64));\n";
    let src = format!("{both}{INC}y = both(f: inc);\n");
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(value(&src, "y"), "(3, 3.5)");
}

#[test]
fn a_generic_function_runs_at_each_carrier() {
    let src = format!("{INC}a = inc(x: 2);\nb = inc(x: 2.5f64);\nc = inc(x: 0.1r);\n");
    assert_eq!(value(&src, "a"), "3");
    assert_eq!(value(&src, "b"), "3.5");
    // At `rat` the sum is exact: eleven tenths.
    assert_eq!(value(&src, "c"), "11r/10r");
    // A decimal argument that nothing gives a carrier is rejected at the decimal.
    assert_eq!(
        type_errors(&format!("{INC}y = inc(x: 2.5);\n")),
        [
            "the literal `2.5` is a decimal, and nothing here gives it a carrier; a decimal \
             literal takes the carrier of its use, never `int`, and Zed does not choose one for \
             it\n  fixes, each checked here:\n    y = inc(x: 2.5f64);    the literal is then the f64 \
             2.5\n    y = inc(x: 2.5r);      the literal is then exactly 2.5, a rat [2.5]"
        ]
    );
}

#[test]
fn a_program_passes_a_generic_function_to_a_slot_of_two_arrows() {
    // Run by `zedc run`: `inc` fills a parameter that calls it at `int` and at `f64`, and is
    // also called at `rat`.
    let src = format!(
        "both(f: ((x: int) -> int) & ((x: f64) -> f64)) =\n  \
           String(f(x: 2)) ++ \" \" ++ String(f(x: 2.5f64));\n\
         {INC}\
         main(m: MainArgs) {{\n  \
           m.stdout <- both(f: inc) ++ \" \" ++ String(inc(x: 0.1r));\n\
         }}\n"
    );
    let out = run("l01_26a_two_arrows", &src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "3 3.5 11r/10r\n");
}

#[test]
fn an_integer_literal_removes_the_carriers_that_do_not_hold_it() {
    // 2^53 + 1 has no f64; 2^24 + 1, 2^53, 2049 and 257 have one.
    let cases = [
        ("9007199254740993", "(x: T) -> T for T in int | rat"),
        ("16777217", T),
        ("9007199254740992", T),
        ("2049", T),
        ("257", T),
    ];
    for (k, want) in cases {
        assert_eq!(sig(&format!("f(x) = x + {k};\n"), "f"), want, "{k}");
    }
}

#[test]
fn literals_that_nothing_else_fixes() {
    assert_eq!(value("y = 1;\n", "y"), "1");
    assert_eq!(value("y = 0xFF;\n", "y"), "255");
    assert_eq!(value("y = 1.5f64 + 1;\n", "y"), "2.5");
    assert_eq!(value("y = 1 + 0.5r;\n", "y"), "3r/2r");
    assert_eq!(value("y = 1_000 + 0b101;\n", "y"), "1005");
    let src = "f(x: f64) = x + 1;\ny = f(x: 2.0f64);\n";
    assert_eq!(sig(src, "f"), "(x: f64) -> f64");
    assert_eq!(value(src, "y"), "3.0");
}

#[test]
fn a_literal_argument_leaves_the_caller_generic() {
    assert_eq!(sig(SCALE, "double"), T);
    assert_eq!(sig(SCALE, "tenth"), T_NO_INT);
    let src = format!(
        "{SCALE}a = double(x: 21);\nb = double(x: 1.25f64);\nc = tenth(x: 2.5f64);\n\
         q = tenth(x: 3r);\n"
    );
    assert_eq!(value(&src, "a"), "42");
    assert_eq!(value(&src, "b"), "2.5");
    assert_eq!(value(&src, "c"), "0.25");
    assert_eq!(value(&src, "q"), "3r/10r");
}

#[test]
fn a_literal_branch_and_a_literal_component_take_the_carrier_of_the_parameter() {
    assert_eq!(sig(RELU_NEXT, "relu"), T);
    assert_eq!(sig(RELU_NEXT, "next"), T);
    let src = format!(
        "{RELU_NEXT}d = relu(x: -2.5f64);\ne = relu(x: -1r);\nf = next(x: 2.5f64);\n\
         i = next(x: 2);\n"
    );
    assert_eq!(value(&src, "d"), "0.0");
    assert_eq!(value(&src, "e"), "0r");
    assert_eq!(value(&src, "f"), "3.5");
    assert_eq!(value(&src, "i"), "3");
    // In the `else` branch, under `-`, and as a sum of literals.
    let src = "floor(x) = if x > 0 { x } else { -1 };\n\
               two(x) = if x > 0 { x } else { 1 + 1 };\n\
               a = floor(x: -0.5f64);\nb = two(x: -0.5f64);\nc = two(x: -3);\n";
    assert_eq!(sig(src, "floor"), T);
    assert_eq!(sig(src, "two"), T);
    assert_eq!(value(src, "a"), "-1.0");
    assert_eq!(value(src, "b"), "2.0");
    assert_eq!(value(src, "c"), "2");
}

#[test]
fn a_program_runs_literal_arguments_branches_and_components() {
    // Run by `zedc run`: each function is called at int, f64 and rat.
    let src = format!(
        "{SCALE}{RELU_NEXT}\
         main(m: MainArgs) {{\n  \
           m.stdout <- String(double(x: 21)) ++ \" \" ++ String(double(x: 1.25f64)) ++ \" \" ++ \
         String(tenth(x: 2.5f64)) ++ \" \" ++ String(relu(x: -2.5f64)) ++ \" \" ++ \
         String(relu(x: -1r)) ++ \" \" ++ String(next(x: 2.5f64));\n\
         }}\n"
    );
    let out = run("l01_26a_joins", &src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "42 2.5 0.25 0.0 0r 3.5\n");
}

#[test]
fn an_operation_on_literals_alone_takes_the_carrier_it_meets() {
    let src = "g(x) = x * (2 + 1);\ny = g(x: 0.5f64);\n";
    assert_eq!(sig(src, "g"), T);
    assert_eq!(value(src, "y"), "1.5");
    // Where it meets no carrier, an operation on integer literals is an int.
    let src = "three() = 1 + 2;\ny = 1 + 2;\nmain = 1 + 1;\n";
    assert_eq!(sig(src, "three"), "() -> int");
    assert_eq!(value(src, "y"), "3");
    assert_eq!(value(src, "main"), "2");
    // `1 / 2` at a class of f64 or rat takes its carrier.
    let src = "g(x) = x * (1 / 2);\na = g(x: 3.0f64);\nb = g(x: 3r);\n";
    assert_eq!(sig(src, "g"), T_NO_INT);
    assert_eq!(value(src, "a"), "1.5");
    assert_eq!(value(src, "b"), "3r/2r");
}

#[test]
fn literals_that_nothing_fixes_and_that_no_int_holds_are_rejected_with_a_menu() {
    assert_eq!(
        type_errors("half = 1 / 2;\n"),
        [
            "`half = 1 / 2` divides two integer literals, and nothing here gives them a \
             carrier; `/` has no arrow at `int`, and Zed does not choose `f64` or `rat` for \
             it\n  fixes, each checked here:\n    half = 1.0f64 / 2;    half is 0.5\n    \
             half = 1r / 2;        half is 1r/2r\n    half = f64(1) / 2;    half is 0.5 [1 / 2]"
        ]
    );
    assert_eq!(
        type_errors("y = 0.1;\n"),
        [
            "the literal `0.1` is a decimal, and nothing here gives it a carrier; a decimal \
             literal takes the carrier of its use, never `int`, and Zed does not choose one for \
             it\n  fixes, each checked here:\n    y = 0.1f64;    y is 0.1\n    y = 0.1r;      y is \
             1r/10r [0.1]"
        ]
    );
    assert_eq!(
        type_errors("y = 1 == 1.0;\n"),
        [
            "the literal `1.0` is a decimal, and nothing here gives it a carrier; a decimal \
             literal takes the carrier of its use, never `int`, and Zed does not choose one for \
             it\n  fixes, each checked here:\n    y = 1 == 1.0f64;    y is true\n    y = 1 == 1.0r;      \
             y is true [1.0]"
        ]
    );
    // The fixes the menus name each check.
    assert_eq!(value("half = f64(1) / 2;\n", "half"), "0.5");
    assert_eq!(value("half = 1.0f64 / 2;\n", "half"), "0.5");
    assert_eq!(value("y = 0.1f64;\n", "y"), "0.1");
    assert_eq!(value("y = 0.1r;\n", "y"), "1r/10r");
    assert_eq!(value("y = 1 == 1.0f64;\n", "y"), "true");
    assert_eq!(value("y = 1 == 1.0r;\n", "y"), "true");
}

#[test]
fn a_literal_at_one_declared_carrier_takes_it_exactly_or_not_at_all() {
    let id = |t: &str, k: &str| format!("id(positional v: {t}) = v;\nx = id({k});\n");
    assert_eq!(value(&id("f64", "1"), "x"), "1.0");
    assert_eq!(value(&id("f64", "0.1"), "x"), "0.1");
    assert_eq!(value(&id("rat", "0.1"), "x"), "1r/10r");
    assert_eq!(
        type_errors(&id("f64", "9007199254740993")),
        [
            "the literal `9007199254740993` has no exact `f64`, and `f64` is expected here; an \
             integer literal takes a carrier only where it is exact\n  fixes, each checked here:\n    \
             x = id(9007199254740992);    the literal is then 9007199254740992.0, the nearer \
             f64 by ties to even [9007199254740993]"
        ]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x;\ny = f(1);\n"),
        [
            "the literal `1` can be a `rat` or an `f64` at `rat | f64`, and nothing here \
             chooses one\n  T1 stands for a part written more than once:\n    type T1 = rat | \
             f64;\n  fixes, each checked here:\n    y = f(1r);        the literal is then \
             exactly 1, a rat\n    y = f(1.0f64);    the literal is then the f64 1.0 [1]"
        ]
    );
}

#[test]
fn a_literal_compared_with_a_class_leaves_its_carriers() {
    let src = "isBig(x) = x == 9007199254740993;\n\
               i = isBig(x: 9007199254740993);\ny = isBig(x: 9007199254740992.0f64);\n";
    assert_eq!(sig(src, "isBig"), "(x: _) -> bool");
    assert_eq!(value(src, "i"), "true");
    assert_eq!(value(src, "y"), "false");
}

#[test]
fn a_literal_survives_an_if() {
    // DESIGN.md step L1.26a writes this type `2 | 1`, the branches in the order written;
    // zedc prints the values in ascending order, `1 | 2`. DESIGN states no order for the
    // members of a printed union, so this is open (items LIT-if-print, LIT-print-order).
    assert_eq!(
        sig("g(positional c: bool) = if c { 2 } else { 1 };\n", "g"),
        "(bool) -> 1 | 2"
    );
    assert_eq!(
        sig("g(positional c: bool) = if c { 1 } else { 2.5 };\n", "g"),
        "(bool) -> 1 | 2.5"
    );
    assert_eq!(
        sig(
            "g(positional c: bool, positional x: f64) = if c { x } else { 1 };\n",
            "g"
        ),
        "(bool, f64) -> 1 | f64"
    );
}

#[test]
fn literal_branches_take_int_where_the_result_is_used_at_int() {
    // DESIGN.md step L1.26a: where both branches are literals "each keeps its own value and
    // is fixed where the result is used". Used at a parameter of type `int`, both are `int`.
    let src = "g(positional c: bool) = if c { 2 } else { 1 };\n\
               h(positional z: int) = z;\n\
               f(positional c: bool) = h(g(c));\n\
               a = f(true);\nb = f(false);\nc = h(if true { 2 } else { 1 });\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool) -> int");
    assert_eq!(value(src, "a"), "2");
    assert_eq!(value(src, "b"), "1");
    assert_eq!(value(src, "c"), "2");
}

#[test]
fn literal_branches_take_f64_where_the_result_is_used_at_f64() {
    // Through a call, `h(g(c))`: the result of `g` lists literal values alone, so it is read
    // at the carrier of the parameter (item LIT-branch-op-value, tested in lit_branch_ops).
    // DESIGN.md step L1.26a: "`z: f64 = if c { 2 } else { 1 }` and `z: f64 = g(c)` read both
    // branches at `f64`". A declared binding is layer L10, so the result is used here at a
    // parameter of type `f64`, which fixes the carrier the same way (sec:type_resolution rule
    // 2, and step L1.26: "A literal at a declared type takes the one numeric carrier of the
    // type it can take").
    let src = "g(positional c: bool) = if c { 2 } else { 1 };\n\
               h(positional z: f64) = z;\n\
               f(positional c: bool) = h(g(c));\n\
               a = f(true);\nb = f(false);\nc = h(if true { 2 } else { 1 });\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool) -> f64");
    assert_eq!(value(src, "a"), "2.0");
    assert_eq!(value(src, "b"), "1.0");
    assert_eq!(value(src, "c"), "2.0");
}

#[test]
#[ignore = "open: a binding with a declared type is layer L10, and zedc refuses it at L1"]
fn a_declared_binding_reads_literal_branches_at_its_carrier() {
    // DESIGN.md step L1.26a, word for word: `z: f64 = if c { 2 } else { 1 }` reads both
    // branches at `f64`.
    let src = "g(positional c: bool) = { z: f64 = if c { 2 } else { 1 }; z };\ny = g(true);\n";
    assert_eq!(sig(src, "g"), "(bool) -> f64");
    assert_eq!(value(src, "y"), "2.0");
}

#[test]
fn an_operation_on_literals_keeps_its_value_in_an_if() {
    // DESIGN.md step L1.26a: "an operation on literals alone keeps its value in an `if`, so
    // `if c { 1 + 1 } else { 1.5 }` is `2 | 1.5`".
    let src = "g(positional c: bool) = if c { 1 + 1 } else { 1.5 };\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    // The order zedc prints today, `int` values before `f64` ones. The author's answer B to
    // A92 (2026-11-11) puts numeric literals ascending, `1.5 | 2`; ledger item LIT-print-order
    // changes the printer and this pin with it.
    assert_eq!(sig(src, "g"), "(bool) -> 2 | 1.5");
}

#[test]
fn a_literal_in_a_returned_tuple_is_an_int() {
    // DESIGN.md step L1.26a: an integer literal is an `int` "as a component of a returned
    // tuple, so `f(x) = (x, 1)` is `(x: _) -> (_, 1)`".
    let src = "f(x) = (x, 1);\n";
    assert_eq!(sig(src, "f"), "(x: _) -> (_, 1)");
    let run = format!("{src}a = f(x: 2.5f64);\nb = f(x: \"s\");\n");
    assert_eq!(value(&run, "a"), "(2.5, 1)");
    assert_eq!(value(&run, "b"), "(\"s\", 1)");
}

#[test]
fn a_decimal_literal_takes_a_float_format_or_rat_and_never_int() {
    // `twice(x: int) = x * 2.0;` alone in a file: the message of sec:diagnostics, whose
    // menu item MSG-literal-fixes writes as source lines with their values.
    assert_eq!(
        type_errors("twice(x: int) = x * 2.0;\n"),
        [
            "the literal `2.0` is a decimal, and `*` expects `int`, the carrier of `x`; a \
             decimal literal is never an `int`\n  fixes, each checked here:\n    \
             twice(x: int) = x * 2;           2 takes the int of x\n    \
             twice(x: int) = f64(x) * 2.0;    x is cast to f64, and `*` takes two f64\n    \
             twice(x: int) = rat(x) * 2.0;    x is cast to rat, and `*` takes two rat [2.0]"
        ]
    );
    assert_eq!(
        sig("twice(x: f64) = x * 2.0;\n", "twice"),
        "(x: f64) -> f64"
    );
    let src = "twice(x: rat) = x * 2.0;\ny = twice(x: 3r);\n";
    assert_eq!(sig(src, "twice"), "(x: rat) -> rat");
    assert_eq!(value(src, "y"), "6r");
    assert_eq!(sig("half(x) = x * 0.5;\n", "half"), T_NO_INT);
    assert_eq!(value("y = 0.1f64;\n", "y"), "0.1");
}

#[test]
fn the_lexer_reads_no_suffix_on_an_integer() {
    let toks = |s: &str| tokens::render(&lex_fence(s).unwrap());
    assert_eq!(toks("1 0xFF 0b1_0"), "1₍10₎ FF₍16₎ 10₍2₎");
    let err = |s: &str| lex_fence(s).unwrap_err().to_string();
    assert_eq!(
        err("1n"),
        "the number `1` runs into the name `n` with nothing between them, and a number must not \
         run into a name. Put an operator or a space between them, as in `1 * n`."
    );
    assert_eq!(
        err("1nx"),
        "the number `1` runs into the name `nx` with nothing between them, and a number must \
         not run into a name. Put an operator or a space between them, as in `1 * nx`."
    );
    assert_eq!(
        err("1f64"),
        "`1f64` is the integer `1` with the format suffix `f64`, and only a decimal literal \
         takes a format suffix. Write `1.0f64` for an `f64`, or `1`, which takes the carrier of \
         its use."
    );
    assert_eq!(
        err("2bf16"),
        "`2bf16` is the integer `2` with the format suffix `bf16`, and only a decimal literal \
         takes a format suffix. Write `2.0bf16` for a `bf16`, or `2`, which takes the carrier \
         of its use."
    );
}

/// The step's unit given a `main` that writes a value, rejected programs, and a generic
/// function called at a parameter of declared type.
fn units() -> Vec<String> {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let unit = dir.join("steps/l01_26a_generic_literals/zed/generic.zed");
    vec![
        std::fs::read_to_string(unit).unwrap()
            + "main(m: MainArgs) { m.stdout <- String(inc(mask)); }\n",
        "f(positional x: f64 | rat) = x;\nmain(m: MainArgs) { m.stdout <- String(f(1)); }\n".into(),
        format!(
            "{INC}g(positional y: f64) = inc(x: y) * 2;\nmain(m: MainArgs) {{ m.stdout <- String(g(1.5)); }}\n"
        ),
        format!(
            "{SCALE}{RELU_NEXT}main(m: MainArgs) {{ m.stdout <- String(double(x: relu(x: -1.5f64))); }}\n"
        ),
        "main = 0.1;\n".into(),
    ]
}

#[test]
fn batch_and_single_file_checking_agree() {
    let answer = |src: &str| zedc::run::load(src.as_bytes()).err();
    let units = units();
    let alone: Vec<Option<String>> = units
        .iter()
        .map(|src| {
            let src = src.clone();
            std::thread::spawn(move || answer(&src)).join().unwrap()
        })
        .collect();
    let batch: Vec<Option<String>> = units.iter().map(|s| answer(s)).collect();
    let mut reversed: Vec<Option<String>> = units.iter().rev().map(|s| answer(s)).collect();
    reversed.reverse();
    assert_eq!(alone, batch);
    assert_eq!(alone, reversed);
    assert_eq!(alone[0], None);
    let first = |i: usize| alone[i].as_deref().and_then(|a| a.lines().next());
    assert_eq!(
        first(1),
        Some(
            "2:42: the literal `1` can be a `rat` or an `f64` at `rat | f64`, and nothing here \
             chooses one"
        )
    );
    assert_eq!(alone[2], None);
    assert_eq!(alone[3], None);
    assert!(
        first(4).is_some_and(|l| l.starts_with("1:8: the literal `0.1` is a decimal")),
        "{:?}",
        alone[4]
    );
}
