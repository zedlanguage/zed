//! Step L1.26a: generic integer literals. An integer written with the suffix `n` is the exact
//! integer in whichever numeric carrier its use needs: wherever it joins the class of a
//! parameter (an operand of an operator other than `==` and `!=`, a call's argument, a branch
//! of an `if`, a component of a tuple argument), it removes from the class the carriers that
//! do not hold it exactly, and does not make the class `int`, so `inc(x) = x + 1n` takes
//! `int`, `f64` and `rat` (DESIGN.md L1.26a). Where it meets no carrier it is an int.

mod scaling;

use zed_tests::tokens;
use zedc::lex::lex_fence;

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

const INC: &str = "inc(x) = x + 1n;\n";

#[test]
fn a_generic_literal_leaves_the_parameter_generic() {
    assert_eq!(sig(INC, "inc"), "(x: T) -> T for T in int | f64 | rat");
    // A plain literal makes the class `int`, as before.
    assert_eq!(sig("inc(x) = x + 1;\n", "inc"), "(x: int) -> int");
    // On either side, and under `-` and `*`.
    assert_eq!(
        sig("f(x) = 2n * x - 1n;\n", "f"),
        "(x: T) -> T for T in int | f64 | rat"
    );
    // A plain literal beside a generic one still makes the class `int`.
    assert_eq!(sig("f(x) = x + 1n + 1;\n", "f"), "(x: int) -> int");
}

#[test]
fn a_generic_function_fits_a_slot_of_two_arrows() {
    let both = "both(f: ((x: int) -> int) & ((x: f64) -> f64)) = (f(x: 2), f(x: 2.5));\n";
    let src = format!("{both}{INC}y = both(f: inc);\n");
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(value(&src, "y"), "(3, 3.5)");
    // The plain literal makes `inc` take `int` alone, so it does not fit.
    let plain = format!("{both}inc(x) = x + 1;\ny = both(f: inc);\n");
    assert_eq!(
        type_errors(&plain),
        [
            "`inc` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64)`: it is passed where a function of that type is expected, and its own type does not fit that one [inc]"
        ]
    );
}

#[test]
fn a_program_passes_a_generic_function_to_a_slot_of_two_arrows() {
    // Run by `zedc run`: `inc` fills a parameter that calls it at `int` and at `f64`, and is
    // also called at `rat`.
    let src = format!(
        "both(f: ((x: int) -> int) & ((x: f64) -> f64)) =\n  \
           String(f(x: 2)) ++ \" \" ++ String(f(x: 2.5));\n\
         {INC}\
         main(stdin: Lines) -> (stdout: Lines) {{\n  \
           stdout <- both(f: inc) ++ \" \" ++ String(inc(x: 0.1r));\n\
         }}\n"
    );
    let out = run("l01_26a_two_arrows", &src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "3 3.5 11r/10r\n");
}

#[test]
fn a_generic_function_runs_at_each_carrier() {
    let src = format!("{INC}a = inc(x: 2);\nb = inc(x: 2.5);\nc = inc(x: 0.1r);\n");
    assert_eq!(value(&src, "a"), "3");
    assert_eq!(value(&src, "b"), "3.5");
    // At `rat` the sum is exact: eleven tenths.
    assert_eq!(value(&src, "c"), "11r/10r");
    let src = "half(x) = x / 2n;\nh = half(x: 1r);\nk = half(x: 3.0);\n";
    assert_eq!(sig(src, "half"), "(x: T) -> T for T in f64 | rat");
    assert_eq!(value(src, "h"), "1r/2r");
    assert_eq!(value(src, "k"), "1.5");
}

#[test]
fn a_generic_literal_removes_the_carriers_that_do_not_hold_it() {
    // 2^53 + 1 is not an f64.
    assert_eq!(
        sig("f(x) = x + 9007199254740993n;\n", "f"),
        "(x: T) -> T for T in int | rat"
    );
    assert_eq!(
        sig("f(x) = x + 9007199254740992n;\n", "f"),
        "(x: T) -> T for T in int | f64 | rat"
    );
}

#[test]
fn a_generic_literal_with_nothing_to_follow_is_an_int() {
    assert_eq!(value("y = 1n;\n", "y"), "1");
    assert_eq!(value("y = 1n + 2n;\n", "y"), "3");
    assert_eq!(value("y = 0xFFn;\n", "y"), "255");
    assert_eq!(value("y = 1_000n + 0b101n;\n", "y"), "1005");
    // A carrier the other operand has is taken where the function is checked.
    assert_eq!(value("y = 1.5 + 1n;\n", "y"), "2.5");
    assert_eq!(value("y = 1n + 0.5r;\n", "y"), "3r/2r");
}

#[test]
fn a_generic_literal_at_a_declared_type_reads_as_a_plain_one() {
    assert_eq!(
        sig("f(x: int | f64) = x == 1n;\n", "f"),
        "(x: int | f64) -> bool"
    );
    assert_eq!(value("f(x: f64) = x + 1n;\ny = f(x: 2.0);\n", "y"), "3.0");
    let src = "f(positional x: f64 | rat) = x;\ny = f(1n);\n";
    assert_eq!(
        type_errors(src),
        [
            "`1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
          write the one meant, as `1r` or `1.0` [1n]"
        ]
    );
}

#[test]
fn the_lexer_reads_the_suffix_after_an_integer_only() {
    let toks = |s: &str| tokens::render(&lex_fence(s).unwrap());
    assert_eq!(toks("1n 0xFFn 0b1_0n 1"), "1₍10₎n FF₍16₎n 10₍2₎n 1₍10₎");
    let err = |s: &str| lex_fence(s).unwrap_err().to_string();
    assert_eq!(
        err("1.5n"),
        "the number `1.5n` puts the suffix `n` on a decimal, and only an integer takes `n`: an \
         integer has the same value in every number type, while a decimal has one value in f64 \
         and another in rat. Write `1.5` for a float or `1.5r` for an exact rational."
    );
    assert_eq!(
        err("1e3n"),
        "the number `1e3n` puts the suffix `n` on a decimal, and only an integer takes `n`: an \
         integer has the same value in every number type, while a decimal has one value in f64 \
         and another in rat. Write `1e3` for a float or `1e3r` for an exact rational."
    );
    assert_eq!(
        err("1nx"),
        "the number `1n` runs into the name `x` with nothing between them, and a number must not \
         run into a name. Put an operator or a space between them, as in `1n * x`."
    );
}

/// `scale` multiplies its arguments, and `double` passes it its parameter and a generic
/// literal: the literal joins the class of `x` at the call.
const SCALE: &str = "scale(positional x, positional by) = x * by;\n\
                     double(positional x) = scale(x, 2n);\n";

/// A rectifier: zero below zero, else its argument.
const RELU: &str = "relu(positional x) = if x < 0n { 0n } else { x };\n";

#[test]
fn a_generic_literal_argument_leaves_the_caller_generic() {
    assert_eq!(sig(SCALE, "double"), "(T) -> T for T in int | f64 | rat");
    let src = format!("{SCALE}i = double(21);\nr = double(1.25);\nq = double(1r / 3r);\n");
    assert_eq!(value(&src, "i"), "42");
    assert_eq!(value(&src, "r"), "2.5");
    assert_eq!(value(&src, "q"), "2r/3r");
    // A plain literal makes the caller `int`, as before.
    let plain = "scale(positional x, positional by) = x * by;\n\
                 double(positional x) = scale(x, 2);\n";
    assert_eq!(sig(plain, "double"), "(int) -> int");
}

#[test]
fn a_generic_literal_argument_passes_through_two_functions() {
    // `percent` passes its own parameters on to `scale`; `tenth` gives `percent` a literal
    // first and its parameter second.
    let src = format!(
        "{SCALE}percent(positional p, positional x) = scale(x, p) / 100n;\n\
         tenth(positional x) = percent(10n, x);\n\
         r = tenth(2.5);\nq = tenth(3r);\n"
    );
    assert_eq!(sig(&src, "tenth"), "(T) -> T for T in f64 | rat");
    assert_eq!(value(&src, "r"), "0.25");
    assert_eq!(value(&src, "q"), "3r/10r");
}

#[test]
fn a_generic_literal_branch_takes_the_carrier_of_the_other() {
    assert_eq!(sig(RELU, "relu"), "(T) -> T for T in int | f64 | rat");
    let src = format!("{RELU}i = relu(-2);\nr = relu(-2.5);\ns = relu(1.5);\nq = relu(-1r);\n");
    assert_eq!(value(&src, "i"), "0");
    assert_eq!(value(&src, "r"), "0.0");
    assert_eq!(value(&src, "s"), "1.5");
    assert_eq!(value(&src, "q"), "0r");
    // In the `else` branch, under `-`, and as a sum of generic literals.
    let src = "floor(positional x) = if x > 0n { x } else { -1n };\n\
               two(positional x) = if x > 0n { x } else { 1n + 1n };\n\
               a = floor(-0.5);\nb = two(-0.5);\nc = two(-3);\n";
    assert_eq!(sig(src, "floor"), "(T) -> T for T in int | f64 | rat");
    assert_eq!(sig(src, "two"), "(T) -> T for T in int | f64 | rat");
    assert_eq!(value(src, "a"), "-1.0");
    assert_eq!(value(src, "b"), "2.0");
    assert_eq!(value(src, "c"), "2");
    // A plain literal makes the class `int`, as before.
    let plain = "relu(positional x) = if x < 0 { 0 } else { x };\n";
    assert_eq!(sig(plain, "relu"), "(int) -> int");
}

#[test]
fn a_sum_of_generic_literals_takes_the_carrier_it_meets() {
    let src = "f(positional x) = x * (2n + 1n);\ni = f(2);\nr = f(0.5);\n";
    assert_eq!(sig(src, "f"), "(T) -> T for T in int | f64 | rat");
    assert_eq!(value(src, "i"), "6");
    assert_eq!(value(src, "r"), "1.5");
    // Where it meets no carrier, it is an int, inside a function or outside.
    let src = "three() = 1n + 2n;\nt = three();\nmain = 1n + 1n;\n";
    assert_eq!(sig(src, "three"), "() -> int");
    assert_eq!(value(src, "t"), "3");
    assert_eq!(value(src, "main"), "2");
}

#[test]
fn a_quotient_of_generic_literals_is_an_f64_where_nothing_decides() {
    // `/` is not defined on int, so where nothing decides, `1n / 2n` is an f64. A plain
    // `1 / 2` is rejected: its literals are ints, and take no other carrier.
    let src = "half() = 1n / 2n;\nh = half();\nmain = 1n / 2n;\n";
    assert_eq!(sig(src, "half"), "() -> f64");
    assert_eq!(value(src, "h"), "0.5");
    assert_eq!(value(src, "main"), "0.5");
    assert_eq!(
        type_errors("main = 1 / 2;\n"),
        [
            "`1` is an int where `f64` is expected; a literal takes no other carrier; write \
             `1.0` or `1n` [1]"
        ]
    );
    // Where it meets a class, it takes the class's carrier, of f64 and rat.
    let src = "f(positional x) = x * (1n / 2n);\nr = f(3.0);\nq = f(3r);\n";
    assert_eq!(sig(src, "f"), "(T) -> T for T in f64 | rat");
    assert_eq!(value(src, "r"), "1.5");
    assert_eq!(value(src, "q"), "3r/2r");
}

#[test]
fn a_generic_literal_in_a_tuple_argument_joins_the_component_it_meets() {
    let src = "sumPair(positional p) = p[0] + p[1];\n\
               next(positional x) = sumPair((x, 1n));\n\
               i = next(2);\nr = next(2.5);\n";
    assert_eq!(sig(src, "next"), "(T) -> T for T in int | f64 | rat");
    assert_eq!(value(src, "i"), "3");
    assert_eq!(value(src, "r"), "3.5");
    // A plain literal makes the caller `int`, as before.
    let plain = "sumPair(positional p) = p[0] + p[1];\n\
                 next(positional x) = sumPair((x, 1));\n";
    assert_eq!(sig(plain, "next"), "(int) -> int");
}

#[test]
fn a_generic_literal_under_equality_stays_a_plain_one() {
    // 2^53 + 1 is not an f64: a generic reading would take f64 from the class of `x`, and the
    // comparison reads the literal as an int instead, which no f64 equals.
    let src = "f(positional x) = x == 9007199254740993n;\n\
               i = f(9007199254740993);\nr = f(9007199254740992.0);\n";
    assert_eq!(sig(src, "f"), "(_) -> bool");
    assert_eq!(value(src, "i"), "true");
    assert_eq!(value(src, "r"), "false");
}

#[test]
fn a_program_runs_generic_literal_arguments_and_branches() {
    // Run by `zedc run`: each function is called at int, f64 and rat.
    let src = format!(
        "{SCALE}{RELU}\
         sumPair(positional p) = p[0] + p[1];\n\
         next(positional x) = sumPair((x, 1n));\n\
         main(stdin: Lines) -> (stdout: Lines) {{\n  \
           stdout <- String(double(21)) ++ \" \" ++ String(double(1.25)) ++ \" \" ++ \
         String(relu(-2.5)) ++ \" \" ++ String(relu(-1r)) ++ \" \" ++ String(next(0.5r)) ++ \" \" ++ \
         String(next(2));\n\
         }}\n"
    );
    let out = run("l01_26a_joins", &src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    assert_eq!(out.stdout, "42 2.5 0.0 0r 3r/2r 3\n");
}

/// The step's unit given a `main`, a rejected program, and a generic function called at a
/// parameter of declared type.
fn units() -> Vec<String> {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let unit = dir.join("steps/l01_26a_generic_literals/zed/generic.zed");
    vec![
        std::fs::read_to_string(unit).unwrap() + "main() = inc(mask);\n",
        "f(positional x: f64 | rat) = x;\nmain() = f(1n);\n".into(),
        format!("{INC}g(positional y: f64) = inc(x: y) * 2n;\nmain() = g(1.5);\n"),
        format!("{SCALE}{RELU}main() = double(relu(-1.5));\n"),
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
    assert_eq!(
        alone[1].as_deref().and_then(|a| a.lines().next()),
        Some(
            "2:12: `1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and \
             f64; write the one meant, as `1r` or `1.0`"
        )
    );
    assert_eq!(alone[2], None);
    assert_eq!(alone[3], None);
}
