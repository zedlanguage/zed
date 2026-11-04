//! Step L1.26a: generic integer literals. An integer written with the suffix `n` is the exact
//! integer in whichever numeric carrier its use needs: as an operand of an operator, it removes
//! from the class of the other operand the carriers that do not hold it exactly, and does not
//! make the class `int`, so `inc(x) = x + 1n` takes `int`, `f64` and `rat` (DESIGN.md L1.26a).

mod scaling;

use zed_tests::tokens;
use zedc::lex::lex_fence;

use crate::l01_16_elaboration::value;
use crate::l01_19_whole_file_ports::run;
use crate::l01_26_type_resolution::{sig, type_errors};

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
        ["`inc` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64)` [inc]"]
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
        "malformed number: only an integer takes `n`: write `1.5` for a float or `1.5r` for an \
         exact rational; a decimal has a different value in f64 and in rat, an integer the same \
         in every carrier"
    );
    assert_eq!(
        err("1e3n"),
        "malformed number: only an integer takes `n`: write `1e3` for a float or `1e3r` for an \
         exact rational; a decimal has a different value in f64 and in rat, an integer the same \
         in every carrier"
    );
    assert_eq!(
        err("1nx"),
        "malformed number: a number must not run into a name: `x`"
    );
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
}
