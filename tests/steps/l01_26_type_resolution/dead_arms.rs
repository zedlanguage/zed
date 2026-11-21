//! Row NARROW-dead-arm-constant: a test on a value the text shows, a top-level constant such as
//! `k = 0;` or an expression over such constants, empties it in the arm the test refutes, as a
//! test on a parameter does. DESIGN.md sec:constraints: an arm a narrowing test makes
//! unreachable "adds nothing to the join, and the program is accepted", with a warning only
//! where the derivation reads no static value definition; `k = 0;` is one, so these programs
//! are accepted with no warning. (A test on literals alone, `if 0 > 0`, is owed that warning;
//! no `if` arm has it yet, step L2.12, and its arm is still refused.)

use super::{info, type_errors};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// `f` tests the constant `k = {k}` with `test` and takes `x mod k` in the arm it guards.
fn guarded(k: &str, test: &str) -> String {
    format!("k = {k};\nf(positional x: int) = if {test} {{ x mod k }} else {{ 0 }};\n")
}

/// The refusal of `x mod k` with `k` read as `shown`.
fn refused(shown: &str) -> Vec<String> {
    vec![format!(
        "`mod` takes `m` in int[1..]: `x mod k : {shown}`. [x mod k]"
    )]
}

#[test]
fn a_test_a_constant_fails_makes_its_arm_dead() {
    let f = guarded("0", "k > 0");
    let (checked, _) = info(&f);
    assert_eq!(type_errors(&f), Vec::<String>::new());
    // A static value definition is read: no warning (DESIGN.md sec:constraints).
    assert!(checked.warnings.is_empty(), "{:?}", checked.warnings);
    assert_eq!(value(&format!("{f}y = f(7);\n"), "y"), "0");
}

#[test]
fn a_test_a_constant_passes_keeps_its_arm() {
    let f = guarded("3", "k > 0");
    assert_eq!(type_errors(&f), Vec::<String>::new());
    assert_eq!(value(&format!("{f}y = f(7);\n"), "y"), "1");
}

#[test]
fn a_live_arm_with_a_zero_constant_is_still_refused() {
    // `k >= 0` holds of 0: the arm runs, and `x mod 0` with it.
    assert_eq!(type_errors(&guarded("0", "k >= 0")), refused("0"));
    assert_eq!(type_errors(&guarded("0", "k == 0")), refused("0"));
    assert_eq!(
        type_errors("k = 0;\nf(positional x: int) = x mod k;\n"),
        refused("0")
    );
    // A negative constant under a test it fails is dead too, and refused where it passes.
    assert_eq!(type_errors(&guarded("-2", "k > 0")), Vec::<String>::new());
    assert_eq!(type_errors(&guarded("-2", "k < 0")), refused("-2"));
}

#[test]
fn the_dead_arm_may_be_the_else() {
    let f = "k = 0;\nf(positional x: int) = if k == 0 { 0 } else { x mod k };\n";
    assert_eq!(type_errors(f), Vec::<String>::new());
    assert_eq!(value(&format!("{f}y = f(7);\n"), "y"), "0");
}

#[test]
fn a_constant_through_names_or_operators_and_a_literal() {
    for f in [
        "j = 0;\nk = j;\nf(positional x: int) = if k > 0 { x mod k } else { 0 };\n",
        "k = 2 - 2;\nf(positional x: int) = if k > 0 { x mod k } else { 0 };\n",
        // The same holds at `^`, whose exponent `k - 1` is -1 only in the dead arm.
        "k = 0;\nf(positional x: int) = if k > 0 { 2 ^ (k - 1) } else { 0 };\n",
    ] {
        assert_eq!(type_errors(f), Vec::<String>::new(), "{f}");
    }
}

#[test]
fn an_arm_under_a_test_of_literals_alone_is_still_refused() {
    // A literal is not read in the arm's scope (`Ck::ints_here`): doing so settles the scope,
    // which warns at tests the checker decides elsewhere. DESIGN.md sec:constraints owes this
    // arm the unreachable-arm warning instead (step L2.12).
    let f = "f(positional x: int) = if 0 > 0 { x mod 0 } else { 0 };\n";
    assert_eq!(type_errors(f).len(), 1, "{f}");
}

#[test]
fn a_value_of_an_interval_type_is_narrowed_the_same_way() {
    // A top-level binding with a declared type (`k: int[0..=0] = 0;`) is not supported by this
    // version of zedc; a parameter declared with an interval type is the value of an interval
    // type here, and was narrowed before this row too.
    for f in [
        "f(positional x: int, k: int[0..=0]) = if k > 0 { x mod k } else { 0 };\n",
        "f(positional x: int, k: int[-5..=0]) = if k > 0 { x mod k } else { 0 };\n",
    ] {
        assert_eq!(type_errors(f), Vec::<String>::new(), "{f}");
    }
    let live = "f(positional x: int, k: int[-5..=0]) = if k >= 0 { x mod k } else { 0 };\n";
    assert_eq!(type_errors(live).len(), 1, "{live}");
}

/// `n` constants `k{i} = 0`, then one function whose chain of `n` tests on `d` holds in each
/// arm a dead test of `k{i}` with `x mod k{i}` in it: `n` dead arms, each under `i` tests.
pub(super) fn dead_arm_chain(n: usize) -> String {
    let mut s: String = (0..n).map(|i| format!("k{i} = 0;\n")).collect();
    s += "f(positional x: int, d: int) = { a0 = x; ";
    for i in 1..=n {
        let (p, k) = (i - 1, i - 1);
        s += &format!(
            "a{i} = if d != {i} {{ a{p} + (if k{k} > 0 {{ x mod k{k} }} else {{ 0 }}) }} \
             else {{ a{p} }}; "
        );
    }
    s += &format!("a{n} }};\n");
    s
}

#[test]
fn a_chain_of_dead_arms_gives_no_error() {
    // A small instance of the benchmark `bench::dead_arms::a_chain_of_dead_arms_scales`.
    assert_eq!(type_errors(&dead_arm_chain(3)), Vec::<String>::new());
}
