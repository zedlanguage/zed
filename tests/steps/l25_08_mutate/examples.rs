//! The examples of DESIGN.md L25.8, as programs a person would write.

use super::report;

const FARES: &str = include_str!("zed/fares.zed");

#[test]
fn the_fares_report() {
    assert_eq!(
        report(FARES),
        [
            "10:51: skipped: `+` replaced by `-` in `fare` at .0.1.1: the build stage gives the \
             definition the original's term",
            "6:31: undetected: `<` replaced by `<=` in `isMinor` at .0: every row that reaches \
             it passes",
            "6:33: undetected: `18` replaced by `17` in `isMinor` at .0.1: every row that \
             reaches it passes",
            "6:33: undetected: `18` replaced by `19` in `isMinor` at .0.1: every row that \
             reaches it passes",
            "15 mutants: 11 detected, 3 undetected, 1 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_boundary_the_table_checks_detects_its_mutants() {
    // `age <= 12` replaced by `age < 12` gives `12 -> false`; 12 replaced by 11 or 13 moves
    // the boundary past a row.
    let unit = "isChild(positional age) = age <= 12 test { 12 -> true, 13 -> false, 0 -> true }\n";
    assert_eq!(
        report(unit),
        ["3 mutants: 3 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_mutant_the_build_stage_proves_equal_is_skipped() {
    // `2 + 0` and `2 - 0` are both built to 2; the other mutants change the factor.
    let unit = "scale(positional x) = x * (2 + 0) test { 3 -> 6 }\n";
    assert_eq!(
        report(unit),
        [
            "1:30: skipped: `+` replaced by `-` in `scale` at .0.1: the build stage gives the \
             definition the original's term",
            "5 mutants: 4 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_table_that_omits_the_boundary_leaves_its_mutants_undetected() {
    let unit = "isMinor(positional age) = age < 18 test { 5 -> true, 40 -> false }\n";
    assert_eq!(
        report(unit),
        [
            "1:31: undetected: `<` replaced by `<=` in `isMinor` at .0: every row that reaches \
             it passes",
            "1:33: undetected: `18` replaced by `17` in `isMinor` at .0.1: every row that \
             reaches it passes",
            "1:33: undetected: `18` replaced by `19` in `isMinor` at .0.1: every row that \
             reaches it passes",
            "3 mutants: 0 detected, 3 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_definition_no_table_reaches_has_its_mutants_undetected() {
    let unit = "limit = 10;\ndouble(positional x) = x * 2 test { 3 -> 6 }\n";
    assert_eq!(
        report(unit),
        [
            "1:9: undetected: `10` replaced by `9` in `limit` at .: no table reaches the \
             definition",
            "1:9: undetected: `10` replaced by `11` in `limit` at .: no table reaches the \
             definition",
            "4 mutants: 2 detected, 2 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_multiplication_becomes_a_division_only_where_division_is_defined() {
    // On `rat` operands `/` is defined: `x / 0.5r` gives 8r, not 2r. On `int` operands it is
    // not, so `n * 2` has only its constant's mutants.
    let half = "half(positional x: rat) = x * 0.5r test { 4r -> 2r }\n";
    assert_eq!(
        report(half),
        ["1 mutants: 1 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    let double = "double(positional n: int) = n * 2 test { 3 -> 6 }\n";
    assert_eq!(
        report(double),
        ["2 mutants: 2 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_whole_number_on_rat_has_its_mutants_at_rat() {
    // The generic `2n` takes `rat`, so `price * 2n` is a `rat` product, on which `/` is defined,
    // and the constant's neighbors are the `rat` values 1 and 3. A table that tries only a price of
    // zero detects none of them; one that tries 3 detects all three.
    let only_zero = "doubled(positional price: rat) = price * 2 test { 0r -> 0r }\n";
    assert_eq!(
        report(only_zero),
        [
            "1:40: undetected: `*` replaced by `/` in `doubled` at .0: every row that reaches \
             it passes",
            "1:42: undetected: `2r` replaced by `1r` in `doubled` at .0.1: every row that \
             reaches it passes",
            "1:42: undetected: `2r` replaced by `3r` in `doubled` at .0.1: every row that \
             reaches it passes",
            "3 mutants: 0 detected, 3 undetected, 0 skipped, 0 not run",
        ]
    );
    let three = "doubled(positional price: rat) = price * 2 test { 3r -> 6r }\n";
    assert_eq!(
        report(three),
        ["3 mutants: 3 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // On `f64` too `/` is defined, and the generic constant takes `f64`.
    let scaled = "scaled(positional x: f64) = x * 4 test { 2.0 -> 8.0 }\n";
    assert_eq!(
        report(scaled),
        ["3 mutants: 3 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_row_of_main_runs_the_mutant_wave() {
    // `c * 9 div 5 + 32`: each mutant changes what the wave writes for 21 degrees.
    let unit = "\
fahrenheit(positional c) = c * 9 div 5 + 32;

main(stdin: Lines) -> (stdout: Lines) {
  stdout <- \"${fahrenheit(int(trim(stdin[1] else \"\")))}F\" else \"not a number\";
}
test { \"21\\n\" -> \"69F\\n\" }
";
    assert_eq!(
        report(unit),
        ["9 mutants: 9 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_mutant_whose_row_may_not_end_is_not_run() {
    // Replacing 0 by -1 sends `guard(0)` to `w(w)`, which never ends: such a row runs only
    // when its form shows that it ends (`stage::ends`), and `w` calls through a parameter.
    let unit = "\
w(positional f) = f(f);
guard(positional x) = if x > 0 { w(w) } else { x } test { 0 -> 0 }
";
    assert_eq!(
        report(unit),
        [
            "2:28: not run: `>` replaced by `>=` in `guard` at .0.0: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "2:30: not run: `0` replaced by `-1` in `guard` at .0.0.1: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "2:30: not run: `0` replaced by `1` in `guard` at .0.0.1: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "3 mutants: 0 detected, 0 undetected, 0 skipped, 3 not run",
        ]
    );
}

#[test]
fn a_default_constant_has_a_mutant_at_each_call_that_uses_it() {
    // A literal default is copied into each call that leaves its argument out, so each copy
    // is a node of the calling definition, at the default's place in the source. No table
    // reaches these, so each is reported.
    let unit = "\
pad(positional n, by = 1) = n + by;
once(positional n) = pad(n);
again(positional n) = pad(n);
";
    assert_eq!(
        report(unit),
        [
            "1:24: undetected: `1` replaced by `0` in `again` at .0.1.0: no table reaches the \
             definition",
            "1:24: undetected: `1` replaced by `2` in `again` at .0.1.0: no table reaches the \
             definition",
            "1:24: undetected: `1` replaced by `0` in `once` at .0.1.0: no table reaches the \
             definition",
            "1:24: undetected: `1` replaced by `2` in `once` at .0.1.0: no table reaches the \
             definition",
            "1:31: undetected: `+` replaced by `-` in `pad` at .0: no table reaches the \
             definition",
            "5 mutants: 0 detected, 5 undetected, 0 skipped, 0 not run",
        ]
    );
}
