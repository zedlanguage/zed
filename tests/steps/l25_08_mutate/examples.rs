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
            "6:31: undetected: `<` replaced by `<=` in `isMinor` at .0.1: every row that reaches \
             it passes",
            "6:33: undetected: `18` replaced by `17` in `isMinor` at .0.1.1.4: every row that \
             reaches it passes",
            "6:33: undetected: `18` replaced by `19` in `isMinor` at .0.1.1.4: every row that \
             reaches it passes",
            "21 mutants: 17 detected, 3 undetected, 1 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_boundary_the_table_checks_detects_its_mutants() {
    // `age <= 12` replaced by `age < 12` gives `12 -> false`, and by `age >= 12` (H3: `age` is
    // generic, so not `int` alone) gives `0 -> false`; 12 replaced by 11 or 13 moves
    // the boundary past a row.
    let unit = "isChild(positional age) = age <= 12 test { 12 -> true, 13 -> false, 0 -> true }\n";
    assert_eq!(
        report(unit),
        ["4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_mutant_the_build_stage_proves_equal_is_skipped() {
    // `2 + 0` and `2 - 0` are both built to 2; the other mutants change the factor. With `x`
    // generic, `2 + 0` takes the carrier of `x` (L1.26a) and is built once per carrier, one
    // `match` on `x` whose arms are `2.0 + 0.0`, `2r + 0r`, … and, last, `2 + 0`
    // (STAGE-generic-fold): the build stage builds each arm to its constant, and the mutant,
    // which replaces `+` in every arm, is skipped. It is named by the first arm, .1 (the
    // `match` on `x` is .0). The product, the root, is also negated whole (H6).
    let unit = "scale(positional x) = x * (2 + 0) test { 3 -> 6 }\n";
    assert_eq!(
        report(unit),
        [
            "1:30: skipped: `+` replaced by `-` in `scale` at .0.1.1: the build stage gives the \
             definition the original's term",
            "6 mutants: 5 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_mutant_of_an_operation_on_generic_literals_changes_it_at_every_carrier() {
    // `2 + 1` is built once per carrier; its mutant `2 - 1` replaces `+` in every arm, so a
    // row at `f64` alone detects it. The mutants of the constants 2 and 1 replace them in
    // every arm too, each by its neighbor at that arm's carrier (`2.0` by `1.0` at `f64`), so
    // the row at `f64` detects them as well (plan row MUTATE-generic-constants), and the
    // product negated whole (H6).
    let unit = "scale(positional x) = x * (2 + 1) test { 1.5f64 -> 4.5f64 }\n";
    assert_eq!(
        report(unit),
        ["6 mutants: 6 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // A row at `0` detects none of them; each is named by its own node, the last arm, and the
    // constant the source writes.
    let unit = "scale(positional x) = x * (2 + 1) test { 0 -> 0 }\n";
    assert_eq!(
        report(unit),
        [
            "1:25: undetected: `x * (2 + 1)` replaced by `-(x * (2 + 1))` in `scale` at .0: \
             every row that reaches it passes",
            "1:30: undetected: `+` replaced by `-` in `scale` at .0.1.1: every row that reaches \
             it passes",
            "1:28: undetected: `2` replaced by `1` in `scale` at .0.1.4.0: every row that reaches \
             it passes",
            "1:28: undetected: `2` replaced by `3` in `scale` at .0.1.4.0: every row that reaches \
             it passes",
            "1:32: undetected: `1` replaced by `0` in `scale` at .0.1.4.1: every row that reaches \
             it passes",
            "1:32: undetected: `1` replaced by `2` in `scale` at .0.1.4.1: every row that reaches \
             it passes",
            "6 mutants: 0 detected, 6 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_literal_following_another_keeps_its_mark_at_the_other_s_carrier() {
    // `/` takes no `int`, so at the `int` 2 the last arm of `4 / 2` is `4.0 / 2.0`: `2` takes
    // the carrier of `4.0` and keeps its mark there, so its mutants are made, at `f64` in the
    // last arm and at its own carrier in each other arm (plan row MUTATE-generic-constants),
    // and the row at `f64` detects them. `4 / 2` is also swapped (H11) and, the root of its
    // arithmetic, negated whole (H6).
    let unit = "g(positional x) = x == 4 / 2 test { 2 -> false, 2.0f64 -> true, 3r -> false }\n";
    assert_eq!(
        report(unit),
        ["8 mutants: 8 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // With no row at `f64`, the mutants of the constants are undetected, and named at `f64`, by
    // the last arm.
    let unit = "g(positional x) = x == 4 / 2 test { 2 -> false, 3r -> false }\n";
    assert_eq!(
        report(unit),
        [
            "1:26: undetected: `/` replaced by `*` in `g` at .0.1.1: every row that reaches it \
             passes",
            "1:26: undetected: `4 / 2` replaced by `2 / 4` in `g` at .0.1.1: every row that \
             reaches it passes",
            "1:26: undetected: `4 / 2` replaced by `-(4 / 2)` in `g` at .0.1.1: every row that \
             reaches it passes",
            "1:24: undetected: `4.0` replaced by `3.0` in `g` at .0.1.4.0: every row that \
             reaches it passes",
            "1:24: undetected: `4.0` replaced by `5.0` in `g` at .0.1.4.0: every row that \
             reaches it passes",
            "1:28: undetected: `2.0` replaced by `1.0` in `g` at .0.1.4.1: every row that \
             reaches it passes",
            "1:28: undetected: `2.0` replaced by `3.0` in `g` at .0.1.4.1: every row that \
             reaches it passes",
            "8 mutants: 1 detected, 7 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_mutant_of_an_int_parameter_the_build_stage_proves_equal_is_skipped() {
    // The same at a parameter declared `int`: no `match`, the operation itself built to 2.
    let unit = "scale(positional x: int) = x * (2 + 0) test { 3 -> 6 }\n";
    assert_eq!(
        report(unit),
        [
            "1:35: skipped: `+` replaced by `-` in `scale` at .0.1: the build stage gives the \
             definition the original's term",
            "6 mutants: 5 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_table_that_omits_the_boundary_leaves_its_mutants_undetected() {
    // The rows lie far from 18, so only the reversed `age > 18` (H3: `age` is generic) is
    // detected.
    let unit = "isMinor(positional age) = age < 18 test { 5 -> true, 40 -> false }\n";
    assert_eq!(
        report(unit),
        [
            "1:31: undetected: `<` replaced by `<=` in `isMinor` at .0.1: every row that reaches \
             it passes",
            "1:33: undetected: `18` replaced by `17` in `isMinor` at .0.1.1.4: every row that \
             reaches it passes",
            "1:33: undetected: `18` replaced by `19` in `isMinor` at .0.1.1.4: every row that \
             reaches it passes",
            "4 mutants: 1 detected, 3 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_definition_no_table_reaches_has_its_mutants_undetected() {
    // `limit` has a parameter, so it is not a declared constant (`limit = 10;` would have no
    // mutant, A103) and its literal is inline.
    let unit = "limit(positional n: int) = n + 10;\ndouble(positional x) = x * 2 test { 3 -> 6 }\n";
    assert_eq!(
        report(unit),
        [
            "1:30: undetected: `+` replaced by `-` in `limit` at .0: no table reaches the \
             definition",
            "1:30: undetected: `n + 10` replaced by `-(n + 10)` in `limit` at .0: no table \
             reaches the definition",
            "1:32: undetected: `10` replaced by `9` in `limit` at .0.1: no table reaches the \
             definition",
            "1:32: undetected: `10` replaced by `11` in `limit` at .0.1: no table reaches the \
             definition",
            "7 mutants: 3 detected, 4 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_multiplication_becomes_a_division_only_where_division_is_defined() {
    // On `rat` operands `/` is defined: `x / 0.5r` gives 8r, not 2r. On `int` operands it is
    // not, so `n * 2` has no `/` mutant, only the negated product (H6) and its constant's two.
    // `0.5r` moves by one unit of its last digit, to `0.4r` and `0.6r` (H4).
    let half = "half(positional x: rat) = x * 0.5r test { 4r -> 2r }\n";
    assert_eq!(
        report(half),
        ["4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    let double = "double(positional n: int) = n * 2 test { 3 -> 6 }\n";
    assert_eq!(
        report(double),
        ["3 mutants: 3 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_whole_number_on_rat_has_its_mutants_at_rat() {
    // The generic `2n` takes `rat`, so `price * 2n` is a `rat` product, on which `/` is defined,
    // and the constant's neighbors are the `rat` values 1 and 3. A table that tries only a price of
    // zero detects none of them, nor the negated product (H6); one that tries 3 detects all
    // four.
    let only_zero = "doubled(positional price: rat) = price * 2 test { 0r -> 0r }\n";
    assert_eq!(
        report(only_zero),
        [
            "1:40: undetected: `*` replaced by `/` in `doubled` at .0: every row that reaches \
             it passes",
            "1:40: undetected: `price * 2` replaced by `-(price * 2)` in `doubled` at .0: every \
             row that reaches it passes",
            "1:42: undetected: `2r` replaced by `1r` in `doubled` at .0.1: every row that \
             reaches it passes",
            "1:42: undetected: `2r` replaced by `3r` in `doubled` at .0.1: every row that \
             reaches it passes",
            "4 mutants: 0 detected, 4 undetected, 0 skipped, 0 not run",
        ]
    );
    let three = "doubled(positional price: rat) = price * 2 test { 3r -> 6r }\n";
    assert_eq!(
        report(three),
        ["4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // On `f64` too `/` is defined, and the generic constant takes `f64`.
    let scaled = "scaled(positional x: f64) = x * 4 test { 2.0 -> 8.0 }\n";
    assert_eq!(
        report(scaled),
        ["4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_row_of_main_runs_the_mutant_wave() {
    // `c * 9 div 5 + 32`: each mutant changes what the wave writes for 21 degrees, among them
    // the negated sum (H6) and `5 div (c * 9)` (H11), and the index `0` of `m.stdin[0]`.
    let unit = "\
fahrenheit(positional c) = c * 9 div 5 + 32;

main(m: MainArgs) {
  m.stdout <- \"${fahrenheit(int(trim(m.stdin[0] else \"\")))}F\" else \"not a number\";
}
test { \"21\\n\" -> \"69F\\n\" }
";
    assert_eq!(
        report(unit),
        ["12 mutants: 12 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

#[test]
fn a_mutant_whose_row_may_not_end_is_not_run() {
    // Replacing 0 by -1 sends `guard(0)` to `w(w)`, which never ends: such a row runs only
    // when its form shows that it ends (`stage::ends`), and `w` calls through a parameter. So
    // do the `if` replaced by its then branch and by its negated condition, and `x < 0` (H3);
    // the `if` replaced by its else branch is run, and the row passes.
    let unit = "\
w(positional f) = f(f);
guard(positional x) = if x > 0 { w(w) } else { x } test { 0 -> 0 }
";
    assert_eq!(
        report(unit),
        [
            "2:23: not run: `if x > 0 { w(w) } else { x }` replaced by `{ w(w) }` in `guard` at \
             .0: no row that ran fails, and the form of a row that reaches it does not show that \
             it ends",
            "2:23: undetected: `if x > 0 { w(w) } else { x }` replaced by `{ x }` in `guard` at \
             .0: every row that reaches it passes",
            "2:23: not run: `if x > 0 { w(w) } else { x }` replaced by `if !(x > 0) { w(w) } \
             else { x }` in `guard` at .0: no row that ran fails, and the form of a row that \
             reaches it does not show that it ends",
            "2:28: not run: `>` replaced by `>=` in `guard` at .0.0.1: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "2:28: not run: `>` replaced by `<` in `guard` at .0.0.1: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "2:30: not run: `0` replaced by `-1` in `guard` at .0.0.1.1.4: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "2:30: not run: `0` replaced by `1` in `guard` at .0.0.1.1.4: no row that ran fails, \
             and the form of a row that reaches it does not show that it ends",
            "7 mutants: 0 detected, 1 undetected, 0 skipped, 6 not run",
        ]
    );
}

#[test]
fn a_default_constant_has_no_mutant_at_the_calls_that_use_it() {
    // A literal default is copied into each call that leaves its argument out, so each copy
    // is a node of the calling definition, at the default's place in the source. A default is
    // a declared constant (A103, MUTATION.md section 4), so no copy has a mutant; `pad`'s sum
    // has its two, which no table reaches.
    let unit = "\
pad(positional n, by = 1) = n + by;
once(positional n) = pad(n);
again(positional n) = pad(n);
";
    assert_eq!(
        report(unit),
        [
            "1:31: undetected: `+` replaced by `-` in `pad` at .0: no table reaches the \
             definition",
            "1:31: undetected: `n + by` replaced by `-(n + by)` in `pad` at .0: no table \
             reaches the definition",
            "2 mutants: 0 detected, 2 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_mutant_of_a_generic_constant_replaces_it_at_every_carrier() {
    // Plan row MUTATE-generic-constants. At `f32`: `2.0f32` is replaced by `1.0f32` and
    // `3.0f32`, so the row at `f32` detects the mutants of 2 and of 1, and the negated
    // product (H6).
    let unit = "scale(positional x) = x * (2 + 1) test { 1.5f32 -> 4.5f32 }\n";
    assert_eq!(
        report(unit),
        ["6 mutants: 6 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // At `rat`.
    let unit = "scale(positional x) = x * (2 + 1) test { 1r/2r -> 3r/2r }\n";
    assert_eq!(
        report(unit),
        ["6 mutants: 6 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // A literal compared by `==` with a class takes the carrier of the other operand
    // (`elab::walk::follow`): its mutants replace it in each arm too, so a row at `f64` detects
    // them.
    let unit = "isTwo(positional x) = x == 2 test { 2.0f64 -> true, 3.0f64 -> false }\n";
    assert_eq!(
        report(unit),
        ["3 mutants: 3 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    // A generic literal with no other operand, a branch, taking its carrier from the
    // parameter (`elab::walk::witnessed`). The 0 of `x > 0` follows `x` too: at `f64` it is
    // replaced by `-1.0`, which the row detects, and by `1.0`, which it does not. The row takes
    // the else branch, so the `if` replaced by that branch passes it (H9).
    let unit = "floor(positional x) = if x > 0 { x } else { 1 } test { -0.5f64 -> 1.0f64 }\n";
    assert_eq!(
        report(unit),
        [
            "1:23: undetected: `if x > 0 { x } else { 1 }` replaced by `{ 1 }` in `floor` at .0: \
             every row that reaches it passes",
            "1:28: undetected: `>` replaced by `>=` in `floor` at .0.0.1: every row that reaches \
             it passes",
            "1:30: undetected: `0` replaced by `1` in `floor` at .0.0.1.1.4: every row that \
             reaches it passes",
            "9 mutants: 6 detected, 3 undetected, 0 skipped, 0 not run",
        ]
    );
}

#[test]
fn a_mutant_of_a_folded_decimal_or_power_is_skipped() {
    // Plan row STAGE-generic-fold-div. `1.5 + 0` and `(2 + 0) ^ 2` are built once per carrier,
    // `0` taking the decimal's arms and `2` the base's, and the build stage builds each arm to
    // its constant; `- 0` in place of `+ 0` then gives the original's term and is skipped. Each
    // product is negated whole (H6), and the decimal `1.5` moves to `1.4` and `1.6` (H4).
    let unit = "f(positional x) = x * (1.5 + 0) test { 2r -> 3r }\n";
    assert_eq!(
        report(unit),
        [
            "1:28: skipped: `+` replaced by `-` in `f` at .0.1.1: the build stage gives the \
             definition the original's term",
            "6 mutants: 5 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
    let unit = "f(positional x) = x * ((2 + 0) ^ 2) test { 1.5f64 -> 6.0f64 }\n";
    assert_eq!(
        report(unit),
        [
            "1:27: skipped: `+` replaced by `-` in `f` at .0.1.1.0: the build stage gives the \
             definition the original's term",
            "8 mutants: 7 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
    // `1 / 2 + 0` is one `match` too. `/` has no arrow on two `int`s, so no `int` reaches it,
    // and its last arm is at `f64`, `(1.0 / 2.0) + 0.0`, which the build stage builds as it
    // does the others (plan row STAGE-generic-fold-int-arm; before it, the last arm was at
    // `int`, `(1 / 2) + 0r`, which the build stage could not build, and the mutant was run and
    // reported undetected).
    let unit = "f(positional x) = x * (1 / 2 + 0) test { 2r -> 1r }\n";
    assert_eq!(
        report(unit),
        [
            "1:30: skipped: `+` replaced by `-` in `f` at .0.1.1: the build stage gives the \
             definition the original's term",
            "10 mutants: 9 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
    // A decimal and an integer: the last arm of `1 + 1.5` was at `int`, `1 + 1.5`, and is at
    // `f64`, `1.0 + 1.5`.
    let unit = "f(positional x) = x * ((1 + 1.5) + 0) test { 2r -> 5r }\n";
    assert_eq!(
        report(unit),
        [
            "1:34: skipped: `+` replaced by `-` in `f` at .0.1.1: the build stage gives the \
             definition the original's term",
            "9 mutants: 8 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
}

/// The exponent `1 + 0` follows the base `2`, which follows `x`: at `f64` it is read as `1.0`. A
/// mutant of `1` or `0` inside it changes it at every carrier, since each arm other than the
/// last casts the one term of the exponent (plan row MUTATE-follows-operation; before it, those
/// arms were the constant `1.0`, the mutant changed the last arm alone, and the four mutants were
/// reported undetected at the `f64` row).
#[test]
fn a_mutant_inside_a_generic_exponent_changes_it_at_every_carrier() {
    let unit = "f(positional x) = x * (2 ^ (1 + 0)) test { 1.5f64 -> 3.0f64 }\n";
    assert_eq!(
        report(unit),
        [
            "1:31: skipped: `+` replaced by `-` in `f` at .0.1.1.0: the build stage gives the \
             definition the original's term",
            "8 mutants: 7 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
    // A row at each carrier: each arm of the exponent runs with each mutant.
    let unit = "f(positional x) = x * (2 ^ (1 + 0)) \
                test { 1.5f64 -> 3.0f64, 1.5f32 -> 3.0f32, 1r -> 2r, 1 -> 2 }\n";
    assert_eq!(
        report(unit),
        [
            "1:31: skipped: `+` replaced by `-` in `f` at .0.1.1.0: the build stage gives the \
             definition the original's term",
            "8 mutants: 7 detected, 0 undetected, 1 skipped, 0 not run",
        ]
    );
}
