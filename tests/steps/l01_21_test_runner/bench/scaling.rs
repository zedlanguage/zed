//! The runner's rows at the rule of low complexity: the benchmarks of `scaling.rs`, whose tests
//! make each of their checks at small sizes.

use zed_tests::scaling::{check, inputs};
use zed_tests::step_helpers::l01_16_elaboration::checked;

use crate::scaling::*;

#[test]
fn running_the_rows_of_many_tables_scales() {
    // The front end's result for each size, made before the timing, so that the rows alone are
    // timed. Each run runs them on a copy, which holds the front end's results and no row's.
    let n = 100;
    let warm = inputs(n, |m| warm(tables(m)));
    check("running n functions' rows", n, |m| {
        all_rows_pass(&warm[&m], m)
    });
}

#[test]
fn rows_whose_calls_pass_atoms_by_scale() {
    let n = 100;
    let warm = inputs(n, |m| warm(passing_rows(m)));
    check("running n rows whose keys pass atoms", n, |m| {
        all_rows_pass(&warm[&m], 2 * m)
    });
}

#[test]
fn a_row_passing_the_atoms_of_many_arguments_scales() {
    // Elaboration alone, on units checked before the timing. `test_in` on a `Db` that holds
    // the front end's result does not elaborate, so it never reaches `Elab::row_call`; and
    // timing the whole front end lets checking, about 200,000 instructions an argument, hide a
    // quadratic term in `row_call`. A span map rebuilt for each argument gives 56 times the
    // work here.
    let n = 400;
    let units = inputs(n, |m| checked(&wide_row(m)));
    check(
        "elaborating a row of n arguments that each pass an atom",
        n,
        |m| elaborates_rows(&units[&m], 1),
    );
}

#[test]
fn the_rows_of_a_rejected_unit_fail_in_linear_time() {
    let n = 400;
    let warm = inputs(n, |m| warm(rejected_rows(m)));
    check("reporting the n rows of a rejected unit", n, |m| {
        rows_not_run(&warm[&m], m)
    });
}

#[test]
fn the_rows_of_tables_with_clauses_scale() {
    // Rows × clauses: elaborating `n` tables of one row each finds each row's clause by a
    // cursor that moves forward, and running `n` rows of one clause gives each row the clause's
    // value once.
    let n = 2000;
    let units = inputs(n, |m| checked(&clause_tables(m, 1)));
    check("elaborating n tables with a clause each", n, |m| {
        elaborates_rows(&units[&m], m)
    });
    let n = 200;
    let warm = inputs(n, |m| warm(clause_tables(1, m)));
    check("running n rows of a table with a clause", n, |m| {
        all_rows_pass(&warm[&m], m)
    });
}
