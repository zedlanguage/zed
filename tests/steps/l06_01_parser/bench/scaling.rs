//! Building, formatting, refusing in name resolution and dropping the forms of `scaling.rs` is
//! linear in their size. Each input is lexed and parsed before timing, so the work measured is
//! this step's.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, body, formats_on_lines, nested, parsed, pass, pieces};

/// The units `make(base)` and `make(8 * base)`, parsed.
fn units(base: usize, make: impl Fn(usize) -> String) -> HashMap<usize, Parsed> {
    [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect()
}

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units = units(base, make);
    scaling::check(what, base, |n| pass(&units[&n], true));
}

#[test]
fn a_loop_body_of_many_statements_scales() {
    linear("a loop body of n statements", 2000, body);
}

/// Building, resolving and dropping are linear in the depth. The formatter writes each loop on
/// its own lines, indented by its depth, so its text is of order n^2 and so is writing it, as
/// for any nest of blocks (step L1.13).
#[test]
fn nested_loops_scale() {
    let units = units(1000, nested);
    scaling::check("n nested loops, built and resolved", 1000, |n| {
        pass(&units[&n], false)
    });
    scaling::check_order("n nested loops, formatted", 1000, 2, |n| {
        formats_on_lines(&units[&n], n)
    });
}

#[test]
fn a_piecewise_definition_of_many_pieces_scales() {
    linear("a piecewise definition of n pieces", 2000, pieces);
}
