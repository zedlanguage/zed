//! The checks of `initial` statements in time of order `n log n`: the benchmarks of
//! `initial.rs`, whose tests make each check of each input at small sizes. Each input is lexed,
//! and parsed where the work timed is not the parser's, before timing.

use zed_tests::scaling;

use crate::initial::{
    INITIALS, OVERLAPPING, bare_item, bare_item_refused, builds, many_entries, overlapping_verdict,
    parsed, second_site, second_site_refused,
};

/// Each site is one query and one insertion into a Fenwick tree over the first keys of its
/// class (`crate::ast::sentinel` in zedc-syntax), so `2n` sites of one variable whose entries
/// are apart are checked in time of order `n log n`, and a site after them that meets one is
/// found in the same time.
#[test]
fn overlapping_entries_scale() {
    for (what, tail, ok) in OVERLAPPING {
        let units = scaling::inputs(500, |n| parsed(many_entries(n, tail)));
        scaling::check(what, 500, |n| overlapping_verdict(what, &units[&n], ok));
    }
}

/// The checks of a loop body are one pass over its statements, with a Fenwick tree over the
/// first keys of the sites of each variable, so `n` `initial` statements in one body, and `n`
/// loops with one each, are built in time of order `n log n`; and a second site after `n` is
/// found in the same time.
#[test]
fn initial_statements_scale() {
    for (what, make) in INITIALS {
        let units = scaling::inputs(500, |n| parsed(make(n)));
        scaling::check(what, 500, |n| builds(&units[&n]));
    }
    let units = scaling::inputs(500, |n| parsed(second_site(n)));
    scaling::check("a second initial statement after n", 500, |n| {
        second_site_refused(&units[&n])
    });
}

/// A bare `with` item is found by the parser on the error path, which parses the unit again
/// with each repair written in, a fixed number of times: linear in the unit's size.
#[test]
fn finding_a_bare_item_scales() {
    let units = scaling::inputs(500, bare_item);
    scaling::check("a bare item after n statements", 500, |n| {
        bare_item_refused(&units[&n])
    });
}
