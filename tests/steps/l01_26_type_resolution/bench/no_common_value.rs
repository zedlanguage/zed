use zed_tests::deep::statements;
use zed_tests::scaling;
use zedc::rejection::Row;

use super::deep_ops::{DEEP, on_shallow_stack};
use super::super::no_common_value::{
    carriers_of_nested_tuples, shared, wide_tuples, wide_union, wide_written,
};

#[test]
fn carriers_of_shared_tuples_scale() {
    // `t(k+1) = (t(k), t(k))` has `2^n` paths through `n` nodes; each is widened once.
    let ts = scaling::inputs(512, shared);
    scaling::check_order("carriers of n shared tuples", 512, 1, |n| {
        assert!(!ts[&n].carriers().is_empty());
    });
}

/// Checks the programs `text(n)` and `text(8n)`, lexed, parsed and resolved before timing,
/// and checks each is rejected once, in the row `row`, in time linear in n.
fn rejects_linearly(what: &str, n: usize, text: fn(usize) -> String, row: Row) {
    let units = scaling::inputs(n, |m| {
        let stmts = statements(&text(m));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check_order(what, n, 1, |m| {
        let (stmts, res) = &units[&m];
        let info = zedc::check::walk::check(stmts, res);
        let rows: Vec<_> = info.errors.iter().map(|e| e.row).collect();
        assert_eq!(rows, [Some(row)], "{:?}", info.errors);
    });
}

#[test]
fn rejecting_two_wide_types_that_share_no_value_scales_for_a_union() {
    rejects_linearly(
        "== of a union of n tuples",
        256,
        wide_union,
        Row::EqNoCommonCarrier,
    );
}

#[test]
fn rejecting_two_wide_types_that_share_no_value_scales_for_tuples() {
    rejects_linearly(
        "== of two tuples of n components",
        256,
        wide_tuples,
        Row::EqNoCommonCarrier,
    );
}

#[test]
fn rejecting_two_wide_types_that_share_no_value_scales_for_a_written_tuple() {
    rejects_linearly(
        "== of a tuple of n components and a written one",
        256,
        wide_written,
        Row::EqNoCommonCarrier,
    );
}

#[test]
fn carriers_of_a_deep_tuple_run_on_a_shallow_stack() {
    on_shallow_stack(|| carriers_of_nested_tuples(DEEP));
}
