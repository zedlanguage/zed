//! Canonicalizing, keying, ranking and renaming a deep graph is linear in its depth, and
//! canonicalizing and keying an edge of many facets is `O(F log F)`: the benchmarks of
//! `scaling.rs`, whose tests make each pass at small sizes.

use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::canon::{canonicalize, key, ranks, step};

use crate::scaling::{deep_match, many_facets, sorts_its_facets};

#[test]
fn canonicalizing_a_deep_graph_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (deep_match(12_500, "x"), deep_match(100_000, "x"));
        let pick = |k| if k == 12_500 { &small } else { &large };
        check_order("canonicalizing nested `if` regions", 12_500, 1, |k| {
            canonicalize(pick(k));
        });
        check_order("keying nested `if` regions", 12_500, 1, |k| {
            key(pick(k)).expect("memory for the key");
        });
        check_order("ranking nested `if` regions", 12_500, 1, |k| {
            ranks(pick(k));
        });
        check_order(
            "renaming the binder of nested `if` regions",
            12_500,
            1,
            |k| {
                let mut g = pick(k).clone();
                while step(&mut g).is_some() {}
            },
        );
    });
}

#[test]
fn canonicalizing_an_edge_of_many_facets_is_n_log_n() {
    let (small, large) = (many_facets(100), many_facets(800));
    let pick = |k| if k == 100 { &small } else { &large };
    check_order(
        "canonicalizing an edge of n facets in reverse order",
        100,
        1,
        |k| sorts_its_facets(pick(k)),
    );
    check_order("keying an edge of n facets in reverse order", 100, 1, |k| {
        key(pick(k)).expect("memory for the key");
    });
}
