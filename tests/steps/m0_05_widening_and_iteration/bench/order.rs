//! The keyed order's time on four families of n cells, of order n log n (checked with order 1 at
//! n and 8n); each family is ordered at small sizes by
//! `order::the_keyed_order_of_each_benchmark_family_is_found_at_small_sizes`.

use zed_tests::scaling;
use zedc::store::iterate::order;

use crate::order::{Keyed, keyed_chain, keyed_loops, keyed_one_binding, keyed_one_node};

/// Runs the order at `n` and `8n` on the systems `build` makes, built before the timing.
fn order_scales(what: &str, n: usize, build: impl Fn(usize) -> Keyed) {
    let (small, large) = (build(n), build(scaling::FACTOR * n));
    scaling::check_order(what, n, 1, |m| {
        let eq = if m == n { &small } else { &large };
        order(eq).unwrap();
    });
}

#[test]
fn the_order_of_a_long_chain_scales() {
    order_scales("the keyed order of a chain", 20_000, keyed_chain);
}

#[test]
fn the_order_of_many_small_loops_scales() {
    // Loops of three cells, each reading the one before it in the loop.
    order_scales("the keyed order of loops of three", 21_000, keyed_loops);
}

#[test]
fn the_order_of_one_bindings_nodes_scales() {
    // Every cell has one name and one address, so every comparison reaches the canonical
    // forms: n log n comparisons of forms of a fixed length.
    order_scales(
        "the keyed order of nodes with one name and address",
        21_000,
        keyed_one_binding,
    );
}

#[test]
fn the_order_of_one_nodes_cells_scales() {
    // Every cell is a cell of one static node: one name, one address and equal forms of eight
    // numbers, held apart, so every comparison reads both forms and then the keypaths, a
    // string key and a scrambled integer key. n log n comparisons of keys of a fixed length.
    order_scales(
        "the keyed order of one node's cells",
        21_000,
        keyed_one_node,
    );
}
