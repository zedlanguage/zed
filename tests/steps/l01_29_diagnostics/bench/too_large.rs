//! Chains and lists of builds past the address space, at `n` and `8n` (`too_large.rs`). Each
//! input is built before the timing.

use zed_tests::scaling;

use crate::too_large::{
    chain, kept_sums, powers, product_chain, rat_product_chain, rejected_times,
};

/// Checks that rejecting `make(n)`, with `per * n` rejections, scales as a pass of order n.
fn rejecting(what: &str, n: usize, per: usize, make: fn(usize) -> String) {
    let srcs = scaling::inputs(n, make);
    scaling::check(what, n, |k| rejected_times(&srcs[&k], per * k));
}

#[test]
fn rejecting_many_powers_scales() {
    // The bound is O(1) words per power: one division and one comparison.
    rejecting(
        "n powers past the address space, each rejected",
        200,
        1,
        powers,
    );
}

#[test]
fn reading_a_chain_of_names_and_divisions_scales() {
    // Each name is read once, however many powers read it: the chain of `n` names costs `n`
    // divisions of 103-bit numbers and `n` rejections.
    rejecting(
        "a chain of n names and divisions, a power of each rejected",
        200,
        1,
        chain,
    );
}

#[test]
fn bounding_a_chain_of_products_scales() {
    // Each name is read once, however many products read through it: the chain of `n` names
    // costs O(n) reads of bit lengths and `n` rejections, each at the third `*` of its line.
    rejecting(
        "a chain of n names and products, a product of each rejected",
        200,
        1,
        product_chain,
    );
}

#[test]
fn bounding_a_chain_of_rat_products_scales() {
    // Plan row CONST-too-large-products-unproved, cases (a) and (c): each name keeps `b` as
    // the root of its numerator and `c` as that of its denominator, so each `*` costs at most
    // six gcds of 65-bit numbers, not a gcd of the whole chain's product: O(n) in all, and
    // `2n` rejections.
    rejecting(
        "a chain of n rat names, a product and a power of each rejected",
        200,
        2,
        rat_product_chain,
    );
}

#[test]
fn judging_many_builds_scales() {
    // One kernel step per sum, refused before it allocates: O(1) words each, O(n) in all.
    rejecting(
        "n kept powers and n sums past the address space, each sum rejected",
        800,
        1,
        kept_sums,
    );
}
