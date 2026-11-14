//! Cutting, moving and checking the items of a unit, at `n` and `8n` items (`order.rs`).

use zed_tests::scaling;

use crate::order::{
    Items, chain, checked_with_its_items_moved, cut_into_items, items, moved, pairs, rates,
};

/// Cutting a unit into items is O(i): the lex and parse, and one pass over the root's items.
#[test]
fn cutting_a_unit_into_items_scales() {
    let n = 21_000;
    let units = scaling::inputs(n, rates);
    scaling::check("cutting n items of seven names", n, |k| {
        cut_into_items(&units[&k], k);
    });
}

/// Checks the moves of the items of `make(n)` and `make(8n)`, cut before timing.
fn moving(what: &str, n: usize, make: fn(usize) -> String) {
    let units = scaling::inputs(n, make);
    let cut: std::collections::HashMap<usize, Items> =
        units.iter().map(|(&k, t)| (k, items(t))).collect();
    scaling::check(what, n, |k| moved(&units[&k], &cut[&k]));
}

/// Moving the items is O(i): the two orders, each name's written order kept, and the moved
/// texts. The items are cut before timing, since the lex and parse would hide a quadratic
/// permutation.
#[test]
fn moving_the_items_of_a_unit_scales() {
    moving("moving n items of seven names", 2000, rates);
}

/// Keeping the written order of items that declare several names is O(i): the joins of
/// shared names are found by union-find, with one hash lookup per name.
#[test]
fn moving_items_of_several_names_scales() {
    moving("moving n items, every other one of two names", 2000, pairs);
}

#[test]
fn checking_a_unit_with_its_items_moved_scales() {
    let n = 1300;
    let units = scaling::inputs(n, chain);
    scaling::check(
        "cutting, moving and checking n items, with a test on every tenth",
        n,
        |k| checked_with_its_items_moved(&units[&k], k),
    );
}
