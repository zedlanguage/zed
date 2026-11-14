//! Shared values at the rule of low complexity (COMPLEXITY.md K21), each linear in its size:
//! a tuple read and copied once per element, a list built by an accumulator, equality, order
//! and keys of values and of families that share their parts, the text of sets nested inside
//! tuples, one part held in many places, and families made from one family. What each asserts
//! besides its ratio is checked at small sizes by
//! `shared::shared_values_compare_and_show_at_small_sizes`,
//! `shared::a_record_read_once_per_field_gives_each_field` and
//! `shared::an_accumulated_list_holds_every_element_in_order`.

use std::collections::HashMap;

use zed_kernel::{Term, Value};
use zed_tests::scaling::check_order;

use crate::shared::{
    cons_list, families, families_compare, made, made_compare, nested_sets, on_large_stack,
    one_part_compares, reads, row, run, shared_parts, shared_parts_compare, shows_nested_sets,
    tuple, wide,
};

/// Inputs for `check_order`, built before any timing: `make(n)` and `make(8n)`.
fn built<T>(n: usize, make: impl Fn(usize) -> T) -> HashMap<usize, T> {
    [n, 8 * n].into_iter().map(|m| (m, make(m))).collect()
}

#[test]
fn reading_a_tuple_once_per_element_scales() {
    // Each read copied the tuple: 100 reads of an n-tuple took 14.5, 127.6 and 1098 ms at
    // n = 1000, 8000 and 64000 (T11).
    let terms: HashMap<usize, Term> = built(2000, reads);
    check_order("a tuple read once per element, by elements", 2000, 1, |n| {
        run(&terms[&n]);
    });
}

#[test]
fn copying_a_tuple_once_per_element_scales() {
    let tuples = built(2000, tuple);
    check_order("n copies of a tuple of n, by n", 2000, 1, |n| {
        let t = &tuples[&n];
        let copies: Vec<Value> = (0..n).map(|_| t.clone()).collect();
        assert_eq!(copies.len(), n);
    });
}

#[test]
fn a_list_built_by_an_accumulator_scales() {
    // Each step copied the accumulator: through `zedc run`, 6,400, 12,800 and 25,600 elements
    // took 1.60, 7.77 and 37.13 s (COMPLEXITY.md K21).
    on_large_stack(|| {
        let terms = built(1000, cons_list);
        check_order(
            "a foldl that conses onto its accumulator, by elements",
            1000,
            1,
            |n| {
                run(&terms[&n]);
            },
        );
    });
}

#[test]
fn comparing_and_keying_values_that_share_their_parts_scales() {
    // Read path by path, each walk took time 2^depth: past 60 s at depth 1,000,000.
    let values = built(5000, shared_parts);
    check_order(
        "equality, order and keys of shared parts, by depth",
        5000,
        1,
        |n| shared_parts_compare(&values[&n]),
    );
}

#[test]
fn showing_sets_nested_inside_tuples_scales() {
    // `{({(...,)},)}`: each set's member is its own key, so the test that writes a set by its
    // members compares one shared value with itself, O(1) at each level.
    let values = built(2000, nested_sets);
    check_order(
        "Display of sets nested inside tuples, by depth",
        2000,
        1,
        |n| shows_nested_sets(&values[&n], n),
    );
}

#[test]
fn comparing_families_that_share_their_levels_scales() {
    // With no read set for pairs of families, a comparison read every keypath: 2^depth.
    let values = built(2000, families);
    check_order(
        "equality, order and the language's relations of families, by depth",
        2000,
        1,
        |n| families_compare(&values[&n]),
    );
}

#[test]
fn comparing_one_part_held_in_many_places_scales() {
    let values = built(1000, |n| [wide(n), wide(n), row(n), row(n)]);
    check_order(
        "equality of n entries holding one tuple of n, and the language's relations on a \
         tuple of n copies of one family of n, by n",
        1000,
        1,
        |n| one_part_compares(&values[&n]),
    );
}

#[test]
fn comparing_families_made_from_one_family_scales() {
    // `h_i = h_0 | {1000 + i: i}` for one family `h_0` of 101 entries, one of them a family `f`
    // of n entries: the n families have n ids but share the map node that holds `f`, so `f` is
    // met n times though it is held in one entry of one map. Each side is built apart.
    let values = built(1000, |n| [made(n), made(n)]);
    check_order(
        "equality, order and the language's relations of n families made from one family \
         that holds a family of n, by n",
        1000,
        1,
        |n| made_compare(&values[&n]),
    );
}
