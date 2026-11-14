//! The rejections of `type_size.rs` at `n` and `8n` (MSG-derive-type-size,
//! MSG-derive-print-per-message, MSG-derive-print-union-names): their texts and their work
//! grow at most about 8 times. The texts at small sizes are held exactly by the tests of
//! `type_size.rs`.

use zed_tests::scaling;

use crate::rejected;
use crate::type_size::{
    compared, compared_with_1, doubling, growing, same, unions, unions_each_its_own, unions_inside,
    unions_named_one_by_one,
};

/// Checks that the rejection of `make(8n)` is at most about 8 times as long as that of
/// `make(n)`. [`works`] holds the work to the same order, on the same derivations without the
/// repair of `+` ([`compared_with_1`]).
fn scales(what: &str, n: usize, make: fn(usize) -> String) {
    let large = scaling::FACTOR * n;
    let bytes = |k: usize| rejected(&make(k)).len() as u64;
    scaling::hold(what, "bytes of the rejection", bytes(n), bytes(large), 1);
}

#[test]
fn rejecting_a_tuple_doubled_n_times_writes_a_text_linear_in_n() {
    scales("rejecting a tuple doubled n times", 40, doubling);
}

#[test]
fn rejecting_a_comparison_of_tuples_doubled_n_times_writes_a_text_linear_in_n() {
    scales(
        "rejecting a comparison of tuples doubled n times",
        40,
        compared,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_the_one_before_writes_a_text_linear_in_n() {
    scales(
        "rejecting a chain of n names each holding the one before",
        40,
        growing,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_of_one_type_writes_a_text_linear_in_n() {
    // A type of five components at each link. A type as wide as the chain is long is written
    // whole at each link, n × m in all (COMPLEXITY.md row MSG-derive-same-chain).
    scales(
        "rejecting a chain of n names of one type of five components",
        40,
        |n| same(n, 5),
    );
}

/// Checks that rejecting `make(8n)` does at most about 8 times the work and allocates at most
/// about 8 times the bytes of rejecting `make(n)`: the derivation prints the parts of its types
/// once per message, not once per step (MSG-derive-print-per-message).
fn works(what: &str, n: usize, make: fn(usize) -> String) {
    let srcs = scaling::inputs(n, make);
    scaling::check(what, n, |k| {
        rejected(&srcs[&k]);
    });
}

#[test]
fn rejecting_a_comparison_of_a_tuple_doubled_n_times_with_1_does_work_linear_in_n() {
    works(
        "rejecting a comparison of a tuple doubled n times with 1",
        40,
        |n| compared_with_1(doubling(n)),
    );
}

#[test]
fn rejecting_a_comparison_of_tuples_doubled_n_times_does_work_linear_in_n() {
    works(
        "rejecting a comparison of tuples doubled n times",
        40,
        compared,
    );
}

#[test]
fn rejecting_a_comparison_of_a_chain_of_n_names_each_holding_the_one_before_with_1_does_work_linear_in_n()
 {
    works(
        "rejecting a comparison of a chain of n names each holding the one before with 1",
        40,
        |n| compared_with_1(growing(n)),
    );
}

// The repair of `t_n + 1` lists the one value of `t_n`. Its maker files the first components
// of each type once for the whole listing; before, each level's maker walked every level below
// it again, O(n²) in a chain of n levels (COMPLEXITY.md row K109, MAKER-file-chain).

#[test]
fn rejecting_a_tuple_doubled_n_times_with_1_added_does_work_linear_in_n() {
    works(
        "rejecting a tuple doubled n times with 1 added",
        40,
        doubling,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_the_one_before_with_1_added_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each holding the one before with 1 added",
        40,
        growing,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_a_union_writes_a_text_linear_in_n() {
    scales(
        "rejecting a chain of n names each holding a union",
        40,
        unions,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_a_union_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each holding a union",
        40,
        unions,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_holding_a_union_of_its_own_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each holding a union of its own",
        40,
        unions_each_its_own,
    );
}

#[test]
fn rejecting_a_chain_of_n_names_each_using_a_union_once_and_twice_does_work_linear_in_n() {
    works(
        "rejecting a chain of n names each using a union once and twice",
        40,
        unions_inside,
    );
}

#[test]
fn rejecting_a_chain_naming_one_more_union_of_a_part_at_each_link_writes_a_text_linear_in_n() {
    scales(
        "rejecting a chain naming one more union of a part at each link",
        40,
        unions_named_one_by_one,
    );
}

#[test]
fn rejecting_a_chain_naming_one_more_union_of_a_part_at_each_link_does_work_linear_in_n() {
    works(
        "rejecting a chain naming one more union of a part at each link",
        40,
        unions_named_one_by_one,
    );
}
