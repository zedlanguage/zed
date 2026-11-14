use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::Resolved;
use super::super::ordered_tuples::{doubled, lengths, nested, tagged};

#[test]
fn rows_held_twice_at_each_level_compare_in_linear_time() {
    let units: BTreeMap<usize, Resolved> = [6000, scaling::FACTOR * 6000]
        .into_iter()
        .map(|n| (n, Resolved::new(&doubled(n, "<"))))
        .collect();
    scaling::check_order(
        "t < t over n levels each holding the last twice",
        6000,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "at {n}: {:?}", info.errors);
        },
    );
}

#[test]
fn many_tuple_shapes_compare_in_linear_time() {
    let units: BTreeMap<usize, Resolved> = [16_000, scaling::FACTOR * 16_000]
        .into_iter()
        .map(|n| (n, Resolved::new(&tagged(n))))
        .collect();
    scaling::check_order("x < x over n tuple shapes (#ai, int)", 16_000, 1, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "at {n}: {:?}", info.errors);
    });
}

#[test]
fn tuples_of_every_length_compare_in_time_linear_in_their_components() {
    // The type holds n(n + 1)/2 components, so work linear in it is of order n².
    let units: BTreeMap<usize, Resolved> = [200, scaling::FACTOR * 200]
        .into_iter()
        .map(|n| (n, Resolved::new(&lengths(n))))
        .collect();
    scaling::check_order(
        "x < x over tuples of each length from 1 to n",
        200,
        2,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "at {n}: {:?}", info.errors);
        },
    );
}

#[test]
fn a_mismatch_at_depth_n_is_reported_in_linear_time() {
    // The message names the place, `n` indices, once, and one step for each level, each of
    // its own size; the two declared types, of size `n`, are printed once each.
    let units: BTreeMap<usize, Resolved> = [3200, scaling::FACTOR * 3200]
        .into_iter()
        .map(|n| (n, Resolved::new(&nested(n, "bool"))))
        .collect();
    scaling::check_order("x < y failing at depth n", 3200, 1, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "at {n}");
        assert_eq!(info.errors[0].notes.len(), n + 8, "at {n}");
    });
}

#[test]
fn a_repair_at_depth_n_is_written_in_time_linear_in_its_length() {
    // Complexity tradeoff: the repair is the whole comparison rewritten, and the component it
    // writes at level `j` is read from `x` by `j` indices, so the repair holds n(n + 1)/2
    // indices: work linear in it is of order n². Naming the place alone, `rat(x[0]…[0])` in
    // place of `x[0]…[0]`, was O(n), but it is not an expression the program can hold
    // (DESIGN.md sec:diagnostics). COMPLEXITY.md row F140.
    let units: BTreeMap<usize, Resolved> = [800, scaling::FACTOR * 800]
        .into_iter()
        .map(|n| (n, Resolved::new(&nested(n, "rat"))))
        .collect();
    scaling::check_order("x < y with a repair at depth n", 800, 2, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "at {n}");
        assert!(info.errors[0].message.contains("Try `("), "at {n}");
    });
}
