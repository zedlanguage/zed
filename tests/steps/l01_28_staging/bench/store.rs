//! The mixes of `store.rs` at `n` and `8n` (COMPLEXITY.md row F83). Each unit is built before
//! the timing; `store.rs` compares each mix with that of the tree form at small sizes.

use zed_tests::scaling;

use crate::cone::F0;
use crate::store::{expected, family, mixed};

fn mixing_scales(what: &'static str, f0: F0, lets: bool) {
    let n = 400;
    let units = scaling::inputs(n, |n| family(n, f0, true, lets));
    scaling::check(what, n, |n| {
        assert_eq!(mixed(&units[&n]), expected(n, f0));
    });
}

#[test]
fn mixing_calls_of_a_chain_under_nested_ifs_whose_arms_are_one_part_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions under n nested ifs whose two arms \
         are one part",
        F0::Ends,
        false,
    );
}

#[test]
fn mixing_calls_left_to_run_under_nested_ifs_whose_arms_are_one_part_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions whose form does not show it ends, \
         under n nested ifs whose two arms are one part",
        F0::Loops,
        false,
    );
}

#[test]
fn mixing_calls_under_nested_ifs_whose_arms_bind_a_name_over_one_part_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions under n nested ifs whose two arms \
         each bind g over one part",
        F0::Ends,
        true,
    );
}
