//! The `conflicts` tool is linear in the items of the plan; what it finds is checked at small
//! sizes by `conflicts::the_conflicts_of_many_strands_are_found_at_small_sizes`.

use zed_tests::scaling::{check, inputs};

use crate::conflicts::{strands, strands_conflicts_found};

#[test]
fn conflicts_scale_with_the_number_of_items() {
    let n = 200;
    let texts = inputs(n, strands);
    check("conflicts, by items", n, |m| {
        strands_conflicts_found(&texts[&m], m)
    });
}
