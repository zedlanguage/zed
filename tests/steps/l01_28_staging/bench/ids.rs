//! The form rule of `ids.rs` at `d` and `8d` levels. Each term is built before the timing.

use zed_kernel::{Shared, Term};
use zed_tests::scaling;
use zedc::stage::ends;

use crate::ids::same_arms;

#[test]
fn a_part_held_by_both_arms_of_nested_ifs_is_read_once() {
    // The two arms of each `if` are one node: read by the place it is reached from, the walk
    // would take 2^d steps.
    let n = 1000;
    let terms = scaling::inputs(n, same_arms);
    scaling::check_order(
        "stage::ends on d nested ifs whose two arms are one part",
        n,
        1,
        |d| {
            assert!(ends(&terms[&d]));
        },
    );
    // Under a binder of `n` the chain still ends.
    let under = Term::Lam(vec!["n".into()], Shared::new(same_arms(n)));
    assert!(ends(&under));
}
