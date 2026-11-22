//! `n` parcel checks in a row, each a derived node whose certificate compares with `>` and
//! `>=`: legalization's work is linear in the graph. The small instance is in `legalize.rs`.

use zed_tests::scaling;
use zedc::zir::Region;

use crate::legalize::parcel_checks;

#[test]
fn legalization_is_linear_in_the_graph() {
    // Each run legalizes a graph built before its timing starts, one held at a time
    // (MEM-l0126-40gb); the legalized graph is released inside the run, as it was.
    let n = 110_000;
    let legalize = |_: usize, g: Region| drop(zed_native::legalize(g));
    scaling::check_order_fresh(
        "legalizing parcel checks",
        n,
        1,
        |k, _| parcel_checks(k),
        legalize,
    );
}
