//! The layout record of a unit is made in time linear in its definitions: the benchmark of
//! `layout.rs`, whose test makes it for a few.

use zed_tests::layout::record;
use zed_tests::scaling::check;

use crate::layout::many;

#[test]
fn the_record_of_a_unit_scales() {
    check("the layout record of a unit of n definitions", 100, |n| {
        record(&many(n)).unwrap_or_else(|e| panic!("{e}"));
    });
}
