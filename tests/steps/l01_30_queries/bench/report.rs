//! The recorder and a report are linear in their rows: the benchmarks of `report.rs`, whose test
//! records and reports at small sizes.

use zed_tests::scaling::check;

use crate::report::{definitions, marks, records, reports};

/// The front end's work hides the recorder's in the test below, so this one measures it apart.
#[test]
fn the_recorder_scales_with_its_rows() {
    let n = 2000;
    let (small, large) = (marks(n), marks(8 * n));
    check("the recorder with n rows", n, |m| {
        records(if m == n { &small } else { &large });
    });
}

#[test]
fn a_report_scales_with_the_definitions() {
    // The texts are built before any run is counted.
    let n = 40;
    let (small, large) = (definitions(n), definitions(8 * n));
    check("a reported test of n definitions", n, |m| {
        reports(if m == n { &small } else { &large }, m);
    });
}
