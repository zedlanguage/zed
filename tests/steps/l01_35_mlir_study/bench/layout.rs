//! The layout record of a unit is made in time and peak bytes linear in its definitions: the
//! benchmarks of `layout.rs`, whose test makes it for a few.

use zed_tests::layout::record;
use zed_tests::scaling::{self, check};

use crate::layout::many;

#[test]
fn the_record_of_a_unit_scales() {
    check("the layout record of a unit of n definitions", 100, |n| {
        record(&many(n)).unwrap_or_else(|e| panic!("{e}"));
    });
}

#[test]
fn the_peak_bytes_of_n_and_8n_definitions_scale() {
    let peak = |n: usize| {
        let text = many(n);
        let (r, l) = zed_alloc_count::live(|| record(&text).unwrap_or_else(|e| panic!("{e}")));
        assert_eq!(r.native.runs, n as u64);
        l.peak
    };
    scaling::hold(
        "the peak bytes of recording 100 and 800 definitions",
        "bytes",
        peak(100),
        peak(800),
        1,
    );
}
