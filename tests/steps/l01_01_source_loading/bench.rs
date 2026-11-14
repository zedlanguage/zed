//! Loading is of order n log n in the bytes of the file, NFC or not, and so is placing every
//! offset of it (DESIGN.md Part G): the benchmarks of this step, run by `tools/run_tests.sh
//! --bench`. Each check they make besides the ratio is made at small sizes by the correctness
//! tests in `scaling.rs`.

mod random;

use zed_tests::scaling::{check, check_instructions_only, inputs};

use super::scaling::{
    base_with_marks, crlf_lines, late_bad_byte, loads_nfc_lines, nfc_lines, places_every_offset,
    rejects_base_with_marks, rejects_late_bad_byte,
};

#[test]
fn nfc_text_with_line_breaks_of_every_kind_scales() {
    const N: usize = 4_000;
    let files = inputs(N, nfc_lines);
    check("loading n lines of NFC text", N, |n| {
        loads_nfc_lines(&files[&n], n)
    });
}

#[test]
fn one_base_with_a_long_run_of_marks_of_mixed_classes_scales() {
    const N: usize = 4_000;
    let files = inputs(N, base_with_marks);
    check("loading one base with n marks", N, |n| {
        rejects_base_with_marks(&files[&n])
    });
}

#[test]
fn a_rejection_late_in_a_long_file_scales() {
    const N: usize = 4_000;
    let files = inputs(N, late_bad_byte);
    // The rejection allocates nothing: std finds the bad byte, and the span is two numbers.
    check_instructions_only("loading n lines and a byte that is not UTF-8", N, 1, |n| {
        rejects_late_bad_byte(&files[&n])
    });
}

#[test]
fn placing_every_offset_scales() {
    const N: usize = 4_000;
    let files = inputs(N, crlf_lines);
    check("placing every offset of n lines", N, |n| {
        places_every_offset(&files[&n], n)
    });
}
