//! Lexing and parsing the fences of a page, and finding the names in them, are linear in its
//! fences: the benchmark of `mathlib.rs`, whose test reads a generated page of a few fences.

use zed_tests::scaling::{check, inputs};

use crate::mathlib::{generated_page, reads_the_generated_page};

#[test]
fn parsing_the_fences_of_a_page_scales() {
    let pages = inputs(500, generated_page);
    check(
        "lexing and parsing n fences of a page, and finding names in them",
        500,
        |n| reads_the_generated_page(&pages[&n]),
    );
}
