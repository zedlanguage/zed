//! A JSON document nested as deeply as its line is long, and a spreadsheet cell and a type that
//! depend on a chain as long as the input (author P178: an unusual size is a benchmark). A
//! reference that followed the chain by recursion would overflow a test thread's 2 MiB stack.
//! `a_short_nest_and_short_chains_are_followed` in `mod.rs` runs the same at small sizes.

use crate::{json_nests, sheet_chain, type_chain};

#[test]
fn a_json_document_may_nest_as_deeply_as_its_line_is_long() {
    json_nests(2_000_000);
}

/// Every edit prints every cell, so the output is quadratic in the chain's length.
#[test]
fn a_spreadsheet_cell_may_depend_on_a_chain_as_long_as_the_sheet() {
    sheet_chain(3000);
}

#[test]
fn a_type_may_depend_on_a_chain_as_long_as_the_program() {
    type_chain(50_000);
}
