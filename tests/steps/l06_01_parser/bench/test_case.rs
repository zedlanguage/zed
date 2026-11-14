//! Finding a clause in a test case is linear in the unit: the benchmark of `test_case.rs`.

use zed_tests::scaling;

use crate::test_case::{clause_after, clause_found};

/// The case is found by a scan back to the table's `{` and forward to the case's end, one parse
/// of the values and the case's left side, at most two parses of the unit with the clause
/// rewritten, and one walk down the tree: linear in the unit, here in the cases before it.
#[test]
fn finding_a_clause_in_a_test_case_scales() {
    let units = scaling::inputs(500, clause_after);
    scaling::check("a clause in a test case after n cases", 500, |n| {
        clause_found(&units[&n])
    });
}
