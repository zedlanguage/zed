//! Recovering from `n` declarations left open, at `n` and `8n` (`syntax_recovery.rs`).

use zed_tests::scaling;

use crate::syntax_recovery::{declarations_left_open_recovered, left_open};

/// Each failing declaration is parsed once more alone, and the table of the parse is shared, so
/// the parse is linear in the unit; restarting the parse at each declaration on a fresh table
/// re-reads every declaration after it, O(n²).
#[test]
fn many_declarations_left_open_parse_in_linear_time() {
    let n = 200;
    let srcs = scaling::inputs(n, left_open);
    scaling::check_order("recovering from n declarations left open", n, 1, |k| {
        declarations_left_open_recovered(&srcs[&k], k);
    });
}
