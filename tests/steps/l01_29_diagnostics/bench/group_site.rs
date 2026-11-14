//! The message of a refused check reading groups of `n` definitions, at `n` and `8n`
//! (`group_site.rs`).

use zed_tests::scaling;

use crate::group_site::the_head_group_named;

/// The head group grows with n and is listed whole, so the message grows too. A walk to the
/// head and its definitions sorted by name and written, `O(n log n)`.
#[test]
fn naming_the_head_group_scales() {
    let n = 1000;
    scaling::check_order(
        "the message of a refused check reading n definitions",
        n,
        1,
        the_head_group_named,
    );
}
