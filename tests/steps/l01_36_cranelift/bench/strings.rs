//! The check of `strings.rs` on a line of 500 fields, whose recursive passes over the program
//! (lowering, planning and the drop of a graph) need a stack larger than a test thread's (author
//! P178: a test that needs an unusual size is a benchmark).

use crate::strings::{FIELDS, appended_lens, both_with};

/// Small instance: `strings::len_after_many_appends_agrees_natively_and_in_the_kernel`.
#[test]
fn len_after_500_appends_agrees_natively_and_in_the_kernel() {
    let (t, want) = appended_lens(500, &FIELDS);
    let (native, kernel) = std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn_scoped(s, || both_with(&t, "log:"))
            .unwrap()
            .join()
            .unwrap()
    });
    assert_eq!(native, want);
    assert_eq!(kernel, want);
}
