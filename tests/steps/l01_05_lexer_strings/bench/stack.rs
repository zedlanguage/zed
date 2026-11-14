//! Holes nested 100,000 deep, far more levels than a test thread's 2 MiB stack holds were the
//! tokens walked by recursion (author P178: an unusual size is a benchmark).
//! `scaling::tokens_a_few_holes_deep_compare_print_and_drop` makes the same checks at a few
//! levels.

use crate::scaling::deep_tokens;

#[test]
fn deep_tokens_compare_print_and_drop() {
    deep_tokens(100_000);
}
