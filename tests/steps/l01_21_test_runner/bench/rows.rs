//! Checking marks against their rows, and finding the words a message must not say, are linear:
//! the benchmarks of `rows.rs`, whose tests check a few of each.

use zed_tests::scaling::{check, check_order, inputs};

use crate::rows::{every_mark_is_ok, messages, rebound, said, unsaid_words};

#[test]
fn checking_n_marks_scales() {
    let n = 200;
    let units = inputs(n, rebound);
    check_order("checking n marked lines against their rows", n, 1, |m| {
        every_mark_is_ok(&units[&m], m)
    });
}

#[test]
fn finding_the_unsaid_words_scales() {
    let words = unsaid_words();
    let texts = inputs(2000, messages);
    check("finding kernel rule names in n message lines", 2000, |m| {
        assert_eq!(said(&texts[&m], &words).len(), m);
    });
}
