//! The work limit at its size, `BUDGET` steps (author P178: an unusual size is a benchmark).
//! `hardness::a_short_or_and_a_few_ands_are_joined_without_refusal` makes the same checks on
//! short laws.

use crate::hardness::{long_or, many};
use crate::trivial::BUDGET;

/// The work limit counts steps of multiplying out, not the size of the law: one `||` of more
/// comparisons than `BUDGET` is joined with nothing multiplied out and is not refused, while
/// `&&`s of `(a && b) || c`, six atoms written each, are refused exactly when the steps pass
/// the limit.
#[test]
fn the_work_limit_is_not_a_size_limit() {
    let n = BUDGET as usize + 2;
    let t = long_or(n);
    assert!(!t.laws[0].refused());
    assert_eq!(t.laws[0].clauses().len(), 1);
    assert_eq!(t.laws[0].clauses()[0].len(), n);
    let m = BUDGET as usize / 6;
    let t = many(m);
    assert!(!t.laws[0].refused());
    assert_eq!(t.laws[0].clauses().len(), 2 * m);
    assert!(many(m + 1).laws[0].refused());
}
