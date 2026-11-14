//! Law 25's invariant form on all 768 relations (512 on three points and 256 on four), through
//! `N` iterates each: a run of many cases, so a benchmark (author P178).
//! `laws_21_28::law_25_a_left_multiplied_step_takes_the_invariant_form` checks the 512 on three
//! points and the 5 on four whose index among the 768 is a multiple of 48 (TEST-law25-time).

use zed_tests::check::holds;

use crate::laws_11_20::relations;
use crate::laws_21_28::left_multiplied_invariant;

#[test]
fn law_25_a_left_multiplied_step_takes_the_invariant_form_on_every_relation() {
    let n = holds(relations(), |pairs| left_multiplied_invariant(pairs));
    assert_eq!(n, 512 + 256);
}
