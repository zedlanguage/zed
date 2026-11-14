//! Law 25's invariant form on all 768 relations (512 on three points and 256 on four), through
//! `N` iterates each: about 9 s, a long run (author P178: a long run is a benchmark;
//! TEST-law25-time is to make it fast enough to return here to the correctness tests).
//! `laws_21_28::law_25_a_left_multiplied_step_takes_the_invariant_form` checks every 48th.

use zed_tests::check::holds;

use crate::laws_11_20::relations;
use crate::laws_21_28::left_multiplied_invariant;

#[test]
fn law_25_a_left_multiplied_step_takes_the_invariant_form_on_every_relation() {
    let n = holds(relations(), |pairs| left_multiplied_invariant(pairs));
    assert_eq!(n, 512 + 256);
}
