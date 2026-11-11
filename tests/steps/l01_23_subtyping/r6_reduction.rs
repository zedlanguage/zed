//! The R6 selector reduction gets separate test pieces so the original agreement suite and
//! each quarter of these 384 formulas stay within the runner's per-piece time limit (one piece
//! of all 384 took 38 s to 77 s by load, and 90 s in a full suite at load 48).
#[test]
fn two_predicate_reduction_matches_boolean_bruteforce_first_quarter() {
    super::sweep_agreement::r6_two_predicate_reduction_matches_boolean_bruteforce(0..96);
}

#[test]
fn two_predicate_reduction_matches_boolean_bruteforce_second_quarter() {
    super::sweep_agreement::r6_two_predicate_reduction_matches_boolean_bruteforce(96..192);
}

#[test]
fn two_predicate_reduction_matches_boolean_bruteforce_third_quarter() {
    super::sweep_agreement::r6_two_predicate_reduction_matches_boolean_bruteforce(192..288);
}

#[test]
fn two_predicate_reduction_matches_boolean_bruteforce_fourth_quarter() {
    super::sweep_agreement::r6_two_predicate_reduction_matches_boolean_bruteforce(288..384);
}
