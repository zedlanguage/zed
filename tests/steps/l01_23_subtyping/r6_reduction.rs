//! The R6 selector reduction gets a separate test piece so the original agreement
//! suite and this check each stay within the runner's per-piece time limit.
#[test]
fn two_predicate_reduction_matches_boolean_bruteforce() {
    super::sweep_agreement::r6_two_predicate_reduction_matches_boolean_bruteforce();
}
