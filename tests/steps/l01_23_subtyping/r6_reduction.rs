//! The R6 selector reduction, a piece of its own beside the original agreement suite. Until
//! TEST-bench-move-l0123 it checked the 384 formulas of one fixed seed, in four quarters of 4 to
//! 5 s each (one piece of all 384 took 38 s to 77 s by load); now 12 random ones, new each run
//! (author P169).
#[test]
fn two_predicate_reduction_matches_boolean_bruteforce() {
    super::sweep_agreement::r6_two_predicate_reduction_matches_boolean_bruteforce(12);
}
