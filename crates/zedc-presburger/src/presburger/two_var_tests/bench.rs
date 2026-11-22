//! The benchmark of `two_var_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. The correctness test that keeps small instances of it is
//! `chains_of_unit_equalities_project_exactly_in_either_order`.

use super::*;
use crate::scaling;

/// [`two_var_domains`] on [`chain`] with `e` equalities, given in order: each substitution
/// meets the two rows that hold its atom, O(e log e) in all (the work list and the rows that
/// hold each atom, comment at the elimination in `two_var_domains`). Before, each read every
/// row, O(e²).
#[test]
fn a_chain_of_unit_equalities_scales() {
    let inputs = scaling::inputs(N_CHAIN, |e| chain(e, false));
    let sym = [xa(0)];
    scaling::check_order(
        "a chain of unit equalities in two_var_domains",
        N_CHAIN,
        1,
        |e| {
            let (each, _) = two_var_domains(&inputs[&e], &sym).expect("two_var_domains answers");
            assert_eq!(each[0].as_ref().expect("a domain"), &expected(e));
        },
    );
}

/// The size of [`a_chain_of_unit_equalities_scales`].
const N_CHAIN: usize = 2_000;
