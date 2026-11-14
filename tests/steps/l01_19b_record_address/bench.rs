//! A program's content address is taken in O(t log t) for a term of size t, the
//! canonicalizer's cost: measured on a chain of n functions, each calling the one before. The
//! benchmark of this step, run by `tools/run_tests.sh --bench` and left out of its default
//! run; its small instance is `a_chain_of_functions_has_an_address_of_its_own` in `mod.rs`.

use zed_tests::scaling::{self, FACTOR};

use super::chain;

#[test]
fn the_address_of_a_program_scales() {
    let n = 2_000;
    // Both programs are loaded before the runs are measured. The address is taken from the
    // ports and the term, as `Program::address` does, since that caches it after one run.
    let (small, large) = (chain(n), chain(FACTOR * n));
    assert_ne!(small.address().unwrap(), large.address().unwrap());
    scaling::check("the content address of a program of n functions", n, |m| {
        let p = if m == n { &small } else { &large };
        std::hint::black_box(p.ports().address(p.term()).unwrap());
    });
}
