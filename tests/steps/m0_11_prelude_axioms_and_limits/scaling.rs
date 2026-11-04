//! The finite-model harness checks a bit word's law in work linear in the tuples it checks: the
//! associativity of `bitXor` on the 8^w triples of the `w`-digit values, at 8^6 and 8^7
//! triples. The table of the word costs 4^w evaluations, below the triples' count.

use zed_tests::scaling::check_order;
use zedc::axioms::{AXIOMS, Law};

use super::axioms::check_word;

#[test]
fn the_harness_is_linear_in_the_tuples_it_checks() {
    let assoc = AXIOMS
        .iter()
        .find(|a| a.op == "bitXor" && a.law == Law::Associative)
        .expect("bitXor is associative by axiom");
    check_order(
        "harness: bitXor associative at n triples",
        1 << 18,
        1,
        |n| {
            let w = n.ilog2() / 3;
            assert_eq!(n, 1 << (3 * w), "a count of triples is 8^w");
            assert_eq!(check_word(assoc, w), Ok(n));
        },
    );
}
