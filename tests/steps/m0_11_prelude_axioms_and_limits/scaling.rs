//! The law the benchmark of `bench.rs` checks, and the count of triples checking it must give,
//! checked here at small widths (TEST-bench-move-rest, P170).

use zedc::axioms::{AXIOMS, Axiom, Law};

use super::axioms::check_word;

/// The associativity of `bitXor`.
pub(super) fn bitxor_associative() -> &'static Axiom {
    AXIOMS
        .iter()
        .find(|a| a.op == "bitXor" && a.law == Law::Associative)
        .expect("bitXor is associative by axiom")
}

/// The harness checks the law on each of the 8^w triples of `w`-digit values, and it holds.
pub(super) fn checks_every_triple(assoc: &Axiom, w: u32) {
    assert_eq!(check_word(assoc, w), Ok(1 << (3 * w)));
}

#[test]
fn the_harness_checks_each_triple_of_a_narrow_word_once() {
    for w in 1..=3 {
        checks_every_triple(bitxor_associative(), w);
    }
}
