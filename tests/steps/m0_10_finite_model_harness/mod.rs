//! Step M0.10: the finite-model harness.
//!
//! Every law of the catalog (DESIGN.md sec:optimizer) is run against the reference evaluator
//! of step M0.9 on finite models: each law's two sides, built as the kernel terms a program
//! elaborates to, must agree on every instance, and each side condition comes with the
//! counterexample that makes it necessary, an instance on which the sides differ once the
//! condition is dropped. Beside the laws: witness bijectivity (`witnesses`), the recursion
//! checks (`recursion`), and the metatheory smoke cases (`smoke`).
//!
//! The instances are exhaustive enumerations in shortlex order up to the rung 6 bounds of
//! `zed_kernel::budgets`, with at most `ENUMERATION_BUDGET` per law, plus
//! `RANDOM_INSTANCES` seeded random ones beyond those bounds.

mod derived;
mod laws_01_10;

use zed_kernel::Value;
use zed_kernel::budgets::ENUMERATION_BUDGET;
use zed_kernel::term::build::lit;
use zed_kernel::{Family, Term};
use zed_tests::instances::{RANDOM_INSTANCES, Rng, map_value, partial_maps, seq_value};

/// A one-level family of integers, as its entries in key order.
type IntMap = Vec<(i64, i64)>;

/// The integer maps every law over one level runs on: all 1,296 partial maps from the keys
/// `0..4` to the values `-2..=2`, then random maps over the keys and values `-8..=8`.
fn int_maps(seed: u64) -> Vec<IntMap> {
    let mut out = partial_maps(&[0, 1, 2, 3], &[-2, -1, 0, 1, 2]);
    let mut rng = Rng::new(seed);
    for _ in 0..RANDOM_INSTANCES {
        let mut m = Vec::new();
        for k in -8..=8 {
            if rng.below(3) == 0 {
                m.push((k, rng.int(-8, 8)));
            }
        }
        out.push(m);
    }
    assert!(out.len() as u64 <= ENUMERATION_BUDGET);
    out
}

/// The map as a literal family term.
fn ints(m: &[(i64, i64)]) -> Term {
    lit(map_value(m))
}

/// A sequence as a literal family term `0..n -> x`.
fn seq<T: Clone + Into<Value>>(xs: &[T]) -> Term {
    lit(seq_value(xs))
}

/// A literal family from its entries, each a value already.
fn family(entries: Vec<(Value, Value)>) -> Term {
    lit(Value::Family(Family::of(entries)))
}
