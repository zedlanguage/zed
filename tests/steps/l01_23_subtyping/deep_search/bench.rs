//! The benchmarks of `deep_search.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_search.rs`.

use super::*;

#[test]
fn deciding_and_comparing_deep_tuple_types_scale_with_depth() {
    scales("tuples", tuples);
}

#[test]
fn deciding_and_comparing_deep_atom_types_scale_with_depth() {
    scales("atoms", atoms);
}

#[test]
fn deciding_and_comparing_deep_morphism_types_scale_with_depth() {
    scales("morphisms", morphisms);
}
