//! The benchmarks of step L1.26, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-split, TEST-bench-move-l0126). Each file holds the benchmarks of the file of
//! the same name one level up, and each check they make besides the ratio has a small instance
//! among the correctness tests there.

mod always_fails;
mod atom_scaling;
mod bounds;
mod cycles;
mod deep_ops;
mod deep_scaling;
mod deep_types;
mod divisors;
mod docs;
mod exact_casts;
mod fits;
mod function_variance;
mod given;
mod held_functions;
mod is_chains;
mod literals;
mod named_calls;
mod never_operands;
mod no_common_value;
mod ordered_tuples;
mod partial_maps;
mod payload_variables;
mod ranges;
mod scaling;
mod shared_tuples;
mod soundness;
mod standing_twice;
mod tuple_keys;
