//! Step L1.26: resolution rules 1, 3 and 4. Each declared function gets a signature from its
//! body; a bare numeric literal adopts the carrier an operator or a parameter expects,
//! exactly or not at all; an `is` test narrows the name it tests; a function argument fits
//! the function type its slot expects.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod adoption;
mod always_fails;
mod atom_scaling;
mod bench;
mod boundaries;
mod bounds;
mod bubble;
mod calls;
mod curried_classes;
mod cycles;
mod dead_arms;
mod deep_ops;
mod deep_scaling;
mod deep_types;
mod divisors;
mod docs;
mod else_difference;
mod exact_casts;
mod fits;
mod function_variance;
mod given;
mod handled;
mod held_functions;
mod internal_result_names;
mod is_chains;
mod kept_checks;
mod literals;
mod named_calls;
mod narrowing;
mod never;
mod never_operands;
mod no_common_value;
mod op_table;
mod ordered_tuples;
mod out_of_bounds;
mod partial_maps;
mod payload_variables;
mod random;
mod range_elements;
mod ranges;
mod scaling;
mod shared_tuples;
mod signatures;
mod soundness;
mod standing_twice;
mod tuple_keys;

pub(crate) use zed_tests::step_helpers::l01_26_type_resolution::{
    Resolved, info, menu, sig, sig_of, tried, type_errors,
};

/// Each test of this binary gives the C library's free memory back to the kernel as it ends
/// (TEST-l01-26-peak-memory): `zed_meter_settings`, linked into every test binary, turns it on as
/// the process starts. Without it, a run of the whole binary on one thread
/// (`--test-threads=1`) held 40,348,564 kB at its peak (Colab, 2026-11-22), each test adding the
/// free pages it left in glibc's arenas to the next one's peak, where no test alone reaches
/// 3.0 GB; the mechanism's own test is `a_test_gives_back_what_it_freed_when_it_ends` in
/// crates/zed-alloc-count/tests/zed_alloc_count.rs.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn each_test_gives_back_its_free_memory_as_it_ends() {
    assert!(zed_alloc_count::gives_back());
}
