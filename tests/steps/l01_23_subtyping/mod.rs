//! Step L1.23: semantic subtyping. `a <: b` iff `a & !b` is empty, decided by a memoized
//! coinductive check; recursive definitions are checked for contractivity, regularity and
//! monotonicity in emptiness when they are defined. The check is compared with an exact oracle
//! over random types, and run on the spec's examples and on recursive types. The four
//! definitions the plan names are written here as kernel definition groups: `type`
//! declarations, which elaborate to them, join at L2.
//!
//! The step has two test binaries (TESTS-split, author A30): the refusals, the decider of
//! recursive groups, the front sweep's oracle and the spec's examples are in
//! l01_23_groups_and_refusals.

mod admission;
mod admission_sweep;
mod arrow_keys;
mod bound_paths;
mod bound_sameness;
mod cells;
mod deep_rec;
mod group_refusal;
mod listing;
mod meet_join_oracle;
mod one_pass;
mod oracle;
mod payload_scaling;
mod printed_meets;
mod rec;
mod rec_order;
mod refusal_cost;
mod scaling;
mod setop;
mod two_sat;
mod witnesses;
mod x13;
