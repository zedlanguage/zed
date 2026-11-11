//! Step L1.23: semantic subtyping. `a <: b` iff `a & !b` is empty, decided by a memoized
//! coinductive check; recursive definitions are checked for contractivity, regularity and
//! monotonicity in emptiness when they are defined. The check is compared with an exact oracle
//! over random types, and run on the spec's examples and on recursive types. The four
//! definitions the plan names are written here as kernel definition groups: `type`
//! declarations, which elaborate to them, join at L2.

mod admission;
mod admission_sweep;
mod bes;
mod bes_families;
mod bound_paths;
mod bound_sameness;
mod cases;
mod cells;
mod cycle_dup;
mod deep_rec;
mod group_oracle;
mod group_refusal;
mod judgments;
mod listing;
mod meet_join_oracle;
mod one_pass;
mod oracle;
mod r6_reduction;
mod rec;
mod rec_order;
mod refusals;
mod scaling;
mod setop;
mod sweep_agreement;
mod two_sat;
mod witnesses;
mod x13;
