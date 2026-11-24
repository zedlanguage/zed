//! Step L1.39: the reduced product (DESIGN.md sec:domains and sec:constraints).
//!
//! Each name in scope holds a product of its cell, its type and its binding time, and the
//! scope holds the linear relation and the written constraints. `spec` checks the design's
//! examples: an arm whose test fixes `n mod 4 == 1` within `0..=10` holds `n` in `1..=9`, an
//! arm whose test no value meets is unreachable and the program is accepted, and a binding
//! read from a static `if` is static. `random` checks against the interpreter that each
//! arm's scope holds every value that reaches it and that no value reaches an unreachable
//! arm, and `controls` checks each reduction.
//!
//! The tests of how a scope relates its names (linked components, nested tests, holes in
//! difference constraints, the lazy scope) and the suites of the cross-reviews xst and
//! LAZY-hub-xr are in l01_39_scope_relations, a test target of its own (rule in
//! docs/layout.md, Tests).
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod arm_test_through_call;
mod class_unions;
mod completeness;
mod controls;
mod deep_let;
mod exact;
mod finite_from_type;
mod follow;
mod generic_need_arm;
mod helpers;
mod hull;
mod if_shortcut;
mod let_terms;
mod listed_shortcuts;
mod loops;
mod named_test;
mod pendants;
mod pow_nan;
mod random;
mod ranges;
mod refused;
mod roots;
mod scaling;
mod spec;
mod written_address;

use std::sync::Arc;

use zedc::store::product::{Arm, arms};

pub(crate) use zed_tests::step_helpers::l01_39_reduced_product::{
    arm, arms_of, binding, generic_arms_of, ints,
};
