//! Step L1.38: the linear-relation domain (DESIGN.md sec:domains, "linear-integer relations
//! among in-scope keys and cardinalities (Presburger)", and sec:verification, rung 2).
//!
//! `entailment` checks rung 2 on the facts the design names, written as Zed functions:
//! `y * w + x < h * w` follows from `0 <= y < h` and `0 <= x < w`, and not from `y <= h`.
//! `preimage` checks the z3 fixtures and the relation a non-box preimage keeps. `random`
//! checks the translation, the Omega test, the projection and entailment against the
//! interpreter at every point of a window, and `controls` checks that a relation of any size is
//! decided, that a question outside the polynomial fragment is refused, and that each check of
//! `random` rejects a wrong answer. `omega` holds the solver's corner cases, and `repair` the
//! greedy search over disjunctions and its repair of one disjunct.
//!
//! The step has two test binaries (TESTS-split, author A30): `omega`, `repair`, `preimage`,
//! `scaling`, `stages`, `one_scope`, `extend` and the modules that use them are in
//! l01_38_omega_test.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod bench;
mod canonical;
mod carrier;
mod cell_sweep;
mod cell_sweep_nested;
mod cells;
mod checker;
mod controls;
mod deep;
mod entailment;
mod exclusive_cases;
mod exp_families;
mod ground;
mod ids;
mod kept_constants;
mod ladder;
mod linked_nest;
mod memo;
mod mod_symbol;
mod near;
mod nest_empty;
mod one_row;
mod oracle;
mod pncx_probe;
mod product_parity;
pub(crate) mod random;
mod random_conjuncts;
mod shared;
mod slack_points;
mod slack_scale;
mod slack_unbounded;
mod small_cost;
mod strided;

use zedc::store::preimage::relations;

pub(crate) use zed_tests::step_helpers::l01_38_presburger::points::{
    at, holds, point, projections, window,
};
