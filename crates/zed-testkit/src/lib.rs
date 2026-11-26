//! The seed of a random test ([`seed`]) and the scaling test of the rule of low complexity
//! ([`scaling`]), shared by the tests of every crate as a dev-dependency, and by the step tests
//! through `zed_tests::seed` and `zed_tests::scaling` (DRY-testkit-2026-11-26).
//!
//! A test binary that measures with [`scaling`] also calls `zed_alloc_count::meter_entry_points!()`
//! once, as zed-tests and each library crate's tests do: the meter's `malloc` must be in the
//! binary itself.

pub mod scaling;
pub mod seed;
