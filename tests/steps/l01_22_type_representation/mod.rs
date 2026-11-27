//! Step L1.22: types as sets of values, with union, intersection, difference and complement
//! taken within each universe; tuple, atom and morphism types; and the `is` test, which
//! elaborates to a match on a type. The connectives are checked against membership computed
//! from the type expression itself, over a sample of values from every universe.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod complete;
mod exact_sets_study;
mod forms;
mod is;
mod kinds;
mod laws;
mod rat_literals;
mod scaling;
mod surface;
mod table_life;
