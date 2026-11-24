//! Step L1.29: diagnostics. A rejection shows its derivation: each type constraint and each
//! step of propagation that led to it, numbered and placed in the source, the declarations
//! and signatures it met, every failing combination of a signature search, and the repairs
//! the checker discharges.
//!
//! The tests of the repairs and of how types and steps are printed and ordered are in
//! l01_29_repairs_and_printing, a test target of its own (rule in docs/layout.md, Tests).
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod above;
mod always_fails;
mod batch;
mod bench;
mod binder_type;
mod body_display;
mod bug;
mod completeness;
mod declared;
mod derivations;
mod emptied;
mod explained;
mod fold_machine;
mod follow_on;
mod fresh_names;
mod group_site;
mod kinds;
mod layout;
mod literal_steps;
mod main_limits;
mod markers;
mod member_headline;
mod negative_literals;
mod neglit;
mod overload_cycles;
mod package_recovery;
mod quoted;
mod recursion;
mod shared_parts;
mod shared_print;
mod sum_plus;
mod syntax_recovery;
mod too_large_literal;
mod top_statements;
mod tyvars;
mod untracked;
mod variants;
mod widen;

pub(crate) use zed_tests::step_helpers::l01_29_diagnostics::{rejected, steps};
