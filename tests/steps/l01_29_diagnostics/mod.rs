//! Step L1.29: diagnostics. A rejection shows its derivation: each type constraint and each
//! step of propagation that led to it, numbered and placed in the source, the declarations
//! and signatures it met, every failing combination of a signature search, and the repairs
//! the checker discharges.
//!
//! The tests of the repairs and of how types and steps are printed and ordered are in
//! l01_29_repairs_and_printing, a test target of its own (rule in docs/layout.md, Tests).

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
mod sum_plus;
mod syntax_recovery;
mod tyvars;
mod untracked;
mod variants;
mod widen;

pub(crate) use zed_tests::step_helpers::l01_29_diagnostics::{rejected, steps};
