//! Step L1.16: elaboration of the L1 surface to kernel terms. Each program is elaborated and
//! its definitions evaluated by the kernel evaluator; where a term's shape is the point, it is
//! printed; and each error elaboration reports has a case.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod bench;
mod calls;
mod complete;
mod displays;
mod errors;
mod handled;
mod kept;
mod order;
mod programs;
mod scaling;

pub(crate) use zed_tests::step_helpers::l01_16_elaboration::{
    Checked, checked, elab, errors, term, value, with_prelude,
};
