//! Step L1.37a: truncated content addresses collide, and results do not change. The
//! `short-addresses` feature of `zed-kernel` keeps 8 bits of every content address and digest
//! (`zed_kernel::address`), so distinct values collide often. Every place that compares by
//! address falls back to comparing contents on equal addresses, and nothing is ordered by an
//! address alone, so the build with the feature gives the verdicts and outputs of the full
//! build: the snapshots of `record` are the same file in both builds.
//!
//! The feature build is run over this group and `l01_37_oracle`, each test under 60 s. Tests
//! of the address function itself (that distinct graphs have distinct addresses, the pinned
//! address of `l01_32_canonical_zir`) and the scaling tests, whose costs assume few collisions,
//! are for the full build only.

mod cex;
mod collide;
mod record;
mod scaling;
