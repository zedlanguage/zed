//! The Zed kernel: the seven generators of the kernel calculus (`reindex`, `discard`, `fold`,
//! `fix`, `gen`, `port`, `fam`; DESIGN.md sec:kernel) and the ZIR node inventory built on them
//! (sec:ir).
//!
//! Every surface form elaborates to these terms, so this crate is the contract between the
//! front end, which produces kernel terms, and every back end, which consumes them. Step M0.9
//! adds the executable small-step reference evaluator here; the inventory is fixed by M0 and
//! built whole at L1 (steps L1.15 and L1.31), so later layers add no term and no node kind.
