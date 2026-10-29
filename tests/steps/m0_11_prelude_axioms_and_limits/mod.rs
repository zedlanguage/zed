//! Step M0.11: three artifacts moved forward from step S.3 because L1–L3 use them, each with its
//! prelude source in `zed/prelude/`: the laws each built-in operator carries by axiom
//! (`axioms.zed`, `zedc::axioms`), how a unit is addressed (`unit.zed`,
//! `zedc::canon::unit_address`), and the minimum resource limits of compile-time evaluation
//! (`limits.zed`, `zed_kernel::eval::MIN_*`).

mod axioms;
mod limits;
mod units;
