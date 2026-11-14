//! Step M0.11: three artifacts moved forward from step S.3 because L1–L3 use them, each with its
//! prelude source in `zed/prelude/`: the laws each built-in operator carries by axiom
//! (`axioms.zed`, `zedc::axioms`), how a unit is addressed (`unit.zed`,
//! `zedc::canon::unit_address`), and the limits of compile-time evaluation
//! (`limits.zed`, `zed_kernel::eval::MIN_NESTED_CALLS`): the minimum depth of nested calls, with no
//! minimum of steps or of memory.

mod axioms;
mod bench;
mod cases;
mod fail_limits_steps_memory;
mod leaves;
mod limits;
mod scaling;
mod signed_zero;
mod units;
