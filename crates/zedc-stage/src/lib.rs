//! The build-stage terms of the compiler `zedc` (DESIGN.md sec:staging): a unit's definitions and
//! tests, the cones of definitions each demands, and their evaluation at build time. `zedc`
//! re-exports each module at its old path (`zedc::stage`, ...).

pub mod defs;
pub mod stage;
