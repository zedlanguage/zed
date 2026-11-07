//! The intermediate representation of the compiler `zedc` (DESIGN.md sec:ir): the canonical form of
//! a program's definitions and its content addresses, and ZIR with its lowering, legalization,
//! validation, memory layout and text and binary forms. `zedc` re-exports each module at its old
//! path (`zedc::canon`, `zedc::zir`).

pub mod canon;
pub mod zir;
