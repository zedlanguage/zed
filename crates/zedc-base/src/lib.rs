//! The bottom of the compiler `zedc`: the modules every other part reads and that read no other
//! part. Content addresses, source loading, the interpreter's limits, fences, the axioms, the
//! cost model, the rejection catalog and the work recorder. `zedc` re-exports each module at its
//! old path (`zedc::address`, ...).

pub mod address;
pub mod axioms;
pub mod cost;
pub mod fence;
pub mod interp;
pub mod rejection;
pub mod source;
pub mod work;
