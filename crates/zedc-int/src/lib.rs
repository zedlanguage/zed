//! The integers of the compiler `zedc`'s constraint store: [`int::Int`], a machine word until it
//! overflows, then a big integer. `zedc` re-exports the module at its old path (`zedc::store::int`).

pub mod int;
