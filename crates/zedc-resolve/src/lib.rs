//! Name resolution of the compiler `zedc` (DESIGN.md sec:names): the resolver, its tables and the
//! topological order of declarations, and the documentation comments it attaches. `zedc`
//! re-exports each module at its old path (`zedc::resolve`, `zedc::docs`).

pub mod docs;
pub mod resolve;
