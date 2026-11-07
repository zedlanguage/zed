//! The type checker of the compiler `zedc` (DESIGN.md sec:types): the walk over a unit's
//! declarations, the narrowing and widening of its binders' types, and the reading of written types.
//! `zedc` re-exports the module at its old path (`zedc::check`).

pub mod check;
