//! The constraint store's lattices and their solving (DESIGN.md sec:domains and
//! sec:constraints): integer interval unions and the other per-cell domains, the weak
//! topological order, the two-phase iteration strategy with widening and narrowing, and the
//! tonicity and interval-revision tables. Step M0.5 fixes the constants and algorithms these
//! sections leave open; each module names its prelude source.

pub mod interval;
pub mod iterate;
pub mod lattice;
pub mod revision;
pub mod wto;
