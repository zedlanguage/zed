//! The constraint store's lattices and their solving (DESIGN.md sec:domains and
//! sec:constraints): integer interval unions and the other per-cell domains, the weak
//! topological order, the two-phase iteration strategy with widening and narrowing, the
//! tonicity and interval-revision tables, and the cell that holds a fact's elements with the
//! premises each rests on (step L1.24). Step M0.5 fixes the constants and algorithms these
//! sections leave open; each module names its prelude source.

pub use zedc_int::int;
pub use zedc_lattice::affine;
pub use zedc_lattice::cell;
pub use zedc_lattice::float;
pub use zedc_lattice::interval;
pub use zedc_lattice::iterate;
pub use zedc_lattice::landmarks;
pub use zedc_lattice::lattice;
pub use zedc_lattice::revision;
pub use zedc_lattice::wto;
pub use zedc_preimage::images;
pub use zedc_preimage::preimage;
/// The backward transfer before S22a, which tests compare [`preimage`] with. Built only with
/// the feature `preimage-ref`, which only zed-tests enables.
#[cfg(feature = "preimage-ref")]
#[doc(hidden)]
pub use zedc_preimage::preimage_ref;
pub use zedc_preimage::product;
pub use zedc_presburger::conjuncts;
pub use zedc_presburger::hull;
pub use zedc_presburger::presburger;
pub use zedc_solvers::linear;
pub use zedc_solvers::live3;
pub use zedc_solvers::negsssp;
pub use zedc_solvers::twovar;
pub use zedc_solvers::utvpi;
