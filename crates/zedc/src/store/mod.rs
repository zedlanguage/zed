//! The constraint store's lattices and their solving (DESIGN.md sec:domains and
//! sec:constraints): integer interval unions and the other per-cell domains, the weak
//! topological order, the two-phase iteration strategy with widening and narrowing, the
//! tonicity and interval-revision tables, and the cell that holds a fact's elements with the
//! premises each rests on (step L1.24). Step M0.5 fixes the constants and algorithms these
//! sections leave open; each module names its prelude source.

pub use zedc_lattice::affine;
pub use zedc_lattice::cell;
pub mod conjuncts;
pub use zedc_lattice::float;
pub mod hull;
pub use zedc_int::int;
pub use zedc_lattice::interval;
pub use zedc_lattice::iterate;
pub use zedc_lattice::landmarks;
pub use zedc_lattice::lattice;
pub mod linear;
pub mod live3;
pub mod negsssp;
pub mod preimage;
/// The backward transfer before S22a, which tests compare [`preimage`] with.
#[doc(hidden)]
pub mod preimage_ref;
pub mod presburger;
pub mod product;
pub use zedc_lattice::revision;
pub mod twovar;
pub mod utvpi;
pub use zedc_lattice::wto;
