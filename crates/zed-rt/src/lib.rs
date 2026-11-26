//! The Zed runtime: what natively compiled Zed code links against (DESIGN.md sec:runtime,
//! sec:memory, sec:ports).
//!
//! It grows with the back end. At L1 (step L1.36) it holds the value words native code
//! passes, the counted heap their cells live in, with precise reference counts under the
//! memory plan of step L1.34, strings as the kernel's rope-backed `Text`, pattern matching over
//! cells, the port runtime of a wave, and the stack a run switches to (`stack`); work stealing
//! with heartbeat promotion and the wave scheduler come at the layers that need them. The
//! interpreter in `zedc` does not use this crate, so the differential oracle (step L1.37)
//! compares two independent implementations, except for strings: both use the kernel's `Text`,
//! so the oracle does not test it.

mod bug;
pub mod close;
pub mod code;
pub mod heap;
pub mod limits;
mod line;
pub mod ports;
pub mod stack;

/// The scaling test of the rule of low complexity, shared with the step tests, for the
/// benchmarks of `stack`.
#[cfg(test)]
use zed_testkit::scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();

pub use bug::bug;
pub use heap::{FunObj, Heap, HeldObj, HeldShape, Obj, Parts, Stats, Word};
#[cfg(feature = "counts")]
pub use heap::{Released, Survivor};
// What `Heap::matches` records and `Heap::release` reads, shared with the counting machine.
pub use stack::Stack;
pub use zed_kernel::paths::Paths;
