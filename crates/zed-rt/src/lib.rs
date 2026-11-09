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
pub mod heap;
pub mod ports;
pub mod stack;

pub use bug::bug;
#[cfg(feature = "counts")]
pub use heap::Survivor;
pub use heap::{Heap, Obj, Stats, Word};
// What `Heap::matches` records and `Heap::release` reads, shared with the counting machine.
pub use stack::Stack;
pub use zed_kernel::paths::Paths;
