//! The Zed runtime: what natively compiled Zed code links against (DESIGN.md sec:runtime,
//! sec:memory, sec:ports).
//!
//! It grows with the back end: the port runtime and precise reference counting at L1
//! (steps L1.34 and L1.36), work stealing with heartbeat promotion and the wave scheduler at
//! the layers that need them. The interpreter in `zedc` does not use this crate, so the
//! differential oracle (step L1.37) compares two independent implementations.
