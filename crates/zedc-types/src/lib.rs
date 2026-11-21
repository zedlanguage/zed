//! The types of the compiler `zedc`'s checker (DESIGN.md sec:types): the checker's type, its
//! signatures and classes, its printing, and the kernel type a written type denotes. `zedc`
//! re-exports each module at its old path (`zedc::check::ty`, ...).

pub mod forms;
pub mod kernel_type;
pub mod ty;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "this crate's benchmarks use only some of the shared checks"
)]
mod scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();
