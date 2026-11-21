//! The type checker of the compiler `zedc` (DESIGN.md sec:types): the walk over a unit's
//! declarations, the narrowing and widening of its binders' types, and the reading of written
//! types. `zedc` re-exports the module at its old path (`zedc::check`).

pub mod check;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "the benchmarks use only some of the shared checks"
)]
mod scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();
