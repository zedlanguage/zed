//! Algorithms on wide integers (`BigUint`, `BigInt`) that every crate shares: products,
//! division, gcd, printing and reading in [`fast`]; product and remainder trees in [`trees`];
//! Bernstein's coprime base in [`coprime`]; least roots in [`least_root`]; outward-rounded
//! bounds of `m * 2^e` in [`approx`]; rounding to a whole number by a named rule and exact
//! weighted splits in [`round`]. Moved down from zed-kernel's `num`
//! (DRY-bignum-crate-2026-11-26), which re-exports them, and from zedc-int
//! (DRY-bignum-bound-type), so that zedc-int and the kernel call one copy and the kernel's build
//! does not compile them.

pub mod approx;
pub mod coprime;
pub mod digit_text;
pub mod fast;
pub mod least_root;
pub mod round;
pub mod trees;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
use zed_testkit::scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;

/// The crossover tests of [`fast`] (plan row TEST-complete-kernel), moved with it.
#[cfg(test)]
mod completeness;

/// The benchmarks set for the unit build's small leaves, moved from zed-kernel.
#[cfg(test)]
mod bench;
