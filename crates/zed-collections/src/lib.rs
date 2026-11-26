//! Operations on sorted lists, and other small data structures, shared by every crate of the
//! workspace (DRY-sorted-structures). It depends on no other crate, so zed-kernel, the lowest of
//! the others, can use it too, and each operation below is written once.
//!
//! [`sorted`]: sorting with duplicates removed, the union of sorted lists in one merge, and the
//! walk of two sorted lists side by side.
//!
//! [`intervals`]: sorted lists of disjoint closed intervals of integers, and their union, meet,
//! difference and complement.
//!
//! [`search`]: binary search for the border of a monotone predicate over a range of integers,
//! and the overflow-free midpoint it halves with.
//!
//! [`fenwick`]: a Fenwick tree, for prefix sums under changes to single items, or prefix maxima
//! under raises of single items (P. M. Fenwick, Software: Practice and Experience 24(3), 1994,
//! doi:10.1002/spe.4380240306; the full comment is at the head of `fenwick.rs`).
//!
//! [`min_add`]: a segment tree over integers, with an addition to a range of items and the
//! search for the first item at or after a place whose value is at most a bound, each O(log n).
//!
//! [`held`]: values put in through a shared reference and kept at their places, so that a walk
//! may borrow from them while it puts in more.
//!
//! [`index`]: a count or index converted to `u32`, refused past `u32::MAX`.
//!
//! [`intern`]: dense ids for distinct values, and the values back by id.
//!
//! [`cartesian`]: the Cartesian tree of items in key order by priority, each node made once over
//! its children, in `O(n)`.
//!
//! [`priority`]: treap priorities drawn at random once per run, by a polynomial of limited
//! independence over the prime `2^64 - 59` (Seidel and Aragon 1996; the full comment and the
//! proofs are at the head of `priority.rs`), and the two primes of the kernel's fingerprints.
//!
//! [`by_address`]: a map key that is the address of an `Arc` and holds it, so no address in a
//! memo is freed and given to another value while the memo lives.
//!
//! [`period`]: the least period of a sequence that is a whole number of copies of a block, by
//! the prefix function, O(n).
//!
//! [`spelling`]: the spelling index of step L1.29e, the name near in spelling to each written
//! name of a unit and visible at its site, for all of them together in `O(n log n)`.

// Loaded for its num-bigint only (see Cargo.toml): nothing here names it, and a crate never named
// is never loaded, so this dylib would carry its own copy of num-bigint beside zed-numtheory's.
extern crate zed_numtheory as _;

pub mod by_address;
pub mod cartesian;
pub mod fenwick;
pub mod held;
pub mod index;
pub mod intern;
pub mod intervals;
pub mod min_add;
pub mod period;
pub mod priority;
pub mod search;
pub mod sorted;
pub mod spelling;

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

#[cfg(test)]
mod bench;

#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
