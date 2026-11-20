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
//! [`fenwick`]: a Fenwick tree, for prefix sums or prefix maxima under changes to single items.

// Loaded for its num-bigint only (see Cargo.toml): nothing here names it, and a crate never named
// is never loaded, so this dylib would carry its own copy of num-bigint beside zed-numtheory's.
extern crate zed_numtheory as _;

pub mod fenwick;
pub mod intervals;
pub mod search;
pub mod sorted;

#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
