//! Operations on sorted lists, and other small data structures, shared by every crate of the
//! workspace (DRY-sorted-structures). It depends on no other crate, so zed-kernel, the lowest of
//! the others, can use it too, and each operation below is written once.
//!
//! [`sorted`]: sorting with duplicates removed, the union of sorted lists in one merge, and the
//! walk of two sorted lists side by side.
//!
//! [`intervals`]: sorted lists of disjoint closed intervals of integers, and their union, meet,
//! difference and complement.

pub mod intervals;
pub mod sorted;
