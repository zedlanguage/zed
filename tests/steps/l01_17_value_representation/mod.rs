//! Step L1.17: the representation of values. Integers are unbounded and rationals exact;
//! every value has a place in one total order, numbers by value across kinds; the language's
//! `==` is IEEE 754 at floats and the bitwise identity of keys elsewhere; an atom carries a
//! payload by position or by name; and `==` on functions waits for the enumerable domain
//! their types give.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod asks;
mod atoms;
mod bench;
mod completeness;
mod edges;
mod equality;
mod fields;
mod function_in_family;
mod function_in_payload_run;
mod function_in_tuple;
mod in_place;
pub(crate) mod memory_check;
mod numbers;
mod order;
mod powers;
mod products;
mod string_copies;
mod subquadratic;
