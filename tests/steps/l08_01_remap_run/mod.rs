//! Remaps compiled and run (DESIGN.md sec:remap_law, sec:grouping, sec:reduction; plan row
//! REMAP-run, author P228, P229): `m as (p)`, `m into (q)` and `m as (p) into (q)` parse to
//! one AST node, resolve, elaborate to the kernel's `reindex`, `discard` and `fold`, check by
//! the bounds table and the collision rule, and run.
//!
//! `parse` covers the syntax: each form builds to its s-expression and formats back, and the
//! forms of later steps (sort keys, joins, named keys, reduction policies) are refused naming
//! what they are.

mod parse;
