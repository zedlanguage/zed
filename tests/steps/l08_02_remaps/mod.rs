//! Remaps (DESIGN.md sec:remap_law, sec:grouping, sec:push_pull, sec:level_names; steps
//! L8.1, L8.2, L8.2a–c and EMPTY-level-swap; plan row REMAP-tests, author P216).
//!
//! `kernel` runs the kernel terms a remap elaborates to on the reference evaluator, so the
//! rules and examples of the spec are checked on values before the source forms compile.
//! COMPLETENESS.md lists each case and the test that covers it.

mod kernel;
