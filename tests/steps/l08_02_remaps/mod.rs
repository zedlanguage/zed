//! Remaps (DESIGN.md sec:remap_law, sec:grouping, sec:push_pull, sec:level_names; steps
//! L8.1, L8.2, L8.2a–c and EMPTY-level-swap; plan rows REMAP-tests and REMAP-run, author P216,
//! P228, P229).
//!
//! `kernel` runs the kernel terms a remap elaborates to on the reference evaluator, so the
//! rules and examples of the spec are checked on values apart from the source forms.
//! `moves`, `collisions` and `source` write the same rules and examples in source form; the
//! cases of later steps (join patterns, tuple sources, level names: L8.2a–c) assert the
//! refusal naming their step. `rules` holds the small tests of each rule of step L8.2,
//! `group` and `rekey` among them, and `bench` its scaling benchmarks (run with `--bench`).
//! COMPLETENESS.md lists each case and the test that covers it.
mod bench;
mod collisions;
mod kernel;
mod moves;
mod names;
mod rules;
mod source;
