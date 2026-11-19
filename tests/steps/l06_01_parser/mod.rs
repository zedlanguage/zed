//! Step L6.1: the parser of the forms of layer L6: `loop` with primes, `with` boundaries,
//! `initial x = e with carryForward;`, the guards `while` and `until` and `break`; indexed
//! definitions, generation pushes `x' <- e`, expression statements `e;` and the call `*.`. Each
//! form builds and formats; name resolution refuses it, naming the step that compiles it.

mod bench;
mod breaks;
mod carry_forward;
mod clause_edges;
mod corners;
mod formatting;
mod forms;
mod initial;
mod initial_reads;
mod initial_reads_shadowed;
mod later;
mod path_parts;
mod scaling;
mod test_case;

use zed_tests::step_helpers::l02_01_parser_structs::{build, check, fmt, refused, sx};
