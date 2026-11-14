//! The benchmarks of steps L1.26a and L1.26b, run by `tools/run_tests.sh --bench` and left out
//! of its default run (TEST-bench-split, TEST-bench-move-l0126). Each file holds the benchmarks
//! of the file of the same name one level up, and each check they make besides the ratio has a
//! small instance among the correctness tests there.

mod call_union_at_f64;
mod cast_int_f64;
mod cast_of_union;
mod cast_rat_int;
mod lit_branch_ops;
mod lit_branches;
mod name_fixed;
mod param_follows;
mod parts_type;
mod scaling;
mod spelling;
mod top_body_agree;
mod tuple_arg_pair;
mod tuple_rest;
mod tuples;
mod two_union_operands;
mod written;
