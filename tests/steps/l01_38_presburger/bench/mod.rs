//! The benchmarks of step L1.38, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-split, author P169). Each file holds the tests that measured work at two sizes
//! in the file of the same name one level up, which keeps the families they build. A small
//! instance of the check each makes besides the ratio is not yet in a correctness test for every
//! family: those of `one_scope::questions_scale_unit` are
//! (`one_scope::the_chains_of_the_benchmarks_have_no_question_refused_at_small_sizes`), and the
//! rest are listed in plan row TEST-bench-cover-l0138 (author P170).

mod canonical;
mod carrier;
mod cells;
mod checker;
mod deep;
mod disj_groups;
mod exclusive_cases;
mod exp_families;
mod extend;
mod front_cost;
mod ids;
mod ladder;
mod linked_nest;
mod live3;
mod mod_symbol;
mod model;
mod names;
mod near;
mod nest_empty;
mod omega;
mod one_row;
mod one_scope;
mod pncx_probe;
mod probe;
mod q1_local;
mod repair;
mod scaling;
mod shared;
mod slack_scale;
mod small_cost;
mod stages;
mod tight;
