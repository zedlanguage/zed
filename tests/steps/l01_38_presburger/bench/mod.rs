//! The benchmarks of step L1.38, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-split, author P169). Each file holds the tests that measured work at two sizes
//! in the file of the same name one level up, which keeps the families they build. The check each
//! makes besides the ratio also runs at small sizes in a correctness test of that file, named
//! `the_families_of_the_benchmarks_are_answered_at_small_sizes` or after the families it checks
//! (TEST-bench-cover-l0138, author P170).

mod canonical;
mod carrier;
mod cell_sweep;
mod cells;
mod checker;
mod deep;
mod exclusive_cases;
mod exp_families;
mod ids;
mod ladder;
mod linked_nest;
mod mod_symbol;
mod near;
mod nest_empty;
mod one_row;
mod oracle;
mod pncx_probe;
mod product_parity;
mod shared;
mod slack_scale;
mod small_cost;
mod strided;
