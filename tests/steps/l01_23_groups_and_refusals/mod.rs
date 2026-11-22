//! Step L1.23, its second test binary (TESTS-split, author A30; the first is l01_23_subtyping):
//! the refusals of the emptiness check and the decider of recursive groups. `refusals` and
//! `cycle_dup` check each cause of a refusal and the types that once hung the search, `bes`,
//! `bes_families`, `judgments`, `group_oracle` and `complete` the decider against the Büchi game
//! reference, `sweep_agreement` and `r6_reduction` the front sweep against an oracle, and
//! `cases` the spec's subtyping examples.

mod bes;
mod bes_families;
mod cases;
mod cell_order_sweep;
mod complete;
mod cycle_dup;
mod group_oracle;
mod judgments;
mod nested_cover;
mod r6_reduction;
mod refusals;
mod sweep_agreement;
