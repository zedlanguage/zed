//! Step L1.38, its second test binary (TESTS-split, author A30; the first is
//! l01_38_presburger): the Omega test and what is built on it. `omega` holds the solver's corner
//! cases, `repair` the greedy search over disjunctions and its repair of one disjunct, `preimage`
//! the z3 fixtures and the relation a non-box preimage keeps, `scaling` and `stages` the families
//! the solver's work is measured on, and `one_scope` and `extend` the relations of one scope and
//! their extension.

mod bench;
mod completeness;
mod decide_sat;
mod disj_groups;
mod equation_sign;
mod extend;
mod front_cost;
mod live3;
mod model;
mod model_keys;
mod names;
mod omega;
mod one_scope;
mod preimage;
mod probe;
mod projection_oracle;
mod q1_local;
mod repair;
pub(crate) mod scaling;
mod stages;
mod tight;

pub(crate) use zed_tests::step_helpers::l01_38_presburger::points::{holds, window};
