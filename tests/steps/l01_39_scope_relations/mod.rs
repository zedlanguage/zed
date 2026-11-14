//! Step L1.39: the reduced product, second test target. How a scope relates its names: names
//! linked into one component and the blocks a relation is projected by, tests nested in tests,
//! holes in a tree of difference constraints, the checker's difference paths against the
//! solver's, the lazy scope against the eager one, joins of disjoint groups and conditions
//! nested deep; and the suites of the cross-reviews xst and LAZY-hub-xr. The other tests of
//! L1.39, and the step's COMPLETENESS.md, are in l01_39_reduced_product; the folder is split so
//! that an edit to either half rebuilds only that half (rule in docs/layout.md, Tests).

mod deep_condition;
mod disjoint;
mod families;
mod holes;
mod lazy;
mod linked;
mod nests;
mod path_check;
mod seed_edges;
mod two_disjunctions;
mod xst;

pub(crate) use zed_tests::step_helpers::l01_39_reduced_product::{arms_of, ints};
