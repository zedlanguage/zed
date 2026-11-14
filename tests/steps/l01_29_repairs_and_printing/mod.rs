//! Step L1.29: diagnostics, second test target. The repairs a rejection offers (casts, domains,
//! powers, the menu and its order, values too large), and how types and steps are printed and
//! ordered, with the warnings beside them. The other tests of L1.29, and the step's
//! COMPLETENESS.md, are in l01_29_diagnostics; the folder is split so that an edit to either
//! half rebuilds only that half (rule in docs/layout.md, Tests).

mod bench;
mod casts;
mod domain_repairs;
mod kernel_names;
mod menu_order;
mod offered_repairs;
mod order;
mod parens;
mod power_repairs;
mod printed;
mod rare;
mod refused_in_rejection;
mod refused_warning;
mod rejection_addresses;
mod repairs;
mod scaling;
mod stable;
mod suppress;
mod too_large;
mod type_size;
mod widen_test;

pub(crate) use zed_tests::step_helpers::l01_29_diagnostics::{rejected, steps};
