//! Step L1.33: kernel terms lowered to ZIR. Every test row of every corpus unit lowers to a
//! valid graph whose raised term has the original's value; repeated subexpressions are one
//! node; ports thread one state edge each through the regions that touch them; and a term the
//! graph cannot hold is refused with the reason.

mod asks;
mod bench;
mod corpus;
mod cse;
mod errors;
mod forms;
mod ports;
pub(crate) mod scaling;

use zed_kernel::Term;
use zedc::elab::Unit;
use zedc::zir::Region;
use zedc::zir::lower::lower;

pub(crate) use zed_tests::step_helpers::l01_16_elaboration::elab;
pub(crate) use zed_tests::step_helpers::l01_33_lowering::{count, eval, round_trip};

/// `t` closed over the definitions of `u` and the prelude words.
pub(crate) fn closed(u: &Unit, t: Term) -> Term {
    zedc::interp::prelude(u.close(t))
}

/// The graph of definition `name` of the unit `text`.
pub(crate) fn graph(text: &str, name: &str) -> Region {
    let u = elab(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let t = closed(&u, Term::Var(kernel(&u, name)));
    lower(&t).unwrap_or_else(|e| panic!("{name}: {e}"))
}

/// The kernel name of definition `name`.
pub(crate) fn kernel(u: &Unit, name: &str) -> std::sync::Arc<str> {
    let d = u.defs.iter().find(|d| d.name == name);
    d.unwrap_or_else(|| panic!("no definition `{name}`"))
        .kernel
        .clone()
}
