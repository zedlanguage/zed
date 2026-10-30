//! Step L1.33: kernel terms lowered to ZIR. Every test row of every corpus unit lowers to a
//! valid graph whose raised term has the original's value; repeated subexpressions are one
//! node; ports thread one state edge each through the regions that touch them; and a term the
//! graph cannot hold is refused with the reason.

mod corpus;
mod cse;
mod errors;
mod forms;
mod ports;
mod scaling;

use zed_kernel::{Evaluator, Term, World};
use zedc::elab::Unit;
use zedc::zir::Region;
use zedc::zir::lower::{lower, raise};

pub(crate) use crate::l01_16_elaboration::elab;

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

/// The value of `t` with no ports, printed, or its error.
pub(crate) fn eval(t: &Term) -> Result<String, String> {
    Evaluator::new(World::new())
        .run(t)
        .map(|v| v.to_string())
        .map_err(|e| e.to_string())
}

/// The value of `t` lowered and raised back.
pub(crate) fn round_trip(t: &Term) -> Result<String, String> {
    let g = lower(t)?;
    eval(&raise(&g)?)
}

/// The number of nodes of `g` and its regions whose operation is named `op`.
pub(crate) fn count(g: &Region, op: &str) -> usize {
    g.nodes
        .iter()
        .map(|n| {
            usize::from(zedc::zir::op_name(&n.op) == op)
                + n.regions.iter().map(|r| count(r, op)).sum::<usize>()
        })
        .sum()
}
