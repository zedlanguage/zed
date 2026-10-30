//! Step L1.34: memory. Each graph gets a plan of owned and borrowed edges with a dup before
//! each owned use but the last and a drop at each last use that borrows; the machine runs the
//! graph under the plan and checks, after every node, that each live cell's count is the
//! number of references to it.

mod borrow;
mod cells;
mod checks;
mod corpus;
mod fusion;

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Evaluator, Prim, Term, World};
use zedc::zir::Region;
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Plan, Stats};

/// A fresh string: the concatenation of `a` and `b`, made when the program runs.
pub(crate) fn cat(a: &str, b: &str) -> Term {
    prim(Prim::Concat, vec![lit(a), lit(b)])
}

/// `t` lowered and planned, with fusion or not.
pub(crate) fn planned(t: &Term, fuse: bool) -> (Region, Plan) {
    let g = lower(t).unwrap_or_else(|e| panic!("{e}"));
    let p = memory::plan(&g, fuse);
    (g, p)
}

/// `g` run by the machine under `p`, with no ports: its value, printed, and its counts.
pub(crate) fn run(g: &Region, p: &Plan) -> Result<(String, Stats), String> {
    let (v, s) = memory::run(g, p, &mut Evaluator::new(World::new()))?;
    Ok((v.to_string(), s))
}

/// `t` planned with fusion and run.
pub(crate) fn machine(t: &Term) -> (String, Stats, Plan) {
    let (g, p) = planned(t, true);
    let (v, s) = run(&g, &p).unwrap_or_else(|e| panic!("{e}"));
    (v, s, p)
}
