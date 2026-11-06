//! Native-code helpers of step L1.36 (tests/steps/l01_36_cranelift).

use zed_kernel::{Evaluator, Term, Value, World};
use zedc::zir::legalize::Legalized;
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Plan};

/// `t` lowered, legalized for this back end and planned with fusion.
pub fn planned(t: &Term) -> (Legalized, Plan) {
    let g = zed_native::legalize(lower(t).unwrap_or_else(|e| panic!("{e}")));
    let p = memory::plan(g.graph(), true);
    (g, p)
}

/// `t` run natively with no ports.
pub fn native(t: &Term) -> Result<zed_native::Outcome, String> {
    let (g, p) = planned(t);
    zed_native::run(&g, &p, &mut Evaluator::new(World::new()))
}

/// `t` run by the kernel with no ports.
pub fn kernel(t: &Term) -> Result<Value, String> {
    Evaluator::new(World::new())
        .run(t)
        .map_err(|e| e.to_string())
}
