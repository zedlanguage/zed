//! Step L1.36: codegen via Cranelift. Each planned graph compiles, by the JIT or to an object
//! file from the same generator, to native code that runs scalar nodes inline and every other
//! node through the runtime of `zed-rt`; every corpus row gives the interpreter's value and
//! the counting machine's counts.

mod aot;
mod checks;
mod corpus;
mod ports;
mod scalars;
mod strings;

use zed_kernel::{Evaluator, F64, Term, Value, World};
use zedc::zir::Region;
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Plan};

/// A float literal.
pub(crate) fn float(x: f64) -> Term {
    Term::Lit(Value::Float(F64::new(x)))
}

/// `t` lowered and planned with fusion.
pub(crate) fn planned(t: &Term) -> (Region, Plan) {
    let g = lower(t).unwrap_or_else(|e| panic!("{e}"));
    let p = memory::plan(&g, true);
    (g, p)
}

/// `t` run natively with no ports.
pub(crate) fn native(t: &Term) -> Result<zed_native::Outcome, String> {
    let (g, p) = planned(t);
    zed_native::run(&g, &p, &mut Evaluator::new(World::new()))
}

/// `t` run by the kernel with no ports.
pub(crate) fn kernel(t: &Term) -> Result<Value, String> {
    Evaluator::new(World::new())
        .run(t)
        .map_err(|e| e.to_string())
}
