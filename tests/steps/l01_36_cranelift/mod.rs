//! Step L1.36: codegen via Cranelift. Each planned graph compiles, by the JIT or to an object
//! file from the same generator, to native code that runs scalar nodes inline and every other
//! node through the runtime of `zed-rt`; every corpus row gives the interpreter's value and
//! the counting machine's counts.

mod aot;
mod checks;
mod constants;
mod corpus;
mod deep_calls;
mod drops;
mod hooks;
mod kernel_inputs;
mod kinds;
mod legalize;
mod levels;
mod ports;
mod reuse;
mod scalars;
mod scaling;
mod string_length;
mod string_scaling;
mod strings;
mod table;

use zed_kernel::{Evaluator, F64, Term, Value, World};
use zedc::zir::legalize::Legalized;
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Plan};

/// A float literal.
pub(crate) fn float(x: f64) -> Term {
    Term::Lit(Value::Float(F64::new(x)))
}

/// `t` lowered, legalized for this back end and planned with fusion.
pub(crate) fn planned(t: &Term) -> (Legalized, Plan) {
    let g = zed_native::legalize(lower(t).unwrap_or_else(|e| panic!("{e}")));
    let p = memory::plan(g.graph(), true);
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
