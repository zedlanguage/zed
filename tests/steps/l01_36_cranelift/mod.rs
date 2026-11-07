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
mod function_binders;
mod hooks;
mod kernel_inputs;
mod kinds;
mod legalize;
mod levels;
mod minmax;
mod ports;
mod reuse;
mod scalars;
mod scaling;
mod shared_closures;
mod string_length;
mod string_scaling;
mod strings;
mod table;

use zed_kernel::{F64, Term, Value};

pub(crate) use zed_tests::step_helpers::l01_36_cranelift::{kernel, native, planned};

/// A float literal.
pub(crate) fn float(x: f64) -> Term {
    Term::Lit(Value::Float(F64::new(x)))
}
