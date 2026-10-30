//! Native code for planned ZIR graphs (step L1.36): Cranelift compiles each graph, by the
//! JIT to run now or to an object file, from the same generator. The generated code runs
//! integer, float and boolean nodes inline and every other node through the runtime of
//! `zed-rt`, which allocates and counts as the counting machine does, so a native run gives
//! the interpreter's value and the machine's counts.

mod codegen;
mod hooks;
mod tables;

use std::sync::Arc;

use cranelift_codegen::settings::{self, Configurable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::default_libcall_names;
use cranelift_object::{ObjectBuilder, ObjectModule};

use zed_kernel::{Evaluator, Term, Value, World};
use zedc::zir::Region;
use zedc::zir::lower::lower;
use zedc::zir::memory::{Plan, plan};

use zed_rt::{Stats, Word};

use crate::tables::Tables;

/// What one native run gives.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// The program's value.
    pub value: Value,
    /// The heap's counts.
    pub stats: Stats,
    /// How many nodes the kernel ran for the runtime.
    pub kernel_calls: u64,
}

fn isa(pic: bool) -> Result<Arc<dyn cranelift_codegen::isa::TargetIsa>, String> {
    let mut flags = settings::builder();
    let set = |f: &mut settings::Builder, k, v| f.set(k, v).map_err(|e| format!("native: {e}"));
    set(&mut flags, "opt_level", "speed")?;
    set(&mut flags, "is_pic", if pic { "true" } else { "false" })?;
    let host = cranelift_native::builder().map_err(|e| format!("native: {e}"))?;
    host.finish(settings::Flags::new(flags))
        .map_err(|e| format!("native: {e}"))
}

/// Compiles graph `g` under `plan` by the JIT and runs it, the kernel in `ev` running the
/// nodes the runtime does not.
pub fn run(g: &Region, plan: &Plan, ev: &mut Evaluator) -> Result<Outcome, String> {
    let t = Arc::new(Tables::new(g, plan)?);
    let mut b = JITBuilder::with_isa(isa(false)?, default_libcall_names());
    for ((name, _, _), a) in hooks::HOOKS.iter().zip(hooks::addresses()) {
        b.symbol(*name, a);
    }
    let mut m = JITModule::new(b);
    let f = codegen::define(&mut m, &t, plan, g)?;
    m.finalize_definitions()
        .map_err(|e| format!("native: {e}"))?;
    let code = m.get_finalized_function(f.root);
    let taken = std::mem::replace(ev, Evaluator::new(World::new()));
    hooks::install(hooks::State::new(t, taken));
    // SAFETY: `code` is `zed_root`, which the generator defines with no parameters and two
    // `i64` results under the host's calling convention, as `Word` is laid out.
    #[allow(unsafe_code)]
    let root: extern "C" fn() -> Word = unsafe { std::mem::transmute(code) };
    let w = root();
    let mut s = hooks::remove();
    let r = hooks::finish(&mut s, w);
    *ev = s.ev;
    // SAFETY: nothing generated runs after this point.
    #[allow(unsafe_code)]
    unsafe {
        m.free_memory();
    }
    Ok(Outcome {
        value: r?,
        stats: s.heap.stats,
        kernel_calls: s.kernel_calls,
    })
}

/// The object file of graph `g` under `plan`, for the host: `zed_root` exported, the
/// runtime's hooks imported.
pub fn object(g: &Region, plan: &Plan) -> Result<Vec<u8>, String> {
    let t = Tables::new(g, plan)?;
    let b = ObjectBuilder::new(isa(true)?, "zed", default_libcall_names())
        .map_err(|e| format!("native: {e}"))?;
    let mut m = ObjectModule::new(b);
    codegen::define(&mut m, &t, plan, g)?;
    m.finish().emit().map_err(|e| format!("native: {e}"))
}

/// Lowers, plans with `fuse` and runs a closed term natively: a `through` for
/// `zedc::testing::test_through` and `Program::run_through`.
pub fn through(fuse: bool) -> impl Fn(&Term, &mut Evaluator) -> Result<Value, String> {
    move |t, ev| {
        let g = lower(t)?;
        run(&g, &plan(&g, fuse), ev).map(|o| o.value)
    }
}
