//! Native code for planned ZIR graphs (step L1.36): Cranelift compiles each graph, by the
//! JIT to run now or to an object file, from the same generator. The generated code runs
//! integer, float and boolean nodes inline and every other node through the runtime of
//! `zed-rt`, which allocates and counts as the counting machine does, so a native run gives
//! the interpreter's value and the machine's counts.

mod codegen;
mod hooks;
mod tables;

use std::mem::ManuallyDrop;
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

#[cfg(feature = "counts")]
pub use hooks::{Counted, counted};

/// What one native run gives.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// The program's value.
    pub value: Value,
    /// The heap's counts.
    pub stats: Stats,
    /// How many nodes the kernel ran for the runtime.
    pub kernel_calls: u64,
    /// The entries of the heap's table of uncounted values when the run ends.
    pub table: usize,
    /// The cells the heap holds when the run ends, live or free.
    pub cells: usize,
}

/// Cranelift's `opt_level`, with the register allocator that goes with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptLevel {
    /// `none`, with the `single_pass` register allocator: each pass is linear in the size of a
    /// function. [`run`] and [`object`] use it.
    None,
    /// `speed`, with the `backtracking` register allocator: Cranelift's optimizing settings,
    /// whose passes grow faster than the size of a function. Tests compare it with `None`.
    Speed,
}

fn isa(pic: bool, level: OptLevel) -> Result<Arc<dyn cranelift_codegen::isa::TargetIsa>, String> {
    let mut flags = settings::builder();
    let set = |f: &mut settings::Builder, k, v| f.set(k, v).map_err(|e| format!("native: {e}"));
    // Cranelift's e-graph optimizer and its backtracking register allocator take time growing
    // faster than the size of a function (n^1.6 and n^1.4 measured); with neither, each pass is
    // linear (COMPLEXITY.md Z15).
    //
    // Complexity tradeoff: at `OptLevel::None`, which `run` and `object` use, the code Cranelift
    // emits is unoptimized and keeps more values on the stack, so it runs slower; every input
    // still compiles. Why: the costs above. Trigger: every function. Tests: the unit test
    // `tests::the_default_level_is_opt_level_none_with_a_single_pass_allocator` checks the
    // settings, and `l01_36_cranelift::levels` runs programs at both levels and checks that
    // their values agree. COMPLEXITY.md row Z15. A complete solution is the ZIR e-graph
    // optimizer (DESIGN.md L23) before Cranelift, with a linear-time register allocator.
    let (opt, regalloc) = match level {
        OptLevel::None => ("none", "single_pass"),
        OptLevel::Speed => ("speed", "backtracking"),
    };
    set(&mut flags, "opt_level", opt)?;
    set(&mut flags, "regalloc_algorithm", regalloc)?;
    set(&mut flags, "is_pic", if pic { "true" } else { "false" })?;
    // A body's frame grows with its size, so a frame can be larger than the guard page below the
    // stack; without probes its first write could land past that page, in other memory.
    set(&mut flags, "enable_probestack", "true")?;
    set(&mut flags, "probestack_strategy", "inline")?;
    let host = cranelift_native::builder().map_err(|e| format!("native: {e}"))?;
    host.finish(settings::Flags::new(flags))
        .map_err(|e| format!("native: {e}"))
}

/// A JIT module whose code and data are freed when it is dropped, on every way out of [`run`]:
/// Cranelift's module leaks them unless `free_memory` is called.
struct Jit(ManuallyDrop<JITModule>);

impl Drop for Jit {
    fn drop(&mut self) {
        // SAFETY: the module is taken once, here, and not used after. Its code is not running:
        // `run` drops the guard after `zed_root` returns, and a panic cannot unwind out of the
        // generated `extern "C"` code, so no frame of it is on the stack during unwinding.
        #[expect(
            unsafe_code,
            reason = "Cranelift frees JIT memory only through an unsafe call"
        )]
        unsafe {
            ManuallyDrop::take(&mut self.0).free_memory();
        }
    }
}

/// Compiles graph `g` under `plan` by the JIT and runs it, the kernel in `ev` running the
/// nodes the runtime does not.
pub fn run(g: &Arc<Region>, plan: &Plan, ev: &mut Evaluator) -> Result<Outcome, String> {
    run_at(OptLevel::None, g, plan, ev)
}

/// [`run`] at Cranelift's `opt_level` `level`.
pub fn run_at(
    level: OptLevel,
    g: &Arc<Region>,
    plan: &Plan,
    ev: &mut Evaluator,
) -> Result<Outcome, String> {
    let (t, plans) = Tables::new(g, plan)?;
    let t = Arc::new(t);
    let mut b = JITBuilder::with_isa(isa(false, level)?, default_libcall_names());
    for ((name, _, _), a) in hooks::HOOKS.iter().zip(hooks::addresses()) {
        b.symbol(*name, a);
    }
    let mut m = Jit(ManuallyDrop::new(JITModule::new(b)));
    let f = codegen::define(&mut *m.0, &t, &plans)?;
    m.0.finalize_definitions()
        .map_err(|e| format!("native: {e}"))?;
    let code = m.0.get_finalized_function(f.root);
    let taken = std::mem::replace(ev, Evaluator::new(World::new()));
    hooks::install(hooks::State::new(t, taken));
    // SAFETY: `code` is `zed_root`, which the generator defines with no parameters and two
    // `i64` results under the host's calling convention, as `Word` is laid out.
    #[expect(
        unsafe_code,
        reason = "calling generated code needs a function pointer from it"
    )]
    let root: extern "C" fn() -> Word = unsafe { std::mem::transmute(code) };
    let w = root();
    let mut s = hooks::remove();
    let r = hooks::finish(&s.t, &mut s.run, w);
    *ev = s.run.ev;
    drop(m);
    Ok(Outcome {
        value: r?,
        stats: s.run.heap.stats,
        kernel_calls: s.run.kernel_calls,
        table: s.run.heap.table_len(),
        cells: s.run.heap.cell_slots(),
    })
}

/// The object file of graph `g` under `plan`, for the host: `zed_root` exported, the
/// runtime's hooks imported.
pub fn object(g: &Arc<Region>, plan: &Plan) -> Result<Vec<u8>, String> {
    let (t, plans) = Tables::new(g, plan)?;
    let b = ObjectBuilder::new(isa(true, OptLevel::None)?, "zed", default_libcall_names())
        .map_err(|e| format!("native: {e}"))?;
    let mut m = ObjectModule::new(b);
    codegen::define(&mut m, &t, &plans)?;
    m.finish().emit().map_err(|e| format!("native: {e}"))
}

/// Lowers, plans with `fuse` and runs a closed term natively: a `through` for
/// `zedc::testing::test_through` and `Program::run_through`.
pub fn through(fuse: bool) -> impl Fn(&Term, &mut Evaluator) -> Result<Value, String> {
    move |t, ev| {
        let g = Arc::new(lower(t)?);
        run(&g, &plan(&g, fuse), ev).map(|o| o.value)
    }
}

#[cfg(test)]
mod tests {
    use std::io;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use cranelift_codegen::ir::types::I64;
    use cranelift_codegen::ir::{AbiParam, InstBuilder};
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
    use cranelift_jit::{BranchProtection, JITMemoryKind, JITMemoryProvider, SystemMemoryProvider};
    use cranelift_module::{Linkage, Module, ModuleResult};

    use super::*;

    /// The system's JIT memory, counting the bytes handed out and the calls that free them.
    struct Counted {
        memory: SystemMemoryProvider,
        allocated: Arc<AtomicUsize>,
        freed: Arc<AtomicUsize>,
    }

    impl JITMemoryProvider for Counted {
        fn allocate(
            &mut self,
            size: usize,
            align: u64,
            kind: JITMemoryKind,
        ) -> io::Result<*mut u8> {
            self.allocated.fetch_add(size, Ordering::SeqCst);
            self.memory.allocate(size, align, kind)
        }

        #[expect(unsafe_code, reason = "the provider's trait declares freeing unsafe")]
        unsafe fn free_memory(&mut self) {
            self.freed.fetch_add(1, Ordering::SeqCst);
            // SAFETY: the caller's contract, passed on: no code of the module runs after this.
            unsafe { self.memory.free_memory() }
        }

        fn finalize(&mut self, branch_protection: BranchProtection) -> ModuleResult<()> {
            self.memory.finalize(branch_protection)
        }
    }

    /// Defines `seven() -> 7`, then `broken() -> int` whose body returns nothing, which the
    /// verifier rejects: a compile that fails after code was written.
    fn compile_until_broken(m: &mut JITModule) -> Result<(), String> {
        for (name, value) in [("seven", Some(7)), ("broken", None)] {
            let mut ctx = m.make_context();
            ctx.func.signature.returns.push(AbiParam::new(I64));
            let id = m
                .declare_function(name, Linkage::Local, &ctx.func.signature)
                .map_err(|e| e.to_string())?;
            let mut fbc = FunctionBuilderContext::new();
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = b.create_block();
            b.switch_to_block(entry);
            b.seal_block(entry);
            match value {
                Some(v) => {
                    let v = b.ins().iconst(I64, v);
                    b.ins().return_(&[v]);
                }
                None => {
                    b.ins().return_(&[]);
                }
            }
            b.finalize(m.isa().frontend_config());
            m.define_function(id, &mut ctx).map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    #[test]
    fn the_default_level_is_opt_level_none_with_a_single_pass_allocator() {
        use cranelift_codegen::settings::{OptLevel as Cranelift, RegallocAlgorithm};
        for pic in [false, true] {
            let flags = isa(pic, OptLevel::None).unwrap().flags().clone();
            assert_eq!(flags.opt_level(), Cranelift::None);
            assert_eq!(flags.regalloc_algorithm(), RegallocAlgorithm::SinglePass);
        }
        let flags = isa(false, OptLevel::Speed).unwrap().flags().clone();
        assert_eq!(flags.opt_level(), Cranelift::Speed);
        assert_eq!(flags.regalloc_algorithm(), RegallocAlgorithm::Backtracking);
    }

    #[test]
    fn a_failed_compile_frees_the_jit_memory() {
        let (allocated, freed) = (Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0)));
        let mut b =
            JITBuilder::with_isa(isa(false, OptLevel::None).unwrap(), default_libcall_names());
        b.memory_provider(Box::new(Counted {
            memory: SystemMemoryProvider::new(),
            allocated: allocated.clone(),
            freed: freed.clone(),
        }));
        let mut m = Jit(ManuallyDrop::new(JITModule::new(b)));
        let failed = compile_until_broken(&mut m.0);
        assert!(failed.is_err(), "the broken function was accepted");
        assert!(allocated.load(Ordering::SeqCst) > 0, "no code was written");
        assert_eq!(freed.load(Ordering::SeqCst), 0);
        drop(m);
        assert_eq!(freed.load(Ordering::SeqCst), 1);
    }
}
