//! Native code for planned ZIR graphs (step L1.36): Cranelift compiles each graph, by the
//! JIT to run now or to an object file, from the same generator. The generated code runs
//! integer, float and boolean nodes inline and every other node through the runtime of
//! `zed-rt`, which allocates and counts as the counting machine does, so a native run gives
//! the interpreter's value and the machine's counts.
//!
//! `zedc build` ([`link`], step L1.36a) links that object file, with the program as data and a C
//! `main`, against this crate built as a static library, the runtime of every executable.

mod codegen;
#[cfg(unix)]
mod exe;
mod hooks;
mod legal;
#[cfg(target_os = "linux")]
pub mod link;
mod outcome;
pub mod sources;
mod tables;

use std::mem::ManuallyDrop;
use std::sync::Arc;

use cranelift_codegen::settings::{self, Configurable};
use cranelift_jit::{JITBuilder, JITMemoryProvider, JITModule, SystemMemoryProvider};
use cranelift_module::default_libcall_names;
use cranelift_object::{ObjectBuilder, ObjectModule};

use zed_kernel::{Evaluator, Term, Value};
use zedc::zir::Region;
use zedc::zir::legalize::Legalized;
use zedc::zir::lower::lower;
use zedc::zir::memory::{Plan, plan};

use zed_rt::Word;

use crate::tables::Tables;

#[cfg(feature = "counts")]
pub use hooks::{Counted, counted};
pub use legal::{EXPANSIONS, legalize};
pub use outcome::Outcome;
use outcome::call;

/// The message for a failure of zedc's own making of machine code, which is a bug in zedc and
/// never the program's fault (DESIGN.md sec:diagnostics): `detail` is the one part meant for
/// zedc's developers.
pub(crate) fn bug(detail: impl std::fmt::Display) -> String {
    format!(
        "zedc could not make machine code for the program because of a bug in zedc, not in the \
         program. Please report it to the Zed developers with the program's source and this \
         line: {detail}. Until it is fixed, `zedc run` runs the program without machine code"
    )
}

/// Cranelift's `opt_level`, with the register allocator that goes with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptLevel {
    /// `none`, with the `single_pass` register allocator: each pass is linear in the size of a
    /// function. [`run`] and [`object()`] use it.
    None,
    /// `speed`, with the `backtracking` register allocator: Cranelift's optimizing settings,
    /// whose passes grow faster than the size of a function. Tests compare it with `None`.
    Speed,
}

fn isa(pic: bool, level: OptLevel) -> Result<Arc<dyn cranelift_codegen::isa::TargetIsa>, String> {
    let mut flags = settings::builder();
    let set = |f: &mut settings::Builder, k, v| f.set(k, v).map_err(bug);
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
    let host = cranelift_native::builder().map_err(|e| {
        format!(
            "zedc cannot make machine code for this machine: {e}. Repair: run the program with \
             `zedc run`, which needs no machine code"
        )
    })?;
    host.finish(settings::Flags::new(flags)).map_err(bug)
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

/// Compiles graph `g`, made by [`legalize`], under `plan` by the JIT and runs it, the kernel in
/// `ev` running the nodes the runtime does not. Only a legalized graph is taken, so every node
/// legalization expands is expanded or refused by name, and a node it swapped is run by the
/// kernel as the program wrote it.
pub fn run(g: &Legalized, plan: &Plan, ev: &mut Evaluator) -> Result<Outcome, String> {
    run_at(OptLevel::None, g, plan, ev)
}

/// [`run`] at Cranelift's `opt_level` `level`.
pub fn run_at(
    level: OptLevel,
    g: &Legalized,
    plan: &Plan,
    ev: &mut Evaluator,
) -> Result<Outcome, String> {
    run_in(Box::new(SystemMemoryProvider::new()), level, g, plan, ev)
}

/// [`run_at`] with the JIT's code placed in `memory`.
fn run_in(
    memory: Box<dyn JITMemoryProvider + Send>,
    level: OptLevel,
    g: &Legalized,
    plan: &Plan,
    ev: &mut Evaluator,
) -> Result<Outcome, String> {
    let (t, plans) = Tables::new(g, plan)?;
    let t = Arc::new(t);
    // The JIT maps code in pieces, one mapping at a time, so two functions of one module can
    // lie any distance apart: other mappings, such as a run's stack on another thread, land
    // between them. Position-independent code reaches every symbol by an address that cannot
    // overflow: x86-64 loads a symbol's address through `X86GOTPCRel4`, which cranelift-jit
    // turns into a `lea` when the symbol is within 2 GiB and otherwise into a load from an
    // entry it adds at the end of the same allocation, and it sends a call whose target is out
    // of reach through a jump it adds there too. Without it, taking the address of a function
    // of the module (the root registering each lambda's entry) is a `lea` whose 32-bit
    // displacement overflowed when the two lay more than 2 GiB apart (JIT-reloc). cranelift-jit
    // accepts position-independent code on x86-64 only, as its own default does.
    let pic = cfg!(target_arch = "x86_64");
    let mut b = JITBuilder::with_isa(isa(pic, level)?, default_libcall_names());
    b.memory_provider(memory);
    for ((name, _, _), a) in hooks::HOOKS.iter().zip(hooks::addresses()) {
        b.symbol(*name, a);
    }
    let mut m = Jit(ManuallyDrop::new(JITModule::new(b)));
    let f = codegen::define(&mut *m.0, &t, &plans)?;
    m.0.finalize_definitions().map_err(bug)?;
    let code = m.0.get_finalized_function(f.root);
    // SAFETY: `code` is `zed_root`, which the generator defines with no parameters and two
    // `i64` results under the host's calling convention, as `Word` is laid out.
    #[expect(
        unsafe_code,
        reason = "calling generated code needs a function pointer from it"
    )]
    let root: extern "C" fn() -> Word = unsafe { std::mem::transmute(code) };
    let o = call(t, root, ev);
    drop(m);
    o
}

/// The object file of graph `g`, made by [`legalize`], under `plan`, for the host: `zed_root`
/// exported, the runtime's hooks imported.
pub fn object(g: &Legalized, plan: &Plan) -> Result<Vec<u8>, String> {
    let (t, plans) = Tables::new(g, plan)?;
    let mut m = object_module()?;
    codegen::define(&mut m, &t, &plans)?;
    m.finish().emit().map_err(bug)
}

/// The object file of an executable that runs the lowered graph `g`, planned with `fuse`, with
/// `main`'s ports `ports` and the program's content address `address` (steps L1.36a and
/// L1.19b): [`object()`]'s code for `g` legalized, the program as data, and a C `main` that
/// passes both, with the command line, to the runtime library's start. The data holds `g` as
/// lowered, since ZIR's binary form does not record which nodes legalization swapped; the
/// start legalizes and plans it again, as this does.
#[cfg(unix)]
pub fn executable_object(
    g: Region,
    fuse: bool,
    ports: &zedc::run::Ports,
    address: zedc::address::ContentAddress,
) -> Result<Vec<u8>, String> {
    let data = exe::data(fuse, address, ports, &g)?;
    let g = legalize(g);
    let plan = plan(g.graph(), fuse);
    let (t, plans) = Tables::new(&g, &plan)?;
    let mut m = object_module()?;
    let f = codegen::define(&mut m, &t, &plans)?;
    exe::define_main(&mut m, f.root, &data)?;
    m.finish().emit().map_err(bug)
}

/// An empty object module for the host, its code position-independent.
fn object_module() -> Result<ObjectModule, String> {
    let b = ObjectBuilder::new(isa(true, OptLevel::None)?, "zed", default_libcall_names())
        .map_err(bug)?;
    Ok(ObjectModule::new(b))
}

/// Lowers, legalizes, plans with `fuse` and runs a closed term natively: a `through` for
/// `zedc::testing::test_through` and `Program::run_through`.
pub fn through(fuse: bool) -> impl Fn(&Term, &mut Evaluator) -> Result<Value, String> {
    move |t, ev| {
        let g = legalize(lower(t)?);
        run(&g, &plan(g.graph(), fuse), ev).map(|o| o.value)
    }
}

#[cfg(test)]
mod tests {
    use std::io;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use cranelift_codegen::ir::types::I64;
    use cranelift_codegen::ir::{AbiParam, InstBuilder};
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
    use cranelift_jit::{BranchProtection, JITMemoryKind};
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

/// Tests of where the JIT may place code: anywhere, whatever the distance between its parts.
#[cfg(test)]
mod placement {
    use std::io;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use cranelift_jit::{BranchProtection, JITMemoryKind};
    use cranelift_module::ModuleResult;
    use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
    use zed_kernel::{Prim, Term, World};
    use zedc::zir::memory::plan;

    use super::*;

    /// The distance between two allocations of [`FarApart`]: twice the reach of a 32-bit
    /// displacement, so no allocation is within reach of another.
    const SLOT: usize = 4 << 30;
    /// The slots [`FarApart`] reserves, more than the program below allocates.
    const SLOTS: usize = 16;

    /// JIT memory that puts each allocation at the start of its own slot, [`SLOT`] bytes after
    /// the last: the placement the system's provider gives when other mappings, such as the
    /// stack of a run on another thread, land between the mappings it makes one by one.
    struct FarApart {
        /// The reserved slots, mapped with no access.
        base: *mut u8,
        /// The executable allocations, by slot and length, to protect at `finalize`.
        code: Vec<(usize, usize)>,
        /// The slots used.
        used: Arc<AtomicUsize>,
    }

    #[expect(
        unsafe_code,
        reason = "reserving and protecting memory are system calls"
    )]
    impl FarApart {
        fn new(used: Arc<AtomicUsize>) -> FarApart {
            // SAFETY: a fresh anonymous mapping, at an address the kernel chooses.
            let base = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    SLOT * SLOTS,
                    libc::PROT_NONE,
                    libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
                    -1,
                    0,
                )
            };
            assert_ne!(base, libc::MAP_FAILED, "{}", io::Error::last_os_error());
            FarApart {
                base: base.cast(),
                code: Vec::new(),
                used,
            }
        }

        /// Sets the protection of `len` bytes from the start of slot `slot`.
        fn protect(&self, slot: usize, len: usize, prot: libc::c_int) -> io::Result<()> {
            // SAFETY: the bytes lie in the reservation, since `len` is at most a slot.
            let r = unsafe { libc::mprotect(self.base.add(slot * SLOT).cast(), len, prot) };
            if r == 0 {
                Ok(())
            } else {
                Err(io::Error::last_os_error())
            }
        }
    }

    // SAFETY: the reservation belongs to the provider alone, whichever thread holds it.
    #[expect(unsafe_code, reason = "a raw pointer is not `Send` by itself")]
    unsafe impl Send for FarApart {}

    impl JITMemoryProvider for FarApart {
        fn allocate(
            &mut self,
            size: usize,
            align: u64,
            kind: JITMemoryKind,
        ) -> io::Result<*mut u8> {
            let slot = self.used.fetch_add(1, Ordering::SeqCst);
            if slot >= SLOTS {
                return Err(io::Error::other(format!("all {SLOTS} slots are used")));
            }
            if align > 4096 || size > SLOT {
                return Err(io::Error::other(format!(
                    "{size} bytes at alignment {align}"
                )));
            }
            let len = size.next_multiple_of(4096);
            self.protect(slot, len, libc::PROT_READ | libc::PROT_WRITE)?;
            if let JITMemoryKind::Executable = kind {
                self.code.push((slot, len));
            }
            // SAFETY: the slot lies in the reservation.
            #[expect(unsafe_code, reason = "an address in the reservation")]
            Ok(unsafe { self.base.add(slot * SLOT) })
        }

        #[expect(unsafe_code, reason = "the provider's trait declares freeing unsafe")]
        unsafe fn free_memory(&mut self) {
            self.code.clear();
        }

        fn finalize(&mut self, _: BranchProtection) -> ModuleResult<()> {
            for &(slot, len) in &self.code {
                self.protect(slot, len, libc::PROT_READ | libc::PROT_EXEC)
                    .map_err(|err| cranelift_module::ModuleError::Allocation { err })?;
            }
            Ok(())
        }
    }

    impl Drop for FarApart {
        fn drop(&mut self) {
            // SAFETY: the module that used the memory is gone before its provider.
            #[expect(unsafe_code, reason = "unmapping is a system call")]
            let r = unsafe { libc::munmap(self.base.cast(), SLOT * SLOTS) };
            assert_eq!(r, 0, "{}", io::Error::last_os_error());
        }
    }

    /// `f0 = x => x ++ "0"; f1 = x => x ++ "1"; (f0("a"), f1("a"))`: the root takes the
    /// address of each lambda's entry, which lies in another allocation.
    fn two_lambdas() -> Term {
        let calls = prim(
            Prim::Tuple,
            vec![
                app(var("f0"), vec![lit("a")]),
                app(var("f1"), vec![lit("a")]),
            ],
        );
        (0..2).rev().fold(calls, |b, i| {
            let f = lam(
                &["x"],
                prim(Prim::Concat, vec![var("x"), lit(i.to_string().as_str())]),
            );
            let_(&format!("f{i}"), f, b)
        })
    }

    /// Every allocation past the last slot is refused, not only the first: an address past
    /// the reservation may belong to another mapping, whose protection `allocate` would change.
    #[test]
    fn far_apart_refuses_every_allocation_past_its_slots() {
        let used = Arc::new(AtomicUsize::new(0));
        let mut memory = FarApart::new(used);
        for _ in 0..SLOTS {
            memory
                .allocate(1, 16, JITMemoryKind::ReadOnly)
                .expect("a slot is free");
        }
        for _ in 0..2 {
            let err = memory.allocate(1, 16, JITMemoryKind::ReadOnly).unwrap_err();
            assert_eq!(err.to_string(), format!("all {SLOTS} slots are used"));
        }
    }

    #[test]
    fn code_runs_with_its_functions_more_than_2_gib_apart() {
        let t = two_lambdas();
        let g = legalize(lower(&t).unwrap());
        let p = plan(g.graph(), true);
        let want = Evaluator::new(World::new()).run(&t).unwrap();
        for level in [OptLevel::None, OptLevel::Speed] {
            let used = Arc::new(AtomicUsize::new(0));
            let memory = Box::new(FarApart::new(used.clone()));
            let mut ev = Evaluator::new(World::new());
            let o = run_in(memory, level, &g, &p, &mut ev).unwrap();
            assert_eq!(o.value, want, "{level:?}");
            assert!(
                used.load(Ordering::SeqCst) >= 3,
                "{level:?}: too few allocations"
            );
        }
    }
}
