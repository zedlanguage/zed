//! The code generator (step L1.36): one Cranelift function per planned graph, written
//! against the [`Module`] trait so the JIT and the object writer share every line.
//!
//! Every value is a word, two `i64`s. The root region is the function `zed_root`, with no
//! parameters, returning its result's word. Each lambda body is a function `zed_body_<i>`
//! taking the closure and the parameters, held as the body's plan holds them, and reading
//! its captures from the closure; `zed_entry_<i>` takes every parameter owned and drops the
//! ones the body borrows, for calls whose callee is known only when they run. The arms of
//! `if` and `match` are emitted inline. Each node's dups and drops are calls of `rt_inc` and
//! `rt_dec`. Integer, float and boolean arithmetic and comparisons run inline when the tags
//! say the operands are scalars; overflow and every other case call the runtime, which runs
//! the node as the counting machine does. `sqrt` and `fma` on `f64` are Cranelift's `sqrt`
//! and `fma`, each rounded once as the kernel's are; no multiply and add is ever fused into an
//! `fma` the program did not write. Float `^` calls `rt_pow`, after a NaN test of each
//! operand the graph does not prove NaN-free. After each call that returns a word, an error
//! word leaves the function, returning the error word.

use std::collections::{HashMap, HashSet};

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::types::{F64, I64};
use cranelift_codegen::ir::{AbiParam, Block, BlockArg, FuncRef, InstBuilder, MemFlagsData};
use cranelift_codegen::ir::{Signature, StackSlotData, StackSlotKind, Value as V};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Switch};
use cranelift_module::{FuncId, Linkage, Module};

use zed_kernel::Prim;
use zedc::zir::legalize::Expansion;
use zedc::zir::memory::{Mode, RegionPlan};
use zedc::zir::{Op, Src, binds};

use zed_rt::Word;

use crate::hooks::HOOKS;
use crate::tables::Tables;

/// A word in generated code: its tag and its payload.
type W = (V, V);

/// Where a word is kept between the node that makes it and the nodes that use it: a stack
/// slot, or a constant. Each word is loaded just before each use, so every value the register
/// allocator sees lives only a few instructions; a value live across many calls costs it
/// time in proportion to their number (COMPLEXITY.md Z14).
// Complexity tradeoff: the standard form keeps each word in a virtual register from its
// definition to its last use, so a word used after many calls stays live across all of them,
// and the register allocator's work is O(n²) for n words each live across the calls after it
// (Z14; many named fields were killed at 671 s on that form). Here each word lives in a stack
// slot and is loaded just before each use, so every live range is a few instructions long and
// allocation is linear. Tradeoffs: a store per word made and a load per use, and a 16-byte
// frame slot per word (R10), so the code is slower than register-held code by a constant
// factor; stack slots are not reused by liveness. Nothing is refused. Tests
// `l01_36_cranelift::scaling`.
#[derive(Clone, Copy)]
enum Loc {
    Slot(cranelift_codegen::ir::StackSlot),
    Const(Word),
}

fn err(e: impl std::fmt::Display) -> String {
    crate::bug::bug(e)
}

fn args(ws: &[W]) -> Vec<BlockArg> {
    ws.iter()
        .flat_map(|(t, b)| [BlockArg::from(*t), BlockArg::from(*b)])
        .collect()
}

fn sig<M: Module>(m: &M, params: usize, rets: usize) -> Signature {
    let mut s = m.make_signature();
    s.params.extend((0..params).map(|_| AbiParam::new(I64)));
    s.returns.extend((0..rets).map(|_| AbiParam::new(I64)));
    s
}

/// The functions of one graph.
pub(crate) struct Funcs {
    /// `zed_root`.
    pub root: FuncId,
}

struct Gen<'a, M: Module> {
    m: &'a mut M,
    t: &'a Tables,
    /// Each region's plan, by the region's number.
    plans: &'a [&'a RegionPlan],
    hooks: HashMap<&'static str, FuncId>,
    bodies: Vec<FuncId>,
    entries: Vec<FuncId>,
    /// For each number of parameters of [`Tables::arities`], the function that calls a body
    /// of that many on the words of a buffer ([`Gen::trampoline`]).
    trampolines: Vec<(usize, FuncId)>,
    /// Each lambda's placed entry ([`Gen::placed`]), for those [`Tables::placeable`] keeps.
    placed: Vec<Option<FuncId>>,
    /// The numbers of parameters of the lambdas with a placed entry: a call by name with
    /// another number of arguments never reaches one, and its site asks no `rt_direct`.
    direct: HashSet<usize>,
    /// Where each function's IR text goes, as emitted and before Cranelift's passes, when
    /// asked for.
    ir: Option<&'a mut String>,
}

/// One function being built.
struct Fx<'b> {
    b: FunctionBuilder<'b>,
    refs: HashMap<FuncId, FuncRef>,
    err: Block,
}

/// A region being emitted. Regions nest as deep as the term and the arms of `if` and `match`
/// are inline, so the regions in progress are on a stack.
struct Frame {
    /// The region's number.
    at: usize,
    args: Vec<Loc>,
    /// The outputs of the nodes emitted so far; the next node is the one at this length.
    outs: Vec<Vec<Loc>>,
    /// The inputs of the node with `open` arms.
    ins: Vec<Loc>,
    /// The `if` or `match` whose arms are being emitted.
    open: Option<Open>,
}

/// An `if` or a `match` whose test is emitted, with the arms that remain.
struct Open {
    merge: Block,
    fail: Block,
    arms: Vec<Block>,
    /// The number of binders of each arm.
    binders: Vec<usize>,
    /// The next arm.
    next: usize,
    /// Whether the condition is already released, as [`Gen::finish`] needs to know.
    early: bool,
}

/// Declares and defines every function of the graph in `t`, with `plans` by region, in `m`;
/// appends each function's IR text to `ir` when given.
pub(crate) fn define<'a, M: Module>(
    m: &'a mut M,
    t: &'a Tables,
    plans: &'a [&'a RegionPlan],
    ir: Option<&'a mut String>,
) -> Result<Funcs, String> {
    let mut hooks = HashMap::new();
    for (name, p, r) in HOOKS {
        let s = sig(m, *p, *r);
        hooks.insert(
            *name,
            m.declare_function(name, Linkage::Import, &s).map_err(err)?,
        );
    }
    let mut bodies = Vec::new();
    let mut entries = Vec::new();
    for (i, l) in t.lambdas.iter().enumerate() {
        let s = sig(m, 2 + 2 * l.params, 2);
        bodies.push(
            m.declare_function(&format!("zed_body_{i}"), Linkage::Local, &s)
                .map_err(err)?,
        );
        entries.push(
            m.declare_function(&format!("zed_entry_{i}"), Linkage::Local, &s)
                .map_err(err)?,
        );
    }
    let mut trampolines = Vec::new();
    for a in t.arities() {
        let id = m
            .declare_function(&format!("zed_named_{a}"), Linkage::Local, &sig(m, 2, 2))
            .map_err(err)?;
        trampolines.push((a, id));
    }
    let mut placed = Vec::new();
    let mut direct = HashSet::new();
    for (i, p) in t.placeable().into_iter().enumerate() {
        placed.push(if p {
            direct.insert(t.lambdas[i].params);
            let s = sig(m, 4, 2);
            let id = m.declare_function(&format!("zed_placed_{i}"), Linkage::Local, &s);
            Some(id.map_err(err)?)
        } else {
            None
        });
    }
    let root = m
        .declare_function("zed_root", Linkage::Export, &sig(m, 0, 2))
        .map_err(err)?;
    let mut cg = Gen {
        m,
        t,
        plans,
        hooks,
        bodies,
        entries,
        trampolines,
        placed,
        direct,
        ir,
    };
    cg.root(root)?;
    for i in 0..t.lambdas.len() {
        cg.body(i)?;
        cg.entry(i)?;
        if let Some(Some(id)) = cg.placed.get(i) {
            cg.placed(i, *id)?;
        }
    }
    for i in 0..cg.trampolines.len() {
        cg.trampoline(i)?;
    }
    Ok(Funcs { root })
}

impl<M: Module> Gen<'_, M> {
    /// Builds function `id` with `params` and `rets` words; `f` emits its body from the
    /// entry block's parameters and returns the words it returns.
    fn function(
        &mut self,
        id: FuncId,
        params: usize,
        rets: usize,
        f: impl FnOnce(&mut Self, &mut Fx<'_>, Vec<W>) -> Result<Vec<W>, String>,
    ) -> Result<(), String> {
        let mut ctx = self.m.make_context();
        ctx.func.signature = sig(self.m, 2 * params, 2 * rets);
        let mut fbc = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            // The code goes in a block after the entry block, which holds only the jump to it.
            // Complexity tradeoff: Cranelift's verifier (cranelift-codegen 0.137,
            // `Verifier::block_integrity`) checks every parameter of a block at each of its
            // instructions, so code in an entry block of 2 + 2p parameters, whose stores of
            // the p words are O(p) instructions, cost O(p²) to verify: 15 times the time at 4
            // times p, measured at p = 320 and 1280 (row CALL-callee-places-native). With one
            // instruction in the entry block it costs O(p), and every other block has a fixed
            // number of parameters. The jump is to the next block and emits no code.
            let start = b.create_block();
            b.ins().jump(start, &[]);
            b.switch_to_block(start);
            let err = b.create_block();
            let mut fx = Fx {
                b,
                refs: HashMap::new(),
                err,
            };
            let ws = ps.chunks(2).map(|c| (c[0], c[1])).collect();
            let out = f(self, &mut fx, ws)?;
            let flat: Vec<V> = out.iter().flat_map(|(t, b)| [*t, *b]).collect();
            fx.b.ins().return_(&flat);
            fx.b.switch_to_block(err);
            let e = fx.b.ins().iconst(I64, Word::ERR);
            let z = fx.b.ins().iconst(I64, 0);
            let flat: Vec<V> = (0..rets).flat_map(|_| [e, z]).collect();
            fx.b.ins().return_(&flat);
            fx.b.seal_all_blocks();
            let fc = self.m.isa().frontend_config();
            fx.b.finalize(fc);
        }
        if let Some(s) = self.ir.as_deref_mut() {
            s.push_str(&ctx.func.display().to_string());
        }
        self.m.define_function(id, &mut ctx).map_err(err)?;
        self.m.clear_context(&mut ctx);
        Ok(())
    }

    fn root(&mut self, id: FuncId) -> Result<(), String> {
        self.function(id, 0, 1, |cg, fx, _| {
            for i in 0..cg.t.lambdas.len() {
                let r = cg.fref(fx, cg.entries[i]);
                let a = fx.b.ins().func_addr(I64, r);
                let l = fx.b.ins().iconst(I64, i as i64);
                cg.call(fx, "rt_register", &[l, a]);
            }
            if !cg.trampolines.is_empty() {
                for i in 0..cg.t.lambdas.len() {
                    let r = cg.fref(fx, cg.bodies[i]);
                    let a = fx.b.ins().func_addr(I64, r);
                    let l = fx.b.ins().iconst(I64, cg.t.body(i) as i64);
                    cg.call(fx, "rt_register", &[l, a]);
                    if let Some(Some(id)) = cg.placed.get(i) {
                        let r = cg.fref(fx, *id);
                        let a = fx.b.ins().func_addr(I64, r);
                        let l = fx.b.ins().iconst(I64, cg.t.placed(i) as i64);
                        cg.call(fx, "rt_register", &[l, a]);
                    }
                }
            }
            for i in 0..cg.trampolines.len() {
                let (arity, id) = cg.trampolines[i];
                let r = cg.fref(fx, id);
                let a = fx.b.ins().func_addr(I64, r);
                let l = fx.b.ins().iconst(I64, cg.t.trampoline(arity) as i64);
                cg.call(fx, "rt_register", &[l, a]);
            }
            let g = &cg.t.regions[0].region;
            let args = g.args.iter().map(|_| Loc::Const(Word::state())).collect();
            Ok(vec![cg.walk(fx, 0, args)?[0]])
        })
    }

    fn body(&mut self, i: usize) -> Result<(), String> {
        let l = &self.t.lambdas[i];
        let region = &self.t.regions[l.body].region;
        // A body that uses ports takes their states after its parameters, as state words
        // like any other, and returns them after its value; the states order nothing here,
        // since the code runs the effects in the order of the nodes.
        let states = region.args[..l.params]
            .iter()
            .filter(|a| a.is_state())
            .count();
        if region.results.len() != 1 + states {
            return Err(crate::bug::bug(format_args!(
                "lambda body `{}` has {} results; a body returns one value and the \
                 states of the {} it takes",
                self.t.region_path(l.body),
                region.results.len(),
                if states == 1 {
                    "1 port".to_string()
                } else {
                    format!("{states} ports")
                }
            )));
        }
        self.function(self.bodies[i], 1 + l.params, 1, |cg, fx, ps| {
            let args: Vec<Loc> = ps[1..].iter().map(|w| cg.put(fx, *w)).collect();
            cg.lambda_body(fx, i, ps[0], args)
        })
    }

    /// The code of lambda `i`'s body on the closure `env` and the parameters `args`: the
    /// captures read from `env`, then the body's region.
    fn lambda_body(
        &mut self,
        fx: &mut Fx<'_>,
        i: usize,
        env: W,
        mut args: Vec<Loc>,
    ) -> Result<Vec<W>, String> {
        let l = &self.t.lambdas[i];
        let caps = self.t.nodes[l.node].node().inputs.len();
        for c in 0..caps {
            let k = fx.b.ins().iconst(I64, c as i64);
            let w = self.call(fx, "rt_cap", &[env.0, env.1, k]);
            let w = self.checked(fx, (w[0], w[1]));
            args.push(self.put(fx, w));
        }
        Ok(vec![self.walk(fx, l.body, args)?[0]])
    }

    /// Lambda `i`'s placed entry: it takes the closure's word and the addresses of the
    /// arguments of a call by name, as its call site stored them, and of the byte offsets of a
    /// merge ([`crate::hooks`]' `rt_direct`), reads each parameter at its offset, gives a
    /// reference to each the body consumes, as a call the runtime places gives it, and runs the
    /// body inline (row CALL-callee-places-native).
    // Complexity tradeoff: a call through a function that calls the body on the parameters
    // read at the offsets passes them twice, the second time as the body's arguments, about 4
    // instructions each; inline, one load of the offset and two of the word, against two of
    // the word for a direct call. The cost is a second copy of the body, O(size of the body)
    // more to compile, for each lambda [`Tables::placeable`] keeps.
    fn placed(&mut self, i: usize, id: FuncId) -> Result<(), String> {
        let l = &self.t.lambdas[i];
        self.function(id, 2, 1, |cg, fx, ps| {
            let (args, offs) = ps[1];
            let flags = MemFlagsData::trusted();
            let mut ws = Vec::with_capacity(l.params);
            for j in 0..l.params {
                let off = fx.b.ins().load(I64, flags, offs, 8 * j as i32);
                let at = fx.b.ins().iadd(args, off);
                let tag = fx.b.ins().load(I64, flags, at, 0);
                let bits = fx.b.ins().load(I64, flags, at, 8);
                ws.push((tag, bits));
            }
            let mut kept = Vec::with_capacity(l.params);
            for (w, m) in ws.into_iter().zip(&l.modes) {
                if *m == Mode::Owned {
                    cg.inc(fx, w);
                }
                kept.push(cg.put(fx, w));
            }
            cg.lambda_body(fx, i, ps[0], kept)
        })
    }

    fn entry(&mut self, i: usize) -> Result<(), String> {
        let l = &self.t.lambdas[i];
        self.function(self.entries[i], 1 + l.params, 1, |cg, fx, ps| {
            let flat: Vec<V> = ps.iter().flat_map(|(t, b)| [*t, *b]).collect();
            let kept: Vec<Loc> = ps[1..].iter().map(|w| cg.put(fx, *w)).collect();
            let r = cg.fref(fx, cg.bodies[i]);
            let inst = fx.b.ins().call(r, &flat);
            let out = fx.b.inst_results(inst).to_vec();
            for (j, m) in l.modes.iter().enumerate() {
                if *m == Mode::Borrowed {
                    let w = cg.get(fx, kept[j]);
                    cg.dec(fx, w);
                }
            }
            Ok(vec![(out[0], out[1])])
        })
    }

    /// The function that calls a body of `a` parameters, `a` the arity of
    /// `self.trampolines[i]`, on a buffer [`crate::hooks`]' `rt_named` filled: the body's
    /// address, then the closure's word and the `a` parameters' words, each two `i64`s. It
    /// takes the buffer's address as its one word and gives the body's result. The words are
    /// all loaded before the call, so a call by name inside the body may fill the buffer
    /// again.
    fn trampoline(&mut self, i: usize) -> Result<(), String> {
        let (a, id) = self.trampolines[i];
        self.function(id, 1, 1, |cg, fx, ps| {
            let buf = ps[0].0;
            let flags = MemFlagsData::trusted();
            let addr = fx.b.ins().load(I64, flags, buf, 0);
            let words: Vec<V> = (0..2 * (1 + a))
                .map(|k| fx.b.ins().load(I64, flags, buf, 8 * (1 + k as i32)))
                .collect();
            let s = sig(cg.m, 2 * (1 + a), 2);
            let sr = fx.b.import_signature(s);
            let inst = fx.b.ins().call_indirect(sr, addr, &words);
            let out = fx.b.inst_results(inst).to_vec();
            Ok(vec![(out[0], out[1])])
        })
    }

    fn fref(&mut self, fx: &mut Fx<'_>, id: FuncId) -> FuncRef {
        if let Some(r) = fx.refs.get(&id) {
            return *r;
        }
        let r = self.m.declare_func_in_func(id, fx.b.func);
        fx.refs.insert(id, r);
        r
    }

    fn call(&mut self, fx: &mut Fx<'_>, hook: &str, a: &[V]) -> Vec<V> {
        let r = self.fref(fx, self.hooks[hook]);
        let inst = fx.b.ins().call(r, a);
        fx.b.inst_results(inst).to_vec()
    }

    fn call_word(&mut self, fx: &mut Fx<'_>, hook: &str, a: &[V]) -> W {
        let r = self.call(fx, hook, a);
        self.checked(fx, (r[0], r[1]))
    }

    /// `w`, after leaving the function when it is the error word.
    fn checked(&mut self, fx: &mut Fx<'_>, w: W) -> W {
        let is_err = fx.b.ins().icmp_imm_s(IntCC::Equal, w.0, Word::ERR);
        let ok = fx.b.create_block();
        fx.b.ins().brif(is_err, fx.err, &[], ok, &[]);
        fx.b.switch_to_block(ok);
        w
    }

    fn konst(&mut self, fx: &mut Fx<'_>, w: Word) -> W {
        (
            fx.b.ins().iconst(I64, w.tag),
            fx.b.ins().iconst(I64, w.bits),
        )
    }

    fn src(&self, s: &Src, args: &[Loc], outs: &[Vec<Loc>]) -> Loc {
        match s {
            Src::Arg(i) => args[*i],
            Src::Out(n, p) => outs[*n][*p],
            Src::Const(v) => Loc::Const(Word::scalar(v).unwrap_or_else(|| Word {
                tag: Word::VAL,
                bits: self.t.const_index(v) as i64,
            })),
        }
    }

    /// `w` kept in a new stack slot.
    fn put(&mut self, fx: &mut Fx<'_>, w: W) -> Loc {
        let s =
            fx.b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 16, 3));
        fx.b.ins().stack_store(I64, w.0, s, 0);
        fx.b.ins().stack_store(I64, w.1, s, 8);
        Loc::Slot(s)
    }

    /// The word at `l`.
    fn get(&mut self, fx: &mut Fx<'_>, l: Loc) -> W {
        match l {
            Loc::Slot(s) => (
                fx.b.ins().stack_load(I64, I64, s, 0),
                fx.b.ins().stack_load(I64, I64, s, 8),
            ),
            Loc::Const(w) => self.konst(fx, w),
        }
    }

    fn inc(&mut self, fx: &mut Fx<'_>, w: W) {
        self.on_cell(fx, "rt_inc", w);
    }

    fn dec(&mut self, fx: &mut Fx<'_>, w: W) {
        self.on_cell(fx, "rt_dec", w);
    }

    /// Hook `hook` called on `w` when `w` is a cell: the heap counts references to cells only,
    /// and its `inc` and `dec` change nothing for any other word.
    // Complexity tradeoff: the hook call on every word cost a call and the borrow of the run,
    // about 60 instructions, for a word that is not a cell too; a callee of p `int` parameters
    // dropped each through it, 25% of a placed call's run time at p = 320 (row
    // CALL-callee-places-native). Here one compare and branch per word, and the call for a
    // cell alone; the cost is one more block per count change compiled.
    fn on_cell(&mut self, fx: &mut Fx<'_>, hook: &str, w: W) {
        let next = fx.b.create_block();
        let cell = fx.b.ins().icmp_imm_s(IntCC::Equal, w.0, Word::CELL);
        self.when(fx, cell, next);
        self.call(fx, hook, &[w.0, w.1]);
        fx.b.ins().jump(next, &[]);
        fx.b.switch_to_block(next);
    }

    /// Emits region `at`, its arms inline, on `args`; gives its results.
    fn walk(&mut self, fx: &mut Fx<'_>, at: usize, args: Vec<Loc>) -> Result<Vec<W>, String> {
        let t = self.t;
        let mut stack = vec![self.enter(fx, at, args)];
        while let Some(top) = stack.last_mut() {
            let info = &t.regions[top.at];
            let k = top.outs.len();
            if let Some(open) = &mut top.open {
                let id = info.ids[k];
                let i = open.next;
                if i < open.arms.len() {
                    open.next += 1;
                    fx.b.switch_to_block(open.arms[i]);
                    let mut args = Vec::new();
                    for b in 0..open.binders[i] {
                        let k = fx.b.ins().iconst(I64, b as i64);
                        let w = self.call(fx, "rt_out", &[k]);
                        args.push(self.put(fx, (w[0], w[1])));
                    }
                    args.extend_from_slice(&top.ins[1..]);
                    let f = self.enter(fx, t.nodes[id].subs[i], args);
                    stack.push(f);
                } else {
                    let (merge, fail) = (open.merge, open.fail);
                    fx.b.switch_to_block(fail);
                    self.fail(fx, t.nodes[id].node().outputs.len(), merge);
                    fx.b.switch_to_block(merge);
                    let ws = self.params(fx, merge);
                    self.finish(fx, top, ws);
                }
            } else if k < info.ids.len() {
                let id = info.ids[k];
                let node = t.nodes[id].node();
                let np = &self.plans[top.at].nodes[k];
                top.ins = node
                    .inputs
                    .iter()
                    .map(|s| self.src(s, &top.args, &top.outs))
                    .collect();
                for &j in &np.dups {
                    let w = self.get(fx, top.ins[j]);
                    self.inc(fx, w);
                }
                match &node.op {
                    Op::If => {
                        // An `if` reads its condition only to choose an arm, so an owned
                        // condition the arms do not take is released then.
                        let c = &node.inputs[0];
                        let early = !node.inputs[1..].contains(c) && np.drops.contains(c);
                        top.open = Some(self.branch(fx, id, &top.ins, early));
                    }
                    Op::Match(ps) => {
                        let binders = ps.iter().map(binds).collect();
                        top.open = Some(self.matched(fx, id, binders, &top.ins));
                    }
                    _ => {
                        let ws = self.node(fx, id, &top.ins)?;
                        self.finish(fx, top, ws);
                    }
                }
            } else {
                let r = &info.region;
                for &i in &self.plans[top.at].result_dups {
                    let l = self.src(&r.results[i], &top.args, &top.outs);
                    let w = self.get(fx, l);
                    self.inc(fx, w);
                }
                let mut out = Vec::new();
                for s in &r.results {
                    let l = self.src(s, &top.args, &top.outs);
                    out.push(self.get(fx, l));
                }
                stack.pop();
                let Some(up) = stack.last() else {
                    return Ok(out);
                };
                let open = up.open.as_ref().expect("an arm's node has its arms open");
                self.jump(fx, open.merge, &out);
            }
        }
        unreachable!("the last region returns its results")
    }

    /// The frame of region `at` on `args`, after the drops at its entry.
    fn enter(&mut self, fx: &mut Fx<'_>, at: usize, args: Vec<Loc>) -> Frame {
        for &a in &self.plans[at].entry_drops {
            let w = self.get(fx, args[a]);
            self.dec(fx, w);
        }
        Frame {
            at,
            args,
            outs: Vec::new(),
            ins: Vec::new(),
            open: None,
        }
    }

    /// Ends frame `f`'s next node with outputs `ws`: keeps them and runs the node's drops.
    fn finish(&mut self, fx: &mut Fx<'_>, f: &mut Frame, ws: Vec<W>) {
        let k = f.outs.len();
        let early = f.open.take().is_some_and(|o| o.early);
        let o = ws.into_iter().map(|w| self.put(fx, w)).collect();
        f.outs.push(o);
        let t = self.t;
        let released = early.then(|| &t.nodes[t.regions[f.at].ids[k]].node().inputs[0]);
        for s in &self.plans[f.at].nodes[k].drops {
            if released == Some(s) {
                continue;
            }
            let l = self.src(s, &f.args, &f.outs);
            let w = self.get(fx, l);
            self.dec(fx, w);
        }
    }

    /// The outputs of a node after the first, which are states.
    fn states(&mut self, fx: &mut Fx<'_>, first: W, n: usize) -> Vec<W> {
        let mut out = vec![first];
        for _ in 1..n {
            let w = self.konst(fx, Word::state());
            out.push(w);
        }
        out
    }

    fn node(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[Loc]) -> Result<Vec<W>, String> {
        let t = self.t;
        let node = t.nodes[id].node();
        let n = node.outputs.len();
        Ok(match &node.op {
            Op::Prim(p) if ins.is_empty() && p.arity().is_some() => {
                let i = t.prims.iter().position(|q| q == p).expect("a primitive");
                let w = self.konst(
                    fx,
                    Word {
                        tag: Word::PRIM,
                        bits: i as i64,
                    },
                );
                self.states(fx, w, n)
            }
            Op::Prim(p @ (Prim::Gt | Prim::Ge)) if ins.len() == 2 => {
                let x = if *p == Prim::Gt {
                    Expansion::Gt
                } else {
                    Expansion::Ge
                };
                return Err(crate::bug::bug(format_args!(
                    "`prim {}` has no lowering here; legalization expands it ({}), and \
                     this back end does not declare that expansion",
                    p.printed(),
                    x.name()
                )));
            }
            Op::Prim(p) if inline(*p, ins.len()) => {
                let w = self.inline(fx, *p, id, ins);
                self.states(fx, w, n)
            }
            Op::Apply => self.apply(fx, id, ins)?,
            Op::Prim(Prim::CallNamed)
                if t.nodes[id].named.is_some()
                    && !self.trampolines.is_empty()
                    && t.nodes[id].modes.iter().all(|m| *m != Mode::Owned) =>
            {
                let w = self.named(fx, id, ins);
                self.states(fx, w, n)
            }
            _ => {
                let w = self.slow(fx, id, ins);
                self.states(fx, w, n)
            }
        })
    }

    /// Node `id` run by the runtime on `ins`.
    fn slow(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[Loc]) -> W {
        for l in ins {
            let w = self.get(fx, *l);
            self.call(fx, "rt_arg", &[w.0, w.1]);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        self.call_word(fx, "rt_node", &[k])
    }

    /// Call by name `id` on `ins`, every input borrowed: placed by the runtime (`rt_named`)
    /// and run through the body of the function called, or, where the runtime does not place
    /// it, run by the runtime as any node (row CALL-callee-places-native).
    // Complexity tradeoff: before, every call by name ran in the kernel ([`Gen::slow`]),
    // O(p + a) for p parameters and a arguments with a large constant, and the function's
    // body with it. Here one runtime call merges the names, O(p + a), and the body runs in
    // native code. The arguments are stored straight into the runtime's buffer (`rt_args`),
    // two stores each, where one `rt_arg` hook call each made the placed call 8.4 times the
    // run cost of a direct call at p = 320; a call the runtime does not place runs in the
    // kernel on the same buffer (`rt_named` leaves it). Through `rt_named` the arguments
    // pass three times and the placed call ran 2.6 times the instructions of the direct one;
    // so first, where some lambda has a placed entry of this many parameters, `rt_direct`
    // checks in O(1) that the merge kept for the node is for the closure's list, and the call
    // goes to that entry on the same buffer (`Gen::named_direct`): 1.085 times the direct
    // call's run at p = 320. Nothing is refused.
    fn named(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[Loc]) -> W {
        let merge = self.merge(fx, 1);
        let n = fx.b.ins().iconst(I64, ins.len() as i64);
        let buf = self.call(fx, "rt_args", &[n])[0];
        let flags = MemFlagsData::trusted();
        for (i, l) in ins.iter().enumerate() {
            let w = self.get(fx, *l);
            fx.b.ins().store(flags, w.0, buf, 16 * i as i32);
            fx.b.ins().store(flags, w.1, buf, 16 * i as i32 + 8);
        }
        let sh = self.t.nodes[id].named.as_deref().expect("a literal shape");
        if !sh.flagged && self.direct.contains(&(sh.k + sh.names.len())) {
            self.named_direct(fx, id, ins, buf, merge);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        let r = self.call(fx, "rt_named", &[k]);
        let (call, buf) = (r[0], r[1]);
        self.checked(fx, (call, buf));
        let kern = fx.b.create_block();
        let nz = fx.b.ins().icmp_imm_s(IntCC::NotEqual, call, 0);
        self.when(fx, nz, kern);
        let s = sig(self.m, 2, 2);
        let sr = fx.b.import_signature(s);
        let zero = fx.b.ins().iconst(I64, 0);
        let inst = fx.b.ins().call_indirect(sr, call, &[buf, zero]);
        let out = fx.b.inst_results(inst).to_vec();
        let w = self.checked(fx, (out[0], out[1]));
        self.jump(fx, merge, &[w]);
        fx.b.switch_to_block(kern);
        let k = fx.b.ins().iconst(I64, id as i64);
        let w = self.call_word(fx, "rt_node", &[k]);
        self.jump(fx, merge, &[w]);
        fx.b.switch_to_block(merge);
        self.params(fx, merge)[0]
    }

    /// The call by name `id` on `ins`, its shape with no flag, sent to the placed entry of the
    /// function's lambda when the runtime's merge kept for the node holds for the function's
    /// list (`rt_direct`), with its result to `merge`; else on to the code after, which
    /// places the call through `rt_named`. The entry reads the arguments after the function
    /// where the call site stored `ins` for `rt_named`, at `buf`.
    fn named_direct(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[Loc], buf: V, merge: Block) {
        let f = self.get(fx, ins[1]);
        let k = fx.b.ins().iconst(I64, id as i64);
        let r = self.call(fx, "rt_direct", &[k, f.0, f.1]);
        let (call, offs) = (r[0], r[1]);
        let other = fx.b.create_block();
        let nz = fx.b.ins().icmp_imm_s(IntCC::NotEqual, call, 0);
        self.when(fx, nz, other);
        let args = fx.b.ins().iadd_imm_s(buf, 32);
        let s = sig(self.m, 4, 2);
        let sr = fx.b.import_signature(s);
        let inst = fx.b.ins().call_indirect(sr, call, &[f.0, f.1, args, offs]);
        let out = fx.b.inst_results(inst).to_vec();
        let w = self.checked(fx, (out[0], out[1]));
        self.jump(fx, merge, &[w]);
        fx.b.switch_to_block(other);
    }

    /// The words at `ins`, flat, for a call.
    fn flat(&mut self, fx: &mut Fx<'_>, ins: &[Loc]) -> Vec<V> {
        ins.iter()
            .flat_map(|l| {
                let (t, b) = self.get(fx, *l);
                [t, b]
            })
            .collect()
    }

    /// A block taking `n` words, for the end of a branch.
    fn merge(&mut self, fx: &mut Fx<'_>, n: usize) -> Block {
        let b = fx.b.create_block();
        for _ in 0..2 * n {
            fx.b.append_block_param(b, I64);
        }
        b
    }

    fn params(&mut self, fx: &mut Fx<'_>, b: Block) -> Vec<W> {
        fx.b.block_params(b)
            .chunks(2)
            .map(|c| (c[0], c[1]))
            .collect()
    }

    fn jump(&mut self, fx: &mut Fx<'_>, to: Block, ws: &[W]) {
        fx.b.ins().jump(to, &args(ws));
    }

    /// Whether both words are tagged `tag`.
    fn both(&mut self, fx: &mut Fx<'_>, a: W, b: W, tag: i64) -> V {
        let x = fx.b.ins().icmp_imm_s(IntCC::Equal, a.0, tag);
        let y = fx.b.ins().icmp_imm_s(IntCC::Equal, b.0, tag);
        fx.b.ins().band(x, y)
    }

    /// Continues in a new block when `c` holds, else in `otherwise`.
    fn when(&mut self, fx: &mut Fx<'_>, c: V, otherwise: Block) {
        let yes = fx.b.create_block();
        fx.b.ins().brif(c, yes, &[], otherwise, &[]);
        fx.b.switch_to_block(yes);
    }

    fn float(&mut self, fx: &mut Fx<'_>, x: V) -> V {
        fx.b.ins().bitcast(F64, MemFlagsData::new(), x)
    }

    /// The float word of `r`, a NaN replaced by the canonical NaN, as the kernel does.
    fn float_word(&mut self, fx: &mut Fx<'_>, r: V) -> W {
        let nan = fx.b.ins().fcmp(FloatCC::Unordered, r, r);
        let bits = fx.b.ins().bitcast(I64, MemFlagsData::new(), r);
        let canon = fx.b.ins().iconst(I64, zed_kernel::F64::NAN_BITS as i64);
        let bits = fx.b.ins().select(nan, canon, bits);
        (fx.b.ins().iconst(I64, Word::FLOAT), bits)
    }

    fn bool_word(&mut self, fx: &mut Fx<'_>, c: V) -> W {
        let bits = fx.b.ins().uextend(I64, c);
        (fx.b.ins().iconst(I64, Word::BOOL), bits)
    }

    /// Primitive `p` on scalar words inline, the runtime running every other case.
    fn inline(&mut self, fx: &mut Fx<'_>, p: Prim, id: usize, ins: &[Loc]) -> W {
        let merge = self.merge(fx, 1);
        let slow = fx.b.create_block();
        let a = self.get(fx, ins[0]);
        if ins.len() == 1 {
            let next = fx.b.create_block();
            match p {
                Prim::Neg => {
                    let c = fx.b.ins().icmp_imm_s(IntCC::Equal, a.0, Word::INT);
                    self.when(fx, c, next);
                    let min = fx.b.ins().icmp_imm_s(IntCC::Equal, a.1, i64::MIN);
                    let ok = fx.b.create_block();
                    fx.b.ins().brif(min, slow, &[], ok, &[]);
                    fx.b.switch_to_block(ok);
                    let r = fx.b.ins().ineg(a.1);
                    let tag = fx.b.ins().iconst(I64, Word::INT);
                    self.jump(fx, merge, &[(tag, r)]);
                    fx.b.switch_to_block(next);
                    let c = fx.b.ins().icmp_imm_s(IntCC::Equal, a.0, Word::FLOAT);
                    self.when(fx, c, slow);
                    let x = self.float(fx, a.1);
                    let r = fx.b.ins().fneg(x);
                    let w = self.float_word(fx, r);
                    self.jump(fx, merge, &[w]);
                }
                Prim::Not => {
                    let c = fx.b.ins().icmp_imm_s(IntCC::Equal, a.0, Word::BOOL);
                    self.when(fx, c, slow);
                    let r = fx.b.ins().bxor_imm_s(a.1, 1);
                    self.jump(fx, merge, &[(a.0, r)]);
                    fx.b.switch_to_block(next);
                    fx.b.ins().jump(slow, &[]);
                }
                Prim::Sqrt => {
                    // IEEE 754 `squareRoot` (IEEE Std 754-2019, "IEEE Standard for
                    // Floating-Point Arithmetic", IEEE, 2019, section 5.4.1): one `sqrtsd`,
                    // O(1). Only an `f64` runs here. An `f32` has no word tag of its own (a
                    // `Word::VAL` in the heap's table), so it takes the kernel call, as all
                    // `f32` arithmetic in native code does; a tag for it would make every
                    // `f32` operation inline, a change beyond this primitive. Measured: the
                    // same bits as the kernel on 900 random operands (test
                    // `l01_18_scalar_interpreter::sqrt_fma`).
                    let c = fx.b.ins().icmp_imm_s(IntCC::Equal, a.0, Word::FLOAT);
                    self.when(fx, c, slow);
                    let x = self.float(fx, a.1);
                    let r = fx.b.ins().sqrt(x);
                    let w = self.float_word(fx, r);
                    self.jump(fx, merge, &[w]);
                    fx.b.switch_to_block(next);
                    fx.b.ins().jump(slow, &[]);
                }
                _ => unreachable!("checked by `inline`"),
            }
        } else if p == Prim::Fma {
            // IEEE 754 `fusedMultiplyAdd` (IEEE Std 754-2019, section 5.4.1), rounded once:
            // one `vfmadd` where the host has FMA, else the C library's `fma`, which Cranelift
            // calls in its place; O(1) either way. As for `sqrt`, an `f32` takes the kernel
            // call. Cranelift never fuses a separate `fmul` and `fadd`, so a written
            // `a * b + c` keeps its two roundings (test `l01_18_scalar_interpreter::sqrt_fma`
            // shows the two differ).
            let (b, c) = (self.get(fx, ins[1]), self.get(fx, ins[2]));
            let ab = self.both(fx, a, b, Word::FLOAT);
            let cf = fx.b.ins().icmp_imm_s(IntCC::Equal, c.0, Word::FLOAT);
            let all = fx.b.ins().band(ab, cf);
            self.when(fx, all, slow);
            let (x, y, z) = (
                self.float(fx, a.1),
                self.float(fx, b.1),
                self.float(fx, c.1),
            );
            let r = fx.b.ins().fma(x, y, z);
            let w = self.float_word(fx, r);
            self.jump(fx, merge, &[w]);
        } else {
            let b = self.get(fx, ins[1]);
            let int = int_op(p) || int_cmp(p).is_some();
            let float = float_op(p) || float_cmp(p).is_some();
            if int {
                let next = fx.b.create_block();
                let c = self.both(fx, a, b, Word::INT);
                self.when(fx, c, next);
                let tag = fx.b.ins().iconst(I64, Word::INT);
                if let Some(cc) = int_cmp(p) {
                    let c = fx.b.ins().icmp(cc, a.1, b.1);
                    let w = self.bool_word(fx, c);
                    self.jump(fx, merge, &[w]);
                } else {
                    let (r, of) = match p {
                        Prim::Add => fx.b.ins().sadd_overflow(a.1, b.1),
                        Prim::Sub => fx.b.ins().ssub_overflow(a.1, b.1),
                        _ => fx.b.ins().smul_overflow(a.1, b.1),
                    };
                    fx.b.ins().brif(of, slow, &[], merge, &args(&[(tag, r)]));
                }
                fx.b.switch_to_block(next);
            }
            if float {
                let next = fx.b.create_block();
                let c = self.both(fx, a, b, Word::FLOAT);
                self.when(fx, c, next);
                let (x, y) = (self.float(fx, a.1), self.float(fx, b.1));
                if let Some(cc) = float_cmp(p) {
                    let c = fx.b.ins().fcmp(cc, x, y);
                    let w = self.bool_word(fx, c);
                    self.jump(fx, merge, &[w]);
                } else {
                    let r = match p {
                        Prim::Add => fx.b.ins().fadd(x, y),
                        Prim::Sub => fx.b.ins().fsub(x, y),
                        Prim::Mul => fx.b.ins().fmul(x, y),
                        Prim::Min => fx.b.ins().fmin(x, y),
                        Prim::Max => fx.b.ins().fmax(x, y),
                        _ => fx.b.ins().fdiv(x, y),
                    };
                    let w = self.float_word(fx, r);
                    self.jump(fx, merge, &[w]);
                }
                fx.b.switch_to_block(next);
            }
            if p == Prim::Pow {
                self.pow(fx, id, a, b, merge);
            }
            if matches!(p, Prim::And | Prim::Or) {
                let next = fx.b.create_block();
                let c = self.both(fx, a, b, Word::BOOL);
                self.when(fx, c, next);
                let r = match p {
                    Prim::And => fx.b.ins().band(a.1, b.1),
                    _ => fx.b.ins().bor(a.1, b.1),
                };
                self.jump(fx, merge, &[(a.0, r)]);
                fx.b.switch_to_block(next);
            }
            fx.b.ins().jump(slow, &[]);
        }
        fx.b.switch_to_block(slow);
        let w = self.slow(fx, id, ins);
        self.jump(fx, merge, &[w]);
        fx.b.switch_to_block(merge);
        self.params(fx, merge)[0]
    }

    /// Float `^` of node `id` on words `a` and `b` when both are floats, by `rt_pow`, its
    /// result jumping to `merge`; any other operands continue in a new block. NaN in, NaN out
    /// (DESIGN.md sec:domains, NaN rule 5), where IEEE 754 `pow` gives `pow(NaN, 0) = 1` and
    /// `pow(1, NaN) = 1`: an operand the graph does not rule the NaN out of is tested, one
    /// `fcmp uno` for one such operand or for two, and an operand it does is not.
    fn pow(&mut self, fx: &mut Fx<'_>, id: usize, a: W, b: W, merge: Block) {
        let t = self.t;
        let ni = &t.nodes[id];
        let next = fx.b.create_block();
        let c = self.both(fx, a, b, Word::FLOAT);
        self.when(fx, c, next);
        let tag = fx.b.ins().iconst(I64, Word::FLOAT);
        let test = match (ni.may_be_nan(0), ni.may_be_nan(1)) {
            (true, true) => Some((a.1, b.1)),
            (true, false) => Some((a.1, a.1)),
            (false, true) => Some((b.1, b.1)),
            (false, false) => None,
        };
        if let Some((u, v)) = test {
            let (x, y) = (self.float(fx, u), self.float(fx, v));
            let nan = fx.b.ins().fcmp(FloatCC::Unordered, x, y);
            let canon = fx.b.ins().iconst(I64, zed_kernel::F64::NAN_BITS as i64);
            let call = fx.b.create_block();
            fx.b.ins()
                .brif(nan, merge, &args(&[(tag, canon)]), call, &[]);
            fx.b.switch_to_block(call);
        }
        let r = self.call(fx, "rt_pow", &[a.1, b.1])[0];
        self.jump(fx, merge, &[(tag, r)]);
        fx.b.switch_to_block(next);
    }

    /// A call: directly when the plan resolves the callee and the closure is it, through
    /// the closure's entry when its arity fits, else by the runtime.
    fn apply(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[Loc]) -> Result<Vec<W>, String> {
        let t = self.t;
        let ni = &t.nodes[id];
        let n = ni.node().outputs.len();
        let merge = self.merge(fx, n);
        let generic = fx.b.create_block();
        let f = self.get(fx, ins[0]);
        let nargs = fx.b.ins().iconst(I64, ins.len() as i64 - 1);
        let lam = self.call(fx, "rt_callable", &[f.0, f.1, nargs])[0];
        if let Some(li) = ni.callee {
            let is = fx.b.ins().icmp_imm_s(IntCC::Equal, lam, li as i64 + 1);
            self.when(fx, is, generic);
            if ni.error.is_some() {
                let k = fx.b.ins().iconst(I64, id as i64);
                self.call_word(fx, "rt_error", &[k]);
                fx.b.ins().jump(fx.err, &[]);
            } else {
                let flat = self.flat(fx, ins);
                let r = self.fref(fx, self.bodies[li]);
                let inst = fx.b.ins().call(r, &flat);
                let out = fx.b.inst_results(inst).to_vec();
                let w = self.checked(fx, (out[0], out[1]));
                for (i, m) in t.lambdas[li].modes.iter().enumerate() {
                    if ni.modes[1 + i] == Mode::Owned && *m == Mode::Borrowed {
                        let w = self.get(fx, ins[1 + i]);
                        self.dec(fx, w);
                    }
                }
                let ws = self.states(fx, w, n);
                self.jump(fx, merge, &ws);
            }
        } else {
            fx.b.ins().jump(generic, &[]);
        }
        fx.b.switch_to_block(generic);
        let kern = fx.b.create_block();
        let nz = fx.b.ins().icmp_imm_s(IntCC::NotEqual, lam, 0);
        self.when(fx, nz, kern);
        let li = fx.b.ins().iadd_imm_s(lam, -1);
        let addr = self.call(fx, "rt_entry", &[li])[0];
        let s = sig(self.m, 2 * ins.len(), 2);
        let sr = fx.b.import_signature(s);
        let flat = self.flat(fx, ins);
        let inst = fx.b.ins().call_indirect(sr, addr, &flat);
        let out = fx.b.inst_results(inst).to_vec();
        let w = self.checked(fx, (out[0], out[1]));
        let ws = self.states(fx, w, n);
        self.jump(fx, merge, &ws);
        fx.b.switch_to_block(kern);
        let w = self.slow(fx, id, ins);
        let ws = self.states(fx, w, n);
        self.jump(fx, merge, &ws);
        fx.b.switch_to_block(merge);
        Ok(self.params(fx, merge))
    }

    /// The runtime's failure word as the node's result, the other outputs states.
    fn fail(&mut self, fx: &mut Fx<'_>, n: usize, merge: Block) {
        let w = self.call_word(fx, "rt_pending", &[]);
        let ws = self.states(fx, w, n);
        self.jump(fx, merge, &ws);
    }

    /// Dispatches on code `r`: `blocks[i]` for `i`, else the error exit, by one jump table
    /// rather than a test per block.
    fn dispatch(&mut self, fx: &mut Fx<'_>, r: V, blocks: &[Block]) {
        let mut s = Switch::new();
        for (i, b) in blocks.iter().enumerate() {
            s.set_entry(i as u128, *b);
        }
        s.emit(&mut fx.b, r, fx.err);
    }

    /// The test of `if` node `id`; `early` releases the condition once an arm is chosen.
    fn branch(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[Loc], early: bool) -> Open {
        let n = self.t.nodes[id].node().outputs.len();
        let merge = self.merge(fx, n);
        let arms = vec![fx.b.create_block(), fx.b.create_block()];
        let fail = fx.b.create_block();
        let slow = fx.b.create_block();
        let c = self.get(fx, ins[0]);
        let is = fx.b.ins().icmp_imm_s(IntCC::Equal, c.0, Word::BOOL);
        self.when(fx, is, slow);
        fx.b.ins().brif(c.1, arms[0], &[], arms[1], &[]);
        fx.b.switch_to_block(slow);
        for l in ins {
            let w = self.get(fx, *l);
            self.call(fx, "rt_arg", &[w.0, w.1]);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        let r = self.call(fx, "rt_branch", &[k])[0];
        // On the fast path the condition is a bool, which holds no cell to release.
        if early {
            self.dec(fx, c);
        }
        self.dispatch(fx, r, &[arms[0], arms[1], fail]);
        Open {
            merge,
            fail,
            arms,
            binders: vec![0, 0],
            next: 0,
            early,
        }
    }

    /// The test of `match` node `id`, whose arms have `binders` binders.
    fn matched(&mut self, fx: &mut Fx<'_>, id: usize, binders: Vec<usize>, ins: &[Loc]) -> Open {
        let n = self.t.nodes[id].node().outputs.len();
        let merge = self.merge(fx, n);
        for l in ins {
            let w = self.get(fx, *l);
            self.call(fx, "rt_arg", &[w.0, w.1]);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        let r = self.call(fx, "rt_match", &[k])[0];
        let mut arms: Vec<Block> = binders.iter().map(|_| fx.b.create_block()).collect();
        let fail = fx.b.create_block();
        arms.push(fail);
        self.dispatch(fx, r, &arms);
        arms.pop();
        Open {
            merge,
            fail,
            arms,
            binders,
            next: 0,
            early: false,
        }
    }
}

/// Whether primitive `p` on `n` inputs has an inline path.
fn inline(p: Prim, n: usize) -> bool {
    match n {
        1 => matches!(p, Prim::Neg | Prim::Not | Prim::Sqrt),
        2 => {
            int_op(p)
                || int_cmp(p).is_some()
                || float_op(p)
                || float_cmp(p).is_some()
                || matches!(p, Prim::And | Prim::Or | Prim::Pow)
        }
        3 => p == Prim::Fma,
        _ => false,
    }
}

fn int_op(p: Prim) -> bool {
    matches!(p, Prim::Add | Prim::Sub | Prim::Mul)
}

fn int_cmp(p: Prim) -> Option<IntCC> {
    Some(match p {
        Prim::Lt => IntCC::SignedLessThan,
        Prim::Le => IntCC::SignedLessThanOrEqual,
        Prim::Eq => IntCC::Equal,
        Prim::Ne => IntCC::NotEqual,
        _ => return None,
    })
}

/// The float operations with a float result. `min` and `max` are Cranelift's `fmin` and `fmax`,
/// whose WebAssembly rules are IEEE 754-2019 `minimum` and `maximum` up to the NaN's bits, which
/// [`Gen::float_word`] makes canonical: a NaN in either position gives the NaN, and `-0.0` is
/// below `0.0` (DESIGN.md sec:reduction, item 5). `min` and `max` on ints run in the kernel.
fn float_op(p: Prim) -> bool {
    matches!(
        p,
        Prim::Add | Prim::Sub | Prim::Mul | Prim::Div | Prim::Min | Prim::Max
    )
}

/// The float comparisons, ordered (`>` and `>=` are legalized to `<` and `<=`), so a NaN compares false as the kernel's do; `==` and
/// `!=` on floats are the kernel's surface equality and are not inline.
fn float_cmp(p: Prim) -> Option<FloatCC> {
    Some(match p {
        Prim::Lt => FloatCC::LessThan,
        Prim::Le => FloatCC::LessThanOrEqual,
        _ => return None,
    })
}
