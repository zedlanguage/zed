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
//! the node as the counting machine does. After each call that returns a word, an error
//! word leaves the function, returning the error word.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::types::{F64, I64};
use cranelift_codegen::ir::{AbiParam, Block, BlockArg, FuncRef, InstBuilder, MemFlagsData};
use cranelift_codegen::ir::{Signature, Value as V};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module};

use zed_kernel::Prim;
use zedc::zir::memory::{Mode, Plan};
use zedc::zir::{Op, Region, Src, binds};

use zed_rt::Word;

use crate::hooks::HOOKS;
use crate::tables::Tables;

/// A word in generated code: its tag and its payload.
type W = (V, V);

fn err(e: impl std::fmt::Display) -> String {
    format!("native: {e}")
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
    plan: &'a Plan,
    hooks: HashMap<&'static str, FuncId>,
    bodies: Vec<FuncId>,
    entries: Vec<FuncId>,
}

/// One function being built.
struct Fx<'b> {
    b: FunctionBuilder<'b>,
    refs: HashMap<FuncId, FuncRef>,
    err: Block,
}

/// Declares and defines every function of graph `g` under `plan` in `m`.
pub(crate) fn define<M: Module>(
    m: &mut M,
    t: &Tables,
    plan: &Plan,
    g: &Region,
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
    let root = m
        .declare_function("zed_root", Linkage::Export, &sig(m, 0, 2))
        .map_err(err)?;
    let mut cg = Gen {
        m,
        t,
        plan,
        hooks,
        bodies,
        entries,
    };
    cg.root(root, g)?;
    for i in 0..t.lambdas.len() {
        cg.body(i)?;
        cg.entry(i)?;
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
        self.m.define_function(id, &mut ctx).map_err(err)?;
        self.m.clear_context(&mut ctx);
        Ok(())
    }

    fn root(&mut self, id: FuncId, g: &Region) -> Result<(), String> {
        self.function(id, 0, 1, |cg, fx, _| {
            for i in 0..cg.t.lambdas.len() {
                let r = cg.fref(fx, cg.entries[i]);
                let a = fx.b.ins().func_addr(I64, r);
                let l = fx.b.ins().iconst(I64, i as i64);
                cg.call(fx, "rt_register", &[l, a]);
            }
            let args: Vec<W> = g.args.iter().map(|_| cg.konst(fx, Word::state())).collect();
            let out = cg.region(fx, g, "r", args)?;
            Ok(vec![out[0]])
        })
    }

    fn body(&mut self, i: usize) -> Result<(), String> {
        let l = &self.t.lambdas[i];
        let node = &self.t.nodes[l.node].node;
        let region = &node.regions[0];
        // A body that uses ports takes their states after its parameters, as state words
        // like any other, and returns them after its value; the states order nothing here,
        // since the code runs the effects in the order of the nodes.
        let states = region.args[..l.params]
            .iter()
            .filter(|a| a.is_state())
            .count();
        if region.results.len() != 1 + states {
            return Err(format!(
                "native: lambda body `{}` has {} results; a body returns one value and the \
                 states of the {} it takes",
                l.path,
                region.results.len(),
                if states == 1 {
                    "1 port".to_string()
                } else {
                    format!("{states} ports")
                }
            ));
        }
        let caps = node.inputs.len();
        self.function(self.bodies[i], 1 + l.params, 1, |cg, fx, ps| {
            let env = ps[0];
            let mut args = ps[1..].to_vec();
            for c in 0..caps {
                let k = fx.b.ins().iconst(I64, c as i64);
                let w = cg.call(fx, "rt_cap", &[env.0, env.1, k]);
                args.push(cg.checked(fx, (w[0], w[1])));
            }
            Ok(vec![cg.region(fx, region, &l.path, args)?[0]])
        })
    }

    fn entry(&mut self, i: usize) -> Result<(), String> {
        let l = &self.t.lambdas[i];
        self.function(self.entries[i], 1 + l.params, 1, |cg, fx, ps| {
            let flat: Vec<V> = ps.iter().flat_map(|(t, b)| [*t, *b]).collect();
            let r = cg.fref(fx, cg.bodies[i]);
            let inst = fx.b.ins().call(r, &flat);
            let out = fx.b.inst_results(inst).to_vec();
            for (j, m) in l.modes.iter().enumerate() {
                if *m == Mode::Borrowed {
                    cg.call(fx, "rt_dec", &[ps[1 + j].0, ps[1 + j].1]);
                }
            }
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

    fn src(&mut self, fx: &mut Fx<'_>, s: &Src, args: &[W], outs: &[Vec<W>]) -> W {
        match s {
            Src::Arg(i) => args[*i],
            Src::Out(n, p) => outs[*n][*p],
            Src::Const(v) => {
                let w = Word::scalar(v).unwrap_or_else(|| Word {
                    tag: Word::VAL,
                    bits: self.t.const_index(v) as i64,
                });
                self.konst(fx, w)
            }
        }
    }

    fn inc(&mut self, fx: &mut Fx<'_>, w: W) {
        self.call(fx, "rt_inc", &[w.0, w.1]);
    }

    fn dec(&mut self, fx: &mut Fx<'_>, w: W) {
        self.call(fx, "rt_dec", &[w.0, w.1]);
    }

    fn region(
        &mut self,
        fx: &mut Fx<'_>,
        r: &Region,
        path: &str,
        args: Vec<W>,
    ) -> Result<Vec<W>, String> {
        let plan = self.plan;
        let rp = plan
            .regions
            .get(path)
            .ok_or_else(|| format!("native: region `{path}` has no plan"))?;
        for &a in &rp.entry_drops {
            self.dec(fx, args[a]);
        }
        let mut outs: Vec<Vec<W>> = Vec::new();
        for (k, node) in r.nodes.iter().enumerate() {
            let at = format!("{path}.{k}");
            let np = &rp.nodes[k];
            let ins: Vec<W> = node
                .inputs
                .iter()
                .map(|s| self.src(fx, s, &args, &outs))
                .collect();
            for &j in &np.dups {
                self.inc(fx, ins[j]);
            }
            let o = self.node(fx, &at, &ins)?;
            outs.push(o);
            for s in &np.drops {
                let w = self.src(fx, s, &args, &outs);
                self.dec(fx, w);
            }
        }
        let mut out = Vec::new();
        for (i, s) in r.results.iter().enumerate() {
            let w = self.src(fx, s, &args, &outs);
            if rp.result_dups.contains(&i) {
                self.inc(fx, w);
            }
            out.push(w);
        }
        Ok(out)
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

    fn node(&mut self, fx: &mut Fx<'_>, at: &str, ins: &[W]) -> Result<Vec<W>, String> {
        let t = self.t;
        let id = t.ids[at];
        let node = &t.nodes[id].node;
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
            Op::Prim(p) if inline(*p, ins.len()) => {
                let w = self.inline(fx, *p, id, ins);
                self.states(fx, w, n)
            }
            Op::Apply => self.apply(fx, id, ins)?,
            Op::If => self.branch(fx, id, at, ins)?,
            Op::Match(ps) => self.matched(fx, id, at, ps.iter().map(binds).collect(), ins)?,
            _ => {
                let w = self.slow(fx, id, ins);
                self.states(fx, w, n)
            }
        })
    }

    /// Node `id` run by the runtime on `ins`.
    fn slow(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[W]) -> W {
        for w in ins {
            self.call(fx, "rt_arg", &[w.0, w.1]);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        self.call_word(fx, "rt_node", &[k])
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
        let canon = fx.b.ins().iconst(I64, f64::NAN.to_bits() as i64);
        let bits = fx.b.ins().select(nan, canon, bits);
        (fx.b.ins().iconst(I64, Word::FLOAT), bits)
    }

    fn bool_word(&mut self, fx: &mut Fx<'_>, c: V) -> W {
        let bits = fx.b.ins().uextend(I64, c);
        (fx.b.ins().iconst(I64, Word::BOOL), bits)
    }

    /// Primitive `p` on scalar words inline, the runtime running every other case.
    fn inline(&mut self, fx: &mut Fx<'_>, p: Prim, id: usize, ins: &[W]) -> W {
        let merge = self.merge(fx, 1);
        let slow = fx.b.create_block();
        let a = ins[0];
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
                _ => unreachable!("checked by `inline`"),
            }
        } else {
            let b = ins[1];
            let int = int_op(p).is_some() || int_cmp(p).is_some();
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
                        _ => fx.b.ins().fdiv(x, y),
                    };
                    let w = self.float_word(fx, r);
                    self.jump(fx, merge, &[w]);
                }
                fx.b.switch_to_block(next);
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

    /// A call: directly when the plan resolves the callee and the closure is it, through
    /// the closure's entry when its arity fits, else by the runtime.
    fn apply(&mut self, fx: &mut Fx<'_>, id: usize, ins: &[W]) -> Result<Vec<W>, String> {
        let t = self.t;
        let ni = &t.nodes[id];
        let n = ni.node.outputs.len();
        let merge = self.merge(fx, n);
        let generic = fx.b.create_block();
        let f = ins[0];
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
                let flat: Vec<V> = ins.iter().flat_map(|(t, b)| [*t, *b]).collect();
                let r = self.fref(fx, self.bodies[li]);
                let inst = fx.b.ins().call(r, &flat);
                let out = fx.b.inst_results(inst).to_vec();
                let w = self.checked(fx, (out[0], out[1]));
                for (i, m) in t.lambdas[li].modes.iter().enumerate() {
                    if ni.modes[1 + i] == Mode::Owned && *m == Mode::Borrowed {
                        self.dec(fx, ins[1 + i]);
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
        let flat: Vec<V> = ins.iter().flat_map(|(t, b)| [*t, *b]).collect();
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

    /// Emits arm `i` of node `id` inline on `args`, then jumps to `merge`.
    fn arm(
        &mut self,
        fx: &mut Fx<'_>,
        id: usize,
        at: &str,
        i: usize,
        args: Vec<W>,
        merge: Block,
    ) -> Result<(), String> {
        let t = self.t;
        let region = &t.nodes[id].node.regions[i];
        let out = self.region(fx, region, &format!("{at}/{i}"), args)?;
        self.jump(fx, merge, &out);
        Ok(())
    }

    /// The runtime's failure word as the node's result, the other outputs states.
    fn fail(&mut self, fx: &mut Fx<'_>, n: usize, merge: Block) {
        let w = self.call_word(fx, "rt_pending", &[]);
        let ws = self.states(fx, w, n);
        self.jump(fx, merge, &ws);
    }

    /// Dispatches on code `r`: `blocks[i]` for `i`, else the error exit.
    fn dispatch(&mut self, fx: &mut Fx<'_>, r: V, blocks: &[Block]) {
        for (i, b) in blocks.iter().enumerate() {
            let c = fx.b.ins().icmp_imm_s(IntCC::Equal, r, i as i64);
            let next = fx.b.create_block();
            fx.b.ins().brif(c, *b, &[], next, &[]);
            fx.b.switch_to_block(next);
        }
        fx.b.ins().jump(fx.err, &[]);
    }

    fn branch(
        &mut self,
        fx: &mut Fx<'_>,
        id: usize,
        at: &str,
        ins: &[W],
    ) -> Result<Vec<W>, String> {
        let n = self.t.nodes[id].node.outputs.len();
        let merge = self.merge(fx, n);
        let arms = [fx.b.create_block(), fx.b.create_block()];
        let fail = fx.b.create_block();
        let slow = fx.b.create_block();
        let c = ins[0];
        let is = fx.b.ins().icmp_imm_s(IntCC::Equal, c.0, Word::BOOL);
        self.when(fx, is, slow);
        fx.b.ins().brif(c.1, arms[0], &[], arms[1], &[]);
        fx.b.switch_to_block(slow);
        for w in ins {
            self.call(fx, "rt_arg", &[w.0, w.1]);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        let r = self.call(fx, "rt_branch", &[k])[0];
        self.dispatch(fx, r, &[arms[0], arms[1], fail]);
        for (i, b) in arms.into_iter().enumerate() {
            fx.b.switch_to_block(b);
            self.arm(fx, id, at, i, ins[1..].to_vec(), merge)?;
        }
        fx.b.switch_to_block(fail);
        self.fail(fx, n, merge);
        fx.b.switch_to_block(merge);
        Ok(self.params(fx, merge))
    }

    fn matched(
        &mut self,
        fx: &mut Fx<'_>,
        id: usize,
        at: &str,
        binders: Vec<usize>,
        ins: &[W],
    ) -> Result<Vec<W>, String> {
        let n = self.t.nodes[id].node.outputs.len();
        let merge = self.merge(fx, n);
        for w in ins {
            self.call(fx, "rt_arg", &[w.0, w.1]);
        }
        let k = fx.b.ins().iconst(I64, id as i64);
        let r = self.call(fx, "rt_match", &[k])[0];
        let mut blocks: Vec<Block> = binders.iter().map(|_| fx.b.create_block()).collect();
        let fail = fx.b.create_block();
        blocks.push(fail);
        self.dispatch(fx, r, &blocks);
        for (i, nb) in binders.iter().enumerate() {
            fx.b.switch_to_block(blocks[i]);
            let mut args = Vec::new();
            for b in 0..*nb {
                let k = fx.b.ins().iconst(I64, b as i64);
                let w = self.call(fx, "rt_out", &[k]);
                args.push((w[0], w[1]));
            }
            args.extend_from_slice(&ins[1..]);
            self.arm(fx, id, at, i, args, merge)?;
        }
        fx.b.switch_to_block(fail);
        self.fail(fx, n, merge);
        fx.b.switch_to_block(merge);
        Ok(self.params(fx, merge))
    }
}

/// Whether primitive `p` on `n` inputs has an inline path.
fn inline(p: Prim, n: usize) -> bool {
    match n {
        1 => matches!(p, Prim::Neg | Prim::Not),
        2 => {
            int_op(p).is_some()
                || int_cmp(p).is_some()
                || float_op(p)
                || float_cmp(p).is_some()
                || matches!(p, Prim::And | Prim::Or)
        }
        _ => false,
    }
}

fn int_op(p: Prim) -> Option<()> {
    matches!(p, Prim::Add | Prim::Sub | Prim::Mul).then_some(())
}

fn int_cmp(p: Prim) -> Option<IntCC> {
    Some(match p {
        Prim::Lt => IntCC::SignedLessThan,
        Prim::Le => IntCC::SignedLessThanOrEqual,
        Prim::Gt => IntCC::SignedGreaterThan,
        Prim::Ge => IntCC::SignedGreaterThanOrEqual,
        Prim::Eq => IntCC::Equal,
        Prim::Ne => IntCC::NotEqual,
        _ => return None,
    })
}

fn float_op(p: Prim) -> bool {
    matches!(p, Prim::Add | Prim::Sub | Prim::Mul | Prim::Div)
}

/// The float comparisons, ordered, so a NaN compares false as the kernel's do; `==` and
/// `!=` on floats are the kernel's surface equality and are not inline.
fn float_cmp(p: Prim) -> Option<FloatCC> {
    Some(match p {
        Prim::Lt => FloatCC::LessThan,
        Prim::Le => FloatCC::LessThanOrEqual,
        Prim::Gt => FloatCC::GreaterThan,
        Prim::Ge => FloatCC::GreaterThanOrEqual,
        _ => return None,
    })
}
