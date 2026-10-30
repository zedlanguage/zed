//! The runtime the generated code calls: every node it does not run inline, every count
//! write, and the decisions of `if` and `match` it cannot make from a tag. Each hook does
//! what the counting machine of step L1.34 does for the same node, on words, so a native run
//! makes the machine's allocations and count writes one for one.
//!
//! The state of the run in progress lives in a thread-local slot; a hook never calls back
//! into generated code, so the slot is never borrowed twice.

use std::cell::RefCell;
use std::sync::Arc;

use zed_kernel::{Evaluator, KernelError, Pattern, Prim, Term, Value};
use zedc::zir::Op;
use zedc::zir::lower::raise_with;
use zedc::zir::memory::Mode;

use zed_rt::{Heap, Obj, Rope, Word};

use crate::tables::{NodeInfo, Tables};

/// A match's binders: each word, and its path in the scrutinee when native matching found it.
type Binders = Vec<(Word, Option<Vec<usize>>)>;

/// The state of one native run.
pub(crate) struct State {
    pub heap: Heap,
    pub ev: Evaluator,
    pub t: Arc<Tables>,
    args: Vec<Word>,
    outs: Vec<Word>,
    pending: Word,
    pub err: Option<String>,
    entries: Vec<i64>,
    pub kernel_calls: u64,
}

impl State {
    pub fn new(t: Arc<Tables>, ev: Evaluator) -> State {
        let mut heap = Heap::new();
        for (i, v) in t.consts.iter().enumerate() {
            let w = heap.uncounted(v.clone());
            debug_assert_eq!(w.bits as usize, i);
        }
        State {
            heap,
            ev,
            entries: vec![0; t.lambdas.len()],
            t,
            args: Vec::new(),
            outs: Vec::new(),
            pending: Word::err(),
            err: None,
            kernel_calls: 0,
        }
    }
}

thread_local! {
    static STATE: RefCell<Option<State>> = const { RefCell::new(None) };
}

/// Installs `s` as this thread's run.
pub(crate) fn install(s: State) {
    STATE.with(|c| *c.borrow_mut() = Some(s));
}

/// Removes this thread's run.
pub(crate) fn remove() -> State {
    STATE.with(|c| c.borrow_mut().take().expect("a run is installed"))
}

fn with<R>(f: impl FnOnce(&mut State) -> R) -> R {
    STATE.with(|c| f(c.borrow_mut().as_mut().expect("a run is installed")))
}

/// `r`'s word, or the error word with the message recorded.
fn word(s: &mut State, r: Result<Word, String>) -> Word {
    r.unwrap_or_else(|e| {
        s.err.get_or_insert(e);
        Word::err()
    })
}

fn code(s: &mut State, r: Result<i64, String>) -> i64 {
    r.unwrap_or_else(|e| {
        s.err.get_or_insert(e);
        -1
    })
}

/// Every hook: its symbol, its number of parameters and of results.
pub(crate) const HOOKS: &[(&str, usize, usize)] = &[
    ("rt_arg", 2, 0),
    ("rt_node", 1, 2),
    ("rt_inc", 2, 0),
    ("rt_dec", 2, 0),
    ("rt_cap", 3, 2),
    ("rt_callable", 3, 1),
    ("rt_entry", 1, 1),
    ("rt_register", 2, 0),
    ("rt_branch", 1, 1),
    ("rt_match", 1, 1),
    ("rt_out", 1, 2),
    ("rt_pending", 0, 2),
    ("rt_error", 1, 2),
];

/// Each hook's address, in the order of [`HOOKS`].
pub(crate) fn addresses() -> Vec<*const u8> {
    vec![
        rt_arg as extern "C" fn(i64, i64) as *const u8,
        rt_node as extern "C" fn(i64) -> Word as *const u8,
        rt_inc as extern "C" fn(i64, i64) as *const u8,
        rt_dec as extern "C" fn(i64, i64) as *const u8,
        rt_cap as extern "C" fn(i64, i64, i64) -> Word as *const u8,
        rt_callable as extern "C" fn(i64, i64, i64) -> i64 as *const u8,
        rt_entry as extern "C" fn(i64) -> i64 as *const u8,
        rt_register as extern "C" fn(i64, i64) as *const u8,
        rt_branch as extern "C" fn(i64) -> i64 as *const u8,
        rt_match as extern "C" fn(i64) -> i64 as *const u8,
        rt_out as extern "C" fn(i64) -> Word as *const u8,
        rt_pending as extern "C" fn() -> Word as *const u8,
        rt_error as extern "C" fn(i64) -> Word as *const u8,
    ]
}

extern "C" fn rt_arg(tag: i64, bits: i64) {
    with(|s| s.args.push(Word { tag, bits }));
}

extern "C" fn rt_node(id: i64) -> Word {
    with(|s| {
        let ins = std::mem::take(&mut s.args);
        let r = node(s, id as usize, ins);
        word(s, r)
    })
}

extern "C" fn rt_inc(tag: i64, bits: i64) {
    with(|s| s.heap.inc(Word { tag, bits }));
}

extern "C" fn rt_dec(tag: i64, bits: i64) {
    with(|s| {
        if let Err(e) = s.heap.dec(Word { tag, bits }) {
            s.err.get_or_insert(e);
        }
    });
}

extern "C" fn rt_cap(tag: i64, bits: i64, i: i64) -> Word {
    with(|s| {
        let r = s.heap.capture(Word { tag, bits }, i as usize);
        word(s, r)
    })
}

extern "C" fn rt_callable(tag: i64, bits: i64, nargs: i64) -> i64 {
    with(|s| match s.heap.obj(Word { tag, bits }) {
        Ok(Some(Obj::Clo { lambda, .. })) if s.t.lambdas[*lambda].params == nargs as usize => {
            *lambda as i64 + 1
        }
        _ => 0,
    })
}

extern "C" fn rt_entry(lambda: i64) -> i64 {
    with(|s| s.entries[lambda as usize])
}

extern "C" fn rt_register(lambda: i64, address: i64) {
    with(|s| s.entries[lambda as usize] = address);
}

extern "C" fn rt_branch(id: i64) -> i64 {
    with(|s| {
        let ins = std::mem::take(&mut s.args);
        let r = branch(s, id as usize, ins);
        code(s, r)
    })
}

extern "C" fn rt_match(id: i64) -> i64 {
    with(|s| {
        let ins = std::mem::take(&mut s.args);
        let r = matched(s, id as usize, ins);
        code(s, r)
    })
}

extern "C" fn rt_out(k: i64) -> Word {
    with(|s| s.outs[k as usize])
}

extern "C" fn rt_pending() -> Word {
    with(|s| s.pending)
}

extern "C" fn rt_error(id: i64) -> Word {
    with(|s| {
        let e = s.t.nodes[id as usize].error.clone();
        word(
            s,
            Err(e.unwrap_or_else(|| "native: an error with no message".into())),
        )
    })
}

/// Whether `w` is data: not a function and not a port's state.
fn data(s: &State, w: Word) -> Result<bool, String> {
    Ok(w.tag != Word::STATE && !s.heap.is_function(w)?)
}

/// The rope of string word `w`, when it is one.
fn rope(s: &State, w: Word) -> Result<Option<Rope>, String> {
    Ok(match w.tag {
        Word::CELL => match s.heap.obj(w)? {
            Some(Obj::Str(r)) => Some(r.clone()),
            _ => None,
        },
        Word::VAL => match s.heap.value_ref(w) {
            Value::Str(x) => Some(Rope::leaf(x.clone())),
            _ => None,
        },
        _ => None,
    })
}

/// Runs node `id` on `ins` as the counting machine does; returns its first output, owned.
fn node(s: &mut State, id: usize, ins: Vec<Word>) -> Result<Word, String> {
    let t = s.t.clone();
    let ni = &t.nodes[id];
    let all_data = ins
        .iter()
        .map(|w| data(s, *w))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .all(|d| d);
    match &ni.node.op {
        Op::Prim(Prim::Tuple) if all_data && !ins.is_empty() => Ok(s.heap.alloc(Obj::Tuple(ins))),
        Op::Prim(Prim::Atom) if all_data => {
            let v = kernel(s, ni, &ins)?;
            let names = match s.heap.value(ins[1])? {
                Value::Tuple(ns) => ns,
                _ => Vec::new(),
            };
            match v {
                Value::Atom(a) if !a.args.is_empty() && a.args.len() + 2 == ins.len() => {
                    let args = (0..a.args.len())
                        .map(|i| {
                            let from = match names.is_empty() {
                                true => i,
                                false => names
                                    .iter()
                                    .position(|n| *n == Value::Str(a.fields[i].clone()))
                                    .expect("a field the atom was made with"),
                            };
                            ins[2 + from]
                        })
                        .collect();
                    Ok(s.heap.alloc(Obj::Atom {
                        name: a.name,
                        fields: a.fields,
                        args,
                    }))
                }
                v => {
                    consume(s, ni, &ins)?;
                    Ok(s.heap.fresh(&v))
                }
            }
        }
        Op::Prim(Prim::TupleGet) => {
            if let (Ok(Some(Obj::Tuple(xs))), Word::INT) = (s.heap.obj(ins[0]), ins[1].tag)
                && let Some(kid) = usize::try_from(ins[1].bits).ok().and_then(|i| xs.get(i))
            {
                let kid = *kid;
                s.heap.inc(kid);
                return Ok(kid);
            }
            let v = kernel(s, ni, &ins)?;
            Ok(s.heap.fresh(&v))
        }
        Op::Prim(Prim::Concat) if ins.len() == 2 => match (rope(s, ins[0])?, rope(s, ins[1])?) {
            (Some(a), Some(b)) => {
                let r = Rope::cat(&a, &b);
                consume(s, ni, &ins)?;
                Ok(s.heap.alloc(Obj::Str(r)))
            }
            _ => slow(s, ni, &ins),
        },
        Op::Prim(Prim::Len) if ins.len() == 1 => match rope(s, ins[0])? {
            Some(r) => {
                consume(s, ni, &ins)?;
                Ok(Word::int(r.chars() as i64))
            }
            None => slow(s, ni, &ins),
        },
        Op::Lambda => Ok(s.heap.alloc(Obj::Clo {
            lambda: ni.lambda.expect("a lambda's index"),
            caps: ins,
        })),
        Op::Read(p) => match s.ev.world.inputs.get(&**p) {
            Some(v) => {
                let v = v.clone();
                Ok(s.heap.fresh(&v))
            }
            None if s.ev.world.sources.contains_key(&**p) => Ok(Word {
                tag: Word::SOURCE,
                bits: t.ports.iter().position(|q| q == p).expect("a port") as i64,
            }),
            None => {
                let v = s.ev.run(&Term::Read(p.clone()));
                Err(v.map_or_else(|e| e.to_string(), |_| "a read".into()))
            }
        },
        _ => slow(s, ni, &ins),
    }
}

/// The kernel runs the node, the owned inputs are dropped, and the value is allocated.
fn slow(s: &mut State, ni: &NodeInfo, ins: &[Word]) -> Result<Word, String> {
    let v = kernel(s, ni, ins)?;
    consume(s, ni, ins)?;
    Ok(s.heap.fresh(&v))
}

/// Drops each input the node takes owned.
fn consume(s: &mut State, ni: &NodeInfo, ins: &[Word]) -> Result<(), String> {
    for (j, w) in ins.iter().enumerate() {
        if ni.modes[j] == Mode::Owned {
            s.heap.dec(*w)?;
        }
    }
    Ok(())
}

/// The value the kernel gives node `ni` run alone on `ins`.
fn kernel(s: &mut State, ni: &NodeInfo, ins: &[Word]) -> Result<Value, String> {
    let mut lets = Vec::new();
    let mut terms = Vec::new();
    for w in ins {
        terms.push(term(s, *w, &mut lets)?);
    }
    let t = raise_with(&ni.alone, &terms)?;
    run(s, &wrap(lets, t))
}

fn run(s: &mut State, t: &Term) -> Result<Value, String> {
    s.kernel_calls += 1;
    s.ev.run(t).map_err(|e| e.to_string())
}

/// The kernel term for word `w`; a lookup port is read once, by a `let` in `lets`.
fn term(s: &mut State, w: Word, lets: &mut Vec<Arc<str>>) -> Result<Term, String> {
    Ok(match w.tag {
        Word::PRIM => Term::PrimFn(s.t.prims[w.bits as usize]),
        Word::STATE => Term::Lit(Value::Tuple(Vec::new())),
        Word::SOURCE => {
            let p = s.t.ports[w.bits as usize].clone();
            if !lets.contains(&p) {
                lets.push(p.clone());
            }
            Term::Var(port_var(&p))
        }
        Word::CELL if s.heap.is_function(w)? => {
            let Some(Obj::Clo { lambda, caps }) = s.heap.obj(w)?.cloned() else {
                unreachable!("checked to be a closure")
            };
            let mut terms = Vec::new();
            for c in caps {
                terms.push(term(s, c, lets)?);
            }
            let t = s.t.clone();
            raise_with(&t.nodes[t.lambdas[lambda].node].alone, &terms)?
        }
        _ => Term::Lit(s.heap.value(w)?),
    })
}

fn port_var(p: &str) -> Arc<str> {
    format!("\0port {p}").into()
}

/// `t` with each lookup port in `ports` read first.
fn wrap(ports: Vec<Arc<str>>, t: Term) -> Term {
    ports.into_iter().rev().fold(t, |b, p| {
        Term::Let(port_var(&p), Arc::new(Term::Read(p)), Arc::new(b))
    })
}

/// An `if` or `match` whose decision is failure value `v`: the owned inputs are dropped and
/// the value is pending as the node's result.
fn failed(s: &mut State, ni: &NodeInfo, ins: &[Word], v: Value) -> Result<(), String> {
    consume(s, ni, ins)?;
    s.pending = s.heap.fresh(&v);
    Ok(())
}

/// An `if` whose condition is not a boolean word: the kernel decides. Returns the arm, or 2
/// for a failure.
fn branch(s: &mut State, id: usize, ins: Vec<Word>) -> Result<i64, String> {
    let t = s.t.clone();
    let ni = &t.nodes[id];
    if ins[0].tag == Word::BOOL {
        return Ok(i64::from(ins[0].bits == 0));
    }
    let c = term(s, ins[0], &mut Vec::new())?;
    let q = Term::If(
        Arc::new(c),
        Arc::new(Term::Lit(Value::Int(0))),
        Arc::new(Term::Lit(Value::Int(1))),
    );
    match run(s, &q)? {
        Value::Int(i) => Ok(i),
        v => {
            failed(s, ni, &ins, v)?;
            Ok(2)
        }
    }
}

/// A `match`: the arm whose pattern the scrutinee matches first, its binders in the output
/// buffer, the scrutinee released as the plan says; or the number of arms for a failure.
fn matched(s: &mut State, id: usize, ins: Vec<Word>) -> Result<i64, String> {
    let t = s.t.clone();
    let ni = &t.nodes[id];
    let Op::Match(ps) = &ni.node.op else {
        unreachable!("a match node")
    };
    let scrut = ins[0];
    let function = s.heap.is_function(scrut)?;
    let mut found = None;
    if !function {
        for (i, p) in ps.iter().enumerate() {
            let mut out = Vec::new();
            if s.heap.matches(p, scrut, &mut Vec::new(), &mut out)? {
                found = Some((i, out.into_iter().map(|(w, p)| (w, Some(p))).collect()));
                break;
            }
        }
    }
    let (i, binders): (usize, Binders) = match found {
        Some(f) => f,
        None => match kernel_match(s, ps, scrut)? {
            Ok((i, vals)) => {
                if !function {
                    return Err(format!(
                        "native: {}: no pattern matches natively, and the kernel picks arm {i}",
                        ni.path
                    ));
                }
                let binders = vals.into_iter().map(|v| (s.heap.uncounted(v), None));
                (i, binders.collect())
            }
            Err(v) => {
                failed(s, ni, &ins, v)?;
                return Ok(ps.len() as i64);
            }
        },
    };
    let arm = &ni.arms[i];
    let mut words = Vec::new();
    if ni.modes[0] == Mode::Owned {
        let kept: Vec<usize> = (0..binders.len())
            .filter(|b| arm[*b] == Mode::Owned)
            .collect();
        // A binder the arm borrows holds no reference once the scrutinee is released, so it
        // is detached first: the machine gives it no cell.
        for (b, (w, _)) in binders.iter().enumerate() {
            if kept.contains(&b) || w.tag != Word::CELL {
                words.push(*w);
            } else {
                let v = s.heap.value(*w)?;
                words.push(s.heap.uncounted(v));
            }
        }
        let kept_paths: Vec<&[usize]> = kept
            .iter()
            .filter_map(|b| binders[*b].1.as_deref())
            .collect();
        if t.fuse {
            s.heap.release(scrut, &kept_paths)?;
        } else {
            for b in &kept {
                s.heap.inc(binders[*b].0);
            }
            s.heap.dec(scrut)?;
        }
    } else {
        for (b, (w, _)) in binders.iter().enumerate() {
            if arm[b] == Mode::Owned {
                return Err(format!(
                    "memory: {}: the scrutinee is borrowed, and arm {i} owns binder {b}",
                    ni.path
                ));
            }
            words.push(*w);
        }
    }
    s.outs = words;
    Ok(i as i64)
}

/// The kernel's decision on a scrutinee native matching does not decide: the arm and its
/// binders' values, or the failure value.
#[allow(clippy::type_complexity)]
fn kernel_match(
    s: &mut State,
    ps: &[Pattern],
    scrut: Word,
) -> Result<Result<(usize, Vec<Value>), Value>, String> {
    let mut lets = Vec::new();
    let st = term(s, scrut, &mut lets)?;
    let mut arms = Vec::new();
    for (i, p) in ps.iter().enumerate() {
        let mut p = p.clone();
        let mut xs = vec![Term::Lit(Value::Int(i as i64))];
        let mut n = 0;
        rename(&mut p, &mut || {
            n += 1;
            let x: Arc<str> = format!("\0bind{n}").into();
            xs.push(Term::Var(x.clone()));
            x
        });
        arms.push((p, Term::Prim(Prim::Tuple, xs)));
    }
    let q = wrap(lets, Term::Match(Arc::new(st), arms));
    Ok(match run(s, &q)? {
        Value::Tuple(mut xs) if matches!(xs.first(), Some(Value::Int(i)) if (*i as usize) < ps.len()) =>
        {
            let Value::Int(i) = xs.remove(0) else {
                unreachable!("checked above")
            };
            Ok((i as usize, xs))
        }
        v => Err(v),
    })
}

/// Renames each binder of `p`, in preorder, to what `f` gives.
fn rename(p: &mut Pattern, f: &mut dyn FnMut() -> Arc<str>) {
    match p {
        Pattern::Bind(x) => *x = f(),
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter_mut().for_each(|q| rename(q, f)),
        Pattern::Fields(_, fs) => fs.iter_mut().for_each(|(_, q)| rename(q, f)),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
    }
}

/// The program's result: its value, after the result is dropped and no cell is left live.
pub(crate) fn finish(s: &mut State, w: Word) -> Result<Value, String> {
    if let Some(e) = s.err.take() {
        return Err(e);
    }
    if w.tag == Word::ERR {
        return Err("native: the run failed and recorded no message".into());
    }
    let function = s.heap.is_function(w)?;
    let v = if function {
        None
    } else {
        Some(s.heap.value(w)?)
    };
    s.heap.dec(w)?;
    if s.heap.live() != 0 {
        let n = s.heap.live();
        return Err(format!(
            "memory: {n} cell{} live after the result is dropped",
            if n == 1 { "" } else { "s" }
        ));
    }
    v.ok_or_else(|| KernelError::Type("the program's result is a function".into()).to_string())
}
