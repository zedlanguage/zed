//! The runtime the generated code calls: every node it does not run inline, every count
//! write, and the decisions of `if` and `match` it cannot make from a tag. Each hook does
//! what the counting machine of step L1.34 does for the same node, on words, so a native run
//! makes the machine's allocations and count writes one for one.
//!
//! The state of the run in progress lives in a thread-local slot; a hook never calls back
//! into generated code, so the slot is never borrowed twice.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::{Evaluator, Fields, KernelError, Pattern, Prim, Shared, Term, Text, Value};
use zedc::zir::Op;
use zedc::zir::lower::raise_node;
use zedc::zir::memory::Mode;

use zed_rt::{Heap, Obj, Word};

use crate::tables::{NodeInfo, Tables};

/// A match's binders: each word, and its path in the scrutinee when native matching found it.
type Binders = Vec<(Word, Option<Vec<usize>>)>;

/// The kernel's decision on a match: the arm and the tuple `(arm, binders…)` it gives, or the
/// failure value.
type Decision = Result<(usize, Vec<Value>), Value>;

/// A native run: the program's tables, read by every hook, and the state the hooks change.
pub(crate) struct State {
    pub t: Arc<Tables>,
    pub run: Run,
}

/// The state of one native run that the hooks change.
pub(crate) struct Run {
    pub heap: Heap,
    pub ev: Evaluator,
    /// The words passed by `rt_arg` for the next hook; the buffer is kept between hooks.
    args: Vec<Word>,
    outs: Vec<Word>,
    pending: Word,
    pub err: Option<String>,
    entries: Vec<i64>,
    pub kernel_calls: u64,
    /// For each atom node, the shape last made from constant name and field words.
    shapes: Vec<Option<(Word, Word, Shape)>>,
}

/// An atom's name, its field names sorted, and for each field the payload input it holds.
#[derive(Clone)]
struct Shape {
    name: Arc<str>,
    fields: Fields,
    order: Arc<[usize]>,
}

impl State {
    pub fn new(t: Arc<Tables>, ev: Evaluator) -> State {
        let mut heap = Heap::new();
        for (i, v) in t.consts.iter().enumerate() {
            let w = heap.uncounted(v.clone());
            debug_assert_eq!(w.bits as usize, i);
        }
        let run = Run {
            heap,
            ev,
            args: Vec::new(),
            outs: Vec::new(),
            pending: Word::err(),
            err: None,
            entries: vec![0; t.lambdas.len()],
            kernel_calls: 0,
            shapes: vec![None; t.nodes.len()],
        };
        State { t, run }
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

fn with<R>(f: impl FnOnce(&Tables, &mut Run) -> R) -> R {
    STATE.with(|c| {
        let mut slot = c.borrow_mut();
        let s = slot.as_mut().expect("a run is installed");
        f(&s.t, &mut s.run)
    })
}

/// Runs `f` on the words `rt_arg` passed, then empties the buffer and keeps it.
fn with_args<R>(f: impl FnOnce(&Tables, &mut Run, &[Word]) -> R) -> R {
    with(|t, s| {
        let mut ins = std::mem::take(&mut s.args);
        let r = f(t, s, &ins);
        ins.clear();
        s.args = ins;
        r
    })
}

/// `r`'s word, or the error word with the message recorded.
fn word(s: &mut Run, r: Result<Word, String>) -> Word {
    r.unwrap_or_else(|e| {
        s.err.get_or_insert(e);
        Word::err()
    })
}

fn code(s: &mut Run, r: Result<i64, String>) -> i64 {
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

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_arg(tag: i64, bits: i64) {
    with(|_, s| s.args.push(Word { tag, bits }));
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_node(id: i64) -> Word {
    with_args(|t, s, ins| {
        s.heap.allocating(Some(id as usize));
        let r = node(t, s, id as usize, ins);
        word(s, r)
    })
}

/// An error is recorded here, as at every other hook: generated code does not check after an
/// `inc`, and no `dec` need follow it.
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_inc(tag: i64, bits: i64) {
    with(|_, s| {
        if let Err(e) = s.heap.inc(Word { tag, bits }) {
            s.err.get_or_insert(e);
        }
    });
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_dec(tag: i64, bits: i64) {
    with(|_, s| {
        if let Err(e) = s.heap.dec(Word { tag, bits }) {
            s.err.get_or_insert(e);
        }
    });
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_cap(tag: i64, bits: i64, i: i64) -> Word {
    with(|_, s| {
        let r = s.heap.capture(Word { tag, bits }, i as usize);
        word(s, r)
    })
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_callable(tag: i64, bits: i64, nargs: i64) -> i64 {
    with(|t, s| match s.heap.obj(Word { tag, bits }) {
        Ok(Some(Obj::Clo { lambda, .. })) if t.lambdas[*lambda].params == nargs as usize => {
            *lambda as i64 + 1
        }
        _ => 0,
    })
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_entry(lambda: i64) -> i64 {
    with(|_, s| s.entries[lambda as usize])
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_register(lambda: i64, address: i64) {
    with(|_, s| s.entries[lambda as usize] = address);
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_branch(id: i64) -> i64 {
    with_args(|t, s, ins| {
        s.heap.allocating(Some(id as usize));
        let r = branch(t, s, id as usize, ins);
        code(s, r)
    })
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_match(id: i64) -> i64 {
    with_args(|t, s, ins| {
        s.heap.allocating(Some(id as usize));
        let r = matched(t, s, id as usize, ins);
        code(s, r)
    })
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_out(k: i64) -> Word {
    with(|_, s| s.outs[k as usize])
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_pending() -> Word {
    with(|_, s| s.pending)
}

#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_error(id: i64) -> Word {
    with(|t, s| {
        let e = t.nodes[id as usize].error.clone();
        word(
            s,
            Err(e.unwrap_or_else(|| "native: an error with no message".into())),
        )
    })
}

/// Whether every word of `ins` is data: not a function and not a port's state.
fn all_data(s: &Run, ins: &[Word]) -> Result<bool, String> {
    for w in ins {
        if w.tag == Word::STATE || s.heap.is_function(*w)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether `w` names one value for the whole run: a scalar or a constant. A cell or another
/// uncounted value may be freed and its index used again.
fn stable(t: &Tables, w: Word) -> bool {
    match w.tag {
        Word::CELL => false,
        Word::VAL => (w.bits as usize) < t.consts.len(),
        _ => true,
    }
}

/// The text of string word `w`, when it is one, shared.
fn text(s: &Run, w: Word) -> Result<Option<Text>, String> {
    Ok(match w.tag {
        Word::CELL => match s.heap.obj(w)? {
            Some(Obj::Str(r)) => Some(r.clone()),
            _ => None,
        },
        Word::VAL => match s.heap.value_ref(w) {
            Value::Str(x) => Some(x.clone()),
            _ => None,
        },
        _ => None,
    })
}

/// An atom's name or field name as one shared block (`Text::try_shared`): a join is written
/// out once the system gives the memory, else the kernel's message for it.
fn atom_name(x: &Text) -> Result<Arc<str>, String> {
    x.try_shared()
        .map_err(|_| KernelError::AtomNameTooLarge { bytes: x.len() }.to_string())
}

/// The shape of atom node `id` on `ins`, `[name, field names, payload…]`, or `None` when the
/// kernel refuses it. A shape made from stable words is kept for the node's next run.
fn shape(t: &Tables, s: &mut Run, id: usize, ins: &[Word]) -> Result<Option<Shape>, String> {
    let key = (ins[0], ins[1]);
    if let Some((a, b, sh)) = &s.shapes[id]
        && (*a, *b) == key
    {
        return Ok(Some(sh.clone()));
    }
    let (Value::Str(name), Value::Tuple(names)) = (s.heap.value(ins[0])?, s.heap.value(ins[1])?)
    else {
        return Ok(None);
    };
    let n = ins.len() - 2;
    let (fields, order): (Vec<Arc<str>>, Vec<usize>) = match names.is_empty() {
        true => (Vec::new(), (0..n).collect()),
        false if names.len() != n => return Ok(None),
        false => {
            let mut named = Vec::with_capacity(n);
            for (i, x) in names.iter().enumerate() {
                let Value::Str(x) = x else { return Ok(None) };
                named.push((atom_name(x)?, i));
            }
            // The kernel's order, and its refusal of a repeated name (`Value::atom_named`).
            named.sort_by(|a, b| a.0.cmp(&b.0));
            if named.windows(2).any(|w| w[0].0 == w[1].0) {
                return Ok(None);
            }
            named.into_iter().unzip()
        }
    };
    let sh = Shape {
        name: atom_name(&name)?,
        fields: fields.into(),
        order: order.into(),
    };
    if stable(t, key.0) && stable(t, key.1) {
        s.shapes[id] = Some((key.0, key.1, sh.clone()));
    }
    Ok(Some(sh))
}

/// Runs node `id` on `ins` as the counting machine does; returns its first output, owned.
fn node(t: &Tables, s: &mut Run, id: usize, ins: &[Word]) -> Result<Word, String> {
    let ni = &t.nodes[id];
    match &ni.node().op {
        Op::Prim(Prim::Tuple) if !ins.is_empty() && all_data(s, ins)? => {
            Ok(s.heap.alloc(Obj::Tuple(ins.to_vec())))
        }
        // The atom is made from its words, as the kernel would make it: the payload moves
        // into the cell, and the name and field names are borrowed.
        Op::Prim(Prim::Atom) if ins.len() >= 2 && all_data(s, ins)? => {
            match shape(t, s, id, ins)? {
                None => slow(t, s, ni, ins),
                Some(sh) if ins.len() == 2 => {
                    consume(s, ni, ins)?;
                    Ok(s.heap.fresh(&Value::atom(&sh.name)))
                }
                Some(sh) => Ok(s.heap.alloc(Obj::Atom {
                    args: sh.order.iter().map(|&i| ins[2 + i]).collect(),
                    name: sh.name,
                    fields: sh.fields,
                })),
            }
        }
        Op::Prim(Prim::TupleGet) => {
            if let (Ok(Some(Obj::Tuple(xs))), Word::INT) = (s.heap.obj(ins[0]), ins[1].tag)
                && let Some(kid) = usize::try_from(ins[1].bits).ok().and_then(|i| xs.get(i))
            {
                let kid = *kid;
                s.heap.inc(kid)?;
                return Ok(kid);
            }
            let v = kernel(t, s, ni, ins)?;
            Ok(s.heap.fresh(&v))
        }
        Op::Prim(Prim::Concat) if ins.len() == 2 => match (text(s, ins[0])?, text(s, ins[1])?) {
            (Some(a), Some(b)) => {
                let r = Text::join(&a, &b).map_err(|e| KernelError::from(e).to_string())?;
                consume(s, ni, ins)?;
                Ok(s.heap.alloc(Obj::Str(r)))
            }
            _ => slow(t, s, ni, ins),
        },
        // A count past `i64::MAX`, a string doubled 63 times, is a big integer the kernel makes.
        Op::Prim(Prim::Len) if ins.len() == 1 => {
            match text(s, ins[0])?.map(|r| i64::try_from(r.char_count())) {
                Some(Ok(n)) => {
                    consume(s, ni, ins)?;
                    Ok(Word::int(n))
                }
                _ => slow(t, s, ni, ins),
            }
        }
        // A string of one scalar is never a join, whose parts are each at least one scalar, so
        // its text is read in place; any other string gives `#notScalar`, which the kernel makes.
        Op::Prim(Prim::CodePoint) if ins.len() == 1 => {
            if let Some(r) = text(s, ins[0])?
                && r.char_count() == 1
                && let Some(c) = r.chunks().next().and_then(|b| b.chars().next())
            {
                consume(s, ni, ins)?;
                return Ok(Word::int(i64::from(u32::from(c))));
            }
            slow(t, s, ni, ins)
        }
        Op::Lambda => Ok(s.heap.alloc(Obj::Clo {
            lambda: ni.lambda.expect("a lambda's index"),
            caps: ins.to_vec(),
        })),
        Op::Read(p) => match s.ev.world.inputs.get(&**p) {
            Some(v) => {
                let v = v.clone();
                Ok(s.heap.fresh(&v))
            }
            None if s.ev.world.sources.contains_key(&**p) => Ok(Word {
                tag: Word::SOURCE,
                bits: t.port_at[p] as i64,
            }),
            None => {
                let v = s.ev.run(&Term::Read(p.clone()));
                Err(v.map_or_else(|e| e.to_string(), |_| "a read".into()))
            }
        },
        _ => slow(t, s, ni, ins),
    }
}

/// The kernel runs the node, the owned inputs are dropped, and the value is allocated.
fn slow(t: &Tables, s: &mut Run, ni: &NodeInfo, ins: &[Word]) -> Result<Word, String> {
    let v = kernel(t, s, ni, ins)?;
    consume(s, ni, ins)?;
    Ok(s.heap.fresh(&v))
}

/// Drops each input the node takes owned.
fn consume(s: &mut Run, ni: &NodeInfo, ins: &[Word]) -> Result<(), String> {
    for (j, w) in ins.iter().enumerate() {
        if ni.modes[j] == Mode::Owned {
            s.heap.dec(*w)?;
        }
    }
    Ok(())
}

/// The value the kernel gives node `ni` run alone on `ins`.
fn kernel(t: &Tables, s: &mut Run, ni: &NodeInfo, ins: &[Word]) -> Result<Value, String> {
    let mut lets = Lets::default();
    let mut terms = Vec::with_capacity(ins.len());
    for w in ins {
        terms.push(term(t, s, *w, &mut lets)?);
    }
    let q = raise_node(ni.node(), ni.number, &t.swapped, &terms)?;
    run(s, &wrap(lets, q))
}

fn run(s: &mut Run, q: &Term) -> Result<Value, String> {
    s.kernel_calls += 1;
    s.ev.run(q).map_err(|e| e.to_string())
}

/// The kernel term for word `w`; a lookup port is read once, by a `let` in `lets`, and each
/// closure's term is built once, in `lets.closures`.
fn term(t: &Tables, s: &mut Run, w: Word, lets: &mut Lets) -> Result<Term, String> {
    // Closures capture closures as deep as a program builds them, so the closures in progress
    // are on a stack, each with the terms of its captures so far.
    let mut stack: Vec<(Word, Vec<Term>)> = Vec::new();
    let mut made = term_of(t, s, w, lets, &mut stack)?;
    loop {
        let Some((clo, terms)) = stack.last_mut() else {
            return Ok(made.expect("an empty stack follows a finished term"));
        };
        terms.extend(made.take());
        let Some(Obj::Clo { lambda, caps }) = s.heap.obj(*clo)? else {
            unreachable!("only closures are entered")
        };
        match caps.get(terms.len()) {
            Some(&c) => made = term_of(t, s, c, lets, &mut stack)?,
            None => {
                let ni = &t.nodes[t.lambdas[*lambda].node];
                let q = raise_node(ni.node(), ni.number, &t.swapped, terms)?;
                let (clo, _) = stack.pop().expect("the closure finished");
                lets.closures.insert(clo.bits, q.clone());
                made = Some(q);
            }
        }
    }
}

/// The term of `w` when it is not a closure or is a closure whose term is built; any other
/// closure is entered on `stack`.
fn term_of(
    t: &Tables,
    s: &mut Run,
    w: Word,
    lets: &mut Lets,
    stack: &mut Vec<(Word, Vec<Term>)>,
) -> Result<Option<Term>, String> {
    Ok(Some(match w.tag {
        Word::PRIM => Term::PrimFn(t.prims[w.bits as usize]),
        Word::STATE => Term::Lit(Value::tuple(Vec::new())),
        Word::SOURCE => {
            let p = t.ports[w.bits as usize].clone();
            if lets.seen.insert(p.clone()) {
                lets.order.push(p.clone());
            }
            Term::Var(port_var(&p))
        }
        Word::CELL if s.heap.is_function(w)? => match lets.closures.get(&w.bits) {
            Some(q) => q.clone(),
            None => {
                stack.push((w, Vec::new()));
                return Ok(None);
            }
        },
        _ => Term::Lit(s.heap.value(w)?),
    }))
}

fn port_var(p: &str) -> Arc<str> {
    format!("\0port {p}").into()
}

/// `t` with each lookup port in `ports` read first.
fn wrap(ports: Lets, t: Term) -> Term {
    ports.order.into_iter().rev().fold(t, |b, p| {
        Term::Let(port_var(&p), Shared::new(Term::Read(p)), Shared::new(b))
    })
}

/// The lookup ports a kernel term reads, each once, in the order first met, and the term of
/// each closure it holds.
#[derive(Default)]
struct Lets {
    seen: HashSet<Arc<str>>,
    order: Vec<Arc<str>>,
    /// The term of each closure met, by its cell word's bits: a closure captured on many paths
    /// is built once, so the term is a graph the size of the closures, not a tree of every
    /// path (COMPLEXITY.md R9). No cell is freed while a term is built, so each word names one
    /// closure. A closure's term is a lambda whose body is shared, so a copy costs its
    /// parameter names.
    closures: HashMap<i64, Term>,
}

/// An `if` or `match` whose decision is failure value `v`: the owned inputs are dropped and
/// the value is pending as the node's result.
fn failed(s: &mut Run, ni: &NodeInfo, ins: &[Word], v: Value) -> Result<(), String> {
    consume(s, ni, ins)?;
    s.pending = s.heap.fresh(&v);
    Ok(())
}

/// An `if` whose condition is not a boolean word: the kernel decides. Returns the arm, or 2
/// for a failure.
fn branch(t: &Tables, s: &mut Run, id: usize, ins: &[Word]) -> Result<i64, String> {
    let ni = &t.nodes[id];
    if ins[0].tag == Word::BOOL {
        return Ok(i64::from(ins[0].bits == 0));
    }
    // A lookup port as the condition is read by a `let`, as in every other kernel term.
    let mut lets = Lets::default();
    let c = term(t, s, ins[0], &mut lets)?;
    let q = Term::If(
        Shared::new(c),
        Shared::new(Term::Lit(Value::Int(0))),
        Shared::new(Term::Lit(Value::Int(1))),
    );
    match run(s, &wrap(lets, q))? {
        Value::Int(i) => Ok(i),
        v => {
            failed(s, ni, ins, v)?;
            Ok(2)
        }
    }
}

/// A `match`: the arm whose pattern the scrutinee matches first, its binders in the output
/// buffer, the scrutinee released as the plan says; or the number of arms for a failure.
fn matched(t: &Tables, s: &mut Run, id: usize, ins: &[Word]) -> Result<i64, String> {
    let ni = &t.nodes[id];
    let Op::Match(ps) = &ni.node().op else {
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
        None => match kernel_match(t, s, ps, scrut)? {
            Ok((i, vals)) => {
                if !function {
                    return Err(format!(
                        "native: {}: no pattern matches natively, and the kernel picks arm {i}",
                        t.path(id)
                    ));
                }
                // The first value is the arm's index.
                let vals = vals.into_iter().skip(1);
                let binders = vals.map(|v| (s.heap.uncounted(v), None));
                (i, binders.collect())
            }
            Err(v) => {
                failed(s, ni, ins, v)?;
                return Ok(ps.len() as i64);
            }
        },
    };
    let arm = &ni.arms[i];
    let mut words = std::mem::take(&mut s.outs);
    words.clear();
    if ni.modes[0] == Mode::Owned {
        let kept: Vec<usize> = (0..binders.len())
            .filter(|b| arm[*b] == Mode::Owned)
            .collect();
        // With the scrutinee owned, the plan owns every binder the arm uses, so a borrowed
        // binder is one the arm never reads. Its word would point into the released
        // scrutinee; the machine gives it no cell, and the arm gets the error word instead.
        for (b, (w, _)) in binders.iter().enumerate() {
            if arm[b] == Mode::Owned || w.tag != Word::CELL {
                words.push(*w);
            } else {
                words.push(Word::err());
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
                s.heap.inc(binders[*b].0)?;
            }
            s.heap.dec(scrut)?;
        }
    } else {
        for (b, (w, _)) in binders.iter().enumerate() {
            if arm[b] == Mode::Owned {
                return Err(format!(
                    "memory: {}: the scrutinee is borrowed, and arm {i} owns binder {b}",
                    t.path(id)
                ));
            }
            words.push(*w);
        }
    }
    s.outs = words;
    Ok(i as i64)
}

/// The kernel's decision on a scrutinee native matching does not decide: the arm and the
/// values `(arm, binders…)`, or the failure value.
fn kernel_match(t: &Tables, s: &mut Run, ps: &[Pattern], scrut: Word) -> Result<Decision, String> {
    let mut lets = Lets::default();
    let st = term(t, s, scrut, &mut lets)?;
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
    let q = wrap(lets, Term::Match(Shared::new(st), arms));
    Ok(match run(s, &q)? {
        Value::Tuple(xs) => match xs.first() {
            Some(&Value::Int(i)) if (i as usize) < ps.len() => Ok((i as usize, xs.into_vec())),
            _ => Err(Value::Tuple(xs)),
        },
        v => Err(v),
    })
}

/// Renames each binder of `p`, in preorder, to what `f` gives.
fn rename(p: &mut Pattern, f: &mut dyn FnMut() -> Arc<str>) {
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(x) => *x = f(),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter_mut().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter_mut().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
}

/// The program's result: its value, after the result is dropped and no cell is left live.
/// Under feature `counts`, a run that leaves cells live names them, and every run is counted
/// for `counted`, with what it left live, whichever way it ended.
pub(crate) fn finish(t: &Tables, s: &mut Run, w: Word) -> Result<Value, String> {
    let r = result(t, s, w);
    #[cfg(feature = "counts")]
    COUNTED.with(|c| {
        let mut c = c.borrow_mut();
        c.runs += 1;
        if s.heap.live() != 0 {
            c.left.push(survivors(t, &s.heap));
        }
    });
    r
}

/// The native runs of this thread, and what each run that left cells live left, as
/// `survivors` names them (feature `counts`).
#[cfg(feature = "counts")]
#[derive(Clone, Debug, Default)]
pub struct Counted {
    /// The runs that reached their end.
    pub runs: u64,
    /// For each run that left cells live, those cells.
    pub left: Vec<String>,
}

#[cfg(feature = "counts")]
thread_local! {
    static COUNTED: RefCell<Counted> = RefCell::new(Counted::default());
}

/// The native runs of this thread since the last call, and what they left live (feature
/// `counts`).
#[cfg(feature = "counts")]
pub fn counted() -> Counted {
    COUNTED.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// The cells live in `heap`, by type and allocating node: `1 String allocated by node r.0.3,
/// 2 tuple allocated by node r.0.5/1.2`. The node is its fact address in the graph.
#[cfg(feature = "counts")]
fn survivors(t: &Tables, heap: &Heap) -> String {
    let groups = heap.survivors();
    let mut out = String::new();
    for (i, g) in groups.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        let at = g.node.map_or_else(
            || "outside every node".into(),
            |n| format!("by node {}", t.path(n)),
        );
        out.push_str(&format!("{} {} allocated {at}", g.cells, g.kind));
    }
    out
}

fn result(t: &Tables, s: &mut Run, w: Word) -> Result<Value, String> {
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
        #[cfg(feature = "counts")]
        let which = format!(": {}", survivors(t, &s.heap));
        #[cfg(not(feature = "counts"))]
        let which = {
            let _ = t;
            ""
        };
        return Err(format!(
            "memory: {n} cell{} live after the result is dropped{which}",
            if n == 1 { "" } else { "s" }
        ));
    }
    v.ok_or_else(|| KernelError::Type("the program's result is a function".into()).to_string())
}

#[cfg(test)]
mod tests {
    use std::mem::ManuallyDrop;

    use zed_kernel::World;
    use zed_kernel::term::build::{app, if_, lam, lit, var};
    use zedc::zir::lower::lower;
    use zedc::zir::memory::plan;

    use super::*;

    /// How deep the tests go, on the default test stack; each old function overflowed it.
    const DEPTH: usize = 1_000_000;

    #[test]
    fn a_chain_of_closures_becomes_a_term() {
        // `(x) -> (y) -> x`, whose inner lambda captures one value.
        let g = crate::legal::legalize(lower(&lam(&["x"], lam(&["y"], var("x")))).unwrap());
        let (t, _) = Tables::new(&g, &plan(g.graph(), false)).unwrap();
        let captures = |l: &&crate::tables::LambdaInfo| !t.nodes[l.node].node().inputs.is_empty();
        let inner = t.lambdas.iter().position(|l| captures(&l)).unwrap();
        let mut s = State::new(Arc::new(t), Evaluator::new(World::new()));
        let mut w = Word::int(7);
        for _ in 0..DEPTH {
            w = s.run.heap.alloc(Obj::Clo {
                lambda: inner,
                caps: vec![w],
            });
        }
        // The kernel's terms drop by recursion, so this one is left to the end of the process.
        let made = ManuallyDrop::new(term(&s.t, &mut s.run, w, &mut Lets::default()).unwrap());
        let (mut at, mut depth) = (&*made, 0);
        while let Term::Lam(_, body) = at {
            (at, depth) = (&**body, depth + 1);
        }
        assert_eq!(depth, DEPTH);
        assert_eq!(at.to_string(), "7");
    }

    /// A run of `(a, b) -> (y) -> if y < 1 { a } else { b(y - 1) }`, and the index of its inner
    /// lambda, which captures two values.
    fn two_captures() -> (State, usize) {
        let lt = Term::Prim(Prim::Lt, vec![var("y"), lit(1i64)]);
        let less = Term::Prim(Prim::Sub, vec![var("y"), lit(1i64)]);
        let body = if_(lt, var("a"), app(var("b"), vec![less]));
        let g = crate::legal::legalize(lower(&lam(&["a", "b"], lam(&["y"], body))).unwrap());
        let (t, _) = Tables::new(&g, &plan(g.graph(), false)).unwrap();
        let captures = |l: &&crate::tables::LambdaInfo| t.nodes[l.node].node().inputs.len() == 2;
        let inner = t.lambdas.iter().position(|l| captures(&l)).unwrap();
        (State::new(Arc::new(t), Evaluator::new(World::new())), inner)
    }

    #[test]
    fn a_closure_captured_twice_at_each_level_is_built_once() {
        let (mut s, inner) = two_captures();
        let mut w = Word::int(7);
        for _ in 0..64 {
            s.run.heap.inc(w).unwrap();
            w = s.run.heap.alloc(Obj::Clo {
                lambda: inner,
                caps: vec![w, w],
            });
        }
        // A tree of every path would hold 2^64 copies of the bottom closure.
        let mut lets = Lets::default();
        let made = term(&s.t, &mut s.run, w, &mut lets).unwrap();
        assert_eq!(lets.closures.len(), 64);
        // `(y) -> (c = y < 1; r = if c { a } else { z = y - 1; b(z) }; r)` with each capture's
        // term in place of `a` and `b`: at every level the two are one body, shared.
        let (mut at, mut levels) = (&made, 0);
        while let Term::Lam(_, body) = at
            && let Term::Let(_, _, rest) = &**body
            && let Term::Let(_, r, _) = &**rest
            && let Term::If(_, a, other) = &**r
            && let Term::Let(_, _, call) = &**other
            && let Term::Let(_, b, _) = &**call
            && let (Term::Lam(_, a_body), Term::App(b, _)) = (&**a, &**b)
            && let Term::Lam(_, b_body) = &**b
        {
            assert_eq!(a_body.id(), b_body.id());
            (at, levels) = (&**a, levels + 1);
        }
        assert_eq!(levels, 63, "the bottom closure captures two numbers");
        // The kernel runs the term as it is: 63 calls down through the second capture, each
        // level once, to the bottom closure's first capture.
        let ran = Evaluator::new(World::new()).run(&app(made, vec![lit(63i64)]));
        assert_eq!(ran.unwrap(), Value::Int(7));
    }

    #[test]
    fn a_closure_freed_and_its_cell_taken_again_gets_its_own_term() {
        let (mut s, inner) = two_captures();
        let clo = |a, b| Obj::Clo {
            lambda: inner,
            caps: vec![Word::int(a), Word::int(b)],
        };
        let mut lets = Lets::default();
        let old = s.run.heap.alloc(clo(1, 2));
        let was = term(&s.t, &mut s.run, old, &mut lets).unwrap().to_string();
        s.run.heap.dec(old).unwrap();
        let new = s.run.heap.alloc(clo(3, 4));
        assert_eq!(
            s.run.heap.cell_slots(),
            1,
            "the new closure takes the old cell"
        );
        assert_ne!(new, old, "the cell's word names its generation");
        let got = term(&s.t, &mut s.run, new, &mut lets).unwrap().to_string();
        let fresh = term(&s.t, &mut s.run, new, &mut Lets::default()).unwrap();
        assert_eq!(got, fresh.to_string());
        assert_ne!(got, was);
    }

    /// A run of the program `0` installed, with a string cell already freed: a word of it kept
    /// past its free, as a wrong plan would keep it, and a live string.
    fn with_a_freed_cell() -> (Word, Word) {
        let g = crate::legal::legalize(lower(&Term::Lit(Value::Int(0))).unwrap());
        let (t, _) = Tables::new(&g, &plan(g.graph(), false)).unwrap();
        install(State::new(Arc::new(t), Evaluator::new(World::new())));
        with(|_, s| {
            let old = s.heap.alloc(Obj::Str("old".into()));
            s.heap.dec(old).unwrap();
            let new = s.heap.alloc(Obj::Str("new".into()));
            (old, new)
        })
    }

    const SHARED_AFTER_FREE: &str = "runtime: cell 0 is shared after it was freed";

    #[test]
    fn an_inc_that_fails_as_the_last_write_ends_the_run_with_its_error() {
        let (old, new) = with_a_freed_cell();
        // The result is dropped first; the failing `inc` is the run's last write, and the run
        // ends with no result word, so `finish` drops nothing.
        rt_dec(new.tag, new.bits);
        rt_inc(old.tag, old.bits);
        let mut s = remove();
        assert_eq!(
            finish(&s.t, &mut s.run, Word::err()).unwrap_err(),
            SHARED_AFTER_FREE
        );
    }

    #[test]
    fn an_inc_that_fails_before_a_dec_is_the_error_and_the_dec_still_drops() {
        let (old, new) = with_a_freed_cell();
        rt_inc(old.tag, old.bits);
        rt_dec(new.tag, new.bits);
        let mut s = remove();
        assert_eq!(s.run.heap.live(), 0, "the drop was written");
        assert_eq!(
            finish(&s.t, &mut s.run, Word::int(0)).unwrap_err(),
            SHARED_AFTER_FREE
        );
    }

    #[test]
    fn binders_of_a_deep_pattern_are_renamed_in_preorder() {
        let bind = |x: &str| Pattern::Bind(x.into());
        let inner = (0..DEPTH).fold(bind("c"), |p, _| Pattern::Tuple(vec![p]));
        let mut p = ManuallyDrop::new(Pattern::Fields(
            "pair".into(),
            vec![("a".into(), bind("a")), ("b".into(), inner)],
        ));
        let mut n = 0;
        rename(&mut p, &mut || {
            n += 1;
            format!("v{n}").into()
        });
        assert_eq!(n, 2);
        let Pattern::Fields(_, fs) = &*p else {
            unreachable!()
        };
        assert!(matches!(&fs[0].1, Pattern::Bind(x) if &**x == "v1"));
        let mut at = &fs[1].1;
        while let Pattern::Tuple(ps) = at {
            at = &ps[0];
        }
        assert!(matches!(at, Pattern::Bind(x) if &**x == "v2"));
    }
}
