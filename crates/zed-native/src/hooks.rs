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

use zed_kernel::eval::{
    FamilyGot, HeldFamilyAt, Made, MadeNode, MadeShape, held_family_got, placed_fun_term,
};
use zed_kernel::text::prose;
use zed_kernel::value::HeldFamily;
use zed_kernel::{Evaluator, Fields, KernelError, Pattern, Prim, Shared, Term, Text, Value};
use zedc::zir::Op;
use zedc::zir::lower::raise_node;
use zedc::zir::memory::{HeldPart, Mode, held_family_term, held_term};

use zed_rt::{FunObj, Heap, HeldObj, HeldShape, Obj, Paths, Word};

use crate::tables::{NamedShape, NodeInfo, Placing, Tables};

/// A match's binders: each word and its node in the [`Paths`] of the scrutinee.
type Binders = Vec<(Word, usize)>;

/// The kernel's decision on a match: the arm and its number of binders, or the failure value.
type Decision = Result<(usize, usize), Value>;

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
    /// The words a call by name stored at the address [`rt_args`] gave, the first
    /// [`Run::slots_len`] of them; kept between calls, never emptied, grown only by [`rt_args`].
    slots: Vec<Word>,
    /// How many words of [`Run::slots`] the last [`rt_args`] asked for.
    slots_len: usize,
    outs: Vec<Word>,
    pending: Word,
    pub err: Option<String>,
    /// The number of the node whose hook recorded [`Run::err`], when a hook with a node
    /// recorded it: the executable prints the site of that node (plan row RT-sites).
    pub err_at: Option<usize>,
    /// The address of each lambda's entry, then of its body ([`Tables::body`]), then of its
    /// placed entry ([`Tables::placed`]), then of each function that calls a body on
    /// [`Run::named`] ([`Tables::trampoline`]).
    entries: Vec<i64>,
    /// The call [`rt_named`] placed: the body's address, the closure's word and the
    /// arguments' words, flat; kept between calls.
    named: Vec<i64>,
    /// For each node, the merge its last call by name made ([`place_named`]).
    merged: Vec<Option<Merged>>,
    pub kernel_calls: u64,
    /// How many calls by name ran through a placed entry ([`rt_direct`], [`rt_direct_read`]).
    pub placed_calls: u64,
    /// For each atom node, the shape last made from constant name and field words.
    shapes: Vec<Option<(Word, Word, Shape)>>,
    /// The number of hook calls so far, raised by [`with`]; debug builds only.
    #[cfg(debug_assertions)]
    hook_calls: u64,
    /// [`Run::hook_calls`] when [`rt_direct`] last sent a call to a placed entry, until that
    /// entry's [`rt_direct_read`]; debug builds only.
    #[cfg(debug_assertions)]
    direct_at: Option<u64>,
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
        #[cfg(feature = "counts")]
        if RECORD.with(|r| r.get()) {
            heap.record_releases();
        }
        for (i, v) in t.consts.iter().enumerate() {
            let w = heap.uncounted(v.clone());
            debug_assert_eq!(w.bits as usize, i);
        }
        let run = Run {
            heap,
            ev,
            args: Vec::new(),
            slots: Vec::new(),
            slots_len: 0,
            outs: Vec::new(),
            pending: Word::err(),
            err: None,
            err_at: None,
            entries: vec![0; t.entry_count()],
            named: Vec::new(),
            merged: vec![None; t.nodes.len()],
            kernel_calls: 0,
            placed_calls: 0,
            shapes: vec![None; t.nodes.len()],
            #[cfg(debug_assertions)]
            hook_calls: 0,
            #[cfg(debug_assertions)]
            direct_at: None,
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
        #[cfg(debug_assertions)]
        {
            s.run.hook_calls += 1;
        }
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

/// Records `e` as the run's error, raised at node `at` when a node's hook raised it, unless an
/// error is recorded already: the first one stops the run.
fn fail(s: &mut Run, e: String, at: Option<usize>) {
    if s.err.is_none() {
        s.err = Some(e);
        s.err_at = at;
    }
}

/// `r`'s word, or the error word with the message recorded, raised at node `at`.
fn word(s: &mut Run, r: Result<Word, String>, at: Option<usize>) -> Word {
    r.unwrap_or_else(|e| {
        fail(s, e, at);
        Word::err()
    })
}

fn code(s: &mut Run, r: Result<i64, String>, at: Option<usize>) -> i64 {
    r.unwrap_or_else(|e| {
        fail(s, e, at);
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
    ("rt_pow", 2, 1),
    ("rt_named", 1, 2),
    ("rt_args", 1, 1),
    ("rt_direct", 3, 2),
    ("rt_direct_read", 0, 0),
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
        rt_pow as extern "C" fn(i64, i64) -> i64 as *const u8,
        rt_named as extern "C" fn(i64) -> Named as *const u8,
        rt_args as extern "C" fn(i64) -> i64 as *const u8,
        rt_direct as extern "C" fn(i64, i64, i64) -> Named as *const u8,
        rt_direct_read as extern "C" fn() as *const u8,
    ]
}

/// The address of the buffer of a call by name's words ([`Run::slots`]), at least `n` words
/// long, for native code to store all `n` in as `rt_arg` would pass them one at a time: each
/// [`Word`] two `i64`s, tag first. Read by the next hook, [`rt_named`] or [`rt_direct`] and its
/// placed entry; only this hook moves the buffer.
// Complexity tradeoff: `rt_arg` costs a hook call per word, about 30 instructions and the
// borrow of the run; here one call per node and two stores per word. Used by a call by name
// ([`rt_named`]), whose p arguments made it 8 times the cost of a direct call at p = 320
// (`a_placed_call_costs_about_a_direct_call_in_native_code`, row CALL-callee-places-native).
// The buffer is filled only when it grows, O(largest n) over the run, since the call site
// stores every word before any is read. Emptying it and filling n words again at each call, as
// before, cost about 12 instructions a word under nightly-2026-11-18 (`clear` and
// `Vec::resize`), 3.9K a call at p = 320, which made the placed call 1.59 times the direct
// one's run (row CALL-direct-buffer-proof).
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_args(n: i64) -> i64 {
    with(|_, s| {
        let n = n as usize;
        if s.slots.len() < n {
            s.slots.resize(n, Word::err());
        }
        s.slots_len = n;
        s.slots.as_mut_ptr() as i64
    })
}

/// Where [`rt_named`] sends a call: the address of the function that calls a body on the
/// words of `buf` ([`Tables::trampoline`]), 0 when the kernel is to run the call, or
/// [`Word::ERR`] when the run failed; laid out as two `i64` results.
#[repr(C)]
pub(crate) struct Named {
    call: i64,
    buf: i64,
}

/// A call by name, `callNamed` node `id` on the words [`rt_args`] gave: when the function is a
/// closure a `place` made in native code ([`placed_clo`]) and its parameter list places every
/// argument, the call placed, in [`Run::named`], as the kernel's `placing` places it (DESIGN.md
/// sec:values_morphisms, "The function called places the arguments"): each argument in its
/// parameter, and a function with a fill called through its fill on the parameters, a `false`
/// in each defaulted one the call leaves out, then a flag for each defaulted one, `true` where
/// left out. The body is called as a direct call calls it, on what the node borrows, with a
/// reference to each argument it consumes. In every other case the words are copied to the
/// buffer of [`rt_arg`] and the kernel runs the call on them (`rt_node` next), which gives the
/// same value or error (row CALL-callee-places-native).
// Complexity tradeoff: the kernel's call (`rt_node`) builds the term of the function and of
// each argument and runs it, O(p + a) for p parameters and a arguments and a large constant,
// and the function's body runs in the kernel. Here the call's sorted names and the function's
// sorted parameter names are merged once, O(p + a) comparisons of the names' ranks (each
// O(1), [`Tables::rank_names`]), once for each node and list unless an argument has a flag
// ([`place_named`]), with no allocation after the first call (the merges and the buffers
// are kept), and the body runs in native code. The naive merge searches the parameter names
// for each argument, O(p·a). Tradeoff: the arguments are copied twice, into the buffer and
// the call's. Nothing is refused.
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_named(id: i64) -> Named {
    with(|t, s| {
        // `take` and the restore below move only the `Vec`'s header, not its heap buffer, and
        // `place_named` is plain Rust that runs no native code and calls no hook, so the
        // address `rt_args` gave stays valid: only `rt_args` moves the buffer.
        let ins = std::mem::take(&mut s.slots);
        let ins_n = &ins[..s.slots_len];
        let r = place_named(t, s, id as usize, ins_n);
        if matches!(r, Ok(None)) {
            // The kernel runs the call on these words (`rt_node`, through `with_args`).
            s.args.clear();
            s.args.extend_from_slice(ins_n);
        }
        s.slots = ins;
        match r {
            Ok(Some(call)) => Named {
                call,
                buf: s.named.as_ptr() as i64,
            },
            Ok(None) => Named { call: 0, buf: 0 },
            Err(e) => {
                fail(s, e, Some(id as usize));
                Named {
                    call: Word::ERR,
                    buf: 0,
                }
            }
        }
    })
}

/// A parameter of [`Merged::from`] that the call leaves out.
const LEFT: u32 = u32::MAX;

/// Where `callNamed` node `id`, of a shape with no flag, sends its call of function `f`
/// (`tag`, `bits`) without [`rt_named`]: when the merge kept for the node ([`Run::merged`]) is
/// for the list of the closure `f` and that list has no fill, the address of the placed entry
/// of `f`'s lambda ([`Tables::placed`]) and of the merge's byte offsets ([`Merged::offs`]), from
/// which the entry reads each parameter among the arguments the call site stored with
/// [`rt_args`]; else a call of 0, and the call goes through [`rt_named`], which makes the merge.
/// A lambda with no placed entry misses. The buffer is kept either way.
// Complexity tradeoff: through `rt_named` a call passes its p arguments three times, into the
// runtime's buffer, into the placed order ([`call_placed`]) and into the body, where a call to
// the function by its name passes them once; the placed call ran 2.6 times the instructions of
// the direct one at p = 320 (row CALL-callee-places-native). Here O(1): the closure, the kept
// merge and the lambda's number of parameters are compared, and the entry reads each argument
// where the call site stored it, one load of its offset more than a direct call. A call through
// lists that alternate misses here and merges in `rt_named`, as before.
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_direct(id: i64, tag: i64, bits: i64) -> Named {
    with(|t, s| {
        let none = Named { call: 0, buf: 0 };
        let Some(Merged {
            placing,
            from: Some(_),
            offs,
        }) = &s.merged[id as usize]
        else {
            return none;
        };
        let Ok(Some(Obj::Clo {
            lambda,
            placed: Some(pi),
            ..
        })) = s.heap.obj(Word { tag, bits })
        else {
            return none;
        };
        let p = &t.placings[*pi as usize];
        if pi != placing || p.fill || t.lambdas[*lambda].params != p.n {
            return none;
        }
        let call = s.entries[t.placed(*lambda)];
        #[cfg(debug_assertions)]
        if call != 0 {
            s.direct_at = Some(s.hook_calls);
        }
        Named {
            call,
            buf: offs.as_ptr() as i64,
        }
    })
}

/// Called by a placed entry ([`Tables::placed`]) once it has read its arguments from the
/// buffer of [`rt_args`], as the first hook it calls: counts the call
/// ([`Run::placed_calls`]) and, in debug builds, checks the reads.
///
/// Why the entry reads the words the call site stored: the call site (`Gen::named`) stores
/// them at the address [`rt_args`] gave and calls [`rt_direct`], which changes neither the
/// buffer nor its length; on a hit the code between `rt_direct`'s return and this hook is a
/// compare, a branch, an add and the indirect call, in `Gen::named_direct`, then the entry's
/// jump to its first block and its loads, in `Gen::function` and `Gen::placed`, and none of it
/// calls a hook. A hook in between could move the buffer ([`rt_args`] grows it) or have
/// native code overwrite it (the stores after [`rt_args`] of a nested call by name), so debug
/// builds check that no hook ran between [`rt_direct`] and this one: every hook goes through
/// [`with`], which counts it. Nothing empties the buffer ([`Run::slots`]).
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_direct_read() {
    with(|_, s| {
        // A failed run, not a panic, which would abort the process from an `extern "C"` fn.
        #[cfg(debug_assertions)]
        if s.direct_at.take().map(|n| n + 1) != Some(s.hook_calls) {
            let e = zed_rt::bug(
                "read a call's arguments after the runtime could have changed them",
                "a hook ran between rt_direct and the placed entry's rt_direct_read",
            );
            fail(s, e, None);
        }
        s.placed_calls += 1;
    });
}

/// The merge of a call by name with a parameter list, kept for the call's node.
#[derive(Clone)]
struct Merged {
    /// The parameter list's number among [`Tables::placings`].
    placing: u32,
    /// For each parameter, the index among the call's arguments of the one it gets, or
    /// [`LEFT`]; none when the list does not place the call.
    from: Option<Vec<u32>>,
    /// For each parameter, the byte offset of its argument among the call's arguments after
    /// the function, each two `i64`s: what [`rt_direct`] gives a placed entry. Empty unless
    /// the list places the call and has no fill.
    offs: Vec<i64>,
}

/// The address of the function that calls the body [`rt_named`] places node `id`'s call
/// on, with the call in [`Run::named`]; none when the kernel is to run it.
// Complexity tradeoff: the merge of the call's names with the list, O(p + a), depends only on
// the node and the list when the call leaves no argument out by a flag, so it is kept for the
// node ([`Run::merged`]) and a call through the same list copies the arguments, O(p), with no
// compare; it was 40% of a placed call's run time at p = 320 (row CALL-callee-places-native).
// A node called through lists that alternate merges at each call, as before. Memory: O(p)
// per node that calls by name.
fn place_named(t: &Tables, s: &mut Run, id: usize, ins: &[Word]) -> Result<Option<i64>, String> {
    let sh = t.nodes[id]
        .named
        .as_deref()
        .expect("a call with a literal shape");
    let (lambda, pi, fill) = match s.heap.obj(ins[1])? {
        Some(Obj::Clo {
            lambda,
            caps,
            placed: Some(pi),
        }) => {
            let fill = t.placings[*pi as usize].fill;
            (*lambda, *pi, fill.then(|| *caps.last().expect("a fill")))
        }
        _ => return Ok(None),
    };
    let p = &t.placings[pi as usize];
    let (given, flags) = ins[2..].split_at(sh.k + sh.names.len());
    let (from, offs) = match s.merged[id].take() {
        Some(m) if m.placing == pi && !sh.flagged => (m.from, m.offs),
        old => {
            let (mut from, mut offs) = old
                .map(|m| (m.from.unwrap_or_default(), m.offs))
                .unwrap_or_default();
            let placed = merge(sh, p, flags, &mut from);
            offs.clear();
            if placed && !p.fill {
                offs.extend(from.iter().map(|&x| 16 * i64::from(x)));
            }
            (placed.then_some(from), offs)
        }
    };
    let r = match &from {
        Some(from) => call_placed(t, s, given, from, (ins[1], lambda), p, fill),
        None => Ok(None),
    };
    s.merged[id] = Some(Merged {
        placing: pi,
        from,
        offs,
    });
    r
}

/// Sets `from` to the parameter each argument of the call of shape `sh` goes to under list
/// `p`, the flags `flags` saying which the call leaves out; false when the list does not place
/// the call: an argument it has no parameter for, two for one parameter, or a parameter left
/// out that the function does not fill.
fn merge(sh: &NamedShape, p: &Placing, flags: &[Word], from: &mut Vec<u32>) -> bool {
    if sh.k > p.n {
        return false;
    }
    // As the kernel reads a flag: a name is left out when its flag is the boolean true.
    let yes = Word {
        tag: Word::BOOL,
        bits: 1,
    };
    let left_out = |i: usize| sh.opt[i].is_some_and(|x| flags.get(x) == Some(&yes));
    from.clear();
    from.extend(0..sh.k as u32);
    from.resize(p.n, LEFT);
    // One merge of the call's sorted names with the function's, as the kernel's, by the
    // names' ranks ([`Tables::rank_names`]), which keep their order.
    let (mut i, mut j) = (0, 0);
    while i < sh.names.len() {
        if left_out(i) {
            i += 1;
            continue;
        }
        let Some(q) = p.ranks.get(j) else {
            return false;
        };
        match sh.ranks[i].cmp(q) {
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Less => return false,
            std::cmp::Ordering::Equal => {
                let slot = &mut from[p.places[j]];
                if *slot != LEFT {
                    return false;
                }
                *slot = (sh.k + sh.at[i]) as u32;
                i += 1;
                j += 1;
            }
        }
    }
    // Without a fill every parameter needs a value; with one, every parameter without a
    // default.
    !(from.iter().zip(&p.defaulted)).any(|(x, d)| *x == LEFT && (!p.fill || !d))
}

/// The call of closure `f`, of `lambda` with list `p` and fill `fill`, on the arguments
/// `given` as `from` places them, in [`Run::named`], as [`place_named`] gives it; none, with
/// nothing changed, when the kernel is to run it: a body that does not take the parameters
/// one word each.
fn call_placed(
    t: &Tables,
    s: &mut Run,
    given: &[Word],
    from: &[u32],
    (f, lambda): (Word, usize),
    p: &Placing,
    fill: Option<Word>,
) -> Result<Option<i64>, String> {
    let (callee, clo, arity) = match fill {
        None => (lambda, f, p.n),
        Some(g) => match s.heap.obj(g)? {
            Some(Obj::Clo { lambda, .. }) => (*lambda, g, p.n + p.defaults),
            _ => return Ok(None),
        },
    };
    if t.lambdas[callee].params != arity {
        return Ok(None);
    }
    let push = |b: &mut Vec<i64>, w: Word| b.extend([w.tag, w.bits]);
    let mut b = std::mem::take(&mut s.named);
    b.clear();
    // The body, as a direct call calls it: it borrows what the call borrows, and gets a
    // reference to each argument it consumes.
    // Complexity tradeoff: calling the entry instead gave every argument a reference here
    // and the entry dropped it after, two count changes per argument the body borrows, 25% of
    // a placed call's run time at p = 320 (row CALL-callee-places-native). The cost is the
    // bodies' addresses, registered once a run.
    b.push(s.entries[t.body(callee)]);
    push(&mut b, clo);
    let left = Word {
        tag: Word::BOOL,
        bits: 0,
    };
    for (&x, m) in from.iter().zip(&t.lambdas[callee].modes) {
        let w = if x == LEFT { left } else { given[x as usize] };
        if *m == Mode::Owned && w.tag == Word::CELL {
            s.heap.inc(w)?;
        }
        push(&mut b, w);
    }
    if fill.is_some() {
        for (&x, _) in from.iter().zip(&p.defaulted).filter(|(_, d)| **d) {
            push(
                &mut b,
                Word {
                    tag: Word::BOOL,
                    bits: i64::from(x == LEFT),
                },
            );
        }
    }
    s.named = b;
    Ok(Some(s.entries[t.trampoline(arity)]))
}

/// Float `^` on the bits of two floats: IEEE 754 `pow`, a NaN it makes (of a NaN operand, or
/// a finite base below `-0.0` to a finite non-integer power) replaced by the canonical NaN, as
/// the kernel does. Generated code sends a NaN operand to the NaN before this call wherever
/// the graph does not rule out `pow(NaN, 0) = 1` and `pow(1, NaN) = 1` (DESIGN.md sec:domains,
/// NaN rule 5; `codegen.rs`, fn `pow`). It reads and writes no run state. Citation: IEEE
/// Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 9.2, "Additional mathematical
/// operations"; the full comment is in zed-kernel `eval.rs`, fn `prim_on`, at `Prim::Pow`.
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "a linked executable finds each hook by its symbol (step L1.36a)"
)]
extern "C" fn rt_pow(a: i64, b: i64) -> i64 {
    let r = f64::from_bits(a as u64).powf(f64::from_bits(b as u64));
    zed_kernel::F64::new(r).get().to_bits() as i64
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
        word(s, r, Some(id as usize))
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
            fail(s, e, None);
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
            fail(s, e, None);
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
        word(s, r, None)
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
        code(s, r, Some(id as usize))
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
        code(s, r, Some(id as usize))
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
        let e = t.nodes[id as usize]
            .error
            .as_deref()
            .unwrap_or("a node raised no error");
        word(
            s,
            Err(zed_rt::bug(
                "passed a value to a function that releases it, without a reference of its own",
                e,
            )),
            Some(id as usize),
        )
    })
}

/// Whether every word of `ins` is data: not a function, not a value that holds one, and not a
/// port's state.
fn all_data(s: &Run, ins: &[Word]) -> Result<bool, String> {
    for w in ins {
        if w.tag == Word::STATE || s.heap.holds_function(*w)? {
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
/// out once the system gives the memory, else `None`, which hands the atom to the kernel, whose
/// error it then is. The names here are the program's literals, one block each, so `try_shared`
/// does not fail for a compiled program (the proof is at the kernel's `atom_name`).
fn atom_name(x: &Text) -> Option<Arc<str>> {
    x.try_shared().ok()
}

/// The shape of atom node `id` on `ins`, `[name, field names, payload…]`, or `None` when the
/// kernel refuses it. A shape made from stable words is kept for the node's next run.
// Complexity tradeoff: the naive atom node hands its whole payload to the kernel and back,
// O(payload) per atom, so a list of n atoms, each holding the rest, costs O(n²) (COMPLEXITY.md
// R2: 30.0 times for 8 times the length). Here `node` makes the atom from its words as
// `Prim::Atom` would, with this shape, and the kernel is called only for a shape it refuses,
// so that the error is the kernel's; a shape whose name and field names are constants is kept
// per node, so a struct atom run again costs no sort and no map. Tradeoffs: the kernel's
// atom rules (field order, a repeated name refused) are written a second time here and must
// agree with it; one kept shape per atom node. Tests
// `l01_36_cranelift::scaling::a_list_of_many_atoms_scales` and `l01_36_cranelift::hooks`.
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
                let Some(x) = atom_name(x) else {
                    return Ok(None);
                };
                named.push((x, i));
            }
            // The kernel's order, and its refusal of a repeated name (`Value::atom_named`).
            named.sort_by(|a, b| a.0.cmp(&b.0));
            if named.windows(2).any(|w| w[0].0 == w[1].0) {
                return Ok(None);
            }
            named.into_iter().unzip()
        }
    };
    let Some(name) = atom_name(&name) else {
        return Ok(None);
    };
    let sh = Shape {
        name,
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
            Ok(s.heap.alloc(Obj::Tuple(ins.into())))
        }
        // A tuple or an atom with a part that is no data is a held value, its parts moved into
        // its cell as a data tuple's are, as the machine makes it (`Mv::Held`).
        Op::Prim(Prim::Tuple) if any_holds_function(s, ins)? => {
            Ok(s.heap.alloc(Obj::Held(Box::new(HeldObj {
                shape: HeldShape::Tuple,
                parts: ins.into(),
            }))))
        }
        // A display with an entry that is no data is a held family; a key that is no data, or
        // entries the kernel refuses, are the kernel's error.
        Op::Prim(Prim::Entries) if any_holds_function(s, ins)? => match held_entries(s, ins)? {
            Some(h) => {
                let w = s.heap.alloc(Obj::Held(Box::new(h)));
                consume(s, ni, ins)?;
                Ok(w)
            }
            None => slow(t, s, ni, ins),
        },
        // A held family read: the entry, owned, or what the kernel gives where it is not
        // this one's to make.
        Op::Prim(p) if family_at(s, *p, ins)?.is_some() => match family_read(s, *p, ins)? {
            Some(w) => {
                consume(s, ni, ins)?;
                Ok(w)
            }
            None => slow(t, s, ni, ins),
        },
        Op::Prim(Prim::Atom)
            if ins.len() > 2 && all_data(s, &ins[..2])? && any_holds_function(s, &ins[2..])? =>
        {
            match shape(t, s, id, ins)? {
                None => slow(t, s, ni, ins),
                Some(sh) => Ok(s.heap.alloc(Obj::Held(Box::new(HeldObj {
                    parts: sh.order.iter().map(|&i| ins[2 + i]).collect(),
                    shape: HeldShape::Atom(sh.name, sh.fields),
                })))),
            }
        }
        // A held tuple read at a key: the part, or what the kernel gives for a key outside it.
        Op::Prim(Prim::TupleGet | Prim::At)
            if ins.len() == 2 && s.heap.held(ins[0])?.is_some_and(|h| h.is_tuple()) =>
        {
            match read_held(s, ins[0], ins[1])? {
                Some(w) => give(s, ni, ins, w),
                None => slow(t, s, ni, ins),
            }
        }
        // Any other primitive given a held value: an atom that holds a function passes
        // through as a failure does, and anything else is the kernel's error.
        Op::Prim(p) if any_held(s, ins)? => match passed(s, *p, ins)? {
            Some(w) => give(s, ni, ins, w),
            None => slow(t, s, ni, ins),
        },
        // A held family applied to a key is read at it, as the kernel applies it; a primitive
        // called on one reads it as the primitive's node does.
        Op::Apply if !ins.is_empty() && family_called(t, s, ins)?.is_some() => {
            let (p, args) = family_called(t, s, ins)?.expect("checked above");
            match family_read(s, p, &ins[args..])? {
                Some(w) => {
                    consume(s, ni, ins)?;
                    Ok(w)
                }
                None => slow(t, s, ni, ins),
            }
        }
        // A call that is not a closure's, of a held value or on one.
        Op::Apply if any_held(s, ins)? => match called(t, s, ins)? {
            Some(w) => give(s, ni, ins, w),
            None => slow(t, s, ni, ins),
        },
        // The atom is made from its words, as the kernel would make it: the payload moves
        // into the cell, and the name and field names are borrowed.
        Op::Prim(Prim::Atom) if ins.len() >= 2 && all_data(s, ins)? => {
            match shape(t, s, id, ins)? {
                None => slow(t, s, ni, ins),
                Some(sh) if ins.len() == 2 => {
                    consume(s, ni, ins)?;
                    s.heap.fresh(&Value::atom_with(sh.name, Vec::new()))
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
            s.heap.fresh(&v)
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
            caps: ins.into(),
            placed: None,
        })),
        // `place(table, f[, fill])` with a literal table and closures the program made: the
        // closure `f` with the table's parameter list, and the fill after its captures, so a
        // call of it by name places its arguments in native code (`rt_named`) and a call by
        // position calls its entry as before (row CALL-callee-places-native). Any other `f`
        // is the kernel's.
        // Complexity tradeoff: the kernel's `place` copies the closure's environment into a
        // new closure, O(captures), as this does; nothing more. Nothing is refused.
        Op::Prim(Prim::Place) if ni.placing.is_some() => match placed_clo(t, s, ni, ins)? {
            Some(w) => {
                consume(s, ni, ins)?;
                Ok(w)
            }
            None => slow(t, s, ni, ins),
        },
        Op::Read(p) => match s.ev.world.inputs.get(&**p) {
            Some(v) => {
                let v = v.clone();
                s.heap.fresh(&v)
            }
            None if s.ev.world.sources.contains_key(&**p) => Ok(Word {
                tag: Word::SOURCE,
                bits: t.port_at[p] as i64,
            }),
            None => {
                let v = s.ev.run(&Term::Read(p.clone()));
                Err(v.map_or_else(
                    |e| e.to_string(),
                    |_| {
                        zed_rt::bug(
                            "read a port the run was not given",
                            &format!("port `{p}` is neither an input nor a source of the run"),
                        )
                    },
                ))
            }
        },
        _ => slow(t, s, ni, ins),
    }
}

/// Whether some word of `ins` holds a function.
fn any_holds_function(s: &Run, ins: &[Word]) -> Result<bool, String> {
    for w in ins {
        if s.heap.holds_function(*w)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Whether some word of `ins` is a held tuple or atom.
fn any_held(s: &Run, ins: &[Word]) -> Result<bool, String> {
    for w in ins {
        if s.heap.held(*w)?.is_some() {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The node gives `w`, a part of its inputs or one of them: `w` gets a reference before the
/// owned inputs are dropped, so dropping them frees nothing `w` holds. As the machine's
/// `give`.
fn give(s: &mut Run, ni: &NodeInfo, ins: &[Word], w: Word) -> Result<Word, String> {
    s.heap.inc(w)?;
    consume(s, ni, ins)?;
    Ok(w)
}

/// What held tuple `h` read at key `k` gives when it is not the kernel's to make: the part at
/// an integer key inside the tuple, or `k` itself when it is an atom that holds a function.
/// As the machine's `read_held`.
fn read_held(s: &Run, h: Word, k: Word) -> Result<Option<Word>, String> {
    if k.tag == Word::INT {
        let h = s.heap.held(h)?.expect("a held tuple");
        return Ok(usize::try_from(k.bits)
            .ok()
            .and_then(|i| h.parts.get(i))
            .copied());
    }
    Ok(s.heap.is_held_atom(k)?.then_some(k))
}

/// The entries of display `ins`, key then value, as a held family with each value that holds
/// a function a part, each part given a reference of its own; `None` when a key holds a
/// function or the kernel refuses the entries, which is then the kernel's error to give.
// Complexity tradeoff: the naive display hands every entry to the kernel, which cannot give a
// value that holds a function back (`Evaluator::run` gives data). Here the keys and data
// entries are read out of their words, as the kernel's term for them would be, and the
// family built by the kernel's own rules ([`HeldFamily::new`]): O(n log n) for n entries, the
// cost of a data display. Tradeoff: the data entries are copied out of their words, as the
// display of data copies them for the kernel.
fn held_entries(s: &mut Run, ins: &[Word]) -> Result<Option<HeldObj>, String> {
    let mut entries = Vec::with_capacity(ins.len() / 2);
    let mut parts = Vec::new();
    for kv in ins.chunks(2) {
        let &[k, v] = kv else { return Ok(None) };
        if s.heap.holds_function(k)? {
            return Ok(None);
        }
        let k = s.heap.value(k)?;
        if s.heap.holds_function(v)? {
            parts.push(v);
            entries.push((k, None));
        } else {
            entries.push((k, Some(s.heap.value(v)?)));
        }
    }
    let Ok(Some(f)) = HeldFamily::new(entries) else {
        return Ok(None);
    };
    for &p in &parts {
        s.heap.inc(p)?;
    }
    Ok(Some(HeldObj {
        shape: HeldShape::Family(Box::new(f)),
        parts: parts.into(),
    }))
}

/// The position in `ins` of the held family primitive `p` reads, when it reads one.
fn family_at(s: &Run, p: Prim, ins: &[Word]) -> Result<Option<usize>, String> {
    let (at, n) = match p {
        Prim::Get | Prim::TupleGet | Prim::At | Prim::EntryAfter | Prim::EntryBefore => (0, 2),
        Prim::Has => (1, 2),
        Prim::Count | Prim::FirstEntry | Prim::LastEntry | Prim::First | Prim::Last => (0, 1),
        _ => return Ok(None),
    };
    if ins.len() != n {
        return Ok(None);
    }
    let held = s.heap.held(ins[at])?.is_some_and(|h| h.family().is_some());
    Ok(held.then_some(at))
}

/// The primitive a call `ins[0](ins[1..])` reads a held family with, and where its operands
/// start in `ins`: `Get` for the family applied to one key, or the primitive called.
fn family_called(t: &Tables, s: &Run, ins: &[Word]) -> Result<Option<(Prim, usize)>, String> {
    if ins.len() == 2 && family_at(s, Prim::Get, ins)?.is_some() {
        return Ok(Some((Prim::Get, 0)));
    }
    if ins[0].tag != Word::PRIM {
        return Ok(None);
    }
    let p = t.prims[ins[0].bits as usize];
    Ok(family_at(s, p, &ins[1..])?.map(|_| (p, 1)))
}

/// A held family on the heap, read by the kernel's [`held_family_got`] from [`family_read`].
struct NativeFamily<'a> {
    heap: &'a Heap,
    h: &'a HeldObj,
}

impl HeldFamilyAt for NativeFamily<'_> {
    type Part = Word;
    type Error = String;

    fn family(&self) -> &HeldFamily {
        self.h
            .family()
            .expect("only held families are read as families")
    }

    fn part(&self, i: usize) -> Word {
        self.h.parts[i]
    }

    fn sub_family(&self, i: usize) -> Result<Option<Self>, String> {
        Ok(match self.heap.held(self.h.parts[i])? {
            Some(n) if n.family().is_some() => Some(NativeFamily {
                heap: self.heap,
                h: n,
            }),
            _ => None,
        })
    }
}

/// What primitive `p` gives on `ins`, which hold a held family where [`family_at`] says, as
/// the kernel's `Machine::held_family` gives it, as an owned word; `None` where the kernel
/// gives an error, which is then the kernel's to give.
// Complexity tradeoff: the naive read hands the family to the kernel, O(n) per read to build
// its term, so a loop of n reads is O(n²), and an entry that is a function cannot come back.
// Here each read is one lookup in the family's keys, O(log n), and `first` and `last` descend
// one level per step, O(depth · log n). Tradeoff: none; the rules of each read are the
// kernel's `held_family_got`, shared with the kernel and the memory machine (DRY-misc-A5), and
// this reads the key and makes the word on the heap. Tests in `completeness` and
// `l01_36_cranelift::held_values` check that the machines agree.
fn family_read(s: &mut Run, p: Prim, ins: &[Word]) -> Result<Option<Word>, String> {
    let at = family_at(s, p, ins)?.expect("a held family operand");
    let fam = ins[at];
    // The key read, or the entry tuple stepped from.
    let other = match ins.len() {
        2 => Some(ins[1 - at]),
        _ => None,
    };
    let key = match (p, other) {
        (_, None) => None,
        (Prim::EntryAfter | Prim::EntryBefore, Some(e)) => {
            if let Some(h) = s.heap.held(e)? {
                match (h.is_tuple(), &h.parts[..]) {
                    (true, &[k, _]) if !s.heap.holds_function(k)? => Some(s.heap.value(k)?),
                    _ => return Ok(None),
                }
            } else if s.heap.holds_function(e)? {
                return Ok(None);
            } else {
                match s.heap.value(e)? {
                    Value::Tuple(e) if e.len() == 2 => Some(e[0].clone()),
                    _ => return Ok(None),
                }
            }
        }
        (_, Some(k)) => {
            // A key that is a failure passes through.
            if s.heap.is_held_atom(k)? {
                s.heap.inc(k)?;
                return Ok(Some(k));
            }
            if s.heap.holds_function(k)? {
                return Ok(None);
            }
            match s.heap.value(k)? {
                k @ Value::Atom(_) => return s.heap.fresh(&k).map(Some),
                k => Some(k),
            }
        }
    };
    let h = s.heap.held(fam)?.expect("a held family");
    let got = held_family_got(p, NativeFamily { heap: &s.heap, h }, key.as_ref())?;
    Ok(Some(match got {
        FamilyGot::Data(v) => s.heap.fresh(&v)?,
        FamilyGot::Part(w) => {
            s.heap.inc(w)?;
            w
        }
        FamilyGot::Pair(k, w) => {
            let k = s.heap.fresh(&k)?;
            s.heap.inc(w)?;
            s.heap.alloc(Obj::Held(Box::new(HeldObj {
                shape: HeldShape::Tuple,
                parts: vec![k, w].into(),
            })))
        }
    }))
}

/// The input that primitive `p` gives back on `ins`, one of which is a held value, when `p`
/// passes an atom that holds a function through as a failure does. As the machine's `passed`
/// and the kernel's `Machine::held`.
fn passed(s: &Run, p: Prim, ins: &[Word]) -> Result<Option<Word>, String> {
    if matches!(
        p,
        Prim::Tuple | Prim::Atom | Prim::Eq | Prim::Ne | Prim::Path
    ) || p.arity().is_some_and(|n| n != ins.len())
    {
        return Ok(None);
    }
    let (mut failures, mut held) = (0, None);
    for &w in ins {
        if s.heap.is_held_atom(w)? {
            failures += 1;
            held = Some(w);
        } else if w.tag == Word::STATE || s.heap.holds_function(w)? {
            return Ok(None);
        } else if s.heap.is_data_atom(w)? {
            failures += 1;
        }
    }
    Ok(held.filter(|_| failures == 1))
}

/// What a call `ins[0](ins[1..])` of a held value, or of a primitive on one, gives, as the
/// kernel calls it. As the machine's `called`.
fn called(t: &Tables, s: &Run, ins: &[Word]) -> Result<Option<Word>, String> {
    let held_tuple =
        |w: Word| -> Result<bool, String> { Ok(s.heap.held(w)?.is_some_and(|h| h.is_tuple())) };
    if ins.len() == 2 && held_tuple(ins[0])? {
        return read_held(s, ins[0], ins[1]);
    }
    if s.heap.is_held_atom(ins[0])? {
        return Ok(Some(ins[0]));
    }
    if ins[0].tag != Word::PRIM {
        return Ok(None);
    }
    let p = t.prims[ins[0].bits as usize];
    let args = &ins[1..];
    if matches!(p, Prim::TupleGet | Prim::At) && args.len() == 2 && held_tuple(args[0])? {
        return read_held(s, args[0], args[1]);
    }
    passed(s, p, args)
}

/// The closure `place` node `ni` makes of `ins`, owned, when its function and fill are
/// closures the program made, `f` of as many parameters as the table lists (so its entry takes
/// the placed arguments, one word each) and the fill with no list of its own; none otherwise,
/// with nothing changed. As the kernel's `place`, a closure that already had a list gets this
/// one in its place, and its old fill is left out.
fn placed_clo(
    t: &Tables,
    s: &mut Run,
    ni: &NodeInfo,
    ins: &[Word],
) -> Result<Option<Word>, String> {
    let pi = ni.placing.expect("a placing node");
    let lambda = match s.heap.obj(ins[1])? {
        Some(Obj::Clo { lambda, .. }) if t.lambdas[*lambda].params == t.placings[pi as usize].n => {
            *lambda
        }
        _ => return Ok(None),
    };
    // The lambda's own captures; a fill an earlier `place` gave the closure is after them.
    let n = t.nodes[t.lambdas[lambda].node].node().inputs.len();
    let fill = match ins.get(2) {
        Some(&f) => match s.heap.obj(f)? {
            Some(Obj::Clo { placed: None, .. }) => Some(f),
            _ => return Ok(None),
        },
        None => None,
    };
    let Some(Obj::Clo { caps, .. }) = s.heap.obj(ins[1])? else {
        unreachable!("checked above")
    };
    let mut caps: Vec<Word> = caps[..n].to_vec();
    caps.extend(fill);
    for &c in &caps {
        s.heap.inc(c)?;
    }
    Ok(Some(s.heap.alloc(Obj::Clo {
        lambda,
        caps: caps.into(),
        placed: Some(pi),
    })))
}

/// The kernel runs the node, the owned inputs are dropped, and the value is allocated. The
/// value may be a function or hold one, a family of functions a `map` made included (row
/// FAIL-native-fam-result-holds-function): the kernel gives it apart from its run
/// ([`Made`]), and [`alloc_made`] allocates it, as the machine's `slow` does.
fn slow(t: &Tables, s: &mut Run, ni: &NodeInfo, ins: &[Word]) -> Result<Word, String> {
    let q = kernel_term(t, s, ni, ins)?;
    s.kernel_calls += 1;
    let m = s.ev.run_made(&q).map_err(|e| e.to_string())?;
    consume(s, ni, ins)?;
    alloc_made(t, s, m)
}

/// Allocates the value `m`: each node in order, a part before what holds it, data as
/// [`Heap::fresh`] makes it, a closure as an [`Obj::Fun`] and a held value as an
/// [`Obj::Held`], whose parts move into it; a node held at more places than one gets a
/// reference for each place past the first. As the machine's `alloc_made`.
// Complexity tradeoff: the naive way hands the kernel's value to `Heap::fresh`, which takes
// data only. Here each node is allocated once, O(nodes + parts), plus data as `fresh` costs.
// Tradeoff: a closure the kernel gave back is an `Obj::Fun` and not the closure word it may
// have been made from, so a call of it runs in the kernel. Nothing is refused.
fn alloc_made(t: &Tables, s: &mut Run, m: Made) -> Result<Word, String> {
    let mut words: Vec<Word> = Vec::with_capacity(m.nodes.len());
    let mut used = vec![false; m.nodes.len()];
    // Node `i`'s word for one more place: the first takes the reference it was made with.
    let mut take = |heap: &mut Heap, words: &[Word], i: usize| -> Result<Word, String> {
        if std::mem::replace(&mut used[i], true) {
            heap.inc(words[i])?;
        }
        Ok(words[i])
    };
    for node in m.nodes {
        let w = match node {
            MadeNode::Data(v) => s.heap.fresh(&v)?,
            // The kernel makes a primitive value from a term's `PrimFn` only, and every such
            // term comes from a primitive node of the program or a word of the table.
            MadeNode::Prim(p) => match t.prims.iter().position(|q| *q == p) {
                Some(i) => Word {
                    tag: Word::PRIM,
                    bits: i as i64,
                },
                None => {
                    return Err(zed_rt::bug(
                        "was given back a primitive it has no word for",
                        &format!("primitive {p:?} is not in the program's table"),
                    ));
                }
            },
            // As a primitive: a port the kernel reads is one of the program's `Read` nodes.
            MadeNode::Source(p) => match t.port_at.get(&p) {
                Some(&i) => Word {
                    tag: Word::SOURCE,
                    bits: i as i64,
                },
                None => {
                    return Err(zed_rt::bug(
                        "was given back a port it has no word for",
                        &format!("port `{p}` is not in the program's table"),
                    ));
                }
            },
            MadeNode::Fun(f) => {
                let mut caps = Vec::with_capacity(f.caps.len());
                let mut names = Vec::with_capacity(f.caps.len());
                for (x, i) in f.caps {
                    caps.push(take(&mut s.heap, &words, i)?);
                    names.push(x);
                }
                s.heap.alloc(Obj::Fun(Box::new(FunObj {
                    params: f.params,
                    body: f.body,
                    names,
                    caps: caps.into(),
                    placed: f.placed,
                })))
            }
            MadeNode::Held(shape, parts) => {
                let mut ps = Vec::with_capacity(parts.len());
                for i in parts {
                    ps.push(take(&mut s.heap, &words, i)?);
                }
                let shape = match shape {
                    MadeShape::Tuple => HeldShape::Tuple,
                    MadeShape::Atom(n, f) => HeldShape::Atom(n, f),
                    MadeShape::Family(f) => HeldShape::Family(Box::new(f)),
                };
                s.heap.alloc(Obj::Held(Box::new(HeldObj {
                    shape,
                    parts: ps.into(),
                })))
            }
        };
        words.push(w);
    }
    Ok(*words.last().expect("a value has a node"))
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
    let q = kernel_term(t, s, ni, ins)?;
    run(s, &q)
}

/// The closed term the kernel runs node `ni` alone on `ins` by.
fn kernel_term(t: &Tables, s: &mut Run, ni: &NodeInfo, ins: &[Word]) -> Result<Term, String> {
    let mut lets = Lets::default();
    let mut terms = Vec::with_capacity(ins.len());
    for w in ins {
        terms.push(term(t, s, *w, &mut lets)?);
    }
    let q = raise_node(ni.node(), ni.number, &t.swapped, &terms)?;
    Ok(wrap(lets, q))
}

fn run(s: &mut Run, q: &Term) -> Result<Value, String> {
    s.kernel_calls += 1;
    s.ev.run(q).map_err(|e| e.to_string())
}

/// The kernel term for word `w`; a lookup port is read once, by a `let` in `lets`, and each
/// closure's and held value's term is built once, in `lets.closures`. A held value is a
/// variable bound in `lets.held` to the tuple, atom or display primitive on its parts' terms,
/// as the machine builds it (`held_term`), so the term is good only inside [`wrap`].
fn term(t: &Tables, s: &mut Run, w: Word, lets: &mut Lets) -> Result<Term, String> {
    // Closures capture closures, and held values hold them, as deep as a program builds them,
    // so the values in progress are on a stack, each with the terms of its parts so far.
    let mut stack: Vec<(Word, Vec<HeldPart>)> = Vec::new();
    let mut made = term_of(t, s, w, lets, &mut stack)?;
    loop {
        let Some((clo, terms)) = stack.last_mut() else {
            return Ok((made.expect("an empty stack follows a finished term")).into_term());
        };
        terms.extend(made.take());
        let caps = match s.heap.obj(*clo)? {
            Some(Obj::Clo { caps, .. }) => &**caps,
            Some(Obj::Fun(f)) => &*f.caps,
            Some(Obj::Held(h)) => &*h.parts,
            _ => unreachable!("only closures and held values are entered"),
        };
        match caps.get(terms.len()) {
            Some(&c) => made = term_of(t, s, c, lets, &mut stack)?,
            None => {
                let q = match s.heap.obj(*clo)? {
                    Some(Obj::Clo { lambda, placed, .. }) => {
                        let ni = &t.nodes[t.lambdas[*lambda].node];
                        let mut caps = HeldPart::terms(std::mem::take(terms));
                        // A closure a `place` made ([`placed_clo`]): `place(table, f, fill)`,
                        // the fill its last capture, as the kernel's `placed_fun_term` gives it.
                        let placed = placed.map(|p| &t.placings[p as usize]);
                        let fill = placed.and_then(|p| if p.fill { caps.pop() } else { None });
                        let f = raise_node(ni.node(), ni.number, &t.swapped, &caps)?;
                        HeldPart::closure(match placed {
                            None => f,
                            Some(p) => {
                                let mut args = vec![Term::Lit(p.table.clone()), f];
                                args.extend(fill);
                                Term::Prim(Prim::Place, args)
                            }
                        })?
                    }
                    // A closure the kernel made: its lambda with its captures bound inside,
                    // as a closure the program made is raised (`raise_node`'s `Caps::Given`).
                    Some(Obj::Fun(f)) => HeldPart::closure(placed_fun_term(
                        &f.params,
                        &f.body,
                        &f.names,
                        HeldPart::terms(std::mem::take(terms)),
                        f.placed.as_ref(),
                    ))?,
                    _ => {
                        let h = s.heap.held(*clo)?.expect("a held value");
                        let (key, parts) = (clo.bits as u64, std::mem::take(terms));
                        let made = match &h.shape {
                            HeldShape::Tuple => held_term(None, key, parts),
                            HeldShape::Atom(n, f) => held_term(Some((n, f)), key, parts),
                            HeldShape::Family(f) => held_family_term(f, key, parts),
                        };
                        let (x, part) = HeldPart::held(key);
                        lets.held.push((x, made));
                        part
                    }
                };
                let (clo, _) = stack.pop().expect("the closure finished");
                lets.closures.insert(clo.bits, q.clone());
                made = Some(q);
            }
        }
    }
}

/// The term of `w` when it is not a closure or held value or is one whose term is built; any
/// other is entered on `stack`.
fn term_of(
    t: &Tables,
    s: &mut Run,
    w: Word,
    lets: &mut Lets,
    stack: &mut Vec<(Word, Vec<HeldPart>)>,
) -> Result<Option<HeldPart>, String> {
    Ok(Some(match w.tag {
        Word::PRIM => HeldPart::prim(t.prims[w.bits as usize]),
        Word::STATE => HeldPart::data(Value::tuple(Vec::new())),
        Word::SOURCE => {
            let p = t.ports[w.bits as usize].clone();
            if lets.seen.insert(p.clone()) {
                lets.order.push(p.clone());
            }
            HeldPart::port(&p)
        }
        Word::CELL if s.heap.holds_function(w)? => match lets.closures.get(&w.bits) {
            Some(q) => q.clone(),
            None => {
                stack.push((w, Vec::new()));
                return Ok(None);
            }
        },
        _ => HeldPart::data(s.heap.value(w)?),
    }))
}

/// `t` with each held value in `lets` made first, each before the ones that hold it, and each
/// lookup port read before them all, as the memory machine wraps its terms
/// ([`zedc::zir::memory::wrap`]).
fn wrap(lets: Lets, t: Term) -> Term {
    zedc::zir::memory::wrap(lets.order, lets.held, t)
}

/// The lookup ports a kernel term reads, each once, in the order first met, and the term of
/// each closure and held value it holds.
#[derive(Default)]
struct Lets {
    seen: HashSet<Arc<str>>,
    order: Vec<Arc<str>>,
    /// The term of each closure and held value met, by its cell word's bits: a closure
    /// captured on many paths is built once, so the term is a graph the size of the closures,
    /// not a tree of every path (COMPLEXITY.md R9). No cell is freed while a term is built, so
    /// each word names one value. A closure's term is a lambda whose body is shared, so a copy
    /// costs its parameter names; a held value's is the variable `held` binds it to.
    // Complexity tradeoff: the naive build walks a closure once per path to it, 2^d for d
    // levels each capturing the level below twice (R9: 4 times per 2 levels, 17.6 s at 20).
    // Here each closure's term is built once per kernel call and kept by its cell word (index
    // and generation, so a cell freed and taken again is a new key), and every later use is a
    // copy sharing the body: O(closures + captures). Tradeoff: one map entry per closure for
    // the call. Nothing is refused. Tests `l01_36_cranelift::shared_closures`.
    closures: HashMap<i64, HeldPart>,
    /// Each held value met, a variable and the term that makes it, in the order finished, so
    /// a value's parts come before it; [`wrap`] binds each once, outside the node's term.
    // Complexity tradeoff: the naive term puts the making of a held value where the node uses
    // it, and the node's term may run that place once per entry: a `map` over a held family of
    // n functions made the family again for each entry, O(n²) (row FAIL-family-function-entry,
    // 0.25 s at 500 entries, 14 s at 4000). Here each is made once per kernel call, O(parts),
    // and each use reads a variable. Tradeoff: a held value on a path the node does not take
    // is made anyway, O(its parts), no more than building its term cost. Test `l03_02_map_run::
    // bench::a_display_of_functions_read_and_applied_runs_in_linear_time`.
    //
    // Proof that making a held value early cannot fail, refuse, read a port, run a function or
    // change the result (row PROOF-native-held-early-build; author P246). Each entry is
    // `let \0held k = P(a…) in \0held k` (`held_term`, `held_family_term`), P being `Tuple`,
    // `Atom` or `Entries`, and each argument `a` a literal the builder adds (an atom's name and
    // field names, a display's key or data entry) or a `HeldPart`, the only type those take
    // for a part. Its field is private, so a part is one of the five kinds its constructors
    // make (row PROOF-early-build-input-kinds):
    //  1. `HeldPart::data`, a literal;
    //  2. `HeldPart::prim`, `PrimFn`, a primitive used as a value;
    //  3. `HeldPart::port`, `\0port p`, bound by `wrap`'s outer lets. `term_of` adds that let
    //     whenever a source is met, held or not, and the same let was there when held values
    //     were made at their uses, so making a value early adds no read;
    //  4. `HeldPart::held`, `\0cell j`, an earlier entry: `term` finishes a part before its
    //     holder and pushes it first, and `wrap` binds earlier entries outside later ones;
    //  5. `HeldPart::closure`, a closure's term, which it checks is a `Term::Lam` (or `let x =
    //     <lambda> in x`, the form ZIR's memory machine gives) and refuses otherwise, stopping
    //     the run before the value is made. Here it is given `raise_node` of a lambda node
    //     (lower.rs `Op::Lambda => Term::Lam`, its captures placed inside the body) or
    //     `fun_term` (its application of the captures inside its lambda), so the check passes
    //     today; a later path that gives it anything else is refused, not run (test
    //     `hooks::tests::the_term_of_a_closure_a_held_value_holds_is_checked_to_run_no_code`).
    //     Evaluating a lambda makes a closure and calls nothing.
    // So evaluating the arguments runs no function, reads no port and cannot stop. Then P, in
    // the kernel (eval.rs, the held rules beside `Prim::Tuple`):
    //  - `Tuple` takes any arguments.
    //  - `Atom` gets the name and the field names of an atom that exists, sorted and distinct
    //    as `prim_data` stored them, and one part per field in that order. `prim_data` accepted
    //    those when the atom was first made, and it decides on them alone, so it accepts them
    //    again and puts each part back at its place.
    //  - `Entries` gets the top-level keys of an existing `HeldFamily`, from `HeldFamily::iter`:
    //    distinct, in key order, each already its own key. `HeldFamily::new` then gives
    //    `from_leaves` one keypath of length one per key, so there is no empty keypath and no
    //    key twice. A data entry that is a family is placed beneath its key exactly as it lies
    //    in `all`. At least one entry is a part, so `new` gives `Some`.
    // The kernel's other refusals do not apply: the evaluators native code and the machine run
    // are made by `Evaluator::new`, with no fuel limit (value.rs at `burn`), and P runs no step
    // that could be refused. The value made equals the one in the cell: same shape, same parts
    // in the same order, and a kernel value is pure. A use reads the variable, which is the
    // value the inline making gave. `\0` cannot be written in source, so no program name is
    // shadowed. The names are keys of live cells: a closure that captured `\0cell k` keeps
    // that cell alive, so the key cannot name another value in a later call.
    // Tests in `l01_36_cranelift::held_values`: `a_held_value_read_only_on_an_untaken_branch_
    // is_made_without_stopping`, `a_held_value_whose_parts_have_no_other_holder_is_made_for_its_
    // last_use`, `closures_a_kernel_call_made_read_their_own_held_values_in_a_later_call` and
    // `a_held_tuple_at_each_key_of_a_family_is_one_cell`.
    held: Vec<(Arc<str>, Term)>,
}

/// An `if` or `match` whose decision is failure value `v`: the owned inputs are dropped and
/// the value is pending as the node's result.
fn failed(s: &mut Run, ni: &NodeInfo, ins: &[Word], v: Value) -> Result<(), String> {
    consume(s, ni, ins)?;
    s.pending = s.heap.fresh(&v)?;
    Ok(())
}

/// An `if` whose condition is not a boolean word: the kernel decides. Returns the arm, or 2
/// for a failure.
fn branch(t: &Tables, s: &mut Run, id: usize, ins: &[Word]) -> Result<i64, String> {
    let ni = &t.nodes[id];
    if ins[0].tag == Word::BOOL {
        return Ok(i64::from(ins[0].bits == 0));
    }
    // An atom that holds a function passes through an `if` as any failure does, as the
    // machine passes it.
    if s.heap.is_held_atom(ins[0])? {
        s.heap.inc(ins[0])?;
        consume(s, ni, ins)?;
        s.pending = ins[0];
        return Ok(2);
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
    let mut paths = Paths::default();
    if !function {
        for (i, p) in ps.iter().enumerate() {
            let mut out = Vec::new();
            paths.clear();
            if s.heap.matches(p, scrut, &mut paths, &mut out)? {
                found = Some((i, out));
                break;
            }
        }
    }
    let (i, binders): (usize, Binders) = match found {
        Some(f) => f,
        None => match kernel_match(t, s, ps, scrut)? {
            Ok((i, n)) => {
                if !function {
                    return Err(zed_rt::bug(
                        "matched a value against the patterns of a `match` and found no arm, where the \
                         program's own semantics pick one",
                        &format!(
                            "{}: no pattern matches natively, and the kernel picks arm {i}",
                            t.path(id)
                        ),
                    ));
                }
                // A pattern that matches a function binds it whole or not at all (data holds
                // no function), so each binder is the scrutinee, at the empty path.
                (i, vec![(scrut, Paths::ROOT); n])
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
        if t.fuse {
            let kept_nodes: Vec<usize> = kept.iter().map(|b| binders[*b].1).collect();
            s.heap.release(scrut, &paths, &kept_nodes)?;
        } else {
            for b in &kept {
                s.heap.inc(binders[*b].0)?;
            }
            s.heap.dec(scrut)?;
        }
    } else {
        for (b, (w, _)) in binders.iter().enumerate() {
            if arm[b] == Mode::Owned {
                return Err(zed_rt::bug(
                    "took ownership of a part of a value that the `match` only borrows",
                    &format!(
                        "{}: the scrutinee is borrowed, and arm {i} owns binder {b}",
                        t.path(id)
                    ),
                ));
            }
            words.push(*w);
        }
    }
    s.outs = words;
    Ok(i as i64)
}

/// The kernel's decision on a scrutinee native matching does not decide: the arm and its
/// number of binders, or the failure value. The binders' values are not asked for: a function
/// scrutinee is no data, so the kernel could not give it back in a tuple, and a data
/// scrutinee that native matching does not match matches no arm.
fn kernel_match(t: &Tables, s: &mut Run, ps: &[Pattern], scrut: Word) -> Result<Decision, String> {
    let mut lets = Lets::default();
    let st = term(t, s, scrut, &mut lets)?;
    let mut arms = Vec::new();
    let mut counts = Vec::new();
    for (i, p) in ps.iter().enumerate() {
        let mut p = p.clone();
        let mut n = 0;
        p.rename_binders(|x| {
            n += 1;
            *x = format!("\0bind{n}").into()
        });
        counts.push(n);
        arms.push((
            p,
            Term::Prim(Prim::Tuple, vec![Term::Lit(Value::Int(i as i64))]),
        ));
    }
    let q = wrap(lets, Term::Match(Shared::new(st), arms));
    Ok(match run(s, &q)? {
        Value::Tuple(xs) => match xs.first() {
            Some(&Value::Int(i)) if xs.len() == 1 && (i as usize) < ps.len() => {
                Ok((i as usize, counts[i as usize]))
            }
            _ => Err(Value::Tuple(xs)),
        },
        v => Err(v),
    })
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
        if RECORD.with(|r| r.get()) {
            c.released.push(s.heap.released());
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
    /// For each run, once [`record_releases`] has asked for them, the cells it freed in the
    /// order it freed them, the result's last.
    pub released: Vec<Vec<zed_rt::Released>>,
}

#[cfg(feature = "counts")]
thread_local! {
    static COUNTED: RefCell<Counted> = RefCell::new(Counted::default());
    static RECORD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the native runs this thread starts from now on record the cells they free, in
/// order, for [`Counted::released`] (feature `counts`). Off by default, so other runs keep
/// nothing per free.
#[cfg(feature = "counts")]
pub fn record_releases(on: bool) {
    RECORD.with(|r| r.set(on));
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
        return Err(zed_rt::bug(
            "failed and recorded no reason",
            "the result is the error word, and no message was recorded",
        ));
    }
    let function = s.heap.is_function(w)?;
    let held = s.heap.held(w)?.is_some();
    let v = if function || held {
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
        return Err(zed_rt::bug(
            "kept values in memory that nothing uses after the program's result was made",
            &format!(
                "{} live after the result is dropped{which}",
                prose::counted(n, "cell")
            ),
        ));
    }
    v.ok_or_else(|| {
        let what = if held { "holds" } else { "is" };
        KernelError::Type(format!("the program's result {what} a function")).to_string()
    })
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod completeness;

#[cfg(test)]
mod tests {
    use std::mem::ManuallyDrop;

    use zed_kernel::World;
    use zed_kernel::term::build::{app, if_, lam, lit, var};
    use zedc::zir::lower::lower;
    use zedc::zir::memory::{cell_var, plan, port_var};

    use super::*;

    /// Builds `depth` closures of `(x) -> (y) -> x`'s inner lambda, each capturing the one
    /// below and the bottom one 7, makes the chain a term, and checks that the term is `depth`
    /// lambdas around `7`. `bench` runs it at a depth that overflowed the default test stack
    /// when `term` recursed; the test here at a small one.
    pub(super) fn a_chain_of_closures_of_depth_becomes_a_term(depth: usize) {
        // `(x) -> (y) -> x`, whose inner lambda captures one value.
        let g = crate::legal::legalize(lower(&lam(&["x"], lam(&["y"], var("x")))).unwrap());
        let (t, _) = Tables::new(&g, &plan(g.graph(), false)).unwrap();
        let captures = |l: &&crate::tables::LambdaInfo| !t.nodes[l.node].node().inputs.is_empty();
        let inner = t.lambdas.iter().position(|l| captures(&l)).unwrap();
        let mut s = State::new(Arc::new(t), Evaluator::new(World::new()));
        let mut w = Word::int(7);
        for _ in 0..depth {
            w = s.run.heap.alloc(Obj::Clo {
                lambda: inner,
                caps: vec![w].into(),
                placed: None,
            });
        }
        // The kernel's terms drop by recursion, so this one is left to the end of the process.
        let made = ManuallyDrop::new(term(&s.t, &mut s.run, w, &mut Lets::default()).unwrap());
        let (mut at, mut levels) = (&*made, 0);
        while let Term::Lam(_, body) = at {
            (at, levels) = (&**body, levels + 1);
        }
        assert_eq!(levels, depth);
        assert_eq!(at.to_string(), "7");
    }

    #[test]
    fn a_chain_of_closures_becomes_a_term() {
        a_chain_of_closures_of_depth_becomes_a_term(3);
    }

    #[test]
    fn a_closure_with_no_closure_below_becomes_a_term() {
        a_chain_of_closures_of_depth_becomes_a_term(1);
    }

    /// A held value is made before the node that uses it (`Lets::held`), so the term of a
    /// closure it holds must make a closure and run nothing. Every term `term` builds for a
    /// closure passes the check, and one that would run code, read a port or read a name of
    /// another value is refused with the check's message (row PROOF-early-build-input-kinds).
    #[test]
    fn the_term_of_a_closure_a_held_value_holds_is_checked_to_run_no_code() {
        let (mut s, inner) = two_captures();
        let w = s.run.heap.alloc(Obj::Clo {
            lambda: inner,
            caps: vec![Word::int(1), Word::int(2)].into(),
            placed: None,
        });
        let made = term(&s.t, &mut s.run, w, &mut Lets::default()).unwrap();
        assert!(matches!(made, Term::Lam(..)));
        assert!(HeldPart::closure(made.clone()).is_ok());
        let x: Arc<str> = "x".into();
        let bound = |e: Term, b: Term| Term::Let(x.clone(), Shared::new(e), Shared::new(b));
        assert!(HeldPart::closure(bound(made.clone(), var("x"))).is_ok());
        let call = app(lam(&["y"], var("y")), vec![lit(1i64)]);
        for runs in [
            call.clone(),
            bound(call, var("x")),
            bound(made.clone(), var("z")),
            Term::Read("m.stdin".into()),
            app(made, vec![lit(1i64), lit(2i64)]),
        ] {
            let shown = runs.to_string();
            assert_eq!(
                HeldPart::closure(runs).err(),
                Some(format!(
                    "zedc made the term of a closure as `{shown}`, which is not a lambda. A \
                     value that holds the closure is made before the code that uses it, so \
                     making it from this term could run code the program does not run there. \
                     This is a fault of zedc, not of the program; the run stops here instead."
                ))
            );
        }
    }

    /// `HeldPart::terms` gives the terms in the memory the parts were in: no second vector
    /// (PERF-held-part-collect-alloc). The standard library's collect of a map over a vector's
    /// own iterator reuses that memory for items of equal size and alignment, which it does
    /// but does not promise; this fails if a new compiler stops doing it.
    #[test]
    fn the_terms_of_held_parts_are_made_in_the_parts_own_vector() {
        let parts = vec![
            HeldPart::data(Value::Int(1)),
            HeldPart::held(7).1,
            HeldPart::port("p"),
        ];
        let (at, room) = (parts.as_ptr() as usize, parts.capacity());
        let terms = HeldPart::terms(parts);
        assert_eq!((terms.as_ptr() as usize, terms.capacity()), (at, room));
        assert_eq!(
            terms,
            [
                Term::Lit(Value::Int(1)),
                Term::Var(cell_var(7)),
                Term::Var(port_var("p"))
            ]
        );
    }

    /// The part of a held value and the `let` that binds the value share one name, made once
    /// (PERF-held-part-collect-alloc: two names cost two more allocations per held value).
    #[test]
    fn a_held_part_and_its_let_share_one_name() {
        let (x, part) = HeldPart::held(7);
        assert_eq!(&*x, &*cell_var(7));
        let term = part.into_term();
        let Term::Var(y) = &term else {
            panic!("a held part is a variable")
        };
        assert!(Arc::ptr_eq(&x, y));
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
                caps: vec![w, w].into(),
                placed: None,
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
            caps: vec![Word::int(a), Word::int(b)].into(),
            placed: None,
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

    const SHARED_AFTER_FREE: &str =
        "the heap's cell 0 was given a new reference after it was freed";

    #[test]
    fn an_inc_that_fails_as_the_last_write_ends_the_run_with_its_error() {
        let (old, new) = with_a_freed_cell();
        // The result is dropped first; the failing `inc` is the run's last write, and the run
        // ends with no result word, so `finish` drops nothing.
        rt_dec(new.tag, new.bits);
        rt_inc(old.tag, old.bits);
        let mut s = remove();
        let e = finish(&s.t, &mut s.run, Word::err()).unwrap_err();
        assert!(e.contains(SHARED_AFTER_FREE), "{e}");
    }

    #[test]
    fn an_inc_that_fails_before_a_dec_is_the_error_and_the_dec_still_drops() {
        let (old, new) = with_a_freed_cell();
        rt_inc(old.tag, old.bits);
        rt_dec(new.tag, new.bits);
        let mut s = remove();
        assert_eq!(s.run.heap.live(), 0, "the drop was written");
        let e = finish(&s.t, &mut s.run, Word::int(0)).unwrap_err();
        assert!(e.contains(SHARED_AFTER_FREE), "{e}");
    }

    /// Renames the binders of `pair { a: a, b: ((…(c)…)) }`, with `c` under `depth` tuples, and
    /// checks that they are renamed in preorder, `a` to `v1` and `c` to `v2`. `bench` runs it at
    /// a depth that overflowed the default test stack when this file's `rename` recursed (now
    /// `Pattern::rename_binders`); the test here at a small one.
    pub(super) fn binders_of_a_pattern_of_depth_are_renamed_in_preorder(depth: usize) {
        let bind = |x: &str| Pattern::Bind(x.into());
        let inner = (0..depth).fold(bind("c"), |p, _| Pattern::Tuple(vec![p]));
        let mut p = ManuallyDrop::new(Pattern::Fields(
            "pair".into(),
            vec![("a".into(), bind("a")), ("b".into(), inner)],
        ));
        let mut n = 0;
        p.rename_binders(|x| {
            n += 1;
            *x = format!("v{n}").into()
        });
        assert_eq!(n, 2);
        let Pattern::Fields(_, fs) = &*p else {
            unreachable!()
        };
        assert!(matches!(&fs[0].1, Pattern::Bind(x) if &**x == "v1"));
        let (mut at, mut levels) = (&fs[1].1, 0);
        while let Pattern::Tuple(ps) = at {
            (at, levels) = (&ps[0], levels + 1);
        }
        assert_eq!(levels, depth);
        assert!(matches!(at, Pattern::Bind(x) if &**x == "v2"));
    }

    #[test]
    fn binders_of_a_nested_pattern_are_renamed_in_preorder() {
        binders_of_a_pattern_of_depth_are_renamed_in_preorder(3);
    }

    /// P188: `_`, a literal and `#_` bind nothing and are left as they are, and the binders
    /// inside an atom pattern are renamed in order, as those of a tuple are.
    #[test]
    fn patterns_that_bind_nothing_are_kept_and_atom_payloads_are_renamed() {
        let bind = |x: &str| Pattern::Bind(x.into());
        let mut p = Pattern::Tuple(vec![
            Pattern::Wild,
            Pattern::Atom(
                "ok".into(),
                vec![bind("a"), Pattern::Lit(Value::Int(1)), bind("b")],
            ),
            Pattern::AnyAtom,
            bind("c"),
        ]);
        let mut n = 0;
        p.rename_binders(|x| {
            n += 1;
            *x = format!("v{n}").into()
        });
        assert_eq!(n, 3);
        let Pattern::Tuple(ps) = &p else {
            unreachable!()
        };
        assert!(matches!(ps[0], Pattern::Wild));
        let Pattern::Atom(name, qs) = &ps[1] else {
            unreachable!()
        };
        assert_eq!(&**name, "ok");
        assert!(matches!(&qs[0], Pattern::Bind(x) if &**x == "v1"));
        assert!(matches!(&qs[1], Pattern::Lit(Value::Int(1))));
        assert!(matches!(&qs[2], Pattern::Bind(x) if &**x == "v2"));
        assert!(matches!(ps[2], Pattern::AnyAtom));
        assert!(matches!(&ps[3], Pattern::Bind(x) if &**x == "v3"));
    }
}
