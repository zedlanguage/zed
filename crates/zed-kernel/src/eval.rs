//! The reference evaluator of the kernel calculus (step M0.9).
//!
//! The evaluator is strict and big-step: a term reduces to a value, arguments left to right.
//! It is written for clarity, not speed; every back end is tested against it. The choices
//! the spec leaves to the reference semantics are recorded in DESIGN.md sec:kernel,
//! "Reference semantics", and repeated on the item they govern here.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use crate::error::KernelError;
use crate::exact::{canonical_tree, exact_sum};
use crate::family::{Family, Keypath};
use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{Euclid, Signed, Zero};

use crate::num::MAX_BITS;
use crate::provenance::{Fact, FactAddress, NodeAddress, Provenance, children, unshare};
use crate::term::{FixKind, GuardPos, Pattern, Prim, Term};
use crate::value::Value;

/// The minimum resource limits of compile-time evaluation (DESIGN.md sec:verification,
/// "Budgets"; fixed by step M0.11). A conforming compiler never rejects an evaluation within
/// them; past them, running out is a build failure, the machine's and not the program's.
///
/// Steps of the definitional interpreter, counted as [`DEFAULT_FUEL`] counts them.
pub const MIN_STEPS: u64 = 10_000_000;
/// Bytes of memory. The reference evaluator sets no memory limit of its own, so it is bounded
/// only by the machine.
pub const MIN_MEMORY: u64 = 1 << 30;
/// Nested calls.
pub const MIN_NESTED_CALLS: usize = 20_000;

/// The default fuel: the number of function calls, `fix` rounds and `gen` steps one
/// evaluation may take, ten times [`MIN_STEPS`].
pub const DEFAULT_FUEL: u64 = 100_000_000;

/// The deepest nesting of calls the evaluator follows before it stops with
/// [`KernelError::TooDeep`]. A program that needs more is one the reference evaluator cannot
/// run, not a wrong program.
pub const MAX_DEPTH: usize = 20_000;

/// The stack reserved for one evaluation, 1 GiB, of which the system commits only the pages
/// a run touches. A debug build uses 10 to 20 KB per nested call (a 2 MB stack held 100
/// nested calls and not 200), so [`MAX_DEPTH`] calls need at most 400 MB.
const STACK_BYTES: usize = 1 << 30;

const _: () = assert!(DEFAULT_FUEL >= MIN_STEPS && MAX_DEPTH >= MIN_NESTED_CALLS);

/// A run-time value: a data value, or a function, which families never hold.
#[derive(Clone, Debug)]
pub enum V {
    /// Data.
    Data(Value),
    /// A lambda with its captured environment.
    Closure(Rc<Closure>),
    /// A primitive used as a function.
    Prim(Prim),
    /// The partial family a definedness `fix` is building, as its body sees it.
    Partial(Rc<Partial>),
    /// An input port read by lookup, such as a `Files` port: the port's name.
    Source(Arc<str>),
}

/// A lambda with its environment.
#[derive(Debug)]
pub struct Closure {
    params: Vec<Arc<str>>,
    body: Arc<Term>,
    env: Env,
}

/// The family a definedness `fix` has defined so far, over its whole domain.
#[derive(Debug)]
pub struct Partial {
    /// Which `fix` evaluation this family belongs to, so that a read of an undefined entry
    /// postpones the entry of that `fix` and not of a `fix` nested inside its body.
    fix: u64,
    domain: Rc<BTreeSet<Value>>,
    defined: Rc<RefCell<Defined>>,
    /// The attempt sees the entries defined in rounds before this one.
    round: u64,
}

/// The entries a definedness `fix` has defined, each with the round that defined it. Every
/// attempt shares the one map, so an attempt costs nothing for the entries it does not read.
type Defined = BTreeMap<Value, (Value, u64)>;

#[derive(Debug)]
struct Frame {
    name: Arc<str>,
    value: V,
    /// The fact the value came from, when provenance is recorded and it came from one.
    fact: Option<usize>,
    next: Env,
}

type Env = Option<Rc<Frame>>;

fn bind(env: &Env, name: Arc<str>, value: V) -> Env {
    bind_fact(env, name, value, None)
}

fn bind_fact(env: &Env, name: Arc<str>, value: V, fact: Option<usize>) -> Env {
    Some(Rc::new(Frame {
        name,
        value,
        fact,
        next: env.clone(),
    }))
}

fn lookup_fact(env: &Env, name: &str) -> Option<usize> {
    let mut cur = env;
    while let Some(frame) = cur {
        if &*frame.name == name {
            return frame.fact;
        }
        cur = &frame.next;
    }
    None
}

fn lookup(env: &Env, name: &str) -> Option<V> {
    let mut cur = env;
    while let Some(frame) = cur {
        if &*frame.name == name {
            return Some(frame.value.clone());
        }
        cur = &frame.next;
    }
    None
}

/// Why an evaluation stopped: an error, or, inside a definedness `fix`, a read of an entry
/// not yet defined, which postpones the entry being computed. The read names the `fix` whose
/// family it read and the key it read there.
enum Stop {
    Error(KernelError),
    Undefined { fix: u64, key: Value },
}

/// The order in which a definedness `fix` defines its entries. Every schedule reaches the
/// same family, or stalls on the same keys, which step M0.10 checks; the reference is
/// [`Schedule::Rounds`], and the others exist to be checked against it.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Schedule {
    /// Jacobi rounds, the wavefront: each round evaluates every undefined entry against the
    /// family as the round began.
    #[default]
    Rounds,
    /// Chaotic iteration: each round tries the undefined entries in an order drawn from the
    /// seed, and an entry defined in a round is visible to the entries after it.
    Chaotic(u64),
    /// Memoized demand: the entries are demanded in key order, and a read of an undefined
    /// entry evaluates that entry first. A read of an entry already being demanded is a
    /// cycle, and every entry waiting on it stalls.
    Pull,
}

impl From<KernelError> for Stop {
    fn from(e: KernelError) -> Self {
        Stop::Error(e)
    }
}

type R<T> = Result<T, Stop>;

fn type_err<T>(msg: impl Into<String>) -> R<T> {
    Err(Stop::Error(KernelError::Type(msg.into())))
}

/// One output port of a [`World`].
#[derive(Clone, Debug, Default)]
pub struct Output {
    /// The values pushed, in the order the evaluation made the pushes.
    pub log: Vec<Value>,
    /// How many values the port accepts before a push returns `#full`; `None` is unbounded.
    pub capacity: Option<usize>,
}

/// An input port read by lookup (step L1.19): a `Files` port is `Path ->? String | #ioError`,
/// a partial map too large to hold whole, so the world answers each key when it is read.
pub trait Lookup: std::fmt::Debug + Send + Sync {
    /// The value at `key`, or why the port could not answer, which stops the wave.
    fn get(&self, key: &Value) -> Result<Value, String>;
}

/// The ports a program runs against: one wave of inputs, and the outputs it writes
/// (sec:ports). Each input port holds its whole value for the wave; a lookup port answers
/// each key once, and the answers are kept, so the wave sees one value at each key.
#[derive(Clone, Debug, Default)]
pub struct World {
    /// The input ports by name.
    pub inputs: BTreeMap<String, Value>,
    /// The output ports by name.
    pub outputs: BTreeMap<String, Output>,
    /// The lookup ports by name.
    pub sources: BTreeMap<String, Arc<dyn Lookup>>,
    /// The keys read from each lookup port and the values read there, in key order: what a
    /// replay of the wave must supply.
    pub reads: BTreeMap<String, BTreeMap<Value, Value>>,
}

impl World {
    /// A world with no ports.
    pub fn new() -> Self {
        World::default()
    }

    /// Adds an input port holding `value`.
    pub fn input(mut self, name: &str, value: impl Into<Value>) -> Self {
        self.inputs.insert(name.into(), value.into());
        self
    }

    /// Adds a lookup port.
    pub fn source(mut self, name: &str, port: Arc<dyn Lookup>) -> Self {
        self.sources.insert(name.into(), port);
        self
    }

    /// Adds an unbounded output port.
    pub fn output(mut self, name: &str) -> Self {
        self.outputs.insert(name.into(), Output::default());
        self
    }

    /// Adds an output port that accepts `capacity` values.
    pub fn bounded_output(mut self, name: &str, capacity: usize) -> Self {
        self.outputs.insert(
            name.into(),
            Output {
                log: Vec::new(),
                capacity: Some(capacity),
            },
        );
        self
    }

    /// The values pushed to output `name`.
    pub fn log(&self, name: &str) -> &[Value] {
        &self.outputs[name].log
    }
}

/// What a run records for its provenance (step L1.20).
#[derive(Debug, Default)]
struct Trace {
    /// The preorder position of each node of the evaluated term, by the node's address in
    /// memory, which is used during the run only and never enters a fact address.
    positions: HashMap<usize, u32>,
    term: Option<Term>,
    facts: Vec<Fact>,
    /// The positions of the call sites the run is inside.
    calls: Vec<u32>,
    /// The keypath of the region instance the run is inside.
    keys: Vec<Value>,
    /// The facts read so far by the node being evaluated, one entry per subterm evaluated,
    /// `None` for a value that came from no fact, such as a family key.
    reads: Vec<Option<usize>>,
    /// The call site and the facts of the arguments of the next closure call.
    site: Option<u32>,
    args: Vec<Option<usize>>,
}

/// The reference evaluator, holding the world and the remaining fuel.
pub struct Evaluator {
    /// The ports.
    pub world: World,
    fuel: u64,
    depth: usize,
    /// Above zero while evaluating the closure of a pure region (`fam`, `reindex`,
    /// `discard`, `fold`, `fix`), where a port operation is a type error.
    pure: usize,
    schedule: Schedule,
    /// The number of definedness `fix` evaluations begun, which names each one's family.
    fixes: u64,
    trace: Option<Trace>,
}

/// Proof that the current thread is one [`on_stack`] started, whose stack holds [`MAX_DEPTH`]
/// nested calls. It cannot be made elsewhere or passed to another thread.
pub struct Stack(std::marker::PhantomData<*const ()>);

thread_local! {
    /// Whether this thread is one [`on_stack`] started.
    static EVALUATION_THREAD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Whether an evaluation is running on this thread, so that its stack is in use.
    static EVALUATING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `f` with a stack that holds [`MAX_DEPTH`] nested calls, passing it the [`Stack`] that
/// [`Evaluator::run_on`] asks for: on the current thread when it is an evaluation thread with
/// no evaluation running, else on a new one. Starting a thread reserves 1 GiB of address
/// space and costs tens of microseconds, so a caller that evaluates many terms calls this
/// once around all of them.
pub fn on_stack<R: Send>(f: impl FnOnce(&Stack) -> R + Send) -> R {
    if EVALUATION_THREAD.get() && !EVALUATING.get() {
        return f(&Stack(std::marker::PhantomData));
    }
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .stack_size(STACK_BYTES)
            .spawn_scoped(scope, || {
                EVALUATION_THREAD.set(true);
                f(&Stack(std::marker::PhantomData))
            });
        match worker.expect("the evaluator thread starts").join() {
            Ok(out) => out,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    })
}

/// Evaluates a closed term with no ports and the default fuel, expecting data.
pub fn eval(term: &Term) -> Result<Value, KernelError> {
    Evaluator::new(World::new()).run(term)
}

impl Evaluator {
    /// An evaluator over `world` with the default fuel.
    pub fn new(world: World) -> Self {
        Evaluator {
            world,
            fuel: DEFAULT_FUEL,
            depth: 0,
            pure: 0,
            schedule: Schedule::default(),
            fixes: 0,
            trace: None,
        }
    }

    /// Records the provenance of the next run (step L1.20), which
    /// [`Evaluator::provenance`] then returns. Every keypath begins with `root`, the wave
    /// stamp of a port region's wave, or nothing.
    pub fn with_provenance(mut self, root: Vec<Value>) -> Self {
        self.trace = Some(Trace {
            keys: root,
            ..Trace::default()
        });
        self
    }

    /// The provenance the last run recorded, if it was asked for and the run gave a value.
    pub fn provenance(&mut self) -> Option<Provenance> {
        let t = self.trace.as_mut()?;
        Some(Provenance {
            term: t.term.take()?,
            facts: std::mem::take(&mut t.facts),
        })
    }

    /// Sets the order in which definedness `fix` entries are defined.
    pub fn with_schedule(mut self, schedule: Schedule) -> Self {
        self.schedule = schedule;
        self
    }

    /// Sets the fuel.
    pub fn with_fuel(mut self, fuel: u64) -> Self {
        self.fuel = fuel;
        self
    }

    /// Evaluates a closed term, expecting data. The evaluation runs on its own thread, whose
    /// stack holds [`MAX_DEPTH`] nested calls.
    pub fn run(&mut self, term: &Term) -> Result<Value, KernelError> {
        on_stack(|stack| self.run_on(stack, term))
    }

    /// [`Evaluator::run`] on the current thread, which `stack` shows is one [`on_stack`]
    /// started. Many short evaluations then share one thread instead of starting one each.
    pub fn run_on(&mut self, _stack: &Stack, term: &Term) -> Result<Value, KernelError> {
        let outer = EVALUATING.replace(true);
        let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run_here(term)));
        EVALUATING.set(outer);
        out.unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    }

    fn run_here(&mut self, term: &Term) -> Result<Value, KernelError> {
        let copy;
        let term = match &mut self.trace {
            Some(_) => {
                copy = unshare(term);
                &copy
            }
            None => term,
        };
        if let Some(t) = &mut self.trace {
            t.positions.clear();
            let mut stack = vec![term];
            while let Some(node) = stack.pop() {
                let n = t.positions.len() as u32;
                t.positions.insert(node as *const Term as usize, n);
                stack.extend(children(node).into_iter().rev());
            }
            t.facts.clear();
        }
        let out = self.eval(term, &None);
        if let (Some(t), Ok(_)) = (&mut self.trace, &out) {
            t.term = Some(term.clone());
        }
        match out {
            Ok(V::Data(v)) => Ok(v),
            Ok(_) => Err(KernelError::Type(
                "the program's result is a function".into(),
            )),
            Err(Stop::Error(e)) => Err(e),
            Err(Stop::Undefined { .. }) => {
                unreachable!("only a definedness fix binds a partial family")
            }
        }
    }

    fn burn(&mut self) -> R<()> {
        if self.fuel == 0 {
            return Err(KernelError::OutOfFuel.into());
        }
        self.fuel -= 1;
        Ok(())
    }

    fn data(&mut self, term: &Term, env: &Env) -> R<Value> {
        match self.eval(term, env)? {
            V::Data(v) => Ok(v),
            _ => type_err("expected data, found a function"),
        }
    }

    fn family(&mut self, term: &Term, env: &Env) -> R<Family> {
        match self.data(term, env)? {
            Value::Family(f) => Ok(f),
            other => type_err(format!("expected a family, found {other}")),
        }
    }

    /// Evaluates `term`, and when provenance is recorded, records its fact, whose inputs are
    /// the facts its subterms read. A variable is an edge, not a node: it passes on the fact
    /// of the value it names.
    fn eval(&mut self, term: &Term, env: &Env) -> R<V> {
        let Some(t) = &mut self.trace else {
            return self.eval_node(term, env);
        };
        if let Term::Var(name) = term {
            let out = self.eval_node(term, env);
            if out.is_ok() {
                let fact = lookup_fact(env, name);
                self.trace.as_mut().expect("on").reads.push(fact);
            }
            return out;
        }
        let outer = std::mem::take(&mut t.reads);
        let out = self.eval_node(term, env);
        let t = self.trace.as_mut().expect("on");
        let inputs = std::mem::replace(&mut t.reads, outer);
        if let Ok(v) = &out {
            let mut node = t.calls.clone();
            node.push(t.positions[&(term as *const Term as usize)]);
            t.facts.push(Fact {
                address: FactAddress {
                    node: NodeAddress(node),
                    keypath: t.keys.clone(),
                },
                value: match v {
                    V::Data(d) => Some(d.clone()),
                    _ => None,
                },
                inputs: inputs.into_iter().flatten().collect(),
            });
            let id = t.facts.len() - 1;
            t.reads.push(Some(id));
        }
        out
    }

    /// The fact of the value the last subterm evaluated gave.
    fn last_fact(&self) -> Option<usize> {
        self.trace.as_ref()?.reads.last().copied().flatten()
    }

    /// The position of `term`, when provenance is recorded.
    fn pos(&self, term: &Term) -> Option<u32> {
        Some(self.trace.as_ref()?.positions[&(term as *const Term as usize)])
    }

    /// Names the call site and the argument facts of the next closure call.
    fn aim(&mut self, site: Option<u32>, args: Vec<Option<usize>>) {
        if let Some(t) = &mut self.trace {
            t.site = site;
            t.args = args;
        }
    }

    /// Enters the region instance at `keys`, below the current one.
    fn enter(&mut self, keys: &[Value]) {
        if let Some(t) = &mut self.trace {
            t.keys.extend_from_slice(keys);
        }
    }

    /// Leaves the last `n` coordinates of the keypath.
    fn leave(&mut self, n: usize) {
        if let Some(t) = &mut self.trace {
            t.keys.truncate(t.keys.len() - n);
        }
    }

    fn eval_node(&mut self, term: &Term, env: &Env) -> R<V> {
        match term {
            Term::Lit(v) => Ok(V::Data(v.clone())),
            Term::Var(name) => match lookup(env, name) {
                Some(v) => Ok(v),
                None => type_err(format!("unbound variable `{name}`")),
            },
            Term::Lam(params, body) => Ok(V::Closure(Rc::new(Closure {
                params: params.clone(),
                body: body.clone(),
                env: env.clone(),
            }))),
            Term::PrimFn(p) => Ok(V::Prim(*p)),
            Term::App(f, args) => {
                let f = self.eval(f, env)?;
                let args = args
                    .iter()
                    .map(|a| self.eval(a, env))
                    .collect::<R<Vec<_>>>()?;
                let facts = match &self.trace {
                    Some(t) => t.reads[t.reads.len() - args.len()..].to_vec(),
                    None => Vec::new(),
                };
                self.aim(self.pos(term), facts);
                self.apply(&f, args)
            }
            Term::Prim(p, args) => {
                let args = args
                    .iter()
                    .map(|a| self.eval(a, env))
                    .collect::<R<Vec<_>>>()?;
                self.prim(*p, args)
            }
            Term::Let(name, e, body) => {
                let v = self.eval(e, env)?;
                let fact = self.last_fact();
                self.eval(body, &bind_fact(env, name.clone(), v, fact))
            }
            Term::If(c, a, b) => match self.data(c, env)? {
                Value::Bool(true) => self.eval(a, env),
                Value::Bool(false) => self.eval(b, env),
                atom @ Value::Atom(_) => Ok(V::Data(atom)),
                other => type_err(format!("`if` on {other}")),
            },
            Term::Match(scrutinee, arms) => {
                let v = self.eval(scrutinee, env)?;
                let fact = self.last_fact();
                for (pat, body) in arms {
                    let mut env2 = env.clone();
                    let hit = match (&v, pat) {
                        (V::Data(v), pat) => matches(pat, v, &mut env2, fact),
                        (_, Pattern::Wild) => true,
                        (f, Pattern::Bind(name)) => {
                            env2 = bind_fact(env, name.clone(), f.clone(), fact);
                            true
                        }
                        (_, Pattern::Is(t)) => t.functions(),
                        _ => false,
                    };
                    if hit {
                        return self.eval(body, &env2);
                    }
                }
                match v {
                    V::Data(v) => type_err(format!("no arm matches {v}")),
                    _ => type_err("no arm matches the function"),
                }
            }
            Term::Fam { domain, var, body } => {
                let domain = self.family(domain, env)?;
                self.pure += 1;
                let out = domain
                    .keys()
                    .map(|k| {
                        self.enter(std::slice::from_ref(k));
                        let v = self.data(body, &bind(env, var.clone(), V::Data(k.clone())));
                        self.leave(1);
                        Ok((vec![k.clone()], v?))
                    })
                    .collect::<R<Vec<_>>>();
                self.pure -= 1;
                Ok(V::Data(Value::Family(Family::from_leaves(out?)?)))
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness: _,
            } => {
                let family = self.family(family, env)?;
                let from = self.last_fact();
                let sites = (self.pos(kf), self.pos(vf));
                let (kf, vf) = (self.eval(kf, env)?, self.eval(vf, env)?);
                self.pure += 1;
                let out = self.reindex(&family, (&kf, sites.0), (&vf, sites.1), from);
                self.pure -= 1;
                Ok(V::Data(Value::Family(out?)))
            }
            Term::Discard { family, sel } => {
                let family = self.family(family, env)?;
                let from = self.last_fact();
                let site = self.pos(sel);
                let sel = self.eval(sel, env)?;
                self.pure += 1;
                let out = self.discard(&family, (&sel, site), from, &mut Vec::new());
                self.pure -= 1;
                Ok(V::Data(Value::Family(out?)))
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ..
            } => {
                let family = self.family(family, env)?;
                let from = self.last_fact();
                let site = self.pos(op);
                let op = self.eval(op, env)?;
                let identity = identity.as_ref().map(|t| self.data(t, env)).transpose()?;
                self.pure += 1;
                let out = self.fold(&family, (&op, site), from, identity, *depth);
                self.pure -= 1;
                Ok(V::Data(out?))
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind,
                ..
            } => {
                self.pure += 1;
                let out = match kind {
                    FixKind::Lattice { join } => self.fix_lattice(init, step, join, env),
                    FixKind::Definedness => self.fix_definedness(init, step, this, key, env),
                };
                self.pure -= 1;
                Ok(V::Data(out?))
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                let init = self.data(init, env)?;
                let from = self.last_fact();
                let sites = (self.pos(step), self.pos(guard));
                let (step, guard) = (self.eval(step, env)?, self.eval(guard, env)?);
                let (step, guard) = ((&step, sites.0), (&guard, sites.1));
                Ok(V::Data(self.generations(init, from, step, guard, *pos)?))
            }
            Term::Read(port) => {
                self.check_impure(port)?;
                match self.world.inputs.get(&**port) {
                    Some(v) => Ok(V::Data(v.clone())),
                    None if self.world.sources.contains_key(&**port) => Ok(V::Source(port.clone())),
                    None => Err(KernelError::UnknownPort(port.to_string()).into()),
                }
            }
            Term::Push(port, value) => {
                let value = self.data(value, env)?;
                self.check_impure(port)?;
                let Some(out) = self.world.outputs.get_mut(&**port) else {
                    return Err(KernelError::UnknownPort(port.to_string()).into());
                };
                if out.capacity.is_some_and(|c| out.log.len() >= c) {
                    return Ok(V::Data(Value::atom("full")));
                }
                out.log.push(value);
                Ok(V::Data(Value::atom("ok")))
            }
        }
    }

    fn check_impure(&self, port: &str) -> R<()> {
        if self.pure > 0 {
            return type_err(format!("port `{port}` used inside a pure region"));
        }
        Ok(())
    }

    fn apply(&mut self, f: &V, args: Vec<V>) -> R<V> {
        self.burn()?;
        let (site, mut facts) = match &mut self.trace {
            Some(t) => (t.site.take(), std::mem::take(&mut t.args)),
            None => (None, Vec::new()),
        };
        match f {
            V::Closure(c) => {
                if c.params.len() != args.len() {
                    return type_err(format!(
                        "a function of {} parameters called with {} arguments",
                        c.params.len(),
                        args.len()
                    ));
                }
                if self.depth >= MAX_DEPTH {
                    return Err(KernelError::TooDeep.into());
                }
                facts.resize(args.len(), None);
                let mut env = c.env.clone();
                for ((p, a), fact) in c.params.iter().zip(args).zip(facts) {
                    env = bind_fact(&env, p.clone(), a, fact);
                }
                if let (Some(t), Some(site)) = (&mut self.trace, site) {
                    t.calls.push(site);
                }
                self.depth += 1;
                let out = self.eval(&c.body, &env);
                self.depth -= 1;
                if let (Some(t), Some(_)) = (&mut self.trace, site) {
                    t.calls.pop();
                }
                out
            }
            V::Prim(p) => self.prim(*p, args),
            // Until types arrive (step L1.22), the elaboration of `v[k]` cannot tell a family
            // from a function, so a family or a lookup port applied to one key reads it.
            V::Source(_) | V::Data(Value::Family(_)) if args.len() == 1 => {
                self.prim(Prim::Get, [vec![f.clone()], args].concat())
            }
            V::Partial(_) | V::Source(_) => type_err("a family is read with `[]`, not called"),
            V::Data(Value::Atom(a)) => Ok(V::Data(Value::Atom(a.clone()))),
            V::Data(other) => type_err(format!("{other} is not a function")),
        }
    }

    fn call2(&mut self, f: &V, a: Value, b: Value) -> R<Value> {
        match self.apply(f, vec![V::Data(a), V::Data(b)])? {
            V::Data(v) => Ok(v),
            _ => type_err("expected data, found a function"),
        }
    }

    fn prim(&mut self, p: Prim, args: Vec<V>) -> R<V> {
        if let Some(n) = p.arity()
            && args.len() != n
        {
            return type_err(format!("{p:?} takes {n} arguments, given {}", args.len()));
        }
        // `f[k]` on the family a definedness fix is building.
        if p == Prim::Get
            && let V::Partial(part) = &args[0]
        {
            let V::Data(k) = &args[1] else {
                return type_err("a key must be data");
            };
            if let Value::Atom(_) = k {
                return Ok(V::Data(k.clone()));
            }
            return match part.defined.borrow().get(k) {
                Some((v, r)) if *r < part.round => Ok(V::Data(v.clone())),
                // An entry defined in this Jacobi round is not yet visible to it.
                _ if part.domain.contains(k) => Err(Stop::Undefined {
                    fix: part.fix,
                    key: k.clone(),
                }),
                _ => Ok(V::Data(Value::atom("notFound"))),
            };
        }
        // `fs[k]` on a lookup port: the world answers once, and the answer is kept.
        if matches!(p, Prim::Get | Prim::TupleGet)
            && let V::Source(port) = &args[0]
        {
            self.check_impure(port)?;
            let V::Data(k) = &args[1] else {
                return type_err("a key must be data");
            };
            if let Value::Atom(_) = k {
                return Ok(V::Data(k.clone()));
            }
            if let Some(v) = self.world.reads.get(&**port).and_then(|r| r.get(k)) {
                return Ok(V::Data(v.clone()));
            }
            let v = self.world.sources[&**port]
                .get(k)
                .map_err(|why| KernelError::Port(port.to_string(), why))?;
            let reads = self.world.reads.entry(port.to_string()).or_default();
            reads.insert(k.clone(), v.clone());
            return Ok(V::Data(v));
        }
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            match a {
                V::Data(v) => vals.push(v),
                _ if matches!(p, Prim::Eq | Prim::Ne) => {
                    return type_err(
                        "`==` on functions compares them at every point of an enumerable \
                         domain, which their types give (step L1.22)",
                    );
                }
                _ => return type_err(format!("{p:?} applied to a function")),
            }
        }
        // A tuple and an atom's payload hold atoms as data, and `==` has an arrow at every
        // type, atoms included; every other primitive passes its atoms through, merged.
        if !matches!(p, Prim::Tuple | Prim::Atom | Prim::Eq | Prim::Ne)
            && vals.iter().any(|v| matches!(v, Value::Atom(_)))
        {
            let atoms = vals.iter().filter(|v| matches!(v, Value::Atom(_)));
            return Ok(V::Data(Value::merge_failures(atoms)));
        }
        Ok(V::Data(prim_data(p, vals)?))
    }

    /// Each region call below reads its argument from the fact `from`, the region's input,
    /// and runs at the call site of the operand it calls, inside the region instance of its
    /// leaf, entry, step or iterate.
    fn reindex(
        &mut self,
        family: &Family,
        (kf, kf_site): (&V, Option<u32>),
        (vf, vf_site): (&V, Option<u32>),
        from: Option<usize>,
    ) -> R<Family> {
        let mut out = Vec::new();
        for (path, v) in family.leaves() {
            self.enter(&path);
            let p = Value::Path(path.clone());
            self.aim(kf_site, vec![from; 2]);
            let key = self.call2(kf, p.clone(), v.clone());
            self.aim(vf_site, vec![from; 2]);
            let value = key.and_then(|key| Ok((key, self.call2(vf, p, v)?)));
            self.leave(path.len());
            let (key, value) = value?;
            let key = match key {
                Value::Path(keys) => keys,
                single => vec![single],
            };
            out.push((key, value));
        }
        Ok(Family::from_leaves(out)?)
    }

    fn discard(
        &mut self,
        family: &Family,
        (sel, site): (&V, Option<u32>),
        from: Option<usize>,
        prefix: &mut Keypath,
    ) -> R<Family> {
        let mut out = Vec::new();
        for (k, v) in family.iter() {
            prefix.push(k.clone());
            self.enter(std::slice::from_ref(k));
            self.aim(site, vec![from; 2]);
            let verdict = self.call2(sel, Value::Path(prefix.clone()), v.clone())?;
            match verdict {
                Value::Bool(true) => match v {
                    Value::Family(sub) => out.push((
                        vec![k.clone()],
                        Value::Family(self.discard(sub, (sel, site), from, prefix)?),
                    )),
                    leaf => out.push((vec![k.clone()], leaf.clone())),
                },
                Value::Bool(false) => {}
                Value::Atom(a) if &*a.name == "boundary" && a.args.is_empty() => {
                    out.push((vec![k.clone()], k.clone()))
                }
                other => {
                    prefix.pop();
                    return type_err(format!("a discard selector returned {other}"));
                }
            }
            self.leave(1);
            prefix.pop();
        }
        Ok(Family::from_leaves(out)?)
    }

    fn fold(
        &mut self,
        family: &Family,
        op: (&V, Option<u32>),
        from: Option<usize>,
        identity: Option<Value>,
        depth: usize,
    ) -> R<Value> {
        let leaves = family.leaves();
        if leaves.iter().any(|(p, _)| p.len() != depth) {
            return Err(KernelError::MixedDepth.into());
        }
        if depth == 1 {
            let values: Vec<Value> = leaves.into_iter().map(|(_, v)| v).collect();
            return self.reduce(&values, op, from, identity);
        }
        // Collapse the innermost level beneath each outer keypath.
        let mut groups: BTreeMap<Keypath, Vec<Value>> = BTreeMap::new();
        for (mut path, v) in leaves {
            path.pop();
            groups.entry(path).or_default().push(v);
        }
        let mut out = Vec::new();
        for (path, values) in groups {
            self.enter(&path);
            let v = self.reduce(&values, op, from, identity.clone());
            self.leave(path.len());
            out.push((path, v?));
        }
        Ok(Value::Family(Family::from_leaves(out)?))
    }

    /// Reduces one level in key order. A fold of the primitive `+` over floats is the exact
    /// sum, rounded once; any other operator runs on the canonical tree.
    /// The `i`th application of `op` runs at step `i` of the level.
    fn reduce(
        &mut self,
        values: &[Value],
        (op, site): (&V, Option<u32>),
        from: Option<usize>,
        identity: Option<Value>,
    ) -> R<Value> {
        if values.is_empty() {
            return Ok(identity.unwrap_or_else(|| Value::atom("empty")));
        }
        if matches!(op, V::Prim(Prim::Add)) {
            if let Some(atom) = values.iter().find(|v| matches!(v, Value::Atom(_))) {
                return Ok(atom.clone());
            }
            let floats: Option<Vec<f64>> = values
                .iter()
                .map(|v| match v {
                    Value::Float(x) => Some(x.get()),
                    _ => None,
                })
                .collect();
            if let Some(xs) = floats {
                return Ok(Value::float(exact_sum(&xs)));
            }
        }
        let mut step = 0;
        canonical_tree(values, &mut |a, b| {
            self.enter(&[Value::Int(step)]);
            step += 1;
            self.aim(site, vec![from; 2]);
            let v = self.call2(op, a, b);
            self.leave(1);
            v
        })
    }

    /// Iterate `i`'s step and join run at coordinate `i`, the step reading the fact of the
    /// iterate before.
    fn fix_lattice(&mut self, init: &Term, step: &Term, join: &Term, env: &Env) -> R<Value> {
        let mut x = self.data(init, env)?;
        let mut from = self.last_fact();
        let sites = (self.pos(step), self.pos(join));
        let (step, join) = (self.eval(step, env)?, self.eval(join, env)?);
        for i in 0.. {
            self.burn()?;
            self.enter(&[Value::Int(i)]);
            self.aim(sites.0, vec![from]);
            let next = self.apply(&step, vec![V::Data(x.clone())]);
            let next_fact = self.last_fact();
            self.aim(sites.1, vec![from, next_fact]);
            let joined = next.and_then(|next| match next {
                V::Data(next) => self.call2(&join, x.clone(), next),
                _ => type_err("a fix step returned a function"),
            });
            self.leave(1);
            let joined = joined?;
            from = self.last_fact();
            if joined == x {
                return Ok(x);
            }
            x = joined;
        }
        unreachable!("the fuel ends the ascent")
    }

    fn fix_definedness(
        &mut self,
        init: &Term,
        body: &Term,
        this: &Arc<str>,
        key: &Arc<str>,
        env: &Env,
    ) -> R<Value> {
        let domain: Rc<BTreeSet<Value>> =
            Rc::new(self.family(init, env)?.keys().cloned().collect());
        self.fixes += 1;
        let fix = Definedness {
            id: self.fixes,
            domain,
            body,
            this,
            key,
            env,
            defined: Rc::default(),
        };
        let stalled = match self.schedule {
            Schedule::Rounds => self.define_in_rounds(&fix, None)?,
            Schedule::Chaotic(seed) => self.define_in_rounds(&fix, Some(seed))?,
            Schedule::Pull => self.define_on_demand(&fix)?,
        };
        if !stalled.is_empty() {
            return Err(KernelError::Stalled { keys: stalled }.into());
        }
        let defined = std::mem::take(&mut *fix.defined.borrow_mut());
        let leaves = defined.into_iter().map(|(k, (v, _))| (vec![k], v));
        Ok(Value::Family(Family::from_leaves(leaves)?))
    }

    /// Evaluates the entry at `k` against the entries defined before `round`: its value, or
    /// the key of the undefined entry of this `fix` it read first.
    fn entry(&mut self, fix: &Definedness, round: u64, k: &Value) -> R<Result<Value, Value>> {
        let part = V::Partial(Rc::new(Partial {
            fix: fix.id,
            domain: fix.domain.clone(),
            defined: fix.defined.clone(),
            round,
        }));
        let env = bind(
            &bind(fix.env, fix.this.clone(), part),
            fix.key.clone(),
            V::Data(k.clone()),
        );
        // An attempt that reads an undefined entry is not a fact: what it recorded is
        // dropped, and the entry's fact is the attempt that defines it.
        let mark = self
            .trace
            .as_ref()
            .map(|t| (t.facts.len(), t.calls.len(), t.keys.len()));
        self.enter(std::slice::from_ref(k));
        let out = self.eval(fix.body, &env);
        self.leave(1);
        match out {
            Ok(V::Data(v)) => Ok(Ok(v)),
            Ok(_) => type_err("a fix entry is a function"),
            Err(Stop::Undefined { fix: id, key }) if id == fix.id => {
                if let (Some(t), Some((facts, calls, keys))) = (&mut self.trace, mark) {
                    t.facts.truncate(facts);
                    t.calls.truncate(calls);
                    t.keys.truncate(keys);
                }
                Ok(Err(key))
            }
            Err(e) => Err(e),
        }
    }

    /// Defines entries in rounds until every entry is defined or a round defines none, and
    /// returns the keys left undefined. Without a seed each round reads the family as it
    /// began (Jacobi); with one, each round visits the entries in a shuffled order and reads
    /// the entries defined before it in the same round.
    fn define_in_rounds(&mut self, fix: &Definedness, seed: Option<u64>) -> R<Vec<Value>> {
        let mut rng = seed.map(SplitMix);
        let undefined = |fix: &Definedness| -> Vec<Value> {
            let defined = fix.defined.borrow();
            let left = fix.domain.iter().filter(|k| !defined.contains_key(*k));
            left.cloned().collect()
        };
        for round in 1.. {
            self.burn()?;
            let mut pending = undefined(fix);
            if pending.is_empty() {
                return Ok(pending);
            }
            if let Some(rng) = &mut rng {
                rng.shuffle(&mut pending);
            }
            // Jacobi rounds read the entries of earlier rounds; chaotic ones read every entry.
            let sees = if rng.is_some() { u64::MAX } else { round };
            let mut progress = false;
            for k in pending {
                if let Ok(v) = self.entry(fix, sees, &k)? {
                    fix.defined.borrow_mut().insert(k, (v, round));
                    progress = true;
                }
            }
            if !progress {
                return Ok(undefined(fix));
            }
        }
        unreachable!("the rounds end when every entry is defined or a round defines none")
    }

    /// Demands each entry in key order, evaluating first each undefined entry it reads, and
    /// returns the keys that stalled: those on a cycle and those waiting on one.
    fn define_on_demand(&mut self, fix: &Definedness) -> R<Vec<Value>> {
        let mut stalled = BTreeSet::new();
        for k0 in fix.domain.iter() {
            if fix.defined.borrow().contains_key(k0) || stalled.contains(k0) {
                continue;
            }
            let mut demanded = vec![k0.clone()];
            while let Some(k) = demanded.last().cloned() {
                self.burn()?;
                match self.entry(fix, u64::MAX, &k)? {
                    Ok(v) => {
                        fix.defined.borrow_mut().insert(k, (v, 0));
                        demanded.pop();
                    }
                    Err(read) if demanded.contains(&read) || stalled.contains(&read) => {
                        stalled.extend(demanded.drain(..));
                    }
                    Err(read) => demanded.push(read),
                }
            }
        }
        Ok(stalled.into_iter().collect())
    }

    /// The step making generation `t` and the guard testing it run at coordinate `t`, each
    /// reading the fact of the frame before.
    fn generations(
        &mut self,
        init: Value,
        mut from: Option<usize>,
        (step, step_site): (&V, Option<u32>),
        guard: (&V, Option<u32>),
        pos: GuardPos,
    ) -> R<Value> {
        let mut frames = vec![init];
        loop {
            if pos == GuardPos::Before && !self.go_on(guard, from, &mut frames)? {
                break;
            }
            self.burn()?;
            let last = frames.last().expect("generation 0 is present").clone();
            self.enter(&[Value::Int(frames.len() as i64)]);
            self.aim(step_site, vec![from]);
            let next = self.apply(step, vec![V::Data(last)]);
            self.leave(1);
            match next? {
                V::Data(next) => frames.push(next),
                _ => return type_err("a gen step returned a function"),
            }
            from = self.last_fact();
            if pos == GuardPos::After && !self.go_on(guard, from, &mut frames)? {
                break;
            }
        }
        let leaves = frames
            .into_iter()
            .enumerate()
            .map(|(t, f)| (vec![Value::Int(t as i64)], f));
        Ok(Value::Family(Family::from_leaves(leaves)?))
    }

    /// Tests a `gen` guard on the last frame. A result that is not a bool ends the loop and
    /// is appended as the stream's last entry.
    fn go_on(
        &mut self,
        (guard, site): (&V, Option<u32>),
        from: Option<usize>,
        frames: &mut Vec<Value>,
    ) -> R<bool> {
        let last = frames.last().expect("generation 0 is present").clone();
        self.enter(&[Value::Int(frames.len() as i64 - 1)]);
        self.aim(site, vec![from]);
        let verdict = self.apply(guard, vec![V::Data(last)]);
        self.leave(1);
        match verdict? {
            V::Data(Value::Bool(b)) => Ok(b),
            V::Data(end @ Value::Atom(_)) => {
                frames.push(end);
                Ok(false)
            }
            V::Data(other) => type_err(format!("a gen guard returned {other}")),
            _ => type_err("a gen guard returned a function"),
        }
    }
}

/// One definedness `fix` being evaluated: its family's name, domain, and entry body.
struct Definedness<'a> {
    id: u64,
    domain: Rc<BTreeSet<Value>>,
    defined: Rc<RefCell<Defined>>,
    body: &'a Term,
    this: &'a Arc<str>,
    key: &'a Arc<str>,
    env: &'a Env,
}

/// The SplitMix64 generator, which draws the visiting order of [`Schedule::Chaotic`].
struct SplitMix(u64);

impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A Fisher–Yates shuffle.
    fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            xs.swap(i, (self.next() % (i as u64 + 1)) as usize);
        }
    }
}

/// Whether `v` matches `pat`, binding its variables in `env` to parts of `v`, which came
/// from `fact`.
fn matches(pat: &Pattern, v: &Value, env: &mut Env, fact: Option<usize>) -> bool {
    match (pat, v) {
        (Pattern::Wild, _) => true,
        (Pattern::Bind(name), v) => {
            *env = bind_fact(env, name.clone(), V::Data(v.clone()), fact);
            true
        }
        (Pattern::Lit(l), v) => l == v,
        (Pattern::AnyAtom, Value::Atom(_)) => true,
        (Pattern::Is(t), v) => t.contains(v),
        (Pattern::Atom(name, ps), Value::Atom(a)) => {
            a.name == *name
                && a.fields.is_empty()
                && ps.len() == a.args.len()
                && ps
                    .iter()
                    .zip(&a.args)
                    .all(|(p, x)| matches(p, x, env, fact))
        }
        (Pattern::Fields(name, fs), Value::Atom(a)) => {
            a.name == *name
                && !a.fields.is_empty()
                && fs.iter().all(|(f, p)| match a.fields.binary_search(f) {
                    Ok(i) => matches(p, &a.args[i], env, fact),
                    Err(_) => false,
                })
        }
        (Pattern::Tuple(ps), Value::Tuple(xs)) => {
            ps.len() == xs.len() && ps.iter().zip(xs).all(|(p, x)| matches(p, x, env, fact))
        }
        _ => false,
    }
}

fn overflow<T>() -> Result<T, KernelError> {
    Err(KernelError::Overflow)
}

/// The integer `n`, unless it is beyond the evaluator's size limit.
fn sized(n: BigInt) -> Result<Value, KernelError> {
    if n.bits() > MAX_BITS {
        return overflow();
    }
    Ok(Value::int(n))
}

/// An integer `+`, `-`, `*`, `div`, `mod` or `**` of two integers, either of either width:
/// in a machine word when the result fits, else unbounded. `None` for a negative power.
fn int_binary(p: Prim, a: &Value, b: &Value) -> Result<Option<Value>, KernelError> {
    if let (Value::Int(x), Value::Int(y)) = (a, b) {
        let fast = match p {
            Prim::Add => x.checked_add(*y),
            Prim::Sub => x.checked_sub(*y),
            Prim::Mul => x.checked_mul(*y),
            Prim::IntDiv if *y != 0 => x.checked_div_euclid(*y),
            Prim::Mod if *y != 0 => x.checked_rem_euclid(*y),
            Prim::Pow => u32::try_from(*y).ok().and_then(|y| x.checked_pow(y)),
            _ => None,
        };
        if let Some(n) = fast {
            return Ok(Some(Value::Int(n)));
        }
    }
    let (x, y) = (
        a.as_bigint().expect("an integer"),
        b.as_bigint().expect("an integer"),
    );
    let n = match p {
        Prim::Add => x + y,
        Prim::Sub => x - y,
        Prim::Mul => x * y,
        Prim::IntDiv | Prim::Mod if y.is_zero() => return Ok(Some(Value::atom("divByZero"))),
        Prim::IntDiv => x.div_euclid(&y),
        Prim::Mod => x.rem_euclid(&y),
        _ if y.is_negative() => return Ok(None),
        // `0`, `1` and `-1` stay small at any power.
        _ if x.magnitude() <= &1u32.into() => {
            if y.is_zero() || (x.is_negative() && (&y % 2u32).is_zero()) {
                BigInt::from(1)
            } else {
                x
            }
        }
        _ => match u32::try_from(&y) {
            Ok(e) if x.bits().saturating_mul(u64::from(e)) <= MAX_BITS + 64 => x.pow(e),
            _ => return overflow(),
        },
    };
    sized(n).map(Some)
}

/// A primitive on data none of which is an atom.
fn prim_data(p: Prim, vals: Vec<Value>) -> Result<Value, KernelError> {
    use Value::{Bool, Float, Int, Str};
    let ty = |vals: &[Value]| {
        let shown: Vec<String> = vals.iter().map(|v| v.to_string()).collect();
        Err(KernelError::Type(format!(
            "{p:?} applied to {}",
            shown.join(", ")
        )))
    };
    let out = match (p, vals.as_slice()) {
        (Prim::Add | Prim::Sub | Prim::Mul | Prim::IntDiv | Prim::Mod | Prim::Pow, [a, b])
            if a.number_kind() == Some(0) && b.number_kind() == Some(0) =>
        {
            match int_binary(p, a, b)? {
                Some(v) => v,
                None => return ty(&vals),
            }
        }
        (Prim::Neg, [Int(a)]) => match a.checked_neg() {
            Some(n) => Int(n),
            None => sized(-BigInt::from(*a))?,
        },
        (Prim::Neg, [Value::Big(a)]) => sized(-(**a).clone())?,
        (Prim::Add | Prim::Sub | Prim::Mul | Prim::Div, [Value::Rat(a), Value::Rat(b)]) => {
            let r = match p {
                Prim::Add => a.add(b),
                Prim::Sub => a.sub(b),
                Prim::Mul => a.mul(b),
                _ => match a.div(b) {
                    Some(r) => r,
                    None => return Ok(Value::atom("divByZero")),
                },
            };
            if r.bits() > MAX_BITS {
                return overflow();
            }
            Value::rat(r)
        }
        (Prim::Neg, [Value::Rat(a)]) => Value::rat(a.neg()),
        (Prim::Add, [Float(a), Float(b)]) => Value::float(a.get() + b.get()),
        (Prim::Sub, [Float(a), Float(b)]) => Value::float(a.get() - b.get()),
        (Prim::Mul, [Float(a), Float(b)]) => Value::float(a.get() * b.get()),
        (Prim::Div, [Float(a), Float(b)]) => Value::float(a.get() / b.get()),
        (Prim::Neg, [Float(a)]) => Value::float(-a.get()),
        (Prim::Concat, [Str(a), Str(b)]) => Value::str(&format!("{a}{b}")),
        (Prim::Pow, [Float(a), Float(b)]) => Value::float(a.get().powf(b.get())),
        (Prim::Eq, [a, b]) => Bool(a.surface_eq(b)),
        (Prim::Ne, [a, b]) => Bool(!a.surface_eq(b)),
        // Two floats compare as IEEE 754 does, so every comparison with a NaN is false.
        (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge, [Float(a), Float(b)]) => {
            let (a, b) = (a.get(), b.get());
            Bool(match p {
                Prim::Lt => a < b,
                Prim::Le => a <= b,
                Prim::Gt => a > b,
                _ => a >= b,
            })
        }
        (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Min | Prim::Max, [a, b]) => {
            let same = match (a.number_kind(), b.number_kind()) {
                (None, None) => std::mem::discriminant(a) == std::mem::discriminant(b),
                (x, y) => x == y,
            };
            if !same {
                return ty(&vals);
            }
            let o = a.surface_cmp(b);
            match p {
                Prim::Lt => Bool(o == Some(Ordering::Less)),
                Prim::Le => Bool(matches!(o, Some(Ordering::Less | Ordering::Equal))),
                Prim::Gt => Bool(o == Some(Ordering::Greater)),
                Prim::Ge => Bool(matches!(o, Some(Ordering::Greater | Ordering::Equal))),
                Prim::Min => a.min(b).clone(),
                _ => a.max(b).clone(),
            }
        }
        (Prim::And, [Bool(a), Bool(b)]) => Bool(*a && *b),
        (Prim::Or, [Bool(a), Bool(b)]) => Bool(*a || *b),
        (Prim::Not, [Bool(a)]) => Bool(!a),
        // `v[0]` elaborates to `tupleGet` before types tell a family from a tuple (L1.22).
        (Prim::Get | Prim::TupleGet, [Value::Family(f), k]) => {
            f.get(k).cloned().unwrap_or_else(|| Value::atom("notFound"))
        }
        (Prim::Count, [Value::Family(f)]) => Int(f.len() as i64),
        (Prim::Union, [Value::Family(a), Value::Family(b)]) => {
            let mut leaves = a.leaves();
            let have: BTreeMap<Keypath, Value> = leaves.iter().cloned().collect();
            for (path, v) in b.leaves() {
                match have.get(&path) {
                    Some(w) if *w == v => {}
                    _ => leaves.push((path, v)),
                }
            }
            Value::Family(Family::from_leaves(leaves)?)
        }
        (Prim::Path, keys) => Value::Path(keys.to_vec()),
        (Prim::Atom, [Str(name), Value::Tuple(names), args @ ..]) if names.is_empty() => {
            Value::atom_with(name, args.to_vec())
        }
        (Prim::Atom, [Str(name), Value::Tuple(names), args @ ..]) if names.len() == args.len() => {
            let fields: Option<Vec<(Arc<str>, Value)>> = names
                .iter()
                .zip(args)
                .map(|(n, v)| match n {
                    Str(n) => Some((n.clone(), v.clone())),
                    _ => None,
                })
                .collect();
            match fields.and_then(|fs| Value::atom_named(name, fs)) {
                Some(v) => v,
                None => return ty(&vals),
            }
        }
        (Prim::PathKey, [Value::Path(keys), Int(i)]) => usize::try_from(*i)
            .ok()
            .and_then(|i| keys.get(i))
            .cloned()
            .unwrap_or_else(|| Value::atom("notFound")),
        (Prim::PathLen, [Value::Path(keys)]) => Int(keys.len() as i64),
        (Prim::Tuple, items) => Value::Tuple(items.to_vec()),
        (Prim::TupleGet, [Value::Tuple(items), Int(i)]) => {
            match usize::try_from(*i).ok().and_then(|i| items.get(i)) {
                Some(v) => v.clone(),
                None => return ty(&vals),
            }
        }
        (
            Prim::Show
            | Prim::CastInt
            | Prim::CastRat
            | Prim::CastF64
            | Prim::Abs
            | Prim::Len
            | Prim::Lower
            | Prim::Upper
            | Prim::Trim,
            [x],
        ) => crate::words::word(p, x)?,
        (Prim::Sum, [Value::Tuple(items)]) => {
            if items.iter().any(|v| matches!(v, Value::Atom(_))) {
                return Ok(Value::merge_failures(
                    items.iter().filter(|v| matches!(v, Value::Atom(_))),
                ));
            }
            let Some((first, rest)) = items.split_first() else {
                return Ok(Int(0));
            };
            if first.number_kind().is_none() {
                return ty(&vals);
            }
            let mut total = first.clone();
            for x in rest {
                total = prim_data(Prim::Add, vec![total, x.clone()])?;
            }
            total
        }
        _ => return ty(&vals),
    };
    Ok(out)
}
