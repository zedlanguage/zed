//! The reference evaluator of the kernel calculus (step M0.9).
//!
//! The evaluator is strict and big-step: a term reduces to a value, arguments left to right.
//! It is written for clarity first; every back end is tested against it. The choices the spec
//! leaves to the reference semantics are recorded in DESIGN.md sec:kernel, "Reference
//! semantics", and repeated on the item they govern here.
//!
//! It runs as a machine with a stack of its own: a `Frame` holds what is left to do when the
//! term under evaluation gives its value, so nesting uses memory on the heap, not the thread's
//! stack, and the depth of a program is limited by the machine's memory alone (DESIGN.md
//! sec:verification, step M0.11). A call in tail position leaves no frame unless provenance is
//! recorded, so a loop written as tail recursion runs in constant space.
//!
//! Complexity tradeoff (COMPLEXITY.md K20): the naive evaluator recurses on the thread's stack,
//! O(depth) native stack (run on a 1 GiB thread), and copied the values of `Prim::Tuple` and
//! `Prim::Path`, O(n²) to build a list of `n`. Used: an explicit-stack machine, O(1) work per
//! step outside values and environments, its frames on the heap, values shared. Tradeoffs: a
//! frame is a heap allocation, which measured cheaper than the old recursion (1.2 µs against 10
//! µs per call at 19,990 calls, release build); depth is limited by memory alone.

use imbl::Vector;
use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use crate::exact::{CanonicalTree, TreeStep, exact_sum};
use crate::num::{Test, TooLarge, refused};
use crate::sites::{Sites, Span};
use crate::value::KernelError;
use crate::value::{Atom, Family, Fields, Keypath, all_leaves, ieee_min_max};
use std::sync::Arc;

use num_bigint::BigInt;

use crate::provenance::{Fact, FactAddress, Holds, NodeAddress, Position, Provenance};
use crate::term::{FixKind, GuardPos, Pattern, Prim, Shared, Term};
use crate::value::Value;

mod env;
use env::Env;

/// The minimum depth of nested calls the evaluator reaches (DESIGN.md step M0.11, prelude unit
/// `limits`): a conforming compiler never rejects an evaluation for nesting calls this deep. It
/// is a minimum and not a maximum: the evaluator's frames are on the heap, so it is bounded only
/// by the machine. There is no minimum of steps or of memory, since no count of either may stop
/// compile-time evaluation (author, 2026-11-09); [`Evaluator::with_fuel`] is a setting of the
/// evaluator a caller may choose, not a limit of the language.
pub const MIN_NESTED_CALLS: usize = 20_000;

/// A run-time value: a data value, or a function, which families never hold, or a tuple or an
/// atom that holds a function.
#[derive(Clone)]
enum V<'t> {
    /// Data.
    Data(Value),
    /// A lambda with its captured environment.
    Closure(Rc<Closure<'t>>),
    /// A primitive used as a function.
    Prim(Prim),
    /// The partial family a definedness `fix` is building, as its body sees it.
    Partial(Rc<Partial<'t>>),
    /// An input port read by lookup, such as a `Files` port: the port's name.
    Source(Arc<str>),
    /// A tuple or an atom with a part that is no data.
    Held(Rc<Held<'t>>),
}

/// A tuple or an atom that holds a function at some depth: a tuple, an array or a struct may
/// hold one, and only a use that needs data, such as showing it or `==`, is an error (DESIGN.md
/// step L1.17, QUESTIONS A43). It is made only when a part is no data, so a tuple of data stays
/// a [`Value`] and the common path is unchanged.
// Complexity tradeoff: a [`Value`] holds no function, and giving it one would put closures,
// with their lifetime and their environments, in every data structure, its order and its
// hash. Used: this second form, O(parts) to build like a data tuple, read in O(1) per part; a
// `match` on it walks the pattern as [`matches()`] does. Given up: a type test (`is`) on it
// builds a data stand-in, O(the parts above the data, which it shares), see
// [`Held::stand_in`]. Tests: `l01_17_value_representation::function_in_tuple` and
// `function_in_payload_run`.
struct Held<'t> {
    /// `None` for a tuple; for an atom, its name and its field names, sorted as
    /// [`Value::atom_named`] sorts them, empty for a payload by position.
    atom: Option<(Arc<str>, Fields)>,
    /// The components of a tuple, or the payload of an atom in the order of its field names.
    parts: Vec<V<'t>>,
    drops: Rc<Drops<'t>>,
}

impl Drop for Held<'_> {
    fn drop(&mut self) {
        self.drops
            .free(Freed::Parts(std::mem::take(&mut self.parts)));
    }
}

impl Held<'_> {
    /// `self` with each function in it replaced by the empty family. A type holds a family
    /// exactly when it holds every function (`Type::functions`, and `Type::member` on a
    /// family), so the stand-in is in a type exactly when `self` is. Built from an explicit
    /// stack, so a held value of any depth uses none of the thread's stack.
    fn stand_in(&self) -> Value {
        let mut stack: Vec<(&Held<'_>, Vec<Value>)> = vec![(self, Vec::new())];
        loop {
            let (h, done) = stack.last_mut().expect("the root is popped last");
            let h: &Held<'_> = h;
            match h.parts.get(done.len()) {
                Some(V::Data(d)) => done.push(d.clone()),
                Some(V::Held(k)) => stack.push((k, Vec::new())),
                Some(_) => done.push(Value::Family(Family::default())),
                None => {
                    let (h, done) = stack.pop().expect("the top read above");
                    let v = match &h.atom {
                        None => Value::tuple(done),
                        Some((name, fields)) => Value::Atom(Atom {
                            name: name.clone(),
                            fields: fields.clone(),
                            payload: Some(done.into()),
                        }),
                    };
                    match stack.last_mut() {
                        Some((_, up)) => up.push(v),
                        None => return v,
                    }
                }
            }
        }
    }
}

/// A lambda with its environment. The evaluated term outlives the run, so the closure borrows
/// its parameters and body from it.
struct Closure<'t> {
    params: &'t [Arc<str>],
    body: &'t Term,
    /// The body's position, when provenance is recorded.
    at: At,
    env: Env<'t>,
    drops: Rc<Drops<'t>>,
}

/// What [`Drops`] frees: an environment, or the parts of a [`Held`].
enum Freed<'t> {
    Env(Env<'t>),
    Parts(Vec<V<'t>>),
}

/// Environments and held parts no longer in use, freed one at a time. A closure's environment
/// can hold the only reference to another closure, and a held tuple to another held tuple, to
/// any depth, and dropping such a chain by Rust's recursive drop would use the thread's stack
/// as the evaluator otherwise does not.
#[derive(Default)]
struct Drops<'t> {
    envs: RefCell<Vec<Freed<'t>>>,
    /// Whether a drop further up the thread's stack is already emptying `envs`.
    busy: Cell<bool>,
}

impl<'t> Drops<'t> {
    fn free(&self, env: Freed<'t>) {
        self.envs.borrow_mut().push(env);
        if self.busy.replace(true) {
            return;
        }
        loop {
            // The borrow ends here: dropping the environment can reach `free` again.
            let next = self.envs.borrow_mut().pop();
            match next {
                Some(Freed::Env(env)) => drop(env),
                Some(Freed::Parts(parts)) => drop(parts),
                None => break,
            }
        }
        self.busy.set(false);
    }
}

impl Drop for Closure<'_> {
    fn drop(&mut self) {
        self.drops.free(Freed::Env(self.env.take()));
    }
}

/// The family a definedness `fix` has defined so far, over its whole domain.
struct Partial<'t> {
    /// The `fix` evaluation this family belongs to, so that a read of an undefined entry
    /// postpones or demands the entry of that `fix` and not of a `fix` nested inside its body.
    of: Rc<Definedness<'t>>,
    /// The attempt sees the entries defined in rounds before this one.
    round: u64,
}

/// The entries a definedness `fix` has defined, each with the round that defined it. Every
/// attempt shares the one map, so an attempt costs nothing for the entries it does not read.
type Defined = BTreeMap<Value, (Value, u64)>;

/// A name's binding in an environment.
#[derive(Clone)]
struct Binding<'t> {
    value: Slot<'t>,
    /// The fact the value came from, when provenance is recorded and it came from one.
    fact: Option<usize>,
}

/// What a name is bound to: a value, or a binding of the run's [`Globals`], by its position,
/// whose value is made when the name is first read ([`Machine::global`]).
#[derive(Clone)]
enum Slot<'t> {
    Is(V<'t>),
    Global(usize),
}

/// What a name read by a binding of [`Globals`], or by a term run under them, refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Global {
    /// The binding of the globals at this position.
    At(usize),
    /// A primitive, as the prelude binds its words.
    Prim(Prim),
}

/// Bindings kept in scope from one run to the next ([`Evaluator::run_under`]), innermost
/// last, each a literal, a lambda, a primitive or a name, with what each name it reads refers
/// to. A run makes a binding's value when it first reads the binding, at most once, so a run
/// costs the bindings it reaches, not all those in scope. Each such term gives its value in
/// one step, never fails and writes no port, so the value made when it is first read is the
/// value a `let` of it would bind at the start of the run.
#[derive(Debug, Default)]
pub struct Globals {
    entries: Vec<GlobalEntry>,
}

#[derive(Debug)]
struct GlobalEntry {
    term: Shared,
    reads: Vec<(Arc<str>, Global)>,
}

impl Globals {
    /// Binds `term`, whose free names are `reads`, next, and gives its position; or gives
    /// `None`, binding nothing, when `term` is not a literal, a lambda, a primitive or a name
    /// in `reads`, or a name in `reads` refers to a position not below it.
    pub fn push(&mut self, term: Shared, reads: Vec<(Arc<str>, Global)>) -> Option<usize> {
        let at = self.entries.len();
        let below = |&(_, g): &(Arc<str>, Global)| !matches!(g, Global::At(i) if i >= at);
        let value = match &*term {
            Term::Lit(_) | Term::Lam(..) | Term::PrimFn(_) => true,
            Term::Var(y) => reads.iter().any(|(x, _)| x == y),
            _ => false,
        };
        if !value || !reads.iter().all(below) {
            return None;
        }
        self.entries.push(GlobalEntry { term, reads });
        Some(at)
    }

    /// Removes the innermost binding.
    pub fn pop(&mut self) {
        self.entries.pop();
    }

    /// The number of bindings.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether there are none.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// The environment in which a binding of globals, or a term run under them, reads `reads`.
fn global_env<'t>(reads: &'t [(Arc<str>, Global)]) -> Env<'t> {
    let slot = |g: Global| match g {
        Global::At(i) => Slot::Global(i),
        Global::Prim(p) => Slot::Is(V::Prim(p)),
    };
    reads.iter().fold(None, |env, (x, g)| {
        let b = Binding {
            value: slot(*g),
            fact: None,
        };
        env::insert(env, x, b)
    })
}

fn bind<'t>(env: Env<'t>, name: &'t str, value: V<'t>, fact: Option<usize>) -> Env<'t> {
    let value = Slot::Is(value);
    env::insert(env, name, Binding { value, fact })
}

fn lookup_fact(env: &Env<'_>, name: &str) -> Option<usize> {
    env::get(env, name)?.fact
}

fn lookup<'t>(env: &Env<'t>, name: &str) -> Option<Slot<'t>> {
    Some(env::get(env, name)?.value.clone())
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

    /// Why the port does not take `key`, which stops the wave, asked before the key is
    /// compared with the keys read so far: a port whose keys may hold values whose comparison
    /// costs more than their memory refuses them here. By default a port takes every key.
    fn refuses(&self, key: &Value) -> Option<String> {
        let _ = key;
        None
    }

    /// Whether the port is called, `port(a, ..)`, rather than read, `port[k]`: a call asks the
    /// port at the tuple of its arguments as they are, a `-0.0` kept apart from `0.0`, and an
    /// argument holding a function at the value [`Lookup::function`] gives it. By default a
    /// port is read.
    fn calls(&self) -> bool {
        false
    }

    /// The value that stands in a called port's key for an argument holding the function whose
    /// body is `body`, when the port has one; without one the call stops the wave.
    fn function(&self, body: &Term) -> Option<Value> {
        let _ = body;
        None
    }

    /// Whether the port keeps its own answers, each key answered once, so the world does not
    /// keep them in [`World::reads`]. A port whose keys may hold values it compares more
    /// cheaply than by their bytes, such as joined strings named by
    /// [`crate::text::Names`], keeps its answers itself: a map of the world compares keys by
    /// [`Value`]'s order, which reads a long join byte by byte. By default the world keeps
    /// them.
    fn keeps_answers(&self) -> bool {
        false
    }
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
    /// The position of each node the run has reached, by its [`At`]: the root's is 0.
    nodes: Vec<Position>,
    /// The [`At`] of each position reached below the root, by its parent's and its child index.
    ids: HashMap<(At, u32), At>,
    term: Option<Term>,
    facts: Vec<Fact>,
    /// The positions of the call sites the run is inside, in a persistent vector that each
    /// fact's address shares rather than copies.
    calls: Vector<Position>,
    /// The keypath of the region instance the run is inside, shared the same way.
    keys: Vector<Value>,
    /// The facts read so far by the node being evaluated, one entry per subterm evaluated,
    /// `None` for a value that came from no fact, such as a family key.
    reads: Vec<Option<usize>>,
    /// The call site and the facts of the arguments of the next closure call.
    site: Option<At>,
    args: Vec<Option<usize>>,
    /// Which values the run's facts hold failures in, read as each fact is made.
    holds: Holds,
}

/// A position of the evaluated term during a run, numbered as the run reaches it: the run's own
/// name for the [`Position`] it stands for, which is what enters a fact address. Without
/// provenance every node is at 0.
type At = u32;

/// The reference evaluator, holding the world and the remaining fuel.
pub struct Evaluator {
    /// The ports.
    pub world: World,
    fuel: u64,
    /// Above zero while evaluating the closure of a pure region (`fam`, `reindex`,
    /// `discard`, `fold`, `fix`), where a port operation is a type error.
    pure: usize,
    schedule: Schedule,
    /// The number of definedness `fix` evaluations begun, which names each one's family.
    fixes: u64,
    trace: Option<Trace>,
    /// The source sites of the program's nodes (plan row RT-sites), when it has them.
    sites: Option<Arc<Sites>>,
    /// The site of the node the last run stopped at with an error, if it has one.
    failed: Option<Span>,
}

/// Evaluates a closed term with no ports and no fuel limit, expecting data.
pub fn eval(term: &Term) -> Result<Value, KernelError> {
    Evaluator::new(World::new()).run(term)
}

impl Evaluator {
    /// An evaluator over `world` with no fuel limit: a run takes as many steps as the term
    /// does (docs/thresholds.md, replacement 8). [`Evaluator::with_fuel`] sets one.
    pub fn new(world: World) -> Self {
        Evaluator {
            world,
            fuel: u64::MAX,
            pure: 0,
            schedule: Schedule::default(),
            fixes: 0,
            trace: None,
            sites: None,
            failed: None,
        }
    }

    /// Places each error of a run at the site `sites` gives its node ([`Evaluator::failed_at`]).
    pub fn set_sites(&mut self, sites: Option<Arc<Sites>>) {
        self.sites = sites;
    }

    /// The source site of the node the last run stopped at with an error: the node's own, or
    /// when it has none, that of the innermost call or primitive around it that has one; `None`
    /// when the run gave a value, the evaluator has no sites, or no node around the error has a
    /// site.
    pub fn failed_at(&self) -> Option<Span> {
        self.failed
    }

    /// Records the provenance of the next run (step L1.20), which
    /// [`Evaluator::provenance`] then returns. Every keypath begins with `root`, the wave
    /// stamp of a port region's wave, or nothing.
    pub fn with_provenance(mut self, root: Vec<Value>) -> Self {
        self.trace = Some(Trace {
            keys: root.into(),
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

    /// Evaluates a closed term, expecting data.
    pub fn run(&mut self, term: &Term) -> Result<Value, KernelError> {
        self.run_from(term, None, None)
    }

    /// Evaluates `term`, whose free names are `reads`, under `globals`, expecting data: what
    /// [`Evaluator::run`] gives of `term` under a `let` of each binding of `globals` it
    /// reaches, in time linear in the run and the bindings it reaches. It records no
    /// provenance, which places each node within one closed term.
    ///
    /// # Panics
    ///
    /// When provenance is asked for ([`Evaluator::with_provenance`]).
    pub fn run_under(
        &mut self,
        term: &Term,
        globals: &Globals,
        reads: &[(Arc<str>, Global)],
    ) -> Result<Value, KernelError> {
        assert!(
            self.trace.is_none(),
            "a run under globals records no provenance"
        );
        self.run_from(term, Some(globals), global_env(reads))
    }

    fn run_from<'t>(
        &mut self,
        term: &'t Term,
        globals: Option<&'t Globals>,
        env: Env<'t>,
    ) -> Result<Value, KernelError> {
        let mut marks = (0, 0);
        if let Some(t) = &mut self.trace {
            t.nodes = vec![Position::root()];
            t.ids.clear();
            t.facts.clear();
            t.holds = Holds::default();
            marks = (t.calls.len(), t.keys.len());
        }
        // The order of numbers inside family keys and comparisons asks the system for the
        // memory of its bounds while the run lives.
        let watch = crate::num::Watch::start();
        let mut machine = Machine {
            ev: self,
            frames: Vec::new(),
            drops: Rc::default(),
            globals,
            made: HashMap::new(),
            short_paths: Vec::new(),
            failed: None,
        };
        let out = machine.run(term, env);
        let failed = machine.failed;
        drop(machine);
        drop(watch);
        self.failed = failed.and_then(|k| self.sites.as_ref()?.at(k));
        if let Some(t) = &mut self.trace {
            // A run that stopped with an error left the regions it was inside.
            t.calls.truncate(marks.0);
            t.keys.truncate(marks.1);
            t.holds = Holds::default();
            if out.is_ok() {
                t.term = Some(term.clone());
            }
        }
        match out {
            Ok(V::Data(v)) => Ok(v),
            Ok(V::Held(_)) => Err(KernelError::Type(
                "the program's result holds a function".into(),
            )),
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

    /// The fact of the value the last subterm evaluated gave.
    fn last_fact(&self) -> Option<usize> {
        self.trace.as_ref()?.reads.last().copied().flatten()
    }

    /// The position of child `i` of the node at `at`, when provenance is recorded.
    fn child(&mut self, at: At, i: usize) -> At {
        let Some(t) = &mut self.trace else {
            return 0;
        };
        let i = u32::try_from(i).expect("a node has fewer than 2^32 children");
        let next = At::try_from(t.nodes.len()).expect("a run reaches fewer than 2^32 positions");
        *t.ids.entry((at, i)).or_insert_with(|| {
            t.nodes.push(t.nodes[at as usize].child(i));
            next
        })
    }

    /// Names the call site and the argument facts of the next closure call.
    // Complexity tradeoff (KERNEL-eval-step-cost): this took the facts as a `Vec`, which each
    // caller allocated (`vec![from; 2]`) and dropped unread when provenance is not traced, the
    // common case: an allocation and a free, about 250 instructions, on each call of a key map,
    // value map, test or operator (158,000 in law_04). Used: a slice, copied into a `Vec` only
    // when traced; the traced cost is the same allocation, and the untraced one is none.
    fn aim(&mut self, site: Option<At>, args: &[Option<usize>]) {
        if let Some(t) = &mut self.trace {
            t.site = site;
            t.args = args.to_vec();
        }
    }

    /// Enters the region instance at `keys`, below the current one.
    fn enter(&mut self, keys: &[Value]) {
        if let Some(t) = &mut self.trace {
            t.keys.extend(keys.iter().cloned());
        }
    }

    /// Leaves the last `n` coordinates of the keypath.
    fn leave(&mut self, n: usize) {
        if let Some(t) = &mut self.trace {
            t.keys.truncate(t.keys.len() - n);
        }
    }

    fn check_impure(&self, port: &str) -> R<()> {
        if self.pure > 0 {
            return type_err(format!("port `{port}` used inside a pure region"));
        }
        Ok(())
    }
}

/// What the machine does next.
enum Step<'t> {
    /// Evaluates a term at a position.
    Eval(&'t Term, At, Env<'t>),
    /// Evaluates a function's body, called from `site` when provenance is recorded.
    Call {
        body: &'t Term,
        at: At,
        env: Env<'t>,
        site: Option<At>,
    },
    /// Evaluates an undefined entry where an attempt reads it.
    Demand(Rc<Definedness<'t>>, Value),
    /// Gives a value to the frame on top of the stack.
    Give(V<'t>),
}

fn give<'t>(v: Value) -> R<Step<'t>> {
    Ok(Step::Give(V::Data(v)))
}

fn data(v: V<'_>) -> R<Value> {
    match v {
        V::Data(v) => Ok(v),
        _ => type_err("expected data, found a function"),
    }
}

fn family(v: Value) -> R<Family> {
    match v {
        Value::Family(f) => Ok(f),
        other => type_err(format!(
            "expected a family, found a value of type `{}`",
            other.kind_type()
        )),
    }
}

/// A suspended evaluation: what is left to do when the term above it on the stack has ended.
enum Frame<'t> {
    /// Records the fact of `term` when it gives a value. `outer` holds the reads of the node
    /// around it, which go back in place however the term ended.
    /// `union` when the term is a union, whose value holds a failure exactly when one of its two
    /// operands does.
    Fact {
        at: At,
        outer: Vec<Option<usize>>,
        union: bool,
    },
    /// Ends a pure region.
    Pure,
    /// Leaves a call that recorded its call site.
    Return,
    /// Ends an attempt at an entry of a definedness `fix`.
    Entry(Box<Entry<'t>>),
    /// Goes on with the value given; an error passes through.
    Wait(Wait<'t>),
}

/// A frame with nothing to do unless the term above it gives a value.
enum Wait<'t> {
    /// The function of a call has its value; its arguments come next.
    Fun {
        at: At,
        args: &'t [Term],
        env: Env<'t>,
    },
    /// An argument has its value. For a call, `done` begins with the function.
    Args {
        head: Head,
        /// The position of the call or primitive; the next argument is its child `done.len()`.
        at: At,
        rest: &'t [Term],
        done: Vec<V<'t>>,
        env: Env<'t>,
    },
    Let {
        name: &'t str,
        body: &'t Term,
        at: At,
        env: Env<'t>,
    },
    If {
        a: &'t Term,
        b: &'t Term,
        at: At,
        env: Env<'t>,
    },
    Match {
        arms: &'t [(Pattern, Term)],
        at: At,
        env: Env<'t>,
    },
    Push(&'t Arc<str>),
    /// An operand of `region` has its value.
    Operand {
        region: &'t Term,
        /// The region's position; the next operand is its child `done.len()`.
        at: At,
        done: Vec<V<'t>>,
        from: Option<usize>,
        env: Env<'t>,
    },
    Fam(Box<Fam<'t>>),
    ReindexKey(Box<Reindex<'t>>),
    ReindexValue(Box<Reindex<'t>>),
    Discard(Box<Discard<'t>>),
    Fold(Box<Fold<'t>>),
    LatticeStep(Box<Lattice<'t>>),
    LatticeJoin(Box<Lattice<'t>>),
    GenStep(Box<Gen<'t>>),
    GenGuard(Box<Gen<'t>>),
}

/// What receives the arguments of [`Wait::Args`].
#[derive(Clone, Copy)]
enum Head {
    App,
    Prim(Prim),
}

/// A function operand of a region, with its call site.
type Operator<'t> = (V<'t>, Option<At>);

/// A `fam` running: the keys left, and the entries made.
struct Fam<'t> {
    keys: std::vec::IntoIter<Value>,
    key: Option<Value>,
    var: &'t str,
    body: &'t Term,
    /// The body's position.
    at: At,
    env: Env<'t>,
    out: Vec<(Keypath, Value)>,
}

/// A `reindex` running: the leaves left, the leaf being moved and its new key.
struct Reindex<'t> {
    leaves: std::vec::IntoIter<(Keypath, Value)>,
    kf: Operator<'t>,
    vf: Operator<'t>,
    from: Option<usize>,
    /// The path, the path as a value and the value of the leaf being moved.
    path: Keypath,
    args: Option<(Value, Value)>,
    key: Option<Value>,
    /// Whether the leaf being moved is a keypath that ends early, above an empty level.
    short: bool,
    out: Vec<(Keypath, Value)>,
}

/// One level of a `discard` running: the entries left and the entry being tested.
struct Level {
    entries: std::vec::IntoIter<(Value, Value)>,
    entry: Option<Value>,
    out: Vec<(Keypath, Value)>,
}

/// A `discard` running: the levels entered, each a family nested in the one before, and the
/// keypath of the entry being tested.
struct Discard<'t> {
    levels: Vec<Level>,
    prefix: Keypath,
    sel: Operator<'t>,
    from: Option<usize>,
}

/// A `fold` running: the levels left, each with the keypath above it, and the level being
/// reduced.
struct Fold<'t> {
    groups: std::vec::IntoIter<(Keypath, Vec<Value>)>,
    op: Operator<'t>,
    from: Option<usize>,
    identity: Option<Value>,
    /// Whether the family has one level, so that the result is the level's, not a family.
    whole: bool,
    path: Keypath,
    tree: Option<CanonicalTree<Value>>,
    step: i64,
    out: Vec<(Keypath, Value)>,
}

/// A lattice `fix` running: `x` is iterate `i`, and `from` its fact.
struct Lattice<'t> {
    x: Value,
    from: Option<usize>,
    i: i64,
    step: Operator<'t>,
    join: Operator<'t>,
}

/// A `gen` running.
struct Gen<'t> {
    frames: Vec<Value>,
    from: Option<usize>,
    step: Operator<'t>,
    guard: Operator<'t>,
}

/// A definedness `fix` running in rounds: the entries left in this round, those for the next,
/// and for each undefined entry read, the entries waiting on it.
struct Rounds<'t> {
    fix: Rc<Definedness<'t>>,
    rng: Option<SplitMix>,
    waiting: BTreeMap<Value, Vec<Value>>,
    queue: std::vec::IntoIter<Value>,
    ready: Vec<Value>,
    defined: Vec<Value>,
    round: u64,
    sees: u64,
}

/// A definedness `fix` running by demand: the keys from `next` on, in the order of its domain,
/// are not yet demanded.
struct Pull<'t> {
    fix: Rc<Definedness<'t>>,
    next: usize,
}

/// What an attempt at an entry goes back to.
enum By<'t> {
    Round(Box<Rounds<'t>>),
    Pull(Box<Pull<'t>>),
    /// A read in another attempt, with the trace state that attempt had.
    Demand(Rc<Definedness<'t>>, Option<Saved>),
}

impl<'t> By<'t> {
    /// The `fix` whose entry is attempted.
    fn fix(&self) -> &Rc<Definedness<'t>> {
        match self {
            By::Round(st) => &st.fix,
            By::Pull(st) => &st.fix,
            By::Demand(fix, _) => fix,
        }
    }
}

/// The part of [`Trace`] an entry demanded where it is read swaps for that of its `fix`.
struct Saved {
    calls: Vector<Position>,
    keys: Vector<Value>,
    reads: Vec<Option<usize>>,
    site: Option<At>,
    args: Vec<Option<usize>>,
}

/// An attempt at the entry at `k` of the `fix` of `by`. `mark` holds the lengths of the trace's
/// facts, calls and keys when it began.
struct Entry<'t> {
    k: Value,
    mark: Option<(usize, usize, usize)>,
    by: By<'t>,
}

/// One run: the evaluator and the stack of what is left to do.
struct Machine<'e, 't> {
    ev: &'e mut Evaluator,
    frames: Vec<Frame<'t>>,
    drops: Rc<Drops<'t>>,
    /// The bindings the run is under ([`Evaluator::run_under`]).
    globals: Option<&'t Globals>,
    /// The value of each of them made so far, by position.
    made: HashMap<usize, V<'t>>,
    /// The sequence ids of the keypaths above an empty level whose `reindex` key map is
    /// running, innermost last: `pathKey` past the end of one of them reads [`unbound`]. One
    /// entry per `reindex` nested inside a key map, so a few.
    short_paths: Vec<crate::value::Id>,
    /// The name ([`crate::sites::key`]) of the node the run stopped at with an error, once it
    /// has: the node whose own work failed, or the innermost call or primitive around the
    /// error that has a site. Set at the first error, which ends the run.
    failed: Option<usize>,
}

impl<'t> Machine<'_, 't> {
    fn run(&mut self, term: &'t Term, env: Env<'t>) -> R<V<'t>> {
        let mut step = Ok(Step::Eval(term, 0, env));
        loop {
            let out = match step {
                Ok(Step::Eval(term, at, env)) => {
                    step = self.eval(term, at, env);
                    continue;
                }
                Ok(Step::Call {
                    body,
                    at,
                    env,
                    site,
                }) => {
                    if let (Some(t), Some(site)) = (&mut self.ev.trace, site) {
                        t.calls.push_back(t.nodes[site as usize].clone());
                        self.frames.push(Frame::Return);
                    }
                    step = self.eval(body, at, env);
                    continue;
                }
                Ok(Step::Demand(fix, k)) => {
                    step = self.demand(fix, k);
                    continue;
                }
                Ok(Step::Give(v)) => match refused() {
                    None => Ok(v),
                    Some((t, e)) => Err(test_too_large(None, t, e).into()),
                },
                // A stop after a refused test may follow from the answer the test was given.
                Err(stop) => match refused() {
                    None => Err(stop),
                    Some((t, e)) => Err(test_too_large(None, t, e).into()),
                },
            };
            if let Err(Stop::Error(_)) = out {
                self.fail(None);
            }
            step = match self.frames.pop() {
                Some(frame) => self.resume(frame, out),
                None => return out,
            };
        }
    }

    /// Records the node the run stopped at, once, when the evaluator has sites: `node` when
    /// it has a site, else the innermost call, primitive or `match` waiting on the frames that
    /// has one. O(1) for a node with a site, and at most one walk of the frames per run, since
    /// an error ends the run.
    // Complexity tradeoff: a node with no parts of its own (a variable, a literal) has no key
    // and so no site, and an error there is placed by the frames around it, O(d) once for d
    // frames, where giving every node a key would cost a word in each `Term` and change its
    // identity, which the sites must leave as it was (plan row RT-sites). Trigger: an error
    // raised by a node with no site; one walk per run, since the error ends the run. Test:
    // `l01_36a_executables::sites` (each error kind placed, the same as natively).
    fn fail(&mut self, node: Option<usize>) {
        let Some(sites) = &self.ev.sites else {
            return;
        };
        if self.failed.is_some() {
            return;
        }
        if let Some(k) = node
            && sites.at(k).is_some()
        {
            self.failed = Some(k);
            return;
        }
        if node.is_some() {
            // The node has no site: the frames around it are scanned when the error reaches
            // the run loop.
            return;
        }
        self.failed = self.frames.iter().rev().find_map(|f| {
            let k = match f {
                Frame::Wait(Wait::Args { rest, .. }) => crate::sites::end(rest),
                Frame::Wait(Wait::Fun { args, .. }) => crate::sites::end(args),
                Frame::Wait(Wait::Match { arms, .. }) => crate::sites::end(arms),
                _ => return None,
            };
            sites.at(k).map(|_| k)
        });
        // No site anywhere: the frame walk is not repeated as the error passes each frame.
        if self.failed.is_none() {
            self.failed = Some(0);
        }
    }

    fn wait(&mut self, wait: Wait<'t>) {
        self.frames.push(Frame::Wait(wait));
    }

    /// The value of the binding of the globals at position `i`, made the first time it is read.
    /// A name is followed down to the binding it names, each binding on the way given the same
    /// value; [`Globals::push`] keeps each name in its reads and each read below it, so the
    /// walk ends.
    fn global(&mut self, mut i: usize) -> V<'t> {
        let globals = self.globals.expect("a slot of globals in a run under them");
        let mut names = Vec::new();
        let v = loop {
            if let Some(v) = self.made.get(&i) {
                break v.clone();
            }
            let g = &globals.entries[i];
            let v = match &*g.term {
                Term::Lit(v) => V::Data(v.clone()),
                Term::PrimFn(p) => V::Prim(*p),
                Term::Lam(params, body) => V::Closure(Rc::new(Closure {
                    params,
                    body,
                    at: 0,
                    env: global_env(&g.reads),
                    drops: self.drops.clone(),
                })),
                Term::Var(y) => {
                    names.push(i);
                    match g.reads.iter().find(|(x, _)| x == y).map(|&(_, r)| r) {
                        Some(Global::At(j)) => {
                            i = j;
                            continue;
                        }
                        Some(Global::Prim(p)) => break V::Prim(p),
                        None => unreachable!("Globals::push keeps a name in its reads"),
                    }
                }
                _ => unreachable!("Globals::push takes a literal, lambda, primitive or name"),
            };
            self.made.insert(i, v.clone());
            break v;
        };
        for j in names {
            self.made.insert(j, v.clone());
        }
        v
    }

    /// Goes on from `frame` with how the term above it ended.
    fn resume(&mut self, frame: Frame<'t>, out: R<V<'t>>) -> R<Step<'t>> {
        match frame {
            Frame::Fact { at, outer, union } => self.fact(at, outer, union, out),
            Frame::Pure => {
                self.ev.pure -= 1;
                out.map(Step::Give)
            }
            Frame::Return => {
                if let Some(t) = &mut self.ev.trace {
                    t.calls.pop_back();
                }
                out.map(Step::Give)
            }
            Frame::Entry(entry) => self.entry_ended(*entry, out),
            Frame::Wait(wait) => self.go_on(wait, out?),
        }
    }

    /// Evaluates `term`, and when provenance is recorded, sets up the recording of its fact,
    /// whose inputs are the facts its subterms read. A variable is an edge, not a node: it
    /// passes on the fact of the value it names.
    fn eval(&mut self, term: &'t Term, at: At, env: Env<'t>) -> R<Step<'t>> {
        let Some(t) = &mut self.ev.trace else {
            return self.node(term, at, env);
        };
        if let Term::Var(name) = term {
            let fact = lookup_fact(&env, name);
            let out = self.node(term, at, env);
            if out.is_ok() {
                let t = self.ev.trace.as_mut().expect("provenance is recorded");
                t.reads.push(fact);
            }
            return out;
        }
        let outer = std::mem::take(&mut t.reads);
        let union = matches!(term, Term::Prim(Prim::Union, _));
        self.frames.push(Frame::Fact { at, outer, union });
        self.node(term, at, env)
    }

    fn fact(
        &mut self,
        at: At,
        outer: Vec<Option<usize>>,
        union: bool,
        out: R<V<'t>>,
    ) -> R<Step<'t>> {
        let t = self.ev.trace.as_mut().expect("provenance is recorded");
        let inputs = std::mem::replace(&mut t.reads, outer);
        let v = out?;
        let mut node = t.calls.clone();
        node.push_back(t.nodes[at as usize].clone());
        let value = match &v {
            V::Data(d) => Some(d.clone()),
            _ => None,
        };
        // The two reads of a union are the facts of its operands, whose data were read when they
        // were made: whether its value holds a failure is known unread, where a family made from
        // one holding none would be read by the difference of the two (`Holds`).
        let of_operands = union
            && matches!(value, Some(Value::Family(_)))
            && inputs.len() == 2
            && inputs
                .iter()
                .all(|i| i.is_some_and(|i| t.facts[i].value.is_some()));
        let holds_failure = match &value {
            Some(d) if of_operands => {
                let holds = inputs.iter().flatten().any(|&i| t.facts[i].holds_failure);
                t.holds.set(d, holds);
                holds
            }
            Some(d) => t.holds.of(d),
            None => false,
        };
        t.facts.push(Fact {
            address: FactAddress {
                node: NodeAddress(node),
                keypath: t.keys.clone(),
            },
            value,
            inputs: inputs.into_iter().flatten().collect(),
            holds_failure,
        });
        let id = t.facts.len() - 1;
        t.reads.push(Some(id));
        Ok(Step::Give(v))
    }

    fn node(&mut self, term: &'t Term, at: At, env: Env<'t>) -> R<Step<'t>> {
        match term {
            Term::Lit(v) => give(v.clone()),
            Term::Var(name) => match lookup(&env, name) {
                Some(Slot::Is(v)) => Ok(Step::Give(v)),
                Some(Slot::Global(i)) => Ok(Step::Give(self.global(i))),
                None => type_err(format!("unbound variable `{name}`")),
            },
            Term::Lam(params, body) => Ok(Step::Give(V::Closure(Rc::new(Closure {
                params,
                body,
                at: self.ev.child(at, 0),
                env,
                drops: self.drops.clone(),
            })))),
            Term::PrimFn(p) => Ok(Step::Give(V::Prim(*p))),
            Term::App(f, args) => {
                self.wait(Wait::Fun {
                    at,
                    args,
                    env: env.clone(),
                });
                Ok(Step::Eval(f, self.ev.child(at, 0), env))
            }
            Term::Prim(p, args) => {
                let done = Vec::with_capacity(args.len());
                self.args(Head::Prim(*p), at, args, done, env)
            }
            Term::Let(name, e, body) => {
                self.wait(Wait::Let {
                    name,
                    body,
                    at,
                    env: env.clone(),
                });
                Ok(Step::Eval(e, self.ev.child(at, 0), env))
            }
            Term::If(c, a, b) => {
                self.wait(Wait::If {
                    a,
                    b,
                    at,
                    env: env.clone(),
                });
                Ok(Step::Eval(c, self.ev.child(at, 0), env))
            }
            Term::Match(scrutinee, arms) => {
                self.wait(Wait::Match {
                    arms,
                    at,
                    env: env.clone(),
                });
                Ok(Step::Eval(scrutinee, self.ev.child(at, 0), env))
            }
            Term::Fix { .. } => {
                self.begin_pure();
                self.operand(term, at, Vec::new(), None, env)
            }
            Term::Fam { .. }
            | Term::Reindex { .. }
            | Term::Discard { .. }
            | Term::Fold { .. }
            | Term::Gen { .. } => self.operand(term, at, Vec::new(), None, env),
            Term::Read(port) => {
                self.ev.check_impure(port)?;
                match self.ev.world.inputs.get(&**port) {
                    Some(v) => give(v.clone()),
                    None if self.ev.world.sources.contains_key(&**port) => {
                        Ok(Step::Give(V::Source(port.clone())))
                    }
                    None => Err(KernelError::UnknownPort(port.to_string()).into()),
                }
            }
            Term::Push(port, value) => {
                self.wait(Wait::Push(port));
                Ok(Step::Eval(value, self.ev.child(at, 0), env))
            }
        }
    }

    fn begin_pure(&mut self) {
        self.ev.pure += 1;
        self.frames.push(Frame::Pure);
    }

    /// Evaluates the next of `rest`, or does what `head` does with `done`. The evaluation of
    /// the last argument takes the environment, so that a frame does not hold it longer.
    fn args(
        &mut self,
        head: Head,
        at: At,
        rest: &'t [Term],
        done: Vec<V<'t>>,
        env: Env<'t>,
    ) -> R<Step<'t>> {
        let Some((first, rest)) = rest.split_first() else {
            let out = self.finish(head, at, done);
            if let Err(Stop::Error(_)) = out {
                // `rest` is empty and ends where the node's arguments end, so it names the node.
                self.fail(Some(crate::sites::end(rest)));
            }
            return out;
        };
        let kept = if rest.is_empty() { None } else { env.clone() };
        let first_at = self.ev.child(at, done.len());
        self.wait(Wait::Args {
            head,
            at,
            rest,
            done,
            env: kept,
        });
        Ok(Step::Eval(first, first_at, env))
    }

    fn finish(&mut self, head: Head, at: At, mut done: Vec<V<'t>>) -> R<Step<'t>> {
        match head {
            Head::Prim(p) => self.prim(p, done),
            Head::App => {
                let f = done.remove(0);
                if let Some(t) = &mut self.ev.trace {
                    t.site = Some(at);
                    t.args = t.reads[t.reads.len() - done.len()..].to_vec();
                }
                self.apply(&f, done)
            }
        }
    }

    /// The operands of a region, the terms it evaluates before it begins, in order.
    fn operands(region: &'t Term) -> [Option<&'t Term>; 3] {
        match region {
            Term::Fam { domain, .. } => [Some(domain), None, None],
            Term::Reindex { family, kf, vf, .. } => [Some(family), Some(kf), Some(vf)],
            Term::Discard { family, sel } => [Some(family), Some(sel), None],
            Term::Fold {
                family,
                op,
                identity,
                ..
            } => [Some(family), Some(op), identity.as_ref()],
            Term::Fix {
                init,
                step,
                kind: FixKind::Lattice { join },
                ..
            } => [Some(init), Some(step), Some(join)],
            Term::Fix { init, .. } => [Some(init), None, None],
            Term::Gen {
                init, step, guard, ..
            } => [Some(init), Some(step), Some(guard)],
            _ => unreachable!("only a region has operands"),
        }
        .map(|t| t.map(|t| &**t))
    }

    /// Evaluates the next operand of `region`, or begins it when none is left.
    fn operand(
        &mut self,
        region: &'t Term,
        at: At,
        done: Vec<V<'t>>,
        from: Option<usize>,
        env: Env<'t>,
    ) -> R<Step<'t>> {
        match Self::operands(region).get(done.len()).copied().flatten() {
            Some(t) => {
                let t_at = self.ev.child(at, done.len());
                self.wait(Wait::Operand {
                    region,
                    at,
                    done,
                    from,
                    env: env.clone(),
                });
                Ok(Step::Eval(t, t_at, env))
            }
            None => self.begin(region, at, done, from, env),
        }
    }

    /// The operand `i` of `region` has its value: the operands that must be data, and the
    /// first that must be a family, are checked here, before the next is evaluated.
    fn check_operand(region: &Term, i: usize, v: V<'t>) -> R<V<'t>> {
        let holds_data = !matches!(
            region,
            Term::Gen { .. }
                | Term::Fix {
                    kind: FixKind::Lattice { .. },
                    ..
                }
        );
        match i {
            0 if holds_data => Ok(V::Data(Value::Family(family(data(v)?)?))),
            0 => Ok(V::Data(data(v)?)),
            2 if matches!(region, Term::Fold { .. }) => Ok(V::Data(data(v)?)),
            _ => Ok(v),
        }
    }

    /// Begins `region` with its operands evaluated: `from` is the fact of the first. Operand
    /// `i` is the region's child `i`, and a `fam` or a definedness `fix` evaluates its child 1
    /// for each key.
    fn begin(
        &mut self,
        region: &'t Term,
        at: At,
        operands: Vec<V<'t>>,
        from: Option<usize>,
        env: Env<'t>,
    ) -> R<Step<'t>> {
        let mut operands = operands.into_iter();
        let mut next = || operands.next().expect("the operands of a region");
        let first = data(next())?;
        match region {
            Term::Fam { var, body, .. } => {
                self.begin_pure();
                let keys: Vec<Value> = family(first)?.keys().cloned().collect();
                let out = Vec::with_capacity(keys.len());
                let at = self.ev.child(at, 1);
                self.fam(Box::new(Fam {
                    keys: keys.into_iter(),
                    key: None,
                    var,
                    body,
                    at,
                    env,
                    out,
                }))
            }
            Term::Reindex { .. } => {
                let kf = (next(), Some(self.ev.child(at, 1)));
                let vf = (next(), Some(self.ev.child(at, 2)));
                self.begin_pure();
                self.reindex(Box::new(Reindex {
                    leaves: family(first)?.leaves().into_iter(),
                    kf,
                    vf,
                    from,
                    path: Vec::new(),
                    args: None,
                    key: None,
                    short: false,
                    out: Vec::new(),
                }))
            }
            Term::Discard { .. } => {
                let sel = (next(), Some(self.ev.child(at, 1)));
                self.begin_pure();
                self.discard(Box::new(Discard {
                    levels: vec![level(&family(first)?)],
                    prefix: Vec::new(),
                    sel,
                    from,
                }))
            }
            Term::Fold {
                identity, depth, ..
            } => {
                let op = (next(), Some(self.ev.child(at, 1)));
                let identity = match identity {
                    Some(_) => Some(data(next())?),
                    None => None,
                };
                self.begin_pure();
                self.begin_fold(family(first)?, op, from, identity, *depth)
            }
            Term::Fix {
                step,
                this,
                key,
                kind,
                ..
            } => match kind {
                FixKind::Lattice { .. } => {
                    let step = (next(), Some(self.ev.child(at, 1)));
                    let join = (next(), Some(self.ev.child(at, 2)));
                    self.lattice(Box::new(Lattice {
                        x: first,
                        from,
                        i: 0,
                        step,
                        join,
                    }))
                }
                FixKind::Definedness => {
                    let at = self.ev.child(at, 1);
                    self.begin_definedness(first, step, at, this, key, env)
                }
            },
            Term::Gen { pos, .. } => {
                let step = (next(), Some(self.ev.child(at, 1)));
                let guard = (next(), Some(self.ev.child(at, 2)));
                let st = Box::new(Gen {
                    frames: vec![first],
                    from,
                    step,
                    guard,
                });
                match pos {
                    GuardPos::Before => self.gen_guard(st),
                    GuardPos::After => self.gen_step(st),
                }
            }
            _ => unreachable!("only a region has operands"),
        }
    }

    /// Goes on with the value `v` that the term above `wait` gave.
    fn go_on(&mut self, wait: Wait<'t>, v: V<'t>) -> R<Step<'t>> {
        match wait {
            Wait::Fun { at, args, env } => {
                let mut done = Vec::with_capacity(args.len() + 1);
                done.push(v);
                self.args(Head::App, at, args, done, env)
            }
            Wait::Args {
                head,
                at,
                rest,
                mut done,
                env,
            } => {
                done.push(v);
                self.args(head, at, rest, done, env)
            }
            Wait::Let {
                name,
                body,
                at,
                env,
            } => {
                let fact = self.ev.last_fact();
                let at = self.ev.child(at, 1);
                Ok(Step::Eval(body, at, bind(env, name, v, fact)))
            }
            // An atom that holds a function passes through as any atom does.
            Wait::If { .. } if held_atom(&v) => Ok(Step::Give(v)),
            Wait::If { a, b, at, env } => match data(v)? {
                Value::Bool(true) => Ok(Step::Eval(a, self.ev.child(at, 1), env)),
                Value::Bool(false) => Ok(Step::Eval(b, self.ev.child(at, 2), env)),
                atom @ Value::Atom(_) => give(atom),
                other => type_err(format!("`if` on a value of type `{}`", other.kind_type())),
            },
            Wait::Match { arms, at, env } => {
                let fact = self.ev.last_fact();
                for (i, (pat, body)) in arms.iter().enumerate() {
                    let mut env2 = env.clone();
                    let hit = matches_any(pat, &v, &mut env2, fact);
                    // A literal pattern whose test was refused its memory gave no answer.
                    if let Some((t, e)) = refused() {
                        return Err(test_too_large(Some("match"), t, e).into());
                    }
                    if hit {
                        return Ok(Step::Eval(body, self.ev.child(at, 1 + i), env2));
                    }
                }
                match v {
                    V::Data(v) => type_err(format!(
                        "no arm matches a value of type `{}`",
                        v.kind_type()
                    )),
                    V::Held(_) => type_err("no arm matches the value that holds a function"),
                    _ => type_err("no arm matches the function"),
                }
            }
            Wait::Push(port) => {
                let value = data(v)?;
                self.ev.check_impure(port)?;
                let Some(out) = self.ev.world.outputs.get_mut(&**port) else {
                    return Err(KernelError::UnknownPort(port.to_string()).into());
                };
                if out.capacity.is_some_and(|c| out.log.len() >= c) {
                    return give(Value::atom("full"));
                }
                out.log.push(value);
                give(Value::atom("ok"))
            }
            Wait::Operand {
                region,
                at,
                mut done,
                from,
                env,
            } => {
                done.push(Self::check_operand(region, done.len(), v)?);
                let from = if done.len() == 1 {
                    self.ev.last_fact()
                } else {
                    from
                };
                self.operand(region, at, done, from, env)
            }
            Wait::Fam(mut st) => {
                self.ev.leave(1);
                let k = st.key.take().expect("a `fam` has a key in hand");
                st.out.push((vec![k], data(v)?));
                self.fam(st)
            }
            Wait::ReindexKey(mut st) if st.short => {
                // A keypath above an empty level has no leaf for the value map; the empty level
                // goes beneath the part of the new keypath that its own keys give.
                st.args = None;
                self.short_paths.pop();
                self.ev.leave(st.path.len());
                if let Some(path) = placed(data(v)?) {
                    st.out.push((path, Value::Family(Family::new())));
                }
                self.reindex(st)
            }
            Wait::ReindexKey(mut st) => {
                st.key = Some(data(v)?);
                let (p, leaf) = st.args.take().expect("a `reindex` has a leaf in hand");
                self.ev.aim(st.vf.1, &[st.from; 2]);
                let step = self.call2(&st.vf.0, p, leaf);
                self.wait(Wait::ReindexValue(st));
                step
            }
            Wait::ReindexValue(mut st) => {
                let value = data(v)?;
                self.ev.leave(st.path.len());
                let key = key_of(st.key.take().expect("a `reindex` has a key in hand"));
                st.out.push((key, value));
                self.reindex(st)
            }
            Wait::Discard(st) => self.discarded(st, v),
            Wait::Fold(mut st) => {
                self.ev.leave(1);
                let value = data(v)?;
                st.tree.as_mut().expect("a level in hand").give(value);
                self.fold(st)
            }
            Wait::LatticeStep(st) => {
                let next_fact = self.ev.last_fact();
                self.ev.aim(st.join.1, &[st.from, next_fact]);
                let V::Data(next) = v else {
                    return type_err("a fix step returned a function");
                };
                let step = self.call2(&st.join.0, st.x.clone(), next);
                self.wait(Wait::LatticeJoin(st));
                step
            }
            Wait::LatticeJoin(mut st) => {
                self.ev.leave(1);
                let joined = data(v)?;
                st.from = self.ev.last_fact();
                let same = joined == st.x;
                // The fixpoint test of an iterate whose test was refused its memory gave no answer.
                if let Some((t, e)) = refused() {
                    return Err(test_too_large(Some("fix"), t, e).into());
                }
                if same {
                    return give(st.x);
                }
                st.x = joined;
                st.i += 1;
                self.lattice(st)
            }
            Wait::GenStep(mut st) => {
                self.ev.leave(1);
                let V::Data(next) = v else {
                    return type_err("a gen step returned a function");
                };
                st.frames.push(next);
                st.from = self.ev.last_fact();
                self.gen_guard(st)
            }
            Wait::GenGuard(mut st) => {
                self.ev.leave(1);
                match v {
                    V::Data(Value::Bool(true)) => self.gen_step(st),
                    V::Data(Value::Bool(false)) => gen_end(*st),
                    V::Data(end @ Value::Atom(_)) => {
                        st.frames.push(end);
                        gen_end(*st)
                    }
                    V::Data(other) => type_err(format!(
                        "a gen guard returned a value of type `{}`",
                        other.kind_type()
                    )),
                    _ => type_err("a gen guard returned a function"),
                }
            }
        }
    }

    fn apply(&mut self, f: &V<'t>, args: Vec<V<'t>>) -> R<Step<'t>> {
        self.ev.burn()?;
        let (site, facts) = match &mut self.ev.trace {
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
                let mut env = c.env.clone();
                let facts = facts.into_iter().chain(std::iter::repeat(None));
                for ((p, a), fact) in c.params.iter().zip(args).zip(facts) {
                    env = bind(env, p, a, fact);
                }
                Ok(Step::Call {
                    body: c.body,
                    at: c.at,
                    env,
                    site,
                })
            }
            V::Prim(p) => self.prim(*p, args),
            V::Source(port) if self.ev.world.sources[&**port].calls() => self.call_port(port, args),
            // Until types arrive (step L1.22), the elaboration of `v[k]` cannot tell a family
            // from a function, so a family or a lookup port applied to one key reads it.
            V::Source(_) | V::Data(Value::Family(_)) if args.len() == 1 => {
                let mut with_family = Vec::with_capacity(1 + args.len());
                with_family.push(f.clone());
                with_family.extend(args);
                self.prim(Prim::Get, with_family)
            }
            // `t[k]` with `k` no literal elaborates to an application too; a tuple applied to
            // one key reads the component at it (DESIGN.md sec:types, the `m[k]` row).
            V::Data(Value::Tuple(_)) if args.len() == 1 => {
                let mut with_tuple = Vec::with_capacity(2);
                with_tuple.push(f.clone());
                with_tuple.extend(args);
                self.prim(Prim::TupleGet, with_tuple)
            }
            V::Held(h) if h.atom.is_none() && args.len() == 1 => {
                let mut with_tuple = Vec::with_capacity(2);
                with_tuple.push(f.clone());
                with_tuple.extend(args);
                self.prim(Prim::TupleGet, with_tuple)
            }
            V::Partial(_) | V::Source(_) => type_err("a family is read with `[]`, not called"),
            V::Data(Value::Atom(a)) => Ok(Step::Give(V::Data(Value::Atom(a.clone())))),
            V::Held(h) if h.atom.is_some() => Ok(Step::Give(f.clone())),
            V::Held(_) => type_err("a tuple is read at one key"),
            V::Data(other) => type_err(format!(
                "a value of type `{}` is not a function",
                other.kind_type()
            )),
        }
    }

    /// The answer of the lookup port `port` at the key `k`: the world answers once, and the
    /// answer is kept.
    fn ask_port(&mut self, port: &str, k: Cow<'_, Value>) -> R<Step<'t>> {
        let world = &mut self.ev.world;
        let source = &world.sources[port];
        if let Some(why) = source.refuses(&k) {
            return Err(KernelError::Port(port.to_string(), why).into());
        }
        if source.keeps_answers() {
            let v = source
                .get(&k)
                .map_err(|why| KernelError::Port(port.to_string(), why))?;
            return give(v);
        }
        if let Some(v) = world.reads.get(port).and_then(|r| r.get(&*k)) {
            return give(v.clone());
        }
        let v = world.sources[port]
            .get(&k)
            .map_err(|why| KernelError::Port(port.to_string(), why))?;
        let reads = world.reads.entry(port.to_string()).or_default();
        reads.insert(k.into_owned(), v.clone());
        give(v)
    }

    /// The call `port(args)` of a called lookup port ([`Lookup::calls`]): the port is asked at
    /// the tuple of the arguments as they are, each function among them at the value the port
    /// gives it.
    fn call_port(&mut self, port: &str, args: Vec<V<'t>>) -> R<Step<'t>> {
        self.ev.check_impure(port)?;
        let source = &self.ev.world.sources[port];
        let mut key = Vec::with_capacity(args.len());
        for a in args {
            let v = match a {
                V::Data(v) => Some(v),
                V::Closure(c) => source.function(c.body),
                _ => None,
            };
            let Some(v) = v else {
                let why = "an argument holding a function the port does not take".into();
                return Err(KernelError::Port(port.to_string(), why).into());
            };
            key.push(v);
        }
        self.ask_port(port, Cow::Owned(Value::tuple(key)))
    }

    fn call2(&mut self, f: &V<'t>, a: Value, b: Value) -> R<Step<'t>> {
        self.apply(f, vec![V::Data(a), V::Data(b)])
    }

    /// Primitive `p` on `args`, one of which holds a function or, for a tuple or an atom, is
    /// one: a tuple or an atom is made as a [`Held`], a tuple is read at a key, and an atom
    /// that holds a function passes through every other primitive as any failure does.
    fn held(&mut self, p: Prim, mut args: Vec<V<'t>>) -> R<Step<'t>> {
        let held = |parts, atom| {
            V::Held(Rc::new(Held {
                atom,
                parts,
                drops: self.drops.clone(),
            }))
        };
        match p {
            Prim::Tuple => return Ok(Step::Give(held(args, None))),
            // The atom is made from marks, its payload's positions, by the rules every atom
            // follows ([`prim_data`]: its name, its field names in order, none repeated), and
            // each part is put where its mark landed.
            Prim::Atom => {
                let parts = args.split_off(2.min(args.len()));
                let mut marks = Vec::with_capacity(2 + parts.len());
                for a in args {
                    let V::Data(v) = a else {
                        return type_err(
                            self.at_step(p, format!("{} applied to a function", p.named(None))),
                        );
                    };
                    marks.push(v);
                }
                marks.extend((0..parts.len()).map(|i| Value::Int(i as i64)));
                let shape = match prim_data(Prim::Atom, marks) {
                    Ok(Value::Atom(a)) => a,
                    Ok(_) => return type_err("an atom made as something else"),
                    Err(KernelError::Type(m)) => return type_err(self.at_step(p, m)),
                    Err(e) => return Err(e.into()),
                };
                let mut parts: Vec<Option<V<'t>>> = parts.into_iter().map(Some).collect();
                let mut ordered = Vec::with_capacity(parts.len());
                for m in shape.args().iter() {
                    let Value::Int(i) = m else {
                        unreachable!("each payload value is a mark")
                    };
                    ordered.push(parts[*i as usize].take().expect("each mark once"));
                }
                return Ok(Step::Give(held(ordered, Some((shape.name, shape.fields)))));
            }
            // A tuple's keys are its positions; any other key misses, as for data (`prim_data`).
            Prim::TupleGet | Prim::At if matches!(&args[0], V::Held(h) if h.atom.is_none()) => {
                let V::Held(h) = &args[0] else {
                    unreachable!("matched above")
                };
                return match &args[1] {
                    V::Data(Value::Int(i)) => {
                        match usize::try_from(*i).ok().and_then(|i| h.parts.get(i)) {
                            Some(v) => Ok(Step::Give(v.clone())),
                            None => give(Value::atom("outOfBounds")),
                        }
                    }
                    V::Data(k @ Value::Atom(_)) => give(k.clone()),
                    V::Data(_) => give(Value::atom("outOfBounds")),
                    k if held_atom(k) => Ok(Step::Give(k.clone())),
                    _ => type_err(self.at_step(p, format!("{} at a function", p.named(None)))),
                };
            }
            Prim::Eq | Prim::Ne => {
                return type_err(format!(
                    "`{}` on a value that holds a function compares that function at every \
                     point of an enumerable domain, which its type gives",
                    p.written()
                ));
            }
            _ => {}
        }
        // Every other primitive but a keypath passes its failures through (see [`Self::prim`]):
        // one alone is given as it is, and several are merged into `#errs`, a family, which
        // holds data only.
        let failure = |a: &V<'_>| matches!(a, V::Data(Value::Atom(_))) || held_atom(a);
        if p != Prim::Path
            && args.iter().all(|a| matches!(a, V::Data(_)) || held_atom(a))
            && let Some(i) = args.iter().position(held_atom)
        {
            if args.iter().filter(|a| failure(a)).count() == 1 {
                return Ok(Step::Give(args.swap_remove(i)));
            }
            return type_err(self.at_step(
                p,
                format!(
                    "{} given several failures, one of which holds a function, which `#errs` \
                     cannot hold",
                    p.named(None)
                ),
            ));
        }
        type_err(self.at_step(
            p,
            format!("{} applied to a value that holds a function", p.named(None)),
        ))
    }

    fn prim(&mut self, p: Prim, args: Vec<V<'t>>) -> R<Step<'t>> {
        if let Some(n) = p.arity()
            && args.len() != n
        {
            let s = if n == 1 { "" } else { "s" };
            return type_err(self.at_step(
                p,
                format!(
                    "{} takes {n} argument{s}, given {}",
                    p.named(None),
                    args.len()
                ),
            ));
        }
        // A tuple or an atom made with a part that is no data, or a value that holds a
        // function given to any primitive (DESIGN.md step L1.17).
        if args.iter().any(|a| matches!(a, V::Held(_)))
            || (matches!(p, Prim::Tuple | Prim::Atom)
                && args.iter().any(|a| !matches!(a, V::Data(_))))
        {
            return self.held(p, args);
        }
        // A key past the end of a keypath above an empty level, read by the key map of a
        // `reindex`, is unbound. `short_paths` holds one id per `reindex` nested in a key map.
        if p == Prim::PathKey
            && let [V::Data(Value::Path(keys)), V::Data(Value::Int(i))] = &args[..]
            && usize::try_from(*i).is_ok_and(|i| i >= keys.as_slice().len())
            && self.short_paths.contains(&keys.id())
        {
            return give(unbound());
        }
        // `f[k]` on the family a definedness fix is building.
        if p == Prim::Get && matches!(args[0], V::Partial(_)) {
            let Ok([V::Partial(part), k]) = <[V<'t>; 2]>::try_from(args) else {
                unreachable!("`Get` takes two arguments, the first matched above")
            };
            let V::Data(k) = k else {
                return type_err("a key must be data");
            };
            if let Value::Atom(_) = k {
                return give(k);
            }
            let k = as_key(&k);
            let fix = &part.of;
            let found = match fix.defined.borrow().get(&*k) {
                Some((v, r)) if *r < part.round => Some(v.clone()),
                _ => None,
            };
            return match found {
                Some(v) => give(v),
                None if fix.domain.binary_search(&*k).is_err() => give(Value::atom("notFound")),
                None if self.ev.schedule == Schedule::Pull
                    && !fix.busy.borrow().contains(&*k)
                    && !fix.stalled.borrow().contains(&*k) =>
                {
                    Ok(Step::Demand(fix.clone(), k.into_owned()))
                }
                // An entry defined in this Jacobi round is not yet visible to it.
                None => Err(Stop::Undefined {
                    fix: fix.id,
                    key: k.into_owned(),
                }),
            };
        }
        // `fs[k]` on a lookup port: the world answers once, and the answer is kept.
        if matches!(p, Prim::Get | Prim::TupleGet) && matches!(args[0], V::Source(_)) {
            let Ok([V::Source(port), k]) = <[V<'t>; 2]>::try_from(args) else {
                unreachable!("`Get` and `TupleGet` take two arguments, the first matched above")
            };
            self.ev.check_impure(&port)?;
            let V::Data(k) = k else {
                return type_err("a key must be data");
            };
            if let Value::Atom(_) = k {
                return give(k);
            }
            return self.ask_port(&port, as_key(&k));
        }
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            match a {
                V::Data(v) => vals.push(v),
                _ if matches!(p, Prim::Eq | Prim::Ne) => {
                    return type_err(format!(
                        "`{}` on functions compares them at every point of an enumerable \
                         domain, which their types give",
                        p.written()
                    ));
                }
                _ => {
                    return type_err(self.at_step(
                        p,
                        format!("{} applied to a function", p.named(vals.first())),
                    ));
                }
            }
        }
        // A tuple and an atom's payload hold atoms as data, and `==` has an arrow at every
        // type, atoms included; every other primitive passes its atoms through, merged. A
        // keypath holds them too: a key may be an atom held as data, and a `reindex` reads which
        // keys a keypath above an empty level binds from where its own `unbound` atom lands.
        if !matches!(
            p,
            Prim::Tuple | Prim::Path | Prim::Atom | Prim::Eq | Prim::Ne
        ) && vals.iter().any(|v| matches!(v, Value::Atom(_)))
        {
            let atoms = vals.iter().filter(|v| matches!(v, Value::Atom(_)));
            return give(Value::merge_failures(atoms));
        }
        // A refused test answered by the order of the normal forms, which may have made the
        // primitive fail (a collision of two leaves it took as different): the refusal is the
        // cause.
        let out = prim_data(p, vals);
        if let Some((t, e)) = refused() {
            return Err(order_too_large(p, t, e).into());
        }
        match out {
            Err(KernelError::Type(m)) => type_err(self.at_step(p, m)),
            out => give(out?),
        }
    }

    /// The refusal `m` of the primitive `p`, and for a step on key paths, which the compiler
    /// generates and a program never writes, the call it ran in: the innermost `reindex` key
    /// map or value map or `discard` test running, with the keys of the entry it was given,
    /// or that it ran in none of them. The walk down the frames is O(depth) and runs once, on
    /// the refusal that ends the run.
    fn at_step(&self, p: Prim, m: String) -> String {
        if p.in_words().is_none() {
            return m;
        }
        let keys = |keys: &[Value]| {
            let shown: Vec<String> = keys.iter().map(|k| format!("`{k}`")).collect();
            match shown.len() {
                0 => "with no keys".to_string(),
                1 => format!("at the key {}", shown[0]),
                _ => format!("at the keys {}", shown.join(", ")),
            }
        };
        let call = self.frames.iter().rev().find_map(|f| match f {
            Frame::Wait(Wait::ReindexKey(st)) => Some(("key map", "a `reindex`", keys(&st.path))),
            Frame::Wait(Wait::ReindexValue(st)) => {
                Some(("value map", "a `reindex`", keys(&st.path)))
            }
            Frame::Wait(Wait::Discard(st)) => Some(("test", "a `discard`", keys(&st.prefix))),
            _ => None,
        });
        match call {
            Some((part, of, entry)) => {
                format!("{m}, in the {part} that {of} runs on each entry, on the entry {entry}")
            }
            None => format!(
                "{m}, outside every `reindex` key map and value map and `discard` test, the \
                 only places the compiler generates it"
            ),
        }
    }

    /// Evaluates the entry at the next key, or makes the family.
    fn fam(&mut self, mut st: Box<Fam<'t>>) -> R<Step<'t>> {
        let Some(k) = st.keys.next() else {
            return give(Value::Family(Family::from_leaves(st.out)?));
        };
        self.ev.enter(std::slice::from_ref(&k));
        let env = bind(st.env.clone(), st.var, V::Data(k.clone()), None);
        let (body, at) = (st.body, st.at);
        st.key = Some(k);
        self.wait(Wait::Fam(st));
        Ok(Step::Eval(body, at, env))
    }

    /// Each region call below reads its argument from the fact `from`, the region's input,
    /// and runs at the call site of the operand it calls, inside the region instance of its
    /// leaf, entry, step or iterate.
    fn reindex(&mut self, mut st: Box<Reindex<'t>>) -> R<Step<'t>> {
        let Some((path, v)) = st.leaves.next() else {
            return give(Value::Family(Family::from_leaves(st.out)?));
        };
        self.ev.enter(&path);
        let p = Value::path(path.clone());
        self.ev.aim(st.kf.1, &[st.from; 2]);
        // A keypath above an empty level binds no leaf value and no key past its end: the key
        // map reads the kernel's own atom [`unbound`] there, not `#notFound`, which a key may
        // hold as data.
        st.short = matches!(&v, Value::Family(f) if f.is_empty());
        let leaf = match (st.short, &p) {
            (true, Value::Path(keys)) => {
                self.short_paths.push(keys.id());
                unbound()
            }
            _ => v.clone(),
        };
        let step = self.call2(&st.kf.0, p.clone(), leaf);
        st.path = path;
        st.args = Some((p, v));
        self.wait(Wait::ReindexKey(st));
        step
    }

    /// Tests the next entry of the innermost level, or ends the level.
    fn discard(&mut self, mut st: Box<Discard<'t>>) -> R<Step<'t>> {
        loop {
            let top = st.levels.last_mut().expect("a `discard` is inside a level");
            if let Some((k, v)) = top.entries.next() {
                top.entry = Some(v.clone());
                self.ev.enter(std::slice::from_ref(&k));
                st.prefix.push(k);
                self.ev.aim(st.sel.1, &[st.from; 2]);
                let path = Value::path(st.prefix.clone());
                let step = self.call2(&st.sel.0, path, v);
                self.wait(Wait::Discard(st));
                return step;
            }
            let done = st.levels.pop().expect("a `discard` is inside a level");
            let done = Family::from_leaves(done.out)?;
            let Some(k) = st.prefix.pop() else {
                return give(Value::Family(done));
            };
            let top = st.levels.last_mut().expect("the level above");
            top.out.push((vec![k], Value::Family(done)));
            self.ev.leave(1);
        }
    }

    /// A `discard` selector gave its verdict `v` on the entry in hand.
    fn discarded(&mut self, mut st: Box<Discard<'t>>, v: V<'t>) -> R<Step<'t>> {
        let verdict = data(v)?;
        let k = st.prefix.last().expect("the key of the entry").clone();
        let top = st.levels.last_mut().expect("a `discard` is inside a level");
        let entry = top.entry.take().expect("a `discard` has an entry in hand");
        match verdict {
            Value::Bool(true) => match entry {
                Value::Family(sub) => {
                    st.levels.push(level(&sub));
                    return self.discard(st);
                }
                leaf => top.out.push((vec![k], leaf)),
            },
            Value::Bool(false) => {}
            Value::Atom(a) if &*a.name == "boundary" && a.is_bare() => {
                top.out.push((vec![k.clone()], k))
            }
            other => {
                return type_err(format!(
                    "a discard selector returned a value of type `{}`",
                    other.kind_type()
                ));
            }
        }
        self.ev.leave(1);
        st.prefix.pop();
        self.discard(st)
    }

    fn begin_fold(
        &mut self,
        family: Family,
        op: Operator<'t>,
        from: Option<usize>,
        identity: Option<Value>,
        depth: usize,
    ) -> R<Step<'t>> {
        let leaves = family.leaves();
        // A keypath that ends early, above an empty level, is a leaf holding the empty family.
        // Directly above the innermost level it is a group with no values, which folds to the
        // identity or `#empty`; higher up it keeps its key with an empty level beneath.
        let short = |v: &Value| matches!(v, Value::Family(f) if f.is_empty());
        if leaves.iter().any(|(p, v)| match short(v) {
            true => p.len() >= depth,
            false => p.len() != depth,
        }) {
            return Err(KernelError::MixedDepth.into());
        }
        let mut out = Vec::new();
        let groups: Vec<(Keypath, Vec<Value>)> = if depth == 1 {
            let values = leaves.into_iter().map(|(_, v)| v).collect();
            vec![(Vec::new(), values)]
        } else {
            // Collapse the innermost level beneath each outer keypath.
            let mut groups: BTreeMap<Keypath, Vec<Value>> = BTreeMap::new();
            for (mut path, v) in leaves {
                match short(&v) {
                    true if path.len() + 1 == depth => {
                        groups.entry(path).or_default();
                    }
                    true => out.push((path, v)),
                    false => {
                        path.pop();
                        groups.entry(path).or_default().push(v);
                    }
                }
            }
            groups.into_iter().collect()
        };
        self.fold(Box::new(Fold {
            groups: groups.into_iter(),
            op,
            from,
            identity,
            whole: depth == 1,
            path: Vec::new(),
            tree: None,
            step: 0,
            out,
        }))
    }

    /// Goes on reducing the level in hand in key order, on the canonical tree, then the next
    /// levels, and at the end makes the family of the levels' results. The `i`th application
    /// of `op` runs at step `i` of its level. A level that needs no call of `op` (an empty one,
    /// or one of a single value) goes round the loop, so a fold over many such levels runs in
    /// constant stack.
    fn fold(&mut self, mut st: Box<Fold<'t>>) -> R<Step<'t>> {
        loop {
            if let Some(tree) = st.tree.as_mut() {
                match tree.advance() {
                    TreeStep::Join(a, b) => {
                        self.ev.enter(&[Value::Int(st.step)]);
                        st.step += 1;
                        self.ev.aim(st.op.1, &[st.from; 2]);
                        let step = self.call2(&st.op.0, a, b);
                        self.wait(Wait::Fold(st));
                        return step;
                    }
                    TreeStep::Done(v) => {
                        st.tree = None;
                        self.ev.leave(st.path.len());
                        if st.whole {
                            return give(v);
                        }
                        let path = std::mem::take(&mut st.path);
                        st.out.push((path, v));
                    }
                }
            }
            let Some((path, values)) = st.groups.next() else {
                return give(Value::Family(Family::from_leaves(st.out)?));
            };
            self.ev.enter(&path);
            match reduced(&values, &st.op.0, &st.identity) {
                Some(v) => {
                    self.ev.leave(path.len());
                    if st.whole {
                        return give(v);
                    }
                    st.out.push((path, v));
                }
                None => {
                    st.path = path;
                    st.tree = Some(CanonicalTree::new(values));
                    st.step = 0;
                }
            }
        }
    }

    /// Iterate `i`'s step and join run at coordinate `i`, the step reading the fact of the
    /// iterate before.
    fn lattice(&mut self, st: Box<Lattice<'t>>) -> R<Step<'t>> {
        self.ev.burn()?;
        self.ev.enter(&[Value::Int(st.i)]);
        self.ev.aim(st.step.1, &[st.from]);
        let step = self.apply(&st.step.0, vec![V::Data(st.x.clone())]);
        self.wait(Wait::LatticeStep(st));
        step
    }

    fn begin_definedness(
        &mut self,
        init: Value,
        body: &'t Term,
        at: At,
        this: &'t str,
        key: &'t str,
        env: Env<'t>,
    ) -> R<Step<'t>> {
        let domain: Box<[Value]> = family(init)?.keys().cloned().collect();
        self.ev.fixes += 1;
        let (calls, trace_keys) = match &self.ev.trace {
            Some(t) => (t.calls.clone(), t.keys.clone()),
            None => Default::default(),
        };
        let fix = Rc::new(Definedness {
            id: self.ev.fixes,
            domain,
            body,
            at,
            this,
            key,
            env,
            calls,
            keys: trace_keys,
            defined: RefCell::default(),
            busy: RefCell::default(),
            stalled: RefCell::default(),
            drops: self.drops.clone(),
        });
        let rng = match self.ev.schedule {
            Schedule::Rounds => None,
            Schedule::Chaotic(seed) => Some(SplitMix(seed)),
            Schedule::Pull => return self.pull(Box::new(Pull { fix, next: 0 })),
        };
        // The first round tries every entry; the work list is the rounds' own, since later
        // rounds refill it.
        let ready = fix.domain.to_vec();
        self.round(Box::new(Rounds {
            fix,
            rng,
            waiting: BTreeMap::new(),
            queue: Vec::new().into_iter(),
            ready,
            defined: Vec::new(),
            round: 1,
            sees: 0,
        }))
    }

    /// Begins an attempt at the entry at `k` of the `fix` of `by` against the entries defined
    /// before `round`.
    fn attempt(&mut self, round: u64, k: Value, by: By<'t>) -> R<Step<'t>> {
        let fix = by.fix();
        let part = V::Partial(Rc::new(Partial {
            of: fix.clone(),
            round,
        }));
        let env = bind(fix.env.clone(), fix.this, part, None);
        let env = bind(env, fix.key, V::Data(k.clone()), None);
        let (body, at) = (fix.body, fix.at);
        let mark = self
            .ev
            .trace
            .as_ref()
            .map(|t| (t.facts.len(), t.calls.len(), t.keys.len()));
        self.ev.enter(std::slice::from_ref(&k));
        self.frames
            .push(Frame::Entry(Box::new(Entry { k, mark, by })));
        Ok(Step::Eval(body, at, env))
    }

    /// An attempt ended: with the entry's value, with a read of an undefined entry of its
    /// `fix`, or with something that stops the run. An attempt that reads an undefined entry
    /// is not a fact: what it recorded is dropped, and the entry's fact is the attempt that
    /// defines it.
    fn entry_ended(&mut self, entry: Entry<'t>, out: R<V<'t>>) -> R<Step<'t>> {
        let Entry { k, mark, by } = entry;
        let id = by.fix().id;
        self.ev.leave(1);
        let attempt = match out {
            Ok(V::Data(v)) => Ok(Ok(v)),
            Ok(_) => type_err("a fix entry is a function"),
            Err(Stop::Undefined { fix, key }) if fix == id => {
                if let (Some(t), Some((facts, calls, keys))) = (&mut self.ev.trace, mark) {
                    t.facts.truncate(facts);
                    t.calls.truncate(calls);
                    t.keys.truncate(keys);
                }
                Ok(Err(key))
            }
            Err(e) => Err(e),
        };
        match by {
            By::Round(mut st) => {
                match attempt? {
                    Ok(v) => {
                        let round = st.round;
                        st.fix.defined.borrow_mut().insert(k.clone(), (v, round));
                        st.defined.push(k);
                    }
                    Err(read) => st.waiting.entry(read).or_default().push(k),
                }
                self.next_entry(st)
            }
            By::Pull(st) => {
                st.fix.busy.borrow_mut().remove(&k);
                match attempt? {
                    Ok(v) => {
                        st.fix.defined.borrow_mut().insert(k, (v, 0));
                    }
                    Err(_) => {
                        st.fix.stalled.borrow_mut().insert(k);
                    }
                }
                self.pull(st)
            }
            By::Demand(fix, saved) => {
                fix.busy.borrow_mut().remove(&k);
                if let (Some(t), Some(s)) = (&mut self.ev.trace, saved) {
                    (t.calls, t.keys, t.reads, t.site, t.args) =
                        (s.calls, s.keys, s.reads, s.site, s.args);
                }
                match attempt? {
                    Ok(v) => {
                        fix.defined.borrow_mut().insert(k, (v.clone(), 0));
                        give(v)
                    }
                    Err(key) => {
                        fix.stalled.borrow_mut().insert(k);
                        Err(Stop::Undefined { fix: fix.id, key })
                    }
                }
            }
        }
    }

    /// Begins a round: defines entries in rounds until every entry is defined or a round
    /// defines none. Without a seed each round reads the family as it began (Jacobi); with
    /// one, each round visits its entries in a shuffled order and reads the entries defined
    /// before it in the same round.
    ///
    /// An attempt that read the undefined entry `j` reads the same entries again, and stops
    /// at `j`, while `j` stays undefined, since entries never change once defined. So it
    /// waits on `j` and is tried again in the round after `j` is defined: each round tries
    /// only the entries whose wait ended, and a chain of `D` entries costs `D` attempts, not
    /// `D²/2`. Jacobi rounds define the same entries in the same rounds as trying them all.
    // Complexity tradeoff (COMPLEXITY.md K5): the naive version copies the domain and the
    // defined map for each attempt and tries every undefined entry in every round, O(D³) for a
    // chain of `D` entries (`D` rounds of `D` attempts, each copying `D` entries). Used: one
    // shared map whose entries carry the round that defined them (`Defined`), and a wait list
    // per undefined entry read, so a chain costs `D` attempts under every schedule and each
    // attempt only what it reads, O(D log D) for the chain. Tradeoffs: memory for the round
    // stamps and the wait lists, O(D); it rests on entries never changing once defined, which
    // makes a retried attempt read the same entries and stop at the same one.
    fn round(&mut self, mut st: Box<Rounds<'t>>) -> R<Step<'t>> {
        self.ev.burn()?;
        if st.ready.is_empty() {
            return rounds_end(&st.fix);
        }
        if let Some(rng) = &mut st.rng {
            rng.shuffle(&mut st.ready);
        }
        // Jacobi rounds read the entries of earlier rounds; chaotic ones read every entry.
        st.sees = if st.rng.is_some() { u64::MAX } else { st.round };
        st.queue = std::mem::take(&mut st.ready).into_iter();
        self.next_entry(st)
    }

    fn next_entry(&mut self, mut st: Box<Rounds<'t>>) -> R<Step<'t>> {
        if let Some(k) = st.queue.next() {
            let sees = st.sees;
            return self.attempt(sees, k, By::Round(st));
        }
        if st.defined.is_empty() {
            return rounds_end(&st.fix);
        }
        for k in std::mem::take(&mut st.defined) {
            let waited = st.waiting.remove(&k).unwrap_or_default();
            st.ready.extend(waited);
        }
        // The order of trying a round's entries is the key order, as when all are tried.
        st.ready.sort();
        st.round += 1;
        self.round(st)
    }

    /// Demands the next key not yet settled, evaluating first each undefined entry it reads
    /// ([`Machine::demand`]), so an entry reading `m` undefined entries is evaluated once,
    /// not `m` times from the start. An attempt that stops read an entry that was being
    /// demanded or had stalled: that entry is on a cycle or waits on one, and so does the
    /// attempt, whose entry stalls.
    // Complexity tradeoff (COMPLEXITY.md K14): the naive version reruns an entry from the
    // start after each undefined entry it reads is defined, O(m²) for an entry reading `m`
    // undefined ones, and checks for a cycle by `Vec::contains` on the demand stack, O(D²) for
    // a chain of `D`. Used: the undefined entry is evaluated where it is read, so each entry is
    // evaluated once, and the entries being demanded and those stalled are ordered sets, so the
    // cycle check is O(log D) and a chain ending in a cycle stalls in O(D log D). Tradeoffs: the
    // demanded entries' frames are nested, held on the machine's heap stack, O(D) memory; an
    // entry on a cycle and every entry waiting on it stall rather than being retried.
    fn pull(&mut self, mut st: Box<Pull<'t>>) -> R<Step<'t>> {
        while let Some(k) = st.fix.domain.get(st.next) {
            st.next += 1;
            if st.fix.defined.borrow().contains_key(k) || st.fix.stalled.borrow().contains(k) {
                continue;
            }
            self.ev.burn()?;
            let k = k.clone();
            st.fix.busy.borrow_mut().insert(k.clone());
            return self.attempt(u64::MAX, k, By::Pull(st));
        }
        finish_fix(&st.fix, st.fix.stalled.take().into_iter().collect())
    }

    /// Evaluates the undefined entry `k` where an attempt reads it, with the call sites and
    /// keypath of the `fix` itself, so that its facts are those it would have had demanded
    /// from the top. A read it cannot demand stops it and the attempt reading it.
    fn demand(&mut self, fix: Rc<Definedness<'t>>, k: Value) -> R<Step<'t>> {
        self.ev.burn()?;
        let saved = self.ev.trace.as_mut().map(|t| Saved {
            calls: std::mem::replace(&mut t.calls, fix.calls.clone()),
            keys: std::mem::replace(&mut t.keys, fix.keys.clone()),
            reads: std::mem::take(&mut t.reads),
            site: t.site.take(),
            args: std::mem::take(&mut t.args),
        });
        fix.busy.borrow_mut().insert(k.clone());
        self.attempt(u64::MAX, k, By::Demand(fix, saved))
    }

    /// The step making generation `t` runs at coordinate `t`, reading the fact of the frame
    /// before.
    fn gen_step(&mut self, st: Box<Gen<'t>>) -> R<Step<'t>> {
        self.ev.burn()?;
        let last = st.frames.last().expect("generation 0 is present").clone();
        self.ev.enter(&[Value::Int(st.frames.len() as i64)]);
        self.ev.aim(st.step.1, &[st.from]);
        let step = self.apply(&st.step.0, vec![V::Data(last)]);
        self.wait(Wait::GenStep(st));
        step
    }

    /// Tests a `gen` guard on the last frame, at that frame's coordinate. A result that is
    /// not a bool ends the loop and is appended as the stream's last entry.
    fn gen_guard(&mut self, st: Box<Gen<'t>>) -> R<Step<'t>> {
        let last = st.frames.last().expect("generation 0 is present").clone();
        self.ev.enter(&[Value::Int(st.frames.len() as i64 - 1)]);
        self.ev.aim(st.guard.1, &[st.from]);
        let step = self.apply(&st.guard.0, vec![V::Data(last)]);
        self.wait(Wait::GenGuard(st));
        step
    }
}

/// The result of a level that needs no call of `op`: an empty level's, or, for the primitive
/// `+`, that of a level holding an atom or only floats, which is the exact sum, rounded once.
fn reduced(values: &[Value], op: &V<'_>, identity: &Option<Value>) -> Option<Value> {
    if values.is_empty() {
        return Some(identity.clone().unwrap_or_else(|| Value::atom("empty")));
    }
    if matches!(op, V::Prim(Prim::Add)) {
        if let Some(atom) = values.iter().find(|v| matches!(v, Value::Atom(_))) {
            return Some(atom.clone());
        }
        let floats: Option<Vec<f64>> = values
            .iter()
            .map(|v| match v {
                Value::Float(x) => Some(x.get()),
                _ => None,
            })
            .collect();
        if let Some(xs) = floats {
            return Some(Value::float(exact_sum(&xs)));
        }
    }
    None
}

/// The keypath a `reindex` writes a leaf at, given the key its key map returned there. A
/// keypath holds atoms as data, as a tuple does (DESIGN.md M0.9 (a)), so a key that is an atom
/// keeps its place: the identity reindex of `{#red -> {1 -> 5}}` is itself. Costs the length of
/// the key.
fn key_of(key: Value) -> Keypath {
    match key {
        Value::Path(keys) => keys.into_vec(),
        single => vec![single],
    }
}

/// The kernel's own atom for what a keypath above an empty level does not bind: its leaf, and
/// its keys past its end. Its name is no Zed identifier, so no program writes it, and a key
/// holding `#notFound` or any other atom as data is not taken for it.
fn unbound() -> Value {
    Value::atom(UNBOUND)
}

/// The name of [`unbound`].
const UNBOUND: &str = "unbound key";

/// Where a `reindex` puts the empty level beneath a keypath that ends early, given the key its
/// key map returned there (DESIGN.md sec:remap_law): the keys before the first that holds
/// [`unbound`], which the key map reads past the keypath's end and in place of its leaf. `None`
/// when the first key holds it, since then the new keypath starts with a level the short
/// keypath does not bind, and the key is dropped. A key map that returns the empty keypath gets
/// [`KernelError::EmptyKeypath`] from the family built, as at a full keypath. Costs the size of
/// the key, each shared part read once.
fn placed(key: Value) -> Option<Keypath> {
    let mut keys = match key {
        Value::Path(keys) => keys.into_vec(),
        single => vec![single],
    };
    let unbound = keys.iter().position(|k| {
        !all_leaves(
            std::slice::from_ref(k),
            |v| !matches!(v, Value::Atom(a) if &*a.name == UNBOUND && a.is_bare()),
        )
    });
    match unbound {
        Some(0) => None,
        Some(i) => {
            keys.truncate(i);
            Some(keys)
        }
        None => Some(keys),
    }
}

/// The level of `family`'s top-level entries, before any is tested.
fn level(family: &Family) -> Level {
    let entries: Vec<(Value, Value)> = family.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    Level {
        out: Vec::new(),
        entries: entries.into_iter(),
        entry: None,
    }
}

fn gen_end<'t>(st: Gen<'t>) -> R<Step<'t>> {
    let leaves = st
        .frames
        .into_iter()
        .enumerate()
        .map(|(t, f)| (vec![Value::Int(t as i64)], f));
    give(Value::Family(Family::from_leaves(leaves)?))
}

/// The keys `fix`'s rounds left undefined, or its family.
fn rounds_end<'t>(fix: &Definedness<'t>) -> R<Step<'t>> {
    let left: Vec<Value> = {
        let defined = fix.defined.borrow();
        let left = fix.domain.iter().filter(|k| !defined.contains_key(*k));
        left.cloned().collect()
    };
    finish_fix(fix, left)
}

fn finish_fix<'t>(fix: &Definedness<'t>, stalled: Vec<Value>) -> R<Step<'t>> {
    if !stalled.is_empty() {
        return Err(KernelError::Stalled { keys: stalled }.into());
    }
    let defined = fix.defined.take();
    let leaves = defined.into_iter().map(|(k, (v, _))| (vec![k], v));
    give(Value::Family(Family::from_leaves(leaves)?))
}

/// One definedness `fix` being evaluated: its family's name, domain, and entry body, the
/// call sites and keypath it runs inside, and, for demand, the entries being demanded and
/// those stalled.
struct Definedness<'t> {
    id: u64,
    /// The keys of the initial family, distinct and in order: a pull walks them by index, and
    /// a read finds a key by binary search.
    domain: Box<[Value]>,
    defined: RefCell<Defined>,
    body: &'t Term,
    /// The body's position.
    at: At,
    this: &'t str,
    key: &'t str,
    env: Env<'t>,
    calls: Vector<Position>,
    keys: Vector<Value>,
    busy: RefCell<BTreeSet<Value>>,
    stalled: RefCell<BTreeSet<Value>>,
    drops: Rc<Drops<'t>>,
}

impl Drop for Definedness<'_> {
    fn drop(&mut self) {
        self.drops.free(Freed::Env(self.env.take()));
    }
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

/// Whether `v` is an atom that holds a function.
fn held_atom(v: &V<'_>) -> bool {
    matches!(v, V::Held(h) if h.atom.is_some())
}

/// Whether `v`, data, a function or a value that holds one, matches `pat`, binding its
/// variables in `env` as [`matches()`] does. A function matches a wildcard, a binder and a type
/// test of a type with every function; the parts of a [`Held`] are matched left to right, from
/// a stack of those left, and its data parts by [`matches()`].
fn matches_any<'t>(pat: &'t Pattern, v: &V<'t>, env: &mut Env<'t>, fact: Option<usize>) -> bool {
    let mut left: Vec<(&'t Pattern, &V<'t>)> = Vec::new();
    let mut at = (pat, v);
    loop {
        let hit = match at {
            (pat, V::Data(v)) => matches(pat, v, env, fact),
            (Pattern::Wild, _) => true,
            (Pattern::Bind(name), v) => {
                *env = bind(env.take(), name, v.clone(), fact);
                true
            }
            (Pattern::Is(t), V::Held(h)) => t.contains(&h.stand_in()),
            (Pattern::Is(t), _) => t.functions(),
            (Pattern::AnyAtom, V::Held(h)) => h.atom.is_some(),
            (Pattern::Atom(name, ps), V::Held(h)) => {
                // A held atom has a payload, with a function in it, so it is never bare.
                let hit = matches!(&h.atom, Some((n, f)) if n == name && f.is_empty())
                    && !ps.is_empty()
                    && ps.len() == h.parts.len();
                if hit {
                    left.extend(ps.iter().zip(&h.parts).rev());
                }
                hit
            }
            (Pattern::Fields(name, fs), V::Held(h)) => match &h.atom {
                Some((n, f)) if n == name && !f.is_empty() => {
                    fs.iter().rev().all(|(x, p)| match f.binary_search(x) {
                        Ok(i) => {
                            left.push((p, &h.parts[i]));
                            true
                        }
                        Err(_) => false,
                    })
                }
                _ => false,
            },
            (Pattern::Tuple(ps), V::Held(h)) => {
                let hit = h.atom.is_none() && ps.len() == h.parts.len();
                if hit {
                    left.extend(ps.iter().zip(&h.parts).rev());
                }
                hit
            }
            _ => false,
        };
        if !hit {
            return false;
        }
        match left.pop() {
            Some(next) => at = next,
            None => return true,
        }
    }
}

/// Whether `v` matches `pat`, binding its variables in `env` to parts of `v`, which came
/// from `fact`. The parts are matched left to right, from a stack of those left.
fn matches<'t>(pat: &'t Pattern, v: &Value, env: &mut Env<'t>, fact: Option<usize>) -> bool {
    let mut left: Vec<(&'t Pattern, &Value)> = Vec::new();
    let mut at = (pat, v);
    loop {
        let hit = match at {
            (Pattern::Wild, _) => true,
            (Pattern::Bind(name), v) => {
                *env = bind(env.take(), name, V::Data(v.clone()), fact);
                true
            }
            (Pattern::Lit(l), v) => l == v,
            (Pattern::AnyAtom, Value::Atom(_)) => true,
            (Pattern::Is(t), v) => t.contains(v),
            (Pattern::Atom(name, ps), Value::Atom(a)) => {
                // `#e` matches the bare atom only: a pattern has no `#e()` (sec:grammar,
                // AtomPattern), so an empty pattern list is never an empty payload.
                let hit = a.name == *name
                    && a.fields.is_empty()
                    && match &a.payload {
                        None => ps.is_empty(),
                        Some(xs) => !ps.is_empty() && ps.len() == xs.len(),
                    };
                if hit {
                    left.extend(ps.iter().zip(a.args()).rev());
                }
                hit
            }
            (Pattern::Fields(name, fs), Value::Atom(a)) => {
                a.name == *name
                    && !a.fields.is_empty()
                    && fs
                        .iter()
                        .rev()
                        .all(|(f, p)| match a.fields.binary_search(f) {
                            Ok(i) => {
                                left.push((p, &a.args()[i]));
                                true
                            }
                            Err(_) => false,
                        })
            }
            (Pattern::Tuple(ps), Value::Tuple(xs)) => {
                let hit = ps.len() == xs.len();
                if hit {
                    left.extend(ps.iter().zip(xs).rev());
                }
                hit
            }
            _ => false,
        };
        if !hit {
            return false;
        }
        match left.pop() {
            Some(next) => at = next,
            None => return true,
        }
    }
}

/// The key `k` reads: `k` itself unless it holds a `-0.0`, which its key does not. Domains
/// and maps of entries hold keys, and the order on values tells `-0.0` from `0.0`.
fn as_key(k: &Value) -> Cow<'_, Value> {
    match k.is_key() {
        true => Cow::Borrowed(k),
        false => Cow::Owned(k.key()),
    }
}

/// An integer `+`, `-`, `*`, `div`, `mod` or `^` of two integers, either of either width:
/// in a machine word when the result fits, else unbounded. `None` for a negative power;
/// [`KernelError::NumberTooLarge`] when a number it must build does not fit in memory.
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
    let x = a.as_integer().expect("an integer");
    let y = b.as_integer().expect("an integer");
    if matches!(p, Prim::IntDiv | Prim::Mod) && y.is_zero() {
        return Ok(Some(Value::atom("divByZero")));
    }
    let r = match p {
        Prim::Add => x.add(&y),
        Prim::Sub => x.sub(&y),
        Prim::Mul => x.mul(&y),
        Prim::IntDiv => x.div_euclid(&y),
        Prim::Mod => x.rem_euclid(&y),
        _ if y.is_negative() => return Ok(None),
        // `0`, `1` and `-1` to any power are read from the exponent's sign and parity, so
        // `1 ^ 2 ^ 2 ^ 33` builds no exponent.
        _ => match a {
            Value::Int(u @ -1..=1) => {
                let one = *u == 1 || (*u == -1 && y.is_even());
                return Ok(Some(Value::Int(match (*u, y.is_zero()) {
                    (_, true) => 1,
                    (0, false) => 0,
                    _ if one => 1,
                    _ => -1,
                })));
            }
            // Any other base's power is at least `2^y`, kept with `y` as its exponent, so
            // building `y` costs the size of the result's own form.
            _ => y.to_integer().and_then(|e| x.pow(e.magnitude())),
        },
    };
    match r {
        Ok(r) => Ok(Some(Value::integer(r))),
        Err(e) => Err(too_large(p, e)),
    }
}

/// An atom's name or field name as one shared block ([`crate::text::Text::try_shared`]); a
/// join is written out once the system gives the memory, else [`KernelError::AtomNameTooLarge`].
fn atom_name(name: &crate::text::Text) -> Result<Arc<str>, KernelError> {
    name.try_shared()
        .map_err(|_| KernelError::AtomNameTooLarge { bytes: name.len() })
}

/// The error for a number that `p` must build and the system has no memory for.
fn too_large(p: Prim, e: crate::num::TooLarge) -> KernelError {
    KernelError::NumberTooLarge {
        op: p.written(),
        need: e,
    }
}

/// The error of a primitive during which a test of two numbers was refused its memory: a
/// comparison operator's own, or that of the families a primitive builds or reads.
fn order_too_large(p: Prim, t: Test, e: TooLarge) -> KernelError {
    match p {
        Prim::Eq | Prim::Ne | Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Min | Prim::Max => {
            test_too_large(Some(p.written()), t, e)
        }
        _ => test_too_large(None, t, e),
    }
}

/// The error for a test `t` of two numbers refused its memory, made by `op` (an operator or
/// `match` or `fix`), or with no `op` while building or reading families.
fn test_too_large(op: Option<&'static str>, t: Test, e: TooLarge) -> KernelError {
    let need = e;
    match (op, t) {
        (Some(op), Test::Order) => KernelError::OrderTooLarge { op, need },
        (Some(op), Test::Equality) => KernelError::EqualityTooLarge { op, need },
        (None, Test::Order) => KernelError::KeyOrderTooLarge { need },
        (None, Test::Equality) => KernelError::FamilyEqualityTooLarge { need },
    }
}

/// A primitive on data none of which is an atom.
fn prim_data(p: Prim, vals: Vec<Value>) -> Result<Value, KernelError> {
    use Value::{Bool, Float, Float32, Int, Str};
    // These two keep the values they are given: copying a tuple that holds a list would make
    // building the list quadratic in its length.
    match p {
        Prim::Tuple => return Ok(Value::tuple(vals)),
        Prim::Path => return Ok(Value::path(vals)),
        _ => {}
    }
    let ty = |vals: &[Value]| {
        let shown: Vec<String> = vals
            .iter()
            .map(|v| format!("`{}`", v.kind_type()))
            .collect();
        Err(KernelError::Type(format!(
            "{} applied to {}",
            p.named(vals.first()),
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
            None => Value::int(-BigInt::from(*a)),
        },
        (Prim::Neg, [Value::Big(a)]) => Value::integer(a.try_neg().map_err(|e| too_large(p, e))?),
        (Prim::Add | Prim::Sub | Prim::Mul | Prim::Div, [Value::Rat(a), Value::Rat(b)]) => {
            let r = match p {
                Prim::Add => a.add(b),
                Prim::Sub => a.sub(b),
                Prim::Mul => a.mul(b),
                _ => match a.div(b) {
                    Ok(Some(r)) => Ok(r),
                    Ok(None) => return Ok(Value::atom("divByZero")),
                    Err(e) => Err(e),
                },
            };
            Value::rat(r.map_err(|e| too_large(p, e))?)
        }
        (Prim::Neg, [Value::Rat(a)]) => Value::rat(a.try_neg().map_err(|e| too_large(p, e))?),
        // A `rat` to an integer power of either sign, exact; `0r` to a negative power is
        // `#divByZero`, as `1r / 0r` is (DESIGN.md sec:lexical).
        (Prim::Pow, [Value::Rat(a), b]) if b.number_kind() == Some(0) => {
            let e = b.as_integer().expect("an integer");
            match a.pow_int(&e).map_err(|e| too_large(p, e))? {
                Some(r) => Value::rat(r),
                None => return Ok(Value::atom("divByZero")),
            }
        }
        (Prim::Add, [Float(a), Float(b)]) => Value::float(a.get() + b.get()),
        (Prim::Sub, [Float(a), Float(b)]) => Value::float(a.get() - b.get()),
        (Prim::Mul, [Float(a), Float(b)]) => Value::float(a.get() * b.get()),
        (Prim::Div, [Float(a), Float(b)]) => Value::float(a.get() / b.get()),
        (Prim::Neg, [Float(a)]) => Value::float(-a.get()),
        // An `f32` operation rounds once to `f32`, as IEEE 754 binary32 arithmetic does.
        (Prim::Add, [Float32(a), Float32(b)]) => Value::float32(a.get() + b.get()),
        (Prim::Sub, [Float32(a), Float32(b)]) => Value::float32(a.get() - b.get()),
        (Prim::Mul, [Float32(a), Float32(b)]) => Value::float32(a.get() * b.get()),
        (Prim::Div, [Float32(a), Float32(b)]) => Value::float32(a.get() / b.get()),
        (Prim::Neg, [Float32(a)]) => Value::float32(-a.get()),
        // IEEE 754 `squareRoot` and `fusedMultiplyAdd`, each rounded once to the operands'
        // format: Rust's `sqrt` and `mul_add` are both correctly rounded, `sqrt(-0.0)` is
        // `-0.0`, and a negative or NaN operand of `sqrt`, a NaN operand of `fma`, or
        // `fma(inf, 0, c)` gives NaN (DESIGN.md sec:linalg, machine operations). Method: IEEE
        // Std 754-2019, "IEEE Standard for Floating-Point Arithmetic", IEEE, 2019, section
        // 5.4.1. Cost: O(1), one hardware instruction each (or the C library's `fma` on a host
        // without FMA). Measured: test `l01_18_scalar_interpreter::sqrt_fma` runs n = 2048 and
        // 8n calls of each word, 14225721 and 113703294 instructions, 8.0 times the work.
        (Prim::Sqrt, [Float(a)]) => Value::float(a.get().sqrt()),
        (Prim::Sqrt, [Float32(a)]) => Value::float32(a.get().sqrt()),
        (Prim::Fma, [Float(a), Float(b), Float(c)]) => {
            Value::float(a.get().mul_add(b.get(), c.get()))
        }
        (Prim::Fma, [Float32(a), Float32(b), Float32(c)]) => {
            Value::float32(a.get().mul_add(b.get(), c.get()))
        }
        (Prim::Concat, [Str(a), Str(b)]) => Str(crate::text::Text::join(a, b)?),
        // NaN in, NaN out, as for every float operation (DESIGN.md sec:domains, NaN rule 5):
        // IEEE 754 `pow` gives `pow(NaN, 0) = 1` and `pow(1, NaN) = 1`, so a NaN operand is
        // tested first.
        (Prim::Pow, [Float(a), Float(b)]) => {
            let (a, b) = (a.get(), b.get());
            Value::float(if a.is_nan() || b.is_nan() {
                f64::NAN
            } else {
                a.powf(b)
            })
        }
        (Prim::Pow, [Float32(a), Float32(b)]) => {
            let (a, b) = (a.get(), b.get());
            Value::float32(if a.is_nan() || b.is_nan() {
                f32::NAN
            } else {
                a.powf(b)
            })
        }
        // `f32 ^ int`, the one operator arrow between two carriers (DESIGN.md L1.18): the power
        // is taken in `f64` and rounded once to `f32`. An exponent beyond ±2^53 is read as the
        // nearest `f64` of its parity, which keeps the sign of a negative base; every base but
        // ±1 then overflows or underflows in `f64` as it would at the exact exponent.
        (Prim::Pow, [Float32(a), b]) if b.number_kind() == Some(0) => {
            let a = a.get();
            let e = match b {
                Int(n) if n.unsigned_abs() <= 1 << 53 => *n as f64,
                _ => {
                    let n = b.as_integer().expect("an integer");
                    let m = if n.is_even() {
                        2f64.powi(53)
                    } else {
                        2f64.powi(53) - 1.0
                    };
                    if n.is_negative() { -m } else { m }
                }
            };
            Value::float32(if a.is_nan() {
                f32::NAN
            } else {
                f64::from(a).powf(e) as f32
            })
        }
        (Prim::Eq, [a, b]) => Bool(a.surface_eq(b)),
        (Prim::Ne, [a, b]) => Bool(!a.surface_eq(b)),
        // Two floats compare as IEEE 754 does, so every comparison with a NaN is false.
        (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge, [Float32(a), Float32(b)]) => {
            let (a, b) = (a.get(), b.get());
            Bool(match p {
                Prim::Lt => a < b,
                Prim::Le => a <= b,
                Prim::Gt => a > b,
                _ => a >= b,
            })
        }
        (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge, [Float(a), Float(b)]) => {
            let (a, b) = (a.get(), b.get());
            Bool(match p {
                Prim::Lt => a < b,
                Prim::Le => a <= b,
                Prim::Gt => a > b,
                _ => a >= b,
            })
        }
        (Prim::Min | Prim::Max, [Float(a), Float(b)]) => {
            Value::float(ieee_min_max(p == Prim::Min, a.get(), b.get()))
        }
        // Widening to `f64` is exact and the result is one of the two, so narrowing back is too.
        (Prim::Min | Prim::Max, [Float32(a), Float32(b)]) => {
            Value::float32(
                ieee_min_max(p == Prim::Min, f64::from(a.get()), f64::from(b.get())) as f32,
            )
        }
        // Two tuples: the first component in which they differ decides (DESIGN.md sec:reduction).
        (Prim::Min | Prim::Max, [a @ Value::Tuple(_), b @ Value::Tuple(_)]) => {
            match a.selects(b, p == Prim::Min) {
                Some(true) => a.clone(),
                Some(false) => b.clone(),
                None => return ty(&vals),
            }
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
        (Prim::Union, [Value::Family(a), Value::Family(b)]) => Value::Family(a.union(b)?),
        (Prim::Atom, [Str(name), Value::Tuple(names), args @ ..]) if names.is_empty() => {
            Value::atom_with(atom_name(name)?, args.to_vec())
        }
        (Prim::Atom, [Str(name), Value::Tuple(names), args @ ..]) if names.len() == args.len() => {
            let mut fields = Vec::with_capacity(names.len());
            for (n, v) in names.iter().zip(args) {
                let Str(n) = n else { return ty(&vals) };
                fields.push((atom_name(n)?, v.clone()));
            }
            match Value::atom_named(atom_name(name)?, fields) {
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
        // A tuple's keys are its positions `0..<n`, one integer interval with every key
        // present, so any other key misses with `#outOfBounds` (DESIGN.md sec:type_language,
        // the `m[k]` row).
        (Prim::TupleGet | Prim::At, [Value::Tuple(items), Int(i)]) => usize::try_from(*i)
            .ok()
            .and_then(|i| items.get(i))
            .cloned()
            .unwrap_or_else(|| Value::atom("outOfBounds")),
        (Prim::TupleGet | Prim::At, [Value::Tuple(_), _]) => Value::atom("outOfBounds"),
        // A read the checker proved is of a family whose keys are one integer interval, every
        // key present: a key it lacks lies outside the interval.
        (Prim::At, [Value::Family(f), k]) => f
            .get(k)
            .cloned()
            .unwrap_or_else(|| Value::atom("outOfBounds")),
        (
            Prim::Show
            | Prim::CastInt
            | Prim::CastRat
            | Prim::CastF64
            | Prim::CastF32
            | Prim::Abs
            | Prim::Len
            | Prim::Lower
            | Prim::Upper
            | Prim::Trim
            | Prim::CodePoint
            | Prim::Scalar
            | Prim::Utf8
            | Prim::FromUtf8,
            [x],
        ) => crate::words::word(p, x)?,
        _ if crate::bits::is_bit_word(p) => crate::bits::word(p, &vals)?,
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
