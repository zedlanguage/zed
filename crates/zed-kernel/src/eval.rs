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
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;
use zed_hash::SplitMix64;

use crate::exact::{CanonicalTree, TreeStep};
use crate::num::{Test, TooLarge, refused};
use crate::sites::{Sites, Span};
use crate::text::prose::plural;
use crate::value::KernelError;
use crate::value::{
    Atom, Family, Fields, HeldEntry, HeldFamily, Keypath, all_leaves, ieee_min_max,
};
use std::sync::{Arc, Mutex};

use num_bigint::BigInt;

use crate::value::canon::{Canon, Namer};

use crate::provenance::{Fact, FactAddress, Holds, NodeAddress, Position, Provenance};
use crate::term::{FixKind, GuardPos, Pattern, Prim, Shared, Term};
use crate::value::Value;

mod env;
mod made;
pub use made::{FILL_NAME, Made, MadeFun, MadeNode, MadeShape, fun_term, placed_fun_term};
/// The names in scope (see [`mod@env`]), each bound to a [`Binding`].
type Env<'t> = env::Env<'t, Binding<'t>>;

#[cfg(test)]
mod arrow_tests;
#[cfg(test)]
mod binder_tests;
#[cfg(test)]
mod tests;

#[cfg(test)]
mod bench;

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
    shape: Shape,
    /// The components of a tuple, the payload of an atom in the order of its field names, or
    /// the entries of a family that are no data, by their numbers.
    parts: Vec<V<'t>>,
    drops: Rc<Drops<'t>>,
}

/// What a [`Held`] is.
enum Shape {
    Tuple,
    /// An atom: its name and its field names, sorted as [`Value::atom_named`] sorts them, empty
    /// for a payload by position.
    Atom(Arc<str>, Fields),
    /// A family, with a part that is no data (step FAIL-family-function-entry).
    Family(HeldFamily),
}

impl Held<'_> {
    fn atom(&self) -> Option<(&Arc<str>, &Fields)> {
        match &self.shape {
            Shape::Atom(n, f) => Some((n, f)),
            _ => None,
        }
    }

    fn is_tuple(&self) -> bool {
        matches!(self.shape, Shape::Tuple)
    }
}

/// The kernel's held family, read by [`held_family_got`] from `Machine::held_family`.
impl<'t> HeldFamilyAt for Rc<Held<'t>> {
    type Part = V<'t>;
    type Error = std::convert::Infallible;

    fn family(&self) -> &HeldFamily {
        let Shape::Family(f) = &self.shape else {
            unreachable!("only held families are read as families")
        };
        f
    }

    fn part(&self, i: usize) -> V<'t> {
        self.parts[i].clone()
    }

    fn sub_family(&self, i: usize) -> Result<Option<Self>, Self::Error> {
        Ok(match &self.parts[i] {
            V::Held(n) if matches!(n.shape, Shape::Family(_)) => Some(n.clone()),
            _ => None,
        })
    }
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
    ///
    /// Proof, by induction on the depth of `self`. A function `g` is in a type `t` exactly
    /// when `t.functions()`: that is how [`matches_any`] tests a bare function (`Pattern::Is`
    /// on anything not data and not held). `Type::member`'s `Value::Family(_)` arm answers
    /// `self.functions()` for every family, the empty one too, so the empty family is in `t`
    /// exactly when `g` is. A data part is kept as it is. A held part is its own stand-in, in
    /// each type exactly when the part is, by the induction. The tuple or atom is rebuilt with
    /// the same shape: a tuple, or the atom's name and fields with the parts in field order,
    /// as [`Value::atom_named`] keeps them; and `Type::contains` reads a tuple and an
    /// atom's payload part by part (`Member::Tuple`), and an atom with fields by its name and
    /// its payload type's `structs` flag alone. So each test `contains` makes of a part gives
    /// the answer it gives for that part of `self`. A held family is rebuilt with its keys
    /// and each part beneath its own key ([`HeldFamily::with_parts`]), and a family is read
    /// as a whole by `functions()`. Test: `l01_17_value_representation::equality` and
    /// `function_in_payload_run` build held values; no test was found that runs `is` on one.
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
                    let v = match &h.shape {
                        Shape::Tuple => Value::tuple(done),
                        Shape::Atom(name, fields) => Value::Atom(Atom {
                            name: name.clone(),
                            fields: fields.clone(),
                            payload: Some(done.into()),
                        }),
                        // Each entry goes beneath its own key, and the keys are the distinct
                        // top-level keys of one family, so no two entries collide and none has
                        // an empty keypath: `with_parts` cannot fail.
                        Shape::Family(f) => Value::Family(
                            f.with_parts(done)
                                .expect("the keys of a held family made a family"),
                        ),
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
    /// Shared, so that a closure given back apart from the run ([`made`]) keeps its body.
    body: &'t Shared,
    /// The body's position, when provenance is recorded.
    at: At,
    env: Env<'t>,
    drops: Rc<Drops<'t>>,
    /// The parameter list [`Prim::Place`] gave the closure, by which [`Prim::CallNamed`]
    /// places a call's arguments; none for a closure no `place` made. A positional call
    /// ignores it.
    placed: Option<Rc<Placed<'t>>>,
}

/// The parameter list of a function value ([`Prim::Place`]): the literal table, shared by
/// every closure of the one function, and the lambda that fills its defaults, made in the
/// declaration's scope, or none for a function without defaults.
struct Placed<'t> {
    table: Value,
    fill: Option<V<'t>>,
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

/// Where the entry at one key of a definedness `fix` stands. Every attempt shares the one list
/// of these, so an attempt costs nothing for the entries it does not read.
enum Settled {
    /// Not defined, and neither being demanded nor stalled.
    Open,
    /// Being demanded.
    Busy,
    /// Stalled on a cycle, or on an entry that is.
    Stalled,
    /// Defined, with the round that defined it.
    Defined(Value, u64),
}

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
/// family it read and the position in that `fix`'s domain of the key it read there.
enum Stop {
    Error(KernelError),
    Undefined { fix: u64, i: usize },
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
    /// Which pushes to the port commute, which decides where a pure region may push to it
    /// (`Evaluator::check_push`).
    pub commutes: Commutes,
}

/// The `commutes` value of an output port (DESIGN.md sec:ports, "Operations on one port"), as
/// far as the kernel needs it: which pushes a pure region may make (sec:kernel, reference
/// semantics, (h); QUESTIONS A108). The port value `#distinctKeys` does not arise here: the
/// kernel's pushes are whole-value pushes with no key.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Commutes {
    /// `#none`: two pushes never commute, so no pure region pushes to the port.
    #[default]
    None,
    /// `#keypath`: two pushes commute when their keypaths differ, and the port's log is in
    /// the order of those keypaths. A pure region whose entries each have a keypath, `fam`,
    /// `reindex` and `discard`, may push to it; `fold` and `fix` may not.
    Keypath,
    /// `#all`: every two pushes commute, so any pure region may push to the port.
    All,
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
    /// keep them in [`World::reads`] (which keys them by their canonical forms, [`Reads`]),
    /// and a replay is not given them. By default the world keeps them.
    fn keeps_answers(&self) -> bool {
        false
    }
}

/// The ports a program runs against: one wave of inputs, and the outputs it writes
/// (sec:ports). Each input port holds its whole value for the wave; a lookup port answers
/// each key once, and the answers are kept, so the wave sees one value at each key. In the
/// terms of DESIGN sec:ports, "Push ports and pull ports", `inputs` holds the push ports, read
/// whole as one wave until each arrival starts its own (plan row PORT-push-pull-kernel), and
/// the pull ports whose value is fixed for the run, the arguments; `sources` holds the pull
/// ports asked when a read reaches them.
#[derive(Clone, Debug, Default)]
pub struct World {
    /// The input ports by name.
    pub inputs: BTreeMap<String, Value>,
    /// The output ports by name.
    pub outputs: BTreeMap<String, Output>,
    /// The lookup ports by name.
    pub sources: BTreeMap<String, Arc<dyn Lookup>>,
    /// The keys read from each lookup port and the values read there ([`Reads`]): what a
    /// replay of the wave must supply.
    pub reads: BTreeMap<String, Reads>,
}

/// The keys read from one lookup port and the value read at each, each key kept by its
/// canonical form ([`Canon`]), so a key is found without reading a string's bytes or a shared
/// tuple twice (item WORLD-reads-canon-keys).
// Complexity tradeoff: a map ordered by `Value` compares keys byte by byte and tuple by tuple,
// so a key holding a join doubled k times, 2^k bytes in O(k) nodes, read again at an equal key
// built apart, compares 2^k bytes, and a tuple holding itself doubled k times is read as a tree,
// 2^k parts; neither ends at k = 40. Used: each key is named once when read, O(n log N)
// dictionary steps for n string nodes not named before and N bytes, and O(p log T) for p
// tuple parts not read before and T tuples named, a shared tuple read once by its id
// ([`Namer::canon`]); then a lookup by the form hashes a few words. Tradeoff: each node and
// tuple named is kept while the world lives, as its key is. The replay order, `Value`'s order,
// is made once, when the wave's record is taken ([`Reads::into_map`]), O(r log r) comparisons
// of r keys. Tests
// `m0_09_kernel_evaluator::a_lookup_port_read_at_a_long_join_or_a_doubled_tuple_is_asked_once`
// and `m0_09_kernel_evaluator::bench::scaling::reading_a_port_at_doubled_keys_scales`.
#[derive(Clone, Debug, Default)]
pub struct Reads {
    /// The names of the keys' strings and tuples, shared by the clones of one world: a namer
    /// only adds names, so a clone that names more gives the same forms to the keys it holds.
    namer: Arc<Mutex<Namer>>,
    /// Each key, by its form, with the value read there.
    answers: HashMap<Canon, (Value, Value)>,
}

impl Reads {
    /// The value read at `k`, asking `ask` for it the first time; the answer is kept unless
    /// `ask` fails.
    pub fn get_or_ask<E>(
        &mut self,
        k: Cow<'_, Value>,
        ask: impl FnOnce(&Value) -> Result<Value, E>,
    ) -> Result<Value, E> {
        // A poisoned lock leaves a namer whose maps hold only finished entries (each insert is
        // one call), so its names are still those of equal values; it is read on.
        let canon = (self.namer.lock())
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .canon(&k);
        if let Some((_, v)) = self.answers.get(&canon) {
            return Ok(v.clone());
        }
        let v = ask(&k)?;
        self.answers.insert(canon, (k.into_owned(), v.clone()));
        Ok(v)
    }

    /// The number of keys read.
    pub fn len(&self) -> usize {
        self.answers.len()
    }

    /// Whether no key was read.
    pub fn is_empty(&self) -> bool {
        self.answers.is_empty()
    }

    /// The keys and the values read there, in the order of the keys, the replay order.
    pub fn into_map(self) -> BTreeMap<Value, Value> {
        self.answers.into_values().collect()
    }
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
                commutes: Commutes::None,
            },
        );
        self
    }

    /// Adds an unbounded output port whose pushes commute as `commutes` says.
    pub fn commuting_output(mut self, name: &str, commutes: Commutes) -> Self {
        self.outputs.insert(
            name.into(),
            Output {
                commutes,
                ..Output::default()
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
    /// The steps left, when [`Evaluator::with_fuel`] set a number; `None`, as
    /// [`Evaluator::new`] makes it, counts no steps, so [`KernelError::OutOfFuel`] cannot
    /// arise.
    fuel: Option<u64>,
    /// Above zero while evaluating the closure of a pure region (`fam`, `reindex`,
    /// `discard`, `fold`, `fix`), where a call of a called lookup port is a type error, a push
    /// is one unless its port's `commutes` allows it, and a read of a port is not one
    /// ([`Evaluator::check_impure`]).
    pure: usize,
    /// How many of the open pure regions are a `fold` or a `fix`, whose applications have no
    /// keypath, so that a push inside one, at any depth, has no keypath to take its order from.
    unkeyed: usize,
    schedule: Schedule,
    /// The number of definedness `fix` evaluations begun, which names each one's family.
    fixes: u64,
    trace: Option<Trace>,
    /// The source sites of the program's nodes (plan row RT-sites), when it has them.
    sites: Option<Arc<Sites>>,
    /// The site of the node the last run stopped at with an error, if it has one.
    failed: Option<Span>,
    /// Whether the next run stops at a panic ([`Evaluator::panic_on_run`]); debug builds only.
    #[cfg(debug_assertions)]
    panic_on_run: bool,
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
            fuel: None,
            pure: 0,
            unkeyed: 0,
            schedule: Schedule::default(),
            fixes: 0,
            trace: None,
            sites: None,
            failed: None,
            #[cfg(debug_assertions)]
            panic_on_run: false,
        }
    }

    /// Makes every later [`Evaluator::run`] and [`Evaluator::run_made`] panic, as a broken check of
    /// zedc's own code does: a debug build's way for the tests to reach the report of a bug in
    /// zedc, which no program reaches on purpose, on both engines (plan row EXE-panic-status).
    /// `zedc run` panics at the run of `main`; an executable at the first node its code passes to
    /// the kernel, inside a runtime hook that the machine code called.
    #[cfg(debug_assertions)]
    pub fn panic_on_run(&mut self) {
        self.panic_on_run = true;
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
        self.fuel = Some(fuel);
        self
    }

    /// Evaluates a closed term, expecting data.
    pub fn run(&mut self, term: &Term) -> Result<Value, KernelError> {
        self.stop_if_test_bug();
        match self.run_in(term, None, None, false)? {
            Ran::Data(v) => Ok(v),
            Ran::Made(_) => unreachable!("a run expecting data gives data"),
        }
    }

    /// Evaluates a closed term, which may give a function or a value that holds one, as
    /// [`Evaluator::run`] does but for that: its value apart from the run ([`Made`]). A back
    /// end that runs one node in the kernel takes back what the node makes, a family of
    /// functions included (rows FAIL-native-fam-result-holds-function and
    /// FAIL-machine-held-family).
    pub fn run_made(&mut self, term: &Term) -> Result<Made, KernelError> {
        self.stop_if_test_bug();
        match self.run_in(term, None, None, true)? {
            Ran::Made(m) => Ok(m),
            Ran::Data(_) => unreachable!("a run apart gives its value apart"),
        }
    }

    /// Panics after [`Evaluator::panic_on_run`], in a debug build; does nothing otherwise.
    /// [`Evaluator::run`] and [`Evaluator::run_made`] both stop here, at one source line, since
    /// the report of a bug in zedc names the line and `zedc run` (which runs `main` by `run`)
    /// and an executable (whose runtime hooks run a node by `run_made`) must give the same
    /// report (row FAIL-stops-bug-site-run-made). [`Evaluator::run_under`] does not stop here:
    /// it runs the checker's constants, not the program.
    fn stop_if_test_bug(&self) {
        #[cfg(debug_assertions)]
        assert!(
            !self.panic_on_run,
            "the run of the program does not stop here (a test stopped it, ZEDC_TEST_BUG)"
        );
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
        // It does not stop where `ZEDC_TEST_BUG` stops the program's run
        // ([`Evaluator::stop_if_test_bug`]): it runs the build stage's terms, not the program.
        // Proof that no run reaches this with the flag set (plan row PROOF-run-under-test-bug):
        // the flag is set only by `panic_on_run`, whose one caller (zedc's run.rs, the run of
        // `main`) sets it on the evaluator of that run, which never runs under globals; the one
        // caller of `run_under` (zedc-stage's `Mixer::run_under`) calls it on an evaluator it
        // has just made by `Evaluator::new`, which leaves the flag unset. The assertion checks
        // that this still holds for any new caller (test
        // `a_run_under_globals_given_an_evaluator_set_to_stop_panics`).
        #[cfg(debug_assertions)]
        assert!(
            !self.panic_on_run,
            "a run under globals is never asked to stop (ZEDC_TEST_BUG stops the program's run)"
        );
        match self.run_in(term, Some(globals), global_env(reads), false)? {
            Ran::Data(v) => Ok(v),
            Ran::Made(_) => unreachable!("a run expecting data gives data"),
        }
    }

    /// Runs `term`; gives its value as data, or apart from the run when `apart`.
    fn run_in<'t>(
        &mut self,
        term: &'t Term,
        globals: Option<&'t Globals>,
        env: Env<'t>,
        apart: bool,
    ) -> Result<Ran, KernelError> {
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
            vals: Vec::new(),
        };
        let out = machine.run(term, env);
        let ran = out.is_ok();
        // Made apart while the machine lives: a closure's environment may name its globals.
        let out = match (apart, out) {
            (true, Ok(V::Data(v))) => Ok(Ran::Made(Made {
                nodes: vec![MadeNode::Data(v)],
            })),
            (true, Ok(v)) => machine.made(v).map(Ran::Made),
            (false, Ok(V::Data(v))) => Ok(Ran::Data(v)),
            (false, Ok(V::Held(_))) => Err(Stop::Error(KernelError::Type(
                "the program's result holds a function".into(),
            ))),
            (false, Ok(_)) => Err(Stop::Error(KernelError::Type(
                "the program's result is a function".into(),
            ))),
            (_, Err(e)) => Err(e),
        };
        let failed = machine.failed;
        drop(machine);
        drop(watch);
        self.failed = failed.and_then(|k| self.sites.as_ref()?.at(k));
        if let Some(t) = &mut self.trace {
            // A run that stopped with an error left the regions it was inside.
            t.calls.truncate(marks.0);
            t.keys.truncate(marks.1);
            t.holds = Holds::default();
            if ran {
                t.term = Some(term.clone());
            }
        }
        match out {
            Ok(ran) => Ok(ran),
            Err(Stop::Error(e)) => Err(e),
            Err(Stop::Undefined { .. }) => {
                unreachable!("only a definedness fix binds a partial family")
            }
        }
    }

    /// One step: with no fuel set, nothing; with fuel, one less, and [`KernelError::OutOfFuel`]
    /// once none is left.
    fn burn(&mut self) -> R<()> {
        match &mut self.fuel {
            None => Ok(()),
            Some(0) => Err(KernelError::OutOfFuel.into()),
            Some(n) => {
                *n -= 1;
                Ok(())
            }
        }
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
        let i = zed_collections::index::to_u32(i, "children of a node");
        let next: At = zed_collections::index::to_u32(t.nodes.len(), "positions in a run");
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

    /// Stops with a type error when a push to `port`, whose pushes commute as `commutes` says,
    /// is made where a pure region may not make it (DESIGN.md sec:kernel, reference semantics,
    /// (h); QUESTIONS A108, which replaced the rule that refused every push in a pure region).
    ///
    /// Allowed: any push outside a pure region; a push to a `#all` port anywhere; a push to a
    /// `#keypath` port inside `fam`, `reindex` and `discard` with no `fold` or `fix` open
    /// around it. Proof that these keep the region's meaning, that is, that the port's log does
    /// not depend on the order of the region's steps: for `#all`, every two pushes commute, so
    /// any order of them is the same log as a value (the port's declaration says so, and the
    /// checker trusts it, as sec:ports says). For `#keypath`, the port's log is the pushes in
    /// the order of their keypaths; this evaluator runs the entries of `fam` in key order
    /// (`begin_fam`), the leaves of `reindex` in keypath order (`begin_reindex`) and the
    /// entries of `discard` top down in key order (`discard`), a prefix before its extensions,
    /// so, nested at any depth, it makes the pushes in the lexicographic order of their
    /// keypaths, which is that log; a schedule that runs the entries in another order or at
    /// once must sort the pushes by keypath to give it. Inside a `fold` or a `fix` the steps
    /// have no keypath: a `fold` regroups its applications on the canonical tree, and a
    /// definedness `fix` runs its entries in rounds whose order the cone decides, so a
    /// `#keypath` push there is refused, as is any `#none` push. The log port, which the
    /// spec allows inside `fold` and `fix`, has no kernel form yet (sec:ports, "Logging").
    /// Each refusal keeps the suffix "used inside a pure region", which zedc-stage's
    /// `error_as_written` reads.
    /// Tests: `m0_09_kernel_evaluator::a_commuting_push_inside_a_pure_region_is_accepted` and
    /// `a_port_inside_a_pure_region_is_rejected`.
    // Alternatives weighed: (1) refuse every push in a pure region, the rule (h) had before
    // QUESTIONS A108; the author's answer allows the order-independent ones. (2) Track the
    // innermost region only; wrong for a `fam` inside a `fold`, whose entries have keypaths
    // but whose `fold` applications may be regrouped, so the count of open `fold` and `fix`
    // regions is kept instead. Cost: two comparisons of counters per push, as before one.
    fn check_push(&self, port: &str, commutes: Commutes) -> R<()> {
        if self.pure == 0 {
            return Ok(());
        }
        match commutes {
            Commutes::All => Ok(()),
            Commutes::Keypath if self.unkeyed == 0 => Ok(()),
            Commutes::Keypath => type_err(format!(
                "port `{port}`, whose pushes take their order from a keypath, pushed in a `fold` \
                 or `fix` step, which has none: port `{port}` used inside a pure region"
            )),
            Commutes::None => type_err(format!("port `{port}` used inside a pure region")),
        }
    }

    /// Stops with a type error when a call of the called lookup port `port` is made inside a
    /// pure region.
    ///
    /// A read of a port is allowed there (FAIL-port-read-in-mapped-function: DESIGN.md
    /// sec:ports reads `main::files` "from any function at any depth of calls", and `map`
    /// elaborates to a `fam`, so a function given to `map` that reads a file reads it inside
    /// one). Proof that the read keeps the region pure, that is, that its value does not depend
    /// on the order of the region's steps or on how many times a step runs: an input port's
    /// value is fixed for the whole wave before the run starts (`World::inputs`), and a lookup
    /// port is asked at most once per key, its answer kept for the rest of the run, in
    /// `World::reads` or, for a port that `keeps_answers`, by the port itself (`ask_port`). So
    /// a read gives the same value at a key wherever and however often it is evaluated. A
    /// push, which appends to a log whose order is observable, is decided by its port's
    /// `commutes` ([`Evaluator::check_push`]). Refused here, since the proof does not cover
    /// it: a call of a called lookup port, which only the stager
    /// makes (its stubs, zedc-stage `Port`), whose answer runs a further evaluation, and which
    /// the stager counts on stopping inside a pure region so that such a call is run as
    /// written (zedc-stage `error_as_written`, `Mixer::eval`). A
    /// failed read stops the run with its port error as outside a region: the one frame that
    /// catches a stop, a definedness `fix` entry, takes only `Stop::Undefined`
    /// (`entry_ended`).
    // Alternatives weighed: (1) elaborate a `map`, `where`, fold or nested map whose function
    // may read a port to a non-pure form, such as a `gen` over the keys; this needs the
    // checker's reads-a-port fact at every higher-order form, a second elaboration of each,
    // and a call through a function value the checker cannot see counted as reading, and it
    // loses the region's freedom of order for no gain in meaning, since the read is order-free
    // as shown above. (2) Read every port value before the region; impossible for a lookup
    // port, whose keys are computed inside it. Used: the check moved to the two operations
    // that are order-dependent. Cost: unchanged, one comparison of a counter per
    // called-port call, none per read. Pushes: [`Evaluator::check_push`].
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
    /// Evaluates an undefined entry, at a position in its `fix`'s domain, where an attempt
    /// reads it.
    Demand(Rc<Definedness<'t>>, usize),
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
    /// Ends a pure region; `unkeyed` when it is a `fold` or a `fix` (`Evaluator::unkeyed`).
    Pure { unkeyed: bool },
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
    /// Each entry made, key then value, `None` for the next of `parts`.
    out: Vec<(Value, Option<Value>)>,
    /// The entries made that are no data, functions or values that hold one, in key order.
    parts: Vec<V<'t>>,
}

/// A `reindex` running: the leaves left, the leaf being moved and its new key. A leaf of a
/// family whose entries hold functions may be a function, or hold one (row
/// FAIL-held-family-operators).
struct Reindex<'t> {
    leaves: std::vec::IntoIter<(Keypath, V<'t>)>,
    kf: Operator<'t>,
    vf: Operator<'t>,
    from: Option<usize>,
    /// The path, the path as a value and the value of the leaf being moved.
    path: Keypath,
    args: Option<(Value, V<'t>)>,
    key: Option<Value>,
    /// Whether the leaf being moved is a keypath that ends early, above an empty level.
    short: bool,
    /// Each leaf moved, keypath then value, `None` for the next of `parts`.
    out: Vec<(Keypath, Option<Value>)>,
    /// The leaves moved that are no data, in the order moved.
    parts: Vec<V<'t>>,
}

/// One level of a `discard` running: the entries left and the entry being tested.
struct Level<'t> {
    entries: std::vec::IntoIter<(Value, V<'t>)>,
    entry: Option<V<'t>>,
    /// Each entry kept, key then value, `None` for the next of `parts`.
    out: Vec<(Value, Option<Value>)>,
    /// The entries kept that are no data, in key order.
    parts: Vec<V<'t>>,
}

/// A `discard` running: the levels entered, each a family nested in the one before, and the
/// keypath of the entry being tested.
struct Discard<'t> {
    levels: Vec<Level<'t>>,
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

/// A `gen` running. A frame may be a function or hold one (DESIGN.md step L1.17: only a use
/// that needs data is an error): the frames of `foldl` and `foldr` are `(entry, acc)`, and an
/// accumulator may be a function, as in `[1, 2].foldl(y -> y, (a, x) -> (y -> a(y) + x))`
/// (row FAIL-fold-rotating-tuple-rounds). Before, a frame had to be data, and such a fold,
/// which the checker takes, stopped with zedc's message for a bug of its own.
struct Gen<'t> {
    frames: Vec<V<'t>>,
    from: Option<usize>,
    step: Operator<'t>,
    guard: Operator<'t>,
}

/// A definedness `fix` running in rounds: the entries left in this round, those for the next,
/// and for each undefined entry read, the entries waiting on it.
/// Entries are named by their keys' positions in the domain.
struct Rounds<'t> {
    fix: Rc<Definedness<'t>>,
    /// The SplitMix64 generator (zed-hash's, where its source is), which draws the visiting
    /// order of [`Schedule::Chaotic`] by its Fisher–Yates shuffle.
    rng: Option<SplitMix64>,
    /// By position: the entries waiting on that entry.
    waiting: Vec<Vec<usize>>,
    queue: std::vec::IntoIter<usize>,
    ready: Vec<usize>,
    defined: Vec<usize>,
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

/// An attempt at the entry at position `i` of the domain of the `fix` of `by`. `mark` holds
/// the lengths of the trace's facts, calls and keys when it began.
struct Entry<'t> {
    i: usize,
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
    /// Spare room for the data arguments of a primitive ([`Self::prim`]), empty between steps.
    vals: Vec<Value>,
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
                    placed: None,
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

    /// The environment of a closure of a lambda whose body is `body`, made in `env`: the
    /// bindings of `env` of the names the body reads, its nested lambdas' bodies included, and
    /// no others (DESIGN.md sec:generations, "A closure holds only the values it reads"; row
    /// CLOSURE-captures-read-only). A binding of the globals is a position and holds no value,
    /// so keeping one keeps nothing alive.
    // Complexity tradeoff: the naive closure keeps `env` whole, O(1) per closure since `env` is
    // a persistent map, but every value in scope then lives as long as the closure, read or
    // not: a closure made beside a large value it never reads keeps that value. Used: the
    // names the body reads are found once per body for the life of the term ([`made::reads`],
    // kept on the body), and each closure copies the bindings of those names, O(r log n) for
    // r names read in a scope of n, into a map of r entries, O(r) memory. Tradeoff: a closure
    // costs O(r log n) where it cost O(1). A map restricted in place would share `env`'s nodes
    // and so keep its other values alive, which is what this removes. The names are a
    // superset of the free ones (see [`made::reads`]): the lambda's own parameters, which
    // `env` may also bind, and a name bound above a node the body shares, that `env` also
    // binds, are kept though never read from `env`. The exact set of free names of a term
    // that shares subterms costs, by sets kept per shared subterm, O(n²) on a chain of n
    // `let`s whose last body reads them all (zedc-stage `Sets` keeps that down by hash-consed
    // tries with no proved bound), so at a shared node the superset is kept. Test
    // `eval::tests::a_closure_holds_only_the_values_its_body_reads`; scaling benchmarks
    // `l01_34_memory::bench::closures_made_in_a_scope_of_n_names_scale` and
    // `closures_kept_from_a_scope_of_n_names_scale`.
    fn captures(&mut self, body: &'t Shared, env: &Env<'t>) -> Env<'t> {
        let names = made::reads(body);
        names.iter().fold(None, |out, x| match env::entry(env, x) {
            Some((name, b)) => env::insert(out, name, b.clone()),
            None => out,
        })
    }

    /// Goes on from `frame` with how the term above it ended.
    fn resume(&mut self, frame: Frame<'t>, out: R<V<'t>>) -> R<Step<'t>> {
        match frame {
            Frame::Fact { at, outer, union } => self.fact(at, outer, union, out),
            Frame::Pure { unkeyed } => {
                self.ev.pure -= 1;
                self.ev.unkeyed -= usize::from(unkeyed);
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
        let union = matches!(term, Term::Prim(Prim::Union | Prim::ListConcat, _));
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
        // The two reads of a union, or of `++` on lists, whose entries are its operands' entries
        // under other keys, are the facts of its operands, whose data were read when they
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
                env: self.captures(body, &env),
                drops: self.drops.clone(),
                placed: None,
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
                self.begin_pure(true);
                self.operand(term, at, Vec::new(), None, env)
            }
            Term::Fam { .. }
            | Term::Reindex { .. }
            | Term::Discard { .. }
            | Term::Fold { .. }
            | Term::Gen { .. } => self.operand(term, at, Vec::new(), None, env),
            // A read is allowed inside a pure region ([`Evaluator::check_impure`]).
            Term::Read(port) => match self.ev.world.inputs.get(&**port) {
                Some(v) => give(v.clone()),
                None if self.ev.world.sources.contains_key(&**port) => {
                    Ok(Step::Give(V::Source(port.clone())))
                }
                None => Err(KernelError::UnknownPort(port.to_string()).into()),
            },
            Term::Push(port, value) => {
                self.wait(Wait::Push(port));
                Ok(Step::Eval(value, self.ev.child(at, 0), env))
            }
        }
    }

    /// Begins a pure region; `unkeyed` for a `fold` or a `fix`, whose steps have no keypath.
    fn begin_pure(&mut self, unkeyed: bool) {
        self.ev.pure += 1;
        self.ev.unkeyed += usize::from(unkeyed);
        self.frames.push(Frame::Pure { unkeyed });
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
            // `map` reads a family whose entries may be functions (DESIGN.md
            // sec:values_morphisms); it reads its domain's keys only. `where` (a `discard`) and
            // a remap (a `reindex`) pass such entries to their tests and maps, and keep them
            // (row FAIL-held-family-operators; DESIGN.md L1.17: only a use that needs data, such
            // as showing or `==`, is an error).
            0 if matches!(
                region,
                Term::Fam { .. } | Term::Reindex { .. } | Term::Discard { .. }
            ) && matches!(&v, V::Held(h) if matches!(h.shape, Shape::Family(_))) =>
            {
                Ok(v)
            }
            0 if holds_data => Ok(V::Data(Value::Family(family(data(v)?)?))),
            // A `gen`'s first frame may hold a function, as each of its frames may (`Gen`).
            0 if matches!(region, Term::Gen { .. }) => Ok(v),
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
        let first = next();
        // A family whose entries hold functions: `map` reads its keys, a remap its leaves and
        // `where` its entries, each part as it is.
        if let V::Held(h) = &first
            && let Shape::Family(f) = &h.shape
        {
            match region {
                Term::Fam { var, body, .. } => {
                    let keys: Vec<Value> = f.keys().cloned().collect();
                    return self.begin_fam(var, body, at, env, keys);
                }
                Term::Reindex { .. } => {
                    let leaves = held_leaves(h);
                    let (kf, vf) = (next(), next());
                    return self.begin_reindex(at, leaves, kf, vf, from);
                }
                Term::Discard { .. } => {
                    let level = held_level(h);
                    return self.begin_discard(at, level, next(), from);
                }
                _ => {}
            }
        }
        if let Term::Gen { pos, .. } = region {
            let step = (next(), Some(self.ev.child(at, 1)));
            let guard = (next(), Some(self.ev.child(at, 2)));
            let st = Box::new(Gen {
                frames: vec![first],
                from,
                step,
                guard,
            });
            return match pos {
                GuardPos::Before => self.gen_guard(st),
                GuardPos::After => self.gen_step(st),
            };
        }
        let first = data(first)?;
        match region {
            Term::Fam { var, body, .. } => {
                let keys: Vec<Value> = family(first)?.keys().cloned().collect();
                self.begin_fam(var, body, at, env, keys)
            }
            Term::Reindex { .. } => {
                let leaves = family(first)?.leaves().into_iter();
                let leaves = leaves.map(|(p, v)| (p, V::Data(v))).collect();
                let (kf, vf) = (next(), next());
                self.begin_reindex(at, leaves, kf, vf, from)
            }
            Term::Discard { .. } => {
                let level = level(&family(first)?);
                self.begin_discard(at, level, next(), from)
            }
            Term::Fold {
                identity, depth, ..
            } => {
                let op = (next(), Some(self.ev.child(at, 1)));
                let identity = match identity {
                    Some(_) => Some(data(next())?),
                    None => None,
                };
                self.begin_pure(true);
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
                let Some(commutes) = self.ev.world.outputs.get(&**port).map(|o| o.commutes) else {
                    return Err(KernelError::UnknownPort(port.to_string()).into());
                };
                self.ev.check_push(port, commutes)?;
                let out = self
                    .ev
                    .world
                    .outputs
                    .get_mut(&**port)
                    .expect("the port was found above");
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
                match v {
                    V::Data(v) => st.out.push((k, Some(v))),
                    v => {
                        st.parts.push(v);
                        st.out.push((k, None));
                    }
                }
                self.fam(st)
            }
            Wait::ReindexKey(mut st) if st.short => {
                // A keypath above an empty level has no leaf for the value map; the empty level
                // goes beneath the part of the new keypath that its own keys give.
                st.args = None;
                self.short_paths.pop();
                self.ev.leave(st.path.len());
                if let Some(path) = placed(data(v)?) {
                    st.out.push((path, Some(Value::Family(Family::new()))));
                }
                self.reindex(st)
            }
            Wait::ReindexKey(mut st) => {
                st.key = Some(data(v)?);
                let (p, leaf) = st.args.take().expect("a `reindex` has a leaf in hand");
                self.ev.aim(st.vf.1, &[st.from; 2]);
                let step = self.apply(&st.vf.0, vec![V::Data(p), leaf]);
                self.wait(Wait::ReindexValue(st));
                step
            }
            Wait::ReindexValue(mut st) => {
                self.ev.leave(st.path.len());
                let key = key_of(st.key.take().expect("a `reindex` has a key in hand"));
                // A value map may give a function, or a value holding one, as `map` may.
                match v {
                    V::Data(value) => st.out.push((key, Some(value))),
                    v => {
                        st.parts.push(v);
                        st.out.push((key, None));
                    }
                }
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
                st.frames.push(v);
                st.from = self.ev.last_fact();
                self.gen_guard(st)
            }
            Wait::GenGuard(mut st) => {
                self.ev.leave(1);
                match v {
                    V::Data(Value::Bool(true)) => self.gen_step(st),
                    V::Data(Value::Bool(false)) => self.gen_end(*st),
                    v if matches!(v, V::Data(Value::Atom(_))) || held_atom(&v) => {
                        st.frames.push(v);
                        self.gen_end(*st)
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

    /// [`Prim::Place`]: the closure with its parameter list; [`Prim::CallNamed`]: the call
    /// placed by the list of the function called (DESIGN.md sec:values_morphisms, "The
    /// function called places the arguments"). The checker has checked the call against every
    /// function the value may hold, so each error here is one of elaboration.
    // Complexity tradeoff: the naive placing searches the parameter names for each named
    // argument, O(p·a) for p parameters and a arguments. Used: the call's names and the
    // function's are each sorted when the unit is compiled (`shape` and `table` are
    // literals), and one merge of the two lists places every named argument, O(p + a) name
    // comparisons, each O(the name's length); no name is built or hashed. The slots take one
    // vector of p, and the call of `fill` one of p plus the defaulted parameters.
    fn placing(&mut self, p: Prim, mut args: Vec<V<'t>>) -> R<Step<'t>> {
        let bad = || {
            type_err(format!(
                "{} was given arguments elaboration does not make",
                p.named(None)
            ))
        };
        if args.len() < 2 {
            return bad();
        }
        let given = args.split_off(2);
        let f = args.pop().expect("two arguments");
        let Some(V::Data(Value::Tuple(lit))) = args.pop() else {
            return bad();
        };
        if p == Prim::Place {
            let V::Closure(c) = f else {
                return bad();
            };
            if given.len() > 1 {
                return bad();
            }
            let fill = given.into_iter().next();
            return Ok(Step::Give(V::Closure(Rc::new(Closure {
                params: c.params,
                body: c.body,
                at: c.at,
                env: c.env.clone(),
                drops: c.drops.clone(),
                placed: Some(Rc::new(Placed {
                    table: Value::Tuple(lit),
                    fill,
                })),
            }))));
        }
        let int = |v: &Value| match v {
            Value::Int(i) => usize::try_from(*i).ok(),
            _ => None,
        };
        // `opt`, when the shape has it, gives each sorted name the index of a flag among the
        // flags that follow the arguments, or -1: a name whose flag is true is left out, and
        // the function called fills its parameter with its own default. The fill of a
        // curried call's result passes it, which forwards the parameters its own call left out
        // (row CALL-curried-placed).
        let (k, names, at, opt) = match lit.as_slice() {
            [k, Value::Tuple(names), Value::Tuple(at)] => (k, names, at, None),
            [k, Value::Tuple(names), Value::Tuple(at), Value::Tuple(opt)] => {
                (k, names, at, Some(opt.as_slice()))
            }
            _ => return bad(),
        };
        let (Some(k), names, at) = (int(k), names.as_slice(), at.as_slice()) else {
            return bad();
        };
        let mut given = given;
        let flags = match opt {
            None => Vec::new(),
            Some(opt) => {
                let q = opt
                    .iter()
                    .filter(|o| matches!(o, Value::Int(i) if *i >= 0))
                    .count();
                if opt.len() != names.len() || given.len() < q {
                    return bad();
                }
                given.split_off(given.len() - q)
            }
        };
        // Whether the name at `i` among the sorted names is left out by its flag.
        let left_out = |i: usize| match opt.and_then(|o| o.get(i)).and_then(int) {
            Some(x) => matches!(flags.get(x), Some(V::Data(Value::Bool(true)))),
            None => false,
        };
        let placed = match &f {
            V::Closure(c) => c.placed.clone(),
            _ => None,
        };
        let Some(placed) = placed else {
            // A function value with no list, a lambda or a primitive, takes its arguments by
            // position, and a function of one parameter its one argument in either form; an
            // argument left out by its flag is not passed.
            if opt.is_some() {
                let mut dropped = vec![false; given.len()];
                for i in (0..names.len()).filter(|&i| left_out(i)) {
                    match at.get(i).and_then(int).and_then(|a| dropped.get_mut(k + a)) {
                        Some(d) => *d = true,
                        None => return bad(),
                    }
                }
                given = (given.into_iter().zip(dropped))
                    .filter_map(|(v, d)| (!d).then_some(v))
                    .collect();
            }
            if names.iter().enumerate().all(|(i, _)| left_out(i)) || given.len() == 1 {
                return self.apply(&f, given);
            }
            return type_err(
                "a function value without a parameter list was called with named \
                             arguments",
            );
        };
        let Value::Tuple(table) = &placed.table else {
            return bad();
        };
        let [
            n,
            Value::Tuple(pnames),
            Value::Tuple(places),
            Value::Tuple(defaulted),
        ] = table.as_slice()
        else {
            return bad();
        };
        let (Some(n), pnames, places, defaulted) = (
            int(n),
            pnames.as_slice(),
            places.as_slice(),
            defaulted.as_slice(),
        ) else {
            return bad();
        };
        if k > n || given.len() != k + names.len() {
            return bad();
        }
        let mut given: Vec<Option<V<'t>>> = given.into_iter().map(Some).collect();
        let mut slots: Vec<Option<V<'t>>> = Vec::with_capacity(n);
        slots.extend(given[..k].iter_mut().map(Option::take));
        slots.resize(n, None);
        let (mut i, mut j) = (0, 0);
        while let Some(name) = names.get(i) {
            if left_out(i) {
                i += 1;
                continue;
            }
            let Some(q) = pnames.get(j) else {
                return type_err(format!("the function called has no parameter {name}"));
            };
            match name.cmp(q) {
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Less => {
                    return type_err(format!("the function called has no parameter {name}"));
                }
                std::cmp::Ordering::Equal => {
                    let (Some(to), Some(a)) =
                        (places.get(j).and_then(int), at.get(i).and_then(int))
                    else {
                        return bad();
                    };
                    match (slots.get_mut(to), given.get_mut(k + a)) {
                        (Some(s @ None), Some(x)) => *s = x.take(),
                        _ => return bad(),
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        let missing = |j: usize| {
            let name = (places.iter().position(|q| int(q) == Some(j)))
                .map_or_else(|| format!("{j}"), |i| pnames[i].to_string());
            type_err(format!("the call gives no value to the parameter {name}"))
        };
        let Some(fill) = &placed.fill else {
            let mut call = Vec::with_capacity(n);
            for (j, s) in slots.into_iter().enumerate() {
                match s {
                    Some(v) => call.push(v),
                    None => return missing(j),
                }
            }
            return self.apply(&f, call);
        };
        let mut call = Vec::with_capacity(n + defaulted.len());
        let mut flags = Vec::new();
        for (j, s) in slots.into_iter().enumerate() {
            let d = matches!(defaulted.get(j), Some(Value::Bool(true)));
            if d {
                flags.push(V::Data(Value::Bool(s.is_none())));
            }
            match s {
                Some(v) => call.push(v),
                None if d => call.push(V::Data(Value::Bool(false))),
                None => return missing(j),
            }
        }
        call.extend(flags);
        let fill = fill.clone();
        self.apply(&fill, call)
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
                let body: &'t Shared = c.body;
                Ok(Step::Call {
                    body,
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
            // A held tuple or family applied to one key reads it, as a data one does.
            V::Held(h) if h.atom().is_none() && args.len() == 1 => {
                let p = match h.shape {
                    Shape::Family(_) => Prim::Get,
                    _ => Prim::TupleGet,
                };
                let mut with_held = Vec::with_capacity(2);
                with_held.push(f.clone());
                with_held.extend(args);
                self.prim(p, with_held)
            }
            V::Partial(_) | V::Source(_) => type_err("a family is read with `[]`, not called"),
            V::Data(Value::Atom(a)) => Ok(Step::Give(V::Data(Value::Atom(a.clone())))),
            V::Held(h) if h.atom().is_some() => Ok(Step::Give(f.clone())),
            V::Held(_) => type_err("a tuple or a family is read at one key"),
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
        if !world.reads.contains_key(port) {
            world.reads.insert(port.to_string(), Reads::default());
        }
        let reads = (world.reads.get_mut(port)).expect("inserted above");
        let v = reads.get_or_ask(k, |k| {
            (source.get(k)).map_err(|why| KernelError::Port(port.to_string(), why))
        })?;
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

    /// Primitive `p` on `args`, one of which holds a function or, for a tuple, an atom or a
    /// family display, is one: a tuple, an atom or a family is made as a [`Held`], a tuple or a
    /// family is read at a key, and an atom that holds a function passes through every other
    /// primitive as any failure does.
    fn held(&mut self, p: Prim, mut args: Vec<V<'t>>) -> R<Step<'t>> {
        let drops = self.drops.clone();
        let held = |parts, shape| {
            V::Held(Rc::new(Held {
                shape,
                parts,
                drops,
            }))
        };
        if let Some(i) = family_operand(p)
            && let Some(V::Held(h)) = args.get(i)
            && matches!(h.shape, Shape::Family(_))
        {
            let h = h.clone();
            return self.held_family(p, h, &args);
        }
        match p {
            Prim::Tuple => return Ok(Step::Give(held(args, Shape::Tuple))),
            // A display with an entry that is no data (DESIGN.md sec:values_morphisms: a family
            // is a morphism, and a function may be its value): its keys, data, by the rules of
            // a data display ([`HeldFamily::new`]), and each such entry a part.
            // A key that is no data is refused, a key left without a value too (an odd count,
            // which elaboration never builds, but a term from elsewhere may: [`odd_display`]).
            Prim::Entries => {
                let given = args.len();
                let mut entries = Vec::with_capacity(given / 2);
                let mut parts = Vec::new();
                let mut it = args.into_iter();
                while let Some(k) = it.next() {
                    let V::Data(k) = k else {
                        return type_err(format!("{} applied to a function", p.named(None)));
                    };
                    let Some(v) = it.next() else {
                        return type_err(odd_display(given));
                    };
                    match v {
                        V::Data(v) => entries.push((k, Some(v))),
                        v => {
                            parts.push(v);
                            entries.push((k, None));
                        }
                    }
                }
                // Proof that `None` is not reached: `prim`, the one caller, calls `held` for
                // `Entries` only when some argument is no `V::Data` (a `V::Held` is none). The
                // loop reads every argument, as a key or a value, and returns at a key that is
                // no data, so here some value was no data and `parts` is not empty;
                // `HeldFamily::new` gives `None` only for an empty `parts`. Test
                // (PROOF-kernel-proofdoc3a-gaps (l)):
                // `l01_17_value_representation::function_in_family::a_display_with_a_key_left_without_a_value_is_refused`
                // takes each case of the loop (a function alone, a function key after an entry,
                // a function value before a key, an odd count) and would panic here on any.
                return match HeldFamily::new(entries)? {
                    Some(f) => Ok(Step::Give(held(parts, Shape::Family(f)))),
                    None => unreachable!("a display with a value that is no data has a part"),
                };
            }
            // The atom is made from marks, its payload's positions, by the rules every atom
            // follows ([`prim_data`]: its name, its field names in order, none repeated), and
            // each part is put where its mark landed.
            // Proof that each payload value is a mark, and each mark is met once: the marks
            // given are `Int(0) .. Int(n - 1)` for the `n` parts. `prim_data`'s two `Atom` arms
            // build the payload from those arguments alone: `Value::atom_with` keeps them in
            // order, and `Value::atom_named` sorts the (field, value) pairs by field and
            // unzips them, a permutation. Any other shape is an error, returned above. So
            // `shape.args()` is a permutation of the marks, and `parts[i]` is taken once.
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
                return Ok(Step::Give(held(
                    ordered,
                    Shape::Atom(shape.name, shape.fields),
                )));
            }
            // A tuple's keys are its positions; any other key misses, as for data (`prim_data`).
            Prim::TupleGet | Prim::At if matches!(&args[0], V::Held(h) if h.is_tuple()) => {
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

    /// Primitive `p` reading the held family `h`, its operand [`family_operand`] among `args`,
    /// as [`prim_on`] reads a data family: an entry is a part or data, a key that is an atom
    /// passes through, a key it lacks is `#notFound` (`#outOfBounds` for `At`), and an entry
    /// step gives the tuple `(k, v)`, held when `v` is a part.
    // Complexity tradeoff: each read is one lookup in the family's keys, O(log n), as for
    // data ([`HeldFamily`]); `first` and `last` descend one level per step, O(depth · log n).
    // The rules of each read are [`held_family_got`]'s, shared with the memory machine and
    // native code (DRY-misc-A5); this reads the key, and makes the entry tuple of a part.
    fn held_family(&mut self, p: Prim, h: Rc<Held<'t>>, args: &[V<'t>]) -> R<Step<'t>> {
        let key = match p {
            Prim::Get | Prim::TupleGet | Prim::At | Prim::Has | Prim::GetAtomKey => {
                match &args[usize::from(p != Prim::Has)] {
                    // A key the checker proved the family takes, an atom too, is read.
                    V::Data(k) if p == Prim::GetAtomKey => Some(k),
                    V::Data(k @ Value::Atom(_)) => return give(k.clone()),
                    V::Data(k) => Some(k),
                    k if held_atom(k) => return Ok(Step::Give(k.clone())),
                    _ => return type_err(format!("{} at a function", p.named(None))),
                }
            }
            Prim::EntryAfter | Prim::EntryBefore => {
                // The entry tuple given is one an entry step made: data, or held when its
                // value is a part.
                match &args[1] {
                    V::Data(Value::Tuple(e)) if e.len() == 2 => Some(&e[0]),
                    V::Held(e) if e.is_tuple() && e.parts.len() == 2 => match &e.parts[0] {
                        V::Data(k) => Some(k),
                        _ => return type_err(format!("{} at a function", p.named(None))),
                    },
                    _ => {
                        return type_err(format!(
                            "{} given something other than an entry",
                            p.named(None)
                        ));
                    }
                }
            }
            _ => None,
        };
        let Ok(got) = held_family_got(p, h, key);
        Ok(Step::Give(match got {
            FamilyGot::Data(v) => V::Data(v),
            FamilyGot::Part(v) => v,
            FamilyGot::Pair(k, v) => V::Held(Rc::new(Held {
                shape: Shape::Tuple,
                parts: vec![V::Data(k), v],
                drops: self.drops.clone(),
            })),
        }))
    }

    fn prim(&mut self, p: Prim, args: Vec<V<'t>>) -> R<Step<'t>> {
        // They take functions and any argument as it is, an atom included.
        if matches!(p, Prim::Place | Prim::CallNamed) {
            return self.placing(p, args);
        }
        if let Some(n) = p.arity()
            && args.len() != n
        {
            let s = plural(&n);
            return type_err(self.at_step(
                p,
                format!(
                    "{} takes {n} argument{s}, given {}",
                    p.named(None),
                    args.len()
                ),
            ));
        }
        // `GetAtomKey` on a function applies it to the key, an atom too: the elaborator writes
        // it for a read of a value that may be a family or a function of one parameter, and
        // the checker checked the function's arm as that application
        // (CHECK-atom-key-mixed-receiver).
        if p == Prim::GetAtomKey && matches!(args[0], V::Closure(_) | V::Prim(_)) {
            let mut args = args.into_iter();
            let f = args
                .next()
                .expect("`GetAtomKey` takes two arguments, checked above");
            return self.apply(&f, args.collect());
        }
        // A tuple, an atom or a family display made with a part that is no data, or a value
        // that holds a function given to any primitive (DESIGN.md step L1.17).
        if args.iter().any(|a| matches!(a, V::Held(_)))
            || (matches!(p, Prim::Tuple | Prim::Atom | Prim::Entries)
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
        if matches!(p, Prim::Get | Prim::GetAtomKey) && matches!(args[0], V::Partial(_)) {
            let Ok([V::Partial(part), k]) = <[V<'t>; 2]>::try_from(args) else {
                unreachable!("`Get` takes two arguments, the first matched above")
            };
            let V::Data(k) = k else {
                return type_err("a key must be data");
            };
            if let Value::Atom(_) = k
                && p == Prim::Get
            {
                return give(k);
            }
            let fix = &part.of;
            let Some(i) = position(&fix.index, &k) else {
                return give(Value::atom("notFound"));
            };
            return match &fix.settled.borrow()[i] {
                Settled::Defined(v, r) if *r < part.round => give(v.clone()),
                Settled::Open if self.ev.schedule == Schedule::Pull => {
                    Ok(Step::Demand(fix.clone(), i))
                }
                // An entry defined in this Jacobi round is not yet visible to it.
                _ => Err(Stop::Undefined { fix: fix.id, i }),
            };
        }
        // `fs[k]` on a lookup port: the world answers once, and the answer is kept.
        if matches!(p, Prim::Get | Prim::TupleGet | Prim::GetAtomKey)
            && matches!(args[0], V::Source(_))
        {
            let Ok([V::Source(port), k]) = <[V<'t>; 2]>::try_from(args) else {
                unreachable!("`Get` and `TupleGet` take two arguments, the first matched above")
            };
            // A read, allowed inside a pure region ([`Evaluator::check_impure`]).
            let V::Data(k) = k else {
                return type_err("a key must be data");
            };
            if let Value::Atom(_) = k
                && p != Prim::GetAtomKey
            {
                return give(k);
            }
            return self.ask_port(&port, as_key(&k));
        }
        // Complexity tradeoff (KERNEL-eval-step-cost): the data arguments were moved into a new
        // `Vec` on each step, an allocation and a free (250,000 steps in law_04; removing them
        // saved about 100 instructions a step, 1.4% of the test). Used: a primitive that keeps
        // none of them reads them from the machine's spare `vals`, emptied after the step, so
        // its room is allocated once a run; `Tuple` and `Path` keep theirs and take a new `Vec`,
        // as before. An early return on an error drops the spare room, which the next step
        // allocates again. Both are O(arguments) a step.
        let keeps = matches!(p, Prim::Tuple | Prim::Path | Prim::Entries);
        let mut vals = if keeps {
            Vec::with_capacity(args.len())
        } else {
            std::mem::take(&mut self.vals)
        };
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
        // `GetAtomKey` reads its atom key as data, and passes an atom family through.
        if p == Prim::GetAtomKey
            && let Some(Value::Atom(_)) = vals.first()
        {
            let out = vals.swap_remove(0);
            self.spare(vals);
            return give(out);
        }
        if p != Prim::GetAtomKey
            && !matches!(
                p,
                Prim::Tuple | Prim::Path | Prim::Entries | Prim::Atom | Prim::Eq | Prim::Ne
            )
            && vals.iter().any(|v| matches!(v, Value::Atom(_)))
        {
            let atoms = vals.drain(..).filter(|v| matches!(v, Value::Atom(_)));
            let out = Value::merge_failures(atoms);
            self.spare(vals);
            return give(out);
        }
        // A refused test answered by the order of the normal forms, which may have made the
        // primitive fail (a collision of two leaves it took as different): the refusal is the
        // cause.
        let out = if keeps {
            prim_data(p, vals)
        } else {
            let out = prim_on(p, &vals);
            self.spare(vals);
            out
        };
        if let Some((t, e)) = refused() {
            return Err(order_too_large(p, t, e).into());
        }
        match out {
            Err(KernelError::Type(m)) => type_err(self.at_step(p, m)),
            out => give(out?),
        }
    }

    /// Empties `vals` and keeps its room for the next primitive.
    fn spare(&mut self, mut vals: Vec<Value>) {
        vals.clear();
        self.vals = vals;
    }

    /// The refusal `m` of the primitive `p`, and for a step on key paths, which the compiler
    /// generates and a program never writes, the call it ran in: the innermost `reindex` key
    /// map or value map or `discard` test running, with the keys of the entry it was given,
    /// or that it ran in none of them. The walk down the frames is O(depth) and runs once, on
    /// the refusal that ends the run.
    fn at_step(&self, p: Prim, m: String) -> String {
        // The entry steps are in words too, but the compiler generates them in the `gen` of a
        // walk, not in a `reindex` or a `discard`, so where they ran is not said here.
        if !matches!(p, Prim::Path | Prim::PathKey | Prim::PathLen) {
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

    /// Begins a `fam` over `keys`: binds `var` to each and evaluates `body` (child 1 at `at`).
    fn begin_fam(
        &mut self,
        var: &'t str,
        body: &'t Term,
        at: At,
        env: Env<'t>,
        keys: Vec<Value>,
    ) -> R<Step<'t>> {
        self.begin_pure(false);
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
            parts: Vec::new(),
        }))
    }

    /// Begins a `reindex` (child 0 at `at`) of `leaves` by the key map `kf` and the value map
    /// `vf`.
    fn begin_reindex(
        &mut self,
        at: At,
        leaves: Vec<(Keypath, V<'t>)>,
        kf: V<'t>,
        vf: V<'t>,
        from: Option<usize>,
    ) -> R<Step<'t>> {
        let kf = (kf, Some(self.ev.child(at, 1)));
        let vf = (vf, Some(self.ev.child(at, 2)));
        self.begin_pure(false);
        self.reindex(Box::new(Reindex {
            leaves: leaves.into_iter(),
            kf,
            vf,
            from,
            path: Vec::new(),
            args: None,
            key: None,
            short: false,
            out: Vec::new(),
            parts: Vec::new(),
        }))
    }

    /// Begins a `discard` (child 0 at `at`) of the family whose top level is `level` by the
    /// test `sel`.
    fn begin_discard(
        &mut self,
        at: At,
        level: Level<'t>,
        sel: V<'t>,
        from: Option<usize>,
    ) -> R<Step<'t>> {
        let sel = (sel, Some(self.ev.child(at, 1)));
        self.begin_pure(false);
        self.discard(Box::new(Discard {
            levels: vec![level],
            prefix: Vec::new(),
            sel,
            from,
        }))
    }

    /// The family of the top-level `entries`, key then value, `None` for the next of `parts`:
    /// data when every entry is, and held ([`HeldFamily`]) when one is a function or holds
    /// one. A key given twice is a collision, as in a display.
    fn made_family(&self, entries: Vec<(Value, Option<Value>)>, parts: Vec<V<'t>>) -> R<V<'t>> {
        if parts.is_empty() {
            let leaves = entries.into_iter();
            let leaves = leaves.map(|(k, v)| (vec![k], v.expect("every entry is data")));
            let leaves: Vec<_> = leaves.collect();
            return Ok(V::Data(Value::Family(Family::from_leaves(leaves)?)));
        }
        let f = HeldFamily::new(entries)?.expect("an entry that is no data was made");
        Ok(V::Held(Rc::new(Held {
            shape: Shape::Family(f),
            parts,
            drops: self.drops.clone(),
        })))
    }

    /// The family of `leaves`, keypath then value, `None` for the next of `parts`, as a
    /// `reindex` gives it: data when every leaf is; otherwise each level with a part at or
    /// beneath one of its keys is a held family, a part of the level above it. Every error is
    /// the one [`Family::from_leaves`] gives for the same leaves with each part a leaf of its
    /// own.
    // Complexity tradeoff: the naive build nests the leaves level by level by hand, a second
    // copy of the key rules of `Family::from_leaves` (normalized keys, collisions and their
    // keypaths, a leaf above a level) that must agree with it leaf for leaf. Used: the leaves
    // are built once by `from_leaves` with each part written as a mark, the integer of its
    // number, and the keypaths of the parts once more into a family of marks, O(n log n) for
    // n leaves; then only the levels with a part beneath them are walked, each entry of such a
    // level once, and each made held by [`HeldFamily::new`], O(m log m) for its m entries, so
    // O(n log n) in all. The walk keeps its levels on a list, not the thread's stack, since a
    // keypath may be as long as a program makes it. Tradeoff: a level with one part among many
    // data entries is walked whole; the family of marks is a second map of the parts' keypaths.
    fn held_leaves_family(
        &self,
        leaves: Vec<(Keypath, Option<Value>)>,
        parts: Vec<V<'t>>,
    ) -> R<V<'t>> {
        if parts.is_empty() {
            let leaves = leaves.into_iter();
            let leaves = leaves.map(|(p, v)| (p, v.expect("every leaf is data")));
            return Ok(V::Data(Value::Family(Family::from_leaves(
                leaves.collect::<Vec<_>>(),
            )?)));
        }
        let mut marked = Vec::with_capacity(leaves.len());
        let mut marks = Vec::with_capacity(parts.len());
        for (path, v) in leaves {
            let v = v.unwrap_or_else(|| {
                let mark = Value::Int(marks.len() as i64);
                marks.push((path.clone(), mark.clone()));
                mark
            });
            marked.push((path, v));
        }
        let all = Family::from_leaves(marked)?;
        // The keypaths of the parts are keypaths of `all`, each ending at a leaf of its own,
        // so none is a prefix of another and none is given twice: this cannot fail.
        let marks = Family::from_leaves(marks)?;
        let mut parts: Vec<Option<V<'t>>> = parts.into_iter().map(Some).collect();
        // Each level being made: its entries left, its marks, the entries made so far, key
        // then value `None` for the next of its parts, and those parts.
        struct Making<'f, 't> {
            entries: crate::btree::Iter<'f, Value, Value>,
            marks: &'f Family,
            out: Vec<(Value, Option<Value>)>,
            parts: Vec<V<'t>>,
        }
        fn start<'f, 't>(f: &'f Family, marks: &'f Family) -> Making<'f, 't> {
            Making {
                entries: f.0.built_map().iter(),
                marks,
                out: Vec::new(),
                parts: Vec::new(),
            }
        }
        let mut levels = vec![start(&all, &marks)];
        let mut keys: Vec<Value> = Vec::new();
        loop {
            let top = levels.last_mut().expect("the top level is popped last");
            if let Some((k, v)) = top.entries.next() {
                match (top.marks.get(k), v) {
                    (None, v) => top.out.push((k.clone(), Some(v.clone()))),
                    (Some(Value::Int(i)), _) => {
                        top.out.push((k.clone(), None));
                        let part = parts[*i as usize].take().expect("each part once");
                        top.parts.push(part);
                    }
                    (Some(Value::Family(m)), Value::Family(sub)) => {
                        keys.push(k.clone());
                        levels.push(start(sub, m));
                    }
                    _ => unreachable!("a part's keypath ends at a leaf of `all`"),
                }
                continue;
            }
            let done = levels.pop().expect("the level just read");
            let f = HeldFamily::new(done.out)?.expect("a level with a part beneath it");
            let made = V::Held(Rc::new(Held {
                shape: Shape::Family(f),
                parts: done.parts,
                drops: self.drops.clone(),
            }));
            let Some(top) = levels.last_mut() else {
                return Ok(made);
            };
            top.out
                .push((keys.pop().expect("the key of the level"), None));
            top.parts.push(made);
        }
    }

    /// Evaluates the entry at the next key, or makes the family: data when every entry is,
    /// and held ([`HeldFamily`]) when one is a function or holds one.
    fn fam(&mut self, mut st: Box<Fam<'t>>) -> R<Step<'t>> {
        let Some(k) = st.keys.next() else {
            return Ok(Step::Give(self.made_family(st.out, st.parts)?));
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
            let (out, parts) = (std::mem::take(&mut st.out), std::mem::take(&mut st.parts));
            return Ok(Step::Give(self.held_leaves_family(out, parts)?));
        };
        self.ev.enter(&path);
        let p = Value::path(path.clone());
        self.ev.aim(st.kf.1, &[st.from; 2]);
        // A keypath above an empty level binds no leaf value and no key past its end: the key
        // map reads the kernel's own atom [`unbound`] there, not `#notFound`, which a key may
        // hold as data.
        st.short = matches!(&v, V::Data(Value::Family(f)) if f.is_empty());
        let leaf = match (st.short, &p) {
            (true, Value::Path(keys)) => {
                self.short_paths.push(keys.id());
                V::Data(unbound())
            }
            _ => v.clone(),
        };
        let step = self.apply(&st.kf.0, vec![V::Data(p.clone()), leaf]);
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
                let step = self.apply(&st.sel.0, vec![V::Data(path), v]);
                self.wait(Wait::Discard(st));
                return step;
            }
            let done = st.levels.pop().expect("a `discard` is inside a level");
            let done = self.made_family(done.out, done.parts)?;
            let Some(k) = st.prefix.pop() else {
                return Ok(Step::Give(done));
            };
            let top = st.levels.last_mut().expect("the level above");
            top.keep(k, done);
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
                V::Data(Value::Family(sub)) => {
                    st.levels.push(level(&sub));
                    return self.discard(st);
                }
                V::Held(h) if matches!(h.shape, Shape::Family(_)) => {
                    st.levels.push(held_level(&h));
                    return self.discard(st);
                }
                leaf => top.keep(k, leaf),
            },
            Value::Bool(false) => {}
            Value::Atom(a) if &*a.name == "boundary" && a.is_bare() => {
                top.keep(k.clone(), V::Data(k))
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
        let index = key_index(&domain);
        let settled = domain.iter().map(|_| Settled::Open).collect();
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
            index,
            settled: RefCell::new(settled),
            drops: self.drops.clone(),
        });
        let rng = match self.ev.schedule {
            Schedule::Rounds => None,
            Schedule::Chaotic(seed) => Some(SplitMix64::new(seed)),
            Schedule::Pull => return self.pull(Box::new(Pull { fix, next: 0 })),
        };
        // The first round tries every entry; the work list is the rounds' own, since later
        // rounds refill it.
        let ready = (0..fix.domain.len()).collect();
        let waiting = fix.domain.iter().map(|_| Vec::new()).collect();
        self.round(Box::new(Rounds {
            fix,
            rng,
            waiting,
            queue: Vec::new().into_iter(),
            ready,
            defined: Vec::new(),
            round: 1,
            sees: 0,
        }))
    }

    /// Begins an attempt at the entry at position `i` of the domain of the `fix` of `by`
    /// against the entries defined before `round`.
    fn attempt(&mut self, round: u64, i: usize, by: By<'t>) -> R<Step<'t>> {
        let fix = by.fix();
        let k = fix.domain[i].clone();
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
            .push(Frame::Entry(Box::new(Entry { i, mark, by })));
        Ok(Step::Eval(body, at, env))
    }

    /// An attempt ended: with the entry's value, with a read of an undefined entry of its
    /// `fix`, or with something that stops the run. An attempt that reads an undefined entry
    /// is not a fact: what it recorded is dropped, and the entry's fact is the attempt that
    /// defines it.
    fn entry_ended(&mut self, entry: Entry<'t>, out: R<V<'t>>) -> R<Step<'t>> {
        let Entry { i, mark, by } = entry;
        let id = by.fix().id;
        self.ev.leave(1);
        let attempt = match out {
            Ok(V::Data(v)) => Ok(Ok(v)),
            Ok(_) => type_err("a fix entry is a function"),
            Err(Stop::Undefined { fix, i: read }) if fix == id => {
                if let (Some(t), Some((facts, calls, keys))) = (&mut self.ev.trace, mark) {
                    t.facts.truncate(facts);
                    t.calls.truncate(calls);
                    t.keys.truncate(keys);
                }
                Ok(Err(read))
            }
            Err(e) => Err(e),
        };
        match by {
            By::Round(mut st) => {
                match attempt? {
                    Ok(v) => {
                        st.fix.settled.borrow_mut()[i] = Settled::Defined(v, st.round);
                        st.defined.push(i);
                    }
                    Err(read) => st.waiting[read].push(i),
                }
                self.next_entry(st)
            }
            By::Pull(st) => {
                let (settled, out) = match attempt {
                    Ok(Ok(v)) => (Settled::Defined(v, 0), Ok(())),
                    Ok(Err(_)) => (Settled::Stalled, Ok(())),
                    Err(e) => (Settled::Open, Err(e)),
                };
                st.fix.settled.borrow_mut()[i] = settled;
                out?;
                self.pull(st)
            }
            By::Demand(fix, saved) => {
                if let (Some(t), Some(s)) = (&mut self.ev.trace, saved) {
                    (t.calls, t.keys, t.reads, t.site, t.args) =
                        (s.calls, s.keys, s.reads, s.site, s.args);
                }
                let mut settled = fix.settled.borrow_mut();
                match attempt {
                    Ok(Ok(v)) => {
                        settled[i] = Settled::Defined(v.clone(), 0);
                        give(v)
                    }
                    Ok(Err(read)) => {
                        settled[i] = Settled::Stalled;
                        Err(Stop::Undefined {
                            fix: fix.id,
                            i: read,
                        })
                    }
                    Err(e) => {
                        settled[i] = Settled::Open;
                        Err(e)
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
    // shared list, by position in the domain, of the entries with the round that defined them
    // (`Settled`), and a wait list per undefined entry read, so a chain costs `D` attempts
    // under every schedule and each attempt only what it reads, O(D) for the chain, with a
    // hash lookup a read ([`Definedness::index`]). Tradeoffs: memory for the round
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
        if let Some(i) = st.queue.next() {
            let sees = st.sees;
            return self.attempt(sees, i, By::Round(st));
        }
        if st.defined.is_empty() {
            return rounds_end(&st.fix);
        }
        for i in std::mem::take(&mut st.defined) {
            let waited = std::mem::take(&mut st.waiting[i]);
            st.ready.extend(waited);
        }
        // The order of trying a round's entries is the key order, as when all are tried: the
        // domain is in key order.
        st.ready.sort_unstable();
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
    // evaluated once, and whether an entry is being demanded or has stalled is kept by its
    // position in the domain ([`Settled`]), so the cycle check is O(1) once the key is found
    // ([`Definedness::index`]) and a chain ending in a cycle stalls in O(D). Tradeoffs: the
    // demanded entries' frames are nested, held on the machine's heap stack, O(D) memory; an
    // entry on a cycle and every entry waiting on it stall rather than being retried.
    fn pull(&mut self, mut st: Box<Pull<'t>>) -> R<Step<'t>> {
        while st.next < st.fix.domain.len() {
            let i = st.next;
            st.next += 1;
            if !matches!(st.fix.settled.borrow()[i], Settled::Open) {
                continue;
            }
            self.ev.burn()?;
            st.fix.settled.borrow_mut()[i] = Settled::Busy;
            return self.attempt(u64::MAX, i, By::Pull(st));
        }
        let settled = st.fix.settled.borrow();
        let stalled = st.fix.domain.iter().zip(settled.iter());
        let stalled = stalled.filter(|(_, s)| matches!(s, Settled::Stalled));
        let stalled = stalled.map(|(k, _)| k.clone()).collect();
        drop(settled);
        finish_fix(&st.fix, stalled)
    }

    /// Evaluates the undefined entry at position `i` where an attempt reads it, with the call
    /// sites and keypath of the `fix` itself, so that its facts are those it would have had
    /// demanded from the top. A read it cannot demand stops it and the attempt reading it.
    fn demand(&mut self, fix: Rc<Definedness<'t>>, i: usize) -> R<Step<'t>> {
        self.ev.burn()?;
        let saved = self.ev.trace.as_mut().map(|t| Saved {
            calls: std::mem::replace(&mut t.calls, fix.calls.clone()),
            keys: std::mem::replace(&mut t.keys, fix.keys.clone()),
            reads: std::mem::take(&mut t.reads),
            site: t.site.take(),
            args: std::mem::take(&mut t.args),
        });
        fix.settled.borrow_mut()[i] = Settled::Busy;
        self.attempt(u64::MAX, i, By::Demand(fix, saved))
    }

    /// The step making generation `t` runs at coordinate `t`, reading the fact of the frame
    /// before.
    fn gen_step(&mut self, st: Box<Gen<'t>>) -> R<Step<'t>> {
        self.ev.burn()?;
        let last = st.frames.last().expect("generation 0 is present").clone();
        self.ev.enter(&[Value::Int(st.frames.len() as i64)]);
        self.ev.aim(st.step.1, &[st.from]);
        let step = self.apply(&st.step.0, vec![last]);
        self.wait(Wait::GenStep(st));
        step
    }

    /// Tests a `gen` guard on the last frame, at that frame's coordinate. A result that is
    /// not a bool ends the loop and is appended as the stream's last entry.
    fn gen_guard(&mut self, st: Box<Gen<'t>>) -> R<Step<'t>> {
        let last = st.frames.last().expect("generation 0 is present").clone();
        self.ev.enter(&[Value::Int(st.frames.len() as i64 - 1)]);
        self.ev.aim(st.guard.1, &[st.from]);
        let step = self.apply(&st.guard.0, vec![last]);
        self.wait(Wait::GenGuard(st));
        step
    }

    /// The family of a `gen`'s frames, keyed `0 ..< count`: data when every frame is, and
    /// held when one is a function or holds one ([`Self::made_family`]).
    fn gen_end(&self, st: Gen<'t>) -> R<Step<'t>> {
        let mut entries = Vec::with_capacity(st.frames.len());
        let mut parts = Vec::new();
        for (t, f) in st.frames.into_iter().enumerate() {
            let k = Value::Int(t as i64);
            match f {
                V::Data(v) => entries.push((k, Some(v))),
                f => {
                    entries.push((k, None));
                    parts.push(f);
                }
            }
        }
        Ok(Step::Give(self.made_family(entries, parts)?))
    }
}

/// The result of a level that needs no call of `op`: an empty level's, or, for the primitive
/// `+`, that of a level holding an atom, which is the merge of its atoms (DESIGN.md L3.10: `#a`
/// when `#a` is at two keys, `#errs({#a, #b})` when `#a` and `#b` are both present, by the
/// merge rule of sec:failure). Until row CHECK-fold-merge-errs this gave the level's first
/// atom, dropping the others. A level of floats goes round the canonical tree like any other:
/// sec:reduction item 1 fixes the tree, and item 2 says no float policy is the exact sum (that
/// is `rat`'s, written `xs.map(x -> rat(x)) >< (+)`). Costs one pass over the level and the
/// merge's O(m log m) for its `m` atoms.
fn reduced(values: &[Value], op: &V<'_>, identity: &Option<Value>) -> Option<Value> {
    if values.is_empty() {
        return Some(identity.clone().unwrap_or_else(|| Value::atom("empty")));
    }
    if matches!(op, V::Prim(Prim::Add)) && values.iter().any(|v| matches!(v, Value::Atom(_))) {
        let atoms = values.iter().filter(|v| matches!(v, Value::Atom(_)));
        return Some(Value::merge_failures(atoms.cloned()));
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

/// What [`Evaluator::run_in`] gives: data, or a value apart from the run.
enum Ran {
    Data(Value),
    Made(Made),
}

/// A step of [`Machine::made`]: a value to visit, or a closure or held value whose parts are
/// the last results.
enum Task<'t> {
    Visit(V<'t>),
    Fun(Rc<Closure<'t>>, Vec<Arc<str>>),
    Held(Rc<Held<'t>>),
}

// `made` reads the machine's values, so it is written here and not in eval/made.rs, which then
// imports nothing from this file (step S.1f: no import cycle; row S1F-kernel-eval-made-cycle).
impl<'t> Machine<'_, 't> {
    /// `v` apart from the run (see [`Made`]).
    // Complexity tradeoff: the naive way follows each path to a value, so a closure captured
    // by two closures, each captured by two more, is visited 2^d times for d levels. Used:
    // each closure and held value is visited once, by its address, and its parts once each,
    // on a list of tasks, not the thread's stack, since values nest as deep as a program makes
    // them: O(the values and captures reached), plus the names each distinct body reads,
    // found once per body. Tradeoff: one map entry per closure and held value.
    fn made(&mut self, v: V<'t>) -> R<Made> {
        let mut nodes = Vec::new();
        let mut done: HashMap<*const (), usize> = HashMap::new();
        let mut out: Vec<usize> = Vec::new();
        let mut tasks = vec![Task::Visit(v)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(v) => {
                    let node = match v {
                        V::Data(d) => MadeNode::Data(d),
                        V::Prim(p) => MadeNode::Prim(p),
                        V::Source(p) => MadeNode::Source(p),
                        V::Partial(_) => {
                            return type_err(
                                "a function that reads a family still being defined left it",
                            );
                        }
                        V::Held(h) => {
                            if let Some(&i) = done.get(&(Rc::as_ptr(&h) as *const ())) {
                                out.push(i);
                                continue;
                            }
                            let parts: Vec<V<'t>> = h.parts.clone();
                            tasks.push(Task::Held(h));
                            tasks.extend(parts.into_iter().rev().map(Task::Visit));
                            continue;
                        }
                        V::Closure(c) => {
                            if let Some(&i) = done.get(&(Rc::as_ptr(&c) as *const ())) {
                                out.push(i);
                                continue;
                            }
                            let names = made::reads(c.body);
                            let mut caps = Vec::new();
                            let mut vals = Vec::new();
                            for x in names.iter() {
                                if c.params.contains(x) {
                                    continue;
                                }
                                let v = match lookup(&c.env, x) {
                                    None => continue,
                                    Some(Slot::Is(v)) => v,
                                    // `run_made` runs under no globals, so no environment
                                    // binds one.
                                    Some(Slot::Global(_)) => {
                                        unreachable!("a run made apart is under no globals")
                                    }
                                };
                                caps.push(x.clone());
                                vals.push(v);
                            }
                            // A placed closure's `fill` is one more capture, last, which no
                            // body reads; the back end gives it back to `place`.
                            if let Some(fill) = c.placed.as_ref().and_then(|p| p.fill.clone()) {
                                caps.push(FILL_NAME.into());
                                vals.push(fill);
                            }
                            tasks.push(Task::Fun(c, caps));
                            tasks.extend(vals.into_iter().rev().map(Task::Visit));
                            continue;
                        }
                    };
                    nodes.push(node);
                    out.push(nodes.len() - 1);
                }
                Task::Fun(c, names) => {
                    let parts = out.split_off(out.len() - names.len());
                    nodes.push(MadeNode::Fun(MadeFun {
                        params: c.params.to_vec(),
                        body: c.body.clone(),
                        caps: names.into_iter().zip(parts).collect(),
                        placed: c.placed.as_ref().map(|p| p.table.clone()),
                    }));
                    done.insert(Rc::as_ptr(&c) as *const (), nodes.len() - 1);
                    out.push(nodes.len() - 1);
                }
                Task::Held(h) => {
                    let parts = out.split_off(out.len() - h.parts.len());
                    let shape = match &h.shape {
                        Shape::Tuple => MadeShape::Tuple,
                        Shape::Atom(n, f) => MadeShape::Atom(n.clone(), f.clone()),
                        Shape::Family(f) => MadeShape::Family(f.clone()),
                    };
                    nodes.push(MadeNode::Held(shape, parts));
                    done.insert(Rc::as_ptr(&h) as *const (), nodes.len() - 1);
                    out.push(nodes.len() - 1);
                }
            }
        }
        Ok(Made { nodes })
    }
}

/// The level of `family`'s top-level entries, before any is tested.
fn level<'t>(family: &Family) -> Level<'t> {
    let entries = family.iter().map(|(k, v)| (k.clone(), V::Data(v.clone())));
    Level {
        out: Vec::new(),
        parts: Vec::new(),
        entries: entries.collect::<Vec<_>>().into_iter(),
        entry: None,
    }
}

/// The level of the top-level entries of `h`, a held family, before any is tested: each data
/// entry as it is, and each part.
fn held_level<'t>(h: &Held<'t>) -> Level<'t> {
    let Shape::Family(f) = &h.shape else {
        unreachable!("a level of a held family")
    };
    let entries = f.iter().map(|(k, e)| match e {
        HeldEntry::Data(v) => (k.clone(), V::Data(v.clone())),
        HeldEntry::Part(i) => (k.clone(), h.parts[i].clone()),
    });
    Level {
        out: Vec::new(),
        parts: Vec::new(),
        entries: entries.collect::<Vec<_>>().into_iter(),
        entry: None,
    }
}

impl<'t> Level<'t> {
    /// Keeps the entry `v` at key `k`.
    fn keep(&mut self, k: Value, v: V<'t>) {
        match v {
            V::Data(v) => self.out.push((k, Some(v))),
            v => {
                self.parts.push(v);
                self.out.push((k, None));
            }
        }
    }
}

/// The leaves of `h`, a held family, with their keypaths, in keypath order, as
/// [`Family::leaves`] gives those of a data family: a part that is a held family is a level,
/// and any other part a leaf.
// Complexity tradeoff: the naive way turns the family to data first, which a function cannot
// be. Used: the levels are walked in key order on a list of their own, each entry once, so
// O(n) for n entries and leaves beside the keypaths copied, as `Family::leaves` costs; a data
// level beneath a key is read by `Family::leaves` itself.
fn held_leaves<'t>(h: &Held<'t>) -> Vec<(Keypath, V<'t>)> {
    let mut out = Vec::new();
    // Each level entered: its entries left, as from `held_level`, and the keypath above it.
    let mut levels = vec![(held_level(h).entries, Vec::new())];
    while let Some((entries, prefix)) = levels.last_mut() {
        let Some((k, v)) = entries.next() else {
            levels.pop();
            continue;
        };
        let mut path = prefix.clone();
        path.push(k);
        match v {
            V::Data(Value::Family(f)) if !f.is_empty() => {
                for (mut sub, leaf) in f.leaves() {
                    let mut whole = path.clone();
                    whole.append(&mut sub);
                    out.push((whole, V::Data(leaf)));
                }
            }
            V::Held(h) if matches!(h.shape, Shape::Family(_)) => {
                levels.push((held_level(&h).entries, path));
            }
            leaf => out.push((path, leaf)),
        }
    }
    out
}

/// The keys `fix`'s rounds left undefined, or its family.
fn rounds_end<'t>(fix: &Definedness<'t>) -> R<Step<'t>> {
    let left: Vec<Value> = {
        let settled = fix.settled.borrow();
        let left = fix.domain.iter().zip(settled.iter());
        let left = left.filter(|(_, s)| !matches!(s, Settled::Defined(..)));
        left.map(|(k, _)| k.clone()).collect()
    };
    finish_fix(fix, left)
}

/// The keys that stalled, or, when none did and so every entry is defined, the family.
// Complexity tradeoff (KERNEL-near-limit-benches): the family was built by
// `Family::from_leaves` from one-key keypaths, an ordered-map insertion per entry, O(D log D)
// comparisons of keys. Used: the domain is in key order and its keys are distinct, so the
// entries are already the family's, in order, and are laid out at once, O(D). The result is the
// one `from_leaves` gives: a one-key keypath never collides here and adds no level beneath
// (`Levels::place` and `Levels::insert` write each at level 0, whose slot for a key not seen
// is `Vacant`, as a `Slot::Leaf` of the value, a family or not).
// Every entry is defined when `stalled` is empty, from each caller:
// - `rounds_end` passes the keys not `Defined`.
// - `pull` passes the keys `Stalled` once its loop has passed every position. No entry is
//   `Open` then: the loop attempts each entry it finds `Open`, and an attempt ends `Defined`
//   or `Stalled`, or `Open` with a stop that ends the fix (`out?` in `entry_ended`; an
//   `Entry` frame is the only frame that turns a stop into a value, and only its own fix's
//   undefined read). A `Defined` or `Stalled` entry is not attempted again: `pull` and a read
//   (`Step::Demand`) attempt only `Open` ones. No entry is `Busy` then: `Busy` is set just
//   before an attempt, whose end rewrites it, and the demands an attempt makes run nested
//   inside its frames, so all have ended when `pull` runs again.
// Tests: `a_circular_reference_stalls_and_names_its_cells` (m0_09_kernel_evaluator),
// `a_cycle_through_a_nested_fix_stalls_the_outer_entries_only` and
// `every_schedule_agrees_on_random_graphs_with_dependencies_out_of_key_order`
// (m0_10_finite_model_harness recursion.rs); the `unreachable!` below checks it in release.
fn finish_fix<'t>(fix: &Definedness<'t>, stalled: Vec<Value>) -> R<Step<'t>> {
    if !stalled.is_empty() {
        return Err(KernelError::Stalled { keys: stalled }.into());
    }
    let settled = fix.settled.take();
    let entries = fix.domain.iter().zip(settled).map(|(k, s)| match s {
        Settled::Defined(v, _) => (k.clone(), v),
        _ => unreachable!("an entry neither defined nor stalled when the fix ends"),
    });
    give(Value::Family(Family::from_map(entries.collect())))
}

/// One definedness `fix` being evaluated: its family's name, domain, and entry body, the
/// call sites and keypath it runs inside, and where each of its entries stands.
struct Definedness<'t> {
    id: u64,
    /// The keys of the initial family, distinct and in order: entries are named by their
    /// positions here, and a pull walks them in order.
    domain: Box<[Value]>,
    /// The position of each key of `domain`.
    // Complexity tradeoff (KERNEL-near-limit-benches): a read found its key by binary search
    // of `domain`, then in ordered maps of the defined entries and ordered sets of those being
    // demanded and those stalled, about 4·log D comparisons of keys a read, each a walk of a
    // key that may be a tuple: a definedness fix over `D` tuple keys grew faster than
    // `D log D` would suggest, 10.2 times its work at 8 times `D`. Used: one hash lookup
    // finds the key's position, and where the entry stands is read there ([`Settled`]), so a
    // read costs the key's digest and one comparison. Tradeoffs: the map, O(D) memory, and a
    // digest of every key when the fix begins, O(total key size).
    index: HashMap<Value, usize>,
    /// By position in `domain`: where each entry stands.
    settled: RefCell<Vec<Settled>>,
    body: &'t Term,
    /// The body's position.
    at: At,
    this: &'t str,
    key: &'t str,
    env: Env<'t>,
    calls: Vector<Position>,
    keys: Vector<Value>,
    drops: Rc<Drops<'t>>,
}

impl Drop for Definedness<'_> {
    fn drop(&mut self) {
        self.drops.free(Freed::Env(self.env.take()));
    }
}

/// Whether `v` is an atom that holds a function.
fn held_atom(v: &V<'_>) -> bool {
    matches!(v, V::Held(h) if h.atom().is_some())
}

/// The operand of primitive `p` that is a family it reads, which [`Machine::held_family`]
/// reads when it is held; `None` for a primitive that reads none.
fn family_operand(p: Prim) -> Option<usize> {
    match p {
        Prim::Get
        | Prim::TupleGet
        | Prim::At
        | Prim::GetAtomKey
        | Prim::Count
        | Prim::FirstEntry
        | Prim::LastEntry
        | Prim::EntryAfter
        | Prim::EntryBefore
        | Prim::First
        | Prim::Last => Some(0),
        Prim::Has => Some(1),
        _ => None,
    }
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
            (Pattern::AnyAtom, V::Held(h)) => h.atom().is_some(),
            (Pattern::Atom(name, ps), V::Held(h)) => {
                // A held atom has a payload, with a function in it, so it is never bare.
                // Proof: the one maker of `Shape::Atom` is `Machine::held`'s `Prim::Atom` arm,
                // reached only when some argument is no data (`prim`), and that arm refuses a
                // name or field list that is no data, so some payload part is no data and
                // `h.parts` is not empty. Then the test below is the `Some(xs)` case of
                // [`matches()`]'s `Atom` arm, with `h.parts` for `xs`.
                let hit = matches!(h.atom(), Some((n, f)) if n == name && f.is_empty())
                    && !ps.is_empty()
                    && ps.len() == h.parts.len();
                if hit {
                    left.extend(ps.iter().zip(&h.parts).rev());
                }
                hit
            }
            (Pattern::Fields(name, fs), V::Held(h)) => match h.atom() {
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
                let hit = h.is_tuple() && ps.len() == h.parts.len();
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

/// The position of each key of `domain`, a fix's domain: keys, distinct and in order.
fn key_index(domain: &[Value]) -> HashMap<Value, usize> {
    let index = domain.iter().cloned().enumerate().map(|(i, k)| (k, i));
    index.collect()
}

/// The position in a fix's domain of the entry a read of key `k` names, found in the domain's
/// `index`: the position `Family::get` and a binary search of the domain find (tests
/// TEST-kernel-hash-keys, in `eval/tests.rs`).
fn position(index: &HashMap<Value, usize>, k: &Value) -> Option<usize> {
    index.get(&*as_key(k)).copied()
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
    // A Zed program reaches `mod` only with `m` in `int[1..]`, which the checker proves
    // (DESIGN.md sec:domains and sec:kernel (b); QUESTIONS A174, row MOD-positive-modulus).
    // The kernel keeps `mod` total on the ints as before, `#divByZero` at 0 and the Euclidean
    // remainder by `|m|` below it, because the preimage, Presburger and lattice layers model
    // that operation on the kernel terms they are tested with, and a checked program never
    // observes the difference.
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

/// An atom's name or field name as one shared block ([`crate::text::Text::try_shared`]): a
/// join is written out once the system gives the memory, else [`KernelError::Type`].
///
/// Why no program reaches the error (plan row MSG-kinds-e2e-tests, which removed the kind
/// `AtomNameTooLarge` this used to give). Proof: every atom primitive of a compiled program is
/// built by the elaborator (`zedc_elab`, `Frame::AtomArgs`) or by `held_term`
/// (`zedc_zir::zir::memory`), and both pass the name and each field name as
/// `Term::Lit(Value::str(s))`, `s` an identifier of the source. `Value::str` makes
/// `Text::from(Arc<str>)`, which is one block for a non-empty string, and an identifier is never
/// empty (sec:grammar). `try_shared` of a block returns the block and asks for no memory, so it
/// cannot fail. Only a term built by hand, as the kernel's own tests build one, gives a joined
/// name; a refusal there is a fault of the caller, which `Type` names.
///
/// No test checks the claim (PROOF-kernel-proofdoc3a-gaps (l)): a joined name fails only when
/// the system refuses the memory, which no test run limits, so even
/// `l01_26_type_resolution::random::accepted_random_programs_raise_no_type_error`, which counts
/// the kernel's type errors, would pass with one. That only these two builders make an atom
/// primitive is read from the source, not checked; a test that elaborates programs with atoms
/// and asserts that each name of a `Prim::Atom` is a literal of one block would check both.
fn atom_name(name: &crate::text::Text) -> Result<Arc<str>, KernelError> {
    name.try_shared().map_err(|_| {
        KernelError::Type(format!(
            "an atom's name or field name is a joined string of {} bytes, and the memory to \
             write it in one piece was refused",
            name.len()
        ))
    })
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
    // These two keep the values they are given: copying a tuple that holds a list would make
    // building the list quadratic in its length.
    match p {
        Prim::Tuple => Ok(Value::tuple(vals)),
        Prim::Path => Ok(Value::path(vals)),
        Prim::Entries => entries(vals),
        _ => prim_on(p, &vals),
    }
}

/// The refusal of a display given `n` arguments, `n` odd, so that its last key has no value.
/// Elaboration builds a display from pairs, key then value, so no program gives one; a kernel
/// or ZIR term made elsewhere may, and is refused rather than read with its last key dropped.
fn odd_display(n: usize) -> String {
    format!(
        "{} takes its arguments in pairs, a key then a value, given {n}",
        Prim::Entries.named(None)
    )
}

/// The family of a display's entries, given in pairs, key then value (step L3.2): each key
/// written as a key (`-0.0` as `0.0`), a value that is a family a level beneath its key, and
/// two entries at one key a collision, as [`Family::from_leaves`] makes them.
// Complexity tradeoff: the naive version is a union of one-entry families, one per entry, which
// copies the map built so far on each union, O(n^2) for n entries. Used: the n leaves given to
// `from_leaves` at once, which inserts each into one map, O(n log n), the values moved in.
// Tradeoff: none beyond the pairing.
fn entries(vals: Vec<Value>) -> Result<Value, KernelError> {
    if !vals.len().is_multiple_of(2) {
        return Err(KernelError::Type(odd_display(vals.len())));
    }
    let mut it = vals.into_iter();
    let mut leaves = Vec::with_capacity(it.len() / 2);
    while let (Some(k), Some(v)) = (it.next(), it.next()) {
        leaves.push((vec![k.key()], v));
    }
    Ok(Value::Family(Family::from_leaves(leaves)?))
}

/// `range(a, b)`, the set of the integers from `a` up to `b - 1`, each key mapping to itself,
/// and empty when `b <= a` (DESIGN.md sec:grammar, rule Range).
// Complexity tradeoff: the naive version is a union of one-entry sets, one per integer, which
// copies the set built so far on each union, O(n^2) for n keys, or a display `{a, …, b - 1}`
// put through `from_leaves`, O(n log n), or the keys made in ascending order and collected into
// the ordered map at once, O(n) time and memory (the method until plan row RANGE-lazy). Used:
// when `a` and `b - 1` are both 64-bit, the two ends kept as they are (`Family::range`), O(1);
// a read, `in`, `.count` and the first and last entry cost O(1) and the entry beside a key
// O(log n), and the first walk over the entries builds the map, O(n), as before. When an end is
// past `i64` (plan row RANGE-lazy-wide), the naive version, the method until then, built each
// key `a + i` with `+` and collected them, O(n) big-integer additions and O(n) memory for any
// read, and never ended for a count past memory. Used: the ends built once and kept
// (`Family::range_wide`), O(digits); a read, `in`, `.count` and the first and last entry cost
// O(digits), the entry beside a key O(digits) from the key's value, and the first walk builds
// the map, O(n) additions, as before. Tradeoff: an end that is a kept power (`2^K`, `K` large)
// is built here, as `b - 1` and the old count `b - a` built it; the system may refuse the
// memory, which is the error [`KernelError::NumberTooLarge`] the old build gave too.
fn range(a: &Value, b: &Value) -> Result<Value, KernelError> {
    // `b - 1`, which is 64-bit for every 64-bit `b` above `i64::MIN` and for `b = 2^63`, the end
    // `..= i64::MAX` gives.
    let last = int_binary(Prim::Sub, b, &Value::Int(1))?.expect("an integer difference");
    if let (Value::Int(lo), Value::Int(last)) = (a, &last) {
        return Ok(Value::Family(Family::range(*lo, *last)));
    }
    // An end past `i64`, `b = i64::MIN` (its `b - 1` past `i64`, no integer below it) among
    // them: `range_wide` gives the empty family when `b - 1 < a`.
    let built = |v: &Value| {
        let n = v.as_integer().expect("an integer");
        n.to_integer().map_err(|e| too_large(Prim::Range, e))
    };
    Ok(Value::Family(Family::range_wide(built(a)?, built(&last)?)))
}

/// An entry of a family as the tuple `(k, v)`, or the empty tuple `()` for none: the answer of
/// the entry steps `firstEntry`, `lastEntry`, `entryAfter` and `entryBefore`.
fn entry_tuple(e: Option<(Value, Value)>) -> Value {
    match e {
        Some((k, v)) => Value::tuple(vec![k, v]),
        None => Value::tuple(Vec::new()),
    }
}

/// `f.first`, or with `last` `f.last`: the leaf at the least (greatest) keypath of `f`, each
/// level read in key order, descending while the entry is a family; `#none` when a level on the
/// way is empty, as in `[[]]` (DESIGN.md sec:corner_cases, "`first`/`last` are lexicographic").
// Complexity tradeoff: the naive version lists the leaves (`Family::leaves`) and takes the
// least keypath, O(n log n) for n leaves. Used: the least (greatest) entry of each level the
// descent passes, O(log n) per level, O(d log n) for d levels. Tradeoff: none.
pub fn leaf_at_end(f: &Family, last: bool) -> Value {
    // Each level's end entry is copied, O(1) whether a map or a range (a family's copy shares
    // its map), so a range is read from its ends.
    let mut level = f.clone();
    loop {
        match level.end_entry(last) {
            None => return Value::atom("none"),
            Some((_, Value::Family(inner))) => level = inner,
            Some((_, v)) => return v,
        }
    }
}

/// What a primitive that reads a held family gives ([`held_family_got`]): data, a part of the
/// family or of a family beneath it, or the entry tuple of a key and a part.
pub enum FamilyGot<P> {
    /// Data: an entry, an answer such as `#notFound`, a count, or an entry tuple of data.
    Data(Value),
    /// A part, as the machine names it.
    Part(P),
    /// The entry tuple `(k, v)` of key `k` and a part `v`, made by the machine.
    Pair(Value, P),
}

/// A held family as one machine stores it: the kernel (`Rc<Held>` here), the memory machine
/// (zedc-zir `memory.rs`) and native code (zed-native `hooks.rs`) each keep its parts in their
/// own storage, and [`held_family_got`] reads all three through this.
pub trait HeldFamilyAt: Sized {
    /// A part as the machine names it.
    type Part;
    /// The error of reading the machine's storage.
    type Error;
    /// The family's keys and entries.
    fn family(&self) -> &HeldFamily;
    /// Part `i` of the family ([`HeldEntry::Part`]).
    fn part(&self, i: usize) -> Self::Part;
    /// Part `i` when it is itself a held family, a level beneath its key; none otherwise.
    fn sub_family(&self, i: usize) -> Result<Option<Self>, Self::Error>;
}

/// What primitive `p` gives on the held family `at`, as `prim_on` reads a data family: for
/// `Get`, `TupleGet`, `At` and `Has` at `key` (data, not an atom: an atom key passes through,
/// which each machine does before this; for `GetAtomKey` an atom too), the entry, `#notFound`
/// (`#outOfBounds` for `At`) or whether it is there; for `Count` the number of entries; for an
/// entry step the entry tuple `(k, v)` (`()` past the end), from `key`, the key of the entry
/// tuple given, for
/// `EntryAfter` and `EntryBefore`; and for `First` and `Last` the leaf at the least (greatest)
/// keypath, descending into each part that is a held family and each data family
/// ([`leaf_at_end`]), `#none` at an empty level. Shared by the kernel's `Machine::held_family`,
/// the memory machine's `family_read` (zedc-zir) and native code's `family_read` (zed-native),
/// which held three copies of these rules before DRY-misc-A5 (REPORT-dryA5 row 9); each
/// machine keeps the reading of its operands and the making of what this gives. Panics on a
/// primitive other than these, or on a missing `key`: the callers ask only for these, each
/// through its own `family_at` or `family_operand`.
// Complexity tradeoff: each read is one lookup in the family's keys, O(log n) ([`HeldFamily`]);
// `first` and `last` descend one level per step, O(depth · log n). The naive read hands the
// family to the kernel as data, O(n) per read. Tradeoff: none; the trait's calls are resolved
// when each machine's copy is compiled.
pub fn held_family_got<N: HeldFamilyAt>(
    p: Prim,
    at: N,
    key: Option<&Value>,
) -> Result<FamilyGot<N::Part>, N::Error> {
    let f = at.family();
    let entry = |e: HeldEntry<'_>| match e {
        HeldEntry::Data(v) => FamilyGot::Data(v.clone()),
        HeldEntry::Part(i) => FamilyGot::Part(at.part(i)),
    };
    let pair = |k: &Value, e: HeldEntry<'_>| match e {
        HeldEntry::Data(v) => FamilyGot::Data(Value::tuple(vec![k.clone(), v.clone()])),
        HeldEntry::Part(i) => FamilyGot::Pair(k.clone(), at.part(i)),
    };
    let none = || FamilyGot::Data(Value::tuple(Vec::new()));
    Ok(match p {
        Prim::Get | Prim::TupleGet | Prim::At | Prim::Has | Prim::GetAtomKey => {
            match (p, f.get(key.expect("a key"))) {
                (Prim::Has, e) => FamilyGot::Data(Value::Bool(e.is_some())),
                (_, Some(e)) => entry(e),
                (Prim::At, None) => FamilyGot::Data(Value::atom("outOfBounds")),
                (_, None) => FamilyGot::Data(Value::atom("notFound")),
            }
        }
        Prim::Count => FamilyGot::Data(Value::Int(f.len() as i64)),
        Prim::FirstEntry | Prim::LastEntry => match f.end(p == Prim::LastEntry) {
            Some((k, e)) => pair(k, e),
            None => none(),
        },
        Prim::EntryAfter | Prim::EntryBefore => {
            match f.beside(key.expect("a key"), p == Prim::EntryAfter) {
                Some((k, e)) => pair(k, e),
                None => none(),
            }
        }
        Prim::First | Prim::Last => {
            // A part that is a held family is a level beneath its key: descend into it.
            let last = p == Prim::Last;
            let mut cur = at;
            loop {
                let next = match cur.family().end(last) {
                    None => break FamilyGot::Data(Value::atom("none")),
                    Some((_, HeldEntry::Data(Value::Family(inner)))) => {
                        break FamilyGot::Data(leaf_at_end(inner, last));
                    }
                    Some((_, HeldEntry::Data(v))) => break FamilyGot::Data(v.clone()),
                    Some((_, HeldEntry::Part(i))) => match cur.sub_family(i)? {
                        Some(n) => n,
                        None => break FamilyGot::Part(cur.part(i)),
                    },
                };
                cur = next;
            }
        }
        _ => unreachable!("a primitive that reads no held family"),
    })
}

/// The integer `n`, the exponent of a float to an `int` power, as the `f64` the power takes:
/// `n` itself within ±2^53, where every integer is an `f64`, and past it ±2^53 or ±(2^53 - 1),
/// whichever has the parity of `n`, so that a negative base keeps the sign of the exact power.
/// O(1) within ±2^53, else O(size of `n`) for its sign and parity.
fn float_exponent(n: &Value) -> f64 {
    match n {
        Value::Int(n) if n.unsigned_abs() <= 1 << 53 => *n as f64,
        _ => {
            let n = n.as_integer().expect("an integer");
            let m = if n.is_even() {
                2f64.powi(53)
            } else {
                2f64.powi(53) - 1.0
            };
            if n.is_negative() { -m } else { m }
        }
    }
}

/// [`prim_data`] for a primitive other than `Tuple` and `Path`, which keeps none of `vals`.
fn prim_on(p: Prim, vals: &[Value]) -> Result<Value, KernelError> {
    use Value::{Bool, Float, Float32, Int, Str};
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
    let out = match (p, vals) {
        (Prim::Add | Prim::Sub | Prim::Mul | Prim::IntDiv | Prim::Mod | Prim::Pow, [a, b])
            if a.number_kind() == Some(0) && b.number_kind() == Some(0) =>
        {
            match int_binary(p, a, b)? {
                Some(v) => v,
                None => return ty(vals),
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
        // format: Rust's `sqrt` and `mul_add` are both correctly rounded (std docs, "Precision",
        // read in rustc 1.102 library/std/src/num/f64.rs: "guaranteed to be the rounded
        // infinite-precision result ... and guaranteed not to change"), `sqrt(-0.0)` is
        // `-0.0`, and a negative or NaN operand of `sqrt`, a NaN operand of `fma`, or
        // `fma(inf, 0, c)` gives NaN (DESIGN.md sec:linalg, machine operations). Method: IEEE
        // Std 754-2019, "IEEE Standard for Floating-Point Arithmetic", IEEE, 2019,
        // doi:10.1109/IEEESTD.2019.8766229 (Crossref). Read 2026-11-20 in a copy of the IEEE
        // Xplore PDF of the standard, 84 pages, found by a grounded web search (agy, 18:16-18:21
        // UTC) after the free services had failed (verification only; the copy and the
        // records of every service tried, 16:41-18:21 UTC, are outside the repository, in
        // wt/cd-xr/DOC-cite/cite2 and cite3). Section 5.1, "Overview", p. 29: "each of the
        // computational operations specified by this standard that returns a numeric result
        // shall be performed as if it first produced an intermediate result correct to
        // infinite precision and with unbounded range, and then rounded that intermediate
        // result, if necessary, to fit in the destination's format". Section 5.4.1,
        // "Arithmetic operations", p. 33: "The operation squareRoot(x) computes √ x. It has a
        // positive sign for all operands ≥ 0, except that squareRoot(−0) shall be −0", and
        // "The operation fusedMultiplyAdd(x, y, z) computes (x × y) + z as if with unbounded
        // range and precision, rounding only once to the destination format". Section 7.2,
        // "Invalid operation", p. 52: the default result of an invalid operation "shall be a
        // quiet NaN", and the invalid operations include "squareRoot if the operand is less
        // than zero" and "fusedMultiplyAdd(0, ∞, c) or fusedMultiplyAdd(∞, 0, c) unless c is a
        // quiet NaN; if c is a quiet NaN then it is implementation defined whether the invalid
        // operation exception is signaled". With a quiet NaN `c` the result is still a NaN, by
        // section 6.2, "Operations with NaNs", p. 48: "For an operation with quiet NaN inputs,
        // except as stated otherwise, if a floating-point result is to be delivered the result
        // shall be a canonical quiet NaN". Zed has no signaling NaN and no exception flags, so
        // only these results are used. Departure: none in the results; every NaN is then
        // stored as the canonical one (`value.rs`, at the canonical NaN's bits; test
        // `a_nan_from_sqrt_is_the_canonical_nan`). The 2008 edition
        // (doi:10.1109/IEEESTD.2008.4610935), read 2026-11-20 in study STUDY-ieee754-2019:
        // 5.4.1, p. 21, has the same squareRoot and fusedMultiplyAdd words, and 7.2 the same
        // invalid operations; its 6.2 asks only that the NaN "should be one of the input NaNs",
        // so the canonical NaN rule is the 2019 edition's (6.2). Cost:
        // O(1), one hardware instruction each (or the C library's `fma` on a host without
        // FMA). Measured at commit 59a32b29b: n = 2048 and 8n calls of each word,
        // 14225721 and 113703294 instructions, 8.0 times the work. The bench is now
        // `l01_18_scalar_interpreter::bench::sqrt_fma::n_calls_cost_linear_time`, at n = 2^18.
        (Prim::Sqrt, [Float(a)]) => Value::float(a.get().sqrt()),
        (Prim::Sqrt, [Float32(a)]) => Value::float32(a.get().sqrt()),
        (Prim::Fma, [Float(a), Float(b), Float(c)]) => {
            Value::float(a.get().mul_add(b.get(), c.get()))
        }
        (Prim::Fma, [Float32(a), Float32(b), Float32(c)]) => {
            Value::float32(a.get().mul_add(b.get(), c.get()))
        }
        // `floatMod` (DESIGN.md sec:domains; QUESTIONS A174): the definition, its proof and its
        // citations are at `num::float_mod::float_mod`. A modulus not finite and greater than
        // 0, which a checked program never passes, gives NaN.
        (Prim::FloatMod, [Float(x), Float(m)]) => Value::float(
            crate::num::float_mod::float_mod_total(x.get(), m.get(), f64::NAN),
        ),
        (Prim::FloatMod, [Float32(x), Float32(m)]) => Value::float32(
            crate::num::float_mod::float_mod_total(x.get(), m.get(), f32::NAN),
        ),
        (Prim::CastIntBase, [Str(s), Int(b)]) => crate::words::int_base(s, *b)?,
        // A base too wide for an `i64` is outside `2..=36`.
        (Prim::CastIntBase, [Str(_), Value::Big(_)]) => Value::atom("invalid"),
        (Prim::Concat, [Str(a), Str(b)]) => Str(crate::text::Text::join(a, b)?),
        // NaN in, NaN out, as for every float operation (DESIGN.md sec:domains, NaN rule 5):
        // IEEE 754 `pow` gives `pow(NaN, 0) = 1` and `pow(1, NaN) = 1`, so a NaN operand is
        // tested first. Source: IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229 (full
        // citation at the `sqrt` and `fma` rule above), section 9.2, "Additional mathematical
        // operations", which recommends `pow` and lists its special values: `pow(x, ±0)` is 1
        // for every `x`, a quiet NaN included, and `pow(+1, y)` is 1 for every `y`, a quiet NaN
        // included. Read 2026-11-20 in the 2019 text (the copy named at the `sqrt` rule),
        // 9.2.1, "Special values", p. 63: "pow (x, ±0) is 1 if x is not a signaling NaN" and
        // "pow (+1, y) is 1 for any y (even a quiet NaN)". The 2008 edition, 9.2.1, p. 44 (read
        // 2026-11-20 in study STUDY-ieee754-2019), words the first "pow (x, ±0) is 1 for any
        // x (even a zero, quiet NaN, or infinity)"; Zed
        // has no signaling NaN, so the two agree here. Rust's `powf` gives both. C99 Annex
        // F.9.4.4, "The pow functions", states them too; read 2026-11-20 in the WG14
        // committee draft N1256 (ISO/IEC 9899:TC3, September 7, 2007,
        // open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf, p. 461): "pow(+1, y)
        // returns 1 for any y, even a NaN" and "pow(x, ±0) returns 1 for any x, even a NaN".
        // Departure: Zed gives NaN for both,
        // on purpose. Tests: `l01_36_cranelift::pow_nan` and `l01_39_reduced_product::pow_nan`,
        // which check that both cases give NaN here; a wrong memory of the standard would not
        // change what they check.
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
        // A float to an `int` power, `(F, int) -> F` (DESIGN.md L1.18 for `f32`; plan row
        // POW-domains for `f64`): the power is taken in `f64`, and at `f32` rounded once to
        // `f32`. An exponent beyond ±2^53 is read as the nearest `f64` of its parity, which
        // keeps the sign of a negative base; every base but ±1 then overflows or underflows in
        // `f64` as it would at the exact exponent. Within ±2^53 the exponent is exactly an
        // `f64`, so `x ^ n` at `f64` is `x ^ f64(n)`, Rust's `powf` as in the arm above, and
        // `0.0 ^ -1` is the infinity, `-0.0 ^ -1` the negative one (tests
        // `l01_18_scalar_interpreter::f32::an_f64_to_an_int_power_is_an_f64` and
        // `zed_kernel` `eval::arrow_tests::float_to_an_int_power`).
        (Prim::Pow, [Float(a), b]) if b.number_kind() == Some(0) => {
            let a = a.get();
            Value::float(if a.is_nan() {
                f64::NAN
            } else {
                a.powf(float_exponent(b))
            })
        }
        (Prim::Pow, [Float32(a), b]) if b.number_kind() == Some(0) => {
            let a = a.get();
            Value::float32(if a.is_nan() {
                f32::NAN
            } else {
                f64::from(a).powf(float_exponent(b)) as f32
            })
        }
        (Prim::Eq, [a, b]) => Bool(a.surface_eq(b)),
        (Prim::Ne, [a, b]) => Bool(!a.surface_eq(b)),
        // Two floats compare as IEEE 754 does, so every comparison with a NaN is false (IEEE
        // Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 5.11; the full comment is at
        // `value.rs`, `Value::surface_cmp`).
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
                None => return ty(vals),
            }
        }
        (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Min | Prim::Max, [a, b]) => {
            if !a.same_kind(b) {
                return ty(vals);
            }
            // Two tuples whose deciding components are of two kinds are not ordered by the
            // language, so the comparison is a type error, as `min` and `max` of them are in
            // the arm above (plan row FAIL-kernel-tuple-order-kinds; test
            // `m0_09_kernel_evaluator::tuples_whose_deciding_components_differ_in_kind_are_a_type_error`).
            let Some(o) = a.surface_order(b) else {
                return ty(vals);
            };
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
        (Prim::Get | Prim::TupleGet | Prim::GetAtomKey, [Value::Family(f), k]) => {
            f.lookup(k).unwrap_or_else(|| Value::atom("notFound"))
        }
        (Prim::Count, [Value::Family(f)]) => f.count(),
        (Prim::Has, [k, Value::Family(f)]) => Bool(f.contains(k)),
        (Prim::Range, [a, b]) if a.number_kind() == Some(0) && b.number_kind() == Some(0) => {
            range(a, b)?
        }
        // `a ..`: kept as its low end. Complexity tradeoff (COMPLEXITY.md RANGE-open): the
        // integers up to a key cannot be built for a set with no last entry, and a stream of
        // them would make a read at `k` cost O(k - a); from the low end a read, `in` and
        // `.first` cost O(1) (O(digits) for a wide integer), and nothing walks it (resolution
        // admits only those reads; plan row RANGE-open-walk for the rest).
        (Prim::RangeFrom, [a]) if a.number_kind() == Some(0) => {
            Value::Family(Family::range_from(a.clone()))
        }
        (Prim::FirstEntry, [Value::Family(f)]) => entry_tuple(f.end_entry(false)),
        (Prim::LastEntry, [Value::Family(f)]) => entry_tuple(f.end_entry(true)),
        (Prim::EntryAfter | Prim::EntryBefore, [Value::Family(f), Value::Tuple(e)])
            if e.len() == 2 =>
        {
            entry_tuple(
                f.entry_beside(&e[0], p == Prim::EntryAfter)
                    .map_err(|e| too_large(p, e))?,
            )
        }
        (Prim::First | Prim::Last, [Value::Family(f)]) => leaf_at_end(f, p == Prim::Last),
        (Prim::Union, [Value::Family(a), Value::Family(b)]) => Value::Family(a.union(b)?),
        (Prim::ListConcat, [Value::Family(a), Value::Family(b)]) => match a.concat(b) {
            Some(f) => Value::Family(f),
            None => return ty(vals),
        },
        (Prim::Atom, [Str(name), Value::Tuple(names), args @ ..]) if names.is_empty() => {
            Value::atom_with(atom_name(name)?, args.to_vec())
        }
        (Prim::Atom, [Str(name), Value::Tuple(names), args @ ..]) if names.len() == args.len() => {
            let mut fields = Vec::with_capacity(names.len());
            for (n, v) in names.iter().zip(args) {
                let Str(n) = n else { return ty(vals) };
                fields.push((atom_name(n)?, v.clone()));
            }
            match Value::atom_named(atom_name(name)?, fields) {
                Some(v) => v,
                None => return ty(vals),
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
        (Prim::At, [Value::Family(f), k]) => {
            f.lookup(k).unwrap_or_else(|| Value::atom("outOfBounds"))
        }
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
            | Prim::FromUtf8
            | Prim::Round
            | Prim::RoundTiesAway
            | Prim::Floor
            | Prim::Ceil
            | Prim::Trunc
            | Prim::AwayFromZero,
            [x],
        ) => crate::words::word(p, x)?,
        (Prim::Split, [Str(s), Str(sep)]) => crate::words::split(s, sep)?,
        (Prim::Lines, [Str(s)]) => crate::words::lines(s)?,
        (Prim::Join, [Value::Family(f), Str(sep)]) => match crate::words::join(f, sep)? {
            Some(v) => v,
            None => return ty(vals),
        },
        (Prim::Allocate, [total, Value::Family(w), k]) => {
            match crate::words::allocate(total, w, k)? {
                Some(v) => v,
                None => return ty(vals),
            }
        }
        _ if crate::bits::is_bit_word(p) => crate::bits::word(p, vals)?,
        (Prim::Sum, [Value::Tuple(items)]) => {
            if items.iter().any(|v| matches!(v, Value::Atom(_))) {
                return Ok(Value::merge_failures(
                    items
                        .iter()
                        .filter(|v| matches!(v, Value::Atom(_)))
                        .cloned(),
                ));
            }
            let Some((first, rest)) = items.split_first() else {
                return Ok(Int(0));
            };
            if first.number_kind().is_none() {
                return ty(vals);
            }
            let mut total = first.clone();
            for x in rest {
                total = prim_data(Prim::Add, vec![total, x.clone()])?;
            }
            total
        }
        _ => return ty(vals),
    };
    Ok(out)
}
