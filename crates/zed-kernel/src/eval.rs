//! The reference evaluator of the kernel calculus (step M0.9).
//!
//! The evaluator is strict and big-step: a term reduces to a value, arguments left to right.
//! It is written for clarity, not speed; every back end is tested against it. The choices
//! the spec leaves to the reference semantics are recorded in DESIGN.md sec:kernel,
//! "Reference semantics", and repeated on the item they govern here.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::error::KernelError;
use crate::exact::{canonical_tree, exact_sum};
use crate::family::{Family, Keypath};
use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{Euclid, Signed, Zero};

use crate::num::MAX_BITS;
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
    domain: BTreeSet<Value>,
    defined: BTreeMap<Value, Value>,
}

#[derive(Debug)]
struct Frame {
    name: Arc<str>,
    value: V,
    next: Env,
}

type Env = Option<Rc<Frame>>;

fn bind(env: &Env, name: Arc<str>, value: V) -> Env {
    Some(Rc::new(Frame {
        name,
        value,
        next: env.clone(),
    }))
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
        }
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
        std::thread::scope(|scope| {
            let worker = std::thread::Builder::new()
                .stack_size(STACK_BYTES)
                .spawn_scoped(scope, || self.run_here(term));
            match worker.expect("the evaluator thread starts").join() {
                Ok(out) => out,
                Err(panic) => std::panic::resume_unwind(panic),
            }
        })
    }

    fn run_here(&mut self, term: &Term) -> Result<Value, KernelError> {
        match self.eval(term, &None) {
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

    fn eval(&mut self, term: &Term, env: &Env) -> R<V> {
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
                self.eval(body, &bind(env, name.clone(), v))
            }
            Term::If(c, a, b) => match self.data(c, env)? {
                Value::Bool(true) => self.eval(a, env),
                Value::Bool(false) => self.eval(b, env),
                atom @ Value::Atom(_) => Ok(V::Data(atom)),
                other => type_err(format!("`if` on {other}")),
            },
            Term::Match(scrutinee, arms) => {
                let v = self.data(scrutinee, env)?;
                for (pat, body) in arms {
                    let mut env2 = env.clone();
                    if matches(pat, &v, &mut env2) {
                        return self.eval(body, &env2);
                    }
                }
                type_err(format!("no arm matches {v}"))
            }
            Term::Fam { domain, var, body } => {
                let domain = self.family(domain, env)?;
                self.pure += 1;
                let out = domain
                    .keys()
                    .map(|k| {
                        Ok((
                            vec![k.clone()],
                            self.data(body, &bind(env, var.clone(), V::Data(k.clone())))?,
                        ))
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
                let (kf, vf) = (self.eval(kf, env)?, self.eval(vf, env)?);
                self.pure += 1;
                let out = self.reindex(&family, &kf, &vf);
                self.pure -= 1;
                Ok(V::Data(Value::Family(out?)))
            }
            Term::Discard { family, sel } => {
                let family = self.family(family, env)?;
                let sel = self.eval(sel, env)?;
                self.pure += 1;
                let out = self.discard(&family, &sel, &mut Vec::new());
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
                let op = self.eval(op, env)?;
                let identity = identity.as_ref().map(|t| self.data(t, env)).transpose()?;
                self.pure += 1;
                let out = self.fold(&family, &op, identity, *depth);
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
                let (step, guard) = (self.eval(step, env)?, self.eval(guard, env)?);
                Ok(V::Data(self.generations(init, &step, &guard, *pos)?))
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
                let mut env = c.env.clone();
                for (p, a) in c.params.iter().zip(args) {
                    env = bind(&env, p.clone(), a);
                }
                self.depth += 1;
                let out = self.eval(&c.body, &env);
                self.depth -= 1;
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
            return match part.defined.get(k) {
                Some(v) => Ok(V::Data(v.clone())),
                None if part.domain.contains(k) => Err(Stop::Undefined {
                    fix: part.fix,
                    key: k.clone(),
                }),
                None => Ok(V::Data(Value::atom("notFound"))),
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

    fn reindex(&mut self, family: &Family, kf: &V, vf: &V) -> R<Family> {
        let mut out = Vec::new();
        for (path, v) in family.leaves() {
            let p = Value::Path(path);
            let key = match self.call2(kf, p.clone(), v.clone())? {
                Value::Path(keys) => keys,
                single => vec![single],
            };
            out.push((key, self.call2(vf, p, v)?));
        }
        Ok(Family::from_leaves(out)?)
    }

    fn discard(&mut self, family: &Family, sel: &V, prefix: &mut Keypath) -> R<Family> {
        let mut out = Vec::new();
        for (k, v) in family.iter() {
            prefix.push(k.clone());
            let verdict = self.call2(sel, Value::Path(prefix.clone()), v.clone())?;
            match verdict {
                Value::Bool(true) => match v {
                    Value::Family(sub) => out.push((
                        vec![k.clone()],
                        Value::Family(self.discard(sub, sel, prefix)?),
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
            prefix.pop();
        }
        Ok(Family::from_leaves(out)?)
    }

    fn fold(&mut self, family: &Family, op: &V, identity: Option<Value>, depth: usize) -> R<Value> {
        let leaves = family.leaves();
        if leaves.iter().any(|(p, _)| p.len() != depth) {
            return Err(KernelError::MixedDepth.into());
        }
        if depth == 1 {
            let values: Vec<Value> = leaves.into_iter().map(|(_, v)| v).collect();
            return self.reduce(&values, op, identity);
        }
        // Collapse the innermost level beneath each outer keypath.
        let mut groups: BTreeMap<Keypath, Vec<Value>> = BTreeMap::new();
        for (mut path, v) in leaves {
            path.pop();
            groups.entry(path).or_default().push(v);
        }
        let mut out = Vec::new();
        for (path, values) in groups {
            out.push((path, self.reduce(&values, op, identity.clone())?));
        }
        Ok(Value::Family(Family::from_leaves(out)?))
    }

    /// Reduces one level in key order. A fold of the primitive `+` over floats is the exact
    /// sum, rounded once; any other operator runs on the canonical tree.
    fn reduce(&mut self, values: &[Value], op: &V, identity: Option<Value>) -> R<Value> {
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
        canonical_tree(values, &mut |a, b| self.call2(op, a, b))
    }

    fn fix_lattice(&mut self, init: &Term, step: &Term, join: &Term, env: &Env) -> R<Value> {
        let mut x = self.data(init, env)?;
        let (step, join) = (self.eval(step, env)?, self.eval(join, env)?);
        loop {
            self.burn()?;
            let next = match self.apply(&step, vec![V::Data(x.clone())])? {
                V::Data(v) => v,
                _ => return type_err("a fix step returned a function"),
            };
            let joined = self.call2(&join, x.clone(), next)?;
            if joined == x {
                return Ok(x);
            }
            x = joined;
        }
    }

    fn fix_definedness(
        &mut self,
        init: &Term,
        body: &Term,
        this: &Arc<str>,
        key: &Arc<str>,
        env: &Env,
    ) -> R<Value> {
        let domain: BTreeSet<Value> = self.family(init, env)?.keys().cloned().collect();
        self.fixes += 1;
        let fix = Definedness {
            id: self.fixes,
            domain,
            body,
            this,
            key,
            env,
        };
        let mut defined = BTreeMap::new();
        let stalled = match self.schedule {
            Schedule::Rounds => self.define_in_rounds(&fix, &mut defined, None)?,
            Schedule::Chaotic(seed) => self.define_in_rounds(&fix, &mut defined, Some(seed))?,
            Schedule::Pull => self.define_on_demand(&fix, &mut defined)?,
        };
        if !stalled.is_empty() {
            return Err(KernelError::Stalled { keys: stalled }.into());
        }
        let leaves = defined.into_iter().map(|(k, v)| (vec![k], v));
        Ok(Value::Family(Family::from_leaves(leaves)?))
    }

    /// Evaluates the entry at `k` against the entries in `defined`: its value, or the key of
    /// the undefined entry of this `fix` it read first.
    fn entry(
        &mut self,
        fix: &Definedness,
        defined: &BTreeMap<Value, Value>,
        k: &Value,
    ) -> R<Result<Value, Value>> {
        let part = V::Partial(Rc::new(Partial {
            fix: fix.id,
            domain: fix.domain.clone(),
            defined: defined.clone(),
        }));
        let env = bind(
            &bind(fix.env, fix.this.clone(), part),
            fix.key.clone(),
            V::Data(k.clone()),
        );
        match self.eval(fix.body, &env) {
            Ok(V::Data(v)) => Ok(Ok(v)),
            Ok(_) => type_err("a fix entry is a function"),
            Err(Stop::Undefined { fix: id, key }) if id == fix.id => Ok(Err(key)),
            Err(e) => Err(e),
        }
    }

    /// Defines entries in rounds until every entry is defined or a round defines none, and
    /// returns the keys left undefined. Without a seed each round reads the family as it
    /// began (Jacobi); with one, each round visits the entries in a shuffled order and reads
    /// the entries defined before it in the same round.
    fn define_in_rounds(
        &mut self,
        fix: &Definedness,
        defined: &mut BTreeMap<Value, Value>,
        seed: Option<u64>,
    ) -> R<Vec<Value>> {
        let mut rng = seed.map(SplitMix);
        loop {
            self.burn()?;
            let mut pending: Vec<Value> = fix
                .domain
                .iter()
                .filter(|k| !defined.contains_key(*k))
                .cloned()
                .collect();
            if pending.is_empty() {
                return Ok(pending);
            }
            if let Some(rng) = &mut rng {
                rng.shuffle(&mut pending);
            }
            let start = defined.clone();
            let mut progress = false;
            for k in pending {
                let read = if rng.is_some() { &*defined } else { &start };
                if let Ok(v) = self.entry(fix, read, &k)? {
                    defined.insert(k, v);
                    progress = true;
                }
            }
            if !progress {
                return Ok(fix
                    .domain
                    .iter()
                    .filter(|k| !defined.contains_key(*k))
                    .cloned()
                    .collect());
            }
        }
    }

    /// Demands each entry in key order, evaluating first each undefined entry it reads, and
    /// returns the keys that stalled: those on a cycle and those waiting on one.
    fn define_on_demand(
        &mut self,
        fix: &Definedness,
        defined: &mut BTreeMap<Value, Value>,
    ) -> R<Vec<Value>> {
        let mut stalled = BTreeSet::new();
        for k0 in &fix.domain {
            if defined.contains_key(k0) || stalled.contains(k0) {
                continue;
            }
            let mut demanded = vec![k0.clone()];
            while let Some(k) = demanded.last().cloned() {
                self.burn()?;
                match self.entry(fix, defined, &k)? {
                    Ok(v) => {
                        defined.insert(k, v);
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

    fn generations(&mut self, init: Value, step: &V, guard: &V, pos: GuardPos) -> R<Value> {
        let mut frames = vec![init];
        loop {
            if pos == GuardPos::Before && !self.go_on(guard, &mut frames)? {
                break;
            }
            self.burn()?;
            let last = frames.last().expect("generation 0 is present").clone();
            match self.apply(step, vec![V::Data(last)])? {
                V::Data(next) => frames.push(next),
                _ => return type_err("a gen step returned a function"),
            }
            if pos == GuardPos::After && !self.go_on(guard, &mut frames)? {
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
    fn go_on(&mut self, guard: &V, frames: &mut Vec<Value>) -> R<bool> {
        let last = frames.last().expect("generation 0 is present").clone();
        match self.apply(guard, vec![V::Data(last)])? {
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
    domain: BTreeSet<Value>,
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

fn matches(pat: &Pattern, v: &Value, env: &mut Env) -> bool {
    match (pat, v) {
        (Pattern::Wild, _) => true,
        (Pattern::Bind(name), v) => {
            *env = bind(env, name.clone(), V::Data(v.clone()));
            true
        }
        (Pattern::Lit(l), v) => l == v,
        (Pattern::AnyAtom, Value::Atom(_)) => true,
        (Pattern::Atom(name, ps), Value::Atom(a)) => {
            a.name == *name
                && a.fields.is_empty()
                && ps.len() == a.args.len()
                && ps.iter().zip(&a.args).all(|(p, x)| matches(p, x, env))
        }
        (Pattern::Fields(name, fs), Value::Atom(a)) => {
            a.name == *name
                && !a.fields.is_empty()
                && fs.iter().all(|(f, p)| match a.fields.binary_search(f) {
                    Ok(i) => matches(p, &a.args[i], env),
                    Err(_) => false,
                })
        }
        (Pattern::Tuple(ps), Value::Tuple(xs)) => {
            ps.len() == xs.len() && ps.iter().zip(xs).all(|(p, x)| matches(p, x, env))
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
            match p {
                Prim::Lt => Bool(a < b),
                Prim::Le => Bool(a <= b),
                Prim::Gt => Bool(a > b),
                Prim::Ge => Bool(a >= b),
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
