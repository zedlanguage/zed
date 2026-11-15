//! The value a run gives when it may be a function or hold one ([`super::Evaluator::run_made`]): a
//! back end that runs one node of a program in the kernel takes back a family of functions a
//! `map` made, a `where` kept or a remap moved, as the kernel holds it (rows
//! FAIL-native-fam-result-holds-function and FAIL-machine-held-family; DESIGN.md step L1.17:
//! only a use that needs data, such as showing or `==`, is an error).
//!
//! A run's value lives in the run's machine, its closures pointing into the term run and into
//! environments the run made. [`Made`] is the same value apart from them: a list of nodes,
//! each part before what holds it, a value held twice being one node. A closure is its lambda,
//! the body shared with the term run, with the value of each name of its environment the body
//! may read, so the back end builds the closure's term again from the terms of those values.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use super::{Closure, Held, Machine, R, Shape, Slot, V, lookup, type_err};
use crate::term::{Prim, Shared, Term};
use crate::value::{Fields, HeldFamily, Value};

/// A value a run gives, functions and all: its nodes, each part before the value that holds
/// it, the value itself last. A value held at two places is one node, named by both.
#[derive(Clone, Debug)]
pub struct Made {
    /// The nodes, the value's own last.
    pub nodes: Vec<MadeNode>,
}

/// One node of a [`Made`].
#[derive(Clone, Debug)]
pub enum MadeNode {
    /// Data.
    Data(Value),
    /// A primitive used as a function.
    Prim(Prim),
    /// An input port read by lookup, by its name.
    Source(Arc<str>),
    /// A closure.
    Fun(MadeFun),
    /// A tuple, an atom or a family with a part that is no data, and the nodes of its parts in
    /// the order of the kernel's `Held`'s parts.
    Held(MadeShape, Vec<usize>),
}

/// A closure the kernel made: `params -> body`, where each name of `caps` that the body reads
/// is the value of its node.
#[derive(Clone, Debug)]
pub struct MadeFun {
    /// The lambda's parameters.
    pub params: Vec<Arc<str>>,
    /// The lambda's body, shared with the term the kernel ran.
    pub body: Shared,
    /// Each name of the closure's environment the body may read, in name order, and its node.
    pub caps: Vec<(Arc<str>, usize)>,
}

/// The closed term of a closure the kernel made, given its parameters, its body, the names of
/// its captures and the term of each capture in the order of `names`:
/// `params -> ((names…) -> body)(caps…)`. The captures are bound inside the lambda, so the
/// term gives its closure in one step, as a lambda does, and a closure that captures another
/// twice is not built twice; a call binds the captures, as a call of a closure the back end
/// made binds its own, O(captures). They are bound by one application, not a `let` each, so
/// no capture's term is read under another capture's name: a back end names the values it
/// binds outside a term (`\0cell k`), and a name of this closure's environment may be one of
/// those from an earlier run, standing for another value.
pub fn fun_term(params: &[Arc<str>], body: &Shared, names: &[Arc<str>], caps: Vec<Term>) -> Term {
    if caps.is_empty() {
        return Term::Lam(params.to_vec(), body.clone());
    }
    let inner = Term::Lam(names.to_vec(), body.clone());
    let body = Term::App(Shared::new(inner), caps);
    Term::Lam(params.to_vec(), Shared::new(body))
}

/// What a [`MadeNode::Held`] is.
#[derive(Clone, Debug)]
pub enum MadeShape {
    /// A tuple.
    Tuple,
    /// An atom: its name and its field names, sorted as [`Value::atom_named`] sorts them,
    /// empty for a payload by position.
    Atom(Arc<str>, Fields),
    /// A family whose entries at [`HeldFamily`]'s parts are the parts.
    Family(HeldFamily),
}

/// The names a body reads, each once, sorted: every variable of the body, those it binds
/// itself too. A name the body binds and its environment binds as well is a capture it never
/// reads, which costs a binding of a value that exists.
// Complexity tradeoff: the naive set is the free names of the body, which needs every binder
// of the calculus (a lambda's, a `let`'s, a `fam`'s, a `fix`'s and the patterns') walked with a
// scope. Used: every variable, a superset of the free ones, O(the body's distinct subterms)
// with a visited set over shared subterms, since a term the back end built is a graph that a
// walk of every path would cross exponentially often. Tradeoff: a name bound in the body and
// in the environment is captured though never read.
fn reads(body: &Shared) -> Vec<Arc<str>> {
    let mut names: HashSet<Arc<str>> = HashSet::new();
    let mut seen: HashSet<u64> = HashSet::new();
    let mut stack: Vec<&Term> = Vec::new();
    // The shared subterms of the term in hand, entered after it unless entered before.
    let mut kids: Vec<&Shared> = Vec::new();
    seen.insert(body.id());
    stack.push(body);
    while let Some(t) = stack.pop() {
        let mut push = |s| kids.push(s);
        match t {
            Term::Lit(_) | Term::PrimFn(_) | Term::Read(_) => {}
            Term::Var(x) => {
                names.insert(x.clone());
            }
            Term::Lam(_, b) => push(b),
            Term::App(f, args) => {
                push(f);
                stack.extend(args.iter());
            }
            Term::Prim(_, args) => stack.extend(args.iter()),
            Term::Let(_, e, b) => {
                push(e);
                push(b);
            }
            Term::If(c, a, b) => {
                push(c);
                push(a);
                push(b);
            }
            Term::Match(s, arms) => {
                push(s);
                stack.extend(arms.iter().map(|(_, t)| t));
            }
            Term::Fam { domain, body, .. } => {
                push(domain);
                push(body);
            }
            Term::Reindex { family, kf, vf, .. } => {
                push(family);
                push(kf);
                push(vf);
            }
            Term::Discard { family, sel } => {
                push(family);
                push(sel);
            }
            Term::Fold {
                family,
                op,
                identity,
                ..
            } => {
                push(family);
                push(op);
                if let Some(i) = identity {
                    push(i);
                }
            }
            Term::Fix { init, step, .. } => {
                push(init);
                push(step);
            }
            Term::Gen {
                init, step, guard, ..
            } => {
                push(init);
                push(step);
                push(guard);
            }
            Term::Push(_, v) => push(v),
        }
        for s in kids.drain(..) {
            if seen.insert(s.id()) {
                stack.push(s);
            }
        }
    }
    let mut names: Vec<_> = names.into_iter().collect();
    names.sort();
    names
}

/// A step of [`Machine::made`]: a value to visit, or a closure or held value whose parts are
/// the last results.
enum Task<'t> {
    Visit(V<'t>),
    Fun(Rc<Closure<'t>>, Vec<Arc<str>>),
    Held(Rc<Held<'t>>),
}

impl<'t> Machine<'_, 't> {
    /// `v` apart from the run (see [`Made`]).
    // Complexity tradeoff: the naive way follows each path to a value, so a closure captured
    // by two closures, each captured by two more, is visited 2^d times for d levels. Used:
    // each closure and held value is visited once, by its address, and its parts once each,
    // on a list of tasks, not the thread's stack, since values nest as deep as a program makes
    // them: O(the values and captures reached), plus the names each distinct body reads,
    // found once per body. Tradeoff: one map entry per closure and held value.
    pub(super) fn made(&mut self, v: V<'t>) -> R<Made> {
        let mut nodes = Vec::new();
        let mut done: HashMap<*const (), usize> = HashMap::new();
        let mut bodies: HashMap<u64, Rc<[Arc<str>]>> = HashMap::new();
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
                            let names = bodies
                                .entry(c.body.id())
                                .or_insert_with(|| reads(c.body).into())
                                .clone();
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
