//! Provenance (step L1.20, DESIGN.md sec:keypaths): the fact address of every value a run
//! computes, and the facts each one read.
//!
//! A fact is one node instance: a node of the term together with the instances of the
//! regions around it (sec:kernel, the objects of the dependency theorem). Its address is the pair of a
//! static [`NodeAddress`], code identity, and a dynamic keypath, data identity, and no two
//! facts of a run share one. A run records its facts when
//! [`Evaluator::with_provenance`](crate::Evaluator::with_provenance) asks for them; the
//! record is the run graph, each fact naming the facts it read.

/// The persistent vector of a fact address's node and keypath.
pub use imbl::Vector;
use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;

use crate::term::{FixKind, Term};
use crate::value::Value;

/// The static half of a fact address: the position of each call site through which the run
/// entered the function holding the node, and then the node's own position. A position is
/// the node's number in the preorder of the evaluated term. Only equality and order mean
/// anything; the numbers change with the build (sec:keypaths, the opaque token).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NodeAddress(pub Vector<u32>);

impl NodeAddress {
    /// The node's own position, the last.
    pub fn position(&self) -> u32 {
        *self.0.last().expect("a node address names a node")
    }
}

/// A fact address: (static node address, dynamic keypath). The keypath holds the wave stamp,
/// then each enclosing region's coordinate: a family key, a generation number, an iterate
/// of a lattice `fix`, the key of a definedness `fix` entry, the step of a `fold`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct FactAddress {
    /// The code identity.
    pub node: NodeAddress,
    /// The data identity.
    pub keypath: Vector<Value>,
}

impl fmt::Display for FactAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let node: Vec<String> = self.node.0.iter().map(u32::to_string).collect();
        let keys: Vec<String> = self.keypath.iter().map(Value::to_string).collect();
        write!(f, "{}@({})", node.join("/"), keys.join(", "))
    }
}

/// One node instance of a run.
#[derive(Clone, Debug)]
pub struct Fact {
    /// Where it is.
    pub address: FactAddress,
    /// Its value; `None` for a function.
    pub value: Option<Value>,
    /// The facts it read, by index into [`Provenance::facts`], in the order it read them.
    pub inputs: Vec<usize>,
}

/// The run graph of one evaluation: its facts, each after the facts it read.
#[derive(Clone, Debug)]
pub struct Provenance {
    pub(crate) term: Term,
    pub(crate) facts: Vec<Fact>,
}

impl Provenance {
    /// Every fact, in the order the run completed them.
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }

    /// The fact the run's result came from, the last one completed.
    pub fn result(&self) -> usize {
        self.facts.len() - 1
    }

    /// The term at `node`'s position.
    pub fn term(&self, node: &NodeAddress) -> &Term {
        let mut stack = vec![&self.term];
        let mut n = 0;
        while let Some(t) = stack.pop() {
            if n == node.position() {
                return t;
            }
            n += 1;
            stack.extend(children(t).into_iter().rev());
        }
        panic!("no node at position {}", node.position())
    }

    /// The addresses held by more than one fact; a correct run has none (sec:keypaths, one
    /// writer per fact address).
    pub fn repeated(&self) -> Vec<&FactAddress> {
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        for f in &self.facts {
            if !seen.insert(&f.address) {
                out.push(&f.address);
            }
        }
        out
    }

    /// The origins of the failure that fact `i` holds: for each distinct failure, the facts
    /// where it first appeared, so a merged `#errs` keeps the origins of all its operands
    /// rather than a winner (sec:failure). A failure first appears at a fact none of whose
    /// inputs holds it. Empty when the fact holds no failure.
    pub fn origins(&self, i: usize) -> BTreeSet<usize> {
        let Some(v @ Value::Atom(_)) = &self.facts[i].value else {
            return BTreeSet::new();
        };
        let members: Vec<Value> = match v.errs() {
            Some(set) => set.keys().cloned().collect(),
            None => vec![v.clone()],
        };
        members.iter().flat_map(|m| self.first(i, m)).collect()
    }

    fn first(&self, i: usize, atom: &Value) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        let mut stack = vec![i];
        let mut seen = BTreeSet::new();
        while let Some(j) = stack.pop() {
            if !seen.insert(j) {
                continue;
            }
            let from: Vec<usize> = self.facts[j]
                .inputs
                .iter()
                .copied()
                .filter(|&k| self.facts[k].value.as_ref().is_some_and(|v| holds(v, atom)))
                .collect();
            if from.is_empty() {
                out.insert(j);
            }
            stack.extend(from);
        }
        out
    }
}

/// Whether `v` holds the failure `atom`: is it, is an `#errs` with it as a member, or holds it
/// in a tuple, a family or a payload.
fn holds(v: &Value, atom: &Value) -> bool {
    if v == atom {
        return true;
    }
    match v {
        Value::Atom(a) => a.args.iter().any(|x| holds(x, atom)),
        Value::Tuple(xs) | Value::Path(xs) => xs.iter().any(|x| holds(x, atom)),
        Value::Family(f) => f.leaves().iter().any(|(_, x)| holds(x, atom)),
        _ => false,
    }
}

/// The subterms of a term in the order that numbers the positions.
pub(crate) fn children(t: &Term) -> Vec<&Term> {
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => vec![],
        Term::Lam(_, body) => vec![body],
        Term::App(f, args) => std::iter::once(&**f).chain(args).collect(),
        Term::Prim(_, args) => args.iter().collect(),
        Term::Let(_, e, body) => vec![e, body],
        Term::If(c, a, b) => vec![c, a, b],
        Term::Match(s, arms) => std::iter::once(&**s)
            .chain(arms.iter().map(|(_, b)| b))
            .collect(),
        Term::Fam { domain, body, .. } => vec![domain, body],
        Term::Reindex { family, kf, vf, .. } => vec![family, kf, vf],
        Term::Discard { family, sel } => vec![family, sel],
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => [family, op]
            .into_iter()
            .chain(identity)
            .map(|t| &**t)
            .collect(),
        Term::Fix {
            init, step, kind, ..
        } => match kind {
            FixKind::Lattice { join } => vec![init, step, join],
            FixKind::Definedness => vec![init, step],
        },
        Term::Gen {
            init, step, guard, ..
        } => vec![init, step, guard],
        Term::Push(_, v) => vec![v],
    }
}

/// A copy of `t` sharing no subterm with itself: a position is a node's address in memory
/// while the run lasts, and a term built by cloning shares the subterms of its copies.
pub(crate) fn unshare(t: &Term) -> Term {
    let u = |t: &Arc<Term>| Arc::new(unshare(t));
    let all = |ts: &[Term]| ts.iter().map(unshare).collect();
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => t.clone(),
        Term::Lam(ps, body) => Term::Lam(ps.clone(), u(body)),
        Term::App(f, args) => Term::App(u(f), all(args)),
        Term::Prim(p, args) => Term::Prim(*p, all(args)),
        Term::Let(x, e, body) => Term::Let(x.clone(), u(e), u(body)),
        Term::If(c, a, b) => Term::If(u(c), u(a), u(b)),
        Term::Match(s, arms) => Term::Match(
            u(s),
            arms.iter().map(|(p, b)| (p.clone(), unshare(b))).collect(),
        ),
        Term::Fam { domain, var, body } => Term::Fam {
            domain: u(domain),
            var: var.clone(),
            body: u(body),
        },
        Term::Reindex {
            family,
            kf,
            vf,
            witness,
        } => Term::Reindex {
            family: u(family),
            kf: u(kf),
            vf: u(vf),
            witness: witness.clone(),
        },
        Term::Discard { family, sel } => Term::Discard {
            family: u(family),
            sel: u(sel),
        },
        Term::Fold {
            family,
            op,
            identity,
            depth,
            ev,
        } => Term::Fold {
            family: u(family),
            op: u(op),
            identity: identity.as_ref().map(u),
            depth: *depth,
            ev: ev.clone(),
        },
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ev,
        } => Term::Fix {
            init: u(init),
            step: u(step),
            this: this.clone(),
            key: key.clone(),
            kind: match kind {
                FixKind::Lattice { join } => FixKind::Lattice { join: u(join) },
                FixKind::Definedness => FixKind::Definedness,
            },
            ev: ev.clone(),
        },
        Term::Gen {
            init,
            step,
            guard,
            pos,
        } => Term::Gen {
            init: u(init),
            step: u(step),
            guard: u(guard),
            pos: *pos,
        },
        Term::Push(port, v) => Term::Push(port.clone(), u(v)),
    }
}
