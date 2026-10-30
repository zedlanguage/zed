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
use std::collections::{BTreeMap, BTreeSet};
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

    /// The term at `node`'s position. It walks the term to the position, so the terms of
    /// many facts are read from [`Provenance::terms`].
    pub fn term(&self, node: &NodeAddress) -> &Term {
        let at = node.position() as usize;
        self.preorder()
            .nth(at)
            .unwrap_or_else(|| panic!("no node at position {at}"))
    }

    /// The term at each position, in one walk: `terms()[f.address.node.position()]`.
    pub fn terms(&self) -> Vec<&Term> {
        self.preorder().collect()
    }

    fn preorder(&self) -> impl Iterator<Item = &Term> {
        let mut stack = vec![&self.term];
        std::iter::from_fn(move || {
            let t = stack.pop()?;
            stack.extend(children(t).into_iter().rev());
            Some(t)
        })
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
        let members: BTreeSet<Value> = match v.errs() {
            Some(set) => set.keys().cloned().collect(),
            None => BTreeSet::from([v.clone()]),
        };
        // The members each fact reached holds, its value walked once: each member's search
        // walked every value it tested, an `#errs` of up to all the members.
        let mut held: BTreeMap<usize, BTreeSet<&Value>> = BTreeMap::new();
        let mut out = BTreeSet::new();
        for m in &members {
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
                    .filter(|&k| {
                        held.entry(k)
                            .or_insert_with(|| {
                                let mut found = BTreeSet::new();
                                if let Some(v) = &self.facts[k].value {
                                    holds(v, &members, &mut found);
                                }
                                found
                            })
                            .contains(m)
                    })
                    .collect();
                if from.is_empty() {
                    out.insert(j);
                }
                stack.extend(from);
            }
        }
        out
    }
}

/// Adds to `found` each failure of `members` that `v` holds: that `v` is, has as a member of
/// an `#errs`, or holds in a tuple, a family or a payload.
fn holds<'a>(v: &Value, members: &'a BTreeSet<Value>, found: &mut BTreeSet<&'a Value>) {
    if let Some(m) = members.get(v) {
        found.insert(m);
    }
    match v {
        Value::Atom(a) => a.args.iter().for_each(|x| holds(x, members, found)),
        Value::Tuple(xs) | Value::Path(xs) => xs.iter().for_each(|x| holds(x, members, found)),
        Value::Family(f) => f.iter().for_each(|(_, x)| holds(x, members, found)),
        _ => {}
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
