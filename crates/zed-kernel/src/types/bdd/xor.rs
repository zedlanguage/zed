//! The exclusive or of atoms in its one form: the atoms' set, each atom taken (module `set`),
//! and a constant joined to them, so that the exclusive or of one set of atoms is one node
//! whatever order it was built in.
//!
//! The node of a set is built over the set's tree: a tree node's exclusive or joins those of its
//! two subtrees and its own atom, two at a time, each as `p&!q | !p&q`, with the complement
//! `p&q | !p&!q` made beside it. Since one set is one tree, of one shape, its node is one
//! expression, kept in a table of the thread by the tree node's id and the constant, as are
//! those of its subtrees. A set with a literal added or removed has `O(log n)` new tree nodes in
//! expectation, and only those take new expressions, each in constant time.
//!
//! The table holds each node weakly, and a node leaves it when it is dropped (step TABLE-life).
//! The two expressions made beside each other share the halves they were made from (`Pair`),
//! and the one dropped first is made again from them when its complement is asked for
//! ([`mate`]), equal as built to the one dropped.
//!
//! An exclusive or is recognized when it is built from two others ([`xor_of`], [`xor_choice`]),
//! and a literal is one, of one atom; any other part is not taken for one.

use std::collections::BTreeMap;
use std::sync::{Arc, Weak};

use super::set::{self, Set, Tree};
use super::{Expr, Form, Literal, Op, Operands, Owned, Part};

/// An exclusive or: the set of its atoms, each taken, and the constant joined to them.
pub(super) type Tag<A> = (Arc<Set<A>>, bool);

/// The halves `p` and `q` that an exclusive or and its complement are made from, and the set of
/// atoms they are the one form of, if they are.
pub(super) struct Pair<A: Literal> {
    p: Part<A>,
    q: Part<A>,
    pub(super) atoms: Option<Arc<Set<A>>>,
}

/// A pair's halves and set are freed in a loop (module `deep`), as an expression's operands are.
impl<A: Literal> Drop for Pair<A> {
    fn drop(&mut self) {
        for part in [&mut self.p, &mut self.q] {
            if part.is_leaf().is_none() {
                A::free(Owned::Part(std::mem::replace(part, Part::leaf(false))));
            }
        }
        if let Some(s) = self.atoms.take() {
            A::free(Owned::Set(s));
        }
    }
}

/// The live exclusive ors of a thread, by the id of their set's tree node and their constant.
pub(in crate::types) type XorTable<A> = BTreeMap<(u64, bool), Weak<Expr<A>>>;

/// The exclusive or of the one literal on `atom`, taken or refused.
fn literal<A: Literal>(atom: &A, taken: bool) -> Tag<A> {
    (set::single((atom.clone(), true)), !taken)
}

/// Whether `x` is the complement of `y`.
fn opposite<A: Literal>(x: &Tag<A>, y: &Tag<A>) -> bool {
    x.0.id == y.0.id && x.1 != y.1
}

/// The exclusive or of `x` and `y`.
fn join<A: Literal>(x: &Tag<A>, y: &Tag<A>) -> Part<A> {
    Part::xor(
        set::symmetric(&Some(x.0.clone()), &Some(y.0.clone())),
        x.1 != y.1,
    )
}

/// The live exclusive or of the set's tree node `id` and `constant`.
fn found<A: Literal>(id: u64, constant: bool) -> Option<Part<A>> {
    A::table(|t| t.xors.get(&(id, constant)).and_then(Weak::upgrade)).map(Part::Expr)
}

impl<A: Literal> Part<A> {
    /// The part as an exclusive or in its one form: a literal, or a node [`Part::xor`] made.
    pub(super) fn xor_tag(&self) -> Option<Tag<A>> {
        match self {
            Part::Bdd(b) => b.as_literal().map(|(a, taken)| literal(a, taken)),
            Part::Expr(e) => {
                let (pair, constant) = e.xor.as_ref()?;
                Some((pair.atoms.clone()?, *constant))
            }
        }
    }

    /// The exclusive or of `atoms`, each taken, and `constant`, in its one form.
    pub(super) fn xor(atoms: Tree<A>, constant: bool) -> Part<A> {
        let Some(root) = atoms else {
            return Part::leaf(constant);
        };
        if constant && let Some(n) = found(root.id, true) {
            return n;
        }
        let x = node(&root);
        if constant { x.not() } else { x }
    }
}

/// The exclusive or of the atoms of the tree under `n`, built for each tree node below that has
/// none yet, children first, from a stack. The nodes built are held until their parents are.
fn node<A: Literal>(n: &Arc<Set<A>>) -> Part<A> {
    // A node with no children is the literal of its atom, and takes no entry in the table.
    let known = |n: &Arc<Set<A>>| match (&n.left, &n.right) {
        (None, None) => Some(Part::literal(n.key.0.clone())),
        _ => found(n.id, false),
    };
    if let Some(x) = known(n) {
        return x;
    }
    let mut held: BTreeMap<u64, Part<A>> = BTreeMap::new();
    let mut stack = vec![(n, false)];
    while let Some((m, ready)) = stack.pop() {
        if !ready {
            stack.push((m, true));
            for c in [&m.left, &m.right].into_iter().flatten() {
                match known(c) {
                    Some(x) => {
                        held.insert(c.id, x);
                    }
                    None => stack.push((c, false)),
                }
            }
            continue;
        }
        let side = |c: &Option<Arc<Set<A>>>| {
            (c.as_ref()).map(|c| {
                (held.get(&c.id).cloned()).expect("a tree node's children are built before it")
            })
        };
        let k = Part::literal(m.key.0.clone());
        let x = match (side(&m.left), side(&m.right)) {
            (Some(l), None) => xor2(&l, &k, Some(m)),
            (None, Some(r)) => xor2(&k, &r, Some(m)),
            (Some(l), Some(r)) => xor2(&xor2(&l, &k, None), &r, Some(m)),
            (None, None) => unreachable!("a tree node with no children is a literal, known"),
        };
        held.insert(m.id, x);
    }
    held.remove(&n.id).expect("the root is built last")
}

/// `p&!q | !p&q`, made as it stands, with its complement `p&q | !p&!q` held as its own; both
/// tagged as the exclusive ors of `atoms` when given.
fn xor2<A: Literal>(p: &Part<A>, q: &Part<A>, atoms: Option<&Arc<Set<A>>>) -> Part<A> {
    let pair = Arc::new(Pair {
        p: p.clone(),
        q: q.clone(),
        atoms: atoms.cloned(),
    });
    let (np, nq) = (p.not(), q.not());
    let x = half(&pair, false, &np, &nq);
    let n = half(&pair, true, &np, &nq);
    if let (Part::Expr(e), Part::Expr(m)) = (&x, &n) {
        let _ = e.complement.set(n.clone());
        m.set_back(e);
    }
    x
}

/// The exclusive or of `pair` with `constant`: `p&!q | !p&q` when `false`, `p&q | !p&!q` when
/// `true`, `np` and `nq` the halves' complements; kept in the thread's table when the pair is the
/// one form of a set.
fn half<A: Literal>(pair: &Arc<Pair<A>>, constant: bool, np: &Part<A>, nq: &Part<A>) -> Part<A> {
    let (p, q) = (&pair.p, &pair.q);
    let (x, y) = if constant {
        (p.zip(q, Op::And), np.zip(nq, Op::And))
    } else {
        (p.zip(nq, Op::And), np.zip(q, Op::And))
    };
    let (x, y) = if x.before(&y) { (x, y) } else { (y, x) };
    let r = Part::expr_xor(Form::Or(x, y), Some((pair.clone(), constant)));
    if let (Some(s), Part::Expr(e)) = (&pair.atoms, &r) {
        // An entry left by a node dropped on another thread is replaced.
        A::table(|t| t.xors.insert((s.id, constant), Arc::downgrade(e)));
    }
    r
}

/// The exclusive or of `pair` with `constant`, the complement of the one with the other
/// constant: the live one of the table, or made again as it was first made.
pub(super) fn mate<A: Literal>(pair: &Arc<Pair<A>>, constant: bool) -> Part<A> {
    if let Some(s) = &pair.atoms
        && let Some(x) = found(s.id, constant)
    {
        return x;
    }
    half(pair, constant, &pair.p.not(), &pair.q.not())
}

/// The two operands of `p` under `op`, each an exclusive or in its one form.
fn pair<A: Literal>(p: &Part<A>, op: Op) -> Option<[Tag<A>; 2]> {
    // A chain is listed only when it has two literals, so a long one costs constant time here.
    if let Part::Bdd(b) = p
        && b.chain_len(op) != Some(2)
    {
        return None;
    }
    match p.operands(op)? {
        Operands::Two(x, y) => Some([x.xor_tag()?, y.xor_tag()?]),
        Operands::Chain(_, lits) => match lits[..] {
            [(a, s), (b, t)] => Some([literal(a, s), literal(b, t)]),
            _ => None,
        },
    }
}

/// `a op b` as an exclusive or in its one form, when it is `u&v | !u&!v` under `Or` or
/// `(u|v) & (!u|!v)` under `And`, `u` and `v` exclusive ors in their one form.
pub(super) fn xor_of<A: Literal>(a: &Part<A>, b: &Part<A>, op: Op) -> Option<Part<A>> {
    let inner = if op == Op::Or { Op::And } else { Op::Or };
    let [u, v] = pair(a, inner)?;
    let [w, z] = pair(b, inner)?;
    if !(opposite(&u, &w) && opposite(&v, &z) || opposite(&u, &z) && opposite(&v, &w)) {
        return None;
    }
    // `u&v | !u&!v` is `!(u ^ v)`; `(u|v) & (!u|!v)` is `u ^ v`.
    let x = join(&u, &v);
    Some(if op == Op::Or { x.not() } else { x })
}

/// The choice `c&x | !c&y` as an exclusive or in its one form, when `y` is `!x` and `c` and `x`
/// are exclusive ors in their one form: `!(c ^ x)`.
pub(super) fn xor_choice<A: Literal>(c: &Part<A>, x: &Part<A>, y: &Part<A>) -> Option<Part<A>> {
    let (tx, ty) = (x.xor_tag()?, y.xor_tag()?);
    if !opposite(&tx, &ty) {
        return None;
    }
    Some(join(&c.xor_tag()?, &tx).not())
}
