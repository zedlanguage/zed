//! The exclusive or of atoms in its one form: the atoms' set, each atom taken (module `set`),
//! and a constant joined to them, so that the exclusive or of one set of atoms is one node
//! whatever order it was built in.
//!
//! The node of a set is built over the set's tree: a tree node's exclusive or joins those of its
//! two subtrees and its own atom, two at a time, each as `p&!q | !p&q`, with the complement
//! `p&q | !p&!q` made beside it. Since one set is one tree, of one shape, its node is one
//! expression, kept in a table of the thread by the tree node's id, as are those of its
//! subtrees. A set with a literal added or removed has `O(log n)` new tree nodes in expectation,
//! and only those take new expressions, each in constant time.
//!
//! An exclusive or is recognized when it is built from two others ([`xor_of`], [`xor_choice`]),
//! and a literal is one, of one atom; any other part is not taken for one.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::set::{self, Set, Tree};
use super::{Form, Literal, Op, Operands, Part};

/// An exclusive or: the set of its atoms, each taken, and the constant joined to them.
pub(super) type Tag<A> = (Arc<Set<A>>, bool);

/// The exclusive ors of a thread, of the constant `false`, by the id of their set's tree node.
pub(in crate::types) type XorTable<A> = BTreeMap<u64, Part<A>>;

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

impl<A: Literal> Part<A> {
    /// The part as an exclusive or in its one form: a literal, or a node [`Part::xor`] made.
    pub(super) fn xor_tag(&self) -> Option<Tag<A>> {
        match self {
            Part::Bdd(b) => b.as_literal().map(|(a, taken)| literal(a, taken)),
            Part::Expr(e) => e.xor.clone(),
        }
    }

    /// The exclusive or of `atoms`, each taken, and `constant`, in its one form.
    pub(super) fn xor(atoms: Tree<A>, constant: bool) -> Part<A> {
        let Some(root) = atoms else {
            return Part::leaf(constant);
        };
        let x = node(&root);
        if constant { x.not() } else { x }
    }
}

/// The exclusive or of the atoms of the tree under `n`, built for each tree node below that has
/// none yet, children first, from a stack.
fn node<A: Literal>(n: &Arc<Set<A>>) -> Part<A> {
    // A node with no children is the literal of its atom, and takes no entry in the table.
    let known = |n: &Arc<Set<A>>| match (&n.left, &n.right) {
        (None, None) => Some(Part::literal(n.key.0.clone())),
        _ => A::table(|t| t.xors.get(&n.id).cloned()),
    };
    if let Some(x) = known(n) {
        return x;
    }
    let mut stack = vec![(n, false)];
    while let Some((m, ready)) = stack.pop() {
        if !ready {
            stack.push((m, true));
            for c in [&m.left, &m.right].into_iter().flatten() {
                if known(c).is_none() {
                    stack.push((c, false));
                }
            }
            continue;
        }
        let side = |c: &Option<Arc<Set<A>>>| {
            (c.as_ref()).map(|c| known(c).expect("a tree node's children are built before it"))
        };
        let k = Part::literal(m.key.0.clone());
        let x = match (side(&m.left), side(&m.right)) {
            (Some(l), None) => xor2(&l, &k, Some(m)),
            (None, Some(r)) => xor2(&k, &r, Some(m)),
            (Some(l), Some(r)) => xor2(&xor2(&l, &k, None), &r, Some(m)),
            (None, None) => unreachable!("a tree node with no children is a literal, known"),
        };
        A::table(|t| t.xors.insert(m.id, x.clone()));
    }
    known(n).expect("the root is built last")
}

/// `p&!q | !p&q`, made as it stands, with its complement `p&q | !p&!q` kept as its own; both
/// tagged as the exclusive ors of `atoms` when given.
fn xor2<A: Literal>(p: &Part<A>, q: &Part<A>, atoms: Option<&Arc<Set<A>>>) -> Part<A> {
    let (np, nq) = (p.not(), q.not());
    let or = |x: Part<A>, y: Part<A>, constant: bool| {
        let (x, y) = if x.before(&y) { (x, y) } else { (y, x) };
        Part::expr_xor(Form::Or(x, y), atoms.map(|s| (s.clone(), constant)))
    };
    let x = or(p.zip(&nq, Op::And), np.zip(q, Op::And), false);
    let n = or(p.zip(q, Op::And), np.zip(&nq, Op::And), true);
    if let (Part::Expr(e), Part::Expr(m)) = (&x, &n) {
        let _ = e.complement.set(n.clone());
        let _ = m.complement.set(x.clone());
    }
    x
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
