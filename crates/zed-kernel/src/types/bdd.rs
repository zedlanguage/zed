//! Reduced ordered binary decision diagrams over the types of one universe (DESIGN.md
//! sec:type_language): the form of the tuple and morphism parts.
//!
//! A diagram is a leaf, no value of the universe or every value, or a node `(atom & hi) |
//! (!atom & lo)`, with each atom smaller than every atom below it and `hi` and `lo` distinct.
//! Two diagrams over one order of atoms denote one Boolean function of their atoms exactly when
//! they are equal. The complement swaps the leaves, in time linear in the size of the diagram,
//! and a union or intersection takes each pair of nodes at most once, in time the product of
//! the two sizes: a union of clauses would make the complement of a union of `C` clauses of two
//! types each a union of `2^C` clauses.
//!
//! Nodes are shared: the nodes of a thread are kept in a table, so that one atom with one pair
//! of children is one node, and two equal diagrams built on one thread are one pointer. Each
//! node and expression keeps a hash of its contents made from its children's, and two are
//! ordered by it first, so a comparison reads their contents only when the hashes are equal,
//! and reads each pair of nodes or expressions at most once ([`order`]).
//!
//! A diagram is canonical, so some functions have only diagrams exponential in the number of
//! their atoms: `(m1 & !n1) | … | (mC & !nC)`, with every `m` ordered before every `n`, has
//! `2^C` nodes. A union or intersection therefore keeps its diagram only when it has no more
//! nodes than its two operands together, and otherwise keeps the expression (`Part::Expr`),
//! built in constant time; so a diagram has no more nodes than the atoms written to build it.
//! A part is decided (module `empty`) by three-valued operations: it is evaluated with some
//! atoms known (`Part::eval3`) and restricted to them (`Part::restrict`), each in time linear in
//! its nodes; asked which atoms every value takes or refuses (`Part::forced`), in `O(n log n)`
//! on a diagram and one evaluation per atom on an expression; and settled on its shared
//! subexpressions (`Part::settle`), one evaluation per shared subexpression in each round. The
//! last two are above the rule of low complexity, an open item (DESIGN.md L1.23). None of them
//! walks paths, whose number can be exponential in the nodes. Listing values takes one pass over the nodes (`Bdd::reaching`);
//! `Bdd::paths` remains for display.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as Atomic};

use super::{Morphism, Op, Row, mix};

mod list;

/// The next node id. Diagram nodes and expressions take their ids from one counter, so an id
/// names one node among both; ids key the maps of a walk, never addresses.
static NEXT: AtomicU64 = AtomicU64::new(2);

#[derive(Clone)]
pub(super) enum Bdd<A: Literal> {
    Leaf(bool),
    Node(Arc<Branch<A>>),
}

pub(super) struct Branch<A: Literal> {
    id: u64,
    digest: u64,
    atom: A,
    hi: Bdd<A>,
    lo: Bdd<A>,
}

type Table<A> = BTreeMap<(A, u64, u64), Arc<Branch<A>>>;

/// A node's id, atom, `hi` and `lo`.
pub(super) type NodeView<'a, A> = (u64, &'a A, &'a Bdd<A>, &'a Bdd<A>);

/// The atoms of a universe, each kind with its thread's table of nodes.
pub(super) trait Literal: Ord + Clone + 'static {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R;
    /// A hash of the atom, equal for equal atoms.
    fn digest(&self) -> u64;
    /// Drops a part in the thread's loop of type parts (module `deep`).
    fn free(part: Part<Self>);
}

thread_local! {
    static TUPLES: RefCell<Table<Row>> = const { RefCell::new(BTreeMap::new()) };
    static MORPHISMS: RefCell<Table<Morphism>> = const { RefCell::new(BTreeMap::new()) };
}

impl Literal for Row {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R {
        super::hold();
        TUPLES.with(|t| f(&mut t.borrow_mut()))
    }
    fn digest(&self) -> u64 {
        Row::digest(self)
    }
    fn free(part: Part<Row>) {
        super::free(super::Freed::Tuples(part));
    }
}

impl Literal for Morphism {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R {
        super::hold();
        MORPHISMS.with(|t| f(&mut t.borrow_mut()))
    }
    fn digest(&self) -> u64 {
        let m = mix(6, self.guarantee.digest());
        mix(mix(m, self.permission.digest()), self.value.digest())
    }
    fn free(part: Part<Morphism>) {
        super::free(super::Freed::Morphisms(part));
    }
}

/// A diagram node's children are freed in a loop (module `deep`), not by recursion: a node's
/// last owner is the thread's table, so a long diagram is freed when the thread ends.
impl<A: Literal> Drop for Branch<A> {
    fn drop(&mut self) {
        for b in [&mut self.hi, &mut self.lo] {
            if let Bdd::Node(_) = b {
                A::free(Part::Bdd(std::mem::replace(b, Bdd::Leaf(false))));
            }
        }
    }
}

/// An expression's operands and complement are freed in a loop, as a node's children are.
impl<A: Literal> Drop for Expr<A> {
    fn drop(&mut self) {
        let (p, q) = match &mut self.form {
            Form::Not(p) => (p, None),
            Form::Or(p, q) | Form::And(p, q) => (p, Some(q)),
        };
        for part in std::iter::once(p).chain(q) {
            if part.is_leaf().is_none() {
                A::free(std::mem::replace(part, Part::leaf(false)));
            }
        }
        if let Some(c) = self.complement.take() {
            A::free(c);
        }
    }
}

impl<A: Literal> Bdd<A> {
    pub(super) fn literal(a: A) -> Bdd<A> {
        Bdd::node(a, Bdd::Leaf(true), Bdd::Leaf(false))
    }

    fn id(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => u64::from(*b),
            Bdd::Node(n) => n.id,
        }
    }

    fn digest(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => mix(7, u64::from(*b)),
            Bdd::Node(n) => n.digest,
        }
    }

    fn node(atom: A, hi: Bdd<A>, lo: Bdd<A>) -> Bdd<A> {
        if hi == lo {
            return hi;
        }
        let key = (atom, hi.id(), lo.id());
        if let Some(n) = A::table(|t| t.get(&key).cloned()) {
            return Bdd::Node(n);
        }
        let n = Arc::new(Branch {
            id: NEXT.fetch_add(1, Atomic::Relaxed),
            digest: mix(mix(key.0.digest(), hi.digest()), lo.digest()),
            atom: key.0.clone(),
            hi,
            lo,
        });
        A::table(|t| t.insert(key, n.clone()));
        Bdd::Node(n)
    }

    /// The union or intersection.
    pub(super) fn zip(&self, other: &Bdd<A>, op: Op) -> Bdd<A> {
        self.apply(other, op, &mut HashMap::new())
    }

    /// Whether the diagram is one atom or its complement.
    fn is_literal(&self) -> bool {
        matches!(self, Bdd::Node(n) if matches!(n.hi, Bdd::Leaf(_)) && matches!(n.lo, Bdd::Leaf(_)))
    }

    /// Whether the diagram is a chain under `op`: a meet of literals under `And`, a union of
    /// them under `Or`.
    fn is_chain(&self, op: Op) -> bool {
        let out = op == Op::Or;
        let mut b = self;
        loop {
            match b {
                Bdd::Leaf(v) => return *v != out,
                Bdd::Node(n) => match (&n.hi, &n.lo) {
                    (Bdd::Leaf(v), x) | (x, Bdd::Leaf(v)) if *v == out => b = x,
                    _ => return false,
                },
            }
        }
    }

    /// The literals of a chain under `op` of two or more literals, each an atom and whether
    /// the chain takes it; `None` for any other diagram.
    fn chain(&self, op: Op) -> Option<Vec<(&A, bool)>> {
        if self.is_literal() || !self.is_chain(op) {
            return None;
        }
        let out = op == Op::Or;
        let mut lits = Vec::new();
        let mut b = self;
        while let Bdd::Node(n) = b {
            b = match &n.lo {
                Bdd::Leaf(v) if *v == out => {
                    lits.push((&n.atom, !out));
                    &n.hi
                }
                _ => {
                    lits.push((&n.atom, out));
                    &n.lo
                }
            };
        }
        Some(lits)
    }

    /// The chain under `op` without its literal on `atom`, which it takes when `taken`.
    fn chain_without(&self, op: Op, atom: &A, taken: bool) -> Bdd<A> {
        // The literal is left out by fixing it to the value `op` passes over.
        let value = taken != (op == Op::Or);
        self.restrict(&|a| (a == atom).then_some(value), &mut HashMap::new())
    }

    /// The literal on `atom`, taken or refused.
    fn literal_of(atom: &A, taken: bool) -> Bdd<A> {
        let l = Bdd::literal(atom.clone());
        if taken { l } else { l.not() }
    }

    /// The atom of a diagram that is one literal, and whether the literal takes it.
    fn as_literal(&self) -> Option<(&A, bool)> {
        match self {
            Bdd::Node(n) if self.is_literal() => Some((&n.atom, matches!(n.hi, Bdd::Leaf(true)))),
            _ => None,
        }
    }

    fn apply(&self, other: &Bdd<A>, op: Op, memo: &mut HashMap<(u64, u64), Bdd<A>>) -> Bdd<A> {
        match (op, self, other) {
            (Op::And, Bdd::Leaf(false), _) | (Op::And, _, Bdd::Leaf(false)) => {
                return Bdd::Leaf(false);
            }
            (Op::Or, Bdd::Leaf(true), _) | (Op::Or, _, Bdd::Leaf(true)) => {
                return Bdd::Leaf(true);
            }
            (_, Bdd::Leaf(_), x) | (_, x, Bdd::Leaf(_)) => return x.clone(),
            _ if self.id() == other.id() => return self.clone(),
            _ => {}
        }
        let key = (self.id(), other.id());
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let (Bdd::Node(a), Bdd::Node(b)) = (self, other) else {
            unreachable!("both leaves were handled")
        };
        let r = match a.atom.cmp(&b.atom) {
            Ordering::Equal => Bdd::node(
                a.atom.clone(),
                a.hi.apply(&b.hi, op, memo),
                a.lo.apply(&b.lo, op, memo),
            ),
            Ordering::Less => Bdd::node(
                a.atom.clone(),
                a.hi.apply(other, op, memo),
                a.lo.apply(other, op, memo),
            ),
            Ordering::Greater => Bdd::node(
                b.atom.clone(),
                self.apply(&b.hi, op, memo),
                self.apply(&b.lo, op, memo),
            ),
        };
        memo.insert(key, r.clone());
        r
    }

    pub(super) fn not(&self) -> Bdd<A> {
        self.flip(&mut HashMap::new())
    }

    /// The diagram with each atom that `fix` decides replaced by its value, each node rebuilt
    /// once.
    fn restrict(
        &self,
        fix: &impl Fn(&A) -> Option<bool>,
        memo: &mut HashMap<u64, Bdd<A>>,
    ) -> Bdd<A> {
        let Bdd::Node(n) = self else {
            return self.clone();
        };
        if let Some(r) = memo.get(&n.id) {
            return r.clone();
        }
        let r = match fix(&n.atom) {
            Some(true) => n.hi.restrict(fix, memo),
            Some(false) => n.lo.restrict(fix, memo),
            None => Bdd::node(
                n.atom.clone(),
                n.hi.restrict(fix, memo),
                n.lo.restrict(fix, memo),
            ),
        };
        memo.insert(n.id, r.clone());
        r
    }

    /// The atoms every value takes, and those every value refuses: [`Bdd::forced_to`] `true`.
    fn forced(&self) -> (Vec<A>, Vec<A>) {
        self.forced_to(true)
    }

    /// The atoms taken, and those refused, on every path to the leaf `leaf`. The atoms are
    /// ordered, so an atom is free when a path to `leaf` passes its place in the order without
    /// testing it, or tests it and goes on to `leaf` both ways. One pass over the nodes that reach
    /// `leaf` marks the places each edge passes over and the ways each node goes on; the atoms are
    /// then sorted, so the time is `O(n log n)` in the nodes.
    fn forced_to(&self, leaf: bool) -> (Vec<A>, Vec<A>) {
        let Bdd::Node(root) = self else {
            return (Vec::new(), Vec::new());
        };
        // The nodes from which `leaf` is reached, each once.
        let mut reaches: HashMap<u64, bool> = HashMap::new();
        let mut live: Vec<&Arc<Branch<A>>> = Vec::new();
        let mut stack = vec![(root, false)];
        while let Some((n, expanded)) = stack.pop() {
            if reaches.contains_key(&n.id) {
                continue;
            }
            if !expanded {
                stack.push((n, true));
                for c in [&n.lo, &n.hi] {
                    if let Bdd::Node(m) = c
                        && !reaches.contains_key(&m.id)
                    {
                        stack.push((m, false));
                    }
                }
                continue;
            }
            let r = [&n.hi, &n.lo].into_iter().any(|c| match c {
                Bdd::Leaf(v) => *v == leaf,
                Bdd::Node(m) => reaches[&m.id],
            });
            reaches.insert(n.id, r);
            if r {
                live.push(n);
            }
        }
        if !reaches[&root.id] {
            return (Vec::new(), Vec::new());
        }
        let mut atoms: Vec<&A> = live.iter().map(|n| &n.atom).collect();
        atoms.sort();
        atoms.dedup();
        let place = |a: &A| {
            atoms
                .binary_search(&a)
                .expect("an atom of a node is placed")
        };
        // `passed[i] - passed[i - 1]` edges pass over place `i`; `ways[i]` the ways on.
        let count = atoms.len();
        let mut passed = vec![0isize; count + 1];
        let mut ways = vec![(false, false); count];
        let mut pass = |from: usize, to: usize| {
            if from < to {
                passed[from] += 1;
                passed[to] -= 1;
            }
        };
        pass(0, place(&root.atom));
        for n in &live {
            let i = place(&n.atom);
            for (c, v) in [(&n.hi, true), (&n.lo, false)] {
                let to = match c {
                    Bdd::Leaf(v) if *v == leaf => count,
                    Bdd::Leaf(_) => continue,
                    Bdd::Node(m) if reaches[&m.id] => place(&m.atom),
                    Bdd::Node(_) => continue,
                };
                pass(i + 1, to);
                if v {
                    ways[i].0 = true;
                } else {
                    ways[i].1 = true;
                }
            }
        }
        let (mut taken, mut refused) = (Vec::new(), Vec::new());
        let mut over = 0;
        for (i, a) in atoms.iter().enumerate() {
            over += passed[i];
            match (over, ways[i]) {
                (0, (true, false)) => taken.push((*a).clone()),
                (0, (false, true)) => refused.push((*a).clone()),
                _ => {}
            }
        }
        (taken, refused)
    }

    fn flip(&self, memo: &mut HashMap<u64, Bdd<A>>) -> Bdd<A> {
        let Bdd::Node(n) = self else {
            return Bdd::Leaf(*self == Bdd::Leaf(false));
        };
        if let Some(r) = memo.get(&n.id) {
            return r.clone();
        }
        let r = Bdd::node(n.atom.clone(), n.hi.flip(memo), n.lo.flip(memo));
        memo.insert(n.id, r.clone());
        r
    }
}

impl<A: Literal> Bdd<A> {
    /// The node's id, atom, `hi` and `lo`, or the leaf's value.
    pub(super) fn branch(&self) -> Result<NodeView<'_, A>, bool> {
        match self {
            Bdd::Leaf(b) => Err(*b),
            Bdd::Node(n) => Ok((n.id, &n.atom, &n.hi, &n.lo)),
        }
    }

    /// Whether `f` holds of every atom, each node visited once.
    pub(super) fn atoms<'a>(&'a self, f: &mut impl FnMut(&'a A) -> bool) -> bool {
        fn go<'a, A: Literal>(
            b: &'a Bdd<A>,
            seen: &mut HashSet<u64>,
            f: &mut impl FnMut(&'a A) -> bool,
        ) -> bool {
            let Bdd::Node(n) = b else {
                return true;
            };
            !seen.insert(n.id) || (f(&n.atom) && go(&n.hi, seen, f) && go(&n.lo, seen, f))
        }
        go(self, &mut HashSet::new(), f)
    }

    /// Whether `f` holds of every path to the `true` leaf, given as the atoms it takes and those
    /// it refuses, in order, stopping at the first path where it does not. Below a node whose
    /// `hi` is `true` the `lo` path does not refuse the node's atom, since `a | (!a & L)` is
    /// `a | L`, so a union of atoms is a path per atom.
    pub(super) fn paths<'a>(&'a self, f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool) -> bool {
        self.walk(false, f)
    }

    /// [`Bdd::paths`]; with `prune`, `f` is also asked of each path's atoms taken so far with
    /// none refused, and the paths below are passed over when it holds: refusing more atoms
    /// only removes values, so if `f` holds of `pos` alone it holds of every path below.
    pub(super) fn walk<'a>(
        &'a self,
        prune: bool,
        f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool,
    ) -> bool {
        fn go<'a, A: Literal>(
            b: &'a Bdd<A>,
            prune: bool,
            pos: &mut Vec<&'a A>,
            neg: &mut Vec<&'a A>,
            f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool,
        ) -> bool {
            let n = match b {
                Bdd::Leaf(false) => return true,
                Bdd::Leaf(true) => return f(pos, neg),
                Bdd::Node(n) => n,
            };
            pos.push(&n.atom);
            let hi = (prune && !matches!(n.hi, Bdd::Leaf(false)) && f(pos, &[]))
                || go(&n.hi, prune, pos, neg, f);
            pos.pop();
            if !hi {
                return false;
            }
            let refuse = !matches!(n.hi, Bdd::Leaf(true));
            if refuse {
                neg.push(&n.atom);
            }
            let lo = go(&n.lo, prune, pos, neg, f);
            if refuse {
                neg.pop();
            }
            lo
        }
        go(self, prune, &mut Vec::new(), &mut Vec::new(), f)
    }

    /// Whether `f` holds of each node's atom and state, for the nodes from whose `hi` a chain of
    /// `lo` edges alone reaches `true`: the nodes that are the last `hi` taken on some path to
    /// `true`. The root has the state `start`; an edge to a node's `hi` passes on `take` of its
    /// state and its atom, an edge to its `lo` its state; a node's state is `join` of the states
    /// of the edges into it. Each node is visited once, after every node with an edge into it,
    /// so the time is linear in the nodes however many paths there are.
    ///
    /// Which nodes are the last `hi` of a path does not depend on the atom order as much as
    /// which nodes have a `hi` other than `false`: a meet `x & y` has the one path `x, y` in
    /// either order, and only its last node is passed to `f`, so a user that reads a node's state
    /// as the atoms its paths took sees the meet in both orders (step L1.37a: the atom order
    /// follows digests, and truncated digests order atoms differently).
    pub(super) fn reaching<S>(
        &self,
        start: S,
        take: impl Fn(&S, &A) -> S,
        join: impl Fn(&S, &S) -> S,
        mut f: impl FnMut(&A, &S) -> bool,
    ) -> bool {
        let Bdd::Node(root) = self else {
            return true;
        };
        // Nodes in reverse postorder of a depth-first walk: each after those above it.
        let mut order: Vec<&Branch<A>> = Vec::new();
        let mut seen = HashSet::new();
        let mut stack: Vec<(&Branch<A>, bool)> = vec![(root, false)];
        while let Some((n, below)) = stack.pop() {
            if below {
                order.push(n);
                continue;
            }
            if !seen.insert(n.id) {
                continue;
            }
            stack.push((n, true));
            for c in [&n.lo, &n.hi] {
                if let Bdd::Node(c) = c
                    && !seen.contains(&c.id)
                {
                    stack.push((c, false));
                }
            }
        }
        // Whether a chain of `lo` edges from each node reaches `true`, children first.
        let mut lo_true: HashMap<u64, bool> = HashMap::with_capacity(order.len());
        let chain = |b: &Bdd<A>, lo_true: &HashMap<u64, bool>| match b {
            Bdd::Leaf(v) => *v,
            Bdd::Node(c) => *lo_true
                .get(&c.id)
                .expect("a node is ordered after its children"),
        };
        for n in &order {
            let t = chain(&n.lo, &lo_true);
            lo_true.insert(n.id, t);
        }
        let mut state: HashMap<u64, S> = HashMap::from([(root.id, start)]);
        for n in order.into_iter().rev() {
            let here = state
                .remove(&n.id)
                .expect("a node is reached before it is visited");
            if chain(&n.hi, &lo_true) && !f(&n.atom, &here) {
                return false;
            }
            for (child, s) in [(&n.hi, take(&here, &n.atom)), (&n.lo, here)] {
                match child {
                    Bdd::Leaf(_) => {}
                    Bdd::Node(c) => {
                        let s = match state.remove(&c.id) {
                            Some(t) => join(&t, &s),
                            None => s,
                        };
                        state.insert(c.id, s);
                    }
                }
            }
        }
        true
    }

    /// Whether the path that `holds` chooses at each atom ends at `true`.
    pub(super) fn eval(&self, holds: impl Fn(&A) -> bool) -> bool {
        let mut b = self;
        loop {
            match b {
                Bdd::Leaf(v) => return *v,
                Bdd::Node(n) => b = if holds(&n.atom) { &n.hi } else { &n.lo },
            }
        }
    }
}

/// A tuple part of one length, or the morphism part: a diagram, or, when a connective's diagram
/// would have more nodes than its operands together, the connective applied to its operands.
#[derive(Clone, Debug)]
pub(super) enum Part<A: Literal> {
    Bdd(Bdd<A>),
    Expr(Arc<Expr<A>>),
}

pub(super) struct Expr<A: Literal> {
    /// The node's id, unique among the nodes of the process.
    id: u64,
    digest: u64,
    form: Form<A>,
    /// The complement, made once, so that a chain of choices is negated in steps, not walked.
    complement: std::sync::OnceLock<Part<A>>,
}

#[derive(Debug)]
pub(super) enum Form<A: Literal> {
    Not(Part<A>),
    Or(Part<A>, Part<A>),
    And(Part<A>, Part<A>),
}

/// The operands of a part under a connective ([`Part::operands`]).
enum Operands<'a, A: Literal> {
    /// An expression's two operands.
    Two(&'a Part<A>, &'a Part<A>),
    /// A chain, with its literals.
    Chain(&'a Bdd<A>, Vec<(&'a A, bool)>),
}

impl<A: Literal> Part<A> {
    /// The hash of the part's contents.
    pub(super) fn digest(&self) -> u64 {
        match self {
            Part::Bdd(b) => b.digest(),
            Part::Expr(e) => e.digest,
        }
    }

    /// Whether `self` goes first of the two operands of a connective: the smaller digest, and
    /// of equal digests the smaller in the order of contents, so that two distinct parts whose
    /// digests collide still have one order (step L1.37a).
    fn before(&self, other: &Part<A>) -> bool {
        self.digest()
            .cmp(&other.digest())
            .then_with(|| self.cmp(other))
            .is_le()
    }

    pub(super) fn leaf(b: bool) -> Part<A> {
        Part::Bdd(Bdd::Leaf(b))
    }

    pub(super) fn literal(a: A) -> Part<A> {
        Part::Bdd(Bdd::literal(a))
    }

    /// Whether the part is no value (`Some(false)`) or every value (`Some(true)`) as built.
    pub(super) fn is_leaf(&self) -> Option<bool> {
        match self {
            Part::Bdd(Bdd::Leaf(b)) => Some(*b),
            _ => None,
        }
    }

    fn expr(form: Form<A>) -> Part<A> {
        let digest = match &form {
            Form::Not(p) => mix(8, p.digest()),
            Form::Or(a, b) => mix(mix(9, a.digest()), b.digest()),
            Form::And(a, b) => mix(mix(10, a.digest()), b.digest()),
        };
        Part::Expr(Arc::new(Expr {
            id: NEXT.fetch_add(1, Atomic::Relaxed),
            digest,
            form,
            complement: std::sync::OnceLock::new(),
        }))
    }

    pub(super) fn not(&self) -> Part<A> {
        match self {
            Part::Bdd(b) => Part::Bdd(b.not()),
            Part::Expr(e) => e
                .complement
                .get_or_init(|| {
                    let n = if let Form::Not(p) = &e.form {
                        p.clone()
                    } else if let Some((c, x, y)) = self.choice() {
                        Part::choose(&c, &x.not(), &y.not())
                    } else {
                        Part::expr(Form::Not(self.clone()))
                    };
                    if let Part::Expr(m) = &n {
                        let _ = m.complement.set(self.clone());
                    }
                    n
                })
                .clone(),
        }
    }

    pub(super) fn zip(&self, other: &Part<A>, op: Op) -> Part<A> {
        // A leaf that absorbs is the result; a leaf that does not leaves the other operand.
        let absorbs = op == Op::Or;
        match (self.is_leaf(), other.is_leaf()) {
            (Some(b), _) if b == absorbs => return self.clone(),
            (_, Some(b)) if b == absorbs => return other.clone(),
            (Some(_), _) => return other.clone(),
            (_, Some(_)) => return self.clone(),
            _ => {}
        }
        if self == other {
            return self.clone();
        }
        if self.same_as_not(other) {
            return Part::leaf(absorbs);
        }
        // Only chains grow a diagram, so each diagram is a decision list: the latest literal
        // that fires gives the value. Atoms read so far leave at most one function per literal
        // that fired, so a level has at most `n + 1` nodes and a diagram at most `n(n + 1)` on
        // `n` atoms, in any atom order.
        if let (Part::Bdd(a), Part::Bdd(b)) = (self, other)
            && (a.is_chain(op) || b.is_chain(op))
        {
            return Part::Bdd(a.zip(b, op));
        }
        // Choices on one condition meet branch by branch.
        if let (Some((c, x, y)), Some((d, u, v))) = (self.choice(), other.choice())
            && c == d
        {
            return Part::choose(&c, &x.zip(&u, op), &y.zip(&v, op));
        }
        // `c&x | !c&y` and `(!c|x) & (c|y)` are one choice.
        if let Some((c, x, y)) = Part::choice_of(self, other, op) {
            return Part::choose(&c, &x, &y);
        }
        let (a, b) = if self.before(other) {
            (self, other)
        } else {
            (other, self)
        };
        Part::expr(match op {
            Op::Or => Form::Or(a.clone(), b.clone()),
            Op::And => Form::And(a.clone(), b.clone()),
        })
    }

    /// Whether `self` is the complement of `other`, as built.
    fn same_as_not(&self, other: &Part<A>) -> bool {
        match (self, other) {
            (Part::Bdd(a), Part::Bdd(b)) => a.is_literal() && a.not() == *b,
            (Part::Expr(a), _) => {
                a.complement.get().is_some_and(|c| c == other) || self.not() == *other
            }
            _ => other.not() == *self,
        }
    }

    /// The condition of a choice, of `c` and `!c` the one [`Part::before`] puts first.
    fn condition(c: &Part<A>) -> (Part<A>, bool) {
        let n = c.not();
        if c.before(&n) {
            (c.clone(), true)
        } else {
            (n, false)
        }
    }

    /// The choice `c&x | !c&y`, in the one form each choice has.
    fn choose(c: &Part<A>, x: &Part<A>, y: &Part<A>) -> Part<A> {
        if x == y {
            return x.clone();
        }
        let (c, same) = Part::condition(c);
        let (x, y) = if same { (x, y) } else { (y, x) };
        match (x.is_leaf(), y.is_leaf()) {
            (Some(false), Some(false)) => return Part::leaf(false),
            (Some(true), Some(false)) => return c,
            (Some(false), Some(true)) => return c.not(),
            _ => {}
        }
        let parts = [c.zip(x, Op::And), c.not().zip(y, Op::And)];
        let [a, b] = if parts[0].before(&parts[1]) {
            parts
        } else {
            let [p, q] = parts;
            [q, p]
        };
        Part::expr(Form::Or(a, b))
    }

    /// The operands of an expression's `And` or `Or`, under `op`, or the literals of a chain
    /// under `op`.
    fn operands(&self, op: Op) -> Option<Operands<'_, A>> {
        match (self, op) {
            (Part::Expr(e), Op::And) => match &e.form {
                Form::And(a, b) => Some(Operands::Two(a, b)),
                _ => None,
            },
            (Part::Expr(e), Op::Or) => match &e.form {
                Form::Or(a, b) => Some(Operands::Two(a, b)),
                _ => None,
            },
            (Part::Bdd(b), _) => b.chain(op).map(|lits| Operands::Chain(b, lits)),
        }
    }

    /// `(c, x, y)` when `a op b` is a choice: under `Or`, `c&x | !c&y`; under `And`,
    /// `(!c|x) & (c|y)`. The condition `c` is an operand of `a`'s expression, or a literal of
    /// its chain, whose complement is one of `b`'s. When two or more conditions fit, which one
    /// a search finds first depends on the order of the atoms, so there is then no choice, and
    /// the parts built are the same in every order of the atoms (step BDD-atom-order).
    fn choice_of(a: &Part<A>, b: &Part<A>, op: Op) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let inner = if op == Op::Or { Op::And } else { Op::Or };
        let (l, r) = (a.operands(inner)?, b.operands(inner)?);
        // The literal of `lits` that `n` is.
        let within = |n: &Part<A>, lits: &[(&A, bool)]| match n {
            Part::Bdd(d) => d
                .as_literal()
                .filter(|(atom, taken)| lits.iter().any(|(x, t)| x == atom && t == taken))
                .map(|(atom, taken)| (atom.clone(), taken)),
            Part::Expr(_) => None,
        };
        let mut found = Vec::new();
        match (&l, &r) {
            (Operands::Two(p, q), Operands::Two(s, t)) => {
                for (c, x) in [(p, q), (q, p)] {
                    for (n, y) in [(s, t), (t, s)] {
                        if c.same_as_not(n) {
                            found.push(((*c).clone(), (*x).clone(), (*y).clone()));
                        }
                    }
                }
            }
            (Operands::Two(p, q), Operands::Chain(d, lits)) => {
                for (c, x) in [(p, q), (q, p)] {
                    if let Some((atom, taken)) = within(&c.not(), lits) {
                        let y = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push(((*c).clone(), (*x).clone(), y));
                    }
                }
            }
            (Operands::Chain(d, lits), Operands::Two(s, t)) => {
                for (n, y) in [(s, t), (t, s)] {
                    if let Some((atom, taken)) = within(&n.not(), lits) {
                        let c = Part::Bdd(Bdd::literal_of(&atom, taken));
                        let x = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push((c, x, (*y).clone()));
                    }
                }
            }
            (Operands::Chain(d, xs), Operands::Chain(e, ys)) => {
                // The atoms on which the chains' literals are complements, found by sorting so
                // that the time is `O(k log k)` in the literals; the rests are built only for
                // a single atom.
                let mut sorted = xs.clone();
                sorted.sort_unstable();
                let mut both = ys
                    .iter()
                    .filter(|(atom, taken)| sorted.binary_search(&(*atom, !*taken)).is_ok());
                let (Some(&(atom, taken)), None) = (both.next(), both.next()) else {
                    return None;
                };
                found.push((
                    Part::Bdd(Bdd::literal_of(atom, !taken)),
                    Part::Bdd(d.chain_without(inner, atom, !taken)),
                    Part::Bdd(e.chain_without(inner, atom, taken)),
                ));
            }
        }
        let mut found = found.into_iter();
        let (Some((c, x, y)), None) = (found.next(), found.next()) else {
            return None;
        };
        Some(if op == Op::Or {
            (c, x, y)
        } else {
            // `(c|x) & (!c|y)` takes `y` when `c`.
            (c, y, x)
        })
    }

    /// The choice this part is in its one form. Only an expression is one, since an operand
    /// of a chain's union is a literal, which has no operands.
    fn choice(&self) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let Part::Expr(e) = self else { return None };
        let Form::Or(a, b) = &e.form else { return None };
        Part::choice_of(a, b, Op::Or).map(|(c, x, y)| {
            let (d, same) = Part::condition(&c);
            if same { (d, x, y) } else { (d, y, x) }
        })
    }

    /// Whether the value whose membership in each atom `holds` decides is in the part.
    pub(super) fn eval(&self, holds: &impl Fn(&A) -> bool) -> bool {
        fn go<A: Literal>(
            p: &Part<A>,
            holds: &impl Fn(&A) -> bool,
            memo: &mut HashMap<u64, bool>,
        ) -> bool {
            let e = match p {
                Part::Bdd(b) => return b.eval(holds),
                Part::Expr(e) => e,
            };
            if let Some(v) = memo.get(&e.id) {
                return *v;
            }
            let v = match &e.form {
                Form::Not(a) => !go(a, holds, memo),
                Form::Or(a, b) => go(a, holds, memo) || go(b, holds, memo),
                Form::And(a, b) => go(a, holds, memo) && go(b, holds, memo),
            };
            memo.insert(e.id, v);
            v
        }
        go(self, holds, &mut HashMap::new())
    }

    /// The part's value on a set of values where `holds` gives each atom's: in every value
    /// (`Some(true)`), in none (`Some(false)`), or in some (`None`), by three-valued logic, each
    /// node and expression evaluated once. `Some(b)` is the part's value on every value of the
    /// set; `None` says nothing.
    pub(super) fn eval3(&self, holds: &impl Fn(&A) -> Option<bool>) -> Option<bool> {
        self.eval3_pinned(holds, &HashMap::new())
    }

    /// [`Part::eval3`], with each expression in `pins` taken to have the value beside it.
    fn eval3_pinned(
        &self,
        holds: &impl Fn(&A) -> Option<bool>,
        pins: &HashMap<u64, bool>,
    ) -> Option<bool> {
        fn bdd<A: Literal>(
            b: &Bdd<A>,
            holds: &impl Fn(&A) -> Option<bool>,
            memo: &mut HashMap<u64, Option<bool>>,
        ) -> Option<bool> {
            let n = match b {
                Bdd::Leaf(v) => return Some(*v),
                Bdd::Node(n) => n,
            };
            if let Some(v) = memo.get(&n.id) {
                return *v;
            }
            let v = match holds(&n.atom) {
                Some(true) => bdd(&n.hi, holds, memo),
                Some(false) => bdd(&n.lo, holds, memo),
                None => {
                    let hi = bdd(&n.hi, holds, memo);
                    if hi.is_none() {
                        None
                    } else {
                        bdd(&n.lo, holds, memo).filter(|lo| Some(*lo) == hi)
                    }
                }
            };
            memo.insert(n.id, v);
            v
        }
        let mut nodes = HashMap::new();
        let mut memo: HashMap<u64, Option<bool>> =
            pins.iter().map(|(e, v)| (*e, Some(*v))).collect();
        let mut stack = vec![self.clone()];
        // Each expression is evaluated after its operands, on a stack of parts still to do.
        while let Some(p) = stack.pop() {
            let e = match &p {
                Part::Bdd(b) => {
                    bdd(b, holds, &mut nodes);
                    continue;
                }
                Part::Expr(e) => e,
            };
            let key = e.id;
            if memo.contains_key(&key) {
                continue;
            }
            let value = |q: &Part<A>,
                         nodes: &mut HashMap<u64, Option<bool>>,
                         memo: &HashMap<u64, Option<bool>>| match q {
                Part::Bdd(b) => Some(bdd(b, holds, nodes)),
                Part::Expr(x) => memo.get(&x.id).copied(),
            };
            let operands: Vec<&Part<A>> = match &e.form {
                Form::Not(a) => vec![a],
                Form::Or(a, b) | Form::And(a, b) => vec![a, b],
            };
            let vs: Vec<Option<Option<bool>>> = operands
                .iter()
                .map(|q| value(q, &mut nodes, &memo))
                .collect();
            if vs.iter().any(|v| v.is_none()) {
                stack.push(p.clone());
                for (q, v) in operands.iter().zip(&vs) {
                    if v.is_none() {
                        stack.push((*q).clone());
                    }
                }
                continue;
            }
            let vs: Vec<Option<bool>> = vs.into_iter().flatten().collect();
            let v = match &e.form {
                Form::Not(_) => vs[0].map(|v| !v),
                Form::Or(..) => match (vs[0], vs[1]) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
                Form::And(..) => match (vs[0], vs[1]) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                },
            };
            memo.insert(key, v);
        }
        match self {
            Part::Bdd(b) => bdd(b, holds, &mut nodes),
            Part::Expr(e) => memo[&e.id],
        }
    }

    /// The part with each expression used more than once in it replaced by `true` when making
    /// it `false` makes the part `false` by three-valued logic, every atom unknown, and by
    /// `false` in the converse case, until no more is replaced. Every value of the part is in,
    /// or outside, such an expression, so the result holds every value of the part, and may
    /// hold more: it is empty only if the part is.
    pub(super) fn settle(&self) -> Part<A> {
        let mut p = self.clone();
        loop {
            let pins = p.pins();
            if pins.is_empty() {
                return p;
            }
            p = p.substitute_all(&pins);
        }
    }

    /// The pins of one round of [`Part::settle`]. Each trial value is carried up from the
    /// expression through the operators it changes, and stops at the first it leaves alone, so
    /// that a trial reads what it changes, not the whole part.
    fn pins(&self) -> HashMap<u64, bool> {
        // The expressions; those shared, in the order the walk finds them shared, so that the
        // pins taken do not depend on the expressions' ids.
        let mut ids: HashMap<u64, usize> = HashMap::new();
        let mut exprs: Vec<Arc<Expr<A>>> = Vec::new();
        let mut uses: Vec<usize> = Vec::new();
        let mut shared = Vec::new();
        let mut stack = vec![self.clone()];
        while let Some(q) = stack.pop() {
            let Part::Expr(e) = q else { continue };
            if let Some(&i) = ids.get(&e.id) {
                uses[i] += 1;
                if uses[i] == 2 {
                    shared.push(i);
                }
                continue;
            }
            ids.insert(e.id, exprs.len());
            exprs.push(e.clone());
            uses.push(1);
            match &e.form {
                Form::Not(a) => stack.push(a.clone()),
                // The first operand is pushed last, so it is walked first.
                Form::Or(a, b) | Form::And(a, b) => {
                    stack.push(b.clone());
                    stack.push(a.clone());
                }
            }
        }
        let Part::Expr(root) = self else {
            return HashMap::new();
        };
        let root = ids[&root.id];
        let id = |q: &Part<A>| match q {
            Part::Expr(x) => Some(ids[&x.id]),
            Part::Bdd(_) => None,
        };
        let operands = |e: &Expr<A>| match &e.form {
            Form::Not(a) => [Some(a.clone()), None],
            Form::Or(a, b) | Form::And(a, b) => [Some(a.clone()), Some(b.clone())],
        };
        let mut parents = vec![Vec::new(); exprs.len()];
        let mut waiting = vec![0; exprs.len()];
        for (i, e) in exprs.iter().enumerate() {
            for q in operands(e).iter().flatten() {
                if let Some(c) = id(q) {
                    parents[c].push(i);
                    waiting[i] += 1;
                }
            }
        }
        // Every atom unknown: a diagram is known only when it is a leaf.
        let step = |e: &Expr<A>, read: &dyn Fn(usize) -> Option<bool>| {
            let value = |q: &Part<A>| match q {
                Part::Expr(x) => read(ids[&x.id]),
                Part::Bdd(b) => match b {
                    Bdd::Leaf(v) => Some(*v),
                    Bdd::Node(_) => None,
                },
            };
            match &e.form {
                Form::Not(a) => value(a).map(|v| !v),
                Form::Or(a, b) => match (value(a), value(b)) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
                Form::And(a, b) => match (value(a), value(b)) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                },
            }
        };
        let mut known: Vec<Option<bool>> = vec![None; exprs.len()];
        let mut ready: Vec<usize> = (0..exprs.len()).filter(|&i| waiting[i] == 0).collect();
        while let Some(i) = ready.pop() {
            let v = step(&exprs[i], &|c| known[c]);
            known[i] = v;
            for &q in &parents[i] {
                waiting[q] -= 1;
                if waiting[q] == 0 {
                    ready.push(q);
                }
            }
        }
        let mut fixed = vec![false; exprs.len()];
        let carry = |i: usize,
                     v: bool,
                     known: &[Option<bool>],
                     fixed: &[bool]|
         -> HashMap<usize, Option<bool>> {
            let mut changed = HashMap::from([(i, Some(v))]);
            let mut work = vec![i];
            while let Some(n) = work.pop() {
                for &q in &parents[n] {
                    if fixed[q] {
                        continue;
                    }
                    let now = step(&exprs[q], &|c| changed.get(&c).copied().unwrap_or(known[c]));
                    if now != changed.get(&q).copied().unwrap_or(known[q]) {
                        changed.insert(q, now);
                        work.push(q);
                    }
                }
            }
            changed
        };
        let mut pins = HashMap::new();
        for i in shared {
            for v in [true, false] {
                let trial = carry(i, !v, &known, &fixed);
                if trial.get(&root).copied().unwrap_or(known[root]) == Some(false) {
                    pins.insert(exprs[i].id, v);
                    fixed[i] = true;
                    for (n, x) in carry(i, v, &known, &fixed) {
                        known[n] = x;
                    }
                    break;
                }
            }
        }
        pins
    }

    #[cfg(test)]
    fn settle_by_scans(&self) -> Part<A> {
        let mut p = self.clone();
        loop {
            // The shared subexpressions, in the order the walk finds them shared, so that the
            // pins taken do not depend on the expressions' ids.
            let mut uses: HashMap<u64, usize> = HashMap::new();
            let mut shared = Vec::new();
            let mut stack = vec![p.clone()];
            while let Some(q) = stack.pop() {
                let Part::Expr(e) = q else { continue };
                let n = uses.entry(e.id).or_insert(0);
                *n += 1;
                if *n == 2 {
                    shared.push(e.id);
                }
                if *n > 1 {
                    continue;
                }
                match &e.form {
                    Form::Not(a) => stack.push(a.clone()),
                    // The first operand is pushed last, so it is walked first.
                    Form::Or(a, b) | Form::And(a, b) => {
                        stack.push(b.clone());
                        stack.push(a.clone());
                    }
                }
            }
            let mut pins = HashMap::new();
            for key in shared {
                for v in [true, false] {
                    pins.insert(key, !v);
                    if p.eval3_pinned(&|_| None, &pins) == Some(false) {
                        pins.insert(key, v);
                        break;
                    }
                    pins.remove(&key);
                }
            }
            if pins.is_empty() {
                return p;
            }
            p = p.substitute_all(&pins);
        }
    }

    /// The part with each expression in `pins` replaced by its value, each rebuilt once.
    fn substitute_all(&self, pins: &HashMap<u64, bool>) -> Part<A> {
        fn go<A: Literal>(
            p: &Part<A>,
            pins: &HashMap<u64, bool>,
            memo: &mut HashMap<u64, Part<A>>,
        ) -> Part<A> {
            let Part::Expr(e) = p else {
                return p.clone();
            };
            let key = e.id;
            if let Some(v) = pins.get(&key) {
                return Part::leaf(*v);
            }
            if let Some(r) = memo.get(&key) {
                return r.clone();
            }
            let r = match &e.form {
                Form::Not(a) => go(a, pins, memo).not(),
                Form::Or(a, b) => go(a, pins, memo).zip(&go(b, pins, memo), Op::Or),
                Form::And(a, b) => go(a, pins, memo).zip(&go(b, pins, memo), Op::And),
            };
            memo.insert(key, r.clone());
            r
        }
        go(self, pins, &mut HashMap::new())
    }

    /// The part with each atom that `fix` decides replaced by its value, each node and
    /// expression rebuilt once.
    pub(super) fn restrict(&self, fix: &impl Fn(&A) -> Option<bool>) -> Part<A> {
        fn go<A: Literal>(
            p: &Part<A>,
            fix: &impl Fn(&A) -> Option<bool>,
            nodes: &mut HashMap<u64, Bdd<A>>,
            memo: &mut HashMap<u64, Part<A>>,
        ) -> Part<A> {
            let e = match p {
                Part::Bdd(b) => return Part::Bdd(b.restrict(fix, nodes)),
                Part::Expr(e) => e,
            };
            if let Some(r) = memo.get(&e.id) {
                return r.clone();
            }
            let r = match &e.form {
                Form::Not(a) => go(a, fix, nodes, memo).not(),
                Form::Or(a, b) => go(a, fix, nodes, memo).zip(&go(b, fix, nodes, memo), Op::Or),
                Form::And(a, b) => go(a, fix, nodes, memo).zip(&go(b, fix, nodes, memo), Op::And),
            };
            memo.insert(e.id, r.clone());
            r
        }
        go(self, fix, &mut HashMap::new(), &mut HashMap::new())
    }

    /// The atoms in every value of the part (`.0`) and those in none (`.1`), among the atoms
    /// in it: for a diagram, those taken or refused on every path to `true`; for an expression,
    /// each atom whose refusal, or whose taking, makes the part `false` by three-valued logic.
    ///
    /// One pass finds, for each expression and diagram, the settings of one atom, every other
    /// atom unknown, that make it `false` and those that make it `true`: an `or` is `false`
    /// under a setting that makes both sides `false`, an `and` under one that makes either side
    /// `false`, and a diagram under an atom taken or refused on every path to `true`. The sets
    /// are persistent and a union adds the smaller to the larger, so the time is `O(n log n)`
    /// in the nodes when the sets stay small, and at most the nodes times the atoms.
    pub(super) fn forced(&self) -> (Vec<A>, Vec<A>) {
        // Settings `(atom, value)`; `None` is every setting.
        type Set<A> = Option<imbl::OrdSet<(A, bool)>>;
        fn union<A: Literal>(x: &Set<A>, y: &Set<A>) -> Set<A> {
            let (x, y) = (x.as_ref()?, y.as_ref()?);
            let (big, small) = if x.len() >= y.len() { (x, y) } else { (y, x) };
            let mut out = big.clone();
            for s in small {
                out.insert(s.clone());
            }
            Some(out)
        }
        fn meet<A: Literal>(x: &Set<A>, y: &Set<A>) -> Set<A> {
            match (x, y) {
                (None, z) | (z, None) => z.clone(),
                (Some(x), Some(y)) => {
                    let (big, small) = if x.len() >= y.len() { (x, y) } else { (y, x) };
                    Some(small.iter().filter(|&s| big.contains(s)).cloned().collect())
                }
            }
        }
        // The settings that make `b` `false`, and those that make it `true`.
        fn of_bdd<A: Literal>(b: &Bdd<A>) -> (Set<A>, Set<A>) {
            let settings = |(taken, refused): (Vec<A>, Vec<A>)| {
                let off = taken.into_iter().map(|a| (a, false));
                Some(off.chain(refused.into_iter().map(|a| (a, true))).collect())
            };
            match b {
                Bdd::Leaf(false) => (None, Some(imbl::OrdSet::new())),
                Bdd::Leaf(true) => (Some(imbl::OrdSet::new()), None),
                Bdd::Node(_) => (settings(b.forced_to(true)), settings(b.forced_to(false))),
            }
        }
        let root = match self {
            Part::Bdd(b) => return b.forced(),
            Part::Expr(e) => e,
        };
        let mut exprs: HashMap<u64, (Set<A>, Set<A>)> = HashMap::new();
        let mut nodes: HashMap<u64, (Set<A>, Set<A>)> = HashMap::new();
        let mut stack = vec![(root.clone(), false)];
        while let Some((e, expanded)) = stack.pop() {
            if exprs.contains_key(&e.id) {
                continue;
            }
            let operands: Vec<&Part<A>> = match &e.form {
                Form::Not(a) => vec![a],
                Form::Or(a, b) | Form::And(a, b) => vec![a, b],
            };
            if !expanded {
                stack.push((e.clone(), true));
                for q in operands {
                    match q {
                        Part::Expr(x) => stack.push((x.clone(), false)),
                        Part::Bdd(b @ Bdd::Node(n)) => {
                            nodes.entry(n.id).or_insert_with(|| of_bdd(b));
                        }
                        Part::Bdd(Bdd::Leaf(_)) => {}
                    }
                }
                continue;
            }
            let get = |q: &Part<A>| match q {
                Part::Expr(x) => exprs[&x.id].clone(),
                Part::Bdd(Bdd::Node(n)) => nodes[&n.id].clone(),
                Part::Bdd(b) => of_bdd(b),
            };
            let sets = match &e.form {
                Form::Not(a) => {
                    let (off, on) = get(a);
                    (on, off)
                }
                Form::Or(a, b) => {
                    let ((fa, ta), (fb, tb)) = (get(a), get(b));
                    (meet(&fa, &fb), union(&ta, &tb))
                }
                Form::And(a, b) => {
                    let ((fa, ta), (fb, tb)) = (get(a), get(b));
                    (union(&fa, &fb), meet(&ta, &tb))
                }
            };
            exprs.insert(e.id, sets);
        }
        let off = &exprs[&root.id].0;
        let makes_false = |a: &A, v: bool| off.as_ref().is_none_or(|s| s.contains(&(a.clone(), v)));
        let (mut taken, mut refused) = (Vec::new(), Vec::new());
        for a in self.distinct_atoms() {
            if makes_false(&a, false) {
                taken.push(a);
            } else if makes_false(&a, true) {
                refused.push(a);
            }
        }
        (taken, refused)
    }

    /// Whether `f` holds of every atom, each node and expression visited once.
    pub(super) fn atoms<'a>(&'a self, f: &mut impl FnMut(&'a A) -> bool) -> bool {
        fn go<'a, A: Literal>(
            p: &'a Part<A>,
            seen: &mut HashSet<u64>,
            f: &mut impl FnMut(&'a A) -> bool,
        ) -> bool {
            let e = match p {
                Part::Bdd(b) => return b.atoms(f),
                Part::Expr(e) => e,
            };
            if !seen.insert(e.id) {
                return true;
            }
            match &e.form {
                Form::Not(a) => go(a, seen, f),
                Form::Or(a, b) | Form::And(a, b) => go(a, seen, f) && go(b, seen, f),
            }
        }
        go(self, &mut HashSet::new(), f)
    }

    /// Each distinct atom once, in the order first met. One atom can stand on several nodes,
    /// and a caller that tests or splits on each atom must meet it once.
    pub(super) fn distinct_atoms(&self) -> Vec<A> {
        let (mut seen, mut atoms) = (BTreeSet::new(), Vec::new());
        self.atoms(&mut |a| {
            if seen.insert(a.clone()) {
                atoms.push(a.clone());
            }
            true
        });
        atoms
    }

    /// The atoms, if the part is their union and nothing else.
    pub(super) fn union_rows(&self) -> Option<Vec<A>> {
        fn go<A: Literal>(p: &Part<A>, seen: &mut HashSet<u64>, out: &mut Vec<A>) -> bool {
            match p {
                Part::Expr(e) => match &e.form {
                    _ if !seen.insert(e.id) => true,
                    Form::Or(a, b) => go(a, seen, out) && go(b, seen, out),
                    _ => false,
                },
                Part::Bdd(b) => {
                    let mut x = b;
                    loop {
                        match x {
                            Bdd::Leaf(b) => return !b,
                            Bdd::Node(n) => {
                                if !matches!(n.hi, Bdd::Leaf(true)) {
                                    return false;
                                }
                                out.push(n.atom.clone());
                                x = &n.lo;
                            }
                        }
                    }
                }
            }
        }
        let mut out = Vec::new();
        go(self, &mut HashSet::new(), &mut out).then_some(out)
    }

    /// The diagram, or the connective of an expression.
    pub(super) fn view(&self) -> Result<&Bdd<A>, &Form<A>> {
        match self {
            Part::Bdd(b) => Ok(b),
            Part::Expr(e) => Err(&e.form),
        }
    }
}

/// Two diagrams, expressions or parts to compare, or two nodes or expressions whose contents
/// compared equal.
enum Step<'a, A: Literal> {
    Bdds(&'a Bdd<A>, &'a Bdd<A>),
    Exprs(&'a Expr<A>, &'a Expr<A>),
    Parts(&'a Part<A>, &'a Part<A>),
    Equal(u64, u64),
}

/// The order of the pair in `first`: by digest, then by atom or connective, then by `hi` and
/// `lo` or by operands, a diagram before an expression. Two nodes or expressions found equal are
/// kept by node id and not compared again, so the cost is one step per pair of nodes compared,
/// not one per path to them, and linear in the size when the two are equal. A loop with its own
/// stack, as a part can be deeper than the call stack.
fn order<A: Literal>(first: Step<'_, A>) -> Ordering {
    let mut equal = HashSet::new();
    let mut steps = vec![first];
    while let Some(step) = steps.pop() {
        let c = match step {
            Step::Equal(a, b) => {
                equal.insert((a, b));
                Ordering::Equal
            }
            Step::Parts(Part::Bdd(a), Part::Bdd(b)) => {
                steps.push(Step::Bdds(a, b));
                Ordering::Equal
            }
            Step::Parts(Part::Expr(a), Part::Expr(b)) => {
                steps.push(Step::Exprs(a, b));
                Ordering::Equal
            }
            Step::Parts(Part::Bdd(_), Part::Expr(_)) => Ordering::Less,
            Step::Parts(Part::Expr(_), Part::Bdd(_)) => Ordering::Greater,
            Step::Bdds(Bdd::Leaf(a), Bdd::Leaf(b)) => a.cmp(b),
            Step::Bdds(Bdd::Leaf(_), Bdd::Node(_)) => Ordering::Less,
            Step::Bdds(Bdd::Node(_), Bdd::Leaf(_)) => Ordering::Greater,
            Step::Bdds(Bdd::Node(a), Bdd::Node(b)) => {
                let key = (a.id, b.id);
                if key.0 == key.1 || equal.contains(&key) {
                    continue;
                }
                let c = a.digest.cmp(&b.digest).then_with(|| a.atom.cmp(&b.atom));
                if c == Ordering::Equal {
                    // `hi` is pushed last, so it is compared first.
                    steps.extend([
                        Step::Equal(key.0, key.1),
                        Step::Bdds(&a.lo, &b.lo),
                        Step::Bdds(&a.hi, &b.hi),
                    ]);
                }
                c
            }
            Step::Exprs(a, b) => {
                let key = (a.id, b.id);
                if key.0 == key.1 || equal.contains(&key) {
                    continue;
                }
                let (x, y) = (a.form.operands(), b.form.operands());
                let c = a.digest.cmp(&b.digest).then_with(|| x.0.cmp(&y.0));
                if c == Ordering::Equal {
                    steps.push(Step::Equal(key.0, key.1));
                    if let (Some(p), Some(q)) = (x.2, y.2) {
                        steps.push(Step::Parts(p, q));
                    }
                    steps.push(Step::Parts(x.1, y.1));
                }
                c
            }
        };
        if c != Ordering::Equal {
            return c;
        }
    }
    Ordering::Equal
}

impl<A: Literal> Form<A> {
    /// The connective's rank in the order (`Not`, `Or`, `And`) and its operands.
    fn operands(&self) -> (u8, &Part<A>, Option<&Part<A>>) {
        match self {
            Form::Not(a) => (0, a, None),
            Form::Or(a, b) => (1, a, Some(b)),
            Form::And(a, b) => (2, a, Some(b)),
        }
    }
}

impl<A: Literal> Ord for Part<A> {
    fn cmp(&self, other: &Part<A>) -> Ordering {
        order(Step::Parts(self, other))
    }
}

impl<A: Literal> PartialOrd for Part<A> {
    fn partial_cmp(&self, other: &Part<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Literal> PartialEq for Part<A> {
    fn eq(&self, other: &Part<A>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<A: Literal> Eq for Part<A> {}

impl<A: Literal> Ord for Expr<A> {
    fn cmp(&self, other: &Expr<A>) -> Ordering {
        order(Step::Exprs(self, other))
    }
}

impl<A: Literal> PartialOrd for Expr<A> {
    fn partial_cmp(&self, other: &Expr<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Literal> PartialEq for Expr<A> {
    fn eq(&self, other: &Expr<A>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<A: Literal> Eq for Expr<A> {}

impl<A: Literal + fmt::Debug> fmt::Debug for Expr<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.form.fmt(f)
    }
}

impl<A: Literal> Ord for Bdd<A> {
    fn cmp(&self, other: &Bdd<A>) -> Ordering {
        order(Step::Bdds(self, other))
    }
}

impl<A: Literal> PartialOrd for Bdd<A> {
    fn partial_cmp(&self, other: &Bdd<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Literal> PartialEq for Bdd<A> {
    fn eq(&self, other: &Bdd<A>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<A: Literal> Eq for Bdd<A> {}

impl<A: Literal + fmt::Debug> fmt::Debug for Bdd<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bdd::Leaf(b) => write!(f, "{b}"),
            Bdd::Node(n) => f
                .debug_tuple("Node")
                .field(&n.atom)
                .field(&n.hi)
                .field(&n.lo)
                .finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Type;
    use crate::value::Value;

    use crate::scaling;

    /// The tuple type of one integer, an atom independent of the others.
    fn atom(i: u64) -> Row {
        Row::new(vec![Type::lit(&Value::Int(i as i64)).unwrap()])
    }

    fn random(seed: &mut u64, depth: u32) -> Part<Row> {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = *seed >> 33;
        if depth == 0 || pick.is_multiple_of(5) {
            return Part::literal(atom(pick % 6));
        }
        let (a, b) = (random(seed, depth - 1), random(seed, depth - 1));
        match pick % 3 {
            0 => a.zip(&b, Op::Or),
            1 => a.zip(&b, Op::And),
            _ => a.not(),
        }
    }

    /// The part built from `random`'s connectives as expressions, so that every form is met;
    /// an operand is at times one built before, kept in `pool`, so that expressions are shared.
    fn random_expr(seed: &mut u64, depth: u32, pool: &mut Vec<Part<Row>>) -> Part<Row> {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = *seed >> 33;
        if !pool.is_empty() && pick % 7 == 3 {
            return pool[(pick / 7) as usize % pool.len()].clone();
        }
        if depth == 0 || pick.is_multiple_of(5) {
            return random(seed, 2);
        }
        let (a, b) = (
            random_expr(seed, depth - 1, pool),
            random_expr(seed, depth - 1, pool),
        );
        let p = Part::expr(match pick % 3 {
            0 => Form::Or(a, b),
            1 => Form::And(a, b),
            _ => Form::Not(a),
        });
        pool.push(p.clone());
        p
    }

    #[test]
    fn three_valued_operations_keep_the_assignments() {
        // Each set of the six atoms is one assignment, and a partial assignment fixes the
        // atoms of `known` to their membership in `fixed`. A three-valued value is the value
        // of every assignment that agrees with it; restricting keeps the value of every
        // assignment agreeing with what it fixes; settling keeps every assignment in the
        // part, and makes it empty only when the part is; an atom forced taken is in every assignment in the part, and one
        // forced refused in none.
        let (mut seed, mut exprs, mut decided, mut forced, mut settled) = (7, 0, 0, 0, 0);
        for k in 0..3000u32 {
            let p = if seed % 2 == 0 {
                random(&mut seed, 6)
            } else {
                random_expr(&mut seed, 5, &mut Vec::new())
            };
            exprs += usize::from(matches!(p, Part::Expr(_)));
            let holds =
                |set: u32| move |t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
            assert!(p.settle() == p.settle_by_scans(), "settling changed");
            let inside: Vec<u32> = (0..64).filter(|&set| p.eval(&holds(set))).collect();
            let (known, fixed) = (k % 64, (k / 64) % 64);
            let fix = |t: &Row| {
                (0..6)
                    .find(|&i| *t == atom(i) && known & (1 << i) != 0)
                    .map(|i| fixed & (1 << i) != 0)
            };
            let agree = |set: u32| (set ^ fixed) & known == 0;
            if let Some(v) = p.eval3(&fix) {
                decided += 1;
                assert!(
                    (0..64)
                        .filter(|&s| agree(s))
                        .all(|s| p.eval(&holds(s)) == v),
                    "{p:?}"
                );
            }
            let r = p.restrict(&fix);
            let t = p.settle();
            settled += usize::from(inside.is_empty() && t.is_leaf() == Some(false));
            for set in 0..64 {
                if agree(set) {
                    assert_eq!(r.eval(&holds(set)), p.eval(&holds(set)), "{p:?} at {set:b}");
                }
                assert!(
                    !p.eval(&holds(set)) || t.eval(&holds(set)),
                    "{p:?} at {set:b}"
                );
            }
            let (taken, refused) = p.forced();
            forced += taken.len() + refused.len();
            // The one pass finds what trying each atom alone by three-valued logic finds.
            let (mut on, mut off) = (Vec::new(), Vec::new());
            for a in p.distinct_atoms() {
                if p.eval3(&|x| (*x == a).then_some(false)) == Some(false) {
                    on.push(a);
                } else if p.eval3(&|x| (*x == a).then_some(true)) == Some(false) {
                    off.push(a);
                }
            }
            assert_eq!((&taken, &refused), (&on, &off), "{p:?}");
            for a in &taken {
                let i = (0..6).find(|&i| *a == atom(i)).unwrap();
                assert!(inside.iter().all(|s| s & (1 << i) != 0), "{p:?} takes {i}");
            }
            for a in &refused {
                let i = (0..6).find(|&i| *a == atom(i)).unwrap();
                assert!(
                    inside.iter().all(|s| s & (1 << i) == 0),
                    "{p:?} refuses {i}"
                );
            }
            // On a diagram every atom in all assignments, or in none, is found.
            if matches!(p, Part::Bdd(_)) && !inside.is_empty() {
                for i in 0..6 {
                    let at = |set: &u32| set & (1 << i) != 0;
                    assert_eq!(
                        taken.contains(&atom(i)),
                        inside.iter().all(at),
                        "{p:?} at {i}"
                    );
                    assert_eq!(
                        refused.contains(&atom(i)),
                        !inside.iter().any(at),
                        "{p:?} at {i}"
                    );
                }
            }
        }
        assert!(
            exprs > 500 && decided > 300 && forced > 1000 && settled > 100,
            "{exprs} {decided} {forced} {settled}"
        );
    }
    #[test]
    fn forced_atoms_of_a_long_chain_scale() {
        // `w ∧ ((x_1 ∧ … ∧ x_m) ∨ z)`: `true` is reached past `z` from every `x_k`. Finding the
        // branches that dominate `true` took the nearest common dominator of `m` branches at
        // growing depths, walking up one step at a time: `O(m²)`.
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn(|| {
                // Built node by node, the atoms in their order: a union or intersection counts
                // the nodes of its result. `w` is the first atom, `z` the last.
                let chain = |m: usize| {
                    let mut xs: Vec<Row> = (0..m as u64 + 2).map(atom).collect();
                    xs.sort();
                    let z = Bdd::literal(xs[m + 1].clone());
                    let mut g = Bdd::node(xs[m].clone(), Bdd::Leaf(true), z.clone());
                    for x in xs[1..m].iter().rev() {
                        g = Bdd::node(x.clone(), g, z.clone());
                    }
                    (
                        Part::Bdd(Bdd::node(xs[0].clone(), g, Bdd::Leaf(false))),
                        xs[0].clone(),
                    )
                };
                let n = 1 << 12;
                let built: BTreeMap<usize, (Part<Row>, Row)> = [n, scaling::FACTOR * n]
                    .into_iter()
                    .map(|m| (m, chain(m)))
                    .collect();
                scaling::check("the forced atoms of a chain, by its length", n, |m| {
                    let (p, w) = &built[&m];
                    assert_eq!(p.forced(), (vec![w.clone()], Vec::new()));
                });
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn comparing_equal_expressions_built_apart_scales() {
        // `x_{k+1} = x_k & !x_k`, built twice: both operands of each level lead to the level
        // below, so comparing operand by operand met the bottom `2^depth` times.
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn(|| {
                let build = |depth: usize| {
                    let mut x = Part::literal(atom(0));
                    for _ in 0..depth {
                        x = Part::expr(Form::And(x.clone(), x.not()));
                    }
                    x
                };
                let n = 1 << 12;
                let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
                    .into_iter()
                    .map(|m| (m, (build(m), build(m))))
                    .collect();
                scaling::check(
                    "comparing equal expressions built apart, by depth",
                    n,
                    |m| {
                        let (a, b) = &built[&m];
                        assert_eq!(a.cmp(b), Ordering::Equal);
                    },
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn comparing_equal_diagrams_built_on_two_threads_scales() {
        // The parity of `m` atoms: two nodes on each atom, each pointing to both nodes on the
        // next. Each thread has its own table of nodes, so the two diagrams share no node, and
        // comparing `hi` then `lo` met the last atom `2^m` times.
        let parity = |m: usize| {
            let mut xs: Vec<Row> = (0..m as u64).map(atom).collect();
            xs.sort();
            let (mut even, mut odd) = (Bdd::Leaf(true), Bdd::Leaf(false));
            for x in xs.iter().rev() {
                (even, odd) = (
                    Bdd::node(x.clone(), odd.clone(), even.clone()),
                    Bdd::node(x.clone(), even.clone(), odd.clone()),
                );
            }
            Part::Bdd(even)
        };
        let n = 1 << 10;
        let on_a_thread = |m: usize| std::thread::spawn(move || parity(m)).join().unwrap();
        let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (on_a_thread(m), on_a_thread(m))))
            .collect();
        scaling::check(
            "comparing equal diagrams built on two threads, by atoms",
            n,
            |m| {
                let (a, b) = &built[&m];
                assert_eq!(a.cmp(b), Ordering::Equal);
            },
        );
    }

    /// A decision list's blocks with each block's literals sorted, and its tail.
    type Blocks = (Vec<(bool, Vec<(Row, bool)>)>, Result<bool, Bdd<Row>>);

    fn sorted(l: super::list::List<Row>) -> Blocks {
        let blocks = l
            .blocks
            .into_iter()
            .map(|(v, mut lits)| {
                lits.sort();
                (v, lits)
            })
            .collect();
        (blocks, l.tail)
    }

    /// The decision list found block by block: the atoms forced on the paths to one leaf,
    /// then the diagram restricted to their literals false, and so on.
    fn list_by_blocks(b: &Bdd<Row>) -> Blocks {
        let mut f = b.clone();
        let mut blocks = Vec::new();
        let mut last: Option<bool> = None;
        loop {
            if let Bdd::Leaf(v) = f {
                return (blocks, Ok(v));
            }
            // The literals of value `!leaf`: those whose opposite every path to `leaf` takes.
            let of = |leaf: bool| {
                let (taken, refused) = f.forced_to(leaf);
                let mut lits: Vec<(Row, bool)> = taken.into_iter().map(|a| (a, false)).collect();
                lits.extend(refused.into_iter().map(|a| (a, true)));
                lits.sort();
                lits
            };
            let (value, lits) = match last {
                None => match of(false) {
                    l if !l.is_empty() => (true, l),
                    _ => (false, of(true)),
                },
                Some(v) => (!v, of(v)),
            };
            if lits.is_empty() {
                return (blocks, Err(f));
            }
            let fix: BTreeMap<Row, bool> = lits.iter().map(|(a, t)| (a.clone(), !t)).collect();
            f = f.restrict(&|a: &Row| fix.get(a).copied(), &mut HashMap::new());
            blocks.push((value, lits));
            last = Some(value);
        }
    }

    fn eval_list(l: &Blocks, holds: &impl Fn(&Row) -> bool) -> bool {
        for (v, lits) in &l.0 {
            if lits.iter().any(|(a, t)| holds(a) == *t) {
                return *v;
            }
        }
        match &l.1 {
            Ok(v) => *v,
            Err(b) => b.eval(holds),
        }
    }

    #[test]
    fn list_matches_the_blocks_found_one_by_one() {
        let mut seed = 11;
        let mut lists = 0;
        for _ in 0..4000 {
            let Part::Bdd(b) = random(&mut seed, 6) else {
                continue;
            };
            let got = sorted(b.list());
            assert_eq!(got, list_by_blocks(&b), "the list of {b:?}");
            // Every diagram the connectives build is a decision list (`Part::zip`).
            assert!(got.1.is_ok(), "{b:?} is a decision list");
            for bits in 0..64u64 {
                let holds = |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(i));
                assert_eq!(eval_list(&got, &holds), b.eval(holds), "{b:?} at {bits}");
            }
            lists += 1;
        }
        assert!(lists > 1000, "{lists} diagrams");
    }

    #[test]
    fn list_of_a_diagram_that_is_no_decision_list_keeps_the_rest() {
        // `x | (y ^ z)`: the block `x`, then the parity of `y` and `z`, which no literal decides.
        let mut xs: Vec<Row> = (0..3).map(atom).collect();
        xs.sort();
        let (y, z) = (Bdd::literal(xs[1].clone()), Bdd::literal(xs[2].clone()));
        let parity = Bdd::node(xs[1].clone(), z.not(), z.clone());
        let f = Bdd::node(xs[0].clone(), Bdd::Leaf(true), parity.clone());
        let l = f.list();
        assert_eq!(l.blocks, vec![(true, vec![(xs[0].clone(), true)])]);
        assert_eq!(l.tail, Err(parity.clone()));
        assert_eq!(sorted(f.list()), list_by_blocks(&f));
        assert_eq!(parity.list().blocks, Vec::new());
        assert_eq!(y.list().blocks, vec![(true, vec![(xs[1].clone(), true)])]);
        assert_eq!(y.list().tail, Ok(false));
        assert_eq!(
            y.not().list().blocks,
            vec![(true, vec![(xs[1].clone(), false)])]
        );
    }

    #[test]
    fn list_of_alternating_literals_scales() {
        // `((x0 | x1) & !x2 | x3) & !x4 …`, each new literal first in the order, so the
        // diagram is one node per atom and every literal is a block of its own: finding the
        // blocks one by one took a pass over the nodes per block.
        let build = |m: usize| {
            let mut xs: Vec<Row> = (0..m as u64).map(atom).collect();
            xs.sort();
            let mut f = Part::literal(xs[m - 1].clone());
            for (i, x) in xs[..m - 1].iter().rev().enumerate() {
                f = match i % 2 {
                    0 => f.zip(&Part::literal(x.clone()), Op::Or),
                    _ => f.zip(&Part::literal(x.clone()).not(), Op::And),
                };
            }
            let Part::Bdd(b) = f else {
                unreachable!("a literal joined to a diagram is a diagram")
            };
            b
        };
        let n = 1 << 12;
        let built: BTreeMap<usize, Bdd<Row>> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, build(m)))
            .collect();
        scaling::check(
            "the decision list of alternating literals, by atoms",
            n,
            |m| {
                let l = built[&m].list();
                assert_eq!(l.blocks.len(), m - 1);
                assert_eq!(l.tail, Ok(false));
            },
        );
    }
}
