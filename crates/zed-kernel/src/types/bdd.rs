//! Boolean functions of the types of one universe (DESIGN.md sec:type_language): the form of the
//! tuple and morphism parts.
//!
//! A part is a decision list (`Bdd`, module `list`) or an expression over parts (`Part::Expr`).
//! A list is a leaf, no value of the universe or every value, or blocks of literals, the first
//! literal that holds giving its block's value. Only literals and chains of them grow a list
//! (`Part::zip`): a chain joined to a list adds its literals one at a time, each in `O(log n)`
//! expected time when the list does not hold its atom, so a chain of `n` literals is built in
//! `O(n log n)`. Lists are in one form, so two lists of one function are one cell; the
//! complement flips the value of the first block. An exclusive or of literals, or of two others,
//! is kept in its one form, one node for one set of atoms (module `xor`). Any other union or
//! intersection keeps the expression, built in constant time.
//!
//! Cells and expressions keep a hash of their contents made from their children's, and two are
//! ordered by it first, so a comparison reads their contents only when the hashes are equal,
//! and reads each pair of cells, sets or expressions at most once (`order` in module `types`).
//!
//! A part is decided (module `empty`) by three-valued operations: it is evaluated with some
//! atoms known (`Part::eval3`) and restricted to them (`Part::restrict`), each in time linear in
//! its literals; asked which atoms every value takes or refuses (`Part::forced`), in `O(n log n)`
//! on a list and one evaluation per atom on an expression; and settled on its shared
//! subexpressions (`Part::settle`), one evaluation per shared subexpression in each round. The
//! last two are above the rule of low complexity, an open item (DESIGN.md L1.23). Listing values
//! takes one pass over a list's first nodes, as a diagram would have them (`Bdd::reaching`).

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering as Atomic};
use std::sync::{Arc, Mutex, Weak};

use crate::frames::{Deep, Stack};

use super::mix;

mod set;

pub(crate) use super::hash::KeyHasher;
use list::Cell;
use set::{Key, NEXT, Set};

/// A connective of two operands.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Op {
    Or,
    And,
}

#[derive(Clone)]
pub(super) enum Bdd<A: Literal> {
    Leaf(bool),
    /// A decision list (module `list`): its first cell and the value of its first block.
    List(Arc<Cell<A>>, bool),
}

/// A node's id, atom, `hi` and `lo`, as [`Bdd::branch`] shows a list.
pub(super) type NodeView<'a, A> = (u64, &'a A, &'a Bdd<A>, &'a Bdd<A>);

/// The live sets, cells and exclusive ors of a thread, each held weakly: a node leaves its table
/// when it is dropped, so the tables hold what the thread's types hold and no more (step
/// TABLE-life). A node stays in its table while it lives, so a live node is the one node of its
/// contents and keeps its id.
pub(super) struct Tables<A: Literal> {
    sets: set::SetTable<A>,
    cells: list::CellTable<A>,
    xors: xor::XorTable<A>,
}

impl<A: Literal> Tables<A> {
    pub(super) const fn new() -> Tables<A> {
        Tables {
            sets: std::collections::HashMap::with_hasher(std::hash::BuildHasherDefault::new()),
            cells: BTreeMap::new(),
            xors: BTreeMap::new(),
        }
    }
}

/// What a part, cell or set holds that is dropped in the thread's loop of type parts (module
/// `deep`).
#[expect(dead_code, reason = "a part is held only to be dropped")]
pub(super) enum Owned<A: Literal> {
    Part(Part<A>),
    Set(Arc<Set<A>>),
    Cell(Arc<Cell<A>>),
}

/// The atoms of a universe, each kind with its thread's tables of sets and cells.
pub(super) trait Literal: Ord + Clone + 'static {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R;
    /// Runs `f` on the thread's tables to remove a dropped node's entry. While the thread is
    /// ending and its tables are gone, or while they are borrowed, nothing is done: the entry is
    /// then a weak handle that no lookup takes, replaced when its key is next made.
    fn untable(f: impl FnOnce(&mut Tables<Self>));
    /// A hash of the atom, equal for equal atoms.
    fn digest(&self) -> u64;
    /// Drops a part, cell or set in the thread's loop of type parts (module `deep`).
    fn free(part: Owned<Self>);
    /// The order of two lists, cells, sets, expressions or parts of the universe (`order` in
    /// module `types`).
    fn order(w: Walk<'_, Self>) -> Ordering;
}

/// The atoms of a universe are the atoms of its sets (module `set`), whose table is one of the
/// thread's tables.
impl<A: Literal> set::Atom for A {
    fn sets<R>(f: impl FnOnce(&mut set::SetTable<A>) -> R) -> R {
        A::table(|t| f(&mut t.sets))
    }
    fn unsets(f: impl FnOnce(&mut set::SetTable<A>)) {
        A::untable(|t| f(&mut t.sets));
    }
    fn digest(&self) -> u64 {
        Literal::digest(self)
    }
    fn free_set(set: Arc<Set<A>>) {
        A::free(Owned::Set(set));
    }
}
/// An expression leaves its thread's table of exclusive ors, if it is in it, and its operands
/// and complement are freed in a loop, as a cell's next cell is.
impl<A: Literal> Drop for Expr<A> {
    fn drop(&mut self) {
        if let Some((pair, constant)) = &self.xor
            && let Some(s) = &pair.atoms
        {
            let key = (s.id, *constant);
            A::untable(|t| {
                if t.xors
                    .get(&key)
                    .is_some_and(|w| std::ptr::eq(w.as_ptr(), self))
                {
                    t.xors.remove(&key);
                }
            });
        }
        free_form(&mut self.form);
        if let Some(Source::Form(mut f)) = self.source.take() {
            free_form(&mut f);
        }
        if let Some(c) = self.complement.take() {
            A::free(Owned::Part(c));
        }
        // The pair frees its parts in the loop when it is dropped.
        self.xor.take();
    }
}

/// The operands of `form` freed in a loop (module `deep`), leaves left in their place.
fn free_form<A: Literal>(form: &mut Form<A>) {
    let (p, q) = match form {
        Form::Not(p) => (p, None),
        Form::Or(p, q) | Form::And(p, q) => (p, Some(q)),
    };
    for part in std::iter::once(p).chain(q) {
        if part.is_leaf().is_none() {
            A::free(Owned::Part(std::mem::replace(part, Part::leaf(false))));
        }
    }
}

impl<A: Literal> Bdd<A> {
    pub(super) fn literal(a: A) -> Bdd<A> {
        Bdd::literal_key((a, true))
    }

    /// The id of the list, unique among the nodes of the process; a leaf's is its value.
    pub(super) fn id(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => u64::from(*b),
            Bdd::List(c, v) => c.id + u64::from(*v),
        }
    }

    pub(super) fn digest(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => mix(7, u64::from(*b)),
            Bdd::List(c, v) => mix(mix(18, c.digest), u64::from(*v)),
        }
    }

    /// `self op other` when one of the two is a chain under `op`: the chain's literals joined
    /// to the other one at a time, the shorter chain's when both are; `None` when neither is.
    // Complexity tradeoff: when both are chains, joining the shorter to the longer costs
    // `O(k log n)` for the shorter's `k` literals; either order gives the one list.
    fn zip_chain(&self, other: &Bdd<A>, op: Op) -> Option<Bdd<A>> {
        // Only the chain joined is listed: listing the other too would cost its length at each
        // literal added to a long chain.
        let (base, joined) = match (self.chain_len(op), other.chain_len(op)) {
            (Some(x), Some(y)) if x <= y => (other, self),
            (_, Some(_)) => (self, other),
            (Some(_), None) => (other, self),
            (None, None) => return None,
        };
        let lits = joined.chain_keys(op).expect("a chain has its literals");
        Some(lits.into_iter().fold(base.clone(), |f, k| match op {
            Op::Or => f.or_literal(k),
            Op::And => f.and_literal(k),
        }))
    }

    /// The literals of a chain under `op`, of any length; `None` for any other list.
    fn chain_keys(&self, op: Op) -> Option<Vec<Key<A>>> {
        if let Some((a, taken)) = self.as_literal() {
            return Some(vec![(a.clone(), taken)]);
        }
        if let Bdd::Leaf(_) = self {
            return self.is_chain(op).then(Vec::new);
        }
        let lits = self.chain(op)?;
        Some(lits.into_iter().map(|(a, t)| (a.clone(), t)).collect())
    }

    /// The number of literals of a chain under `op`, of any length, in constant time; `None`
    /// for any other list.
    fn chain_len(&self, op: Op) -> Option<usize> {
        if self.is_literal() {
            return Some(1);
        }
        match self {
            Bdd::Leaf(_) => self.is_chain(op).then_some(0),
            Bdd::List(c, _) => self.is_chain(op).then(|| set::len(Some(&c.block))),
        }
    }

    /// Whether the list is one atom or its complement.
    fn is_literal(&self) -> bool {
        self.as_literal().is_some()
    }

    /// Whether the list is a chain under `op`: a meet of literals under `And`, a union of them
    /// under `Or`. A union of literals is one block of value `true`, a meet one of value
    /// `false`, the meet of the complements of its literals; a literal is both.
    fn is_chain(&self, op: Op) -> bool {
        let out = op == Op::Or;
        match self {
            Bdd::Leaf(v) => *v != out,
            Bdd::List(c, v) => c.len == 1 && (*v == out || self.is_literal()),
        }
    }

    /// The literals of a chain under `op` of two or more literals, each an atom and whether
    /// the chain takes it; `None` for any other list.
    fn chain(&self, op: Op) -> Option<Vec<(&A, bool)>> {
        let Bdd::List(c, _) = self else { return None };
        if !self.is_long_chain(op) {
            return None;
        }
        let out = op == Op::Or;
        Some(
            set::iter(Some(&c.block))
                .map(|(a, p)| (a, *p == out))
                .collect(),
        )
    }

    /// Whether the list is a chain under `op` of two or more literals.
    fn is_long_chain(&self, op: Op) -> bool {
        matches!(self, Bdd::List(..)) && !self.is_literal() && self.is_chain(op)
    }

    /// Whether the chain under `op` of two or more literals takes `atom` (`Some(true)`),
    /// refuses it (`Some(false)`), or has no literal on it, in `O(log k)` for its `k` literals.
    fn chain_takes(&self, op: Op, atom: &A) -> Option<bool> {
        let Bdd::List(c, _) = self else { return None };
        set::get(Some(&c.block), atom).map(|p| p == (op == Op::Or))
    }

    /// The chain under `op` without its literal on `atom`, which it takes when `taken`, in
    /// `O(log k)` for its `k` literals: the chain restricted on its one block.
    fn chain_without(&self, op: Op, atom: &A, taken: bool) -> Bdd<A> {
        let Bdd::List(c, v) = self else {
            return self.clone();
        };
        debug_assert!(c.len == 1, "a chain is one block");
        // The literal is left out by fixing it to the value `op` passes over.
        let value = taken != (op == Op::Or);
        match set::get(Some(&c.block), atom) {
            None => self.clone(),
            Some(p) if p == value => Bdd::Leaf(*v),
            Some(p) => {
                let block = set::remove(&c.block, &(atom.clone(), p));
                Bdd::assemble(vec![(*v, block)], &Bdd::Leaf(!*v))
            }
        }
    }

    /// The literal on `atom`, taken or refused.
    fn literal_of(atom: &A, taken: bool) -> Bdd<A> {
        Bdd::literal_key((atom.clone(), taken))
    }

    /// The atom of a list that is one literal, and whether the literal takes it.
    fn as_literal(&self) -> Option<(&A, bool)> {
        match self {
            Bdd::List(c, v) if c.len == 1 => set::single_key(&c.block).map(|(a, p)| (a, *p == *v)),
            _ => None,
        }
    }

    /// The complement: the value of the first block flipped, and a literal's atom refused
    /// rather than taken, so that a single literal keeps the value `true`.
    pub(super) fn not(&self) -> Bdd<A> {
        match self {
            Bdd::Leaf(b) => Bdd::Leaf(!b),
            Bdd::List(c, v) => match self.as_literal() {
                Some((a, taken)) => Bdd::literal_of(a, !taken),
                None => Bdd::List(c.clone(), !v),
            },
        }
    }

    /// The atoms every value takes, and those every value refuses: [`Bdd::forced_to`] `true`.
    fn forced(&self) -> (Vec<A>, Vec<A>) {
        self.forced_to(true)
    }

    /// The atoms taken, and those refused, by every value of the list that is `leaf`, each in
    /// order. A literal is forced on the values `true` only when it is the list, or, when the
    /// first block has the value `false`, refused by every literal of that block: a later block
    /// of the one form, or the default, leaves each of its atoms free.
    fn forced_to(&self, leaf: bool) -> (Vec<A>, Vec<A>) {
        let f = if leaf { self.clone() } else { self.not() };
        let (mut taken, mut refused) = (Vec::new(), Vec::new());
        if let Some((a, t)) = f.as_literal() {
            match t {
                true => taken.push(a.clone()),
                false => refused.push(a.clone()),
            }
        } else if let (Bdd::List(_, false), Some(first)) = (&f, f.first_block()) {
            for (a, p) in set::iter(Some(first)) {
                match p {
                    true => refused.push(a.clone()),
                    false => taken.push(a.clone()),
                }
            }
        }
        (taken, refused)
    }

    /// The node's id, atom, `hi` and `lo`, or the leaf's value. A list is shown as a diagram
    /// whose nodes are its literals in turn ([`Bdd::view`]); a node's id is its list's.
    pub(super) fn branch(&self) -> Result<NodeView<'_, A>, bool> {
        match self {
            Bdd::Leaf(b) => Err(*b),
            Bdd::List(..) => {
                let (a, hi, lo) = self.view().expect("a list has a first node");
                Ok((self.id(), a, hi, lo))
            }
        }
    }

    /// Whether `f` holds of each node's atom and state, for the nodes ([`Bdd::branch`]) from
    /// whose `hi` a chain of `lo` edges alone reaches `true`: the nodes that are the last `hi`
    /// taken on some path to `true`. The root has the state `start`; an edge to a node's `hi`
    /// passes on `take` of its state and its atom, an edge to its `lo` its state; a node's state
    /// is `join` of the states of the edges into it. Each node is visited once, after every node
    /// with an edge into it, so the time is linear in the nodes however many paths there are.
    ///
    /// The nodes of a list follow the literals of each block in the order of their atoms, so
    /// which nodes are the last `hi` of a path depends on the order of the atoms only within a
    /// block: a meet `x & y` has the one path `x, y` in either order, and only its last node is
    /// passed to `f`, so a user that reads a node's state as the atoms its paths took sees the
    /// meet in both orders (step L1.37a: the atom order follows digests, and truncated digests
    /// order atoms differently).
    pub(super) fn reaching<S>(
        &self,
        start: S,
        take: impl Fn(&S, &A) -> S,
        join: impl Fn(&S, &S) -> S,
        mut f: impl FnMut(&A, &S) -> bool,
    ) -> bool {
        if let Bdd::Leaf(_) = self {
            return true;
        }
        fn node<A: Literal>(b: &Bdd<A>) -> NodeView<'_, A> {
            b.branch().expect("only a list is a node")
        }
        // Nodes in reverse postorder of a depth-first walk: each after those above it.
        let mut order: Vec<&Bdd<A>> = Vec::new();
        let mut seen = HashSet::new();
        let mut stack: Vec<(&Bdd<A>, bool)> = vec![(self, false)];
        while let Some((n, below)) = stack.pop() {
            if below {
                order.push(n);
                continue;
            }
            if !seen.insert(n.id()) {
                continue;
            }
            stack.push((n, true));
            let (_, _, hi, lo) = node(n);
            for c in [lo, hi] {
                if let Bdd::List(..) = c
                    && !seen.contains(&c.id())
                {
                    stack.push((c, false));
                }
            }
        }
        // Whether a chain of `lo` edges from each node reaches `true`, children first.
        let mut lo_true: HashMap<u64, bool> = HashMap::with_capacity(order.len());
        let chain = |b: &Bdd<A>, lo_true: &HashMap<u64, bool>| match b {
            Bdd::Leaf(v) => *v,
            Bdd::List(..) => *lo_true
                .get(&b.id())
                .expect("a node is ordered after its children"),
        };
        for n in &order {
            let t = chain(node(n).3, &lo_true);
            lo_true.insert(n.id(), t);
        }
        let mut state: HashMap<u64, S> = HashMap::from([(self.id(), start)]);
        for n in order.into_iter().rev() {
            let (id, atom, hi, lo) = node(n);
            let here = state
                .remove(&id)
                .expect("a node is reached before it is visited");
            if chain(hi, &lo_true) && !f(atom, &here) {
                return false;
            }
            for (child, s) in [(hi, take(&here, atom)), (lo, here)] {
                if let Bdd::List(..) = child {
                    let s = match state.remove(&child.id()) {
                        Some(t) => join(&t, &s),
                        None => s,
                    };
                    state.insert(child.id(), s);
                }
            }
        }
        true
    }

    /// The value of the first block with a literal that `holds` makes true, or the default.
    pub(super) fn eval(&self, holds: impl Fn(&A) -> bool) -> bool {
        if let Bdd::Leaf(v) = self {
            return *v;
        }
        let mut last = true;
        for (v, c) in self.cells() {
            if set::iter(Some(&c.block)).any(|(a, p)| holds(a) == *p) {
                return v;
            }
            last = v;
        }
        !last
    }

    /// The list's value on every value of the set that `holds` gives (`Bdd::eval3`'s use in
    /// [`Part::eval3`]): each block with a literal `holds` leaves unknown may give its value,
    /// and the first block with a literal it makes true ends the walk; the list is known when
    /// one value is left. The atoms of a list are distinct, so each value left is reached.
    fn eval3(&self, holds: &impl Fn(&A) -> Option<bool>) -> Option<bool> {
        if let Bdd::Leaf(v) = self {
            return Some(*v);
        }
        let mut values = [false; 2];
        let mut last = true;
        'blocks: for (v, c) in self.cells() {
            for (a, p) in set::iter(Some(&c.block)) {
                match holds(a) {
                    Some(h) if h == *p => {
                        values[usize::from(v)] = true;
                        return (!values[usize::from(!v)]).then_some(v);
                    }
                    Some(_) => {}
                    None => {
                        values[usize::from(v)] = true;
                        if values == [true; 2] {
                            break 'blocks;
                        }
                    }
                }
            }
            last = v;
        }
        values[usize::from(!last)] = true;
        match values {
            [true, false] => Some(false),
            [false, true] => Some(true),
            _ => None,
        }
    }
}

/// A tuple part of one length, or the morphism part: a decision list, or, when a connective's
/// result is not one, the connective applied to its operands, or an exclusive or of atoms in its
/// one form (module `xor`).
#[derive(Clone)]
pub(super) enum Part<A: Literal> {
    Bdd(Bdd<A>),
    Expr(Arc<Expr<A>>),
}

pub(super) struct Expr<A: Literal> {
    /// The node's id, unique among the nodes of the process.
    pub(super) id: u64,
    pub(super) digest: u64,
    pub(super) form: Form<A>,
    /// The complement, made once and held, so that a chain of choices is negated in steps, not
    /// walked. It is not set when the complement holds the expression (`!e` made as `Not(e)`,
    /// or the complement made first and holding it); `back` then finds it.
    complement: std::sync::OnceLock<Part<A>>,
    /// The complement, not held, when it was made from the expression or holds it: an
    /// expression and its complement never hold each other, so they are freed when no one
    /// holds them (step TABLE-life). When the complement held here is freed, the next one made
    /// replaces it.
    back: Mutex<Weak<Expr<A>>>,
    /// The expression this one was made the complement of, as it was written, when this one does
    /// not hold it: its form, or that it was `Not` of this one. A source freed while this one
    /// lives is made again from it with the same form and digest, so the complement of a part
    /// does not depend on what was freed before (batch and single-file checking agree).
    source: std::sync::OnceLock<Source<A>>,
    /// Whether the complement is `Not` of the expression: no choice was found in it, so a
    /// complement made again skips the search.
    plain: AtomicBool,
    /// The two halves the expression was made from as an exclusive or, and its constant
    /// (module `xor`), if it was; its complement is made again from them.
    xor: Option<(Arc<xor::Pair<A>>, bool)>,
}

impl<A: Literal> Expr<A> {
    /// The complement as kept: held, or made earlier and still held by someone.
    fn known(&self) -> Option<Part<A>> {
        self.complement.get().cloned().or_else(|| {
            let back = self
                .back
                .lock()
                .expect("no thread panics holding a complement");
            back.upgrade().map(Part::Expr)
        })
    }

    /// Keeps `m` as the complement without holding it.
    fn set_back(&self, m: &Arc<Expr<A>>) {
        *self
            .back
            .lock()
            .expect("no thread panics holding a complement") = Arc::downgrade(m);
    }

    /// Whether the expression holds `e` as its operand or its complement.
    fn holds(&self, e: &Arc<Expr<A>>) -> bool {
        let is_e = |p: &Part<A>| matches!(p, Part::Expr(x) if Arc::ptr_eq(x, e));
        matches!(&self.form, Form::Not(q) if is_e(q)) || self.complement.get().is_some_and(is_e)
    }

    /// Keeps `n`, made as the complement of the expression, as its complement:
    /// held when it does not hold the expression, which is then kept as its complement without
    /// being held; not held otherwise. Returns the complement kept, which another thread may
    /// have set first.
    fn link(self: &Arc<Self>, n: Part<A>) -> Part<A> {
        match &n {
            Part::Expr(m) if m.holds(self) => self.set_back(m),
            _ => {
                if let Part::Expr(m) = &n {
                    m.set_back(self);
                }
                let _ = self.complement.set(n.clone());
            }
        }
        self.known().unwrap_or(n)
    }
}

/// What an expression was made the complement of (`Expr::source`).
enum Source<A: Literal> {
    /// `Not` of the expression.
    NotOfThis,
    /// An expression of this form.
    Form(Form<A>),
}

#[derive(Clone)]
pub(super) enum Form<A: Literal> {
    Not(Part<A>),
    Or(Part<A>, Part<A>),
    And(Part<A>, Part<A>),
}

impl<A: Literal> Form<A> {
    /// Whether `e` is an operand of the form.
    fn holds(&self, e: &Arc<Expr<A>>) -> bool {
        let is_e = |p: &Part<A>| matches!(p, Part::Expr(x) if Arc::ptr_eq(x, e));
        match self {
            Form::Not(p) => is_e(p),
            Form::Or(p, q) | Form::And(p, q) => is_e(p) || is_e(q),
        }
    }
}

/// The operands of a part under a connective ([`Part::operands`]).
enum Operands<'a, A: Literal> {
    /// An expression's two operands.
    Two(&'a Part<A>, &'a Part<A>),
    /// A chain of two or more literals, looked up rather than listed.
    Chain(&'a Bdd<A>),
}

impl<A: Literal> Part<A> {
    /// The hash of the part's contents.
    pub(super) fn digest(&self) -> u64 {
        match self {
            Part::Bdd(b) => b.digest(),
            Part::Expr(e) => e.digest,
        }
    }

    /// The id of the part's node, unique among the nodes of the process; a leaf's is its value.
    pub(super) fn id(&self) -> u64 {
        match self {
            Part::Bdd(b) => b.id(),
            Part::Expr(e) => e.id,
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
        Part::expr_xor(form, None)
    }

    /// The expression of `form`, the one form of the exclusive or `xor` when given.
    fn expr_xor(form: Form<A>, xor: Option<(Arc<xor::Pair<A>>, bool)>) -> Part<A> {
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
            back: Mutex::new(Weak::new()),
            source: std::sync::OnceLock::new(),
            plain: AtomicBool::new(false),
            xor,
        }))
    }

    pub(super) fn not(&self) -> Part<A> {
        match self {
            Part::Bdd(b) => Part::Bdd(b.not()),
            Part::Expr(e) => match e.known() {
                Some(n) => n,
                None => Connect::run(|k| k.not(self)),
            },
        }
    }

    pub(super) fn zip(&self, other: &Part<A>, op: Op) -> Part<A> {
        match Part::zip_at_once(self, other, op) {
            Some(r) => r,
            None => Connect::run(|k| k.zip(self, other, op)),
        }
    }

    /// `a op b` when a leaf or equal operands give it at once.
    fn zip_at_once(a: &Part<A>, b: &Part<A>, op: Op) -> Option<Part<A>> {
        // A leaf that absorbs is the result; a leaf that does not leaves the other operand.
        let absorbs = op == Op::Or;
        match (a.is_leaf(), b.is_leaf()) {
            (Some(x), _) if x == absorbs => Some(a.clone()),
            (_, Some(x)) if x == absorbs => Some(b.clone()),
            (Some(_), _) => Some(b.clone()),
            (_, Some(_)) => Some(a.clone()),
            _ => (a == b).then(|| a.clone()),
        }
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
            (Part::Bdd(b), _) => b.is_long_chain(op).then_some(Operands::Chain(b)),
        }
    }
}

/// The complement and the union or intersection of parts. They are a recursion through the
/// choices they find ([`Connect::choice`]), as deep as the parts are nested, so each call of
/// [`Connect::not`] or [`Connect::zip`] that is not answered at once runs on a frame of its own
/// (module `frames`), and a part nested to any depth is negated and combined on a small stack.
/// The frames run in the order of the plain recursion, so the parts made, and the ids they take,
/// are those it made.
// Complexity tradeoff: a frame on the heap per call not answered at once costs a constant
// factor over the plain recursion (measured in a debug build on chains of choices 500 deep:
// `zip` 1.4 times, `not` 1.3 to 1.9 times), for any depth on a small stack; the order of the
// work is unchanged.
struct Connect<'m> {
    stack: Stack<'m>,
}

impl Connect<'_> {
    /// Runs `root` and the calls it makes on a stack of their own.
    fn run<V: Unpin>(root: impl for<'m> FnOnce(&'m Connect<'m>) -> Deep<'m, V>) -> V {
        let k = Connect {
            stack: Stack::default(),
        };
        k.stack.run(root(&k))
    }
}

impl<'m> Connect<'m> {
    fn not<A: Literal>(&'m self, p: &Part<A>) -> Deep<'m, Part<A>> {
        match p {
            Part::Bdd(b) => Stack::ready(Part::Bdd(b.not())),
            Part::Expr(e) => match e.known() {
                Some(n) => Stack::ready(n),
                None => {
                    let p = p.clone();
                    self.stack.call(move || self.negate(p))
                }
            },
        }
    }

    /// The complement of an expression, made once and kept with it, and the expression kept as
    /// the complement's, so that a chain of choices is negated in steps, not walked.
    async fn negate<A: Literal>(&'m self, p: Part<A>) -> Part<A> {
        let Part::Expr(e) = &p else {
            unreachable!("only an expression keeps its complement")
        };
        let n = if let Some(source) = e.source.get() {
            // The expression this one was made the complement of, freed: made again as written.
            match source {
                Source::NotOfThis => Part::expr(Form::Not(p.clone())),
                Source::Form(f) => Part::expr(f.clone()),
            }
        } else if let Some((pair, constant)) = &e.xor {
            // An exclusive or's complement is made again as it was first made beside it, so
            // that the two are equal as built.
            xor::mate(pair, !constant)
        } else if let Form::Not(q) = &e.form {
            if let Part::Expr(m) = q {
                let _ = m.source.set(Source::NotOfThis);
            }
            q.clone()
        } else if !e.plain.load(Atomic::Relaxed)
            && let Some((c, x, y)) = self.choice(&p).await
        {
            let x = self.not(&x).await;
            let y = self.not(&y).await;
            let n = self.choose(&c, &x, &y).await;
            if let Part::Expr(m) = &n
                && !m.holds(e)
                && !e.form.holds(m)
            {
                let _ = m.source.set(Source::Form(e.form.clone()));
            }
            n
        } else {
            e.plain.store(true, Atomic::Relaxed);
            Part::expr(Form::Not(p.clone()))
        };
        e.link(n)
    }

    fn zip<A: Literal>(&'m self, a: &Part<A>, b: &Part<A>, op: Op) -> Deep<'m, Part<A>> {
        match Part::zip_at_once(a, b, op) {
            Some(r) => Stack::ready(r),
            None => {
                let (a, b) = (a.clone(), b.clone());
                self.stack.call(move || self.zipped(a, b, op))
            }
        }
    }

    /// `a op b` of operands neither a leaf nor equal.
    async fn zipped<A: Literal>(&'m self, a: Part<A>, b: Part<A>, op: Op) -> Part<A> {
        if self.same_as_not(&a, &b).await {
            return Part::leaf(op == Op::Or);
        }
        // Only chains grow a list, so each list is a decision list, kept as its blocks: a
        // chain's literals are joined to the other operand one at a time (module `list`).
        if let (Part::Bdd(x), Part::Bdd(y)) = (&a, &b)
            && let Some(z) = x.zip_chain(y, op)
        {
            return Part::Bdd(z);
        }
        // Complexity tradeoff: an exclusive or of two others is taken to its one form (module
        // `xor`), in `O(k log n)` for the `k` atoms of the smaller and the `n` of the larger,
        // rather than kept as the expression made in constant time, so that one set of atoms
        // built in any order is one node; parity built a literal at a time stays `O(n log n)`.
        if let Some(x) = xor::xor_of(&a, &b, op) {
            return x;
        }
        // Choices on one condition meet branch by branch.
        let (l, r) = (self.choice(&a).await, self.choice(&b).await);
        if let (Some((c, x, y)), Some((d, u, v))) = (l, r)
            && c == d
        {
            let p = self.zip(&x, &u, op).await;
            let q = self.zip(&y, &v, op).await;
            return self.choose(&c, &p, &q).await;
        }
        // `c&x | !c&y` and `(!c|x) & (c|y)` are one choice.
        if let Some((c, x, y)) = self.choice_of(&a, &b, op).await {
            return self.choose(&c, &x, &y).await;
        }
        let (a, b) = if a.before(&b) { (a, b) } else { (b, a) };
        Part::expr(match op {
            Op::Or => Form::Or(a, b),
            Op::And => Form::And(a, b),
        })
    }

    /// Whether `a` is the complement of `b`, as built.
    async fn same_as_not<A: Literal>(&'m self, a: &Part<A>, b: &Part<A>) -> bool {
        match (a, b) {
            (Part::Bdd(x), Part::Bdd(y)) => x.is_literal() && x.not() == *y,
            (Part::Expr(e), _) => e.known().is_some_and(|c| c == *b) || self.not(a).await == *b,
            _ => self.not(b).await == *a,
        }
    }

    /// The condition of a choice, of `c` and `!c` the one [`Part::before`] puts first.
    async fn condition<A: Literal>(&'m self, c: &Part<A>) -> (Part<A>, bool) {
        let n = self.not(c).await;
        if c.before(&n) {
            (c.clone(), true)
        } else {
            (n, false)
        }
    }

    /// The choice `c&x | !c&y`, in the one form each choice has.
    async fn choose<A: Literal>(&'m self, c: &Part<A>, x: &Part<A>, y: &Part<A>) -> Part<A> {
        if x == y {
            return x.clone();
        }
        if let Some(z) = xor::xor_choice(c, x, y) {
            return z;
        }
        let (c, same) = self.condition(c).await;
        let (x, y) = if same { (x, y) } else { (y, x) };
        match (x.is_leaf(), y.is_leaf()) {
            (Some(false), Some(false)) => return Part::leaf(false),
            (Some(true), Some(false)) => return c,
            (Some(false), Some(true)) => return self.not(&c).await,
            _ => {}
        }
        let first = self.zip(&c, x, Op::And).await;
        let not_c = self.not(&c).await;
        let parts = [first, self.zip(&not_c, y, Op::And).await];
        let [a, b] = if parts[0].before(&parts[1]) {
            parts
        } else {
            let [p, q] = parts;
            [q, p]
        };
        Part::expr(Form::Or(a, b))
    }

    /// `(c, x, y)` when `a op b` is a choice: under `Or`, `c&x | !c&y`; under `And`,
    /// `(!c|x) & (c|y)`. The condition `c` is an operand of `a`'s expression, or a literal of
    /// its chain, whose complement is one of `b`'s. When two or more conditions fit, which one
    /// a search finds first depends on the order of the atoms, so there is then no choice, and
    /// the parts built are the same in every order of the atoms (step BDD-atom-order).
    async fn choice_of<A: Literal>(
        &'m self,
        a: &Part<A>,
        b: &Part<A>,
        op: Op,
    ) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let inner = if op == Op::Or { Op::And } else { Op::Or };
        let (l, r) = (a.operands(inner)?, b.operands(inner)?);
        // The literal of the chain `d` that `n` is, looked up in `O(log k)`.
        let within = |n: &Part<A>, d: &Bdd<A>| match n {
            Part::Bdd(n) => n
                .as_literal()
                .filter(|(atom, taken)| d.chain_takes(inner, atom) == Some(*taken))
                .map(|(atom, taken)| (atom.clone(), taken)),
            Part::Expr(_) => None,
        };
        let mut found = Vec::new();
        match (&l, &r) {
            (Operands::Two(p, q), Operands::Two(s, t)) => {
                for (c, x) in [(p, q), (q, p)] {
                    for (n, y) in [(s, t), (t, s)] {
                        if self.same_as_not(c, n).await {
                            found.push(((*c).clone(), (*x).clone(), (*y).clone()));
                        }
                    }
                }
            }
            (Operands::Two(p, q), Operands::Chain(d)) => {
                for (c, x) in [(p, q), (q, p)] {
                    if let Some((atom, taken)) = within(&self.not(c).await, d) {
                        let y = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push(((*c).clone(), (*x).clone(), y));
                    }
                }
            }
            (Operands::Chain(d), Operands::Two(s, t)) => {
                for (n, y) in [(s, t), (t, s)] {
                    if let Some((atom, taken)) = within(&self.not(n).await, d) {
                        let c = Part::Bdd(Bdd::literal_of(&atom, taken));
                        let x = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push((c, x, (*y).clone()));
                    }
                }
            }
            (Operands::Chain(d), Operands::Chain(e)) => {
                // The atoms on which the chains' literals are complements, found by looking the
                // shorter chain's literals up in the longer, so that the time is `O(k log n)`
                // for `k` the shorter's literals and `n` the longer's; the rests are built only
                // for a single atom.
                let short_is_d = d.chain_len(inner) <= e.chain_len(inner);
                let (short, long) = if short_is_d { (d, e) } else { (e, d) };
                let lits = short
                    .chain(inner)
                    .expect("an operand chain has its literals");
                let mut both = (lits.into_iter())
                    .filter(|(atom, taken)| long.chain_takes(inner, atom) == Some(!*taken));
                let (Some((atom, taken)), None) = (both.next(), both.next()) else {
                    return None;
                };
                // Whether `d` takes the atom.
                let taken = if short_is_d { taken } else { !taken };
                found.push((
                    Part::Bdd(Bdd::literal_of(atom, taken)),
                    Part::Bdd(d.chain_without(inner, atom, taken)),
                    Part::Bdd(e.chain_without(inner, atom, !taken)),
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

    /// The choice `p` is in its one form. Only an expression is one, since an operand of a
    /// chain's union is a literal, which has no operands.
    async fn choice<A: Literal>(&'m self, p: &Part<A>) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let Part::Expr(e) = p else { return None };
        let Form::Or(a, b) = &e.form else { return None };
        let (c, x, y) = self.choice_of(a, b, Op::Or).await?;
        let (d, same) = self.condition(&c).await;
        Some(if same { (d, x, y) } else { (d, y, x) })
    }
}

impl<A: Literal> Part<A> {
    /// Whether the value whose membership in each atom `holds` decides is in the part.
    /// Each expression is evaluated once, from a stack, and the second operand of an `Or` or
    /// `And` only when the first does not decide it.
    pub(super) fn eval(&self, holds: &impl Fn(&A) -> bool) -> bool {
        /// What is left to do: a part to evaluate, or an expression to finish once the value
        /// of its first operand (`First`), or of the operand that decides it (`Last`), is on
        /// the stack of values.
        enum Job<'a, A: Literal> {
            Part(&'a Part<A>),
            First(&'a Expr<A>),
            Last(&'a Expr<A>),
        }
        let mut memo: HashMap<u64, bool> = HashMap::new();
        let mut values: Vec<bool> = Vec::new();
        let mut jobs = vec![Job::Part(self)];
        while let Some(job) = jobs.pop() {
            match job {
                Job::Part(Part::Bdd(b)) => values.push(b.eval(holds)),
                Job::Part(Part::Expr(e)) => match memo.get(&e.id) {
                    Some(v) => values.push(*v),
                    None => {
                        let (_, a, _) = e.form.operands();
                        jobs.push(Job::First(e));
                        jobs.push(Job::Part(a));
                    }
                },
                Job::First(e) => {
                    let v = values.pop().expect("the first operand's value");
                    match &e.form {
                        Form::Not(_) => {
                            memo.insert(e.id, !v);
                            values.push(!v);
                        }
                        Form::Or(_, b) | Form::And(_, b) => {
                            if v == matches!(e.form, Form::Or(..)) {
                                memo.insert(e.id, v);
                                values.push(v);
                            } else {
                                jobs.push(Job::Last(e));
                                jobs.push(Job::Part(b));
                            }
                        }
                    }
                }
                Job::Last(e) => {
                    let v = *values.last().expect("the second operand's value");
                    memo.insert(e.id, v);
                }
            }
        }
        values.pop().expect("the part's value")
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
        // Each list once.
        fn bdd<A: Literal>(
            b: &Bdd<A>,
            holds: &impl Fn(&A) -> Option<bool>,
            memo: &mut HashMap<u64, Option<bool>>,
        ) -> Option<bool> {
            *memo.entry(b.id()).or_insert_with(|| b.eval3(holds))
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
                    Bdd::List(..) => None,
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
        let mut pins: HashMap<u64, bool> = HashMap::new();
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
            let mut pins: HashMap<u64, bool> = HashMap::new();
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
        self.rebuild(|p| match p {
            Part::Bdd(_) => Some(p.clone()),
            Part::Expr(e) => pins.get(&e.id).map(|v| Part::leaf(*v)),
        })
    }

    /// The part with each atom that `fix` decides replaced by its value, each node and
    /// expression rebuilt once.
    pub(super) fn restrict(&self, fix: &impl Fn(&A) -> Option<bool>) -> Part<A> {
        let mut nodes = list::Memo::default();
        self.rebuild(|p| match p {
            Part::Bdd(b) => Some(Part::Bdd(b.restrict(fix, &mut nodes))),
            Part::Expr(_) => None,
        })
    }

    /// The part with each expression rebuilt from its rebuilt operands by its connective, each
    /// once, after its operands, from a stack. `base` gives what a diagram becomes, and what an
    /// expression it decides becomes; `None` for an expression to rebuild.
    fn rebuild(&self, mut base: impl FnMut(&Part<A>) -> Option<Part<A>>) -> Part<A> {
        if let Some(r) = base(self) {
            return r;
        }
        let Part::Expr(root) = self else {
            unreachable!("`base` decides every diagram")
        };
        let mut memo: HashMap<u64, Part<A>> = HashMap::new();
        let mut stack: Vec<(&Expr<A>, bool)> = vec![(root, false)];
        while let Some((e, ready)) = stack.pop() {
            if memo.contains_key(&e.id) {
                continue;
            }
            let (_, a, b) = e.form.operands();
            if !ready {
                stack.push((e, true));
                // The first operand is pushed last, so it is rebuilt first.
                for q in b.into_iter().chain([a]) {
                    if let Part::Expr(x) = q
                        && !memo.contains_key(&x.id)
                    {
                        match base(q) {
                            Some(r) => {
                                memo.insert(x.id, r);
                            }
                            None => stack.push((x, false)),
                        }
                    }
                }
                continue;
            }
            let mut get = |q: &Part<A>| match q {
                Part::Expr(x) => memo[&x.id].clone(),
                Part::Bdd(_) => base(q).expect("`base` decides every diagram"),
            };
            let (a, b) = (get(a), b.map(get));
            let r = match (&e.form, b) {
                (Form::Or(..), Some(b)) => a.zip(&b, Op::Or),
                (Form::And(..), Some(b)) => a.zip(&b, Op::And),
                _ => a.not(),
            };
            memo.insert(e.id, r);
        }
        memo[&root.id].clone()
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
                Bdd::List(..) => (settings(b.forced_to(true)), settings(b.forced_to(false))),
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
                        Part::Bdd(b @ Bdd::List(..)) => {
                            nodes.entry(b.id()).or_insert_with(|| of_bdd(b));
                        }
                        Part::Bdd(Bdd::Leaf(_)) => {}
                    }
                }
                continue;
            }
            let get = |q: &Part<A>| match q {
                Part::Expr(x) => exprs[&x.id].clone(),
                Part::Bdd(b @ Bdd::List(..)) => nodes[&b.id()].clone(),
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

    /// Whether `f` holds of every atom, each node and expression visited once, from a stack:
    /// an expression's first operand before its second. Diagram nodes and expressions share one
    /// set of ids seen, so a diagram under two expressions is visited once.
    pub(super) fn atoms<'a>(&'a self, f: &mut impl FnMut(&'a A) -> bool) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![self];
        while let Some(p) = stack.pop() {
            match p {
                Part::Bdd(b) => {
                    if !b.atoms_unseen(&mut seen, f) {
                        return false;
                    }
                }
                Part::Expr(e) => {
                    if seen.insert(e.id) {
                        let (_, a, b) = e.form.operands();
                        stack.extend(b);
                        stack.push(a);
                    }
                }
            }
        }
        true
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
    /// Each expression is visited once, from a stack, its first operand before its second.
    pub(super) fn union_rows(&self) -> Option<Vec<A>> {
        let (mut seen, mut out) = (HashSet::new(), Vec::new());
        let mut stack = vec![self];
        while let Some(p) = stack.pop() {
            match p {
                Part::Expr(e) => {
                    if !seen.insert(e.id) {
                        continue;
                    }
                    let Form::Or(a, b) = &e.form else {
                        return None;
                    };
                    stack.push(b);
                    stack.push(a);
                }
                Part::Bdd(b) => match b {
                    Bdd::Leaf(false) => {}
                    Bdd::Leaf(true) => return None,
                    // A union of atoms is one block of value `true` that takes them all.
                    Bdd::List(c, v) => {
                        if !*v || c.len > 1 {
                            return None;
                        }
                        for (a, taken) in set::iter(Some(&c.block)) {
                            if !taken {
                                return None;
                            }
                            out.push(a.clone());
                        }
                    }
                },
            }
        }
        Some(out)
    }

    /// The id of an expression; a diagram part has none of its own.
    pub(super) fn expr_id(&self) -> Option<u64> {
        match self {
            Part::Bdd(_) => None,
            Part::Expr(e) => Some(e.id),
        }
    }

    /// The diagram, or the connective of an expression.
    pub(super) fn view(&self) -> Result<&Bdd<A>, &Form<A>> {
        match self {
            Part::Bdd(b) => Ok(b),
            Part::Expr(e) => Err(&e.form),
        }
    }
}

/// Two lists, cells, sets, expressions or parts of one universe to compare in `order` (module `types`); no
/// cell or set is before one.
pub(super) enum Walk<'a, A: Literal> {
    Bdds(&'a Bdd<A>, &'a Bdd<A>),
    Cells(Option<&'a Cell<A>>, Option<&'a Cell<A>>),
    Sets(Option<&'a Set<A>>, Option<&'a Set<A>>),
    Exprs(&'a Expr<A>, &'a Expr<A>),
    Parts(&'a Part<A>, &'a Part<A>),
}

impl<A: Literal> Form<A> {
    /// The connective's rank in the order (`Not`, `Or`, `And`) and its operands.
    pub(super) fn operands(&self) -> (u8, &Part<A>, Option<&Part<A>>) {
        match self {
            Form::Not(a) => (0, a, None),
            Form::Or(a, b) => (1, a, Some(b)),
            Form::And(a, b) => (2, a, Some(b)),
        }
    }
}

impl<A: Literal> Ord for Part<A> {
    fn cmp(&self, other: &Part<A>) -> Ordering {
        A::order(Walk::Parts(self, other))
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
        A::order(Walk::Exprs(self, other))
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

impl<A: Literal> Ord for Bdd<A> {
    fn cmp(&self, other: &Bdd<A>) -> Ordering {
        A::order(Walk::Bdds(self, other))
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

// The exclusive ors (module `xor`) are written in this file: they are built by the connectives on
// parts, and the connectives recognize them, so the two are one unit.
mod xor {
    //! The exclusive or of atoms in its one form: the atoms' set, each atom taken (module `set`),
    //! and a constant joined to them, so that the exclusive or of one set of atoms is one node
    //! whatever order it was built in.
    //!
    //! The node of a set is built over the set's tree: a tree node's exclusive or joins those of
    //! its two subtrees and its own atom, two at a time, each as `p&!q | !p&q`, with the
    //! complement `p&q | !p&!q` made beside it. Since one set is one tree, of one shape, its node
    //! is one expression, kept in a table of the thread by the tree node's id and the constant,
    //! as are those of its subtrees. A set with a literal added or removed has `O(log n)` new
    //! tree nodes in expectation, and only those take new expressions, each in constant time.
    //!
    //! The table holds each node weakly, and a node leaves it when it is dropped (step
    //! TABLE-life). The two expressions made beside each other share the halves they were made
    //! from (`Pair`), and the one dropped first is made again from them when its complement is
    //! asked for ([`mate`]), equal as built to the one dropped.
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

    /// A pair's halves and set are freed in a loop (module `deep`), as an expression's operands
    /// are.
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

    /// Whether `x` is the complement of `y`: one set of atoms, compared by contents when the
    /// two were made on two threads ([`set::same`]), and the other constant.
    fn opposite<A: Literal>(x: &Tag<A>, y: &Tag<A>) -> bool {
        x.1 != y.1 && set::same(&x.0, &y.0)
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

        /// The atoms of the part as an exclusive or in its one form ([`Part::xor_tag`]), in
        /// order, and the constant joined to them; `None` for a part that is not one.
        pub(in crate::types) fn exclusive_or(&self) -> Option<(Vec<A>, bool)> {
            let (atoms, constant) = self.xor_tag()?;
            let atoms = set::iter(Some(&atoms)).map(|(a, _)| a.clone());
            Some((atoms.collect(), constant))
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
    /// `true`, `np` and `nq` the halves' complements; kept in the thread's table when the pair is
    /// the one form of a set.
    fn half<A: Literal>(
        pair: &Arc<Pair<A>>,
        constant: bool,
        np: &Part<A>,
        nq: &Part<A>,
    ) -> Part<A> {
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
            Operands::Chain(d) => match d.chain(op)?[..] {
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
}
mod list {
    //! A diagram as a decision list in its one form, which does not depend on the order of the
    //! atoms (step BDD-atom-order).
    //!
    //! Only chains grow a diagram (`Part::zip`), so every diagram is a decision list: literals in
    //! turn, the first that holds giving the value, and a default when none holds. Its one form has
    //! blocks: the first block holds every literal under which the function is constant, all with
    //! one value; each later block holds every literal under which the function is constant once
    //! the literals of the blocks before are false; the values alternate, and the default is the
    //! value left. So no atom is in two blocks, two or more blocks end in a block of two or more
    //! literals, and one block of one literal takes the value `true`.
    //!
    //! A list is kept as a sequence of blocks (each a set of literals, module `set`) with the value
    //! of its first block; the values of the others alternate, and the complement flips that value.
    //! The sequence is a treap of cells by position (item CHAIN-deep-atom): a cell is a block and
    //! the sequences of the blocks before and after it, its priority a hash of one literal of its
    //! block ([`priority`]), ties broken by position, the earlier above. So one sequence has one
    //! shape, whatever edits made it, and the cells are shared through a table of the thread by
    //! their children and block: one list is one cell. Each cell keeps, made on first use, the atoms of its blocks, so the
    //! block of an atom is found from the root in `O(log m)` for `m` blocks. A chain of literals
    //! joined to a list ([`Bdd::or_literal`]) adds each literal to the first block, or puts a block
    //! of it first; a literal on an atom the list holds is first set false there, which removes it
    //! from its block or cuts the list at its block. Each such change rebuilds the cells on the
    //! paths to the blocks it changes, `O(log m)` cells in expectation, each looked up in the
    //! table in `O(log N)`.

    use std::collections::HashMap;
    use std::sync::atomic::Ordering as Atomic;
    use std::sync::{Arc, OnceLock, Weak};

    use super::set::{self, Key, NEXT, Set, Tree};
    use super::{Bdd, KeyHasher, Literal, Owned, Part, mix};

    /// A node of a sequence of blocks: a block and the sequences of the blocks before and after
    /// it. A cell that is the root of a list's sequence is the list, with the value of its first
    /// block beside it ([`Bdd::List`]).
    pub(in crate::types) struct Cell<A: Literal> {
        /// The cell's id, unique among the nodes of the process, and the next id, kept for it:
        /// the list of first value `v` has the id `id + v`.
        pub(in crate::types) id: u64,
        /// A hash of the blocks in order, equal for equal sequences.
        pub(in crate::types) digest: u64,
        prio: u64,
        /// The number of blocks.
        pub(super) len: usize,
        pub(in crate::types) left: Seq<A>,
        pub(in crate::types) block: Arc<Set<A>>,
        pub(in crate::types) right: Seq<A>,
        /// The atoms of the blocks, made on first use.
        atoms: OnceLock<imbl::OrdSet<A>>,
        /// The first node of the list of each first value, as [`Bdd::branch`] shows it: its `hi`
        /// and `lo`, made on first use.
        view: [OnceLock<(Bdd<A>, Bdd<A>)>; 2],
    }

    /// A sequence of blocks: its root, or `None` when empty.
    pub(in crate::types) type Seq<A> = Option<Arc<Cell<A>>>;

    /// The live cells of a thread, by the ids of their children and block, each held weakly: a cell
    /// leaves the table when it is dropped (step TABLE-life).
    pub(in crate::types) type CellTable<A> =
        std::collections::BTreeMap<(u64, u64, u64), Weak<Cell<A>>>;

    /// A cell leaves its thread's table, and its children and views are freed in a loop (module
    /// `deep`).
    impl<A: Literal> Drop for Cell<A> {
        fn drop(&mut self) {
            let key = (id(&self.left), self.block.id, id(&self.right));
            A::untable(|t| {
                // Another cell of the key may have taken the entry since, or none was made here.
                if let std::collections::btree_map::Entry::Occupied(e) = t.cells.entry(key)
                    && std::ptr::eq(e.get().as_ptr(), self)
                {
                    e.remove();
                }
            });
            for c in [self.left.take(), self.right.take()].into_iter().flatten() {
                A::free(Owned::Cell(c));
            }
            for v in &mut self.view {
                if let Some((hi, lo)) = v.take() {
                    A::free(Owned::Part(Part::Bdd(hi)));
                    A::free(Owned::Part(Part::Bdd(lo)));
                }
            }
        }
    }

    /// A diagram as a decision list in its one form (module comment).
    #[derive(Debug)]
    pub(in crate::types) struct List<A: Literal> {
        /// The blocks in order, each its value and its literals: an atom and whether it is
        /// taken. The literals of a block are in the order of their atoms.
        pub(in crate::types) blocks: Vec<(bool, Vec<(A, bool)>)>,
        /// The value when no literal holds.
        pub(in crate::types) tail: bool,
    }

    /// A run of blocks, the values alternating from the second: the sequence, and the value of its
    /// first block (any value when it is empty).
    type Run<A> = (Seq<A>, bool);

    /// A list restricted ([`Bdd::restrict`]) from one of its cells on: the run of blocks left, and,
    /// when a literal set true cut it, the value it ends with.
    type Piece<A> = (Run<A>, Option<bool>);

    /// The pieces of the cells restricted, by twice the cell's id plus the value of its first block
    /// (`Part::restrict`'s memo for lists).
    pub(super) type Memo<A> = HashMap<u64, Piece<A>, std::hash::BuildHasherDefault<KeyHasher>>;

    fn id<A: Literal>(t: &Seq<A>) -> u64 {
        t.as_ref().map_or(0, |c| c.id)
    }

    fn len<A: Literal>(t: &Seq<A>) -> usize {
        t.as_ref().map_or(0, |c| c.len)
    }

    fn digest<A: Literal>(t: &Seq<A>) -> u64 {
        t.as_ref().map_or(mix(17, 0), |c| c.digest)
    }

    /// The priority of the cell of `block`: a hash of the literal at the root of the block's treap,
    /// the literal of highest priority there (module `set`), by a hash other than that priority. So
    /// it is uniform whatever the size of the block, and a literal added to a block of `k` changes
    /// it only when it outranks the `k` there, with probability `1 / (k + 1)` in any order of
    /// adding: a block edited in place keeps its cell's place, and its atoms are carried over
    /// ([`replace`]). A priority hashed from the whole block moved the cell at each edit and made
    /// its atoms again, `O(k)` each.
    fn priority<A: Literal>(block: &Set<A>) -> u64 {
        mix(mix(19, block.key.0.digest()), u64::from(block.key.1))
    }

    /// The value of the block at `k` of a run whose first block has the value `first`.
    fn value_at(first: bool, k: usize) -> bool {
        first != (k % 2 == 1)
    }

    /// The atoms of `block`.
    fn atoms_of<A: Literal>(block: &Arc<Set<A>>) -> Vec<A> {
        set::iter(Some(block)).map(|(a, _)| a.clone()).collect()
    }

    /// The cell of `block` between `left` and `right`, the one in the table if there is one.
    fn cell<A: Literal>(left: Seq<A>, block: Arc<Set<A>>, right: Seq<A>) -> Arc<Cell<A>> {
        let key = (id(&left), block.id, id(&right));
        // One walk of the table finds the cell or the place for a new one; a cell found dead is
        // replaced there, and its weak handle dropped, which touches no table.
        A::table(|t| {
            let entry = t.cells.entry(key);
            if let std::collections::btree_map::Entry::Occupied(e) = &entry
                && let Some(c) = e.get().upgrade()
            {
                return c;
            }
            let c = Arc::new(Cell {
                id: NEXT.fetch_add(2, Atomic::Relaxed),
                digest: mix(mix(mix(16, digest(&left)), block.digest), digest(&right)),
                prio: priority(&block),
                len: len(&left) + 1 + len(&right),
                left,
                block,
                right,
                atoms: OnceLock::new(),
                view: [OnceLock::new(), OnceLock::new()],
            });
            entry.insert_entry(Arc::downgrade(&c));
            c
        })
    }

    /// The sequence of `x` then `y`, rebuilt along the right edge of `x` and the left edge of `y`
    /// down to where their cells meet by priority, the earlier above on a tie.
    fn merge<A: Literal>(x: Seq<A>, y: Seq<A>) -> Seq<A> {
        let mut path: Vec<(Arc<Cell<A>>, bool)> = Vec::new();
        let (mut x, mut y) = (x, y);
        let mut node = loop {
            match (x, y) {
                (None, r) => break r,
                (l, None) => break l,
                (Some(a), Some(b)) => {
                    if a.prio >= b.prio {
                        x = a.right.clone();
                        y = Some(b);
                        path.push((a, true));
                    } else {
                        y = b.left.clone();
                        x = Some(a);
                        path.push((b, false));
                    }
                }
            }
        };
        for (n, from_x) in path.into_iter().rev() {
            node = Some(match from_x {
                true => cell(n.left.clone(), n.block.clone(), node),
                false => cell(node, n.block.clone(), n.right.clone()),
            });
        }
        node
    }

    /// The first `k` blocks of `t` and the blocks after, rebuilt along the path to the place cut.
    fn split<A: Literal>(t: &Seq<A>, k: usize) -> (Seq<A>, Seq<A>) {
        split_parts(t, k, (true, true))
    }

    /// The first `k` blocks of `t` ([`split`]).
    fn prefix<A: Literal>(t: &Seq<A>, k: usize) -> Seq<A> {
        split_parts(t, k, (true, false)).0
    }

    /// The blocks of `t` after the first `k` ([`split`]).
    fn suffix<A: Literal>(t: &Seq<A>, k: usize) -> Seq<A> {
        split_parts(t, k, (false, true)).1
    }

    /// [`split`], building only the parts `want` names, `None` for the other: each cell built
    /// costs a lookup and an entry in the table, and leaves it again when dropped. A cut at either
    /// end of `t` leaves `t` whole.
    fn split_parts<A: Literal>(t: &Seq<A>, k: usize, want: (bool, bool)) -> (Seq<A>, Seq<A>) {
        let whole = |w: bool| if w { t.clone() } else { None };
        if k == 0 {
            return (None, whole(want.1));
        }
        if k >= len(t) {
            return (whole(want.0), None);
        }
        let mut path: Vec<(&Arc<Cell<A>>, bool)> = Vec::new();
        let (mut at, mut k) = (t.as_ref(), k);
        while let Some(n) = at {
            let ln = len(&n.left);
            if k <= ln {
                path.push((n, false));
                at = n.left.as_ref();
            } else {
                path.push((n, true));
                k -= ln + 1;
                at = n.right.as_ref();
            }
        }
        let (mut l, mut r) = (None, None);
        for (n, before) in path.into_iter().rev() {
            match before {
                true if want.0 => l = Some(cell(n.left.clone(), n.block.clone(), l)),
                false if want.1 => r = Some(cell(r, n.block.clone(), n.right.clone())),
                _ => {}
            }
        }
        (l, r)
    }

    /// The block at `k` of `t`, which has more than `k` blocks.
    fn nth<A: Literal>(t: &Seq<A>, mut k: usize) -> &Arc<Set<A>> {
        let mut at = t.as_ref().expect("a sequence has the block asked for");
        loop {
            let ln = len(&at.left);
            match k.cmp(&ln) {
                std::cmp::Ordering::Less => {
                    at = at.left.as_ref().expect("the block is on the left")
                }
                std::cmp::Ordering::Equal => return &at.block,
                std::cmp::Ordering::Greater => {
                    k -= ln + 1;
                    at = at.right.as_ref().expect("the block is on the right");
                }
            }
        }
    }

    /// The atoms in the blocks the edit removes, and those in the blocks it puts in their place,
    /// atoms in both left out.
    type Delta<'a, A> = (&'a [A], &'a [A]);

    /// Gives `new`, a cell of the blocks of `old` after an edit that changed its atoms by `delta`,
    /// the atoms of `old` changed by `delta`, when `old` has made its atoms: `O(|delta| log m)`.
    /// Otherwise `new` makes its atoms on first use.
    fn carry<A: Literal>(old: &Arc<Cell<A>>, new: &Arc<Cell<A>>, (gone, added): Delta<'_, A>) {
        if Arc::ptr_eq(old, new) || new.atoms.get().is_some() {
            return;
        }
        if let Some(s) = old.atoms.get() {
            let mut s = s.clone();
            for a in gone {
                s.remove(a);
            }
            for a in added {
                s.insert(a.clone());
            }
            let _ = new.atoms.set(s);
        }
    }

    /// `t` with the blocks from `i` to before `j` replaced by `new`, whose atoms differ from theirs
    /// by `delta`. The cells above the place edited whose priority stays above the new blocks' are
    /// rebuilt along the path; below, the cell where the path stops is the root of the region
    /// rebuilt by `split` and `merge`, `O(log m)` blocks in expectation. Every cell rebuilt on the
    /// path, and the region's root, covers the blocks of a cell of `t` changed by `delta` alone, and
    /// takes its atoms from that cell's ([`carry`]).
    fn replace<A: Literal>(
        t: &Seq<A>,
        (i, j): (usize, usize),
        new: Vec<Arc<Set<A>>>,
        delta: Delta<'_, A>,
    ) -> Seq<A> {
        let top = new.iter().map(|s| priority(s)).max();
        let mut path: Vec<(&Arc<Cell<A>>, bool)> = Vec::new();
        let (mut at, mut i, mut j) = (t.as_ref(), i, j);
        let region = loop {
            let Some(n) = at else { break None };
            let ln = len(&n.left);
            // A new block before the cell is above it on a tie of priorities, one after is below.
            if j <= ln && top.is_none_or(|p| n.prio > p) {
                path.push((n, true));
                at = n.left.as_ref();
            } else if i > ln && top.is_none_or(|p| n.prio >= p) {
                path.push((n, false));
                (i, j) = (i - ln - 1, j - ln - 1);
                at = n.right.as_ref();
            } else {
                break Some(n);
            }
        };
        // When the region is the one cell edited, a block removed leaves its children merged, and
        // a block in its place whose priority keeps the order of the treap takes its children:
        // the cells `split` and `merge` would make, without the cells they make and drop.
        let alone = region.filter(|n| i == len(&n.left) && j == i + 1);
        let fits = |n: &Cell<A>, p: u64| {
            n.left.as_ref().is_none_or(|l| l.prio < p)
                && n.right.as_ref().is_none_or(|r| r.prio <= p)
        };
        let mut node = match (alone, &new[..]) {
            (Some(n), []) => merge(n.left.clone(), n.right.clone()),
            (Some(n), [b]) if fits(n, priority(b)) => {
                Some(cell(n.left.clone(), b.clone(), n.right.clone()))
            }
            _ => {
                let (before, rest) = split(&region.cloned(), i);
                let after = suffix(&rest, j - i);
                let mid = new
                    .into_iter()
                    .fold(None, |s, b| merge(s, Some(cell(None, b, None))));
                merge(merge(before, mid), after)
            }
        };
        if let (Some(old), Some(made)) = (region, &node) {
            carry(old, made, delta);
        }
        for (n, left) in path.into_iter().rev() {
            let made = match left {
                true => cell(node, n.block.clone(), n.right.clone()),
                false => cell(n.left.clone(), n.block.clone(), node),
            };
            carry(n, &made, delta);
            node = Some(made);
        }
        node
    }

    /// The run of `x` then `y`, the last block of `x` and the first of `y` joined when they have
    /// one value.
    fn join<A: Literal>((x, v): Run<A>, (y, w): Run<A>) -> Run<A> {
        let (n, m) = (len(&x), len(&y));
        if n == 0 {
            return (y, w);
        }
        if m == 0 {
            return (x, v);
        }
        if value_at(v, n - 1) != w {
            return (merge(x, y), v);
        }
        let joined = set::union(nth(&x, n - 1), nth(&y, 0));
        let front = prefix(&x, n - 1);
        let back = suffix(&y, 1);
        let mid = Some(cell(None, joined, None));
        (merge(merge(front, mid), back), v)
    }

    impl<A: Literal> Cell<A> {
        /// The atoms of the blocks, made once for each cell, children first, each from the larger
        /// of its children's with the smaller's atoms and its block's added: `O(min(l, r) log m)`
        /// for a cell whose children have `l` and `r` atoms.
        pub(super) fn atoms(&self) -> &imbl::OrdSet<A> {
            if let Some(s) = self.atoms.get() {
                return s;
            }
            let mut stack: Vec<(&Cell<A>, bool)> = vec![(self, false)];
            while let Some((c, ready)) = stack.pop() {
                if c.atoms.get().is_some() {
                    continue;
                }
                let kids = [c.left.as_deref(), c.right.as_deref()];
                if !ready {
                    stack.push((c, true));
                    for k in kids.into_iter().flatten() {
                        if k.atoms.get().is_none() {
                            stack.push((k, false));
                        }
                    }
                    continue;
                }
                let [l, r] = kids.map(|k| k.and_then(|k| k.atoms.get()));
                let (big, small) = match (l, r) {
                    (Some(l), Some(r)) if l.len() < r.len() => (Some(r), Some(l)),
                    (Some(l), r) => (Some(l), r),
                    (None, r) => (r, None),
                };
                let mut s = big.cloned().unwrap_or_default();
                for a in small.into_iter().flatten() {
                    s.insert(a.clone());
                }
                for (a, _) in set::iter(Some(&c.block)) {
                    s.insert(a.clone());
                }
                let _ = c.atoms.set(s);
            }
            self.atoms.get().expect("the atoms were just made")
        }

        /// The first block.
        fn first(&self) -> &Arc<Set<A>> {
            let mut at = self;
            while let Some(l) = &at.left {
                at = l;
            }
            &at.block
        }

        /// The place of the block that holds `atom`, and whether it takes it: down from the root,
        /// to the left when the cell on the left holds it, in `O(log m)` steps for `m` blocks.
        fn find(&self, atom: &A) -> Option<(usize, bool)> {
            let (mut at, mut off) = (self, 0);
            loop {
                let ln = len(&at.left);
                if let Some(taken) = set::get(Some(&at.block), atom) {
                    return Some((off + ln, taken));
                }
                match &at.left {
                    Some(l) if l.atoms().contains(atom) => at = l,
                    _ => {
                        off += ln + 1;
                        at = at.right.as_deref()?;
                    }
                }
            }
        }
    }

    /// The cells of a list in order, with the value of each block (`Bdd::cells`).
    pub(super) struct Cells<'a, A: Literal> {
        stack: Vec<&'a Cell<A>>,
        value: bool,
    }

    impl<'a, A: Literal> Cells<'a, A> {
        fn down(&mut self, mut at: Option<&'a Cell<A>>) {
            while let Some(c) = at {
                self.stack.push(c);
                at = c.left.as_deref();
            }
        }
    }

    impl<'a, A: Literal> Iterator for Cells<'a, A> {
        type Item = (bool, &'a Cell<A>);
        fn next(&mut self) -> Option<Self::Item> {
            let c = self.stack.pop()?;
            self.down(c.right.as_deref());
            let v = self.value;
            self.value = !v;
            Some((v, c))
        }
    }

    /// The list of the run `(seq, first)` and the default `default`, in its one form (module
    /// comment), its blocks already alternating and none empty: the last block dropped when its
    /// value is the default, then a last block of one literal `{m}` after another moved into it as
    /// `!m`, then a single block of one literal and value `false` made `{!m}` of value `true`.
    fn finish<A: Literal>((mut seq, mut first): Run<A>, mut default: bool) -> Bdd<A> {
        let mut n = len(&seq);
        if n == 0 {
            return Bdd::Leaf(default);
        }
        if value_at(first, n - 1) == default {
            let gone = atoms_of(nth(&seq, n - 1));
            seq = replace(&seq, (n - 1, n), Vec::new(), (&gone, &[]));
            n -= 1;
            if n == 0 {
                return Bdd::Leaf(default);
            }
        }
        if n >= 2
            && let Some(m) = set::single_key(nth(&seq, n - 1))
        {
            // `… before:!u, {m}:u, default !u` is `… (before ∪ {!m}):!u, default u`.
            let joined = set::insert(Some(nth(&seq, n - 2)), (m.0.clone(), !m.1));
            default = value_at(first, n - 1);
            seq = replace(&seq, (n - 2, n), vec![joined], (&[], &[]));
            n -= 1;
        }
        if n == 1
            && !first
            && let Some(m) = set::single_key(nth(&seq, 0))
        {
            // `{m}:false, default true` is `{!m}:true, default false`.
            let flipped = set::single((m.0.clone(), !m.1));
            seq = replace(&seq, (0, 1), vec![flipped], (&[], &[]));
            first = true;
            default = false;
        }
        debug_assert_ne!(
            value_at(first, n - 1),
            default,
            "the default follows the last block"
        );
        Bdd::List(seq.expect("a list of one or more blocks has a cell"), first)
    }

    impl<A: Literal> Bdd<A> {
        /// The list of the one literal `key`.
        pub(super) fn literal_key(key: Key<A>) -> Bdd<A> {
            Bdd::List(cell(None, set::single(key), None), true)
        }

        /// The cells with the value of each block, first to last.
        pub(super) fn cells(&self) -> Cells<'_, A> {
            let mut cells = Cells {
                stack: Vec::new(),
                value: false,
            };
            if let Bdd::List(c, v) = self {
                cells.value = *v;
                cells.down(Some(c));
            }
            cells
        }

        /// The list of `prefix`, each block a value and its literals, before `rest`, in its one form
        /// (module comment): empty blocks dropped, neighbors of one value joined, and the end put
        /// in its one form ([`finish`]).
        pub(super) fn assemble(prefix: Vec<(bool, Tree<A>)>, rest: &Bdd<A>) -> Bdd<A> {
            let (mut run, default) = match rest {
                Bdd::Leaf(x) => ((None, false), *x),
                Bdd::List(c, v) => ((Some(c.clone()), *v), rest.default()),
            };
            for (v, s) in prefix.into_iter().rev() {
                if let Some(s) = s {
                    run = join((Some(cell(None, s, None)), v), run);
                }
            }
            finish(run, default)
        }

        /// `self | l`, `l` the literal `key`. When the list holds the atom, the literal is first set
        /// false in it; the literal then joins the first block if its value is `true`, or comes
        /// first in a block of its own.
        pub(super) fn or_literal(&self, key: Key<A>) -> Bdd<A> {
            let (c, v) = match self {
                Bdd::Leaf(true) => return self.clone(),
                Bdd::Leaf(false) => return Bdd::literal_key(key),
                Bdd::List(c, v) => (c, *v),
            };
            let seq = Some(c.clone());
            let Some((at, taken)) = c.find(&key.0) else {
                let added = [key.0.clone()];
                let root = match v {
                    true => {
                        let first = set::insert(Some(c.first()), key);
                        replace(&seq, (0, 1), vec![first], (&[], &added))
                    }
                    false => replace(&seq, (0, 0), vec![set::single(key)], (&[], &added)),
                };
                return Bdd::List(root.expect("a list with a block added has a cell"), true);
            };
            if v && at == 0 && taken == key.1 {
                return self.clone();
            }
            let (n, w) = (c.len, value_at(v, at));
            let rest = if taken == key.1 {
                // The literal set false leaves its block; an empty block leaves the list, and the
                // blocks on either side of it, of one value, are joined. The default stays.
                let gone = [key.0.clone()];
                let delta = (&gone[..], &[][..]);
                let default = !value_at(v, n - 1);
                match set::remove(nth(&seq, at), &key) {
                    Some(b) => finish((replace(&seq, (at, at + 1), vec![b], delta), v), default),
                    None if at == 0 => {
                        finish((replace(&seq, (0, 1), Vec::new(), delta), !v), default)
                    }
                    None if at + 1 == n => {
                        finish((replace(&seq, (at, n), Vec::new(), delta), v), default)
                    }
                    None => {
                        let joined = set::union(nth(&seq, at - 1), nth(&seq, at + 1));
                        finish(
                            (replace(&seq, (at - 1, at + 2), vec![joined], delta), v),
                            default,
                        )
                    }
                }
            } else {
                // The opposite literal holds, so the list ends at its block.
                // Complexity tradeoff: the blocks before the cut are split off in `O(log m)`, and
                // the cells on the path cut make their atoms again on first use, each from its
                // children's, the smaller added to the larger: up to `O(min(p, m - p) log m)` for a
                // cut after `p` of `m` blocks, where carrying the atoms over would cost the `m - p`
                // atoms dropped. Measured in `rejoining_one_atom_of_each_block_scales`; COMPLEXITY.md
                // K67 (4). A sequence that kept its atoms by count of blocks would carry them in
                // `O(log m)`.
                finish((prefix(&seq, at), v), w)
            };
            rest.or_literal(key)
        }

        /// `self & l`, `l` the literal `key`: `!(!self | !l)`.
        pub(super) fn and_literal(&self, (a, taken): Key<A>) -> Bdd<A> {
            self.not().or_literal((a, !taken)).not()
        }

        /// The value when no literal holds: the value after the last block's.
        pub(super) fn default(&self) -> bool {
            match self {
                Bdd::Leaf(v) => *v,
                Bdd::List(c, v) => !value_at(*v, c.len - 1),
            }
        }

        /// The first block, for a list.
        pub(super) fn first_block(&self) -> Option<&Arc<Set<A>>> {
            match self {
                Bdd::Leaf(_) => None,
                Bdd::List(c, _) => Some(c.first()),
            }
        }

        /// The decision list in its one form (module comment).
        pub(in crate::types) fn list(&self) -> List<A> {
            let blocks = self
                .cells()
                .map(|(v, c)| (v, set::iter(Some(&c.block)).cloned().collect()))
                .collect();
            List {
                blocks,
                tail: self.default(),
            }
        }

        /// The list's first node, as a diagram would have it: the smallest literal of the first
        /// block, and the leaf of the block's value on the side where it holds, the list without
        /// it on the other. The view is made once for each list.
        pub(super) fn view(&self) -> Option<(&A, &Bdd<A>, &Bdd<A>)> {
            let Bdd::List(c, v) = self else { return None };
            let first = c.first();
            let (a, taken) = set::min(first);
            let (hi, lo) = c.view[usize::from(*v)].get_or_init(|| {
                let seq = Some(c.clone());
                let gone = [a.clone()];
                let delta = (&gone[..], &[][..]);
                let rest = match set::remove(first, &(a.clone(), *taken)) {
                    Some(b) => (replace(&seq, (0, 1), vec![b], delta), *v),
                    None => (replace(&seq, (0, 1), Vec::new(), delta), !*v),
                };
                let rest = finish(rest, self.default());
                match taken {
                    true => (Bdd::Leaf(*v), rest),
                    false => (rest, Bdd::Leaf(*v)),
                }
            });
            Some((a, hi, lo))
        }

        /// Whether `f` holds of the atom of every cell not in `seen`, each added to it; the blocks
        /// in turn, the atoms of a block in order. A cell seen before is passed over with the cells
        /// below it, all of which were walked then.
        pub(super) fn atoms_unseen<'a>(
            &'a self,
            seen: &mut std::collections::HashSet<u64>,
            f: &mut impl FnMut(&'a A) -> bool,
        ) -> bool {
            let Bdd::List(c, _) = self else { return true };
            let mut stack: Vec<&'a Cell<A>> = Vec::new();
            let mut at = Some(&**c).filter(|c| seen.insert(c.id));
            loop {
                while let Some(c) = at {
                    stack.push(c);
                    at = c.left.as_deref().filter(|l| seen.insert(l.id));
                }
                let Some(c) = stack.pop() else { return true };
                if !set::iter(Some(&c.block)).all(|(a, _)| f(a)) {
                    return false;
                }
                at = c.right.as_deref().filter(|r| seen.insert(r.id));
            }
        }

        /// The list with each atom that `fix` decides replaced by its value: a literal set false
        /// leaves its block, and one set true ends the list at its block with the block's value.
        /// Each cell is restricted once for each `memo` and value of its first block, keyed by its
        /// id and that value, so lists that share cells share the work (item CHAIN-restrict-memo):
        /// a cell's piece is its left child's, then its block's, then, when neither ended the list,
        /// its right child's, joined, from a stack. So the blocks after the first literal set true
        /// are not walked, and a cell whose block and children are unchanged is kept. The end is
        /// put in its one form once ([`finish`]).
        pub(super) fn restrict(
            &self,
            fix: &impl Fn(&A) -> Option<bool>,
            memo: &mut Memo<A>,
        ) -> Bdd<A> {
            let Bdd::List(root, v) = self else {
                return self.clone();
            };
            let key = |c: &Cell<A>, w: bool| 2 * c.id + u64::from(w);
            let piece = |memo: &Memo<A>, c: &Seq<A>, w: bool| match c {
                None => ((None, w), None),
                Some(c) => memo[&key(c, w)].clone(),
            };
            /// What is left to do for a cell: its left child, its block, or, with the block left
            /// and the left child's piece, its right child.
            enum Stage<A: Literal> {
                Left,
                Block,
                Right(Tree<A>, Piece<A>),
            }
            let mut stack = vec![(root, *v, Stage::<A>::Left)];
            while let Some((c, w, stage)) = stack.pop() {
                let wb = value_at(w, len(&c.left));
                match stage {
                    Stage::Left => {
                        if !memo.contains_key(&key(c, w)) {
                            stack.push((c, w, Stage::Block));
                            if let Some(l) = &c.left {
                                stack.push((l, w, Stage::Left));
                            }
                        }
                    }
                    Stage::Block => {
                        let left = piece(memo, &c.left, w);
                        if left.1.is_some() {
                            memo.insert(key(c, w), left);
                            continue;
                        }
                        let mut block = Some(c.block.clone());
                        let mut cut = false;
                        for k in set::iter(Some(&c.block)) {
                            match fix(&k.0) {
                                None => {}
                                Some(x) if x == k.1 => {
                                    cut = true;
                                    break;
                                }
                                Some(_) => {
                                    let b = block
                                        .as_ref()
                                        .expect("a literal not yet removed is in its block");
                                    block = set::remove(b, k);
                                }
                            }
                        }
                        if cut {
                            memo.insert(key(c, w), (left.0, Some(wb)));
                            continue;
                        }
                        stack.push((c, w, Stage::Right(block, left)));
                        if let Some(r) = &c.right {
                            stack.push((r, !wb, Stage::Left));
                        }
                    }
                    Stage::Right(block, left) => {
                        let right = piece(memo, &c.right, !wb);
                        let kept = right.1.is_none()
                            && id(&left.0.0) == id(&c.left)
                            && id(&right.0.0) == id(&c.right)
                            && block.as_ref().is_some_and(|b| b.id == c.block.id);
                        // With a block left whose neighbors have the other value, and whose
                        // priority keeps the order of the treap over the pieces, the joins below
                        // make one cell of the block between them, the cell made here.
                        let ((l, lw), (r, rw)) = (&left.0, &right.0);
                        let direct = block.as_ref().is_some_and(|b| {
                            let p = priority(b);
                            l.as_ref()
                                .is_none_or(|l| value_at(*lw, l.len - 1) != wb && l.prio < p)
                                && r.as_ref().is_none_or(|r| *rw != wb && r.prio <= p)
                        });
                        let made = if kept {
                            ((Some(c.clone()), w), None)
                        } else if direct && let Some(b) = block {
                            let first = if l.is_some() { *lw } else { wb };
                            ((Some(cell(l.clone(), b, r.clone())), first), right.1)
                        } else {
                            let mid = (block.map(|b| cell(None, b, None)), wb);
                            (join(join(left.0, mid), right.0), right.1)
                        };
                        memo.insert(key(c, w), made);
                    }
                }
            }
            let (run, cut) = piece(memo, &Some(root.clone()), *v);
            finish(run, cut.unwrap_or_else(|| self.default()))
        }
    }

    #[cfg(test)]
    impl<A: Literal> Bdd<A> {
        /// Whether every cell of the list that has made its atoms holds the atoms of its blocks,
        /// and its length and shape are those of a treap by position and priority.
        pub(super) fn cells_are_sound(&self) -> bool {
            let Bdd::List(c, _) = self else { return true };
            let mut stack = vec![&**c];
            while let Some(c) = stack.pop() {
                let mut all = imbl::OrdSet::new();
                let mut blocks = 0;
                let mut sub = vec![c];
                while let Some(d) = sub.pop() {
                    blocks += 1;
                    for (a, _) in set::iter(Some(&d.block)) {
                        all.insert(a.clone());
                    }
                    sub.extend(d.left.as_deref());
                    sub.extend(d.right.as_deref());
                }
                if c.atoms.get().is_some_and(|s| *s != all) || blocks != c.len {
                    return false;
                }
                if c.left.as_ref().is_some_and(|l| l.prio >= c.prio)
                    || c.right.as_ref().is_some_and(|r| r.prio > c.prio)
                {
                    return false;
                }
                stack.extend(c.left.as_deref());
                stack.extend(c.right.as_deref());
            }
            true
        }
    }
}

#[cfg(test)]
mod tests;
