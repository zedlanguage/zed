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
//! and reads each pair of cells, sets or expressions at most once ([`order`]).
//!
//! A part is decided (module `empty`) by three-valued operations: it is evaluated with some
//! atoms known (`Part::eval3`) and restricted to them (`Part::restrict`), each in time linear in
//! its literals; asked which atoms every value takes or refuses (`Part::forced`), in `O(n log n)`
//! on a list and one evaluation per atom on an expression; and settled on its shared
//! subexpressions (`Part::settle`), one evaluation per shared subexpression in each round. The
//! last two are above the rule of low complexity, an open item (DESIGN.md L1.23). Listing values
//! takes one pass over a list's first nodes, as a diagram would have them (`Bdd::reaching`).

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::Bound;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering as Atomic};
use std::sync::{Arc, Mutex, Weak};

use crate::frames::{Deep, Stack};

use super::{AtomPart, Morphism, Node, Op, Row, Type, mix};

mod list;
mod set;
mod xor;

use list::Cell;
use set::{Key, Set};

/// The next node id. Cells, sets and expressions take their ids from one counter, so an id
/// names one node among them; ids key the maps of a walk, never addresses.
static NEXT: AtomicU64 = AtomicU64::new(2);

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
    const fn new() -> Tables<A> {
        Tables {
            sets: BTreeMap::new(),
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
pub(super) trait Literal: Ord + Clone + super::debug::Queue + 'static {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R;
    /// Runs `f` on the thread's tables to remove a dropped node's entry. While the thread is
    /// ending and its tables are gone, or while they are borrowed, nothing is done: the entry is
    /// then a weak handle that no lookup takes, replaced when its key is next made.
    fn untable(f: impl FnOnce(&mut Tables<Self>));
    /// A hash of the atom, equal for equal atoms.
    fn digest(&self) -> u64;
    /// Drops a part, cell or set in the thread's loop of type parts (module `deep`).
    fn free(part: Owned<Self>);
    /// The step of [`order`] that compares two atoms.
    fn atoms<'a>(a: &'a Self, b: &'a Self) -> Step<'a>;
    /// The step of [`order`] that compares two lists, cells, sets, expressions or parts of the
    /// universe.
    fn walk(w: Walk<'_, Self>) -> Step<'_>;
}

thread_local! {
    static TUPLES: RefCell<Tables<Row>> = const { RefCell::new(Tables::new()) };
    static MORPHISMS: RefCell<Tables<Morphism>> = const { RefCell::new(Tables::new()) };
}

impl Literal for Row {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R {
        super::hold();
        TUPLES.with(|t| f(&mut t.borrow_mut()))
    }
    fn untable(f: impl FnOnce(&mut Tables<Self>)) {
        let _ = TUPLES.try_with(|t| t.try_borrow_mut().map(|mut t| f(&mut t)));
    }
    fn digest(&self) -> u64 {
        Row::digest(self)
    }
    fn free(part: Owned<Row>) {
        super::free(super::Freed::Tuples(part));
    }
    fn atoms<'a>(a: &'a Row, b: &'a Row) -> Step<'a> {
        Step::Rows(a, b)
    }
    fn walk(w: Walk<'_, Row>) -> Step<'_> {
        Step::Tuples(w)
    }
}

impl Literal for Morphism {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R {
        super::hold();
        MORPHISMS.with(|t| f(&mut t.borrow_mut()))
    }
    fn untable(f: impl FnOnce(&mut Tables<Self>)) {
        let _ = MORPHISMS.try_with(|t| t.try_borrow_mut().map(|mut t| f(&mut t)));
    }
    fn digest(&self) -> u64 {
        let m = mix(6, self.guarantee.digest());
        mix(mix(m, self.permission.digest()), self.value.digest())
    }
    fn free(part: Owned<Morphism>) {
        super::free(super::Freed::Morphisms(part));
    }
    fn atoms<'a>(a: &'a Morphism, b: &'a Morphism) -> Step<'a> {
        Step::Morphisms(a, b)
    }
    fn walk(w: Walk<'_, Morphism>) -> Step<'_> {
        Step::Arrows(w)
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

    fn digest(&self) -> u64 {
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
            Bdd::List(c, v) => c.next.is_none() && (*v == out || self.is_literal()),
        }
    }

    /// The literals of a chain under `op` of two or more literals, each an atom and whether
    /// the chain takes it; `None` for any other list.
    fn chain(&self, op: Op) -> Option<Vec<(&A, bool)>> {
        let Bdd::List(c, _) = self else { return None };
        if self.is_literal() || !self.is_chain(op) {
            return None;
        }
        let out = op == Op::Or;
        Some(
            set::iter(Some(&c.block))
                .map(|(a, p)| (a, *p == out))
                .collect(),
        )
    }

    /// The chain under `op` without its literal on `atom`, which it takes when `taken`.
    fn chain_without(&self, op: Op, atom: &A, taken: bool) -> Bdd<A> {
        // The literal is left out by fixing it to the value `op` passes over.
        let value = taken != (op == Op::Or);
        self.restrict(&|a| (a == atom).then_some(value), &mut HashMap::new())
    }

    /// The literal on `atom`, taken or refused.
    fn literal_of(atom: &A, taken: bool) -> Bdd<A> {
        Bdd::literal_key((atom.clone(), taken))
    }

    /// The atom of a list that is one literal, and whether the literal takes it.
    fn as_literal(&self) -> Option<(&A, bool)> {
        match self {
            Bdd::List(c, v) if c.next.is_none() => {
                set::single_key(&c.block).map(|(a, p)| (a, *p == *v))
            }
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

    /// The list with each atom that `fix` decides replaced by its value: a literal set false
    /// leaves its block, and one set true ends the list at its block with the block's value.
    /// The blocks after the last one changed are kept as they are.
    fn restrict(
        &self,
        fix: &impl Fn(&A) -> Option<bool>,
        memo: &mut HashMap<u64, Bdd<A>>,
    ) -> Bdd<A> {
        if let Bdd::Leaf(_) = self {
            return self.clone();
        }
        if let Some(r) = memo.get(&self.id()) {
            return r.clone();
        }
        let mut prefix = Vec::new();
        // The length of the prefix to the last block changed, and the list after that block.
        let mut changed = None;
        let mut cut = None;
        'blocks: for (w, c) in self.cells() {
            let mut block = Some(c.block.clone());
            for k in set::iter(Some(&c.block)) {
                match fix(&k.0) {
                    None => {}
                    Some(x) if x == k.1 => {
                        cut = Some(w);
                        break 'blocks;
                    }
                    Some(_) => {
                        let b = block
                            .as_ref()
                            .expect("a literal not yet removed is in its block");
                        block = set::remove(b, k);
                        changed = Some((prefix.len() + 1, (c.next.clone(), !w)));
                    }
                }
            }
            prefix.push((w, block, None));
        }
        let r = match (cut, changed) {
            (Some(w), _) => Bdd::assemble(prefix, (None, w)),
            (None, Some((len, rest))) => {
                prefix.truncate(len);
                Bdd::assemble(prefix, rest)
            }
            (None, None) => self.clone(),
        };
        memo.insert(self.id(), r.clone());
        r
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
        } else if let Bdd::List(c, false) = &f {
            for (a, p) in set::iter(Some(&c.block)) {
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

    /// Whether `f` holds of the atom of every cell not in `seen`, each added to it; the blocks
    /// in turn, the atoms of a block in order.
    fn atoms_unseen<'a>(
        &'a self,
        seen: &mut HashSet<u64>,
        f: &mut impl FnMut(&'a A) -> bool,
    ) -> bool {
        for (_, c) in self.cells() {
            if !seen.insert(c.id) {
                break;
            }
            if !set::iter(Some(&c.block)).all(|(a, _)| f(a)) {
                return false;
            }
        }
        true
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
    id: u64,
    digest: u64,
    form: Form<A>,
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
            (Part::Bdd(b), _) => b.chain(op).map(|lits| Operands::Chain(b, lits)),
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
                        if self.same_as_not(c, n).await {
                            found.push(((*c).clone(), (*x).clone(), (*y).clone()));
                        }
                    }
                }
            }
            (Operands::Two(p, q), Operands::Chain(d, lits)) => {
                for (c, x) in [(p, q), (q, p)] {
                    if let Some((atom, taken)) = within(&self.not(c).await, lits) {
                        let y = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push(((*c).clone(), (*x).clone(), y));
                    }
                }
            }
            (Operands::Chain(d, lits), Operands::Two(s, t)) => {
                for (n, y) in [(s, t), (t, s)] {
                    if let Some((atom, taken)) = within(&self.not(n).await, lits) {
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
        self.rebuild(|p| match p {
            Part::Bdd(_) => Some(p.clone()),
            Part::Expr(e) => pins.get(&e.id).map(|v| Part::leaf(*v)),
        })
    }

    /// The part with each atom that `fix` decides replaced by its value, each node and
    /// expression rebuilt once.
    pub(super) fn restrict(&self, fix: &impl Fn(&A) -> Option<bool>) -> Part<A> {
        let mut nodes = HashMap::new();
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
                        if !*v || c.next.is_some() {
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

/// Two lists, cells, sets, expressions or parts of one universe to compare in [`order`]; no
/// cell or set is before one.
pub(super) enum Walk<'a, A: Literal> {
    Bdds(&'a Bdd<A>, &'a Bdd<A>),
    Cells(Option<&'a Cell<A>>, Option<&'a Cell<A>>),
    Sets(Option<&'a Set<A>>, Option<&'a Set<A>>),
    Exprs(&'a Expr<A>, &'a Expr<A>),
    Parts(&'a Part<A>, &'a Part<A>),
}

/// The atom names of a type with their parts.
type AtomNames = imbl::OrdMap<Arc<str>, AtomPart>;

/// The tuple lengths of a type with their parts.
type Lens = BTreeMap<usize, Part<Row>>;

/// A pair to compare in [`order`], the rest of two sequences compared in order, the order of two
/// fields already compared, or two nodes or expressions whose contents compared equal.
pub(super) enum Step<'a> {
    Types(&'a Type, &'a Type),
    Rows(&'a Row, &'a Row),
    Morphisms(&'a Morphism, &'a Morphism),
    Tuples(Walk<'a, Row>),
    Arrows(Walk<'a, Morphism>),
    /// The remaining components of two rows.
    Items(std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>),
    /// The atom names of two types after the bound, each with its part: the maps and the last
    /// name read rather than two iterators, which would make every step five times the size.
    Names(&'a AtomNames, &'a AtomNames, Bound<&'a Arc<str>>),
    /// The tuple lengths of two types after the bound, each with its part.
    Lens(&'a Lens, &'a Lens, Bound<usize>),
    /// The order of two scalar fields, read when every field before them compared equal.
    Is(Ordering),
    Equal(u64, u64),
}

/// The order of the pair in `first`, the order of contents that `Ord` gives every type, row,
/// morphism type, part, diagram and expression: two types by digest, then by their parts field
/// by field (a recursive node after every other, two of them by key, `rec::Key::order`); two
/// rows by digest, then component by component; two morphism types by guarantee, permission and
/// value; two diagrams or expressions by digest, then by atom or connective, then by `hi` and
/// `lo` or by operands, a diagram before an expression; sequences (rows, atom names, tuple
/// lengths) lexicographically, a prefix first. Two nodes or expressions found equal are kept by node id
/// and not compared again, so the cost is one step per pair of nodes compared, not one per path
/// to them, and linear in the size when the two are equal. A loop with its own stack, as a type
/// can be deeper than the call stack: a row's components are types, whose tuple parts are
/// diagrams over rows, so where the digests tie (short-addresses build, step L1.37a, or a 64-bit
/// collision) two types n deep are compared n levels down (SHORT-stack-l01_22).
pub(super) fn order(first: Step<'_>) -> Ordering {
    let mut equal = HashSet::new();
    // The first step is held apart, so that a comparison its digests decide allocates nothing.
    let mut steps = Vec::new();
    let mut next = Some(first);
    while let Some(step) = next.take().or_else(|| steps.pop()) {
        let c = match step {
            Step::Equal(a, b) => {
                equal.insert((a, b));
                Ordering::Equal
            }
            Step::Is(c) => c,
            Step::Tuples(w) => walk(w, &mut steps, &equal),
            Step::Arrows(w) => walk(w, &mut steps, &equal),
            Step::Types(a, b) => types(a, b, &mut steps, &equal),
            Step::Rows(a, b) => {
                if Arc::ptr_eq(&a.0, &b.0) {
                    continue;
                }
                a.digest()
                    .cmp(&b.digest())
                    .then_with(|| items(a.iter(), b.iter(), &mut steps, &equal))
            }
            Step::Morphisms(a, b) => {
                steps.extend([
                    Step::Types(&a.value, &b.value),
                    Step::Types(&a.permission, &b.permission),
                    Step::Types(&a.guarantee, &b.guarantee),
                ]);
                Ordering::Equal
            }
            Step::Items(x, y) => items(x, y, &mut steps, &equal),
            Step::Names(p, q, from) => atom_names((p, q), from, &mut steps),
            Step::Lens(p, q, from) => tuple_lens((p, q), from, &mut steps, &equal),
        };
        if c != Ordering::Equal {
            return c;
        }
    }
    Ordering::Equal
}

/// One step of [`order`] on the remaining components of two rows: each pair of components is
/// read at once by [`types`] where its fields decide it, so that two rows told apart without
/// reading a nested type push nothing; at the first pair that needs one, the rest of the rows is
/// pushed below what [`types`] pushed. [`types`] calls neither this nor itself, so the depth of
/// the call stack is fixed.
fn items<'a>(
    mut x: std::slice::Iter<'a, Type>,
    mut y: std::slice::Iter<'a, Type>,
    steps: &mut Vec<Step<'a>>,
    equal: &HashSet<(u64, u64)>,
) -> Ordering {
    loop {
        match (x.next(), y.next()) {
            (Some(s), Some(t)) => {
                let n = steps.len();
                let c = types(s, t, steps, equal);
                if c != Ordering::Equal {
                    return c;
                }
                if steps.len() > n {
                    steps.insert(n, Step::Items(x, y));
                    return Ordering::Equal;
                }
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
}

/// One step of [`order`] on two types: the fields in order, each read at once where it can be,
/// so that two types told apart without reading a nested type push nothing; at the first field
/// that needs a nested comparison (an atom's payload, a tuple length's part, the morphism part)
/// the fields after it are pushed in reverse and the nested comparison above them, so that they
/// are compared in order.
fn types<'a>(
    a: &'a Type,
    b: &'a Type,
    steps: &mut Vec<Step<'a>>,
    equal: &HashSet<(u64, u64)>,
) -> Ordering {
    if Arc::ptr_eq(&a.0, &b.0) {
        return Ordering::Equal;
    }
    let c = a.digest().cmp(&b.digest());
    if c != Ordering::Equal {
        return c;
    }
    let (p, q) = match (&*a.0, &*b.0) {
        (Node::Parts(p, _), Node::Parts(q, _)) => (p, q),
        (Node::Parts(..), Node::Rec(_)) => return Ordering::Less,
        (Node::Rec(_), Node::Parts(..)) => return Ordering::Greater,
        (Node::Rec(r), Node::Rec(s)) => {
            // The types inside the keys that tie in digest wait on the stack, in order.
            let mut ties = Vec::new();
            let c = r.key.order(&s.key, &mut ties);
            if c.is_eq() {
                steps.extend(ties.into_iter().rev().map(|(x, y)| Step::Types(x, y)));
            }
            return c;
        }
    };
    let c = (p.digest.cmp(&q.digest))
        .then(p.bools.cmp(&q.bools))
        .then_with(|| p.ints.cmp(&q.ints))
        .then_with(|| p.rats.cmp(&q.rats))
        .then_with(|| p.floats.cmp(&q.floats))
        .then_with(|| p.strings.cmp(&q.strings))
        .then(p.atoms.cofinite.cmp(&q.atoms.cofinite));
    if c != Ordering::Equal {
        return c;
    }
    let n = steps.len();
    let names = (&p.atoms.names, &q.atoms.names);
    let c = atom_names(names, Bound::Unbounded, steps);
    if c != Ordering::Equal {
        return c;
    }
    let sum = (p.atoms.sum.cmp(&q.atoms.sum)).then(p.tuples.rest.cmp(&q.tuples.rest));
    let lens = (&p.tuples.lens, &q.tuples.lens);
    if steps.len() > n {
        // A payload ties in digest: the fields after the atoms wait below its contents.
        steps.splice(
            n..n,
            [
                Step::Arrows(Walk::Parts(&p.morphisms, &q.morphisms)),
                Step::Is(p.structs.cmp(&q.structs)),
                Step::Lens(lens.0, lens.1, Bound::Unbounded),
                Step::Is(sum),
            ],
        );
        return Ordering::Equal;
    }
    if sum != Ordering::Equal {
        return sum;
    }
    let c = tuple_lens(lens, Bound::Unbounded, steps, equal);
    if c != Ordering::Equal {
        return c;
    }
    if steps.len() > n {
        // A part ties in digest: the fields after the tuples wait below its contents.
        steps.splice(
            n..n,
            [
                Step::Arrows(Walk::Parts(&p.morphisms, &q.morphisms)),
                Step::Is(p.structs.cmp(&q.structs)),
            ],
        );
        return Ordering::Equal;
    }
    p.structs
        .cmp(&q.structs)
        .then_with(|| walk(Walk::Parts(&p.morphisms, &q.morphisms), steps, equal))
}

/// One step of [`order`] on the atom names of two types after `from`, each with its part, read
/// at once where the names, the bare atoms or the payloads' digests decide them; at the first
/// payload that ties in digest, the rest of the names is pushed (as the last name read) and the
/// two payloads above it. Resuming takes `O(log n)` in the names, read only after a nested
/// comparison.
fn atom_names<'a>(
    (p, q): (&'a AtomNames, &'a AtomNames),
    from: Bound<&'a Arc<str>>,
    steps: &mut Vec<Step<'a>>,
) -> Ordering {
    // Complexity tradeoff: a step resumes by a search, O(log n) in the names, after a nested
    // comparison of at least that cost, rather than holding two iterators, which made each step
    // 208 bytes and the bytes a comparison allocates on ties more than 24x at 8n in the pinwheel
    // tests of `l01_23` (short-addresses build).
    let (mut x, mut y) = (
        p.range::<_, Arc<str>>((from, Bound::Unbounded)),
        q.range::<_, Arc<str>>((from, Bound::Unbounded)),
    );
    loop {
        match (x.next(), y.next()) {
            (Some((k, u)), Some((l, v))) => {
                let c = k.cmp(l).then(u.bare.cmp(&v.bare));
                if c != Ordering::Equal {
                    return c;
                }
                if Arc::ptr_eq(&u.payload.0, &v.payload.0) {
                    continue;
                }
                let c = u.payload.digest().cmp(&v.payload.digest());
                if c == Ordering::Equal {
                    steps.extend([
                        Step::Names(p, q, Bound::Excluded(k)),
                        Step::Types(&u.payload, &v.payload),
                    ]);
                }
                return c;
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
}

/// One step of [`order`] on the tuple lengths of two types after `from`, each with its part,
/// read at once where the lengths or the parts' digests decide them; at the first pair of parts
/// that ties in digest, the rest of the lengths is pushed (as the last length read) below what
/// [`walk`] pushed. Resuming takes `O(log n)` in the lengths, read only after a nested
/// comparison.
fn tuple_lens<'a>(
    (p, q): (&'a Lens, &'a Lens),
    from: Bound<usize>,
    steps: &mut Vec<Step<'a>>,
    equal: &HashSet<(u64, u64)>,
) -> Ordering {
    // Complexity tradeoff: as in `atom_names`, O(log n) to resume against a step a fifth the size.
    let (mut x, mut y) = (
        p.range((from, Bound::Unbounded)),
        q.range((from, Bound::Unbounded)),
    );
    loop {
        match (x.next(), y.next()) {
            (Some((k, s)), Some((l, t))) => {
                let c = k.cmp(l);
                if c != Ordering::Equal {
                    return c;
                }
                let n = steps.len();
                let c = walk(Walk::Parts(s, t), steps, equal);
                if c != Ordering::Equal {
                    return c;
                }
                if steps.len() > n {
                    steps.insert(n, Step::Lens(p, q, Bound::Excluded(*k)));
                    return Ordering::Equal;
                }
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
}

/// One step of [`order`] on two diagrams, expressions or parts of one universe.
fn walk<'a, A: Literal>(
    w: Walk<'a, A>,
    steps: &mut Vec<Step<'a>>,
    equal: &HashSet<(u64, u64)>,
) -> Ordering {
    match w {
        Walk::Parts(Part::Bdd(a), Part::Bdd(b)) => walk(Walk::Bdds(a, b), steps, equal),
        Walk::Parts(Part::Expr(a), Part::Expr(b)) => walk(Walk::Exprs(a, b), steps, equal),
        Walk::Parts(Part::Bdd(_), Part::Expr(_)) => Ordering::Less,
        Walk::Parts(Part::Expr(_), Part::Bdd(_)) => Ordering::Greater,
        Walk::Bdds(Bdd::Leaf(a), Bdd::Leaf(b)) => a.cmp(b),
        Walk::Bdds(Bdd::Leaf(_), Bdd::List(..)) => Ordering::Less,
        Walk::Bdds(Bdd::List(..), Bdd::Leaf(_)) => Ordering::Greater,
        Walk::Bdds(x @ Bdd::List(a, v), y @ Bdd::List(b, w)) => {
            let c = x.digest().cmp(&y.digest()).then(v.cmp(w));
            if c != Ordering::Equal {
                return c;
            }
            walk(Walk::Cells(Some(a), Some(b)), steps, equal)
        }
        Walk::Cells(None, None) | Walk::Sets(None, None) => Ordering::Equal,
        Walk::Cells(None, Some(_)) | Walk::Sets(None, Some(_)) => Ordering::Less,
        Walk::Cells(Some(_), None) | Walk::Sets(Some(_), None) => Ordering::Greater,
        Walk::Cells(Some(a), Some(b)) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let c = a.digest.cmp(&b.digest);
            if c == Ordering::Equal {
                // The blocks are pushed last, so they are compared first.
                steps.extend([
                    Step::Equal(key.0, key.1),
                    A::walk(Walk::Cells(a.next.as_deref(), b.next.as_deref())),
                    A::walk(Walk::Sets(Some(&a.block), Some(&b.block))),
                ]);
            }
            c
        }
        Walk::Sets(Some(a), Some(b)) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let c = a.digest.cmp(&b.digest).then(a.key.1.cmp(&b.key.1));
            if c == Ordering::Equal {
                // The atoms are pushed last, so they are compared first, then the left sets.
                steps.extend([
                    Step::Equal(key.0, key.1),
                    A::walk(Walk::Sets(a.right.as_deref(), b.right.as_deref())),
                    A::walk(Walk::Sets(a.left.as_deref(), b.left.as_deref())),
                    A::atoms(&a.key.0, &b.key.0),
                ]);
            }
            c
        }
        Walk::Exprs(a, b) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let (x, y) = (a.form.operands(), b.form.operands());
            let c = a.digest.cmp(&b.digest).then_with(|| x.0.cmp(&y.0));
            if c == Ordering::Equal {
                steps.push(Step::Equal(key.0, key.1));
                if let (Some(p), Some(q)) = (x.2, y.2) {
                    steps.push(A::walk(Walk::Parts(p, q)));
                }
                steps.push(A::walk(Walk::Parts(x.1, y.1)));
            }
            c
        }
    }
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
        order(A::walk(Walk::Parts(self, other)))
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
        order(A::walk(Walk::Exprs(self, other)))
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
        order(A::walk(Walk::Bdds(self, other)))
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
            .spawn(|| {
                // Built from its literals by the connectives: `w` is atom 0, `z` atom `m + 1`.
                let chain = |m: usize| {
                    let xs: Vec<Row> = (0..m as u64 + 2).map(atom).collect();
                    let lit = |k: usize| Part::literal(xs[k].clone());
                    let meet = (2..=m).fold(lit(1), |g, k| g.zip(&lit(k), Op::And));
                    let g = meet.zip(&lit(m + 1), Op::Or);
                    (lit(0).zip(&g, Op::And), xs[0].clone())
                };
                let n = 1 << 12;
                let built = scaling::inputs(n, chain);
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
    fn forced_atoms_of_a_long_conjunction_scale() {
        // `x_0 ∧ x_1 ∧ … ∧ x_{m-1}`, every third literal refused, kept as expressions: built one
        // literal at a time, and as a balanced tree, whose meets join two large sets. A pass that
        // copied the settings found so far at each conjunction took 12.5 ms at 512 literals and
        // 760 ms at 4096 (cross-review XR3, R3_CODEX.md Q7).
        let lit = |i: usize| {
            let l = Part::literal(atom(i as u64));
            if i % 3 == 2 { l.not() } else { l }
        };
        let and = |a: Part<Row>, b: Part<Row>| Part::expr(Form::And(a, b));
        let deep = |m: usize| (1..m).fold(lit(0), |p, i| and(p, lit(i)));
        let balanced = |m: usize| {
            let mut level: Vec<Part<Row>> = (0..m).map(lit).collect();
            while level.len() > 1 {
                let mut next = Vec::with_capacity(level.len().div_ceil(2));
                let mut it = level.into_iter();
                while let Some(a) = it.next() {
                    next.push(match it.next() {
                        Some(b) => and(a, b),
                        None => a,
                    });
                }
                level = next;
            }
            level.pop().expect("one literal at least")
        };
        let expected = |m: usize| {
            let (mut taken, mut refused): (Vec<Row>, Vec<Row>) = (Vec::new(), Vec::new());
            for i in 0..m {
                if i % 3 == 2 { &mut refused } else { &mut taken }.push(atom(i as u64));
            }
            taken.sort();
            refused.sort();
            (taken, refused)
        };
        let sorted = |(mut t, mut r): (Vec<Row>, Vec<Row>)| {
            t.sort();
            r.sort();
            (t, r)
        };
        assert_eq!(sorted(lit(0).forced()), expected(1), "one literal");
        assert_eq!(
            sorted(deep(7).forced()),
            expected(7),
            "seven, one at a time"
        );
        assert_eq!(sorted(balanced(7).forced()), expected(7), "seven, balanced");
        // A conjunction holding an atom both ways holds nowhere: every atom is then forced.
        let empty = and(deep(5), Part::literal(atom(0)).not());
        let (t, r) = empty.forced();
        assert_eq!(t.len() + r.len(), 5, "{empty:?}");
        let n = 1 << 11;
        let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (deep(m), balanced(m))))
            .collect();
        for (&m, (deep, balanced)) in &built {
            assert_eq!(sorted(deep.forced()), expected(m), "{m}, one at a time");
            assert_eq!(sorted(balanced.forced()), expected(m), "{m}, balanced");
        }
        scaling::check(
            "the forced atoms of a conjunction, by its literals",
            n,
            |m| {
                let (deep, balanced) = &built[&m];
                std::hint::black_box((deep.forced(), balanced.forced()));
            },
        );
    }

    #[test]
    fn two_exclusive_ors_on_disjoint_atoms_meet_in_an_expression() {
        // With the atoms in the order `a < b < c < d`, the diagrams of `a xor c` and `b xor d`
        // have three nodes each and no atom in common, and their meet has nine: disjoint atoms
        // bound a meet by the sum of the sizes only when one diagram's atoms all come before
        // the other's (cross-review XR3, R3_CODEX.md Q1). An exclusive or is no decision list,
        // so `Part::zip` keeps each, and their meet, as expressions.
        let oxor = |p: &Old, q: &Old| {
            (p.apply(&q.not(), Op::And)).apply(&p.not().apply(q, Op::And), Op::Or)
        };
        let (a, b) = (
            oxor(&Old::literal(0), &Old::literal(2)),
            oxor(&Old::literal(1), &Old::literal(3)),
        );
        assert_eq!(
            (a.nodes(), b.nodes(), a.apply(&b, Op::And).nodes()),
            (3, 3, 9)
        );
        let lit = |i: u64| Part::literal(atom(i));
        let xor = |p: Part<Row>, q: Part<Row>| {
            p.zip(&q.not(), Op::And)
                .zip(&p.not().zip(&q, Op::And), Op::Or)
        };
        let (pa, pb) = (xor(lit(0), lit(2)), xor(lit(1), lit(3)));
        let kept = pa.zip(&pb, Op::And);
        assert!(matches!(kept, Part::Expr(_)), "{kept:?}");
        for set in 0..16u32 {
            let holds = |t: &Row| (0..4).any(|i| set >> i & 1 == 1 && *t == atom(i));
            let bit = |i: u32| set >> i & 1 == 1;
            assert_eq!(kept.eval(&holds), (bit(0) != bit(2)) && (bit(1) != bit(3)));
        }
    }

    #[test]
    fn comparing_equal_expressions_built_apart_scales() {
        // `x_{k+1} = x_k & !x_k`, built twice: both operands of each level lead to the level
        // below, so comparing operand by operand met the bottom `2^depth` times.
        std::thread::Builder::new()
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
    fn comparing_equal_lists_built_on_two_threads_scales() {
        // A list of `m` literals in blocks of two of alternating values. Each thread has its
        // own tables of cells and sets, so the two lists share no node, and comparing them
        // reads each pair of cells and of set nodes once. (The parity of `m` atoms, a diagram
        // the lists no longer build, met its last atom `2^m` times when compared `hi` then
        // `lo`.)
        let blocks = |m: usize| {
            let mut b = Bdd::Leaf(false);
            for i in 0..m {
                let k = (atom(i as u64), true);
                b = if (i / 2) % 2 == 0 {
                    b.or_literal(k)
                } else {
                    b.and_literal(k)
                };
            }
            Part::Bdd(b)
        };
        let n = 1 << 10;
        let on_a_thread = |m: usize| std::thread::spawn(move || blocks(m)).join().unwrap();
        let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (on_a_thread(m), on_a_thread(m))))
            .collect();
        scaling::check(
            "comparing equal lists built on two threads, by literals",
            n,
            |m| {
                let (a, b) = &built[&m];
                assert_eq!(a.cmp(b), Ordering::Equal);
            },
        );
    }

    /// A decision list's blocks with each block's literals sorted, and its default.
    type Blocks = (Vec<(bool, Vec<(Row, bool)>)>, bool);

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

    /// The one form of the decision list of `f`, a function of the atoms `atom(0..6)` given
    /// by its value on each set of them, found from the values alone: the literals under which
    /// the function is constant, a block, then those once the block's literals are false, and
    /// so on (module `list`). `None` when the function is no decision list.
    fn list_of_values(f: impl Fn(u32) -> bool) -> Option<Blocks> {
        // The value when the atoms of `fixed` are fixed to theirs, if one.
        let constant = |fixed: &[Option<bool>; 6]| {
            let mut seen = [false; 2];
            for set in 0..64u32 {
                let agrees = (0..6).all(|i| fixed[i].is_none_or(|b| b == (set >> i & 1 == 1)));
                if agrees {
                    seen[usize::from(f(set))] = true;
                }
            }
            match seen {
                [true, false] => Some(false),
                [false, true] => Some(true),
                _ => None,
            }
        };
        let mut fixed = [None; 6];
        let mut blocks = Vec::new();
        loop {
            if let Some(v) = constant(&fixed) {
                return Some((blocks, v));
            }
            let mut lits = Vec::new();
            for i in 0..6 {
                for taken in [true, false] {
                    if fixed[i].is_some() {
                        continue;
                    }
                    let mut f = fixed;
                    f[i] = Some(taken);
                    if let Some(c) = constant(&f) {
                        lits.push((i, taken, c));
                    }
                }
            }
            if lits.is_empty() {
                return None;
            }
            // Literals of both values are one atom's two: the list of one literal, `true`.
            let v = lits.iter().any(|l| l.2);
            let mut block: Vec<(Row, bool)> = Vec::new();
            for &(i, taken, c) in &lits {
                if c == v {
                    fixed[i] = Some(!taken);
                    block.push((atom(i as u64), taken));
                }
            }
            block.sort();
            blocks.push((v, block));
        }
    }

    /// The construction the lists replaced, kept to check them against: a reduced ordered
    /// diagram on the atoms `atom(0..6)` in the order of their indices, two diagrams joined
    /// by `apply`, which builds `O(n²)` nodes for a decision list of `n` literals in the worst
    /// atom order. Small sizes only: the walks recurse and share no node.
    mod old {
        use super::Op;
        use std::rc::Rc;

        #[derive(Clone, PartialEq, Eq, Hash, Debug)]
        pub(super) enum Old {
            Leaf(bool),
            Node(Rc<(usize, Old, Old)>),
        }

        impl Old {
            pub(super) fn node(i: usize, hi: Old, lo: Old) -> Old {
                if hi == lo {
                    hi
                } else {
                    Old::Node(Rc::new((i, hi, lo)))
                }
            }

            pub(super) fn literal(i: usize) -> Old {
                Old::node(i, Old::Leaf(true), Old::Leaf(false))
            }

            fn top(&self) -> usize {
                match self {
                    Old::Leaf(_) => usize::MAX,
                    Old::Node(n) => n.0,
                }
            }

            /// The diagram with atom `i` fixed to `true`, and to `false`; `i` is at or above
            /// the root's atom.
            fn cofactors(&self, i: usize) -> (Old, Old) {
                match self {
                    Old::Node(n) if n.0 == i => (n.1.clone(), n.2.clone()),
                    _ => (self.clone(), self.clone()),
                }
            }

            pub(super) fn apply(&self, other: &Old, op: Op) -> Old {
                if let (Old::Leaf(a), Old::Leaf(b)) = (self, other) {
                    return Old::Leaf(match op {
                        Op::Or => a | b,
                        Op::And => a & b,
                    });
                }
                let i = self.top().min(other.top());
                let ((a1, a0), (b1, b0)) = (self.cofactors(i), other.cofactors(i));
                Old::node(i, a1.apply(&b1, op), a0.apply(&b0, op))
            }

            pub(super) fn not(&self) -> Old {
                match self {
                    Old::Leaf(b) => Old::Leaf(!b),
                    Old::Node(n) => Old::node(n.0, n.1.not(), n.2.not()),
                }
            }

            pub(super) fn restrict(&self, fixed: &[Option<bool>; 6]) -> Old {
                match self {
                    Old::Leaf(_) => self.clone(),
                    Old::Node(n) => match fixed[n.0] {
                        Some(true) => n.1.restrict(fixed),
                        Some(false) => n.2.restrict(fixed),
                        None => Old::node(n.0, n.1.restrict(fixed), n.2.restrict(fixed)),
                    },
                }
            }

            /// The value on the set of atoms whose indices are the bits of `set`.
            pub(super) fn eval(&self, set: u32) -> bool {
                match self {
                    Old::Leaf(b) => *b,
                    Old::Node(n) if set >> n.0 & 1 == 1 => n.1.eval(set),
                    Old::Node(n) => n.2.eval(set),
                }
            }

            /// The number of distinct nodes.
            pub(super) fn nodes(&self) -> usize {
                let mut seen = std::collections::HashSet::new();
                let mut stack = vec![self];
                while let Some(d) = stack.pop() {
                    if let Old::Node(n) = d
                        && seen.insert(d.clone())
                    {
                        stack.extend([&n.1, &n.2]);
                    }
                }
                seen.len()
            }
        }
    }
    use old::Old;

    #[test]
    fn lists_agree_with_the_diagrams_apply_built() {
        // Random lists built by the connectives on lists (complement, a chain joined, a
        // restriction) and, beside each, the diagram the old construction builds. They agree
        // on every set of atoms; the list is the one form of its function, found from its
        // values; two lists of one function are one list, however they were built; and the
        // three-valued value, the forced atoms and the first node each agree with the values.
        let holds = |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
        let mut pool: Vec<(Bdd<Row>, Old)> = (0..6)
            .map(|i| (Bdd::literal(atom(i as u64)), Old::literal(i)))
            .chain([false, true].map(|b| (Bdd::Leaf(b), Old::Leaf(b))))
            .collect();
        // The id of the one list of each function, by its values.
        let mut ids: HashMap<u64, u64> = HashMap::new();
        let mut seed = 5u64;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };
        let (mut joined, mut found_again) = (0, 0);
        for _ in 0..20_000 {
            let r = next() as usize;
            let (a, x) = pool[r % pool.len()].clone();
            let (b, y) = pool[next() as usize % pool.len()].clone();
            let op = if (r / pool.len()).is_multiple_of(2) {
                Op::Or
            } else {
                Op::And
            };
            let made = match r / pool.len() / 2 % 4 {
                0 => (a.not(), x.not()),
                3 => {
                    let mut fixed = [None; 6];
                    for f in &mut fixed {
                        *f = [None, None, Some(false), Some(true)][next() as usize % 4];
                    }
                    let fix = |t: &Row| {
                        (0..6)
                            .find(|&i| *t == atom(i as u64))
                            .and_then(|i| fixed[i])
                    };
                    (a.restrict(&fix, &mut HashMap::new()), x.restrict(&fixed))
                }
                _ => match a.zip_chain(&b, op) {
                    Some(z) => {
                        joined += 1;
                        (z, x.apply(&y, op))
                    }
                    None => continue,
                },
            };
            let (z, d) = made;
            let values: u64 = (0..64).filter(|&s| d.eval(s)).fold(0, |m, s| m | 1 << s);
            for set in 0..64u32 {
                assert_eq!(z.eval(holds(set)), d.eval(set), "{z:?} at {set:b}");
            }
            let id = *ids.entry(values).or_insert_with(|| z.id());
            found_again += usize::from(id == z.id() && pool.iter().any(|(p, _)| p.id() == id));
            assert_eq!(id, z.id(), "two lists of one function: {z:?}");
            assert_eq!(
                Some(sorted(z.list())),
                list_of_values(|s| d.eval(s)),
                "the list of {z:?}"
            );
            // Three-valued: known when every set agreeing with what is known has one value.
            for _ in 0..8 {
                let (known, fixed) = (next() as u32 % 64, next() as u32 % 64);
                let fix = |t: &Row| {
                    (0..6)
                        .find(|&i| *t == atom(i as u64) && known >> i & 1 == 1)
                        .map(|i| fixed >> i & 1 == 1)
                };
                let agreeing: Vec<bool> = (0..64u32)
                    .filter(|s| (s ^ fixed) & known == 0)
                    .map(|s| d.eval(s))
                    .collect();
                let expected = (agreeing.iter().all(|&v| v == agreeing[0])).then_some(agreeing[0]);
                assert_eq!(z.eval3(&fix), expected, "{z:?}");
            }
            // Forced: the atoms in every set of value `true`, and those in none; none when
            // there is no such set, as the diagram's walk found.
            let inside: Vec<u32> = (0..64).filter(|&s| d.eval(s)).collect();
            let (mut taken, mut refused) = (Vec::new(), Vec::new());
            if !inside.is_empty() {
                for i in 0..6 {
                    if inside.iter().all(|s| s >> i & 1 == 1) {
                        taken.push(atom(i as u64));
                    } else if inside.iter().all(|s| s >> i & 1 == 0) {
                        refused.push(atom(i as u64));
                    }
                }
            }
            taken.sort();
            refused.sort();
            assert_eq!(z.forced(), (taken.clone(), refused.clone()), "{z:?}");
            let (mut t, mut f) = Part::Bdd(z.clone()).forced();
            t.sort();
            f.sort();
            assert_eq!((t, f), (taken, refused), "{z:?}");
            // The first node: the list is its `hi` where its atom holds, its `lo` elsewhere.
            if let Ok((_, a, hi, lo)) = z.branch() {
                for set in 0..64u32 {
                    let h = holds(set);
                    let by_node = if h(a) { hi.eval(h) } else { lo.eval(h) };
                    assert_eq!(by_node, z.eval(h), "{z:?} at {set:b}");
                }
            }
            pool.push((z, d));
        }
        assert!(
            joined > 5000 && found_again > 5000,
            "{joined} {found_again}"
        );
    }

    #[test]
    fn list_matches_the_one_form_found_from_its_values() {
        let mut seed = 11;
        let mut lists = 0;
        for _ in 0..4000 {
            let Part::Bdd(b) = random(&mut seed, 6) else {
                continue;
            };
            let holds =
                |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
            let expected = list_of_values(|s| b.eval(holds(s)));
            assert_eq!(Some(sorted(b.list())), expected, "the list of {b:?}");
            lists += 1;
        }
        assert!(lists > 1000, "{lists} lists");
    }

    #[test]
    fn list_of_a_literal_and_its_complement() {
        let y = Bdd::literal(atom(1));
        assert_eq!(y.list().blocks, vec![(true, vec![(atom(1), true)])]);
        assert!(!y.list().tail);
        assert_eq!(y.not().list().blocks, vec![(true, vec![(atom(1), false)])]);
        assert!(!y.not().list().tail);
        assert_eq!(y.not().not(), y);
    }

    #[test]
    fn list_of_alternating_literals_scales() {
        // `((x0 | x1) & !x2 | x3) & !x4 …`, each new literal first in the order, so every
        // literal is a block of its own: finding the blocks one by one took a pass over the
        // diagram's nodes per block.
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
                unreachable!("a literal joined to a list is a list")
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
                assert!(!l.tail);
            },
        );
    }

    #[test]
    fn joining_chains_to_lists_scales() {
        // `((x_0 | x_1) & !x_2 | x_3) & !x_4 …` built a literal at a time, each new literal last
        // in the order of the atoms: the diagram the chain rule built had up to `k` nodes on
        // the `k`-th atom, `O(m²)` in all, and built them all again at each literal (the
        // negative control in STATUS.md, CHAIN-zip-size). A list takes each literal into its
        // first block, or a block of its own, in `O(log m)`. Two chains with half their atoms
        // in common are joined a literal of the shorter at a time.
        let n = 1 << 11;
        let lits = scaling::inputs(n, |m| {
            let mut xs: Vec<Row> = (0..m as u64).map(atom).collect();
            xs.sort();
            let lits: Vec<(Part<Row>, Part<Row>)> = xs
                .into_iter()
                .map(|x| (Part::literal(x.clone()), Part::literal(x).not()))
                .collect();
            lits
        });
        let chains = scaling::inputs(n, |m| {
            let chain = |from: u64| {
                (from..from + m as u64).fold(Part::leaf(false), |f, k| {
                    f.zip(&Part::literal(atom(k)), Op::Or)
                })
            };
            (chain(0), chain(m as u64 / 2))
        });
        scaling::check("a list built a literal at a time, by literals", n, |m| {
            let xs = &lits[&m];
            let f =
                (xs[1..].iter().enumerate()).fold(xs[0].0.clone(), |f, (i, (x, not_x))| {
                    match i % 2 {
                        0 => f.zip(x, Op::Or),
                        _ => f.zip(not_x, Op::And),
                    }
                });
            assert!(matches!(f, Part::Bdd(_)), "{f:?}");
        });
        // A chain grown a literal at a time stays a chain, so both operands of each step are
        // chains; listing the long one too at each step took `O(m²)` (59 s for the forced atoms
        // of a chain of 32768 literals).
        for op in [Op::Or, Op::And] {
            scaling::check("a chain built a literal at a time, by literals", n, |m| {
                let xs = &lits[&m];
                let f = (xs[1..].iter()).fold(xs[0].0.clone(), |f, (x, _)| f.zip(x, op));
                assert!(
                    matches!(&f, Part::Bdd(b) if b.chain_len(op) == Some(m)),
                    "{f:?}"
                );
            });
        }
        scaling::check(
            "the union of two chains with half their atoms in common, by literals",
            n,
            |m| {
                let (a, b) = &chains[&m];
                assert!(a.zip(b, Op::Or) != *a);
            },
        );
    }

    /// `p ^ q` as the type operations build it: `p&!q | !p&q`.
    fn xor_by_or(p: &Part<Row>, q: &Part<Row>) -> Part<Row> {
        let left = p.zip(&q.not(), Op::And);
        left.zip(&p.not().zip(q, Op::And), Op::Or)
    }

    /// `p ^ q` as `(p|q) & (!p|!q)`.
    fn xor_by_and(p: &Part<Row>, q: &Part<Row>) -> Part<Row> {
        let left = p.zip(q, Op::Or);
        left.zip(&p.not().zip(&q.not(), Op::Or), Op::And)
    }

    /// Whether the set `bits` has an odd number of the atoms `0..k`.
    fn odd(bits: u32, k: u32) -> bool {
        (bits & ((1 << k) - 1)).count_ones() % 2 == 1
    }

    #[test]
    fn exclusive_ors_built_in_any_order_are_one_node() {
        let lits: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
        let fold = |order: &[usize], by: fn(&Part<Row>, &Part<Row>) -> Part<Row>| {
            (order.iter()).fold(Part::leaf(false), |f, &i| by(&f, &lits[i]))
        };
        let holds = |bits: u32| move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(i));
        let forward = fold(&[0, 1, 2, 3, 4, 5], xor_by_or);
        assert!(forward.xor_tag().is_some(), "{forward:?}");
        for bits in 0..64 {
            assert_eq!(forward.eval(&holds(bits)), odd(bits, 6), "{bits:b}");
        }
        for order in [[5, 4, 3, 2, 1, 0], [2, 0, 5, 1, 3, 4], [3, 5, 1, 0, 4, 2]] {
            assert_eq!(fold(&order, xor_by_or).id(), forward.id(), "{order:?}");
            assert_eq!(fold(&order, xor_by_and).id(), forward.id(), "{order:?}");
        }
        // Two halves joined, and a literal's complement taken in.
        let halves = xor_by_or(&fold(&[0, 2, 4], xor_by_or), &fold(&[5, 3, 1], xor_by_and));
        assert_eq!(halves.id(), forward.id());
        let flipped = (1..6).fold(lits[0].not(), |f, i| xor_by_or(&f, &lits[i]));
        assert_eq!(flipped.id(), forward.not().id());
        for bits in 0..64 {
            assert_eq!(flipped.eval(&holds(bits)), !odd(bits, 6), "{bits:b}");
        }
        // An atom taken twice leaves; all taken twice leave nothing.
        let twice = xor_by_or(&forward, &lits[3]);
        assert_eq!(twice.id(), fold(&[0, 1, 2, 4, 5], xor_by_or).id());
        assert_eq!(xor_by_and(&forward, &forward.not()).is_leaf(), Some(true));
        // The choice `c&x | !c&!x`, `!(c ^ x)`.
        let (c, x) = (fold(&[0, 1], xor_by_or), fold(&[2, 3, 4, 5], xor_by_or));
        let choice = xor::xor_choice(&c, &x, &x.not()).expect("an exclusive or of two");
        assert_eq!(choice.id(), forward.not().id());
        // Restricted to one atom's value, an exclusive or is the one of the others.
        let fixed = forward.restrict(&|a: &Row| (*a == atom(2)).then_some(true));
        assert_eq!(fixed.id(), fold(&[0, 1, 3, 4, 5], xor_by_or).not().id());
    }

    #[test]
    fn exclusive_ors_agree_with_their_values() {
        // Random parts over six atoms, each built with its set of values beside it as a mask of
        // the 64 assignments; exclusive ors in their one form of one function are one node.
        let lits: Vec<(Part<Row>, u64)> = (0..6)
            .map(|i| {
                let mask = (0..64u32).filter(|b| b >> i & 1 == 1);
                (Part::literal(atom(i)), mask.fold(0u64, |m, b| m | 1 << b))
            })
            .collect();
        let holds = |bits: u32| move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(i));
        let mut pool: Vec<(Part<Row>, u64)> = lits.clone();
        let mut ids: HashMap<u64, u64> = HashMap::new();
        let mut seed = 7u64;
        for _ in 0..4000 {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let pick = (seed >> 33) as usize;
            let (p, pm) = pool[pick % pool.len()].clone();
            let (q, qm) = pool[(pick / 7) % pool.len()].clone();
            let made = match pick % 5 {
                0 => (xor_by_or(&p, &q), pm ^ qm),
                1 => (xor_by_and(&p, &q), pm ^ qm),
                2 => (p.not(), !pm),
                3 => (p.zip(&q, Op::And), pm & qm),
                _ => (p.zip(&q, Op::Or), pm | qm),
            };
            for bits in 0..64 {
                assert_eq!(made.0.eval(&holds(bits)), made.1 >> bits & 1 == 1);
            }
            if made.0.xor_tag().is_some() {
                assert_eq!(*ids.entry(made.1).or_insert(made.0.id()), made.0.id());
            }
            if pool.len() < 200 {
                pool.push(made);
            } else {
                pool[pick % 200] = made;
            }
        }
        assert!(ids.len() >= 10, "{}", ids.len());
    }

    #[test]
    fn exclusive_ors_scale() {
        // Parity built a literal at a time, as the type operations build it: each step takes a
        // literal into the set of the one form in `O(log n)`, and makes the expressions of the
        // `O(log n)` new tree nodes. Two halves of `n` atoms each are joined in `O(n log n)`.
        // Each size has atoms of its own.
        let n = 1 << 10;
        let lits = scaling::inputs(n, |m| {
            (0..m as u64)
                .map(|i| Part::literal(atom(16 * m as u64 + i)))
                .collect::<Vec<_>>()
        });
        scaling::check("parity built a literal at a time, by literals", n, |m| {
            let x = (lits[&m].iter()).fold(Part::leaf(false), |f, l| xor_by_or(&f, l));
            assert!(x.xor_tag().is_some());
        });
        let halves = scaling::inputs(n, |m| {
            let ls = &lits[&m];
            let half = |r: std::ops::Range<usize>| {
                ls[r]
                    .iter()
                    .fold(Part::leaf(false), |f, l| xor_by_or(&f, l))
            };
            (half(0..m / 2), half(m / 4..m))
        });
        scaling::check(
            "two exclusive ors with half their atoms in common joined, by literals",
            n,
            |m| {
                let (a, b) = &halves[&m];
                assert!(xor_by_and(a, b).xor_tag().is_some());
            },
        );
    }

    /// `depth` levels of the atom `#a` with a payload of the level below, over `bottom`, every
    /// digest 0: comparing two of them reads every level, as two types whose digests tie at
    /// every depth are read in the short-addresses build (SHORT-stack-l01_22).
    fn tied(bottom: &str, depth: usize) -> Type {
        let zeroed = |t: Type| {
            let Node::Parts(p, _) = &*t.0 else {
                unreachable!("an atom type is no recursive node")
            };
            let mut p = p.clone();
            p.digest = 0;
            Type(Arc::new(Node::Parts(p, super::super::Shown::default())))
        };
        let mut t = zeroed(Type::atom(bottom));
        for _ in 0..depth {
            let Node::Parts(p, _) = &*Type::atom("a").0 else {
                unreachable!("an atom type is no recursive node")
            };
            let mut p = p.clone();
            p.digest = 0;
            p.atoms.names = p.atoms.names.update(
                "a".into(),
                AtomPart {
                    bare: false,
                    payload: t,
                },
            );
            t = Type(Arc::new(Node::Parts(p, super::super::Shown::default())));
        }
        t
    }

    #[test]
    fn types_whose_digests_tie_at_every_depth_are_ordered_on_a_small_stack() {
        // The order reads such types n levels down. It was a recursion, which overflowed this
        // 2 MiB stack a few thousand levels down; it is a loop with a stack of its own.
        std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(|| {
                let depth = 100_000;
                let (a, b, c) = (tied("z", depth), tied("z", depth), tied("y", depth));
                assert_eq!(a.digest(), c.digest());
                assert_eq!(a.cmp(&b), Ordering::Equal);
                assert_eq!(a, b);
                // The bottoms differ: `#y` before `#z`, read 100,000 levels down.
                assert_eq!(a.cmp(&c), Ordering::Greater);
                assert_eq!(c.cmp(&a), Ordering::Less);
                // A chain that stops a level short has no payload where the other has one.
                let d = tied("z", depth - 1);
                assert_eq!(d.cmp(&a), a.cmp(&d).reverse());
                assert_ne!(d.cmp(&a), Ordering::Equal);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn ordering_types_whose_digests_tie_at_every_depth_scales() {
        // One step per level: the two chains are equal, so every level is read.
        let n = 10_000;
        let built: BTreeMap<usize, (Type, Type)> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (tied("z", m), tied("z", m))))
            .collect();
        scaling::check(
            "ordering two equal chains of tied digests, by depth",
            n,
            |m| {
                let (a, b) = &built[&m];
                assert_eq!(a.cmp(b), Ordering::Equal);
            },
        );
    }

    /// `x_0 | x_1 | … | x_{m-1}` as expressions nested `m - 1` deep, the first operand the
    /// deeper, each `x_k` the part `leaf` makes of the atom `base + k`.
    fn ors(base: u64, m: usize, leaf: impl Fn(Row) -> Part<Row>) -> Part<Row> {
        (1..m as u64).fold(leaf(atom(base)), |e, k| {
            Part::expr(Form::Or(e, leaf(atom(base + k))))
        })
    }

    /// `t | y_1 | … | y_{m-1}` as expressions nested `m - 1` deep, and `!t`: `t` is the
    /// complement of the atom `base` kept as an expression, and `y_k` the list of the
    /// atoms `base + 2k - 1` and `base + 2k`, which is no chain under `|`, so that no union
    /// rebuilt from them merges into a list. [`Part::settle`] pins `t` to `false` and
    /// rebuilds the `m - 1` expressions above it.
    fn settled_by_one_pin(base: u64, m: usize) -> Part<Row> {
        let t = Part::expr(Form::Not(Part::literal(atom(base))));
        let p = (1..m as u64).fold(t.clone(), |e, k| {
            let x = Bdd::literal(atom(base + 2 * k - 1));
            Part::expr(Form::Or(
                e,
                Part::Bdd(x.and_literal((atom(base + 2 * k), true))),
            ))
        });
        Part::expr(Form::And(p, Part::expr(Form::Not(t))))
    }

    /// The list `x_0 & x_1 & … & x_{m-1}`, one block of `m` literals, the atoms from `base`.
    fn meet(base: u64, m: usize) -> Bdd<Row> {
        (0..m as u64).fold(Bdd::Leaf(true), |b, k| {
            b.and_literal((atom(base + k), true))
        })
    }

    /// The walks on expressions and diagrams nested this deep, on a 2 MiB stack.
    const DEEP: usize = 100_000;

    #[test]
    fn the_walks_over_parts_nested_deep_run_on_a_small_stack() {
        // Each walk was a recursion, which overflowed this stack (see the negative control in
        // STATUS.md, T2-types-rest part 3); each is now a loop with a stack of its own.
        std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(|| {
                let p = ors(0, DEEP, Part::literal);
                assert_eq!(p.union_rows().map(|r| r.len()), Some(DEEP));
                assert!(!p.eval(&|_| false));
                assert!(p.eval(&|a| *a == atom(0)));
                assert_eq!(p.eval3(&|_| None), None);
                assert_eq!(p.eval3(&|a| Some(*a == atom(0))), Some(true));
                assert_eq!(p.distinct_atoms().len(), DEEP);
                assert_eq!(p.forced(), (Vec::new(), Vec::new()));
                let only = |x: Row| move |a: &Row| (*a != x).then_some(false);
                assert_eq!(p.restrict(&only(atom(0))), Part::literal(atom(0)));
                let q = settled_by_one_pin(0, DEEP);
                assert_eq!(q.settle().distinct_atoms().len(), 2 * (DEEP - 1));
                let b = Part::Bdd(meet(0, DEEP));
                assert_eq!(b.eval3(&|_| None), None);
                assert_eq!(b.eval3(&|_| Some(true)), Some(true));
                assert_eq!(b.distinct_atoms().len(), DEEP);
                assert_eq!(b.restrict(&|_| None), b);
                let all_but = |x: Row| move |a: &Row| (*a != x).then_some(true);
                assert_eq!(b.restrict(&all_but(atom(0))), Part::literal(atom(0)));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn the_walks_over_parts_scale() {
        let n = 1 << 12;
        let sizes = [n, scaling::FACTOR * n];
        let ors: BTreeMap<usize, Part<Row>> = sizes
            .map(|m| (m, ors(10 * m as u64, m, Part::literal)))
            .into();
        let pins: BTreeMap<usize, Part<Row>> = sizes
            .map(|m| (m, settled_by_one_pin(20 * m as u64, m)))
            .into();
        let meets: BTreeMap<usize, Part<Row>> =
            sizes.map(|m| (m, Part::Bdd(meet(30 * m as u64, m)))).into();
        scaling::check("eval of an expression, by depth", n, |m| {
            assert!(!ors[&m].eval(&|_| false));
        });
        scaling::check("eval3 of an expression and a diagram, by depth", n, |m| {
            assert_eq!(ors[&m].eval3(&|_| None), None);
            assert_eq!(meets[&m].eval3(&|_| None), None);
        });
        scaling::check(
            "the atoms of an expression and a diagram, by depth",
            n,
            |m| {
                assert_eq!(ors[&m].distinct_atoms().len(), m);
                assert_eq!(meets[&m].distinct_atoms().len(), m);
            },
        );
        scaling::check("the union's rows, by depth", n, |m| {
            assert_eq!(ors[&m].union_rows().map(|r| r.len()), Some(m));
        });
        scaling::check("the forced atoms of an expression, by depth", n, |m| {
            assert_eq!(ors[&m].forced(), (Vec::new(), Vec::new()));
        });
        scaling::check(
            "restricting an expression and a diagram, by depth",
            n,
            |m| {
                assert_eq!(ors[&m].restrict(&|_| Some(false)), Part::leaf(false));
                assert_eq!(meets[&m].restrict(&|_| None), meets[&m]);
            },
        );
        scaling::check("settling on one pin, by depth", n, |m| {
            assert_eq!(pins[&m].settle().distinct_atoms().len(), 2 * (m - 1));
        });
    }

    /// The list `x_0 & … & x_{m-2} & !x_{m-1}`, on the atoms of [`meet`]`(base, m)`, which
    /// meets it in no value: the meet of the two joins each literal of one to the other.
    fn meet_but_last(base: u64, m: usize) -> Bdd<Row> {
        let last = atom(base + m as u64 - 1);
        meet(base, m - 1).and_literal((last, false))
    }

    /// The choice `c_{m-1} & (… (c_1 & x_0 | !c_1 & y_1) …) | !c_{m-1} & y_{m-1}`, kept as
    /// expressions nested `m - 1` deep, each `c_k` the atom `base + k`, `x_0` the atom
    /// `base + m`, and `y_k` the atom `leaves + k`. Its complement, and its union with another
    /// such chain on the same conditions, are each built a level at a time, through the choice
    /// each level is.
    fn choices(base: u64, leaves: u64, m: usize) -> Part<Row> {
        (1..m as u64).fold(Part::literal(atom(base + m as u64)), |p, k| {
            let c = Part::literal(atom(base + k));
            Part::expr(Form::Or(
                Part::expr(Form::And(c.clone(), p)),
                Part::expr(Form::And(c.not(), Part::literal(atom(leaves + k)))),
            ))
        })
    }

    /// How deep the lists of the depth test go: the diagrams' `apply` and `flip`, as
    /// recursions, overflowed the 8 MiB stack of a main thread at 60,000 (and ran at 30,000).
    const DIAGRAM_DEPTH: usize = 100_000;

    /// How deep the choices of the depth test go: `Part::not` and `Part::zip`, as a mutual
    /// recursion through `choice`, `choice_of`, `same_as_not` and `choose`, overflowed the
    /// 8 MiB stack at 10,000 (and ran at 6,000).
    const CHOICE_DEPTH: usize = 20_000;

    #[test]
    fn the_connectives_on_parts_nested_deep_run_on_the_default_stack() {
        // On the test thread's own stack (2 MiB unless RUST_MIN_STACK says otherwise), a
        // quarter of the 8 MiB the depths above overflowed.
        let (a, b) = (meet(0, DIAGRAM_DEPTH), meet_but_last(0, DIAGRAM_DEPTH));
        assert_eq!(a.zip_chain(&b, Op::And), Some(Bdd::Leaf(false)));
        let not_a = a.not();
        assert_eq!(not_a.not(), a);
        assert_eq!(a.zip_chain(&not_a, Op::Or), Some(Bdd::Leaf(true)));
        let l = b.list();
        assert_eq!(l.blocks.len(), 1);
        assert_eq!(l.blocks[0].1.len(), DIAGRAM_DEPTH);
        let base = 10 * DIAGRAM_DEPTH as u64;
        let p = choices(base, base + 2 * CHOICE_DEPTH as u64, CHOICE_DEPTH);
        let q = choices(base, base + 4 * CHOICE_DEPTH as u64, CHOICE_DEPTH);
        let not_p = p.not();
        assert_eq!(not_p.not(), p);
        assert_eq!(p.zip(&not_p, Op::And), Part::leaf(false));
        let both = p.zip(&q, Op::Or);
        // Every condition and `x_0` held: both chains take the deepest branch, `x_0`.
        let deepest: BTreeSet<Row> = (1..=CHOICE_DEPTH as u64).map(|k| atom(base + k)).collect();
        assert!(p.eval(&|a| deepest.contains(a)));
        assert!(both.eval(&|a| deepest.contains(a)));
        // No condition held, and the top leaf of `q`: only `q` takes it.
        let top_of_q = atom(base + 4 * CHOICE_DEPTH as u64 + CHOICE_DEPTH as u64 - 1);
        assert!(both.eval(&|a| *a == top_of_q));
        assert!(!p.eval(&|a| *a == top_of_q));
    }

    #[test]
    fn the_connectives_on_parts_scale_by_depth() {
        // Inputs Θ(m) deep, built before any run is timed; each connective meets each node or
        // expression a constant number of times.
        let n = 1 << 12;
        let meets = scaling::inputs(n, |m| {
            let base = 100 * m as u64;
            (meet(base, m), meet_but_last(base, m))
        });
        // A union keeps the complements it makes with the expressions, so each run of it takes
        // chains of its own, on atoms of their own.
        let (small, large) = scaling::Meter::new().runs();
        type Pairs = std::sync::Mutex<Vec<(Part<Row>, Part<Row>)>>;
        let chains: BTreeMap<usize, Pairs> = [(n, small), (scaling::FACTOR * n, large)]
            .map(|(m, runs)| {
                let pairs = (0..runs as u64)
                    .map(|i| {
                        let base = (1000 + 10 * i) * m as u64;
                        (
                            choices(base, base + 2 * m as u64, m),
                            choices(base, base + 4 * m as u64, m),
                        )
                    })
                    .collect();
                (m, std::sync::Mutex::new(pairs))
            })
            .into();
        scaling::check("the meet of two lists, by depth", n, |m| {
            let (a, b) = &meets[&m];
            assert_eq!(a.zip_chain(b, Op::And), Some(Bdd::Leaf(false)));
        });
        // The complement flips the value of the first block and allocates nothing.
        scaling::check_instructions_only("the complement of a list, by depth", n, 1, |m| {
            assert!(meets[&m].0.not() != meets[&m].0);
        });
        scaling::check("the union of two chains of choices, by depth", n, |m| {
            let (p, q) = chains[&m]
                .lock()
                .expect("the chains of a size")
                .pop()
                .expect("a pair of chains per run");
            assert!(p.zip(&q, Op::Or) != p);
        });
    }

    /// The entries of this thread's tables of tuple nodes, in all: sets, cells and exclusive ors.
    fn entries() -> usize {
        Row::table(|t| t.sets.len() + t.cells.len() + t.xors.len())
    }

    /// The exclusive or of the atoms `base..base + k`.
    fn parity(base: u64, k: u64) -> Part<Row> {
        (base..base + k).fold(Part::leaf(false), |f, i| {
            xor_by_or(&f, &Part::literal(atom(i)))
        })
    }

    #[test]
    fn the_tables_keep_a_node_only_while_it_lives() {
        // Each table holds its nodes weakly, and a node leaves it when it is dropped (step
        // TABLE-life): the lists, sets, exclusive ors and complements of a unit leave no entry.
        let before = entries();
        {
            let x = parity(7000, 8);
            assert!(x.xor_tag().is_some());
            let parts = [x.not(), Part::Bdd(meet(7100, 64)), choices(7200, 7300, 16)];
            let nots: Vec<Part<Row>> = parts.iter().map(Part::not).collect();
            assert!(entries() > before);
            assert_eq!(nots[2].not().id(), parts[2].id());
        }
        assert_eq!(entries(), before);
    }

    #[test]
    fn a_node_rebuilt_after_its_drop_equals_the_first() {
        // While a node lives, building it again finds it; once dropped, it is built anew with
        // another id and the same contents.
        let first = meet(7400, 32);
        let (id, digest) = (first.id(), first.digest());
        assert_eq!(meet(7400, 32).id(), id);
        drop(first);
        let again = meet(7400, 32);
        assert_eq!(again.digest(), digest);
        assert_eq!(meet(7400, 32).id(), again.id());
        let holds = |a: &Row| *a != atom(7400 + 31);
        assert!(!again.eval(holds));
        assert!(again.eval(|_| true));
    }

    #[test]
    fn a_complement_is_found_while_it_lives_and_rebuilt_alike_after() {
        // The complement of an expression: found again while it lives, rebuilt with the same
        // contents once dropped, and its own complement the expression in both cases.
        let e = choices(7500, 7600, 8);
        let n = e.not();
        assert_eq!(e.not().id(), n.id());
        assert_eq!(n.not().id(), e.id());
        let n_digest = n.digest();
        drop(n);
        let n = e.not();
        assert_eq!((n.digest(), n.not().id()), (n_digest, e.id()));
        // The expression dropped while its complement lives: made again as written, with the
        // same digest (so no order or text depends on whether it was freed), the same values,
        // and negating back to the complement.
        let (e_id, e_digest) = (e.id(), e.digest());
        drop(e);
        let again = n.not();
        assert_ne!(again.id(), e_id);
        assert_eq!(again.digest(), e_digest);
        assert_eq!(again.not().id(), n.id());
        let written = choices(7500, 7600, 8);
        let atoms: Vec<Row> = (7501..=7508).chain(7601..7608).map(atom).collect();
        for bits in 0..1u32 << atoms.len() {
            let holds = |a: &Row| (0..atoms.len()).any(|i| bits >> i & 1 == 1 && *a == atoms[i]);
            assert_eq!(again.eval(&holds), written.eval(&holds), "{bits:b}");
        }
        // An exclusive or's complement, its mate, rebuilt after its drop: the same contents, an
        // exclusive or again, and the one node a literal's complement taken in reaches.
        let x = parity(7700, 6);
        let mate = x.not();
        let mate_digest = mate.digest();
        assert_eq!(mate.not().id(), x.id());
        drop(mate);
        let mate = x.not();
        assert_eq!(mate.digest(), mate_digest);
        assert!(mate.xor_tag().is_some());
        assert_eq!(mate.not().id(), x.id());
        let flipped = (7701..7706).fold(Part::literal(atom(7700)).not(), |f, i| {
            xor_by_or(&f, &Part::literal(atom(i)))
        });
        assert_eq!(flipped.id(), mate.id());
        let holds = |bits: u32| {
            move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(7700 + i as u64))
        };
        for bits in 0..64 {
            assert_eq!(mate.eval(&holds(bits)), !odd(bits, 6), "{bits:b}");
        }
        // The exclusive or dropped while its mate lives: rebuilt from the mate, the same node
        // the literals give.
        let x_digest = x.digest();
        drop(x);
        let x = mate.not();
        assert_eq!(x.digest(), x_digest);
        assert_eq!(x.id(), parity(7700, 6).id());
    }

    #[test]
    fn equal_rows_alive_together_are_one_node_and_leave_the_table_when_freed() {
        // Step TABLE-life: two equal rows built apart while both live are one node, so a meet
        // compares them by pointer; a freed row leaves the table.
        let (a, b) = (atom(7900), atom(7900));
        assert!(std::ptr::eq(a.as_ptr(), b.as_ptr()));
        assert!(!std::ptr::eq(a.as_ptr(), atom(7901).as_ptr()));
        let digest = a.digest();
        let live = || super::super::ROWS.with(|t| t.borrow().get(&digest).map_or(0, Vec::len));
        assert_eq!(live(), 1);
        drop((a, b));
        assert_eq!(live(), 0);
    }
}
