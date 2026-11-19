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
//! its literals once the forms it reads are made (an exclusive or of `n` atoms makes its forms on
//! first read, `O(n log n)` expected over all of them, module `xor`); asked which atoms every
//! value takes or refuses (`Part::forced`), in `O(n log n)` on a list and in one pass over the
//! nodes of an expression once the forms it reads are made (COMPLEXITY.md K32); and settled on
//! its shared subexpressions (`Part::settle`), one evaluation per shared subexpression in each
//! round. The last is above the rule of low complexity, an open item (DESIGN.md L1.23). Listing
//! values takes one pass over a list's first nodes, as a diagram would have them
//! (`Bdd::reaching`).
//!
//! Complexity tradeoff (COMPLEXITY.md K1, K3): the naive form, a union of clauses (DNF), takes
//! `2^C` clauses to complement `C` clauses by De Morgan's product (K1) and `O(C³)` to merge its
//! clauses after each change (K3); a reduced ordered diagram makes a union or intersection of
//! `a` and `b` in up to `|a|·|b|` nodes, exponential over a chain of them. Used: a list in one
//! form, complemented in `O(1)` by flipping its first block's value, grown only by literals,
//! `O(log n)` expected each; every other union or intersection an expression built in `O(1)`,
//! with no merging step. Given up: what a diagram would show at once is found when the part is
//! decided (module `empty`), whose walk of an expression's paths is exponential in the worst
//! case and refuses the classes named there; memory is the expressions kept, one node per
//! connective built.

use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::BuildHasherDefault;
use std::sync::atomic::{AtomicBool, Ordering as Atomic};
use std::sync::{Arc, Mutex, Weak};

use crate::digest::{DigestMap, DigestSet};
use crate::frames::{Deep, Stack};

use super::hash::digests_cmp;
use super::mix;

mod set;
mod settings;

use crate::digest::Digest;
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
    /// Never run at run time, so coverage counts it unreached: its only callers are the
    /// `const { … }` initializers of the thread-local tables `TUPLES` and `MORPHISMS` (module
    /// `types`), which the compiler evaluates.
    pub(super) const fn new() -> Tables<A> {
        Tables {
            sets: std::collections::HashMap::with_hasher(std::hash::BuildHasherDefault::new()),
            cells: std::collections::HashMap::with_hasher(std::hash::BuildHasherDefault::new()),
            xors: std::collections::HashMap::with_hasher(std::hash::BuildHasherDefault::new()),
        }
    }
}

/// What a part, cell or set holds that is dropped in the thread's loop of type parts (module
/// `deep`).
pub(super) enum Owned<A: Literal> {
    Part(Part<A>),
    Set(Arc<Set<A>>),
    Cell(Arc<Cell<A>>),
}

impl<A: Literal> Owned<A> {
    /// Whether this handle is the last strong one of its node, so that dropping it frees the
    /// node. A leaf holds no node.
    fn is_last(&self) -> bool {
        match self {
            Owned::Part(Part::Expr(e)) => Arc::strong_count(e) == 1,
            Owned::Part(Part::Bdd(Bdd::List(c, _))) | Owned::Cell(c) => Arc::strong_count(c) == 1,
            Owned::Part(Part::Bdd(Bdd::Leaf(_))) => false,
            Owned::Set(s) => Arc::strong_count(s) == 1,
        }
    }

    /// Drops the handle: in the thread's loop (module `deep`) when it is the last of its node, and
    /// in place otherwise, which only lowers the count. A node freed holds handles to the nodes
    /// below it, most of them shared with nodes still live (the halves of the exclusive ors that a
    /// literal added leaves unchanged, the literals, the subtrees of sets and sequences), and each
    /// went through the queue only to have its count lowered there: 7% of the instructions of
    /// parity built a literal at a time (KERNEL-parity-cost). Should another thread drop its
    /// handle between the count read and the drop here, the node is freed here, and its own drop
    /// queues the handles it holds, so the stack grows by one node at most.
    fn release(self) {
        if self.is_last() {
            A::free(self);
        } else {
            drop(self);
        }
    }
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
    fn name_digest(&self) -> u64;
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
    fn name_digest(&self) -> u64 {
        Literal::name_digest(self)
    }
    fn free_set(set: Arc<Set<A>>) {
        Owned::Set(set).release();
    }
}
/// An expression leaves its thread's table of exclusive ors, if it is in one, and its operands,
/// if they were made, complement and set of atoms are freed in a loop, as a cell's next cell is.
impl<A: Literal> Drop for Expr<A> {
    fn drop(&mut self) {
        let is_self = |w: &Weak<Expr<A>>| std::ptr::eq(w.as_ptr(), self);
        if let Some((s, constant)) = &self.xor {
            let key = (s.id, *constant);
            A::untable(|t| untable(&mut t.xors, key, is_self));
        }
        if let Some(mut f) = self.form.take() {
            free_form(&mut f);
        }
        if let Some(Source::Form(mut f)) = self.source.take() {
            free_form(&mut f);
        }
        if let Some(c) = self.complement.take() {
            Owned::Part(c).release();
        }
        if let Some((s, _)) = self.xor.take() {
            Owned::Set(s).release();
        }
    }
}

/// Removes the entry of `key` when it is the node `is_self` names, in one probe: an entry left by
/// a node dropped on another thread, or replaced since, stays.
fn untable<K: std::hash::Hash + Eq, N>(
    table: &mut HashMap<K, Weak<N>, BuildHasherDefault<Digest>>,
    key: K,
    is_self: impl FnOnce(&Weak<N>) -> bool,
) {
    if let Entry::Occupied(e) = table.entry(key)
        && is_self(e.get())
    {
        e.remove();
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
            Owned::Part(std::mem::replace(part, Part::leaf(false))).release();
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

    pub(super) fn name_digest(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => mix(7, u64::from(*b)),
            Bdd::List(c, v) => mix(mix(18, c.name_digest), u64::from(*v)),
        }
    }

    /// `self op other` when one of the two is a chain under `op`: the chain's literals joined
    /// to the other one at a time; `None` when neither is. Two chains of two or more literals
    /// each are one block of one value, so their blocks are joined as sets
    /// ([`set::union_if_agree`]), and an atom taken by one and refused by the other leaves the
    /// leaf `op` stops at.
    fn zip_chain(&self, other: &Bdd<A>, op: Op) -> Option<Bdd<A>> {
        if let (Bdd::List(x, v), Bdd::List(y, _)) = (self, other)
            && self.is_long_chain(op)
            && other.is_long_chain(op)
        {
            return Some(match set::union_if_agree(&x.block, &y.block) {
                Some(block) => Bdd::assemble(vec![(*v, Some(block))], &Bdd::Leaf(!*v)),
                None => Bdd::Leaf(op == Op::Or),
            });
        }
        // A long chain under `op` met with a long chain under the other connective, as
        // `a & !b` of two unions of literals, is made at once (PERF-equal-functions-forms-
        // ratio). Let `j` be the chain under `op`, one block of value `!v` before the leaf `v`,
        // and `x` the other, one block of value `v` before the leaf `!v`. When a literal of `j`
        // holds, the result is `!v`. When none holds, the result is `x`, in which each literal
        // of `j` is now false: a literal of `x` on the same atom with the same polarity is false
        // and leaves its block, and one with the opposite polarity is true and gives `v`, the
        // value `j` gives too, so the result is then `j` itself. Otherwise the list is `j`'s
        // block, then `x`'s without the atoms of `j`, then `!v` ([`set::difference_if_agree`]).
        // Complexity tradeoff: the difference splits the larger block at each node of the
        // smaller, `O(m log(n/m + 1))` nodes for blocks of `m <= n` literals (Blelloch,
        // Ferizovic and Sun, "Just join for parallel ordered sets", SPAA 2016; for the 8-wise
        // independent priorities of the sets, module `priority`, plus the literals that share a
        // point); the literals of
        // `j` joined one at a time to `x` made `O(log n)` nodes each, `O(m log n)`, the 10.8
        // times as many nodes from n = 256 to 2048 left in
        // `functions_equal_at_one_place_are_decided_a_second_time_in_linear_time` after the
        // tuple unions were built at once.
        let other_op = match op {
            Op::Or => Op::And,
            Op::And => Op::Or,
        };
        for (x, j) in [(self, other), (other, self)] {
            if let (Bdd::List(xc, v), Bdd::List(jc, _)) = (x, j)
                && x.is_long_chain(other_op)
                && j.is_long_chain(op)
            {
                return Some(match set::difference_if_agree(&xc.block, &jc.block) {
                    Some(rest) => Bdd::assemble(
                        vec![(!*v, Some(jc.block.clone())), (*v, rest)],
                        &Bdd::Leaf(!*v),
                    ),
                    None => j.clone(),
                });
            }
        }
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
    ///
    /// Every caller (`choice_of_as_kept`, `Connect::choice_of`) passes a chain of
    /// `Operands::Chain`, which `Part::operands` makes only when `is_long_chain` holds, so `self`
    /// is a list; and an `atom` with `chain_takes(op, atom) == Some(taken)` (the `within` or
    /// `both` filters, with `taken` turned for the chain that refuses it). `chain_takes` gives
    /// `p == (op == Op::Or)` for the stored polarity `p`, so `p == (taken == (op == Op::Or))`,
    /// which is `!value` below: the literal is there and is not the one fixed to `value`.
    fn chain_without(&self, op: Op, atom: &A, taken: bool) -> Bdd<A> {
        let Bdd::List(c, v) = self else {
            unreachable!("`chain_without` of a part that is no chain of two or more literals")
        };
        debug_assert!(c.len == 1, "a chain is one block");
        // The literal is left out by fixing it to the value `op` passes over.
        let value = taken != (op == Op::Or);
        match set::get(Some(&c.block), atom) {
            Some(p) if p != value => {
                let block = set::remove(&c.block, &(atom.clone(), p));
                Bdd::assemble(vec![(*v, block)], &Bdd::Leaf(!*v))
            }
            _ => unreachable!("`chain_without` of an atom the chain does not take as `taken`"),
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
    /// passes on `take` of its state and its atom, an edge to its `lo` its state. Each node is
    /// visited once, after every node with an edge into it, so the time is linear in the nodes.
    ///
    /// Each node has one edge into it, so no states are ever joined. Proof: [`Bdd::view`] puts a
    /// leaf on one side of every node, so a node has at most one child that is a list, and the
    /// nodes reached from the root form one chain `n0, n1, …`. Each `n(j+1)` is `n(j)` with its
    /// first literal removed (and `finish` only shortens a list), so it has fewer literals than
    /// every node before it in the chain and is none of them; and two live lists with the same
    /// id are the same list ([`Bdd::id`]: cell ids are drawn two apart from one counter). So no
    /// id is met twice in the walk, and `n(j+1)` gets its state only from `n(j)`.
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
        let mut seen = DigestSet::default();
        let mut stack: Vec<(&Bdd<A>, bool)> = vec![(self, false)];
        while let Some((n, below)) = stack.pop() {
            if below {
                order.push(n);
                continue;
            }
            if !seen.insert(n.id()) {
                // The nodes reached form one chain with no node met twice (proof above).
                unreachable!("a node of the chain is pushed once");
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
        let mut lo_true: DigestMap<u64, bool> =
            DigestMap::with_capacity_and_hasher(order.len(), Default::default());
        let chain = |b: &Bdd<A>, lo_true: &DigestMap<u64, bool>| match b {
            Bdd::Leaf(v) => *v,
            Bdd::List(..) => *lo_true
                .get(&b.id())
                .expect("a node is ordered after its children"),
        };
        for n in &order {
            let t = chain(node(n).3, &lo_true);
            lo_true.insert(n.id(), t);
        }
        let mut state: DigestMap<u64, S> = DigestMap::from_iter([(self.id(), start)]);
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
                    // `child` has one edge into it, this one (proof above), so it has no state yet.
                    if state.insert(child.id(), s).is_some() {
                        unreachable!("a node's state comes from its one parent");
                    }
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
    pub(super) name_digest: u64,
    /// The connective and its operands ([`Expr::form`]). An exclusive or's two halves are made
    /// when the form is first read, from `xor` (module `xor`); every other form is set when the
    /// expression is made. An exclusive or's digests are its set's and constant's, not its
    /// form's ([`xor::halves`]); every other expression's are its form's.
    form: std::sync::OnceLock<Form<A>>,
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
    /// The set of atoms and the constant of the expression as an exclusive or in its one form
    /// (module `xor`), if it is one; its form and its complement are made from them.
    xor: Option<xor::Tag<A>>,
}

impl<A: Literal> Expr<A> {
    /// The connective and its operands, an exclusive or's halves made on the first read.
    pub(super) fn form(&self) -> &Form<A> {
        self.form.get_or_init(|| {
            let (s, constant) = (self.xor.as_ref())
                .expect("only an exclusive or is made without its form (`xor::node`)");
            xor::halves(s, *constant)
        })
    }

    /// The set of atoms and the constant of the expression as an exclusive or in its one form
    /// (module `xor`), if it is one.
    pub(super) fn xor_set(&self) -> Option<(&Set<A>, bool)> {
        self.xor.as_ref().map(|(s, c)| (&**s, *c))
    }

    /// Whether the form is `Or`, read without making an exclusive or's halves: an exclusive or
    /// made without its form is the union of its halves.
    fn is_or(&self) -> bool {
        self.form.get().is_none_or(|f| matches!(f, Form::Or(..)))
    }

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
        // A form not yet made is an exclusive or's `Or`, so no `Not`.
        matches!(self.form.get(), Some(Form::Not(q)) if is_e(q))
            || self.complement.get().is_some_and(is_e)
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

/// An expression's form. No operand of an `Or` or `And` is a leaf (`Part::is_leaf`): every
/// expression is made in [`build`], whose `Part::connect` folds a leaf operand away
/// (`a | true` is `true`, `a | false` is `a`, `a & true` is `a`, `a & false` is `false`), and
/// whose other constructors assert it. Readers of a form (`empty.rs` `read_two_sat`) rely on it.
#[derive(Clone)]
pub(super) enum Form<A: Literal> {
    Not(Part<A>),
    Or(Part<A>, Part<A>),
    And(Part<A>, Part<A>),
}

/// The only constructors of an expression with a form: `Part::expr` is private here, so no
/// other code, the tests included, makes an `Or` or `And` with a leaf operand ([`Form`]).
mod build {
    use super::*;

    impl<A: Literal> Part<A> {
        fn expr(form: Form<A>) -> Part<A> {
            Part::made(
                form.digest(),
                form.name_digest(),
                std::sync::OnceLock::from(form),
                None,
            )
        }

        /// `a | b` (`Op::Or`) or `a & b` (`Op::And`), operands in this order, as an expression;
        /// a leaf operand is folded away and its result returned instead.
        pub(super) fn connect(op: Op, a: Part<A>, b: Part<A>) -> Part<A> {
            match (op, a.is_leaf(), b.is_leaf()) {
                (Op::Or, Some(true), _) | (Op::Or, _, Some(true)) => Part::Bdd(Bdd::Leaf(true)),
                (Op::And, Some(false), _) | (Op::And, _, Some(false)) => {
                    Part::Bdd(Bdd::Leaf(false))
                }
                (_, Some(_), _) => b,
                (_, _, Some(_)) => a,
                (Op::Or, None, None) => Part::expr(Form::Or(a, b)),
                (Op::And, None, None) => Part::expr(Form::And(a, b)),
            }
        }

        /// `!p` kept as an expression.
        pub(super) fn not_expr(p: Part<A>) -> Part<A> {
            Part::expr(Form::Not(p))
        }

        /// The expression of `form`, a form an expression had: its operands are no leaves.
        pub(super) fn of_form(form: Form<A>) -> Part<A> {
            form.assert_no_leaf_operand();
            Part::expr(form)
        }
    }

    impl<A: Literal> Form<A> {
        /// Asserts in debug builds that no operand of an `Or` or `And` is a leaf ([`Form`]).
        pub(super) fn assert_no_leaf_operand(&self) {
            if let Form::Or(a, b) | Form::And(a, b) = self {
                debug_assert!(
                    a.is_leaf().is_none() && b.is_leaf().is_none(),
                    "a leaf operand of an `Or` or `And`"
                );
            }
        }
    }
}

/// The digest of the expression `a | b` (`Op::Or`) or `a & b` (`Op::And`) whose operands, in
/// that order, have the digests `a` and `b`.
fn joined_digest(op: Op, a: u64, b: u64) -> u64 {
    let tag = match op {
        Op::Or => 9,
        Op::And => 10,
    };
    mix(mix(tag, a), b)
}

impl<A: Literal> Form<A> {
    /// The digest of an expression of the form, made from its operands' digests.
    fn digest(&self) -> u64 {
        match self {
            Form::Not(p) => mix(8, p.digest()),
            Form::Or(a, b) => joined_digest(Op::Or, a.digest(), b.digest()),
            Form::And(a, b) => joined_digest(Op::And, a.digest(), b.digest()),
        }
    }

    fn name_digest(&self) -> u64 {
        match self {
            Form::Not(p) => mix(8, p.name_digest()),
            Form::Or(a, b) => joined_digest(Op::Or, a.name_digest(), b.name_digest()),
            Form::And(a, b) => joined_digest(Op::And, a.name_digest(), b.name_digest()),
        }
    }

    /// Whether `e` is an operand of the form.
    fn holds(&self, e: &Arc<Expr<A>>) -> bool {
        let is_e = |p: &Part<A>| matches!(p, Part::Expr(x) if Arc::ptr_eq(x, e));
        match self {
            // Not reached: the one caller, `Connect::negate`, asks this of a form only in its
            // branch for a choice, which it takes after its branch for a form `Not` declined, so
            // the form is an `Or` or an `And`. Kept so that the answer holds for every form.
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

    pub(super) fn name_digest(&self) -> u64 {
        match self {
            Part::Bdd(b) => b.name_digest(),
            Part::Expr(e) => e.name_digest,
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
    pub(super) fn before(&self, other: &Part<A>) -> bool {
        digests_cmp(
            (self.digest(), self.name_digest()),
            (other.digest(), other.name_digest()),
        )
        .then_with(|| self.cmp(other))
        .is_le()
    }

    pub(super) fn leaf(b: bool) -> Part<A> {
        Part::Bdd(Bdd::Leaf(b))
    }

    pub(super) fn literal(a: A) -> Part<A> {
        Part::Bdd(Bdd::literal(a))
    }

    /// The atom `a` when the part is the one [`Part::literal`] makes of `a`, in O(1): a list of
    /// one block holding `(a, true)`, of first value `true` (`Bdd::literal_key`). Both are read
    /// here, not taken from the list's one form, so the answer is the same as comparing the
    /// part with `Part::literal(a)` by contents.
    pub(super) fn literal_atom(&self) -> Option<&A> {
        match self {
            Part::Bdd(b @ Bdd::List(_, true)) => match b.as_literal() {
                Some((a, true)) => Some(a),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether the part is a list that is a union of literals, of any number, in O(1).
    pub(super) fn is_union_of_literals(&self) -> bool {
        matches!(self, Part::Bdd(b) if b.chain_len(Op::Or).is_some())
    }

    /// The union of `ps`, each [`Part::is_union_of_literals`], made at once: their literals
    /// sorted and the one set of them built bottom up ([`set::from_sorted`]), `k` set nodes for
    /// `k` literals, where joining them in pairs made the nodes of each merged set again at each
    /// level, `O(k log k)`. The list is the one [`Part::zip`] makes of them, as a list has one
    /// form. `None` when one takes an atom another refuses, left to [`Part::zip`].
    pub(super) fn union_of_literals(ps: &[&Part<A>]) -> Option<Part<A>> {
        let mut keys = Vec::new();
        for p in ps {
            let Part::Bdd(b) = p else { return None };
            keys.extend(b.chain_keys(Op::Or)?);
        }
        keys.sort_unstable();
        keys.dedup();
        if keys.windows(2).any(|w| w[0].0 == w[1].0) {
            return None;
        }
        Some(Part::Bdd(match keys.len() {
            0 => Bdd::Leaf(false),
            1 => Bdd::literal_key(keys.pop().expect("one literal")),
            _ => Bdd::assemble(vec![(true, set::from_sorted(keys))], &Bdd::Leaf(false)),
        }))
    }

    /// Whether the part is no value (`Some(false)`) or every value (`Some(true)`) as built.
    pub(super) fn is_leaf(&self) -> Option<bool> {
        match self {
            Part::Bdd(Bdd::Leaf(b)) => Some(*b),
            _ => None,
        }
    }

    /// The exclusive or `xor` of the digests `digest` and `name_digest`, its halves made when
    /// its form is first read ([`Expr::form`]).
    fn expr_unmade(digest: u64, name_digest: u64, xor: xor::Tag<A>) -> Part<A> {
        Part::made(digest, name_digest, std::sync::OnceLock::new(), Some(xor))
    }

    /// The expression of `digest` and `form`, the exclusive or `xor` when given.
    fn made(
        digest: u64,
        name_digest: u64,
        form: std::sync::OnceLock<Form<A>>,
        xor: Option<xor::Tag<A>>,
    ) -> Part<A> {
        Part::Expr(Arc::new(Expr {
            id: NEXT.fetch_add(1, Atomic::Relaxed),
            digest,
            name_digest,
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
        match Part::zip_at_once(self, other, op).or_else(|| Part::xor_at_once(self, other, op)) {
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

    /// `a op b` as an exclusive or in its one form ([`xor::xor_of`]), for operands neither a leaf,
    /// nor equal, nor both lists. It is the part `Connect::zipped` makes: its first rule, `a` the
    /// complement of `b`, does not fit them, since `u&v` (`u|v` under `And`) is the complement of
    /// `!u&!v` (`!u|!v`) only when `u` and `v` are one function, and two exclusive ors in their
    /// one form of two sets of atoms or two constants are two functions; its second is for two
    /// lists; its third is this one.
    // Complexity tradeoff: the constant-time test of `xor::xor_of` is run before the frames of
    // `Connect`, and again in no frame, so that the union of two halves of an exclusive or skips
    // the complement of one of them, made, compared and freed by the first rule; a union or
    // meet that is no exclusive or pays for the test once, as before. Measured on parity built
    // a literal at a time (KERNEL-parity-cost). Naive version: the frames of `Connect` alone,
    // whose rule `a = !b` makes, compares and frees the complement of one half, a constant
    // factor per union; used: the test first. Both are of order n log n on parity; COMPLEXITY.md
    // K90 (5): 51.01G to 50.09G instructions and 6.96G to 4.97G bytes at 16,384 literals.
    fn xor_at_once(a: &Part<A>, b: &Part<A>, op: Op) -> Option<Part<A>> {
        match (a, b) {
            (Part::Bdd(_), Part::Bdd(_)) => None,
            _ => xor::xor_of(a, b, op),
        }
    }

    /// Whether the list `x` is the complement of the list `y`, making no cell. A literal's
    /// complement is the literal on its atom with the other value, so two literals are compared
    /// by atom and value, and a literal is no other list's complement. Any other list's
    /// complement is its first cell with the value flipped. Two lists whose cells and blocks
    /// were all made on one thread are one cell when equal (proof below), so for them `y` is
    /// that complement exactly when it has that cell and the other value. A list may also hold
    /// cells of another thread (each thread has its own tables), so when the ids differ and the
    /// digests agree the two are compared by contents.
    //
    // Proof that two equal lists whose cells and set nodes were all made on one thread `T` are
    // one cell (PROOF-lists-opposite-one-cell; test
    // `one_list_built_by_several_routes_on_one_thread_is_one_cell`):
    // (1) `list::cell` is the only place a cell is made, and it looks the key (left child's id,
    //     block's id, right child's id) up in `T`'s table first, returning the live cell found.
    //     An entry is replaced only when its cell is dead (its weak handle does not upgrade) and
    //     is removed only by its own cell's drop (`Drop for Cell` checks the pointer), and
    //     `A::table` panics rather than run without the table, so two live cells of `T` have
    //     different keys. The same holds for set nodes (`set::make_at` and `bucket::find`):
    //     two equal sets made on `T` are one node.
    // (2) A sequence of blocks has one shape: a cell's priority is a function of its block
    //     (`list::priority`), and every cell is built with `left.prio < prio` and
    //     `right.prio <= prio` (`merge`'s tie rule, `replace`'s path and `fits`, `split`'s
    //     path, `restrict`'s direct case; checked by `cells_are_sound`; `Bdd::absorbed` makes
    //     no cell, it returns an operand), so the root is the first block of the
    //     highest priority, and the children are the sequences before and after it.
    // (3) By induction on the number of blocks: two equal lists have one root block, which is
    //     one set node by (1), and equal sequences on each side, which are one cell each by
    //     induction; so the two roots have one key, and by (1) are one cell.
    // Not covered: a list made on another thread, or one made on `T` by editing a list made on
    // another thread, whose untouched cells stay that thread's. Such a list on `T` and an equal
    // list built on `T` are two cells, whose roots may both be `T`'s; the scaling checks meet
    // their inputs this way (`parts_built_on_one_thread_meet_on_another_in_their_one_form`).
    //
    // Complexity tradeoff (COMPLEXITY.md CANON-choose-true-branch): the naive version took
    // `x.not()` and compared first cells' ids, O(1), but `not` of a literal looks the literal
    // up in the calling thread's table, so a literal and its complement made on another thread
    // were not found complements, and a choice on a literal condition built on one thread was
    // kept as an expression when met on another (the scaling checks run on threads of their
    // own). Used: two literals by atom and value, O(1) atom comparisons; other lists by id, O(1),
    // then, when the ids differ and the digests agree, by `==` (`order`): O(1) when the
    // names-aware digests differ, its first step, otherwise O(size of the lists), skipping pairs
    // of one id. The digests leave definition names out, so lists that differ only in names
    // agree on them, and the comparison ends at its first step: measured, 2,566 such comparisons
    // in `group_oracle::bench::verdicts_of_a_ring_of_the_group_that_hung_the_search_scale`
    // (l01_23), none of them past the names-aware digests. For two lists made on one thread the
    // walk of contents is reached only when two different lists agree on both digests, or on
    // `digest` while `hash::blind` leaves names out: digests of 64 bits, or 8 in the
    // short-addresses build (`address::short64`), where that is common; and the digests are fixed
    // functions of the atoms (a sum over a set's literals, a polynomial over a list's blocks), so
    // a program can choose lists whose digests agree. Each such walk costs the size of the lists,
    // and gives the right answer. For lists with cells of two threads it is reached whenever they
    // are complements: measured, 301 comparisons in the l01 benches, all in
    // `payload_scaling::bench::pinwheels_of_{one_tuple,payload}_ends_with_a_cofinite_end_scale`
    // (l01_23), each between a list made wholly on the measuring thread and one holding cells
    // made on another thread. No other l01 bench, and none of the short-addresses tests of l01_37
    // and l01_37a, compared lists here by `==`. These counts were taken on the code before
    // CANON-list-absorb, which changes what `Connect::zipped` and `Part::union_as_kept` return.
    fn lists_opposite(x: &Bdd<A>, y: &Bdd<A>) -> bool {
        match (x.as_literal(), y.as_literal()) {
            (Some((a, t)), Some((b, u))) => return t != u && a == b,
            (Some(_), None) | (None, Some(_)) => return false,
            (None, None) => {}
        }
        match (x, y) {
            (Bdd::List(c, v), Bdd::List(d, w)) => {
                let n = Bdd::List(c.clone(), !v);
                v != w && (c.id == d.id || (n.digest() == y.digest() && n == *y))
            }
            (Bdd::Leaf(p), Bdd::Leaf(q)) => p != q,
            (Bdd::List(..), Bdd::Leaf(_)) | (Bdd::Leaf(_), Bdd::List(..)) => false,
        }
    }

    /// Whether `a` is the complement of `b` as the two are kept, making no part: two lists by
    /// their first cells, two exclusive ors by their tags, and an expression by its complement
    /// as kept or its form `Not`. `false` when the complement is not yet made, where
    /// `Connect::same_as_not` would make it.
    fn opposite_as_kept(a: &Part<A>, b: &Part<A>) -> bool {
        let kept = |p: &Part<A>, q: &Part<A>| match p {
            Part::Expr(e) => {
                e.known().is_some_and(|n| n == *q)
                    || matches!(e.form.get(), Some(Form::Not(r)) if r == q)
            }
            Part::Bdd(_) => false,
        };
        match (a, b) {
            (Part::Bdd(x), Part::Bdd(y)) => Part::lists_opposite(x, y),
            (Part::Expr(e), Part::Expr(f)) if e.xor.is_some() && f.xor.is_some() => {
                let (Some(u), Some(v)) = (&e.xor, &f.xor) else {
                    // The guard of this arm tested both `is_some()`.
                    unreachable!("both tested")
                };
                xor::opposite(u, v)
            }
            _ => kept(a, b) || kept(b, a),
        }
    }

    /// The complement of `p` as kept, making no part but a list's: `None` for an expression
    /// whose complement is not yet made.
    fn not_as_kept(p: &Part<A>) -> Option<Part<A>> {
        match p {
            Part::Bdd(b) => Some(Part::Bdd(b.not())),
            Part::Expr(e) => e.known().or_else(|| match e.form.get() {
                Some(Form::Not(q)) => Some(q.clone()),
                _ => None,
            }),
        }
    }

    /// `a | b` when a rule of `Connect::zipped` gives it from the parts as they are kept, with
    /// no call of `Connect`, so that `Connect::choose` can take the union of its meets without
    /// finding its own choice again: a leaf or equal operands; the two halves of an exclusive
    /// or (`xor::xor_of`); complements, as kept ([`Part::opposite_as_kept`]); two lists that
    /// `Bdd::zip_chain` joins, or of which one absorbs the other (`Bdd::absorbed`); and
    /// `c&x | !c&x`, which is `x`. `None` when none fits.
    /// None of the calls made enters `Connect`: `xor::xor_of` reads no exclusive or's halves
    /// (`xor::pair`) and makes a node of the table (`Part::xor`); `zip_chain` and `absorbed`
    /// read and edit lists; the
    /// order of parts compares two exclusive ors by their sets, not their halves. So the
    /// function ends, after a constant number of calls, each of the cost it has in `zipped`.
    fn union_as_kept(a: &Part<A>, b: &Part<A>) -> Option<Part<A>> {
        if let Some(z) = Part::zip_at_once(a, b, Op::Or).or_else(|| xor::xor_of(a, b, Op::Or)) {
            return Some(z);
        }
        if Part::opposite_as_kept(a, b) {
            return Some(Part::leaf(true));
        }
        if let (Part::Bdd(x), Part::Bdd(y)) = (a, b)
            && let Some(z) = x.zip_chain(y, Op::Or).or_else(|| x.absorbed(y, Op::Or))
        {
            return Some(Part::Bdd(z));
        }
        match Part::choice_of_as_kept(a, b) {
            Some((_, x, y)) if x == y => Some(x),
            _ => None,
        }
    }

    /// `(c, x, y)` when `a | b` is the choice `c&x | !c&y`, found as `Connect::choice_of`
    /// finds it under `Or` but with the complements as kept ([`Part::opposite_as_kept`],
    /// [`Part::not_as_kept`]), so with no call of `Connect`. When two or more conditions fit,
    /// `None`, as there. A complement not yet made can hide a second condition that `choice_of`
    /// would find; the one choice found is then a choice still, so the part built from it is
    /// the same set.
    fn choice_of_as_kept(a: &Part<A>, b: &Part<A>) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let inner = Op::And;
        let r = b.operands(inner)?;
        let l = a.operands(inner)?;
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
                        if Part::opposite_as_kept(c, n) {
                            found.push(((*c).clone(), (*x).clone(), (*y).clone()));
                        }
                    }
                }
            }
            (Operands::Two(p, q), Operands::Chain(d)) => {
                for (c, x) in [(p, q), (q, p)] {
                    if let Some((atom, taken)) = Part::not_as_kept(c).and_then(|n| within(&n, d)) {
                        let y = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push(((*c).clone(), (*x).clone(), y));
                    }
                }
            }
            (Operands::Chain(d), Operands::Two(s, t)) => {
                for (n, y) in [(s, t), (t, s)] {
                    if let Some((atom, taken)) = Part::not_as_kept(n).and_then(|m| within(&m, d)) {
                        let c = Part::Bdd(Bdd::literal_of(&atom, taken));
                        let x = Part::Bdd(d.chain_without(inner, &atom, taken));
                        found.push((c, x, (*y).clone()));
                    }
                }
            }
            (Operands::Chain(d), Operands::Chain(e)) => {
                // As in `Connect::choice_of`: the shorter chain's literals looked up in the
                // longer, `O(k log n)`.
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
                let taken = if short_is_d { taken } else { !taken };
                found.push((
                    Part::Bdd(Bdd::literal_of(atom, taken)),
                    Part::Bdd(d.chain_without(inner, atom, taken)),
                    Part::Bdd(e.chain_without(inner, atom, !taken)),
                ));
            }
        }
        let mut found = found.into_iter();
        match (found.next(), found.next()) {
            (Some(one), None) => Some(one),
            _ => None,
        }
    }

    /// `(c, x, y)` when `p` is the choice `c&x | !c&y` in its one form, found as
    /// `Connect::choice` finds it but with the complements as kept
    /// ([`Part::choice_of_as_kept`]); the condition is not put in the order `choice` puts it.
    fn choice_as_kept(&self) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let Part::Expr(e) = self else { return None };
        if e.xor.is_some() {
            return None;
        }
        let Form::Or(a, b) = e.form() else {
            return None;
        };
        Part::choice_of_as_kept(a, b)
    }

    /// The operands of an expression's `And` or `Or`, under `op`, or the literals of a chain
    /// under `op`.
    fn operands(&self, op: Op) -> Option<Operands<'_, A>> {
        match (self, op) {
            // An `Or` is no `And`, read without making an exclusive or's halves.
            (Part::Expr(e), Op::And) if e.is_or() => None,
            (Part::Expr(e), Op::And) => match e.form() {
                Form::And(a, b) => Some(Operands::Two(a, b)),
                _ => None,
            },
            (Part::Expr(e), Op::Or) => match e.form() {
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
            // `Connect::not`, the one caller, answers a `Part::Bdd` itself and sends only a
            // `Part::Expr` here.
            unreachable!("only an expression keeps its complement")
        };
        let n = if let Some(source) = e.source.get() {
            // The expression this one was made the complement of, freed: made again as written.
            match source {
                Source::NotOfThis => Part::not_expr(p.clone()),
                Source::Form(f) => Part::of_form(f.clone()),
            }
        } else if let Some((s, constant)) = &e.xor {
            // An exclusive or's complement is the one of its set and the other constant.
            xor::mate(s, !constant)
        } else if let Form::Not(q) = e.form() {
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
                && !e.form().holds(m)
            {
                let _ = m.source.set(Source::Form(e.form().clone()));
            }
            n
        } else {
            e.plain.store(true, Atomic::Relaxed);
            Part::not_expr(p.clone())
        };
        e.link(n)
    }

    fn zip<A: Literal>(&'m self, a: &Part<A>, b: &Part<A>, op: Op) -> Deep<'m, Part<A>> {
        match Part::zip_at_once(a, b, op).or_else(|| Part::xor_at_once(a, b, op)) {
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
        // Operands not both lists were tested before the frame (`Part::xor_at_once`).
        // Naive version (COMPLEXITY.md K63): the expression kept as made, O(1) per exclusive
        // or, but one set of atoms built in two orders is then two nodes, which are not equal
        // by id; that later steps then compare such parts in full is inferred.
        if let (Part::Bdd(_), Part::Bdd(_)) = (&a, &b)
            && let Some(x) = xor::xor_of(&a, &b, op)
        {
            return x;
        }
        // A list that implies the other, as their blocks show it, absorbs it under `And` and
        // is absorbed under `Or` (`Bdd::absorbed`, with its proof and costs).
        if let (Part::Bdd(x), Part::Bdd(y)) = (&a, &b)
            && let Some(z) = x.absorbed(y, op)
        {
            return Part::Bdd(z);
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
        Part::connect(op, a, b)
    }

    /// Whether `a` is the complement of `b`, as built. Two diagrams are compared by their first
    /// cells' ids, in constant time: a live cell is the one cell of its contents, so the
    /// complement of a list, its first cell with the value flipped, is `b` exactly when `b` has
    /// that cell and value. A list met with its complement is then `false` (or `true` for `|`)
    /// at once, where a part of it kept as an expression would be narrowed one tuple type a
    /// pass, order `n²` in its tuple types (the chain of `c` less that of `c + 1`,
    /// `l01_23_subtyping::one_pass`, COMPLEXITY.md K71).
    async fn same_as_not<A: Literal>(&'m self, a: &Part<A>, b: &Part<A>) -> bool {
        match (a, b) {
            (Part::Bdd(x), Part::Bdd(y)) => Part::lists_opposite(x, y),
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
        // A shortcut: without it the meets below are made and `Part::union_as_kept` reaches the
        // same exclusive or (measured on the test below with this return skipped). Reached
        // from `zipped`'s two choices on one condition: `c&x | !c&!x` built directly is found
        // before `choose`. Test: `bdd::tests::choices_whose_branches_join_to_opposite_exclusive_ors_are_one`.
        if let Some(z) = xor::xor_choice(c, x, y) {
            return z;
        }
        let (c, same) = self.condition(c).await;
        let (x, y) = if same { (x, y) } else { (y, x) };
        // The two parts whose union the choice is: `c | y` when `x` is `true`, since
        // `c | !c&y` is `c | y`, and `x | !c` when `y` is; otherwise the meets `c&x` and
        // `!c&y`. A branch `false` needs no arm: its meet is `false`, which the first rule of
        // `Part::union_as_kept` drops (cross-review of xor-shape, round 3, Gemini Q2).
        // Two leaves need no arm either (TEST-kernel-unreached-paths-4, kernel13: the arms were
        // removed, as no test reached them and the proof that no input does was withdrawn). Both
        // `false` is `x == y`, answered first. `x` true and `y` false gives the parts `c` and
        // `false`, and `x` false and `y` true gives `false` and `!c`; in either order
        // `Part::union_as_kept` calls `Part::zip_at_once` first, which under `Or` gives the
        // operand other than the leaf `false`: `c`, or `!c`, the parts the arms returned.
        let parts = match (x.is_leaf(), y.is_leaf()) {
            (Some(true), _) => [c.clone(), y.clone()],
            (_, Some(true)) => [x.clone(), self.not(&c).await],
            _ => {
                let first = self.zip(&c, x, Op::And).await;
                let not_c = self.not(&c).await;
                [first, self.zip(&not_c, y, Op::And).await]
            }
        };
        let [a, b] = if parts[0].before(&parts[1]) {
            parts
        } else {
            let [p, q] = parts;
            [q, p]
        };
        // `zipped` itself is not called on the two parts: its rules for choices can find this
        // choice again, and no measure is known that falls on that round trip (cross-review of
        // xor-shape, round 3: Opus refuted the step "a meet's choice comes from `c`'s", Gemini
        // the claim "two meets choose on one condition only when `c` chooses on it"). So the
        // union is taken by `Part::union_as_kept`, which makes no call of `Connect` and does not
        // recurse, and so ends; when no rule of it fits, by the rule for two choices on one
        // condition below, one level deep; and otherwise kept as the expression.
        // Complexity tradeoff (COMPLEXITY.md CANON-choose-true-branch): the naive method keeps
        // the union of the meets as an expression, in constant time, and leaves a second node
        // for one function: `c | y` as `c | !c&y` (Opus, round 2, N1), a union of meets that
        // agree as an expression, and a list covered by the two meets as no leaf. Used: a fixed
        // number of tests, each of constant time or of the cost of the call `zipped` makes on
        // such parts (`Part::union_as_kept`), at most three unions of that kind here, and no
        // part compared in full but where the order of parts walks equal digests, as everywhere
        // in this module. Given up: a union whose meets agree only two or more choices deep, or
        // which needs a complement not yet made, is still a second node; and a list absorbed by
        // another list that is no chain is found only in the cases `Bdd::absorbed` proves
        // (`l & (l|b)`, Opus R3-C3, is one; plan row CANON-list-absorb).
        if let Some(z) = Part::union_as_kept(&a, &b) {
            return z;
        }
        // `c&u | !c&v` and `c&s | !c&t` are `c&(u|s) | !c&(v|t)`, which is `u|s` when the two
        // unions are equal.
        // Each arm is reached by a test: `c == d` and the opposite condition by
        // `bdd::tests::a_choice_whose_meets_choose_on_one_condition_with_equal_unions_is_that_union`,
        // two other conditions by `a_choice_whose_meets_choose_on_two_conditions_keeps_their_union`.
        if let (Some((c, u, v)), Some((d, s, t))) = (a.choice_as_kept(), b.choice_as_kept()) {
            let same = if c == d {
                Some((s, t))
            } else if Part::opposite_as_kept(&c, &d) {
                Some((t, s))
            } else {
                None
            };
            if let Some((s, t)) = same
                && let (Some(l), Some(r)) =
                    (Part::union_as_kept(&u, &s), Part::union_as_kept(&v, &t))
                && l == r
            {
                return l;
            }
        }
        Part::connect(Op::Or, a, b)
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
        // `b`'s operands first: when it has none, an exclusive or `a` is not made to show its
        // halves.
        let r = b.operands(inner)?;
        let l = a.operands(inner)?;
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
                // Complexity tradeoff (COMPLEXITY.md K67 (2)): the naive version lists both
                // chains at each join, O(k + n) per join, so a meet of m literals joined to m
                // meets of two costs O(m²). Used: the shorter chain listed and each of its atoms
                // looked up in the longer one's block (`set::get`), O(k log n). Given up: a log
                // factor per lookup where both chains are of one length.
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
    /// chain's union is a literal, which has no operands; and an exclusive or in its one form
    /// is none, since both of its halves' operands have their complements in the other half,
    /// so two conditions fit (`xor::meet`). It is answered without making its halves.
    async fn choice<A: Literal>(&'m self, p: &Part<A>) -> Option<(Part<A>, Part<A>, Part<A>)> {
        let Part::Expr(e) = p else { return None };
        if e.xor.is_some() {
            return None;
        }
        let Form::Or(a, b) = e.form() else {
            return None;
        };
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
        // Keyed by `Digest`, one finalizer step per id: with the standard map's SipHash, hashing
        // was about 47% of a run that evaluates 4000 parts on 64 assignments each, and `Digest`
        // halves that run's instructions (COMPLEXITY.md K104). The ids come from one counter
        // shared by every part, so a vector indexed by id would first need a numbering walk
        // with a map of its own.
        let mut memo: HashMap<u64, bool, BuildHasherDefault<Digest>> = HashMap::default();
        let mut values: Vec<bool> = Vec::new();
        let mut jobs = vec![Job::Part(self)];
        while let Some(job) = jobs.pop() {
            match job {
                Job::Part(Part::Bdd(b)) => values.push(b.eval(holds)),
                Job::Part(Part::Expr(e)) => match memo.get(&e.id) {
                    Some(v) => values.push(*v),
                    None => {
                        let (_, a, _) = e.form().operands();
                        jobs.push(Job::First(e));
                        jobs.push(Job::Part(a));
                    }
                },
                Job::First(e) => {
                    let v = values.pop().expect("the first operand's value");
                    match e.form() {
                        Form::Not(_) => {
                            memo.insert(e.id, !v);
                            values.push(!v);
                        }
                        Form::Or(_, b) | Form::And(_, b) => {
                            if v == matches!(e.form(), Form::Or(..)) {
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
        self.eval3_pinned(holds, &DigestMap::default())
    }

    /// [`Part::eval3`], with each expression in `pins` taken to have the value beside it.
    fn eval3_pinned(
        &self,
        holds: &impl Fn(&A) -> Option<bool>,
        pins: &DigestMap<u64, bool>,
    ) -> Option<bool> {
        // Each list once.
        fn bdd<A: Literal>(
            b: &Bdd<A>,
            holds: &impl Fn(&A) -> Option<bool>,
            memo: &mut DigestMap<u64, Option<bool>>,
        ) -> Option<bool> {
            *memo.entry(b.id()).or_insert_with(|| b.eval3(holds))
        }
        let mut nodes = DigestMap::default();
        let mut memo: DigestMap<u64, Option<bool>> =
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
                         nodes: &mut DigestMap<u64, Option<bool>>,
                         memo: &DigestMap<u64, Option<bool>>| match q {
                Part::Bdd(b) => Some(bdd(b, holds, nodes)),
                Part::Expr(x) => memo.get(&x.id).copied(),
            };
            let operands: Vec<&Part<A>> = match e.form() {
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
            let v = match e.form() {
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
    fn pins(&self) -> DigestMap<u64, bool> {
        // The expressions; those shared, in the order the walk finds them shared, so that the
        // pins taken do not depend on the expressions' ids.
        let mut ids: DigestMap<u64, usize> = DigestMap::default();
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
            match e.form() {
                Form::Not(a) => stack.push(a.clone()),
                // The first operand is pushed last, so it is walked first.
                Form::Or(a, b) | Form::And(a, b) => {
                    stack.push(b.clone());
                    stack.push(a.clone());
                }
            }
        }
        let Part::Expr(root) = self else {
            return DigestMap::default();
        };
        let root = ids[&root.id];
        let id = |q: &Part<A>| match q {
            Part::Expr(x) => Some(ids[&x.id]),
            Part::Bdd(_) => None,
        };
        let operands = |e: &Expr<A>| match e.form() {
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
            match e.form() {
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
        // Each expression after its parts (Kahn's order, last ready first).
        let mut ready: Vec<usize> = zed_graph::sources(&waiting).collect();
        zed_graph::kahn(
            &mut waiting,
            &mut ready,
            |i| parents[i].iter().copied(),
            |i| {
                let v = step(&exprs[i], &|c| known[c]);
                known[i] = v;
            },
        );
        let mut fixed = vec![false; exprs.len()];
        let carry = |i: usize,
                     v: bool,
                     known: &[Option<bool>],
                     fixed: &[bool]|
         -> DigestMap<usize, Option<bool>> {
            let mut changed = DigestMap::from_iter([(i, Some(v))]);
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
        let mut pins: DigestMap<u64, bool> = DigestMap::default();
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
            let mut uses: DigestMap<u64, usize> = DigestMap::default();
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
                match e.form() {
                    Form::Not(a) => stack.push(a.clone()),
                    // The first operand is pushed last, so it is walked first.
                    Form::Or(a, b) | Form::And(a, b) => {
                        stack.push(b.clone());
                        stack.push(a.clone());
                    }
                }
            }
            let mut pins: DigestMap<u64, bool> = DigestMap::default();
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
    fn substitute_all(&self, pins: &DigestMap<u64, bool>) -> Part<A> {
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

    /// The part with each atom `a` replaced by `map(a)`. Whether a value is in a part is its
    /// connectives applied to whether the value is in each of its atoms, so the part made has a
    /// value exactly when the part's connectives, applied to whether the value is in each
    /// `map(a)`, give true, for any `map`. A list is made again from its blocks, last first:
    /// a block of value `v` takes the values in one of its literals and leaves the others to
    /// the blocks after it; each expression from its operands made again, each list and
    /// expression once.
    ///
    /// Complexity tradeoff: the literals of a block are joined in pairs, `O(k log k)` nodes
    /// joined for a block of `k`, against `O(k^2)` one at a time (as [`crate::types::Type::union_all`]
    /// does); each block after that costs one union or meet with what follows it, so a list
    /// costs what building it by its blocks costs. A list is not copied with its atoms renamed
    /// in place, since two atoms may be renamed to one and the atoms' order follows their
    /// digests, which renaming changes.
    pub(super) fn map_atoms(&self, map: &impl Fn(&A) -> A) -> Part<A> {
        let mut lists: DigestMap<u64, Part<A>> = DigestMap::default();
        self.rebuild(|p| match p {
            Part::Bdd(Bdd::Leaf(v)) => Some(Part::leaf(*v)),
            Part::Bdd(b) => Some(
                lists
                    .entry(b.id())
                    .or_insert_with(|| {
                        let list = b.list();
                        let mut after = Part::leaf(list.tail);
                        for (v, literals) in list.blocks.iter().rev() {
                            let mut ps: Vec<Part<A>> = (literals.iter())
                                .map(|(a, taken)| {
                                    let x = Part::literal(map(a));
                                    if *taken { x } else { x.not() }
                                })
                                .collect();
                            while ps.len() > 1 {
                                let mut joined = Vec::with_capacity(ps.len().div_ceil(2));
                                let mut it = ps.into_iter();
                                while let Some(x) = it.next() {
                                    joined.push(match it.next() {
                                        Some(y) => x.zip(&y, Op::Or),
                                        None => x,
                                    });
                                }
                                ps = joined;
                            }
                            let block = ps.pop().unwrap_or_else(|| Part::leaf(false));
                            after = match v {
                                true => block.zip(&after, Op::Or),
                                false => block.not().zip(&after, Op::And),
                            };
                        }
                        after
                    })
                    .clone(),
            ),
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
            // Each `base` given to `rebuild` (`substitute_all`, `restrict`, `map_atoms`) answers
            // `Some` for every `Part::Bdd`, so a part `base` leaves is an expression.
            unreachable!("`base` decides every diagram")
        };
        let mut memo: DigestMap<u64, Part<A>> = DigestMap::default();
        let mut stack: Vec<(&Expr<A>, bool)> = vec![(root, false)];
        while let Some((e, ready)) = stack.pop() {
            if memo.contains_key(&e.id) {
                continue;
            }
            let (_, a, b) = e.form().operands();
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
            let r = match (e.form(), b) {
                (Form::Or(..), Some(b)) => a.zip(&b, Op::Or),
                (Form::And(..), Some(b)) => a.zip(&b, Op::And),
                _ => a.not(),
            };
            memo.insert(e.id, r);
        }
        memo[&root.id].clone()
    }

    /// Positive atoms written as mandatory meet factors or in a list's rejecting first
    /// block. Every returned atom holds in every value, but this is not a complete list.
    // Complexity tradeoff: the general three-valued analysis combines atom sets at every
    // Boolean node, O(nodes * atoms). Walk only meet factors and first blocks here,
    // visiting every shared expression and literal-set node once, O(nodes + atoms log atoms).
    // Common atoms hidden under unions or negation are not inferred; the original
    // narrowing still handles the rest. Test: cycle_dup::shared_morphism_constraints_are_checked_in_the_size_of_the_union.
    pub(super) fn forced_factors(&self) -> Vec<A> {
        let mut exprs = DigestSet::default();
        let mut sets = DigestSet::default();
        let mut first = DigestMap::default();
        let mut taken = BTreeSet::new();
        let mut parts = vec![self];
        while let Some(p) = parts.pop() {
            match p {
                Part::Expr(e) => {
                    // An exclusive or is a union: no factor, and its halves are not made.
                    if e.xor.is_none()
                        && exprs.insert(e.id)
                        && let Form::And(a, b) = e.form()
                    {
                        parts.push(b);
                        parts.push(a);
                    }
                }
                Part::Bdd(b) => {
                    if let Some((a, positive)) = b.as_literal() {
                        if positive {
                            taken.insert(a.clone());
                        }
                        continue;
                    }
                    if let Bdd::List(c, false) = b {
                        // Lists can share the path to their first block too.
                        let mut path = Vec::new();
                        let mut at = c.as_ref();
                        let block = loop {
                            if let Some(&block) = first.get(&at.id) {
                                break block;
                            }
                            path.push(at.id);
                            match at.left.as_deref() {
                                Some(left) => at = left,
                                None => break at.block.as_ref(),
                            }
                        };
                        for id in path {
                            first.insert(id, block);
                        }
                        let mut stack = vec![block];
                        while let Some(s) = stack.pop() {
                            if !sets.insert(s.id) {
                                continue;
                            }
                            if !s.key.1 {
                                taken.insert(s.key.0.clone());
                            }
                            stack.extend(s.right.as_deref());
                            stack.extend(s.left.as_deref());
                        }
                    }
                }
            }
        }
        taken.into_iter().collect()
    }

    /// The atoms in every value of the part (`.0`) and those in none (`.1`), among the atoms
    /// in it: for a diagram, those taken or refused on every path to `true`; for an expression,
    /// each atom whose refusal, or whose taking, makes the part `false` by three-valued logic.
    ///
    /// One pass finds, for each expression and diagram, the settings of one atom, every other
    /// atom unknown, that make it `false` and those that make it `true`: an `or` is `false`
    /// under a setting that makes both sides `false`, an `and` under one that makes either side
    /// `false`, and a diagram under an atom taken or refused on every path to `true`. An `and`
    /// whose operands are `and`s used nowhere else is read as one `and` of all their other
    /// operands, and the same of `or`s, so a set is made only once for such a nest. The sets
    /// are persistent: the sets of a nest are gathered, sorted and made one set, then joined to
    /// the largest by split and join, so the time is `O(n log n)` in the nodes when the sets
    /// stay small, and at most the nodes times the atoms.
    // Complexity tradeoff (COMPLEXITY.md K32): the naive version evaluates the part once per
    // atom, O(atoms × nodes) (11.5 s on the choice chain with a choice swapped at d = 46). Used:
    // one post-order pass with persistent sets, O(N log N) in the nodes while the sets stay
    // small; since subexpressions are shared, no merging argument bounds the total, so the
    // worst case is still the nodes times the atoms, each set taking memory up to the atoms
    // below its node. Nothing refused, the answer exact. PERF-forced-balanced-union: the sets
    // were `imbl::OrdSet`s, the smaller added to the larger a setting at a time, `O(k log n)`
    // for `k` into `n`, so a balanced conjunction of `n` literals cost `O(n log² n)` (9.47
    // times the instructions at 8n). Now a nest of `and`s (or of `or`s) used nowhere else is
    // one set: its operands' settings are sorted once, `O(n log n)` comparisons with no node
    // made at each level (`settings::union_all`), and the largest operand's set is not copied
    // but joined to, `O(k log(n/k + 1))` (treaps, split and join), so a chain adding one
    // literal at a time to a shared expression stays `O(log n)` per link. Union by split and
    // join alone, level by level, was `O(n)` node copies per level, `O(n log n)` copies in all
    // (9.08 times, 301M instructions at 8192 against imbl's 160M); with the nests, 8.13 times
    // and 148M. The root's settings are read once into a map by the atom's digest, so each
    // atom's two questions cost `O(1)` expected, not `O(log n)` comparisons of rows.
    pub(super) fn forced(&self) -> (Vec<A>, Vec<A>) {
        // Settings `(atom, value)`; `None` is every setting.
        type Set<A> = Option<settings::Tree<A>>;
        fn union<A: Literal>(xs: &[&Set<A>]) -> Set<A> {
            let sets: Vec<&settings::Tree<A>> =
                xs.iter().map(|x| x.as_ref()).collect::<Option<_>>()?;
            Some(settings::union_all(&sets))
        }
        fn meet<A: Literal>(xs: &[&Set<A>]) -> Set<A> {
            let sets: Vec<&settings::Tree<A>> = xs.iter().filter_map(|x| x.as_ref()).collect();
            (!sets.is_empty()).then(|| settings::meet_all(&sets))
        }
        // The settings that make `b` `false`, and those that make it `true`.
        fn of_bdd<A: Literal>(b: &Bdd<A>) -> (Set<A>, Set<A>) {
            let to_set = |(taken, refused): (Vec<A>, Vec<A>)| {
                let off = taken.into_iter().map(|a| (a, false));
                Some(settings::from_keys(
                    off.chain(refused.into_iter().map(|a| (a, true))).collect(),
                ))
            };
            match b {
                Bdd::Leaf(false) => (None, Some(None)),
                Bdd::Leaf(true) => (Some(None), None),
                Bdd::List(..) => (to_set(b.forced_to(true)), to_set(b.forced_to(false))),
            }
        }
        let root = match self {
            Part::Bdd(b) => return b.forced(),
            Part::Expr(e) => e,
        };
        fn operands<A: Literal>(e: &Expr<A>) -> Vec<&Part<A>> {
            match e.form() {
                Form::Not(a) => vec![a],
                Form::Or(a, b) | Form::And(a, b) => vec![a, b],
            }
        }
        // The uses of each expression below the root, one per operand that is it.
        let mut uses: DigestMap<u64, usize> = DigestMap::default();
        let mut stack = vec![root.clone()];
        while let Some(e) = stack.pop() {
            for q in operands(&e) {
                if let Part::Expr(x) = q {
                    let n = uses.entry(x.id).or_insert(0);
                    *n += 1;
                    if *n == 1 {
                        stack.push(x.clone());
                    }
                }
            }
        }
        // A cluster: an `and` with the `and`s below it used by nothing else, read as one `and`
        // of all their other operands, and the same of `or`s; any other expression is a cluster
        // of its own. Each expression is in one cluster, so the clusters' operands are found in
        // one walk of the expressions, and a set is made only for a cluster.
        let same = |e: &Expr<A>, x: &Expr<A>| {
            uses[&x.id] == 1
                && matches!(
                    (e.form(), x.form()),
                    (Form::And(..), Form::And(..)) | (Form::Or(..), Form::Or(..))
                )
        };
        let cluster = |e: &Arc<Expr<A>>| {
            let mut out: Vec<Part<A>> = Vec::new();
            let mut members = vec![e.clone()];
            while let Some(m) = members.pop() {
                for q in operands(&m).into_iter().rev() {
                    match q {
                        Part::Expr(x) if same(e, x) => members.push(x.clone()),
                        _ => out.push(q.clone()),
                    }
                }
            }
            out
        };
        let mut exprs: DigestMap<u64, (Set<A>, Set<A>)> = DigestMap::default();
        let mut nodes: DigestMap<u64, (Set<A>, Set<A>)> = DigestMap::default();
        // An expression, with its cluster's operands once they are found.
        type Pending<A> = (Arc<Expr<A>>, Option<Vec<Part<A>>>);
        let mut stack: Vec<Pending<A>> = vec![(root.clone(), None)];
        while let Some((e, ops)) = stack.pop() {
            let Some(ops) = ops else {
                // Met again when two clusters share an operand, as `e & !e` does
                // (`tests::three_valued_operations_keep_the_assignments`).
                if exprs.contains_key(&e.id) {
                    continue;
                }
                let ops = cluster(&e);
                let mut below = Vec::new();
                for q in &ops {
                    match q {
                        Part::Expr(x) if !exprs.contains_key(&x.id) => below.push(x.clone()),
                        Part::Bdd(b @ Bdd::List(..)) => {
                            nodes.entry(b.id()).or_insert_with(|| of_bdd(b));
                        }
                        _ => {}
                    }
                }
                stack.push((e, Some(ops)));
                stack.extend(below.into_iter().map(|x| (x, None)));
                continue;
            };
            // Proof that `e` is not yet in `exprs`. It was not when `(e, Some(ops))` was pushed,
            // just after the check above. Until it is popped, only entries pushed after it are
            // popped: `(x, None)` for `x` in `below`, and what those push in turn, so each
            // concerns an operand of `e`'s cluster or, by induction, an operand of the cluster of
            // one of those. `e` is put in `exprs` only at a pop of an `(e, Some(_))`, so in that
            // time only if `e` is an operand, at some depth, of its own cluster. On such a cycle no
            // expression is ever put in `exprs`: each is put there only after the sets of all its
            // cluster's operands are read from `exprs` (`exprs[&x.id]` below, which panics on one
            // missing), so the first of the cycle to be put there would need its operand on the
            // cycle there before it.
            debug_assert!(
                !exprs.contains_key(&e.id),
                "an expression's sets are made once"
            );
            let sets: Vec<(Set<A>, Set<A>)> = ops
                .iter()
                .map(|q| match q {
                    Part::Expr(x) => exprs[&x.id].clone(),
                    Part::Bdd(b @ Bdd::List(..)) => nodes[&b.id()].clone(),
                    Part::Bdd(b) => of_bdd(b),
                })
                .collect();
            let offs: Vec<&Set<A>> = sets.iter().map(|s| &s.0).collect();
            let ons: Vec<&Set<A>> = sets.iter().map(|s| &s.1).collect();
            let found = match e.form() {
                Form::Not(_) => (ons[0].clone(), offs[0].clone()),
                Form::Or(..) => (meet(&offs), union(&ons)),
                Form::And(..) => (union(&offs), meet(&ons)),
            };
            exprs.insert(e.id, found);
        }
        // The settings that make the root `false`, each atom's found by its digest.
        let mut off: Option<DigestMap<u64, Vec<(A, bool)>>> = None;
        if let Some(s) = &exprs[&root.id].0 {
            let mut by_digest: DigestMap<u64, Vec<(A, bool)>> = DigestMap::default();
            for k in settings::keys(s) {
                by_digest.entry(k.0.digest()).or_default().push(k);
            }
            off = Some(by_digest);
        }
        let makes_false = |a: &A, v: bool| {
            off.as_ref().is_none_or(|m| {
                m.get(&a.digest())
                    .is_some_and(|ks| ks.iter().any(|(b, w)| *w == v && b == a))
            })
        };
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

    /// The operands of the unions at the top of the part, when there are two or more and no
    /// atom stands in two of them. Each operand is walked until an atom met in an earlier one,
    /// so the cost is the size of the part.
    pub(super) fn disjoint_disjuncts(&self) -> Option<Vec<Part<A>>> {
        let (mut seen, mut out) = (DigestSet::default(), Vec::new());
        let mut stack = vec![self];
        while let Some(p) = stack.pop() {
            // The two halves of an exclusive or share its first atom, so no union holding one
            // has disjoint disjuncts; answered without making its halves.
            if let Part::Expr(e) = p
                && e.xor.is_some()
            {
                return None;
            }
            if let Part::Expr(e) = p
                && let Form::Or(a, b) = e.form()
            {
                if seen.insert(e.id) {
                    stack.push(b);
                    stack.push(a);
                }
                continue;
            }
            out.push(p.clone());
        }
        if out.len() < 2 {
            return None;
        }
        let mut owner: BTreeMap<&A, usize> = BTreeMap::new();
        for (i, d) in out.iter().enumerate() {
            let alone = d.atoms(&mut |a| *owner.entry(a).or_insert(i) == i);
            if !alone {
                return None;
            }
        }
        Some(out)
    }

    /// Whether `f` holds of every atom, each node and expression visited once, from a stack:
    /// an expression's first operand before its second. Diagram nodes and expressions share one
    /// set of ids seen, so a diagram under two expressions is visited once.
    pub(super) fn atoms<'a>(&'a self, f: &mut impl FnMut(&'a A) -> bool) -> bool {
        let mut seen = DigestSet::default();
        self.walk_atoms(&mut seen, f, false)
    }

    /// The atoms on nodes not yet walked by this traversal. A false callback ends the
    /// whole traversal; a caller reusing `seen` must not resume after such an early end.
    pub(super) fn atoms_unseen<'a>(
        &'a self,
        seen: &mut DigestSet<u64>,
        f: &mut impl FnMut(&'a A) -> bool,
    ) -> bool {
        self.walk_atoms(seen, f, true)
    }

    fn walk_atoms<'a>(
        &'a self,
        seen: &mut DigestSet<u64>,
        f: &mut impl FnMut(&'a A) -> bool,
        shared_sets: bool,
    ) -> bool {
        let mut stack = vec![self];
        while let Some(p) = stack.pop() {
            match p {
                Part::Bdd(b) => {
                    if !b.atoms_unseen(seen, f, shared_sets) {
                        return false;
                    }
                }
                Part::Expr(e) => {
                    if seen.insert(e.id) {
                        let (_, a, b) = e.form().operands();
                        stack.extend(b);
                        stack.push(a);
                    }
                }
            }
        }
        true
    }

    /// Calls `f` on atoms such that every setting of the atoms that makes the part `to` either
    /// holds one of them or makes the part `to` with no atom holding. A diagram gives the atoms
    /// its paths to `to` take (`Bdd::taken_toward`); `!x` gives those of `x` to `!to`, and
    /// `x | y` and `x & y` those of both operands to `to`. By induction: a setting that makes
    /// `x | y` or `x & y` `to` makes one or both operands `to` with the same atoms, and when it
    /// holds no atom given for them, the setting that holds no atom makes those operands `to`
    /// as well, so the whole too. An atom refused on every path to `to`, as `r` in `!r & s`
    /// to `true`, is not given. Each expression and diagram node is walked once for each value,
    /// by `seen` (shared across calls, so a node met again is passed over), from a stack, so the
    /// time is linear in the nodes.
    pub(super) fn taken_toward<'a>(
        &'a self,
        to: bool,
        seen: &mut DigestSet<(u64, bool)>,
        f: &mut impl FnMut(&'a A),
    ) {
        let mut stack = vec![(self, to)];
        while let Some((p, to)) = stack.pop() {
            match p {
                Part::Bdd(b) => b.taken_toward(to, seen, f),
                Part::Expr(e) => {
                    if seen.insert((e.id, to)) {
                        match e.form() {
                            Form::Not(a) => stack.push((a, !to)),
                            Form::Or(a, b) | Form::And(a, b) => {
                                stack.push((b, to));
                                stack.push((a, to));
                            }
                        }
                    }
                }
            }
        }
    }

    /// Each distinct atom once, in the order first met. One atom can stand on several nodes,
    /// and a caller that tests or splits on each atom must meet it once.
    // Complexity tradeoff: the atoms met are filed by digest. A digest met with one atom keeps
    // that atom alone, so an atom whose digest no other atom has costs O(1) expected; a digest
    // met with a second distinct atom keeps an ordered set of its atoms, so a class of k atoms
    // of one digest costs O(log k) comparisons an atom, O(n log n) in all even when a program
    // writes n distinct atoms of one digest (PERF-distinct-atoms-tied-digest, benchmark
    // `distinct_atoms_of_one_digest_scales`). Two methods given up: a chain of the atoms of each
    // digest, compared one by one, which cost n(n - 1)/2 comparisons on n atoms of one digest
    // (7.6 ms at 512, 1.57 s at 4096); and one sorted set of all the atoms, O(log n)
    // comparisons per atom, each comparing digests, the log factor that took
    // `the_emptiness_of_a_meet_of_tuple_differences_scales` over 9 (PERF-kernel-payload-shape-
    // under9). Cost: one word a digest met once, a B-tree node share a tied atom; the atoms are
    // borrowed from the part, never copied for the sets.
    pub(super) fn distinct_atoms(&self) -> Vec<A> {
        enum Bucket<'a, A> {
            One(&'a A),
            Many(BTreeSet<&'a A>),
        }
        let mut by_digest: DigestMap<u64, Bucket<'_, A>> = DigestMap::default();
        let mut atoms = Vec::new();
        self.atoms(&mut |a| {
            let new = match by_digest.entry(a.digest()) {
                Entry::Vacant(e) => {
                    e.insert(Bucket::One(a));
                    true
                }
                Entry::Occupied(mut e) => match e.get_mut() {
                    Bucket::One(b) if *b == a => false,
                    Bucket::One(b) => {
                        let tied = BTreeSet::from([*b, a]);
                        *e.get_mut() = Bucket::Many(tied);
                        true
                    }
                    Bucket::Many(tied) => tied.insert(a),
                },
            };
            if new {
                atoms.push(a.clone());
            }
            true
        });
        atoms
    }

    /// The atoms, if the part is their union and nothing else.
    /// Each expression is visited once, from a stack, its first operand before its second.
    pub(super) fn union_rows(&self) -> Option<Vec<A>> {
        let (mut seen, mut out) = (DigestSet::default(), Vec::new());
        let mut stack = vec![self];
        while let Some(p) = stack.pop() {
            match p {
                Part::Expr(e) => {
                    if !seen.insert(e.id) {
                        continue;
                    }
                    // An exclusive or's halves are meets, not rows; they are not made to show it.
                    if e.xor.is_some() {
                        return None;
                    }
                    let Form::Or(a, b) = e.form() else {
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

    /// The atoms the part takes and those it refuses, when the part is their meet: `true`,
    /// a literal, a meet of literals, a meet of such parts, or the complement of a union of
    /// atoms. `None` for any other part, `false` included. Each expression is visited once,
    /// from a stack, so the cost is the size of the part.
    pub(super) fn clause(&self) -> Option<(Vec<A>, Vec<A>)> {
        let (mut seen, mut taken, mut refused) = (DigestSet::default(), Vec::new(), Vec::new());
        let mut stack = vec![self];
        while let Some(p) = stack.pop() {
            match p {
                Part::Bdd(Bdd::Leaf(true)) => {}
                Part::Bdd(Bdd::Leaf(false)) => return None,
                Part::Bdd(b) => match b.as_literal() {
                    Some((a, true)) => taken.push(a.clone()),
                    Some((a, false)) => refused.push(a.clone()),
                    None => {
                        for (a, t) in b.chain(Op::And)? {
                            match t {
                                true => taken.push(a.clone()),
                                false => refused.push(a.clone()),
                            }
                        }
                    }
                },
                Part::Expr(e) => {
                    if !seen.insert(e.id) {
                        continue;
                    }
                    // An exclusive or is an `Or`: decline before its halves are made.
                    if e.is_or() {
                        return None;
                    }
                    match e.form() {
                        Form::And(a, b) => {
                            stack.push(b);
                            stack.push(a);
                        }
                        Form::Not(Part::Bdd(b)) if b.as_literal().is_some() => {
                            match b.as_literal() {
                                Some((a, true)) => refused.push(a.clone()),
                                Some((a, false)) => taken.push(a.clone()),
                                // The guard tested `b.as_literal().is_some()`, and
                                // `as_literal` reads `b` alone.
                                None => unreachable!("tested by the guard"),
                            }
                        }
                        Form::Not(x) => refused.extend(x.union_rows()?),
                        // `is_or` above holds of every form `Or` (and of a form not yet made).
                        Form::Or(..) => unreachable!("an `Or` was declined by `is_or`"),
                    }
                }
            }
        }
        Some((taken, refused))
    }

    /// The atoms met and the atoms joined, if the part is a list that is the intersection of
    /// the first with the union of the second (all values when none): a block of value `false`
    /// that refuses each atom met, then one of value `true` that takes each atom joined.
    pub(super) fn meet_rows(&self) -> Option<(Vec<A>, Option<Vec<A>>)> {
        let Part::Bdd(list @ Bdd::List(_, false)) = self else {
            return None;
        };
        let (mut met, mut joined) = (Vec::new(), None);
        for (i, (v, c)) in list.cells().enumerate() {
            if i > 1 || v != (i == 1) {
                return None;
            }
            let mut atoms = Vec::new();
            for (a, taken) in set::iter(Some(&c.block)) {
                if *taken != v {
                    return None;
                }
                atoms.push(a.clone());
            }
            match v {
                false => met = atoms,
                true => joined = Some(atoms),
            }
        }
        Some((met, joined))
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
            Part::Expr(e) => Err(e.form()),
        }
    }
}

/// Two lists, cells, sets, expressions or parts of one universe to compare in `order` (module
/// `types`).
pub(super) enum Walk<'a, A: Literal> {
    Bdds(&'a Bdd<A>, &'a Bdd<A>),
    /// The root cells of two lists, each of one or more blocks.
    Cells(&'a Cell<A>, &'a Cell<A>),
    /// Two blocks, or the sets of two exclusive ors.
    Sets(&'a Set<A>, &'a Set<A>),
    /// Two sets, or two subtrees at one place in two sets, of tied digests, compared by their
    /// literals in order, a prefix first, no subtree before one; their digests are not compared,
    /// since a subtree's literals follow the run's draw of priorities.
    SetsInOrder(Option<&'a Set<A>>, Option<&'a Set<A>>),
    Exprs(&'a Expr<A>, &'a Expr<A>),
    Parts(&'a Part<A>, &'a Part<A>),
    /// The rest of two sequences of blocks of tied digests, compared block by block in order.
    CellRest(Box<Rest<'a, Cell<A>>>),
    /// The rest of two sets of tied digests whose shapes differ, compared literal by literal in
    /// order.
    SetRest(Box<Rest<'a, Set<A>>>),
}

/// A node of a treap read in order by [`Rest`]: its id, the number of keys under it, and its two
/// sides.
pub(super) trait InOrder {
    fn id(&self) -> u64;
    fn len(&self) -> usize;
    fn left(&self) -> Option<&Self>;
    fn right(&self) -> Option<&Self>;
}

impl<A: Literal> InOrder for Cell<A> {
    fn id(&self) -> u64 {
        self.id
    }
    fn len(&self) -> usize {
        self.len
    }
    fn left(&self) -> Option<&Self> {
        self.left.as_deref()
    }
    fn right(&self) -> Option<&Self> {
        self.right.as_deref()
    }
}

impl<A: Literal> InOrder for Set<A> {
    fn id(&self) -> u64 {
        self.id
    }
    fn len(&self) -> usize {
        Set::len(self)
    }
    fn left(&self) -> Option<&Self> {
        self.left.as_deref()
    }
    fn right(&self) -> Option<&Self> {
        self.right.as_deref()
    }
}

/// A piece of a sequence still to be read in order: every key under a node, or the node's own.
pub(super) enum Piece<'a, N> {
    Tree(&'a N),
    Key(&'a N),
}

/// What is left of two sequences, of blocks (the cells of two lists) or of literals (two sets),
/// compared key by key in order (module `types`, `walk`): for each, the pieces still to read,
/// the next last.
///
/// Complexity tradeoff: two sequences whose digests tie were compared by their roots, then
/// their subtrees, which is `O(1)` where the roots differ but reads the shapes, which follow the
/// run's draw of priorities (module [`crate::priority`]), so the order of two distinct sequences
/// of one digest would follow the draw. Read in order, they are compared by their contents only,
/// in `O(k + d)` for a first difference at the `k`-th key and treaps of depth `d` (the nodes
/// opened are those on the paths to the first `k + 1` keys), `O(n)` at worst, as the walk by
/// roots was. Two pieces that are one node are passed over whole, as are two found equal before.
/// Given up: one allocation of the box and two of its stacks for each pair of sequences compared
/// this way; two equal sets have one shape and are compared without it (`SetsInOrder`).
pub(super) struct Rest<'a, N> {
    a: Vec<Piece<'a, N>>,
    b: Vec<Piece<'a, N>>,
}

impl<'a, N: InOrder> Rest<'a, N> {
    pub(super) fn new(a: &'a N, b: &'a N) -> Box<Rest<'a, N>> {
        Box::new(Rest {
            a: vec![Piece::Tree(a)],
            b: vec![Piece::Tree(b)],
        })
    }

    /// The next two keys' nodes, one of each sequence, or the order of the sequences' lengths
    /// when one of them has no more: `Err(Equal)` when both end together. `equal` says whether
    /// two nodes, by id, were found equal before.
    pub(super) fn next(
        &mut self,
        equal: impl Fn(u64, u64) -> bool,
    ) -> Result<(&'a N, &'a N), Ordering> {
        /// Puts the pieces of `n`'s subtree in place of it: the right, the node, the left.
        fn open<'a, N: InOrder>(pieces: &mut Vec<Piece<'a, N>>, n: &'a N) {
            pieces.extend(n.right().map(Piece::Tree));
            pieces.push(Piece::Key(n));
            pieces.extend(n.left().map(Piece::Tree));
        }
        loop {
            match (self.a.pop(), self.b.pop()) {
                (None, None) => return Err(Ordering::Equal),
                (None, Some(_)) => return Err(Ordering::Less),
                (Some(_), None) => return Err(Ordering::Greater),
                (Some(Piece::Key(x)), Some(Piece::Key(y))) => return Ok((x, y)),
                (Some(Piece::Tree(x)), Some(Piece::Tree(y))) => {
                    if x.id() == y.id() || equal(x.id(), y.id()) {
                        continue;
                    }
                    // The larger is opened, both when of one size, so that two subtrees that
                    // hold the same keys meet as pieces.
                    match x.len().cmp(&y.len()) {
                        Ordering::Less => {
                            self.a.push(Piece::Tree(x));
                            open(&mut self.b, y);
                        }
                        Ordering::Greater => {
                            open(&mut self.a, x);
                            self.b.push(Piece::Tree(y));
                        }
                        Ordering::Equal => {
                            open(&mut self.a, x);
                            open(&mut self.b, y);
                        }
                    }
                }
                (Some(Piece::Tree(x)), Some(k)) => {
                    open(&mut self.a, x);
                    self.b.push(k);
                }
                (Some(k), Some(Piece::Tree(y))) => {
                    self.a.push(k);
                    open(&mut self.b, y);
                }
            }
        }
    }
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
    //! The exclusive or of a set of two or more atoms is one expression ([`node`]), kept in a
    //! table of the thread by the set's id and the constant, with the complement, the other
    //! constant, made beside it; an exclusive or of one atom is its literal. Its digests are the
    //! set's and the constant's, so they, the order of parts (`Walk::Exprs` in module `types`)
    //! and its printed form are functions of its atoms and constant alone, the same in every run
    //! whatever shape the set's tree takes under the run's priorities (rule
    //! deterministic-checking, row PERF-xor-shape-free). A set with a literal added or removed
    //! has `O(log n)` new tree nodes in expectation and one new expression.
    //!
    //! Its form is made when first read ([`Expr::form`], [`halves`]): `p&!q | !p&q`, or
    //! `p&q | !p&!q` with the constant `true`, for `p` the literal of the smallest atom and `q`
    //! the exclusive or of the others. The digest, the order of parts and the tables need no
    //! more, and most forms are never read (step KERNEL-parity-lazy-halves).
    //!
    //! The table holds each node weakly, and a node leaves it when it is dropped (step
    //! TABLE-life); one dropped is made again from its set when its complement is asked for
    //! ([`mate`]), equal to the one dropped.
    //!
    //! An exclusive or is recognized when it is built from two others ([`xor_of`], [`xor_choice`]),
    //! and a literal is one, of one atom; any other part is not taken for one. So the one form is
    //! that of these constructions, not of every part equal to a parity: `u&v | !u&!v` and
    //! `(u|v) & (!u|!v)` are read when each meet or union is an expression or a chain of two
    //! literals, but not `(u|v) & !(u&v)` with `u&v` an expression (its complement is a `Not`), nor
    //! a sum of products such as `a&!b&!c | !a&b&!c | !a&!b&c | a&b&c` (cross-review of
    //! PERF-xor-shape-free: Sol F5, Gemini F5).
    //!
    //! Complexity tradeoff (PERF-xor-shape-free, COMPLEXITY.md K123): the naive method built the
    //! exclusive or over the set's tree, a node per tree node joining its subtrees' and its atom,
    //! `O(log n)` expected new expressions per literal added, `O(1)` each; its digest and form
    //! followed the tree's shape, so the set's priorities had to be a fixed hash, and a program
    //! could choose literals whose set is a path, `O(n)` per literal. Used: one expression per set,
    //! `O(1)` plus the set's depth per literal added, its digest the set's sum, so the priorities
    //! are drawn per run and no longer a fixed hash: every node's expected depth is at most
    //! `T0 + n(n - 1)/p + 2c H_n` (Seidel and Aragon, "Randomized search trees", Algorithmica 16,
    //! 1996, which holds for 5-wise independent priorities and so for the 8-wise ones of
    //! module `set`), with no condition on the hash
    //! beyond `T0`, the literals sharing a digest, which a program can still make large (plan row
    //! PERF-set-tied-digest-depth). Given up: reading the whole
    //! form of an exclusive or of `n` atoms makes its `n - 1` nested ones, a removal from a set
    //! each, `O(n log n)` expected, where the tree's form was `O(n)`.

    use std::collections::HashMap;
    use std::sync::{Arc, Weak};

    use super::set::{self, Set, Tree};
    use super::{Bdd, Digest, Expr, Form, Literal, Op, Operands, Part, mix};

    /// An exclusive or: the set of its atoms, each taken, and the constant joined to them.
    pub(super) type Tag<A> = (Arc<Set<A>>, bool);

    /// The live exclusive ors of a thread, by the id of their set and their constant.
    pub(in crate::types) type XorTable<A> =
        HashMap<(u64, bool), Weak<Expr<A>>, std::hash::BuildHasherDefault<Digest>>;

    /// The exclusive or of the one literal on `atom`, taken or refused.
    fn literal<A: Literal>(atom: &A, taken: bool) -> Tag<A> {
        (set::single((atom.clone(), true)), !taken)
    }

    /// Whether `x` is the complement of `y`: one set of atoms, compared by contents when the
    /// two were made on two threads ([`set::same`]), and the other constant.
    pub(super) fn opposite<A: Literal>(x: &Tag<A>, y: &Tag<A>) -> bool {
        x.1 != y.1 && set::same(&x.0, &y.0)
    }

    /// The exclusive or of `x` and `y`, complemented when `flip` holds. The complement is made
    /// here, not by `not` on the result: the node made holds its complement and the complement
    /// holds it only weakly, so `join(..).not()` returned a node whose complement was dropped,
    /// and a later `not` made it again (cross-review of PERF-xor-shape-free, round 2, Sol X2-F3).
    fn join<A: Literal>(x: &Tag<A>, y: &Tag<A>, flip: bool) -> Part<A> {
        Part::xor(
            set::symmetric(&Some(x.0.clone()), &Some(y.0.clone())),
            (x.1 != y.1) != flip,
        )
    }

    /// The live exclusive or of the set `id` and `constant`.
    fn found<A: Literal>(id: u64, constant: bool) -> Option<Part<A>> {
        A::table(|t| t.xors.get(&(id, constant)).and_then(Weak::upgrade)).map(Part::Expr)
    }

    impl<A: Literal> Part<A> {
        /// The part as an exclusive or in its one form: a literal, or a node [`Part::xor`] made.
        pub(super) fn xor_tag(&self) -> Option<Tag<A>> {
            match self {
                Part::Bdd(b) => b.as_literal().map(|(a, taken)| literal(a, taken)),
                Part::Expr(e) => e.xor.clone(),
            }
        }

        /// The atoms of the part as an exclusive or in its one form ([`Part::xor_tag`]), in
        /// order, and the constant joined to them; `None` for a part that is not one.
        pub(in crate::types) fn exclusive_or(&self) -> Option<(Vec<A>, bool)> {
            let (atoms, constant) = self.xor_tag()?;
            let atoms = set::iter(Some(&atoms)).map(|(a, _)| a.clone());
            Some((atoms.collect(), constant))
        }

        /// Whether the part is an exclusive or in its one form ([`Part::xor_tag`]), its atoms
        /// not collected.
        pub(in crate::types) fn is_exclusive_or(&self) -> bool {
            self.xor_tag().is_some()
        }

        /// The exclusive or of `atoms`, each taken, and `constant`, in its one form.
        pub(super) fn xor(atoms: Tree<A>, constant: bool) -> Part<A> {
            let Some(s) = atoms else {
                return Part::leaf(constant);
            };
            if let Some((atom, _)) = set::single_key(&s) {
                let x = Part::literal(atom.clone());
                if constant { x.not() } else { x }
            } else if let Some(x) = found(s.id, constant) {
                x
            } else if let Some(n) = found(s.id, !constant) {
                // When only the complement lives, the one asked for is made and holds that live
                // complement, which keeps it without holding it, as below. Made beside a
                // complement of its own, it would replace the live one in the table, and one
                // function would have two nodes (test
                // `an_exclusive_or_is_found_again_when_only_its_complement_lives`); taken as
                // `n.not()`, it would hold `n` only weakly, and `n` would be made again once the
                // caller drops it (cross-review round 3, Claude R3-C1).
                let x = node(&s, constant);
                // `node` makes an expression, and `found` finds only one.
                let (Part::Expr(e), Part::Expr(m)) = (&x, &n) else {
                    unreachable!("exclusive ors of two or more atoms are expressions")
                };
                let _ = e.complement.set(n.clone());
                m.set_back(e);
                x
            } else {
                // The node asked for holds its complement, so neither is made only to be freed.
                let x = node(&s, constant);
                let n = node(&s, !constant);
                // `node` makes an expression.
                let (Part::Expr(e), Part::Expr(m)) = (&x, &n) else {
                    unreachable!("exclusive ors of two or more atoms are expressions")
                };
                let _ = e.complement.set(n.clone());
                m.set_back(e);
                x
            }
        }
    }

    /// The exclusive or of the set `s` of two or more atoms and `constant`, made with its digests
    /// alone and kept in the thread's table; its form is made when first read ([`halves`]). The
    /// digests are the set's, sums over its literals, with the constant, so they are the same for
    /// every shape of the set's tree.
    fn node<A: Literal>(s: &Arc<Set<A>>, constant: bool) -> Part<A> {
        let digest = |d: u64| mix(mix(11, d), u64::from(constant));
        let x = Part::expr_unmade(
            digest(set::digest(Some(s))),
            digest(set::name_digest(Some(s))),
            (s.clone(), constant),
        );
        // `Part::expr_unmade` makes an expression (`Part::made`).
        let Part::Expr(e) = &x else {
            unreachable!("`Part::expr_unmade` makes an expression")
        };
        // An entry left by a node dropped on another thread is replaced.
        A::table(|t| t.xors.insert((s.id, constant), Arc::downgrade(e)));
        x
    }

    /// The form of the exclusive or of the set `s` of two or more atoms and `constant`: for `p`
    /// the literal of its smallest atom and `q` the exclusive or of the others, `p&!q | !p&q`
    /// when `false` and `p&q | !p&!q` when `true`, its two meets in their order. A function of
    /// the set's atoms, not of its tree's shape.
    pub(super) fn halves<A: Literal>(s: &Arc<Set<A>>, constant: bool) -> Form<A> {
        let first = set::min(s);
        let p = Part::literal(first.0.clone());
        let q = Part::xor(set::remove(s, first), false);
        let (np, nq) = (p.not(), q.not());
        let (x, y) = if constant {
            (meet(&p, &q), meet(&np, &nq))
        } else {
            (meet(&p, &nq), meet(&np, &q))
        };
        // The form is made when first read (`Part::expr_unmade`), so it cannot be folded. Proof
        // that neither operand is a leaf ([`Form`]): `s` has two or more atoms (this function's
        // contract), so `p` is the literal of one atom and `q` the exclusive or of one or more
        // others. `p`, `q`, `!p` and `!q` are each true at some assignment of their atoms and
        // false at another. `x` and `y` each meet one of `p`, `!p` with one of `q`, `!q`, over
        // disjoint atoms, so each is true where both operands are and false where one is not:
        // not constant. `meet` returns either `Part::connect` of two non-leaves, which is an
        // expression, or the diagram `Bdd::assemble` or `zip` builds of that meet, which by
        // their correctness is that function; a leaf is a constant, so neither result is one.
        let form = if x.before(&y) {
            Form::Or(x, y)
        } else {
            Form::Or(y, x)
        };
        form.assert_no_leaf_operand();
        form
    }

    /// `a & b` for `a` and `b` each a literal or an exclusive or made by [`node`] (or the
    /// complement of one), over disjoint sets of atoms: the halves of an exclusive or, which
    /// [`halves`] takes from its smallest atom and the others. It is the part `a.zip(b, Op::And)`
    /// makes, without the search `Connect::zipped` runs, none of whose rules fits such operands:
    /// they are not complements and not equal, since their atoms differ; two literals are two
    /// lists, joined as a chain, which is built here at once; neither is an operand of
    /// `u&v | !u&!v` under `Or`, since the halves of an exclusive or are meets, which are no
    /// exclusive or in their one form; an exclusive or is no choice, since both of its halves'
    /// operands have their complements in the other half (two conditions fit); and they are not
    /// `(!c|x) & (c|y)`, since the complement of a meet made here is a union or `Not` of it, never
    /// a meet over other atoms.
    /// So the meet is the expression of the two, ordered as `Connect::zipped` orders them.
    /// The test `types::bdd::tests::the_halves_of_exclusive_ors_meet_as_zip_meets_them`
    /// compares the two on random exclusive ors. The search took about three quarters of the work
    /// of parity built a literal at a time (SCALE-log-offset, COMPLEXITY K87).
    pub(super) fn meet<A: Literal>(a: &Part<A>, b: &Part<A>) -> Part<A> {
        if let (Part::Bdd(x), Part::Bdd(y)) = (a, b) {
            // Two literals on two atoms meet as the complement of the block that refuses both:
            // the list `Bdd::and_literal` makes, without its search of the list for the atom.
            // Both operands are lists only as two literals on two atoms: the one caller,
            // `halves`, passes the literal of the smallest atom of `s` (or its complement) and
            // the exclusive or of the other atoms (or its complement), which is a list only
            // when it has one atom (`Part::xor`), and then it is that atom's literal.
            let (Some((u, s)), Some((v, t))) = (x.as_literal(), y.as_literal()) else {
                unreachable!("two lists met here are literals")
            };
            assert!(
                u != v,
                "the halves of an exclusive or meet over disjoint atoms"
            );
            let block = set::insert(Some(&set::single((u.clone(), !s))), (v.clone(), !t));
            return Part::Bdd(Bdd::assemble(vec![(false, Some(block))], &Bdd::Leaf(true)));
        }
        let (a, b) = if a.before(b) { (a, b) } else { (b, a) };
        Part::connect(Op::And, a.clone(), b.clone())
    }

    /// The exclusive or of the set `s` of two or more atoms and `constant`, the complement of the
    /// one with the other constant: the live one of the table, or made again.
    pub(super) fn mate<A: Literal>(s: &Arc<Set<A>>, constant: bool) -> Part<A> {
        found(s.id, constant).unwrap_or_else(|| node(s, constant))
    }

    /// The two operands of `p` under `op`, each an exclusive or in its one form.
    fn pair<A: Literal>(p: &Part<A>, op: Op) -> Option<[Tag<A>; 2]> {
        match p {
            // A chain is listed only when it has two literals, so a long one costs constant time
            // here.
            Part::Bdd(b) if b.chain_len(op) != Some(2) => return None,
            // An exclusive or is a union, and its halves are meets, so neither is one in its one
            // form; its halves are not made to show it.
            Part::Expr(e) if e.xor.is_some() => return None,
            _ => {}
        }
        match p.operands(op)? {
            Operands::Two(x, y) => Some([x.xor_tag()?, y.xor_tag()?]),
            Operands::Chain(d) => match d.chain(op)?[..] {
                [(a, s), (b, t)] => Some([literal(a, s), literal(b, t)]),
                // A list reaches here only past the first test above, as a chain of two.
                _ => unreachable!("a chain of two literals lists two"),
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
        Some(join(&u, &v, op == Op::Or))
    }

    /// The choice `c&x | !c&y` as an exclusive or in its one form, when `y` is `!x` and `c` and `x`
    /// are exclusive ors in their one form: `!(c ^ x)`.
    pub(super) fn xor_choice<A: Literal>(c: &Part<A>, x: &Part<A>, y: &Part<A>) -> Option<Part<A>> {
        let (tx, ty) = (x.xor_tag()?, y.xor_tag()?);
        if !opposite(&tx, &ty) {
            return None;
        }
        Some(join(&c.xor_tag()?, &tx, true))
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
    //! the sequences of the blocks before and after it, its priority drawn once per run from one
    //! literal of its block ([`priority`]), ties broken by position, the earlier above. So one
    //! sequence has one shape in a run, whatever edits made it; the shape follows the draw, so a
    //! cell's digests are folds of its blocks in order ([`folded`]), the same for every shape, and
    //! the order of types compares two sequences of equal digests by their blocks in order. The
    //! cells are shared through a table of the thread by
    //! their children and block: one list is one cell. Each cell keeps, made on first use, the atoms of its blocks, so the
    //! block of an atom is found from the root in `O(log m)` for `m` blocks. A list grown a
    //! literal at a time from one literal also keeps, on its root cell, an index of its blocks
    //! ([`Index`]), which finds that block by two lookups instead. A chain of literals
    //! joined to a list ([`Bdd::or_literal`]) adds each literal to the first block, or puts a block
    //! of it first; a literal on an atom the list holds is first set false there, which removes it
    //! from its block or cuts the list at its block. Each such change rebuilds the cells on the
    //! paths to the blocks it changes, `O(log m)` cells in expectation, each looked up in the
    //! table in `O(1)` expected.

    // Complexity tradeoff (COMPLEXITY.md K63): the naive join of a chain to a diagram is the
    // apply of `Bdd::zip`, which builds diagrams of up to `k` nodes at the `k`-th atom, so a
    // list built a literal at a time costs O(m²) for m literals. Used: the list is a treap of
    // hash-consed cells, and a literal joined to it rebuilds the cells on the paths to the blocks
    // it changes, O(log m) cells in expectation, each found in the table in O(1) expected.
    // Given up: the balance holds only in expectation over the run's draw of priorities; each
    // live cell has a weak entry in its thread's table and caches its atoms and
    // views once read; a larger constant factor per literal than a plain node.

    use std::collections::HashMap;
    use std::sync::atomic::Ordering as Atomic;
    use std::sync::{Arc, OnceLock, Weak};

    use super::set::{self, Key, NEXT, Set, Tree};
    use super::{Bdd, Digest, Literal, Op, Owned, Part, mix};
    use crate::priority::Priorities;
    use treap::Keyed;

    mod treap;

    /// A node of a sequence of blocks: a block and the sequences of the blocks before and after
    /// it. A cell that is the root of a list's sequence is the list, with the value of its first
    /// block beside it ([`Bdd::List`]).
    pub(in crate::types) struct Cell<A: Literal> {
        /// The cell's id, unique among the nodes of the process, and the next id, kept for it:
        /// the list of first value `v` has the id `id + v`.
        pub(in crate::types) id: u64,
        /// A hash of the blocks in order, equal for equal sequences ([`folded`]).
        pub(in crate::types) digest: u64,
        pub(in crate::types) name_digest: u64,
        prio: u64,
        /// The number of blocks.
        pub(super) len: usize,
        /// [`R`] to the power `len`, wrapping: what [`folded`] multiplies the digest of the
        /// blocks before a sequence by.
        pow: u64,
        pub(in crate::types) left: Seq<A>,
        pub(in crate::types) block: Arc<Set<A>>,
        pub(in crate::types) right: Seq<A>,
        /// The atoms of the blocks, made on first use.
        atoms: OnceLock<imbl::OrdSet<A>>,
        /// The index of the blocks, when the cell is the root of a list grown a literal at a
        /// time ([`Index`]).
        index: OnceLock<Index<A>>,
        /// The first node of the list of each first value, as [`Bdd::branch`] shows it: its `hi`
        /// and `lo`, made on first use.
        view: [OnceLock<(Bdd<A>, Bdd<A>)>; 2],
    }

    /// A sequence of blocks: its root, or `None` when empty.
    pub(in crate::types) type Seq<A> = Option<Arc<Cell<A>>>;

    /// The live cells of a thread, by the ids of their children and block, each held weakly: a cell
    /// leaves the table when it is dropped (step TABLE-life).
    pub(in crate::types) type CellTable<A> =
        HashMap<(u64, u64, u64), Weak<Cell<A>>, std::hash::BuildHasherDefault<Digest>>;

    /// A cell leaves its thread's table, and its children and views are freed in a loop (module
    /// `deep`).
    impl<A: Literal> Drop for Cell<A> {
        fn drop(&mut self) {
            let key = (id(&self.left), self.block.id, id(&self.right));
            A::untable(|t| {
                // Another cell of the key may have taken the entry since, or none was made here.
                if let std::collections::hash_map::Entry::Occupied(e) = t.cells.entry(key)
                    && std::ptr::eq(e.get().as_ptr(), self)
                {
                    e.remove();
                }
            });
            for c in [self.left.take(), self.right.take()].into_iter().flatten() {
                Owned::Cell(c).release();
            }
            for v in &mut self.view {
                if let Some((hi, lo)) = v.take() {
                    Owned::Part(Part::Bdd(hi)).release();
                    Owned::Part(Part::Bdd(lo)).release();
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
    pub(super) type Memo<A> = HashMap<u64, Piece<A>, std::hash::BuildHasherDefault<Digest>>;

    fn id<A: Literal>(t: &Seq<A>) -> u64 {
        t.as_ref().map_or(0, |c| c.id)
    }

    fn len<A: Literal>(t: &Seq<A>) -> usize {
        t.as_ref().map_or(0, |c| c.len)
    }

    /// The digest of a sequence: [`folded`] over its blocks, 0 when empty.
    fn digest<A: Literal>(t: &Seq<A>) -> u64 {
        t.as_ref().map_or(0, |c| c.digest)
    }

    fn name_digest<A: Literal>(t: &Seq<A>) -> u64 {
        t.as_ref().map_or(0, |c| c.name_digest)
    }

    /// [`R`] to the power of the number of blocks.
    fn pow<A: Literal>(t: &Seq<A>) -> u64 {
        t.as_ref().map_or(1, |c| c.pow)
    }

    /// The base of [`folded`]: odd, so that each power of it is odd too.
    const R: u64 = 0x9e37_79b9_7f4a_7c15;

    /// The digest of the sequence `left`, a block of digest `block`, then `right`, from the
    /// digests of `left` and `right` and [`R`] to the power of the length of `right`: the
    /// polynomial `e_1 R^(k-1) + e_2 R^(k-2) + ... + e_k`, wrapping, of the hashes `e_i` of the `k`
    /// blocks in order. `left` contributes its polynomial times `R^(1 + |right|)`, the block `e`
    /// times `R^|right|`, and `right` its own, so the sum is that of the whole sequence: the same
    /// for every shape of the sequence.
    ///
    /// Complexity tradeoff: the digest this replaces mixed the block's digest with the children's,
    /// also `O(1)` per cell, but a function of the shape, which the drawn priorities make a function
    /// of the draw; digests order types, so the draw reached what zedc prints. The fold is `O(1)`
    /// per cell, two multiplications and an addition, from the children's digests and powers, one
    /// more word per cell. Given up: such a polynomial in a fixed base has collisions a program
    /// could choose; a collision costs only a comparison of the two sequences by their blocks, as
    /// any collision of digests does.
    ///
    /// Under the short-addresses build the digest is kept to its low 8 bits, as `mix` keeps every
    /// digest (`address::short64`): reducing modulo `2^8` commutes with wrapping sums and products,
    /// so it is still one function of the blocks.
    fn folded(left: u64, block: u64, right: u64, right_pow: u64) -> u64 {
        let before = left.wrapping_mul(R).wrapping_add(mix(16, block));
        crate::address::short64(before.wrapping_mul(right_pow).wrapping_add(right))
    }

    /// The priorities of the cells, by the value of `taken` of the literal at the root of their
    /// block, drawn once per run (module [`crate::priority`]). The root is picked by the
    /// priorities of the literals in sets (module `set`), drawn by sites of their own.
    static PRIORITIES: [Priorities; 2] = [Priorities::new(13), Priorities::new(14)];

    /// The priority of the cell of `block`: the run's random polynomial of degree 4 at the digest
    /// of the literal at the root of the block's treap, the literal of highest priority there
    /// (module `set`), one polynomial for each value of `taken`.
    ///
    /// The bound. Each block's root is a function of the block and the sets' draw, which is
    /// independent of this one (other sites, module [`crate::priority`]), so given the sets'
    /// draw the cells' priorities are the polynomials of this draw at points fixed before it.
    /// No atom is in two
    /// blocks of a list (module comment), so the roots of two cells of one sequence are distinct
    /// literals, and distinct points unless their atoms' digests are equal: cells at distinct points take 5-wise independent uniform priorities, which bounds
    /// every cell's expected depth by `O(log m)` for `m` blocks, whatever the blocks (Seidel and
    /// Aragon 1996, Theorem 3.3 and section 6; the proof, with the cells whose points are equal
    /// counted as ties, is in module [`crate::priority`]).
    ///
    /// A literal added to a block changes this priority only when it becomes the block's root, so
    /// a block edited in place mostly keeps its cell's place, and its atoms are carried over
    /// ([`replace`]); a priority hashed from the whole block moved the cell at each edit and made
    /// its atoms again, `O(k)` for a block of `k`. How often the root changes follows the sets'
    /// draw: a literal added to a block of `k` at distinct points becomes its root with
    /// probability at most `c / (k + 1)` (the 1-max property, Seidel and Aragon 1996, section 6);
    /// no bound here rests on it.
    fn priority<A: Literal>(block: &Set<A>) -> u64 {
        PRIORITIES[usize::from(block.key.1)].of(block.key.0.digest())
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
        let prio = priority(&block);
        cell_at(left, block, right, prio)
    }

    /// [`cell`], given `prio`, the priority of `block` ([`priority`]): a cell rebuilt over other
    /// children passes its own, so a miss in the table does not evaluate it again.
    fn cell_at<A: Literal>(
        left: Seq<A>,
        block: Arc<Set<A>>,
        right: Seq<A>,
        prio: u64,
    ) -> Arc<Cell<A>> {
        debug_assert_eq!(prio, priority(&block), "a cell's priority is its block's");
        let key = (id(&left), block.id, id(&right));
        // One walk of the table finds the cell or the place for a new one; a cell found dead is
        // replaced there, and its weak handle dropped, which touches no table.
        A::table(|t| {
            let entry = t.cells.entry(key);
            if let std::collections::hash_map::Entry::Occupied(e) = &entry
                && let Some(c) = e.get().upgrade()
            {
                return c;
            }
            let c = Arc::new(Cell {
                id: NEXT.fetch_add(2, Atomic::Relaxed),
                digest: folded(digest(&left), block.digest, digest(&right), pow(&right)),
                name_digest: folded(
                    name_digest(&left),
                    block.name_digest,
                    name_digest(&right),
                    pow(&right),
                ),
                prio,
                len: len(&left) + 1 + len(&right),
                pow: pow(&left).wrapping_mul(R).wrapping_mul(pow(&right)),
                left,
                block,
                right,
                atoms: OnceLock::new(),
                index: OnceLock::new(),
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
                true => cell_at(n.left.clone(), n.block.clone(), node, n.prio),
                false => cell_at(node, n.block.clone(), n.right.clone(), n.prio),
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
                true if want.0 => l = Some(cell_at(n.left.clone(), n.block.clone(), l, n.prio)),
                false if want.1 => r = Some(cell_at(r, n.block.clone(), n.right.clone(), n.prio)),
                _ => {}
            }
        }
        (l, r)
    }

    /// The block at `k` of `t`, which has more than `k` blocks.
    fn nth<A: Literal>(t: &Seq<A>, k: usize) -> &Arc<Set<A>> {
        block_at(t.as_ref().expect("a sequence has the block asked for"), k)
    }

    /// The block at `k` of the sequence of the cell `at`, which has more than `k` blocks.
    fn block_at<A: Literal>(mut at: &Cell<A>, mut k: usize) -> &Arc<Set<A>> {
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

    /// The label of a block in an [`Index`]: labels increase along the list.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct Label(u64);

    /// An atom as a key of an [`Index`].
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct AtomKey<A>(A);

    impl<A> std::borrow::Borrow<A> for AtomKey<A> {
        fn borrow(&self) -> &A {
            &self.0
        }
    }

    /// The priorities of the labels and of the atoms in the treaps of an [`Index`], drawn once
    /// per run (module [`crate::priority`]).
    static INDEX_PRIORITIES: [Priorities; 2] = [Priorities::new(15), Priorities::new(16)];

    /// The label of the one block of a list of one literal ([`Cell::indexed`]). A block put
    /// first takes the least label less one, so the labels stay below `P` and at distinct points
    /// of the draw (module [`crate::priority`]) for the first `2^62` blocks put first along one
    /// list's edits.
    const FIRST: u64 = 1 << 62;

    impl Keyed for Label {
        fn priority(&self) -> u64 {
            INDEX_PRIORITIES[0].of(self.0)
        }
    }

    /// Atoms of one digest tie and are ordered by the atoms, as the literals of a set are (module
    /// `set`, and module [`crate::priority`] on keys at one point).
    impl<A: Literal> Keyed for AtomKey<A> {
        fn priority(&self) -> u64 {
            INDEX_PRIORITIES[1].of(self.0.digest())
        }
    }

    /// The index of a sequence's blocks (plan row KERNEL-bdd-rejoin-bytes), kept on the cell at
    /// its root: a label for each block, increasing along the sequence, and for each atom the
    /// label of its block, each a treap with sizes (module `treap`). So the place of an atom's
    /// block is one lookup in `atoms` and one in `labels`, one comparison a level each
    /// ([`Index::find`]), where the atoms of the left children ([`Cell::atoms`]) take an
    /// ordered-set lookup at each of `O(log m)` levels.
    ///
    /// Invariant: `labels` has one label per block, in the order of the blocks; every atom of a
    /// block maps to that block's label; and an atom of no block either is absent from `atoms`
    /// or maps to a label absent from `labels` and greater than every label in it (a stale
    /// entry, left by a cut, [`cut`]). The index describes the cell's own sequence, whatever
    /// edits made the cell, so a cell reached by two histories may keep either one's index; it
    /// is outside the cells' hash-consing and equality, which see only the blocks.
    ///
    /// Only a list of one literal is given an index outright, on first use ([`Cell::indexed`]),
    /// and an edit
    /// of an indexed list by [`replace`] or [`cut`] passes its index on ([`reindex`]); every
    /// other list has none and is searched by the atoms of its left children, as before.
    pub(super) struct Index<A: Literal> {
        labels: treap::Tree<Label, ()>,
        atoms: treap::Tree<AtomKey<A>, Label>,
    }

    // Complexity tradeoff (COMPLEXITY.md K67 (5)): the naive way to find an atom's block reads
    // the atoms of each left child on the path down, an ordered-set lookup of `O(log m)` at each
    // of `O(log m)` levels, and every edit carries those atoms over for each left child it
    // rebuilds, `O(log m)` new set nodes each: `O(log² m)` time and bytes per literal. Used: an
    // index on the root, two treap lookups to find (`O(log m + log k)` for `k` atoms) and, per
    // edit, `O(1)` treap updates for each atom it moves (`O(log k)` each). Given up: a list
    // made other than from one literal by `replace` and `cut` (`Bdd::assemble`, `merge`, a split
    // or a zip) has no index and is searched as before; carrying an index through those needs a
    // relabeling of one side, `O(size)`, which made another benchmark quadratic when tried
    // (plan row KERNEL-bdd-rejoin-bytes, the attempt by bundle-kernel4). A block joined to
    // another moves the atoms of all but the largest, `O(s log k)` for `s` atoms moved, where
    // the join of the sets (`set::union`, `set::insert`) already costs `O(s)` or more.
    impl<A: Literal> Index<A> {
        /// The index of the one block `block`, all its atoms under [`FIRST`].
        fn single(block: &Arc<Set<A>>) -> Index<A> {
            let mut atoms = None;
            for (a, _) in set::iter(Some(block)) {
                atoms = treap::insert(&atoms, AtomKey(a.clone()), Label(FIRST));
            }
            Index {
                labels: treap::insert(&None, Label(FIRST), ()),
                atoms,
            }
        }

        /// The place of the block of `atom` in `root`'s sequence, which this indexes, and whether
        /// the block takes it: the label of its block, then the label's place among the labels,
        /// then the block at that place. `None` when the atom is in no block: absent, or under a
        /// label absent from `labels` (the invariant of [`Index`]).
        fn find(&self, root: &Cell<A>, atom: &A) -> Option<(usize, bool)> {
            let label = treap::get(&self.atoms, atom)?;
            let k = treap::place(&self.labels, label)?;
            let taken = set::get(Some(block_at(root, k)), atom);
            debug_assert!(taken.is_some(), "an atom's label is its block's");
            Some((k, taken?))
        }
    }

    /// The index of `t` after `replace` puts `count` new blocks in place of its blocks `i..j`,
    /// whose atoms differ from theirs by `(gone, added)`, from `ix`, the index of `t`: `None` for
    /// more than one new block, which no caller passes.
    ///
    /// Proof that the invariant of [`Index`] holds after. The atoms of `gone` leave `atoms`.
    /// With no new block, the labels of blocks `i..j` leave `labels`; every caller passes every
    /// atom of those blocks in `gone` (a block emptied of its last literal, or the last block
    /// dropped by [`finish`] with its atoms listed), so no atom maps to a removed label. With
    /// one new block in place of `j - i > 0` blocks, it keeps the label of the largest of them,
    /// which lies between the labels of the blocks before `i` and after `j`, so the labels still
    /// increase; the atoms of the other blocks, less `gone`, and the atoms of `added` map to it;
    /// every caller's new block holds exactly the atoms of blocks `i..j` less `gone` plus
    /// `added` (a block with a literal removed or added, two blocks joined over an emptied one,
    /// the last literal moved into the block before, a block flipped). With one new block and
    /// `i = j`, the block is put first (`i = 0`, the only such caller,
    /// [`Bdd::or_new_literal`]) and takes the least label less one, below every label. Labels
    /// are only ever added below the least one, and a removed label's atoms all leave `atoms`, so
    /// a stale label stays greater than every label present and is never given to a block.
    ///
    /// Cost: `O(|gone| + |added| + j - i + 1)` treap operations, `O(log m + log k)` each in
    /// expectation for `m` blocks and `k` entries, plus one insertion for each atom of the
    /// blocks joined to the largest. `gone` is searched only for those atoms, and then holds at
    /// most one atom: it holds more only when no block replaces (the last block dropped).
    fn reindex<A: Literal>(
        t: &Seq<A>,
        ix: &Index<A>,
        (i, j): (usize, usize),
        count: usize,
        (gone, added): Delta<'_, A>,
    ) -> Option<Index<A>> {
        let mut atoms = ix.atoms.clone();
        for a in gone {
            atoms = treap::remove(&atoms, a);
        }
        let olds: Vec<(Label, &Arc<Set<A>>)> = (i..j)
            .map(|k| (*treap::nth(&ix.labels, k), nth(t, k)))
            .collect();
        let mut labels = ix.labels.clone();
        let kept = match count {
            0 => None,
            1 if olds.is_empty() => {
                debug_assert_eq!(i, 0, "a block is added only in front");
                let l = Label(treap::nth(&ix.labels, 0).0 - 1);
                labels = treap::insert(&labels, l, ());
                Some(l)
            }
            1 => olds.iter().max_by_key(|(_, s)| s.len()).map(|&(l, _)| l),
            // Every call of [`replace`] passes `Vec::new()` or a one-element `vec![..]`.
            _ => unreachable!("no caller replaces blocks by more than one"),
        };
        for &(l, s) in &olds {
            if Some(l) == kept {
                continue;
            }
            labels = treap::remove(&labels, &l);
            if let Some(k) = kept {
                for (a, _) in set::iter(Some(s)) {
                    if !gone.contains(a) {
                        atoms = treap::insert(&atoms, AtomKey(a.clone()), k);
                    }
                }
            }
        }
        if let Some(k) = kept {
            for a in added {
                atoms = treap::insert(&atoms, AtomKey(a.clone()), k);
            }
        }
        Some(Index { labels, atoms })
    }

    /// The first `k` blocks of the list `t`, its index passed on when it has one: the labels of
    /// the first `k` blocks, and every atom entry kept, those of the blocks cut off now stale
    /// (the invariant of [`Index`]: their labels were greater than those kept, since labels
    /// increase along the list), `O(log m)` expected.
    fn cut<A: Literal>(t: &Seq<A>, k: usize) -> Seq<A> {
        let made = prefix(t, k);
        if let (Some(root), Some(c)) = (t, &made)
            && let Some(ix) = root.indexed()
            && c.index.get().is_none()
        {
            let _ = c.index.set(Index {
                labels: treap::prefix(&ix.labels, k),
                atoms: ix.atoms.clone(),
            });
        }
        made
    }

    /// `t` with the blocks from `i` to before `j` replaced by `new`, whose atoms differ from theirs
    /// by `delta`. The cells above the place edited whose priority stays above the new blocks' are
    /// rebuilt along the path; below, the cell where the path stops is the root of the region
    /// rebuilt by `split` and `merge`, `O(log m)` blocks in expectation. Every cell rebuilt on the
    /// path, and the region's root, covers the blocks of a cell of `t` changed by `delta` alone;
    /// one placed as a left child takes its atoms from that cell's ([`carry`]). Only
    /// [`Cell::find`] reads a cell's atoms, and only a left child's, so the others (about half
    /// of the path, and always the root) make theirs on first use if they ever become a left
    /// child, which is what a cell that never had them already does. When `t` has an index, the
    /// new root is given one made from it ([`reindex`]).
    fn replace<A: Literal>(
        t: &Seq<A>,
        (i, j): (usize, usize),
        new: Vec<Arc<Set<A>>>,
        delta: Delta<'_, A>,
    ) -> Seq<A> {
        let (edit, count) = ((i, j), new.len());
        let prios: Vec<u64> = new.iter().map(|s| priority(s)).collect();
        let top = prios.iter().copied().max();
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
            (Some(n), [b]) if fits(n, prios[0]) => Some(cell_at(
                n.left.clone(),
                b.clone(),
                n.right.clone(),
                prios[0],
            )),
            _ => {
                let (before, rest) = split(&region.cloned(), i);
                let after = suffix(&rest, j - i);
                let mid = new
                    .into_iter()
                    .zip(prios)
                    .fold(None, |s, (b, p)| merge(s, Some(cell_at(None, b, None, p))));
                merge(merge(before, mid), after)
            }
        };
        let placed_left = |k: usize| k > 0 && path[k - 1].1;
        if let (Some(old), Some(made)) = (region, &node)
            && placed_left(path.len())
        {
            carry(old, made, delta);
        }
        for k in (0..path.len()).rev() {
            let (n, left) = path[k];
            let made = match left {
                true => cell_at(node, n.block.clone(), n.right.clone(), n.prio),
                false => cell_at(n.left.clone(), n.block.clone(), node, n.prio),
            };
            if placed_left(k) {
                carry(n, &made, delta);
            }
            node = Some(made);
        }
        if let (Some(root), Some(c)) = (t, &node)
            && let Some(ix) = root.indexed()
            && c.index.get().is_none()
            && let Some(made) = reindex(t, ix, edit, count, delta)
        {
            let _ = c.index.set(made);
        }
        node
    }

    /// Whether two sequences have the same blocks: by id on one thread, where a live cell is
    /// the one cell of its contents; for cells of two threads, whose ids differ, by digest and
    /// then by contents, as [`Part::lists_opposite`] compares them.
    fn same_seq<A: Literal>(x: &Seq<A>, y: &Seq<A>) -> bool {
        match (x, y) {
            (None, None) => true,
            (Some(c), Some(d)) => {
                c.id == d.id
                    || (c.digest == d.digest
                        && Bdd::List(c.clone(), true) == Bdd::List(d.clone(), true))
            }
            // Both callers are in `implies_by_blocks`: case A compares the rests of two lists of
            // equal length, so both are empty or neither is; case B passes the shorter list,
            // never empty, and the longer one's rest, of its length (checked just before).
            _ => unreachable!("same_seq compares sequences of equal length"),
        }
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
                // Made by another thread since `c` was pushed: the cells of a list are shared
                // between threads, and `OnceLock` keeps the first atoms set. On one thread this
                // does not happen. `c` was pushed with no atoms; until it is popped only cells
                // below it are made, and `c` is not below itself. Nor is a cell made twice in one
                // walk: the walk starts at a list's root (`Cell::find_by_atoms`), and a cell met
                // twice in one tree would put its blocks twice in the list, while a list in its
                // one form holds each atom in one block (module comment). Skipping saves making
                // the set again, which would give the same atoms; no test makes the race, so no
                // test reaches this.
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

        /// The place of the block that holds `atom`, and whether it takes it: by the index when
        /// the cell has one ([`Index::find`]); otherwise down from the root, to the left when the
        /// cell on the left holds it, in `O(log m)` steps for `m` blocks.
        fn find(&self, atom: &A) -> Option<(usize, bool)> {
            match self.indexed() {
                Some(ix) => ix.find(self, atom),
                None => self.find_by_atoms(atom),
            }
        }

        /// The index of the list at this cell ([`Index`]): the one it was given, or for the list
        /// of one literal one made now, `O(1)`; `None` for a list made other than from one
        /// literal by [`replace`] and [`cut`]. A literal's index is made on first use, not by
        /// [`Bdd::literal_key`], since most literals are joined into another list and never
        /// edited themselves.
        fn indexed(&self) -> Option<&Index<A>> {
            if let Some(ix) = self.index.get() {
                return Some(ix);
            }
            let one = self.left.is_none() && self.right.is_none() && self.block.len() == 1;
            one.then(|| self.index.get_or_init(|| Index::single(&self.block)))
        }

        /// [`Cell::find`] by the atoms of the left children on the path down.
        fn find_by_atoms(&self, atom: &A) -> Option<(usize, bool)> {
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
        /// The list of the one literal `key`, whose index is made on first use
        /// ([`Cell::indexed`]).
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
                return self.or_new_literal(key);
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
                    // Proof that the last block of two or more is not emptied: the list is in its
                    // one form (module comment, made so by `finish`, `Bdd::literal_key` and
                    // `Bdd::or_new_literal`; `Bdd::not` keeps the blocks), in which two or more
                    // blocks end in a block of two or more literals, so one left in it. With one
                    // block, `at == 0` is the arm above.
                    None if at + 1 == n => {
                        unreachable!("the last of two or more blocks holds two or more literals")
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
                // atoms dropped. COMPLEXITY.md K67 (4). A list with an index keeps it ([`cut`]):
                // its labels cut in `O(log m)`, the atoms of the blocks dropped left as stale
                // entries, so it never reads those atoms (K67 (5)).
                finish((cut(&seq, at), v), w)
            };
            // `rest` no longer holds the atom: the literal set false left its block, or the cut
            // dropped that block and every block after it.
            rest.or_new_literal(key)
        }

        /// [`Bdd::or_literal`] of a literal whose atom the list does not hold, without looking
        /// for it: the literal joins the first block if its value is `true`, or comes first in a
        /// block of its own.
        fn or_new_literal(&self, key: Key<A>) -> Bdd<A> {
            let (c, v) = match self {
                Bdd::Leaf(true) => return self.clone(),
                Bdd::Leaf(false) => return Bdd::literal_key(key),
                Bdd::List(c, v) => (c, *v),
            };
            let seq = Some(c.clone());
            let added = [key.0.clone()];
            let root = match v {
                true => {
                    let first = set::insert(Some(c.first()), key);
                    replace(&seq, (0, 1), vec![first], (&[], &added))
                }
                false => replace(&seq, (0, 0), vec![set::single(key)], (&[], &added)),
            };
            Bdd::List(root.expect("a list with a block added has a cell"), true)
        }

        /// `self & l`, `l` the literal `key`: `!(!self | !l)`.
        pub(super) fn and_literal(&self, (a, taken): Key<A>) -> Bdd<A> {
            self.not().or_literal((a, !taken)).not()
        }

        /// `self op other` when one of the two lists implies the other as their blocks show it
        /// ([`Bdd::implies_by_blocks`]): `f & g` is `f`, and `f | g` is `g`, when `f` implies
        /// `g`. `None` when the blocks do not show it, which says nothing about implication.
        ///
        /// The result is one of the two operands, a list in its one form, so the one form is
        /// kept: the function `f & g` has one list, and it is `f`.
        pub(super) fn absorbed(&self, other: &Bdd<A>, op: Op) -> Option<Bdd<A>> {
            let self_implies = self.implies_by_blocks(other)?;
            Some(match self_implies == (op == Op::And) {
                true => self.clone(),
                false => other.clone(),
            })
        }

        /// `Some(true)` when `self` implies `other`, `Some(false)` when `other` implies `self`,
        /// found in one of the two cases below; `None` when neither fits.
        ///
        /// Proof. A list `B_1:v_1, …, B_k:v_k, default d` takes, at a setting of the atoms, the
        /// value of the first block with a literal that holds, or `d` when none holds.
        ///
        /// Lemma: let `h` be a list, `S` a set of literals on atoms that `h` does not hold, and
        /// `S:u ⧺ h` the blocks of `h` with `S` put before them (value `u`), with `h`'s default.
        /// Then `S:u ⧺ h` is `S | h` when `u` is `true` and `!S & h` when `u` is `false`, writing
        /// `S` for the union of its literals. At a setting where a literal of `S` holds, its
        /// first block gives `u`. Where none holds, the first block is passed, and the blocks
        /// and default after it are `h`'s, read at the same setting, so it gives `h`'s value.
        /// So `h` implies `S:u ⧺ h` when `u` is `true`, and `S:u ⧺ h` implies `h` when it is
        /// `false`. The proof reads only the value at each setting, not the one form.
        ///
        /// Case B: `g` has one block more than `f`, and the blocks of `g` after its first,
        /// with their values, are `f`'s blocks and values (`f`'s first value is then the
        /// complement of `g`'s, and the two defaults are one, since both follow the last block).
        /// So `g` is `S:u ⧺ f` with `S` and `u` the first block of `g` and its value; no atom is
        /// in two blocks of `g`, so `f` does not hold the atoms of `S`, and the lemma applies.
        ///
        /// Case A: `f` and `g` have the same number of blocks and first value `u`, the same
        /// blocks after the first, and the first block `F` of `f` is a proper subset of the
        /// first block `G` of `g`. Let `S = G \ F`. `G` holds each of its atoms once, so the
        /// atoms of `S` are not in `F`, and no atom is in two blocks of `g`, so they are not in
        /// the later blocks: `f` does not hold them. At each setting, `g` gives what `S:u ⧺ f`
        /// gives: where a literal of `S` holds, `u`; where none holds, `G`'s literals that
        /// hold are `F`'s, so `g` gives `u` exactly when `F` does and otherwise reads the same
        /// later blocks and default as `f`. So `g` is `S:u ⧺ f` as a function, and the lemma
        /// applies. ∎
        ///
        /// Every other implication between lists is not found here, and the zip of such lists
        /// is kept as an expression, as before: for example `g` with a literal added to a later
        /// block of `f`, or two lists that agree only on some later blocks.
        ///
        /// Each case is first tested on the digests, in constant time, then decided exactly.
        /// A sequence's digest is `e_1 R^(k-1) + … + e_k` for the hashes `e_i = mix(16, ·)` of
        /// its `k` blocks, wrapping, kept to its low bits under the short-addresses build
        /// ([`folded`]); reducing to the low bits commutes with wrapping sums and products.
        /// In case A the two digests differ by `(e_F - e_G) R^(k-1)`, and so `R` times their
        /// difference is `(e_F - e_G) R^k`, `R^k` the cell's `pow`; in case B, `g`'s digest less
        /// `e_G R^(k-1)` is `f`'s, for `f`'s `k - 1` blocks. So equal later blocks always pass the
        /// test, and a sequence that fails it differs, and is no case here. One that passes is
        /// then compared exactly ([`same_seq`]).
        // Complexity tradeoff (COMPLEXITY.md CANON-list-absorb): the naive method keeps the meet
        // or union of two lists that are no chains as an expression, `O(1)`, and so leaves a
        // second node for a list's function (`l & (l|b)` is not `l`). An exact implication test
        // of two decision lists, over the pairs of a block of one and a block of the other,
        // costs `O(m)` or more for `m` blocks at every such zip. Used: the two cases above,
        // `O(1)` when the digests rule them out; when they pass, the blocks after the first
        // split off in `O(log m)` expected each ([`suffix`]), compared by id on one thread
        // (by contents, `O(size)`, only for cells of two threads or a collision of digests),
        // and in case A the smaller first block, of `s` literals, taken from the larger
        // (`set::difference_if_agree`): `O(s (1 + D))` expected, `D` the bound on a node's
        // depth there, proved in module `set`, the order of looking up each of the `s` literals
        // in the larger; but subtrees of the two blocks that are one node are passed at once,
        // so a block made from the other by adding a literal, on one thread, costs only the
        // paths that differ (measured, not proved: COMPLEXITY.md CANON-list-absorb; cost only,
        // the shared subtrees give the answer a full walk gives). Given up:
        // the other implications above.
        fn implies_by_blocks(&self, other: &Bdd<A>) -> Option<bool> {
            let (Bdd::List(c, v), Bdd::List(d, w)) = (self, other) else {
                // The one caller, `Bdd::absorbed`, is called only by `Part::union_as_kept` and
                // `Connect::zipped`, each after `Part::zip_at_once` gave `None` for the two
                // operands (`zipped` is entered only from `Connect::zip`, which tests it first);
                // `zip_at_once` gives `Some` whenever an operand is a leaf.
                unreachable!("both operands of `absorbed` are lists")
            };
            let short = crate::address::short64;
            if c.len == d.len {
                // Case A.
                let (f, g) = (c.first(), d.first());
                let lhs = c.digest.wrapping_sub(d.digest).wrapping_mul(R);
                let rhs = mix(16, f.digest)
                    .wrapping_sub(mix(16, g.digest))
                    .wrapping_mul(c.pow);
                if v != w || short(lhs) != short(rhs) {
                    return None;
                }
                let (small, big, self_small) = match f.len().cmp(&g.len()) {
                    std::cmp::Ordering::Less => (f, g, true),
                    std::cmp::Ordering::Greater => (g, f, false),
                    std::cmp::Ordering::Equal => return None,
                };
                let rest = |x: &Arc<Cell<A>>| suffix(&Some(x.clone()), 1);
                // `small` is in `big` exactly when no literal of it is left out of `big`: no
                // atom of it missing from `big` (the difference is empty) and none taken the
                // other way (`None`).
                let subset = || set::difference_if_agree(small, big).is_some_and(|d| d.is_none());
                // The smaller first block's list implies the larger's when the first value is
                // `true`, and is implied by it when `false`.
                return (same_seq(&rest(c), &rest(d)) && subset()).then_some(self_small == *v);
            }
            // Case B, `long` the list of one block more.
            let (long, lv, sh, sv, self_long) = match c.len.cmp(&d.len) {
                std::cmp::Ordering::Greater => (c, *v, d, *w, true),
                _ => (d, *w, c, *v, false),
            };
            let e = mix(16, long.first().digest);
            if long.len != sh.len + 1
                || lv == sv
                || short(long.digest.wrapping_sub(e.wrapping_mul(sh.pow))) != sh.digest
                || !same_seq(&suffix(&Some(long.clone()), 1), &Some(sh.clone()))
            {
                return None;
            }
            // The shorter list implies the longer when the first block's value is `true`.
            Some(lv != self_long)
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
            seen: &mut crate::digest::DigestSet<u64>,
            f: &mut impl FnMut(&'a A) -> bool,
            shared_sets: bool,
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
                if !shared_sets {
                    if !set::iter(Some(&c.block)).all(|(a, _)| f(a)) {
                        return false;
                    }
                } else {
                    // Blocks can share set subtrees even when their list cells differ. Walk
                    // each set node once as well; its id comes from the same counter as cells.
                    let mut literals = Vec::new();
                    let mut next = Some(&*c.block).filter(|s| seen.insert(s.id));
                    loop {
                        while let Some(s) = next {
                            literals.push(s);
                            next = s.left.as_deref().filter(|s| seen.insert(s.id));
                        }
                        let Some(s) = literals.pop() else { break };
                        if !f(&s.key.0) {
                            return false;
                        }
                        next = s.right.as_deref().filter(|s| seen.insert(s.id));
                    }
                }
                at = c.right.as_deref().filter(|r| seen.insert(r.id));
            }
        }

        /// Calls `f` on each atom that some path of the list to the value `to` takes, the atom
        /// holding there; at least those, and exactly those for a list in its one form. A path
        /// ends at the first block with a literal that holds, or at the default, and passes the
        /// blocks before it with none of their literals holding. So a literal `a` of a block of
        /// value `to` is taken by the path that block ends; a literal `!a` is taken by every path
        /// that passes its block, which, for a block before the last, reaches both values later.
        /// The last block's `!a` is taken too unless the block is that one literal and its value
        /// is `to`; in the one form ([`finish`]) a last block of one literal is the whole list, a
        /// literal, which is answered alone. Each cell and each set node is walked once for each
        /// value of `to` relative to its own first block, by `seen` (ids of cells, sets and
        /// expressions come from one counter), from a stack, in order: the blocks first to last,
        /// the literals of a block in order. A node passed over by `seen` was walked whole
        /// before (a node is not under itself), so the calls are those of the walk of every
        /// node, in its order, less some calls repeated; the first call on each atom comes in
        /// an order fixed by the list's contents, whatever the draw.
        /// Complexity tradeoff (PERF-xor-shape-free): the naive walk took a node, then its
        /// right, then its left side, `O(n)` for `n` nodes, but its order followed the shapes,
        /// which follow the run's draw of priorities, and the callers keep the first atom found
        /// (`Type::function_part`) or build unions in the order given (`first_components`). In
        /// order it is `O(n)` as well, at one more step on the stack for each node.
        pub(super) fn taken_toward<'a>(
            &'a self,
            to: bool,
            seen: &mut crate::digest::DigestSet<(u64, bool)>,
            f: &mut impl FnMut(&'a A),
        ) {
            /// A step of the walk; a cell or a set node with the value of its first block or of
            /// its own (`Cell`, `Set`), or a set node's own literal (`Key`).
            enum Job<'a, A: Literal> {
                Cell(&'a Cell<A>, bool),
                Set(&'a Set<A>, bool),
                Key(&'a Set<A>, bool),
            }
            let Bdd::List(root, first) = self else { return };
            if let Some((a, taken)) = self.as_literal() {
                if taken == to {
                    f(a);
                }
                return;
            }
            // Each cell with whether its first block has the value `to`; the blocks of a
            // sequence alternate in value, first to last. The steps are pushed last first.
            let mut jobs: Vec<Job<'a, A>> = vec![Job::Cell(&**root, *first == to)];
            while let Some(job) = jobs.pop() {
                match job {
                    Job::Cell(c, first) => {
                        if !seen.insert((c.id, first)) {
                            continue;
                        }
                        let left = c.left.as_deref();
                        let own = first != left.is_some_and(|l| l.len % 2 == 1);
                        jobs.extend(c.right.as_deref().map(|r| Job::Cell(r, !own)));
                        jobs.push(Job::Set(&c.block, own));
                        jobs.extend(left.map(|l| Job::Cell(l, first)));
                    }
                    Job::Set(s, own) => {
                        if !seen.insert((s.id, own)) {
                            continue;
                        }
                        jobs.extend(s.right.as_deref().map(|r| Job::Set(r, own)));
                        jobs.push(Job::Key(s, own));
                        jobs.extend(s.left.as_deref().map(|l| Job::Set(l, own)));
                    }
                    Job::Key(s, own) => {
                        let (a, taken) = &s.key;
                        if own || !*taken {
                            f(a);
                        }
                    }
                }
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
            // Complexity tradeoff (COMPLEXITY.md K67 (1)): the naive memo is kept per list, so m
            // lists sharing a tail of m blocks restrict that tail once each, O(m²). Used: the
            // memo is keyed by cell id and first value, so each cell is restricted once per
            // memo, and lists that share subtrees below their cut paths share that work. Given
            // up: memory for one memo entry per cell reached and a hash (splitmix64) per cell;
            // two lists share only the subtrees below their cut paths, not a whole common tail.
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
                        // Whether each literal of the block, in order, stays; the literals set
                        // false leave in one walk of the block (`set::retain`), since removing
                        // them one at a time cost `O(log m)` each and a split of `k` classes
                        // removes each literal once on each of its `log k` levels (COMPLEXITY.md
                        // K86).
                        let mut stays = Vec::with_capacity(set::len(Some(&c.block)));
                        let mut cut = false;
                        for k in set::iter(Some(&c.block)) {
                            match fix(&k.0) {
                                None => stays.push(true),
                                Some(x) if x == k.1 => {
                                    cut = true;
                                    break;
                                }
                                Some(_) => stays.push(false),
                            }
                        }
                        if cut {
                            memo.insert(key(c, w), (left.0, Some(wb)));
                            continue;
                        }
                        let block = if stays.iter().all(|&s| s) {
                            Some(c.block.clone())
                        } else {
                            let mut stays = stays.into_iter();
                            set::retain(&c.block, |_| {
                                stays.next().expect("one answer for each literal")
                            })
                        };
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
                        // The block kept whole keeps the cell's priority.
                        let block = block.map(|b| {
                            let p = match b.id == c.block.id {
                                true => c.prio,
                                false => priority(&b),
                            };
                            (b, p)
                        });
                        let direct = block.as_ref().is_some_and(|&(_, p)| {
                            l.as_ref()
                                .is_none_or(|l| value_at(*lw, l.len - 1) != wb && l.prio < p)
                                && r.as_ref().is_none_or(|r| *rw != wb && r.prio <= p)
                        });
                        let made = if kept {
                            ((Some(c.clone()), w), None)
                        } else if direct && let Some((b, p)) = block {
                            let first = if l.is_some() { *lw } else { wb };
                            ((Some(cell_at(l.clone(), b, r.clone(), p)), first), right.1)
                        } else {
                            let mid = (block.map(|(b, p)| cell_at(None, b, None, p)), wb);
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

    /// Whether `ix` meets the invariant of [`Index`] for the sequence of `c`: one label per
    /// block, every atom of a block under its block's label, and every other entry under a label
    /// absent from the labels and greater than all of them.
    #[cfg(test)]
    fn index_is_sound<A: Literal>(c: &Cell<A>, ix: &Index<A>) -> bool {
        let labels: Vec<Label> = treap::iter(&ix.labels).map(|(l, _)| *l).collect();
        if labels.len() != c.len {
            return false;
        }
        let mut atoms = 0;
        for (k, &l) in labels.iter().enumerate() {
            for (a, _) in set::iter(Some(block_at(c, k))) {
                atoms += 1;
                if treap::get(&ix.atoms, a) != Some(&l) {
                    return false;
                }
            }
        }
        let last = labels.last().copied();
        let (mut present, mut stale_above) = (0, true);
        for (_, l) in treap::iter(&ix.atoms) {
            if treap::get(&ix.labels, l).is_some() {
                present += 1;
            } else {
                stale_above &= last.is_none_or(|m| *l > m);
            }
        }
        present == atoms && stale_above
    }

    #[cfg(test)]
    impl<A: Literal> Bdd<A> {
        /// Whether every cell of the list that has made its atoms holds the atoms of its blocks,
        /// every cell with an index has one that meets its invariant ([`Index`]), its length and
        /// shape are those of a treap by position and priority, and its digests are the folds of
        /// its blocks in order, as a sequence of any shape has them.
        pub(super) fn cells_are_sound(&self) -> bool {
            let Bdd::List(c, _) = self else { return true };
            let mut stack = vec![&**c];
            while let Some(c) = stack.pop() {
                // The blocks in order, from a stack of the cells whose left is read.
                let (mut digest, mut name_digest, mut pow) = (0, 0, 1u64);
                let (mut path, mut at) = (Vec::new(), Some(c));
                while at.is_some() || !path.is_empty() {
                    while let Some(d) = at {
                        path.push(d);
                        at = d.left.as_deref();
                    }
                    let d = path.pop().expect("a cell");
                    digest = folded(digest, d.block.digest, 0, 1);
                    name_digest = folded(name_digest, d.block.name_digest, 0, 1);
                    pow = pow.wrapping_mul(R);
                    at = d.right.as_deref();
                }
                if (digest, name_digest, pow) != (c.digest, c.name_digest, c.pow) {
                    return false;
                }
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
                if let Some(ix) = c.index.get()
                    && !index_is_sound(c, ix)
                {
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

    #[cfg(test)]
    mod tests;
}

#[cfg(test)]
mod bench;
#[cfg(test)]
mod tests;
