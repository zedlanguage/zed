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
use super::{Bdd, Literal, Owned, Part, mix};

/// A node of a sequence of blocks: a block and the sequences of the blocks before and after
/// it. A cell that is the root of a list's sequence is the list, with the value of its first
/// block beside it ([`Bdd::List`]).
pub(in crate::types) struct Cell<A: Literal> {
    /// The cell's id, unique among the nodes of the process, and the next id, kept for it:
    /// the list of first value `v` has the id `id + v`.
    pub(super) id: u64,
    /// A hash of the blocks in order, equal for equal sequences.
    pub(super) digest: u64,
    prio: u64,
    /// The number of blocks.
    pub(super) len: usize,
    pub(super) left: Seq<A>,
    pub(super) block: Arc<Set<A>>,
    pub(super) right: Seq<A>,
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
pub(in crate::types) type CellTable<A> = std::collections::BTreeMap<(u64, u64, u64), Weak<Cell<A>>>;

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

/// The hasher of [`Memo`]'s keys, of the thread's tables of live rows and morphism types, and
/// of the pairs a comparison of values has read (`value::Read`): splitmix64's finalizer on each
/// `u64` in turn. SipHash took an eighth of the restriction of a list of three blocks.
#[derive(Default)]
pub(crate) struct KeyHasher(u64);

impl std::hash::Hasher for KeyHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(u64::from(b));
        }
    }

    fn write_u64(&mut self, x: u64) {
        let mut z = (self.0.rotate_left(29) ^ x).wrapping_add(0x9e37_79b9_7f4a_7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        self.0 = z ^ (z >> 31);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

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
            std::cmp::Ordering::Less => at = at.left.as_ref().expect("the block is on the left"),
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
        n.left.as_ref().is_none_or(|l| l.prio < p) && n.right.as_ref().is_none_or(|r| r.prio <= p)
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
                None if at == 0 => finish((replace(&seq, (0, 1), Vec::new(), delta), !v), default),
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
    pub(super) fn restrict(&self, fix: &impl Fn(&A) -> Option<bool>, memo: &mut Memo<A>) -> Bdd<A> {
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
