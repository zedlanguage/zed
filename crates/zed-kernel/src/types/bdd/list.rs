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
//! A list is kept as cells, each a block (a set of literals, module `set`) and the cell of the
//! next block, shared through a table of the thread, so that one list is one cell, and with
//! the value of its first block; the values of the others alternate. The complement flips that
//! value. A chain of literals joined to a list ([`Bdd::or_literal`]) adds each literal to the
//! first block, or puts a block of it first, in `O(log n)`, once the list has had the atom
//! removed: a literal on an atom the list holds is first set false there, which removes it from
//! its block or cuts the list at its block, and rebuilds the blocks before.

use std::sync::atomic::Ordering as Atomic;
use std::sync::{Arc, OnceLock, Weak};

use super::set::{self, Key, NEXT, Set, Tree};
use super::{Bdd, Literal, Owned, Part, mix};

/// A block of a list and the cell of the next block: a list, with the value of its first block
/// beside it ([`Bdd::List`]).
pub(in crate::types) struct Cell<A: Literal> {
    /// The cell's id, unique among the nodes of the process, and the next id, kept for it:
    /// the list of first value `v` has the id `id + v`.
    pub(super) id: u64,
    pub(super) digest: u64,
    pub(super) block: Arc<Set<A>>,
    pub(super) next: Option<Arc<Cell<A>>>,
    /// The atoms of this block and the blocks after, made on first use.
    atoms: OnceLock<imbl::OrdSet<A>>,
    /// The first node of the list of each first value, as [`Bdd::branch`] shows it: its `hi`
    /// and `lo`, made on first use.
    view: [OnceLock<(Bdd<A>, Bdd<A>)>; 2],
}

/// The live cells of a thread, by the ids of their block and next cell, each held weakly: a cell
/// leaves the table when it is dropped (step TABLE-life).
pub(in crate::types) type CellTable<A> = std::collections::BTreeMap<(u64, u64), Weak<Cell<A>>>;

/// A cell leaves its thread's table, and its block, next cell and views are freed in a loop
/// (module `deep`).
impl<A: Literal> Drop for Cell<A> {
    fn drop(&mut self) {
        let key = (self.block.id, self.next.as_ref().map_or(0, |c| c.id));
        A::untable(|t| {
            // Another cell of the key may have taken the entry since, or none was made here.
            if t.cells
                .get(&key)
                .is_some_and(|w| std::ptr::eq(w.as_ptr(), self))
            {
                t.cells.remove(&key);
            }
        });
        if let Some(n) = self.next.take() {
            A::free(Owned::Cell(n));
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

/// A block to put before a list: its value, its literals, and, when known, the atoms of it and
/// of the blocks after it.
type Block<A> = (bool, Tree<A>, Option<imbl::OrdSet<A>>);

/// A block of `assemble`: its value, its literals, none empty, and its atoms as in [`Block`].
type Built<A> = (bool, Arc<Set<A>>, Option<imbl::OrdSet<A>>);

/// The cell of `block` before `next`, the one in the table if there is one.
fn cell<A: Literal>(block: Arc<Set<A>>, next: Option<Arc<Cell<A>>>) -> Arc<Cell<A>> {
    let key = (block.id, next.as_ref().map_or(0, |c| c.id));
    if let Some(c) = A::table(|t| t.cells.get(&key).and_then(Weak::upgrade)) {
        return c;
    }
    let digest = mix(
        mix(16, block.digest),
        next.as_ref().map_or(mix(17, 0), |c| c.digest),
    );
    let c = Arc::new(Cell {
        id: NEXT.fetch_add(2, Atomic::Relaxed),
        digest,
        block,
        next,
        atoms: OnceLock::new(),
        view: [OnceLock::new(), OnceLock::new()],
    });
    A::table(|t| t.cells.insert(key, Arc::downgrade(&c)));
    c
}

impl<A: Literal> Cell<A> {
    /// The atoms of this block and the blocks after it, made once for each cell, from those of
    /// the first cell below that has them.
    pub(super) fn atoms(&self) -> &imbl::OrdSet<A> {
        if let Some(s) = self.atoms.get() {
            return s;
        }
        let mut todo = vec![self];
        let mut below = self.next.as_deref();
        let mut atoms = loop {
            match below {
                None => break imbl::OrdSet::new(),
                Some(c) => match c.atoms.get() {
                    Some(s) => break s.clone(),
                    None => {
                        todo.push(c);
                        below = c.next.as_deref();
                    }
                },
            }
        };
        for c in todo.into_iter().rev() {
            for (a, _) in set::iter(Some(&c.block)) {
                atoms.insert(a.clone());
            }
            let _ = c.atoms.set(atoms.clone());
        }
        self.atoms.get().expect("the atoms were just made")
    }
}

impl<A: Literal> Bdd<A> {
    /// The list of the one literal `key`.
    pub(super) fn literal_key(key: Key<A>) -> Bdd<A> {
        Bdd::List(cell(set::single(key), None), true)
    }

    /// The cells with the value of each block, first to last.
    pub(super) fn cells(&self) -> impl Iterator<Item = (bool, &Cell<A>)> {
        let first = match self {
            Bdd::Leaf(_) => None,
            Bdd::List(c, v) => Some((*v, &**c)),
        };
        std::iter::successors(first, |(v, c)| c.next.as_deref().map(|n| (!*v, n)))
    }

    /// The list of `prefix` before `rest`, a cell and the value of its block, or no cell and the
    /// default, in its one form (module comment): empty blocks dropped, neighbors of one value
    /// joined, and the last block moved into the one before when that leaves the same function
    /// in the one form.
    pub(super) fn assemble(
        prefix: Vec<Block<A>>,
        (mut rest, mut value): (Option<Arc<Cell<A>>>, bool),
    ) -> Bdd<A> {
        let mut blocks: Vec<Built<A>> = Vec::new();
        for (v, s, atoms) in prefix {
            let Some(s) = s else { continue };
            match blocks.last_mut() {
                Some((w, t, _)) if *w == v => *t = set::union(t, &s),
                _ => blocks.push((v, s, atoms)),
            }
        }
        match (blocks.last_mut(), &rest) {
            (Some((v, s, _)), Some(c)) if *v == value => {
                *s = set::union(s, &c.block);
                (rest, value) = (c.next.clone(), !value);
            }
            (Some((v, ..)), None) if *v == value => {
                blocks.pop();
                // The blocks kept have lost atoms of the block dropped.
                for b in &mut blocks {
                    b.2 = None;
                }
            }
            _ => {}
        }
        if rest.is_none()
            && let [.., (_, before, _), (u, last, _)] = &mut blocks[..]
            && let Some(m) = set::single_key(last)
        {
            // `… before:!u, {m}:u, default !u` is `… (before ∪ {!m}):!u, default u`.
            let flipped = (m.0.clone(), !m.1);
            *before = set::insert(Some(&*before), flipped);
            value = *u;
            blocks.pop();
        }
        if rest.is_none()
            && let [(v, only, _)] = &mut blocks[..]
            && !*v
            && let Some(m) = set::single_key(only)
        {
            // `{m}:false, default true` is `{!m}:true, default false`.
            let flipped = (m.0.clone(), !m.1);
            *only = set::single(flipped);
            (*v, value) = (true, false);
        }
        let Some(&(first, ..)) = blocks.first() else {
            return match rest {
                Some(c) => Bdd::List(c, value),
                None => Bdd::Leaf(value),
            };
        };
        for (_, s, atoms) in blocks.into_iter().rev() {
            let c = cell(s, rest.take());
            if let Some(atoms) = atoms {
                let _ = c.atoms.set(atoms);
            }
            rest = Some(c);
        }
        Bdd::List(
            rest.expect("a list of one or more blocks has a cell"),
            first,
        )
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
        if !c.atoms().contains(&key.0) {
            let atoms = Some(c.atoms().update(key.0.clone()));
            return if v {
                let first = set::insert(Some(&c.block), key);
                Bdd::assemble(vec![(true, Some(first), atoms)], (c.next.clone(), false))
            } else {
                let first = set::single(key);
                Bdd::assemble(vec![(true, Some(first), atoms)], (Some(c.clone()), false))
            };
        }
        if v && set::get(Some(&c.block), &key.0) == Some(key.1) {
            return self.clone();
        }
        // The blocks before the atom's, and the block of the atom and its value.
        let mut before: Vec<(bool, &Cell<A>)> = Vec::new();
        let mut cells = self.cells();
        let (w, at, taken) = loop {
            let (w, at) = cells
                .next()
                .expect("an atom of a list is in one of its blocks");
            match set::get(Some(&at.block), &key.0) {
                Some(taken) => break (w, at, taken),
                None => before.push((w, at)),
            }
        };
        let rest = if taken == key.1 {
            // The literal set false leaves its block; each block before loses the atom.
            let lose = |c: &Cell<A>| Some(c.atoms().without(&key.0));
            let mut prefix: Vec<Block<A>> = (before.iter())
                .map(|(w, c)| (*w, Some(c.block.clone()), lose(c)))
                .collect();
            prefix.push((w, set::remove(&at.block, &key), lose(at)));
            Bdd::assemble(prefix, (at.next.clone(), !w))
        } else {
            // The opposite literal holds, so the list ends at its block.
            let prefix = (before.iter())
                .map(|(w, c)| (*w, Some(c.block.clone()), None))
                .collect();
            Bdd::assemble(prefix, (None, w))
        };
        rest.or_literal(key)
    }

    /// `self & l`, `l` the literal `key`: `!(!self | !l)`.
    pub(super) fn and_literal(&self, (a, taken): Key<A>) -> Bdd<A> {
        self.not().or_literal((a, !taken)).not()
    }

    /// The value when no literal holds.
    pub(super) fn default(&self) -> bool {
        match self {
            Bdd::Leaf(v) => *v,
            Bdd::List(..) => {
                let (v, _) = self.cells().last().expect("a list has a cell");
                !v
            }
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
        let (a, taken) = set::min(&c.block);
        let (hi, lo) = c.view[usize::from(*v)].get_or_init(|| {
            let without = set::remove(&c.block, &(a.clone(), *taken));
            let rest = Bdd::assemble(vec![(*v, without, None)], (c.next.clone(), !*v));
            match taken {
                true => (Bdd::Leaf(*v), rest),
                false => (rest, Bdd::Leaf(*v)),
            }
        });
        Some((a, hi, lo))
    }
}
