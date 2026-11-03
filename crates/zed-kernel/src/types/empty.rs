//! Emptiness and subtyping (step L1.23, DESIGN.md sec:type_language): `a <: b` iff `a & !b`
//! is empty, decided by a memoized coinductive check.
//!
//! A type is empty when every part is. The scalar and struct parts are exact, so their
//! emptiness is read off. The tuple part of each length, a Boolean combination of tuple types
//! (module `bdd`), is decided on a box, one type per component, starting from the whole
//! product: each tuple type is known to hold the box, known to miss it, or open on it; the
//! part is evaluated in three-valued logic on what is known; a tuple type in every value of
//! the part narrows the box to it, and one in no value takes itself out of the one component
//! where it does not hold the box. What is known is kept in a table of cells: for each
//! component, one cell for each distinct type the tuple types take there, tested once for all
//! the tuple types that share it, and closed when it holds or misses the box in that component.
//! A cell that misses or holds a component still does when the box shrinks, so only the
//! components changed since they were last tested are tested again, against their open cells,
//! all tests of missing before any test of holding. When narrowing stops, a component whose pieces cut by the
//! open tuple types are pairwise equal or disjoint is split into those pieces, and each piece
//! decided; otherwise each piece on which narrowing alone proves the part empty is taken out
//! of the box; otherwise, once on each branch, when the part holds nothing outside the open
//! tuple types, the box is split into its meet with each of them. A box none of these steps
//! settles counts as inhabited. The morphism part is decided the same way, by the variance
//! law: contravariant in the guarantee, covariant in the permission and the value type.
//!
//! So `is_empty` is sound, never empty for an inhabited type, and its time is polynomial in
//! the types written; it is not complete, since emptiness of Boolean combinations of tuple
//! types is coNP-hard. A part that only a split of the box in more than one component at once
//! proves empty counts as inhabited: a subtyping check then fails, and the error names the
//! types, so the program states the case split itself (DESIGN.md L1.23).
//!
//! The check is coinductive: a type met again while its own emptiness is being decided is
//! assumed empty. Values are finite, so a type whose every value would contain a smaller value
//! of the same type is empty, which is the answer the assumption gives; contractive, regular
//! and monotone definitions (module `rec`) make the set of types met finite. A result, empty
//! or inhabited, that rests on an assumption later found false is dropped, and only such a
//! result, so no result is decided again unless an assumption it read changed: a tuple type
//! wrongly assumed disjoint from the box leaves a clause, so a wrong assumption can make a
//! type count as inhabited too. Results are kept for the thread, until
//! `Type::forget_emptiness`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::bdd::Part;
use super::{Lits, Morphism, Parts, Row, Type};
use crate::value::Value;

thread_local! {
    static MEMO: RefCell<BTreeMap<Type, bool>> = const { RefCell::new(BTreeMap::new()) };
}

impl Type {
    /// Drops the kept emptiness results. A unit's checker calls it first: a type equal to a
    /// kept one but built apart from it is compared with it in full, so a result kept from
    /// another unit costs the size of the type at each lookup.
    pub fn forget_emptiness() {
        MEMO.with(|m| m.borrow_mut().clear());
    }

    /// Whether no value is in `self`.
    pub fn is_empty(&self) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(self).copied()) {
            return b;
        }
        let mut s = Search::default();
        let b = s.empty(self);
        MEMO.with(|m| m.borrow_mut().extend(s.done));
        b
    }

    /// Whether every value of `self` is in `other`: `self <: other`.
    pub fn subtype(&self, other: &Type) -> bool {
        (self - other).is_empty()
    }

    /// Whether `self` and `other` denote one set of values.
    pub fn equiv(&self, other: &Type) -> bool {
        self.subtype(other) && other.subtype(self)
    }
}

/// One query's state: the types being decided, assumed empty, each with its depth among them;
/// those decided; the types decided on assumptions still being made, in the order they were
/// decided, each with the depths of those assumptions; and the depths of the assumptions the
/// current decision has used.
#[derive(Default)]
struct Search {
    busy: BTreeMap<Type, usize>,
    done: BTreeMap<Type, bool>,
    pending: Vec<Type>,
    rests: BTreeMap<Type, BTreeSet<usize>>,
    reads: BTreeSet<usize>,
    reps: BTreeMap<Type, Option<Rep>>,
    members: BTreeMap<(Type, Type), bool>,
}

/// One distinct type among the components a column's tuple types have, and those tuple types.
/// Whether a tuple type misses or holds a component of the box depends only on its type there,
/// so the cell is tested once for all of them, and all are open on the component or none.
struct Cell {
    ty: Type,
    rows: Vec<usize>,
    open: bool,
}

/// A box of tuples, one type per component, and where each tuple type of a part stands on it
/// component by component: missing it, holding it, or open on it. A tuple type that misses a
/// component of the box, or holds it, still does when the box shrinks, so a component that
/// changed is tested again only against the cells open on it that have a tuple type still in
/// the part, and only when they are next read. Each change is logged, so a piece of the box is
/// tried and the box restored after.
struct Region {
    r: Vec<Type>,
    atoms: Vec<Row>,
    index: BTreeMap<Row, usize>,
    /// For each component, the distinct types the tuple types have there.
    cells: Vec<Vec<Cell>>,
    /// The cell of tuple type `k` in component `j`, at `k * r.len() + j`.
    cell_of: Vec<usize>,
    /// For each tuple type, how many components it misses.
    missed: Vec<usize>,
    /// For each tuple type, how many components it does not hold, and the sum of their
    /// positions, which is the position when there is one.
    loose: Vec<(usize, usize)>,
    /// For each component, how many tuple types are open on it.
    opens: Vec<usize>,
    /// For each component, whether it changed since it was last tested.
    changed: Vec<bool>,
    log: Vec<Change>,
}

enum Change {
    /// A component of the box, its type before, and whether it had changed before.
    Component(usize, Type, bool),
    /// A component tested again.
    Tested(usize),
    /// A cell of a component no longer open on it, and whether it misses it.
    Closed(usize, usize, bool),
}

impl Region {
    /// Undoes the changes logged after the first `mark`.
    fn restore(&mut self, mark: usize) {
        while self.log.len() > mark {
            match self.log.pop().expect("a change is logged") {
                Change::Component(j, t, changed) => {
                    self.r[j] = t;
                    self.changed[j] = changed;
                }
                Change::Tested(j) => self.changed[j] = true,
                Change::Closed(j, c, missed) => {
                    let cell = &mut self.cells[j][c];
                    cell.open = true;
                    self.opens[j] += cell.rows.len();
                    for &k in &cell.rows {
                        if missed {
                            self.missed[k] -= 1;
                        } else {
                            self.loose[k].0 += 1;
                            self.loose[k].1 += j;
                        }
                    }
                }
            }
        }
    }

    /// Sets component `j` of the box to `t`, which is within it.
    fn shrink(&mut self, j: usize, t: Type) {
        let old = std::mem::replace(&mut self.r[j], t);
        self.log.push(Change::Component(j, old, self.changed[j]));
        self.changed[j] = true;
    }

    /// The cell of tuple type `k` in component `j`.
    fn cell(&self, k: usize, j: usize) -> usize {
        self.cell_of[k * self.r.len() + j]
    }

    /// Whether tuple type `k` is open on component `j`.
    fn is_open(&self, k: usize, j: usize) -> bool {
        self.cells[j][self.cell(k, j)].open
    }

    /// Closes cell `c` of component `j`, open on it, for each of its tuple types: it misses the
    /// component when `missed`, and holds it otherwise.
    fn close(&mut self, j: usize, c: usize, missed: bool) {
        let cell = &mut self.cells[j][c];
        cell.open = false;
        self.opens[j] -= cell.rows.len();
        for &k in &cell.rows {
            if missed {
                self.missed[k] += 1;
            } else {
                self.loose[k].0 -= 1;
                self.loose[k].1 -= j;
            }
        }
        self.log.push(Change::Closed(j, c, missed));
    }

    /// The open cells of component `j` that have one of the tuple types `ks`, in order.
    fn open_cells(&self, j: usize, ks: &[usize]) -> BTreeSet<usize> {
        ks.iter()
            .map(|&k| self.cell(k, j))
            .filter(|&c| self.cells[j][c].open)
            .collect()
    }

    /// Where the tuple type `a` stands on the box, as last tested: `Some(false)` if it misses it, `Some(true)`
    /// if it holds it, `None` if it is open on it.
    fn stand(&self, a: &Row) -> Option<bool> {
        let k = self.index[a];
        if self.missed[k] > 0 {
            Some(false)
        } else if self.loose[k].0 == 0 {
            Some(true)
        } else {
            None
        }
    }
}

/// A value known to be in a type, held as the types of its parts, each with a representative
/// of its own.
#[derive(Clone)]
enum Rep {
    Value(Value),
    Tuple(Row),
    /// An atom of this name, whose payload is the representative tuple of this type.
    Atom(std::sync::Arc<str>, Type),
}

impl Search {
    fn empty(&mut self, t: &Type) -> bool {
        // A scalar in the type is a value of it, read off before the type is looked up, so a
        // meet or difference of literal sets costs no comparison with the types decided.
        let p = t.p();
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        if p.bools != 0 || lits.iter().any(|l| l.cofinite || !l.values.is_empty()) {
            return false;
        }
        if let Some(b) = MEMO.with(|m| m.borrow().get(t).copied()) {
            return b;
        }
        if let Some(b) = self.done.get(t) {
            if let Some(r) = self.rests.get(t) {
                self.reads.extend(r);
            }
            return *b;
        }
        if let Some(d) = self.busy.get(t) {
            self.reads.insert(*d);
            return true;
        }
        let depth = self.busy.len();
        self.busy.insert(t.clone(), depth);
        let mark = self.pending.len();
        let outer = std::mem::take(&mut self.reads);
        let b = self.parts(t.p());
        let mut rests = std::mem::replace(&mut self.reads, outer);
        rests.remove(&depth);
        self.busy.remove(t);
        // Only results decided since `t` was assumed empty can rest on that. A wrong
        // assumption can make a result wrong either way: an assumed disjointness drops a tuple
        // type from a clause, which can leave the clause inhabited. So when `t` is inhabited,
        // each result that rests on it is dropped; when it is empty, each rests instead on
        // what `t` rests on, and is confirmed when that is nothing.
        let since: Vec<Type> = self.pending.drain(mark..).collect();
        for e in since {
            let r = self
                .rests
                .get_mut(&e)
                .expect("a pending result has its assumptions");
            if r.remove(&depth) {
                if !b {
                    self.done.remove(&e);
                    self.rests.remove(&e);
                    continue;
                }
                r.extend(&rests);
            }
            if r.is_empty() {
                self.rests.remove(&e);
            } else {
                self.pending.push(e);
            }
        }
        if !rests.is_empty() {
            self.reads.extend(&rests);
            self.pending.push(t.clone());
            self.rests.insert(t.clone(), rests);
        }
        self.done.insert(t.clone(), b);
        b
    }

    fn parts(&mut self, p: &Parts) -> bool {
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        p.bools == 0
            && lits.iter().all(|l| !l.cofinite && l.values.is_empty())
            && !p.atoms.cofinite
            && p.atoms
                .names
                .values()
                .all(|a| !a.bare && self.empty(&a.payload))
            && !p.structs
            && !p.tuples.rest
            && p.tuples.lens.iter().all(|(len, b)| {
                let mut g = self.region(vec![Type::top(); *len], b);
                self.tuples(&mut g, b.clone(), true)
            })
            && self.morphisms(
                Morphism {
                    guarantee: Type::empty(),
                    permission: Type::top(),
                    value: Type::top(),
                },
                p.morphisms.clone(),
                true,
            )
    }

    /// The region of the part `f` on the box `r`, each distinct type of each component tested
    /// once.
    fn region(&mut self, r: Vec<Type>, f: &Part<Row>) -> Region {
        let atoms = f.distinct_atoms();
        let n = r.len();
        let mut g = Region {
            cells: (0..n).map(|_| Vec::new()).collect(),
            cell_of: vec![0; atoms.len() * n],
            opens: vec![0; n],
            changed: vec![false; n],
            missed: vec![0; atoms.len()],
            loose: vec![(0, 0); atoms.len()],
            index: BTreeMap::new(),
            atoms: Vec::new(),
            log: Vec::new(),
            r,
        };
        for j in 0..n {
            let mut found: BTreeMap<&Type, usize> = BTreeMap::new();
            for (k, a) in atoms.iter().enumerate() {
                let cells = &mut g.cells[j];
                let c = *found.entry(&a[j]).or_insert_with(|| {
                    cells.push(Cell {
                        ty: a[j].clone(),
                        rows: Vec::new(),
                        open: false,
                    });
                    cells.len() - 1
                });
                cells[c].rows.push(k);
                g.cell_of[k * n + j] = c;
            }
            for c in 0..g.cells[j].len() {
                let cell = &mut g.cells[j][c];
                let missed = self.empty(&(&g.r[j] & &cell.ty));
                if !missed && self.empty(&(&g.r[j] - &cell.ty)) {
                    continue;
                }
                cell.open = !missed;
                if cell.open {
                    g.opens[j] += cell.rows.len();
                }
                for &k in &cell.rows {
                    g.missed[k] += usize::from(missed);
                    g.loose[k].0 += 1;
                    g.loose[k].1 += j;
                }
            }
        }
        for (k, a) in atoms.iter().enumerate() {
            g.index.insert(a.clone(), k);
        }
        g.atoms = atoms;
        g
    }

    /// Tests each changed component of the box against its open cells that have a tuple type
    /// not yet known to miss the box, and closes those it settles. A tuple type that misses a
    /// component is out of the part, so whether it holds the others is not tested: every
    /// changed component is tested for cells that miss it before any is tested for cells that
    /// hold it, and a cell only such tuple types have is not tested. Tuple types the part no
    /// longer has are not looked up: that costs the size of the part at each call, more than
    /// the tests it saves.
    fn retest(&mut self, g: &mut Region) {
        let changed: Vec<usize> = (0..g.r.len()).filter(|&j| g.changed[j]).collect();
        if changed.is_empty() {
            return;
        }
        for &j in &changed {
            g.changed[j] = false;
            g.log.push(Change::Tested(j));
        }
        for missed in [true, false] {
            for &j in &changed {
                for c in 0..g.cells[j].len() {
                    let cell = &g.cells[j][c];
                    if !cell.open || !cell.rows.iter().any(|&k| g.missed[k] == 0) {
                        continue;
                    }
                    let settled = if missed {
                        self.empty(&(&g.r[j] & &cell.ty))
                    } else {
                        self.empty(&(&g.r[j] - &cell.ty))
                    };
                    if settled {
                        g.close(j, c, missed);
                    }
                }
            }
        }
    }

    /// Narrows the box and the part `f` to what `f` forces on it: a tuple type in every value
    /// of `f` meets the box, and a tuple type in none is taken out of the box when it holds the
    /// box in every component but one. True when `f` is proved empty on the box.
    fn narrow_tuples(&mut self, g: &mut Region, f: &mut Part<Row>) -> bool {
        loop {
            if g.r.iter().any(|t| self.empty(t)) {
                return true;
            }
            self.retest(g);
            *f = f.restrict(&|a| g.stand(a)).settle();
            if let Some(b) = f.is_leaf() {
                return !b;
            }
            let (taken, refused) = f.forced();
            // The components changed in this pass.
            let mut shrunk = BTreeSet::new();
            // A component narrowed to a tuple type's own holds it, and one that takes a tuple
            // type out misses it, so its cell there is closed without a test.
            for a in &taken {
                let k = g.index[a];
                for j in 0..g.r.len() {
                    if g.is_open(k, j) {
                        g.shrink(j, &g.r[j] & &a[j]);
                        g.close(j, g.cell(k, j), false);
                        shrunk.insert(j);
                    }
                }
            }
            // The changed components are tested again cell by cell, so where a refused tuple
            // type stands is read off the table, not tested for each tuple type.
            if !shrunk.is_empty() {
                self.retest(g);
            }
            for a in &refused {
                let k = g.index[a];
                let (loose, at) = g.loose[k];
                if g.missed[k] == 0 && loose == 1 {
                    g.shrink(at, &g.r[at] - &a[at]);
                    if g.is_open(k, at) {
                        g.close(at, g.cell(k, at), true);
                    }
                    shrunk.insert(at);
                }
            }
            if shrunk.is_empty() {
                return false;
            }
        }
    }

    /// Whether no tuple in the box is in `f`: `f` is narrowed by what it forces; then a
    /// component on which every open tuple type is open, and whose pieces cut by them are
    /// pairwise equal or disjoint, is split into them; else each such piece on which narrowing
    /// alone proves `f` empty is taken out; else, once on each branch, when `f` holds nothing
    /// outside the open tuple types, each of them is decided on its own. What is left counts as
    /// inhabited. A split into disjoint pieces sends each open tuple type to one piece, and a
    /// component split is never split again below, so the nodes are polynomial in the tuple
    /// types. The components tried for a split are those on which the open tuple type open on
    /// fewest is open, so a box most of whose components the tuple types hold is not searched.
    /// Each piece is tried on the box and the box restored after.
    fn tuples(&mut self, g: &mut Region, mut f: Part<Row>, may_cover: bool) -> bool {
        loop {
            if self.narrow_tuples(g, &mut f) {
                return true;
            }
            if f.is_leaf().is_some() {
                return false;
            }
            let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
            let fewest = *open
                .iter()
                .min_by_key(|&&k| g.loose[k].0)
                .expect("an open part has a tuple type");
            for j in 0..g.r.len() {
                if !g.is_open(fewest, j)
                    || g.opens[j] < open.len()
                    || open.iter().any(|&k| !g.is_open(k, j))
                {
                    continue;
                }
                let mut cells = BTreeSet::new();
                let mut union = Type::empty();
                let ok = g.open_cells(j, &open).into_iter().all(|c| {
                    let c = &g.cells[j][c].ty & &g.r[j];
                    if cells.contains(&c) {
                        return true;
                    }
                    if !self.empty(&(&c & &union)) {
                        return false;
                    }
                    union = &union | &c;
                    cells.insert(c);
                    true
                });
                if !ok {
                    continue;
                }
                let rest = &g.r[j] - &union;
                if !self.empty(&rest) {
                    cells.insert(rest);
                }
                return cells.into_iter().all(|c| {
                    let mark = g.log.len();
                    g.shrink(j, c);
                    let b = self.tuples(g, f.clone(), may_cover);
                    g.restore(mark);
                    b
                });
            }
            let mut narrowed = false;
            for j in 0..g.r.len() {
                let mut tried = BTreeSet::new();
                // A cell closed on the component misses or holds it, so its pieces are the
                // component and nothing, and narrow nothing.
                for cell in g.open_cells(j, &open) {
                    let a = &g.cells[j][cell].ty;
                    for c in [a & &g.r[j], &g.r[j] - a] {
                        if tried.contains(&c) || self.empty(&c) || self.empty(&(&g.r[j] - &c)) {
                            continue;
                        }
                        tried.insert(c.clone());
                        let mark = g.log.len();
                        g.shrink(j, c.clone());
                        let hit = self.narrow_tuples(g, &mut f.clone());
                        g.restore(mark);
                        if hit {
                            let t = &g.r[j] - &c;
                            g.shrink(j, t);
                            narrowed = true;
                        }
                    }
                }
            }
            if narrowed {
                continue;
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                return open.iter().all(|&k| {
                    let mark = g.log.len();
                    for j in 0..g.r.len() {
                        if g.is_open(k, j) {
                            let t = &g.r[j] & &g.atoms[k][j];
                            g.shrink(j, t);
                            g.close(j, g.cell(k, j), false);
                        }
                    }
                    let b = self.tuples(g, f.clone(), false);
                    g.restore(mark);
                    b
                });
            }
            return false;
        }
    }

    /// Whether `m` admits no morphism: a key is promised and not permitted, or promised and no
    /// value can be its. A key is promised only when a value is shown in the type: a type not
    /// proved empty may still be empty, and then the empty morphism is admitted.
    fn no_morphism(&mut self, m: &Morphism) -> bool {
        self.rep(&(&m.guarantee - &m.permission)).is_some()
            || (self.rep(&m.guarantee).is_some() && self.empty(&m.value))
    }

    /// A value in `t`, if one is found: a scalar or bare atom of it, or a tuple or atom payload
    /// whose components have representatives and which `t` holds. The tuples tried at each
    /// length are two: the box the tuple types narrow the part to, and its meet with the first
    /// tuple type left open; each is tested against every tuple type of `t`, so a poor choice
    /// costs precision, never soundness. A type met again while its own is sought has none on
    /// that path, since a value is finite; none found means only that, never that `t` is
    /// empty. Each type is tried once and each test of a representative against a type is
    /// made once, so a value nested in shared types is never copied out.
    fn rep(&mut self, t: &Type) -> Option<Rep> {
        if let Some(r) = self.reps.get(t) {
            return r.clone();
        }
        self.reps.insert(t.clone(), None);
        let r = self.find_rep(t);
        self.reps.insert(t.clone(), r.clone());
        r
    }

    fn find_rep(&mut self, t: &Type) -> Option<Rep> {
        let p = t.p();
        if p.bools != 0 {
            return Some(Rep::Value(Value::Bool(p.bools & 1 == 0)));
        }
        type Fresh = Option<fn(i64) -> Value>;
        let fresh: [(&Lits, Fresh); 4] = [
            (&p.ints, Some(Value::Int)),
            (&p.strings, Some(|i| Value::str(&i.to_string()))),
            (&p.rats, None),
            (&p.floats, None),
        ];
        for (l, make) in fresh {
            let v = match (l.cofinite, make) {
                (false, _) => l.values.iter().next().cloned(),
                (true, Some(make)) => (0..).map(make).find(|v| !l.values.contains(v)),
                (true, None) => None,
            };
            if let Some(v) = v {
                return Some(Rep::Value(v));
            }
        }
        if p.atoms.cofinite {
            let name = (0..)
                .map(|i| format!("a{i}"))
                .find(|n| !p.atoms.names.contains_key(n.as_str()));
            return Some(Rep::Value(Value::atom(&name.expect("a name is free"))));
        }
        for (name, a) in &p.atoms.names {
            if a.bare {
                return Some(Rep::Value(Value::atom(name)));
            }
            if let Some(Rep::Tuple(_)) = self.rep(&a.payload) {
                return Some(Rep::Atom(name.clone(), a.payload.clone()));
            }
        }
        if p.tuples.rest {
            let len = (0..)
                .find(|n| !p.tuples.lens.contains_key(n))
                .expect("a length is free");
            return Some(Rep::Tuple(Row::new(vec![Type::top(); len])));
        }
        for (len, f) in &p.tuples.lens {
            let (mut b, mut g) = (self.region(vec![Type::top(); *len], f), f.clone());
            if self.narrow_tuples(&mut b, &mut g) {
                continue;
            }
            let r = b.r;
            let mut first = None;
            g.atoms(&mut |a| {
                first = Some(a.clone());
                false
            });
            let mut rows = vec![Row::new(r.clone())];
            if let Some(a) = first {
                rows.push(Row::new(
                    r.iter().zip(a.iter()).map(|(x, y)| x & y).collect(),
                ));
            }
            for row in rows {
                if row.iter().all(|x| self.rep(x).is_some()) && self.holds(&row, f) {
                    return Some(Rep::Tuple(row));
                }
            }
        }
        None
    }

    /// Whether the tuple of the representatives of `row` is in `f`.
    fn holds(&mut self, row: &Row, f: &Part<Row>) -> bool {
        let mut fits = BTreeSet::new();
        for a in f.distinct_atoms() {
            if row.iter().zip(a.iter()).all(|(x, y)| self.member(x, y)) {
                fits.insert(a);
            }
        }
        f.eval(&|a| fits.contains(a))
    }

    /// Whether the representative of `t`, which has one, is in `u`.
    fn member(&mut self, t: &Type, u: &Type) -> bool {
        let key = (t.clone(), u.clone());
        if let Some(b) = self.members.get(&key) {
            return *b;
        }
        let b = match self.rep(t).expect("a representative was found") {
            Rep::Value(v) => u.contains(&v),
            Rep::Tuple(row) => self.holds(&row, &u.p().tuples.get(row.len())),
            Rep::Atom(name, payload) => match u.p().atoms.names.get(&name) {
                None => u.p().atoms.cofinite,
                Some(a) => self.member(&payload, &a.payload.clone()),
            },
        };
        self.members.insert(key, b);
        b
    }

    /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
    /// empty morphism is the only one, and its domain is the guarantee.
    fn within(&mut self, m: &Morphism, n: &Morphism) -> bool {
        let no_value = self.empty(&m.value);
        self.empty(&(&n.guarantee - &m.guarantee))
            && (no_value || self.empty(&(&m.permission - &n.permission)))
            && (no_value || self.empty(&m.permission) || self.empty(&(&m.value - &n.value)))
    }

    /// Whether no morphism `r` admits is in `f`, decided as for tuples: `r` meets the morphism
    /// types in every value of `f`, and, once on each branch, when `f` holds nothing outside
    /// the open morphism types, each is decided on its own. Morphism types are closed under
    /// meet but not under difference, so a type in no value of `f` narrows nothing.
    fn morphisms(&mut self, mut r: Morphism, mut f: Part<Morphism>, may_cover: bool) -> bool {
        loop {
            if self.no_morphism(&r) {
                return true;
            }
            let st: BTreeMap<Morphism, Option<bool>> = f
                .distinct_atoms()
                .into_iter()
                .map(|a| {
                    let s = if self.no_morphism(&meet(&r, &a)) {
                        Some(false)
                    } else if self.within(&r, &a) {
                        Some(true)
                    } else {
                        None
                    };
                    (a, s)
                })
                .collect();
            f = f.restrict(&|a| st.get(a).copied().flatten()).settle();
            if let Some(b) = f.is_leaf() {
                return !b;
            }
            let (taken, _) = f.forced();
            if !taken.is_empty() {
                r = taken.iter().fold(r, |r, a| meet(&r, a));
                continue;
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                return f
                    .distinct_atoms()
                    .iter()
                    .all(|a| self.morphisms(meet(&r, a), f.clone(), false));
            }
            return false;
        }
    }
}

/// The morphisms both `a` and `b` admit.
fn meet(a: &Morphism, b: &Morphism) -> Morphism {
    Morphism {
        guarantee: &a.guarantee | &b.guarantee,
        permission: &a.permission & &b.permission,
        value: &a.value & &b.value,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// In `(a - b) | (b - a)` the diagram tests `b` on two nodes; the region gives each tuple
    /// type one entry, so each is tested once and counted once among those open on a component.
    #[test]
    fn a_region_lists_each_tuple_type_once() {
        let a = Type::tuple(vec![Type::int(), Type::top()]);
        let b = Type::tuple(vec![Type::top(), Type::int()]);
        let t = &(&a - &b) | &(&b - &a);
        let f = &t.p().tuples.lens[&2];
        let mut nodes = 0;
        f.atoms(&mut |_| {
            nodes += 1;
            true
        });
        assert_eq!(nodes, 3);
        let g = Search::default().region(vec![Type::top(); 2], f);
        assert_eq!((g.atoms.len(), g.missed.len()), (2, 2));
        assert_eq!(g.opens, [1, 1]);
    }

    /// Tuple types with one type in a component share its cell there, which is tested once
    /// for all of them; a type that holds the box there is closed, and one open on it is open.
    #[test]
    fn tuple_types_with_one_component_type_share_its_cell() {
        let lit = |i| Type::lit(&Value::Int(i)).unwrap();
        let ints = Type::int();
        let rows: Vec<Type> = (0..4)
            .map(|i| Type::tuple(vec![lit(i), ints.clone(), lit(i % 2)]))
            .collect();
        let t = Type::union_all(rows);
        let f = &t.p().tuples.lens[&3];
        let g = Search::default().region(vec![Type::top(); 3], f);
        let sizes: Vec<Vec<usize>> = g
            .cells
            .iter()
            .map(|cells| cells.iter().map(|c| c.rows.len()).collect())
            .collect();
        assert_eq!(sizes, [vec![1, 1, 1, 1], vec![4], vec![2, 2]]);
        assert_eq!(g.opens, [4, 4, 4]);
        let mut h = Search::default().region(vec![Type::top(), Type::int(), Type::top()], f);
        assert_eq!(h.opens, [4, 0, 4]);
        assert!(h.loose.iter().all(|&(n, at)| (n, at) == (2, 2)));
        // Narrowing the last component to `0` closes the cell `1` as missed for both of its
        // tuple types at once, and leaves `0` to be tested again.
        h.shrink(2, lit(0));
        let mut s = Search::default();
        s.retest(&mut h);
        for (k, a) in h.atoms.iter().enumerate() {
            assert_eq!(h.missed[k], usize::from(a[2] == lit(1)), "{k}");
        }
        assert_eq!(h.opens, [4, 0, 0]);
    }
}
