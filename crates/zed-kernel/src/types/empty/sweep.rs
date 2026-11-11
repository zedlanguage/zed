//! The front sweep (plan item RFX-front): the difference of list types whose tuple parts are
//! chains, decided one place of the list at a time, with the chains kept as runs.
//!
//! The class, read from the types alone before any claim. A *head* ([`head_ok`]) is a type of
//! booleans, integers of 64 bits, bare atoms of finitely many names and tuple types, each
//! tuple length a clause with a row taken whose components are booleans and integers of 64
//! bits; no rationals, floats, strings, structs or functions. A *link* is a type whose parts
//! are atoms only (no other universe, not cofinite), each bare or with an empty payload,
//! except one atom name `c`, the same for every link, whose payload is pairs only, one tuple
//! type `(h, y)` with `h` a head, or a union of such tuple types all but one of which go to
//! a link that is its own tail (the *side rows*, read only on refused threads); or no `c`
//! payload at all. The query `t` has the same parts,
//! but its `c` payload is a meet of tuple types and complements of tuple types (a clause, at
//! least one taken), each `(h, y)` with `h` a head and `y` a link, and every type reached
//! from a `y` by second components is a link. A product of such queries (one tuple type,
//! nothing taken out of it) is in the class too, by its components. Last, the links reached
//! must be *bounded* ([`Sweep::bounded`], "The bound" below). Recognizing the class costs one
//! read of each type reached, O(size of `t`'s types), plus O(links) for the bound. Inside the
//! class the query is a meet of *threads*, the taken ones, less a union of threads, the
//! others; a thread is a link at a depth, or one of `t`'s own rows at depth 0.
//!
//! The semantics, by the parts (each line exact, since an atom of name `c` with a payload and
//! any other atom are disjoint, and the types are read least, values being finite):
//! a link `X` holds `E(X) ∪ c(h(X) × S(X))`, `E(X)` its bare atoms and `S(X)` its tail type; so
//! `∩P \ ∪N` holds the bare atoms `∩E(P) \ ∪E(N)` and `c(a, x)` exactly when `a` is in every
//! head of `P` and `x ∈ ∩S(P) \ ∪{S(n) : n ∈ N, a ∈ h(n)}`. The heads cut `∩h(P)` into classes
//! (the atoms of the algebra the negative heads generate), and on one class the set of
//! negative threads whose head holds `a` is the same for every `a`. So the state at depth
//! `d+1` for class `κ` is `∩S(P) \ ∪{S(n) : κ ⊆ h(n)}`, and the state at depth `d` is empty
//! exactly when its bare atoms are and each class's state is. A class is kept as one value
//! of it and the negative heads that hold it ([`Sweep::classes`]); the values read are the
//! listed literals and tuple cells of the heads plus one unlisted integer, which stand for
//! all values.
//!
//! The carrier head. When `t` has taken rows `(h, X)` whose tail `X` has the one row `(h, X)`,
//! every item of every list of `t` is in each such `h`, so in their meet `C`; each head `g`
//! written in a row is then read as `g ∩ C`, which holds the same items of `C` (one meet per
//! distinct head, at reading). Heads that differ only outside `C` (`int | #a_i` with `C` the
//! integers) are then one head, and one signature along a chain. Taking all such rows makes
//! `C` independent of their order.
//!
//! Links are merged first ([`Sweep::merge`]): links with equal bare atoms and heads whose
//! tails are merged hold the same set, so equal definitions in different groups, which are
//! different types, are one link. The sweep then follows the one class whose state it cannot
//! close at once; a class is closed when a negative thread on it has the tail of a taken one
//! (`∩S(P) ⊆ S(p) = S(n)`), or, with no negative thread on it and one taken thread, by a walk
//! down that thread's tail (a link with one tuple type is empty exactly when no link on its
//! chain of tails, before a repeat, has a bare atom; and when it is empty every class is).
//! Two classes or more left open end the sweep: with a list that ends one place later when the
//! next state of one of them has a bare atom no negative thread on it has, else with no claim.
//! A state with no taken thread alone where one is needed, or whose threads are all on cycles
//! of tails, also ends it with no claim, and the search decides `t` as before.
//!
//! The check. An `Inhabited` is given only for a list that [`Sweep::check`] finds in `t`. The
//! check reads [`Plain`]: the links as read from `t`'s rows, before the merge, with their own
//! runs. It does not read the merge, the threads, the kinds or the classes; it tests each row
//! of `t` on the list by the links' equations, each item by `Type::contains` on the head, after
//! testing each item against `C` (so heads read as `g ∩ C` give the answers `g` gives).
//! Cost: one step per run of each row plus, per head, each index of the list once
//! ([`Sweep::first_miss`]), O((links + rows + length) log n). A list the check rejects gives
//! no claim, and the search decides `t`.
//!
//! The runs. A thread's *signature* at a link is its bare atoms, its head and, when its tail is
//! on a cycle, that tail. Along a chain of links on no cycle the signature is often the same for
//! many steps (`F{i} -> F{i-1}` all have head `int` and no bare atom), and the sweep reads a
//! thread only where the signature changes: each link knows how many steps its signature lasts
//! (`run`) and the link it reaches then (`jump`), computed once for every link in one pass. The
//! threads of one sign and signature form one *kind*; the sweep reads the kinds at each depth,
//! never the threads, and a thread is moved from kind to kind by a queue of events keyed by
//! depth. Two threads of one sign at one link are one from then on, so threads on cycles of
//! tails, which move at every depth, are at most one per kind. A kind with no thread left is
//! removed, so each depth reads only the kinds that have a thread.
//!
//! Side rows and groups. A link with side rows holds, past its main row, `c(h_s × S(z_s))` for
//! each side row, `z_s` its own tail; on a refused thread each side row is one more negative
//! unit at that depth, with head `h_s` and a tail that never changes, so it is read like a
//! kind (one unit per kind and side row) and is part of the signature. A taken thread that
//! reaches a link with side rows puts `t` outside the class. Negative threads of different
//! heads that reach one link at the next depth are one thread from there on, so on a class
//! they count as one unit whose head is the union of theirs ([`Sweep::join`], cached per set
//! of heads); without this, `n` such threads give `n` classes at one depth and the next state
//! is read once per class.
//!
//! The bound. The links reached from the roots (`t`'s rows, merged) are *bounded* when (i) at
//! most one of them lies on a cycle of tails, and it is its own tail (the *carrier*), and
//! (ii) a link below a *join* (a link with two ways in) has its tail's signature, unless that
//! tail is *final*: it has no tuple type, or no tail, or its tail is the carrier. A link is
//! *private* when it is below no join; one root reaches it, at one depth. Then, with `L`
//! links, `R` rows and `P ≤ L` private links (proof sketch):
//! - depths: a depth whose threads are all on the carrier ends the sweep, and a thread off
//!   the carrier is on a path with no repeat, so the depths are at most `L + 1`;
//! - events: a thread changes signature at most once per private link it passes, once on
//!   entering the part below a join (constant by (ii)), once at a final link and once on
//!   reaching the carrier, so the events are at most `P + 3R`;
//! - kinds read: a private link holds a thread at one depth only (`≤ P` in all); below a
//!   join, the threads on one segment of one signature enter after a private path and leave
//!   within the segment's length, so a segment is read at most at `(longest private path
//!   into it) + (its length)` depths, `≤ P + L` over all segments; final links add `≤ R`
//!   and the carrier `≤ 2` per depth. So `Σ_d K_d = O(L + R)`.
//!
//! Complexity tradeoff: the naive version is the search's, which at each depth builds the
//! difference of the tail with every negative tail open on the class, `Θ(k)` at a depth with
//! `k` negative threads, `Θ(n²)` over the `n` depths of the front family (1.2·n² types built).
//! Used: the links read once and merged (O(L log L)), the carrier head (one meet per taken
//! row of its form, and one meet with it per distinct head read, cached), one pass for `run`
//! and `jump` (O(L)), the bound (O(L)), then one step per depth, each reading the kinds that
//! have a thread and their classes, kept for each pair of a head and a set of negative heads,
//! plus `O(log n)` per event. With the bound: O((L + R) log n) steps, each of a size set by
//! the heads read (the classes of a pair cost O((Σ literals) log) for integers and atoms,
//! O(cells · K) for booleans and tuples), and the check as above. So O(n log n) for the front
//! and far families and the variants in `l01_23_subtyping::refusals` whose heads have a size
//! fixed as `n` grows. Given up: a head whose size grows with `n` and is read at many depths pays
//! its size at each; inputs outside the class pay their recognition (at most the cost above)
//! and then the search with today's verdict. Memory: O(L + R + cached classes).
//! Preconditions: the class above. Nothing is refused here: a state the sweep does not close
//! goes back to the search, whole.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::Arc;

use super::super::bdd::Part;
use super::super::{Lits, Parts, PartsRef, Row, Type, Verdict};
use super::shared::ByType;
use crate::value::Value;

const NONE: usize = usize::MAX;

/// A link, by number; numbers past the types are `t`'s own rows.
struct Link {
    /// Its bare atoms, by number in [`Sweep::es`].
    e: usize,
    /// Its head, by number in [`Sweep::heads`], or none when it has no `c` payload.
    head: usize,
    /// Its tail, a link, or `NONE`.
    tail: usize,
    cyclic: bool,
    /// How many steps its signature lasts, `NONE` for ever, and the link reached then.
    run: usize,
    jump: usize,
    /// Its *side rows*, by number in [`Sweep::sides`], or `NONE`: the rows of a union payload
    /// other than the one whose tail is `tail`, each to a link that is its own tail.
    sides: usize,
    /// The side rows as read, (head, tail), before the merge.
    side_rows: Vec<(usize, usize)>,
}

/// A signature: bare atoms, head, the tail when it is on a cycle, and the side rows.
type Sig = (usize, usize, usize, usize);

/// What one set of kinds cuts the positive head into ([`Sweep::classes`]).
struct ClassSet {
    /// The negative heads whose integers are cofinite.
    cof: BTreeSet<usize>,
    list: Vec<Class>,
}

/// One class: a value of it, and the negative heads that hold it: those of `delta`, read
/// against `cof` when `flip` (a class of integers), so that the class of an integer no head
/// lists names no head.
struct Class {
    v: Value,
    flip: bool,
    delta: BTreeSet<usize>,
}

type Classes = Rc<ClassSet>;

#[derive(Default)]
#[allow(clippy::type_complexity)]
struct Sweep {
    c: Option<Arc<str>>,
    links: Vec<Link>,
    ids: ByType<usize>,
    es: Vec<BTreeSet<Arc<str>>>,
    e_ids: BTreeMap<BTreeSet<Arc<str>>, usize>,
    heads: Vec<Type>,
    head_ids: ByType<usize>,
    classes: BTreeMap<(usize, Vec<usize>), Classes>,
    /// The walk of each link alone: `Some(Some((value, next)))` for a step or an end, `Some(None)`
    /// for empty.
    walked: Vec<Option<Option<Step>>>,
    /// Per head and index, for the list being checked, the end of the held stretch the index
    /// starts: the index itself when its item is not in the head ([`Sweep::first_miss`]).
    misses: HashMap<(usize, usize), usize>,
    meets: BTreeMap<Vec<usize>, usize>,
    joins: BTreeMap<Vec<usize>, usize>,
    /// Each set of side rows: (head, label of the tail) sorted, with one tail of each, as read.
    sides: Vec<Vec<(usize, usize)>>,
    side_ids: BTreeMap<Vec<(usize, (usize, usize))>, usize>,
    /// Each link's representative after the merge.
    rep: Vec<usize>,
    /// For the check: per (side head, side tail) and index, as `misses`, the first index from
    /// it at which the side row holds the rest of the list.
    goods: HashMap<((usize, usize), usize), usize>,
    /// The carrier head `C`: the meet of the heads `h` of `t`'s taken rows `(h, X)` whose tail
    /// `X` has the one row `(h, X)`, or none. Every item of every list of `t` is in `C`, so
    /// each head `h` read from a row is read as `h ∩ C` ([`Sweep::read_head`]), which holds the
    /// same items of `C`; the check tests each item against `C` first.
    carrier: Option<Type>,
    /// The head read for each head as written, when there is a carrier.
    read: ByType<Option<usize>>,
    /// The carrier link `Z`, when one link is on a cycle of tails and is its own tail.
    z: Option<usize>,
    /// Per link, whether all its lists are lists of `Z` ([`Sweep::subs`]).
    sub: Vec<bool>,
}

/// The bare atoms of `p` and, when it has one, the clause of its one payload, by name `c`; `None`
/// when `p` is outside the class.
///
/// Complexity tradeoff: reading every name to find the payload costs O(names log names) for
/// each type asked, also for the many types outside the class, as a set of `n` failure atoms
/// asked at each of `n` steps of a chain (`n^2 log n`, batch merge 128). Used: the payload name
/// is read from the atoms' set of payload names (`Atoms::payloads`, O(log n)) and the clause is
/// checked before the bare atoms are collected, so a type outside the class costs O(log n) here
/// and one inside it O(names log names), a part of reading it.
#[allow(clippy::type_complexity)]
fn shape(
    p: &Parts,
    c: &mut Option<Arc<str>>,
) -> Option<(BTreeSet<Arc<str>>, Option<(Clause, bool)>)> {
    if p.has_scalars()
        || p.atoms.cofinite
        || !p.tuples.is_default()
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
        || p.atoms.payloads.len() > 1
    {
        return None;
    }
    let mut clause = None;
    if let Some(name) = p.atoms.payloads.get_min() {
        if c.get_or_insert_with(|| name.clone()) != name {
            return None;
        }
        let q = p.atoms.names.get(name)?.payload.p();
        if q.has_scalars()
            || !q.atoms.is_default()
            || q.structs
            || q.morphisms.is_leaf() != Some(false)
            || q.tuples.rest
            || q.tuples.lens.len() != 1
        {
            return None;
        }
        let part: &Part<Row> = q.tuples.lens.get(&2)?;
        // A clause, or else a union of rows (marked `true`).
        let (taken, refused, union): (Vec<Row>, Vec<Row>, bool) = match part.clause() {
            Some((taken, refused)) => (taken, refused, false),
            None => (part.union_rows()?, Vec::new(), true),
        };
        let row = |r: &Row| r.len() == 2 && head_ok(&r[0]);
        if taken.is_empty() || !taken.iter().chain(&refused).all(row) {
            return None;
        }
        clause = Some(((taken, refused), union));
    }
    let e = (p.atoms.names.iter())
        .filter(|(_, part)| part.bare)
        .map(|(name, _)| name.clone())
        .collect();
    Some((e, clause))
}

type Clause = (Vec<Row>, Vec<Row>);

/// The least `p` such that `s` is `s[..p]` repeated, by the prefix function: O(|s|).
fn period<T: Eq>(s: &[T]) -> usize {
    let n = s.len();
    let mut f = vec![0usize; n];
    for i in 1..n {
        let mut k = f[i - 1];
        while k > 0 && s[i] != s[k] {
            k = f[k - 1];
        }
        if s[i] == s[k] {
            k += 1;
        }
        f[i] = k;
    }
    let p = n - f[n - 1];
    if n.is_multiple_of(p) { p } else { n }
}

/// The start of the least rotation of `s`, by the two-index method: O(|s|).
fn least_rotation<T: Ord>(s: &[T]) -> usize {
    let n = s.len();
    let (mut i, mut j, mut k) = (0usize, 1usize, 0usize);
    while i < n && j < n && k < n {
        let (a, b) = (&s[(i + k) % n], &s[(j + k) % n]);
        if a == b {
            k += 1;
            continue;
        }
        if a > b {
            i += k + 1;
        } else {
            j += k + 1;
        }
        if i == j {
            j += 1;
        }
        k = 0;
    }
    i.min(j)
}

/// Whether a type of scalars is one a head's tuple may hold: booleans and integers of 64 bits.
fn scalar_ok(p: &Parts) -> bool {
    p.scalars_only() && lits_ok(p)
}

/// Whether `p` lists no rational, float or string, and only integers of 64 bits.
fn lits_ok(p: &Parts) -> bool {
    [&p.rats, &p.floats, &p.strings]
        .iter()
        .all(|l: &&Lits| !l.cofinite && l.values.is_empty())
        && p.ints.values.iter().all(|v| matches!(v, Value::Int(_)))
}

/// Whether `h` is a head of the class: booleans and integers of 64 bits, bare atoms of
/// finitely many names, and tuple types, each length a clause with a row taken, of rows of
/// such scalars.
fn head_ok(h: &Type) -> bool {
    let p = h.p();
    let atoms =
        !p.atoms.cofinite && (p.atoms.names.values()).all(|a| a.bare && a.payload.lists_nothing());
    let tuples = !p.tuples.rest
        && p.tuples.lens.iter().all(|(&len, part)| {
            part.clause().is_some_and(|(taken, refused)| {
                !taken.is_empty()
                    && (taken.iter().chain(&refused))
                        .all(|r| r.len() == len && r.iter().all(|c| scalar_ok(&c.p())))
            })
        });
    lits_ok(&p) && atoms && tuples && !p.structs && p.morphisms.is_leaf() == Some(false)
}

/// The integers that stand for all of them against the integer parts `ls`: each one listed,
/// and the least from 0 that none lists (found within the first `listed + 1`).
fn int_candidates<'a>(ls: impl Iterator<Item = &'a Lits>) -> Vec<Value> {
    let mut listed: BTreeSet<Value> = BTreeSet::new();
    for l in ls {
        listed.extend(l.values.iter().cloned());
    }
    let fresh = (0..).map(Value::Int).find(|v| !listed.contains(v));
    listed.into_iter().chain(fresh).collect()
}

/// The values that stand for every value of a component, against the component types `cs`:
/// the booleans some of them hold, and the integers ([`int_candidates`]). `false` and `true`
/// are told apart only when some type holds just one of them; otherwise `false` stands for
/// both, so a component every type holds as all of `bool` adds one cell, not two (X20).
fn component_candidates(cs: &[Type]) -> Vec<Value> {
    let ps: Vec<PartsRef<'_>> = cs.iter().map(|c| c.p()).collect();
    let mut out: Vec<Value> = Vec::new();
    let split = ps.iter().any(|p| p.bools == 1 || p.bools == 2);
    for (bit, b) in [(1u8, false), (2u8, true)] {
        if ps.iter().any(|p| p.bools & bit != 0) && (split || out.is_empty()) {
            out.push(Value::Bool(b));
        }
    }
    if ps
        .iter()
        .any(|p| p.ints.cofinite || !p.ints.values.is_empty())
    {
        out.extend(int_candidates(ps.iter().map(|p| &p.ints)));
    }
    out
}

impl Sweep {
    fn e_id(&mut self, e: BTreeSet<Arc<str>>) -> usize {
        if let Some(&i) = self.e_ids.get(&e) {
            return i;
        }
        self.es.push(e.clone());
        self.e_ids.insert(e, self.es.len() - 1);
        self.es.len() - 1
    }

    fn head_id(&mut self, h: &Type) -> usize {
        if let Some(&i) = self.head_ids.get(h) {
            return i;
        }
        self.heads.push(h.clone());
        self.head_ids.insert(h.clone(), self.heads.len() - 1);
        self.heads.len() - 1
    }

    /// The number of the head `h ∩ C` for a head `h` written in a row ([`Sweep::carrier`]),
    /// each `h` met once; `None` when the meet is outside the class of heads.
    fn read_head(&mut self, h: &Type) -> Option<usize> {
        let Some(c) = &self.carrier else {
            return Some(self.head_id(h));
        };
        if let Some(&i) = self.read.get(h) {
            return i;
        }
        let m = h & c;
        let i = head_ok(&m).then(|| self.head_id(&m));
        self.read.insert(h.clone(), i);
        i
    }

    /// Numbers `t` and every type reached from it by tails, from a stack, each once; `None` when
    /// one is not a link.
    fn link(&mut self, t: &Type) -> Option<usize> {
        let mut stack = vec![t.clone()];
        // The links numbered here whose tails are numbered after them.
        let mut pending: Vec<(usize, usize, Type)> = Vec::new();
        while let Some(x) = stack.pop() {
            if self.ids.contains_key(&x) {
                continue;
            }
            let (e, clause) = shape(&x.p(), &mut self.c)?;
            let e = self.e_id(e);
            let rows: Vec<Row> = match clause {
                None => Vec::new(),
                Some(((taken, refused), union)) => {
                    if (!union && taken.len() != 1) || !refused.is_empty() {
                        return None;
                    }
                    taken
                }
            };
            let i = self.links.len();
            self.links.push(Link {
                e,
                head: NONE,
                tail: NONE,
                // Set by `merge`, from the graph of tails.
                cyclic: false,
                run: NONE,
                jump: i,
                sides: NONE,
                side_rows: Vec::new(),
            });
            self.ids.insert(x, i);
            for r in rows {
                let h = self.read_head(&r[0])?;
                pending.push((i, h, r[1].clone()));
                stack.push(r[1].clone());
            }
        }
        // Each link's rows, numbered. One row is the head and tail. Of two or more, a row to a
        // link of one row that is its own tail is a side row; the one other row (or else the
        // least side row) is the head and tail, and two other rows put the link outside the
        // class. Links of one row are set first, so that `loops` reads them.
        let mut rows: BTreeMap<usize, Vec<(usize, usize)>> = BTreeMap::new();
        for (i, h, y) in pending {
            rows.entry(i).or_default().push((h, self.ids[&y]));
        }
        let (one, many): (Vec<_>, Vec<_>) = rows.into_iter().partition(|(_, rs)| rs.len() == 1);
        for (i, rs) in one {
            (self.links[i].head, self.links[i].tail) = rs[0];
        }
        for (i, mut rs) in many {
            let lab = |l: &Link| (l.e, l.head);
            let loops = |y: usize| {
                let l = &self.links[y];
                l.tail == y && l.sides == NONE
            };
            rs.sort_by_key(|&(h, y)| (!loops(y), h, lab(&self.links[y])));
            rs.dedup();
            let others: Vec<(usize, usize)> = rs.iter().filter(|r| !loops(r.1)).copied().collect();
            let main = match others[..] {
                [] => rs[0],
                [m] => m,
                _ => return None,
            };
            let side_rows: Vec<(usize, usize)> = rs.into_iter().filter(|&r| r != main).collect();
            let mut key: Vec<(usize, (usize, usize))> = side_rows
                .iter()
                .map(|&(h, y)| (h, lab(&self.links[y])))
                .collect();
            key.sort();
            key.dedup();
            let id = match self.side_ids.get(&key) {
                Some(&id) => id,
                None => {
                    let tails = (key.iter())
                        .map(|&(h, l)| {
                            let y =
                                (side_rows.iter()).find(|r| r.0 == h && lab(&self.links[r.1]) == l);
                            (h, y.expect("from the rows").1)
                        })
                        .collect();
                    self.sides.push(tails);
                    self.side_ids.insert(key, self.sides.len() - 1);
                    self.sides.len() - 1
                }
            };
            let l = &mut self.links[i];
            (l.head, l.tail, l.sides, l.side_rows) = (main.0, main.1, id, side_rows);
        }
        Some(self.ids[t])
    }

    /// A link for one of `t`'s own rows, with bare atoms `e`, its tail numbered.
    fn row(&mut self, r: &Row, e: usize) -> Option<usize> {
        let tail = self.link(&r[1])?;
        let head = self.read_head(&r[0])?;
        let i = self.links.len();
        self.links.push(Link {
            e,
            head,
            tail,
            cyclic: false,
            run: NONE,
            jump: i,
            sides: NONE,
            side_rows: Vec::new(),
        });
        Some(i)
    }

    /// Merges links that hold the same set: links are states with a label (bare atoms, head)
    /// and one tail, and two links with equal labels and merged tails hold the same set (the
    /// equations are guarded by `c`, so their least solution is their only one). Equal
    /// definitions of different groups are different types, so this is what makes the tail
    /// of `F1` in one group the `L` of another. Each link's `tail` is set to its tail's
    /// representative and `cyclic` to whether it lies on a cycle of tails; returns each link's
    /// representative.
    ///
    /// Complexity tradeoff: the naive minimization refines a partition until stable, O(links²).
    /// Used: a graph where each node has at most one successor is cycles with trees hanging
    /// on them, so each cycle is named by the least rotation of its labels cut to their
    /// period (O(length), by the two-index method), and each node off a cycle by its label
    /// and its tail's name, interned in sorted maps from the cycles outward: O(links log links).
    /// Given up: nothing; the result is the coarsest partition, as by refinement.
    fn merge(&mut self) -> Vec<usize> {
        let n = self.links.len();
        let label = |l: &Link| (l.e, l.head, l.sides);
        // The nodes of each cycle, in tail order, from a walk of each node until a known one.
        let mut state = vec![0u8; n]; // 0 new, 1 on this walk, 2 done
        let mut cycles: Vec<Vec<usize>> = Vec::new();
        for x in 0..n {
            let mut path = Vec::new();
            let mut y = x;
            while y != NONE && state[y] == 0 {
                state[y] = 1;
                path.push(y);
                y = self.links[y].tail;
            }
            if y != NONE && state[y] == 1 {
                let at = path.iter().position(|&p| p == y).expect("on this walk");
                cycles.push(path[at..].to_vec());
            }
            for p in path {
                state[p] = 2;
            }
        }
        let mut name = vec![NONE; n];
        let mut cyclic = vec![false; n];
        let mut cycle_ids: BTreeMap<Vec<(usize, usize, usize)>, usize> = BTreeMap::new();
        let mut names = 0usize;
        for cy in &cycles {
            let ls: Vec<(usize, usize, usize)> =
                cy.iter().map(|&x| label(&self.links[x])).collect();
            let p = period(&ls);
            let s = least_rotation(&ls[..p]);
            let key: Vec<(usize, usize, usize)> = (0..p).map(|j| ls[(s + j) % p]).collect();
            let base = *cycle_ids.entry(key).or_insert_with(|| {
                names += p;
                names - p
            });
            for (j, &x) in cy.iter().enumerate() {
                name[x] = base + (j + p - s % p) % p;
                cyclic[x] = true;
            }
        }
        // Nodes off cycles, each after its tail, from a stack.
        let mut tree_ids: BTreeMap<((usize, usize, usize), usize), usize> = BTreeMap::new();
        for x in 0..n {
            let mut path = Vec::new();
            let mut y = x;
            while y != NONE && name[y] == NONE {
                path.push(y);
                y = self.links[y].tail;
            }
            for &p in path.iter().rev() {
                let t = self.links[p].tail;
                let key = (
                    label(&self.links[p]),
                    if t == NONE { NONE } else { name[t] },
                );
                name[p] = *tree_ids.entry(key).or_insert_with(|| {
                    names += 1;
                    names - 1
                });
            }
        }
        let mut first = vec![NONE; names];
        for x in 0..n {
            if first[name[x]] == NONE {
                first[name[x]] = x;
            }
        }
        let rep: Vec<usize> = (0..n).map(|x| first[name[x]]).collect();
        for (link, &cyc) in self.links.iter_mut().zip(&cyclic) {
            let t = link.tail;
            link.tail = if t == NONE { NONE } else { rep[t] };
            link.cyclic = cyc;
        }
        rep
    }

    /// Whether the links reached from `roots` (merged) are in the bounded class, which makes
    /// the sweep O(n log n) (module comment, "The bound"): (i) at most one link lies on a cycle
    /// of tails, and it is its own tail (a *carrier*); (ii) a link below a *join* (a link with
    /// two ways in: two links whose tail it is, or a root and such a link, or two roots) has
    /// the signature of its tail, unless that tail is *final*: it has no tuple type, or no
    /// tail, or its tail is the carrier. One pass over the links reached: O(links).
    fn bounded(&self, roots: &[usize]) -> bool {
        let n = self.links.len();
        let (mut seen, mut indeg, mut order) = (vec![false; n], vec![0usize; n], Vec::new());
        for &r in roots {
            indeg[r] += 1;
            let mut y = r;
            while y != NONE && !seen[y] {
                seen[y] = true;
                order.push(y);
                let t = self.links[y].tail;
                if t != NONE {
                    indeg[t] += 1;
                }
                y = t;
            }
        }
        // The tails of side rows are reached too, each its own tail; a link with side rows on a
        // cycle is outside the class.
        for k in 0..order.len() {
            let l = &self.links[order[k]];
            if l.sides == NONE {
                continue;
            }
            if l.cyclic {
                return false;
            }
            for &(_, z) in &self.sides[l.sides] {
                let z = self.rep[z];
                if !seen[z] {
                    seen[z] = true;
                    order.push(z);
                }
            }
        }
        let mut cyclic = order.iter().filter(|&&y| self.links[y].cyclic);
        match (cyclic.next(), cyclic.next()) {
            (Some(&y), None) if self.links[y].tail == y => {}
            (None, _) => {}
            _ => return false,
        }
        let fin = |z: usize| {
            let l = &self.links[z];
            l.head == NONE || l.tail == NONE || self.links[l.tail].cyclic
        };
        let mut below = vec![false; n];
        for &y in &order {
            if indeg[y] < 2 {
                continue;
            }
            let mut x = y;
            while x != NONE && !below[x] && !self.links[x].cyclic {
                below[x] = true;
                x = self.links[x].tail;
            }
        }
        order.iter().all(|&x| {
            let z = self.links[x].tail;
            !below[x] || z == NONE || self.links[z].cyclic || fin(z) || self.sig(x) == self.sig(z)
        })
    }

    /// `Z` and `sub` ([`Sweep::z`]). A link `x` with no side row, bare atoms among `Z`'s,
    /// and either no tuple type or a head inside `Z`'s and a tail whose lists are all `Z`'s, has
    /// all its lists in `Z`, since `Z` holds `(head(Z), Z)` and its bare atoms. A head is found
    /// inside `Z`'s when its meet with it is the same head, which is enough, not needed: a
    /// head not found so only leaves `sub` false. Each chain walked once from a stack, the links
    /// other than `Z` being on no cycle: O(links) meets.
    fn subs(&mut self) {
        let n = self.links.len();
        self.sub = vec![false; n];
        let mut cyc = (0..n).filter(|&x| self.rep[x] == x && self.links[x].cyclic);
        let z = match (cyc.next(), cyc.next()) {
            (Some(z), None) if self.links[z].tail == z => z,
            _ => return,
        };
        self.z = Some(z);
        let (hz, ez) = (self.links[z].head, self.links[z].e);
        let mut done = vec![false; n];
        (self.sub[z], done[z]) = (true, true);
        for x in 0..n {
            let mut path = Vec::new();
            let mut y = x;
            while y != NONE && !done[y] {
                if self.links[y].cyclic {
                    // A link on a cycle other than `Z`: not a link of the merged class.
                    done[y] = true;
                    break;
                }
                path.push(y);
                y = self.links[y].tail;
            }
            for &p in path.iter().rev() {
                let l = &self.links[p];
                let (h, t, e, sides) = (l.head, l.tail, l.e, l.sides);
                let mut ok = sides == NONE && self.es[e].is_subset(&self.es[ez]);
                if ok && h != NONE {
                    ok = t != NONE && self.sub[t] && hz != NONE && self.meet(vec![h, hz]) == h;
                }
                self.sub[p] = ok;
                done[p] = true;
            }
        }
    }

    fn sig(&self, x: usize) -> Sig {
        let l = &self.links[x];
        let cyc = match l.tail {
            NONE => NONE,
            y if self.links[y].cyclic => y,
            _ => NONE,
        };
        (l.e, l.head, cyc, l.sides)
    }

    /// `run` and `jump` of every link, each chain walked once from a stack: a link on no cycle
    /// whose tail is on no cycle and has its signature lasts one step more than its tail.
    /// `None` when links on no cycle form a cycle, which a type built from finite terms and
    /// members on no cycle does not.
    fn runs(&mut self) -> Option<()> {
        let n = self.links.len();
        let mut done = vec![false; n];
        let mut on_path = vec![false; n];
        for x in 0..n {
            let mut path = Vec::new();
            let mut y = x;
            while !done[y] {
                if on_path[y] {
                    return None;
                }
                let l = &self.links[y];
                if l.cyclic || l.head == NONE {
                    let (run, jump) = match l.tail {
                        _ if l.head == NONE => (NONE, y),
                        t if t == y => (NONE, y),
                        t => (1, t),
                    };
                    self.links[y].run = run;
                    self.links[y].jump = jump;
                    done[y] = true;
                    break;
                }
                let z = l.tail;
                if self.links[z].cyclic || self.sig(z) != self.sig(y) {
                    self.links[y].run = 1;
                    self.links[y].jump = z;
                    done[y] = true;
                    break;
                }
                on_path[y] = true;
                path.push(y);
                y = z;
            }
            for &p in path.iter().rev() {
                let z = self.links[p].tail;
                self.links[p].run = 1 + self.links[z].run;
                self.links[p].jump = self.links[z].jump;
                done[p] = true;
                on_path[p] = false;
            }
        }
        Some(())
    }

    /// The classes of `pos` (a head) by the heads `neg`, kept for each pair. Two values are in
    /// one class when the same heads of `neg` hold them, and a class is kept as one value of
    /// it and those heads. The values read are those that stand for all ([`int_candidates`],
    /// [`component_candidates`]): a value no head lists behaves as every other such value.
    ///
    /// Complexity tradeoff: the naive version cuts `pos` by each head of `neg` in turn, a meet
    /// and a difference per class and head, `Θ(K · C)` type operations for `K` heads and `C`
    /// classes, `Θ(n²)` for `n` heads each listing its own integer. Used: an integer or atom
    /// is matched to the heads that list it through one map from each listed literal to its
    /// heads, so a class of integers is the heads that list it, read against the heads whose
    /// integers are cofinite; O((Σ literals of the heads) log) per pair. Given up: booleans
    /// and tuples are tested against each head, `O(cells · K)`, where the cells of a tuple
    /// length are the product of its components' candidates.
    fn classes(&mut self, pos: usize, neg: Vec<usize>) -> Classes {
        if let Some(c) = self.classes.get(&(pos, neg.clone())) {
            return c.clone();
        }
        let h = self.heads[pos].clone();
        let gs: Vec<(usize, Type)> = neg.iter().map(|&g| (g, self.heads[g].clone())).collect();
        let p = h.p();
        let cof: BTreeSet<usize> = (gs.iter())
            .filter(|(_, t)| t.p().ints.cofinite)
            .map(|g| g.0)
            .collect();
        let full = |v: &Value| -> BTreeSet<usize> {
            gs.iter()
                .filter(|(_, t)| t.contains(v))
                .map(|g| g.0)
                .collect()
        };
        let mut groups: BTreeMap<(bool, BTreeSet<usize>), Value> = BTreeMap::new();
        let mut add = |flip: bool, delta: BTreeSet<usize>, v: Value| {
            groups.entry((flip && !cof.is_empty(), delta)).or_insert(v);
        };
        for (bit, b) in [(1u8, false), (2u8, true)] {
            if p.bools & bit != 0 {
                let v = Value::Bool(b);
                add(false, full(&v), v);
            }
        }
        if p.ints.cofinite || !p.ints.values.is_empty() {
            let mut lists: BTreeMap<Value, BTreeSet<usize>> = BTreeMap::new();
            for (g, t) in &gs {
                for v in t.p().ints.values.iter() {
                    lists.entry(v.clone()).or_default().insert(*g);
                }
            }
            let in_pos = |v: &Value| p.ints.cofinite != p.ints.values.contains(v);
            for (v, d) in &lists {
                if in_pos(v) {
                    add(true, d.clone(), v.clone());
                }
            }
            // An integer of `pos` that no head of `neg` lists, found within the first
            // `|lists| + |pos's literals| + 1` tried.
            let rest = match p.ints.cofinite {
                true => (0..)
                    .map(Value::Int)
                    .find(|v| in_pos(v) && !lists.contains_key(v)),
                false => p
                    .ints
                    .values
                    .iter()
                    .find(|v| !lists.contains_key(*v))
                    .cloned(),
            };
            if let Some(v) = rest {
                add(true, BTreeSet::new(), v);
            }
        }
        let mut names: BTreeMap<Arc<str>, BTreeSet<usize>> = BTreeMap::new();
        for (g, t) in &gs {
            for (a, part) in t.p().atoms.names.iter() {
                if part.bare {
                    names.entry(a.clone()).or_default().insert(*g);
                }
            }
        }
        for (a, part) in p.atoms.names.iter() {
            if part.bare {
                add(
                    false,
                    names.get(a).cloned().unwrap_or_default(),
                    Value::atom(a),
                );
            }
        }
        for (&len, part) in p.tuples.lens.iter() {
            let mut cols: Vec<Vec<Type>> = vec![Vec::new(); len];
            let mut read = |part: &Part<Row>| {
                if let Some((taken, refused)) = part.clause() {
                    for r in taken.iter().chain(&refused) {
                        for (j, c) in r.iter().enumerate() {
                            cols[j].push(c.clone());
                        }
                    }
                }
            };
            read(part);
            for (_, t) in &gs {
                if let Some(q) = t.p().tuples.lens.get(&len) {
                    read(q);
                }
            }
            let cands: Vec<Vec<Value>> = cols.iter().map(|c| component_candidates(c)).collect();
            // Every tuple of candidates, one component at a time.
            // A component with one candidate extends each tuple in place, so the cells cost
            // O(len) each, not O(len²).
            let mut cells: Vec<Vec<Value>> = vec![Vec::with_capacity(len)];
            for c in &cands {
                if let [v] = c.as_slice() {
                    cells.iter_mut().for_each(|t| t.push(v.clone()));
                    continue;
                }
                cells = (cells.iter())
                    .flat_map(|t| c.iter().map(move |v| [t.clone(), vec![v.clone()]].concat()))
                    .collect();
            }
            for items in cells {
                let v = Value::tuple(items);
                if h.contains(&v) {
                    add(false, full(&v), v);
                }
            }
        }
        let list = (groups.into_iter())
            .map(|((flip, delta), v)| Class { v, flip, delta })
            .collect();
        let out = Rc::new(ClassSet { cof, list });
        self.classes.insert((pos, neg), out.clone());
        out
    }

    /// A value of the head `h`, from its classes alone.
    /// A short escape certificate, independently checked by `check` below. Positive
    /// rows are the integer carrier. There is one stopping guard, with an integer prefix
    /// followed by int\{q} heads, ending at the carrier. Every other negative row has no
    /// stop until a singleton-q terminal and then the carrier. Select a length p inside
    /// the guard's restricted interval such that every negative root of length p has
    /// the same first excluded integer a != q. The word a,f,...,f,q (f != q) escapes:
    /// shorter rows fail at their singleton terminal, longer rows fail on length, equal
    /// rows fail at their first head, and the guard fails on the final q.
    ///
    /// Complexity tradeoff: exploring all open head classes is potentially exponential;
    /// even checking each root by a fresh spine walk is quadratic. This sufficient
    /// certificate uses one visited functional-DAG pass plus sorted maps, O(N log N)
    /// time and O(N) space. No refusal, budget, or size-dependent algorithm is used.
    /// A failed certificate continues to the ordinary sweep/search. The checker uses
    /// minimum-length and mandatory-terminal facts derived from Plain, before merging.
    fn short_escape(&self, roots: &[(usize, bool)]) -> Option<(Vec<Value>, Arc<str>)> {
        let carrier_head = self.carrier.as_ref()?;
        // Exact carrier projection: coordinate zero varies over int; every other
        // coordinate is the same type in every row, so it can be filled once.
        let fixed = if carrier_head == &Type::int() {
            None
        } else {
            let cs = product(&carrier_head.p())?;
            if cs.first()? != &Type::int() {
                return None;
            }
            let mut values = vec![Value::Int(0)];
            for c in &cs[1..] {
                let v = component_candidates(std::slice::from_ref(c))
                    .into_iter()
                    .find(|v| c.contains(v))?;
                values.push(v);
            }
            Some((cs, values))
        };
        // (cofinite, literal); int itself is (true, None).
        let kinds: Vec<Option<(bool, Option<i64>)>> = self
            .heads
            .iter()
            .map(|whole| {
                let projected;
                let h = if let Some((cs, _)) = &fixed {
                    let p = whole.p();
                    if p.has_scalars()
                        || !p.atoms.is_default()
                        || p.structs
                        || p.morphisms.is_leaf() != Some(false)
                        || p.tuples.rest
                        || p.tuples.lens.len() != 1
                    {
                        return None;
                    }
                    let (taken, refused) = p.tuples.lens.get(&cs.len())?.clause()?;
                    if taken.is_empty()
                        || !taken
                            .iter()
                            .chain(&refused)
                            .all(|r| r.len() == cs.len() && r[1..] == cs[1..])
                    {
                        return None;
                    }
                    let mut var = Type::int();
                    for r in &taken {
                        var = &var & &r[0];
                    }
                    for r in &refused {
                        var = &var - &r[0];
                    }
                    projected = var;
                    &projected
                } else {
                    whole
                };
                if h == &Type::int() {
                    return Some((true, None));
                }
                let p = h.p();
                let [Value::Int(v)] = &p.ints.values.iter().cloned().collect::<Vec<_>>()[..] else {
                    return None;
                };
                let one = Type::lit(&Value::Int(*v))?;
                if h == &one {
                    Some((false, Some(*v)))
                } else if h == &(&Type::int() - &one) {
                    Some((true, Some(*v)))
                } else {
                    None
                }
            })
            .collect();
        let full = |h: usize| h != NONE && kinds[h] == Some((true, None));
        let carriers: Vec<_> = self
            .links
            .iter()
            .enumerate()
            .filter(|(i, l)| {
                l.tail == *i && full(l.head) && l.sides == NONE && self.es[l.e].len() == 1
            })
            .map(|(i, _)| i)
            .collect();
        let [carrier] = carriers[..] else {
            return None;
        };
        let ce = self.links[carrier].e;
        if !roots.iter().filter(|r| r.1).all(|&(x, _)| {
            x == carrier
                || full(self.links[x].head)
                    && self.links[x].tail == carrier
                    && self.links[x].sides == NONE
        }) {
            return None;
        }
        let negatives: Vec<_> = roots.iter().filter(|r| !r.1).map(|r| r.0).collect();
        let guards: Vec<_> = negatives
            .iter()
            .copied()
            .filter(|&x| {
                let l = &self.links[x];
                l.tail != NONE
                    && self.links[l.tail].e == ce
                    && l.head != NONE
                    && kinds[l.head].is_some_and(|k| k.0)
            })
            .collect();
        let [guard] = guards[..] else {
            return None;
        };
        let (mut x, mut depth, mut first, mut excluded) = (guard, 0usize, None, None);
        let mut seen = BTreeSet::new();
        while x != carrier {
            if !seen.insert(x) {
                return None;
            }
            let l = &self.links[x];
            if l.head == NONE || l.sides != NONE || l.tail == NONE || depth > 0 && l.e != ce {
                return None;
            }
            depth += 1;
            match kinds[l.head]? {
                (true, Some(q)) => {
                    if excluded.is_some_and(|v| v != q) {
                        return None;
                    }
                    excluded = Some(q);
                    first.get_or_insert(depth);
                }
                (true, None) if excluded.is_none() => {}
                _ => return None,
            }
            x = l.tail;
        }
        let (q, first) = (excluded?, first?);
        let mut lengths = vec![None; self.links.len()];
        let mut state = vec![0u8; self.links.len()];
        state[carrier] = 2;
        for &r in &negatives {
            if r == guard {
                continue;
            }
            let (mut x, mut path) = (r, Vec::new());
            while state[x] == 0 {
                state[x] = 1;
                path.push(x);
                let l = &self.links[x];
                if l.tail == NONE || l.head == NONE || l.sides != NONE || !self.es[l.e].is_empty() {
                    break;
                }
                x = l.tail;
            }
            for &z in path.iter().rev() {
                let l = &self.links[z];
                if l.tail != NONE && l.head != NONE && l.sides == NONE && self.es[l.e].is_empty() {
                    lengths[z] = if l.tail == carrier && kinds[l.head] == Some((false, Some(q))) {
                        Some(1)
                    } else if kinds[l.head].is_some_and(|k| k.0) {
                        lengths[l.tail].map(|n| n + 1)
                    } else {
                        None
                    };
                }
                state[z] = 2;
            }
            lengths[r]?;
        }
        let mut by_length: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for &r in &negatives {
            if r != guard {
                by_length.entry(lengths[r]?).or_default().push(r);
            }
        }
        if first.max(2) > depth {
            return None;
        }
        for (&p, rs) in by_length.range(first.max(2)..=depth) {
            let Some((true, Some(a))) = kinds[self.links[rs[0]].head] else {
                continue;
            };
            if a == q
                || !rs
                    .iter()
                    .all(|&r| kinds[self.links[r].head] == Some((true, Some(a))))
            {
                continue;
            }
            let f = if q == 0 { 1 } else { 0 };
            let lift = |i| match &fixed {
                None => Value::Int(i),
                Some((_, values)) => {
                    let mut xs = values.clone();
                    xs[0] = Value::Int(i);
                    Value::tuple(xs)
                }
            };
            let mut items = vec![lift(f); p];
            items[0] = lift(a);
            items[p - 1] = lift(q);
            return Some((items, self.es[ce].first()?.clone()));
        }
        None
    }

    fn pick(&mut self, h: usize) -> Option<Value> {
        self.classes(h, Vec::new())
            .list
            .first()
            .map(|c| c.v.clone())
    }

    /// Whether the link `x` alone holds a value, and its list: the chain walked until a bare
    /// atom, a link with no tuple type, or a repeat, each link's answer kept. `None` when a
    /// head has no value [`pick`] makes.
    fn walk(&mut self, x: usize) -> Option<Option<(Vec<Value>, Arc<str>)>> {
        if self.walked.len() < self.links.len() {
            self.walked.resize(self.links.len(), None);
        }
        let mut path = Vec::new();
        let mut on_path = BTreeSet::new();
        let mut y = x;
        let end = loop {
            if let Some(w) = &self.walked[y] {
                break w.is_some();
            }
            if !on_path.insert(y) {
                break false;
            }
            let l = &self.links[y];
            if let Some(a) = self.es[l.e].iter().next() {
                self.walked[y] = Some(Some(Step::End(a.clone())));
                break true;
            }
            if l.head == NONE {
                self.walked[y] = Some(None);
                break false;
            }
            path.push(y);
            y = l.tail;
        };
        for &p in path.iter().rev() {
            let (head, tail) = (self.links[p].head, self.links[p].tail);
            self.walked[p] = Some(match end {
                true => Some(Step::Item(self.pick(head)?, tail)),
                false => None,
            });
        }
        if !end {
            return Some(None);
        }
        let mut items = Vec::new();
        let mut y = x;
        loop {
            match &self.walked[y] {
                Some(Some(Step::End(a))) => return Some(Some((items, a.clone()))),
                Some(Some(Step::Item(v, next))) => {
                    items.push(v.clone());
                    y = *next;
                }
                _ => unreachable!("a walk that ends is kept on its path"),
            }
        }
    }

    /// Whether the link `x` of `plain` holds the list of `items` ending in the bare atom `last`,
    /// by the links' equations alone: one step per run, the heads of a run tested at once by the
    /// first index of the run whose item is not in the head ([`Sweep::first_miss`]).
    fn holds(&mut self, pl: &Plain, x: usize, items: &[Value], last: &Arc<str>) -> bool {
        let (mut x, mut d) = (x, 0usize);
        loop {
            if pl.min_len[x] > items.len() - d {
                return false;
            }
            let k = pl.min_len[x];
            if k > 0
                && pl.required[x] != NONE
                && !self.heads[pl.required[x]].contains(&items[d + k - 1])
            {
                return false;
            }
            let ((e, head, sides), run, jump) = (pl.label[x], pl.run[x], pl.jump[x]);
            if d == items.len() {
                return self.es[e].contains(last);
            }
            if head == NONE {
                return false;
            }
            let reach = d.saturating_add(run);
            let to = reach.min(items.len());
            let miss = self.first_miss(head, d, to, items);
            if sides != NONE {
                // A side row taken at an index `i` of the run, up to the first item the head
                // misses: the item in its head and the rest of the list in its tail.
                let upto = (miss + 1).min(to);
                for &(h, z) in &pl.side_rows[x] {
                    if self.first_good(pl, (h, z), d, upto, items, last) < upto {
                        return true;
                    }
                }
            }
            if miss < to {
                return false;
            }
            if reach > items.len() {
                return self.es[e].contains(last);
            }
            (x, d) = (jump, reach);
        }
    }

    /// The first index `i` in `from..to` at which the side row `(h, z)` holds the list from `i`:
    /// `h` holds the item and `z` the rest; `to` when there is none. The tail `z` is read
    /// only when its label lasts for ever ([`Plain`]): `z` then holds a list exactly when its
    /// head holds every item and its bare atoms the last; any other tail counts as holding none,
    /// so the check can only fail by it, never pass.
    ///
    /// Complexity tradeoff: the naive version tests each index of each run of side rows,
    /// `Θ(rows · length)` when many rows share a chain of them. Used: per side row, each index
    /// is tested once and points past the stretch it starts, as in [`Sweep::first_miss`].
    /// Given up: nothing; the answer is the same.
    fn first_good(
        &mut self,
        pl: &Plain,
        key: (usize, usize),
        from: usize,
        to: usize,
        items: &[Value],
        last: &Arc<str>,
    ) -> usize {
        let (h, z) = key;
        let (ze, zh, zs) = pl.label[z];
        let lasting = pl.run[z] == NONE && zs == NONE;
        let mut i = from;
        let mut path = Vec::new();
        while i < to {
            match self.goods.get(&(key, i)) {
                Some(&j) if j == i => break,
                Some(&j) => {
                    path.push(i);
                    i = j;
                }
                None => {
                    let rest = lasting
                        && self.es[ze].contains(last)
                        && (zh == NONE && i + 1 == items.len()
                            || zh != NONE
                                && self.first_miss(zh, i + 1, items.len(), items) == items.len());
                    if rest && self.heads[h].contains(&items[i]) {
                        self.goods.insert((key, i), i);
                        break;
                    }
                    path.push(i);
                    i += 1;
                }
            }
        }
        for p in path {
            self.goods.insert((key, p), i);
        }
        i.min(to)
    }

    /// The first index in `from..to` whose item the head `h` does not hold, or `to`.
    ///
    /// Complexity tradeoff: the naive version tests each item of the run, `Θ(rows · length)`
    /// over the rows of the front family, which share one chain. Used: per head, each index
    /// is tested once, and an index known held points to the end of the held stretch it
    /// starts (path compression), so a head costs the indices of the runs that read it, not
    /// the runs times their length. Given up: nothing; the answer is the same.
    fn first_miss(&mut self, h: usize, from: usize, to: usize, items: &[Value]) -> usize {
        let mut i = from;
        let mut path = Vec::new();
        while i < to {
            match self.misses.get(&(h, i)) {
                Some(&j) if j == i => break,
                Some(&j) => {
                    path.push(i);
                    i = j;
                }
                None if self.heads[h].contains(&items[i]) => {
                    path.push(i);
                    i += 1;
                }
                None => {
                    self.misses.insert((h, i), i);
                    break;
                }
            }
        }
        // Every index on the path starts a held stretch reaching `i`.
        for p in path {
            self.misses.insert((h, p), i);
        }
        i.min(to)
    }

    /// Whether `t`, whose own rows are the links `roots` of `plain` (each with whether it is
    /// taken), holds the list of `items` ending in `last`.
    fn check(
        &mut self,
        pl: &Plain,
        roots: &[(usize, bool)],
        items: &[Value],
        last: &Arc<str>,
    ) -> bool {
        self.misses.clear();
        self.goods.clear();
        if let Some(c) = &self.carrier
            && !items.iter().all(|v| c.contains(v))
        {
            return false;
        }
        roots
            .iter()
            .all(|&(x, taken)| self.holds(pl, x, items, last) == taken)
    }

    /// The union of the heads `hs` (sorted, two or more), kept for each set, built by halves so
    /// that `k` heads of `s` literals in all cost O(s log k), not O(s k).
    fn join(&mut self, hs: Vec<usize>) -> usize {
        if let Some(&m) = self.joins.get(&hs) {
            return m;
        }
        let mut level: Vec<Type> = hs.iter().map(|&g| self.heads[g].clone()).collect();
        while level.len() > 1 {
            level = level
                .chunks(2)
                .map(|c| {
                    if c.len() == 2 {
                        &c[0] | &c[1]
                    } else {
                        c[0].clone()
                    }
                })
                .collect();
        }
        let m = self.head_id(&level[0]);
        self.joins.insert(hs, m);
        m
    }

    /// The meet of the heads `hs`, kept for each set.
    fn meet(&mut self, hs: Vec<usize>) -> usize {
        if let Some(&m) = self.meets.get(&hs) {
            return m;
        }
        let mut h = self.heads[hs[0]].clone();
        for &g in &hs[1..] {
            h = &h & &self.heads[g];
        }
        let m = self.head_id(&h);
        self.meets.insert(hs, m);
        m
    }
}

/// The links as read from `t`'s types, before [`Sweep::merge`], each with the steps its label
/// (bare atoms, head) lasts along its tails, `NONE` for ever, and the link reached then: what
/// [`Sweep::check`] reads, so that a list it finds in `t` rests on `t`'s rows and the types
/// they reach, not on the merge, the threads or the classes.
struct Plain {
    label: Vec<(usize, usize, usize)>,
    run: Vec<usize>,
    jump: Vec<usize>,
    side_rows: Vec<Vec<(usize, usize)>>,
    min_len: Vec<usize>,
    required: Vec<usize>,
}

impl Plain {
    /// From the links as numbered, each walked once from a stack: a link lasts one step more
    /// than its tail when the tail has its label; a link whose tail walk returns to it with one
    /// label lasts for ever. O(links).
    fn new(links: &[Link], es: &[BTreeSet<Arc<str>>]) -> Plain {
        let n = links.len();
        let label: Vec<(usize, usize, usize)> =
            links.iter().map(|l| (l.e, l.head, l.sides)).collect();
        let tail: Vec<usize> = links.iter().map(|l| l.tail).collect();
        let (mut run, mut jump) = (vec![NONE; n], (0..n).collect::<Vec<_>>());
        let mut state = vec![0u8; n]; // 0 new, 1 on this walk, 2 done
        for x in 0..n {
            let mut path = Vec::new();
            let mut y = x;
            while state[y] == 0 {
                state[y] = 1;
                path.push(y);
                let t = tail[y];
                if label[y].1 == NONE {
                    (run[y], jump[y]) = (NONE, y);
                } else if label[t] != label[y] {
                    (run[y], jump[y]) = (1, t);
                } else {
                    y = t;
                    continue;
                }
                path.pop();
                state[y] = 2;
                break;
            }
            if state[y] == 1 {
                // A cycle of one label, from `y` to the end of the path: it holds for ever.
                let at = path.iter().position(|&p| p == y).expect("on this walk");
                for &p in &path[at..] {
                    (run[p], jump[p], state[p]) = (NONE, p, 2);
                }
                path.truncate(at);
            }
            for &p in path.iter().rev() {
                let t = tail[p];
                run[p] = if run[t] == NONE { NONE } else { run[t] + 1 };
                jump[p] = if run[t] == NONE { p } else { jump[t] };
                state[p] = 2;
            }
        }
        // Complexity tradeoff: scanning a shared no-stop prefix for each candidate
        // suffix costs O(rows * length). Its minimum length is a functional-DAG dynamic
        // program, O(links) time/space. For a side row use the conservative bound zero;
        // this is only an early rejection, never a membership proof.
        let mut min_len = vec![NONE; n];
        let mut required = vec![NONE; n];
        let mut state = vec![0u8; n];
        for x in 0..n {
            let mut path = Vec::new();
            let mut y = x;
            while state[y] == 0 {
                state[y] = 1;
                if !es[links[y].e].is_empty() || links[y].sides != NONE {
                    min_len[y] = 0;
                    state[y] = 2;
                    break;
                }
                if links[y].head == NONE {
                    state[y] = 2;
                    break;
                }
                path.push(y);
                y = links[y].tail;
            }
            if state[y] == 1 {
                // No bare atom on this cycle: all cycle states have infinite minimum.
                let at = path.iter().position(|&z| z == y).expect("on walk");
                for &z in &path[at..] {
                    state[z] = 2;
                }
                path.truncate(at);
            }
            for &z in path.iter().rev() {
                let t = links[z].tail;
                min_len[z] = min_len[t].saturating_add(1);
                required[z] = if min_len[t] == 0 {
                    links[z].head
                } else {
                    required[t]
                };
                state[z] = 2;
            }
        }
        let side_rows = links.iter().map(|l| l.side_rows.clone()).collect();
        Plain {
            label,
            run,
            jump,
            side_rows,
            min_len,
            required,
        }
    }
}

/// One step of a walk: an item and the link after it, or the bare atom that ends the list.
#[derive(Clone)]
enum Step {
    Item(Value, usize),
    End(Arc<str>),
}

/// The threads: each at a link, taken or not, alive or not; by kind; their events by depth.
/// A thread placed at a link where a live thread of the same sign already is, at the start of
/// its run or in its middle, ends there, since the two are the same from then on (links are
/// merged, [`Sweep::merge`]): so at most one live thread of each sign is at a link.
/// [`Threads::key`]: sign, the depth a run ends, the jump, the signature.
type Key = (bool, usize, usize, Sig);

#[derive(Default)]
struct Threads {
    at: Vec<usize>,
    /// The depth at which each thread was placed at its link.
    since: Vec<usize>,
    taken: Vec<bool>,
    alive: Vec<bool>,
    kinds: BTreeMap<(bool, Sig), BTreeSet<usize>>,
    events: BTreeSet<(usize, usize)>,
    /// The live threads by [`Threads::key`]: where each is, at every depth of its run.
    by_key: HashMap<Key, usize>,
    /// Live threads at links on no cycle.
    acyclic: usize,
    /// Live taken threads at links all of whose lists are lists of `Z` ([`Sweep::subs`]).
    sub_taken: usize,
}

impl Threads {
    fn start(&mut self, sw: &Sweep, x: usize, taken: bool) {
        self.at.push(x);
        self.since.push(0);
        self.taken.push(taken);
        self.alive.push(true);
        self.place(sw, self.at.len() - 1, x, 0);
    }

    /// Where a thread of sign `s` at link `y` at `depth` is, the same at every depth of its run:
    /// the depth its run ends, its jump and its signature. Two links with one signature and one
    /// jump at one distance from it are one link (the links between are pairwise of one label
    /// and one merged tail, from the jump back, [`Sweep::merge`]), so the key names the link
    /// the thread is at at each depth of the run. A link that holds a thread for ever is named
    /// by itself.
    fn key(sw: &Sweep, s: bool, y: usize, depth: usize) -> Key {
        match sw.links[y].run {
            NONE => (s, NONE, y, sw.sig(y)),
            r => (s, depth + r, sw.links[y].jump, sw.sig(y)),
        }
    }

    /// The live thread of sign `s` at link `y` at `depth`, placed there or passing it.
    fn at_link(&self, sw: &Sweep, s: bool, y: usize, depth: usize) -> Option<usize> {
        let j = *self.by_key.get(&Self::key(sw, s, y, depth))?;
        self.alive[j].then_some(j)
    }

    fn place(&mut self, sw: &Sweep, i: usize, y: usize, depth: usize) {
        let s = self.taken[i];
        if self.at_link(sw, s, y, depth).is_some_and(|j| j != i) {
            self.alive[i] = false;
            return;
        }
        self.by_key.insert(Self::key(sw, s, y, depth), i);
        self.at[i] = y;
        self.since[i] = depth;
        self.kinds.entry((s, sw.sig(y))).or_default().insert(i);
        self.acyclic += usize::from(!sw.links[y].cyclic);
        self.sub_taken += usize::from(s && sw.sub[y]);
        if sw.links[y].run != NONE {
            self.events.insert((depth + sw.links[y].run, i));
        }
    }

    fn leave(&mut self, sw: &Sweep, i: usize) {
        let x = self.at[i];
        let key = Self::key(sw, self.taken[i], x, self.since[i]);
        if self.by_key.get(&key) == Some(&i) {
            self.by_key.remove(&key);
        }
        let k = (self.taken[i], sw.sig(x));
        if let Some(set) = self.kinds.get_mut(&k) {
            set.remove(&i);
            if set.is_empty() {
                self.kinds.remove(&k);
            }
        }
        self.acyclic -= usize::from(!sw.links[x].cyclic);
        self.sub_taken -= usize::from(self.taken[i] && sw.sub[x]);
    }

    /// The link thread `i` is at at `depth`, stepped from the start of its run.
    fn current(&self, sw: &Sweep, i: usize, depth: usize) -> usize {
        let mut x = self.at[i];
        for _ in self.since[i]..depth {
            x = sw.links[x].tail;
        }
        x
    }

    /// The link thread `i` is at at `depth + 1`: the same signature, so the same bare atoms,
    /// unless its run ends then.
    fn next(&self, sw: &Sweep, i: usize, depth: usize) -> usize {
        let (x, l) = (self.at[i], &sw.links[self.at[i]]);
        match l.run {
            r if r != NONE && self.since[i] + r == depth + 1 => l.jump,
            _ => x,
        }
    }

    /// The one live taken thread, when there is one.
    fn one_taken(&self) -> Option<usize> {
        let mut it = self.kinds.range((true, (0, 0, 0, 0))..);
        match (it.next(), it.next()) {
            (Some((_, set)), None) if set.len() == 1 => set.iter().next().copied(),
            _ => None,
        }
    }
}

/// The verdict of `t` by the front sweep, when `t` is in its class and the sweep closes it;
/// `None` otherwise, for the search to decide. An `Inhabited` is given only with a list that
/// [`Sweep::check`] finds in `t`. A product of types (one tuple type, nothing taken out of it)
/// is empty when one component is and inhabited when every one is, each by the sweep: the
/// tuple of the components' checked values is in the product.
pub(super) fn front_sweep(t: &Type) -> Option<Verdict> {
    match product(&t.p()) {
        None => list_sweep(t),
        Some(items) => {
            let mut values = Vec::new();
            let mut all = true;
            // Complexity tradeoff: sweeping each occurrence of a shared list type
            // rebuilt n size-n lists for n identical fields, Theta(n²) work and
            // space. Memoize each distinct component's result within this product:
            // one sweep per distinct type plus O(fields) shared Value clones.
            // Independent checking below still verifies the actual tuple.
            let mut built: ByType<(Option<Verdict>, Option<Value>)> = ByType::default();
            for item in &items {
                let (verdict, value) = built.entry(item.clone()).or_insert_with(|| {
                    let mut value = None;
                    let verdict = list_sweep_value(item, &mut value);
                    (verdict, value)
                });
                match *verdict {
                    Some(Verdict::Empty) => return Some(Verdict::Empty),
                    Some(Verdict::Inhabited) => values.push(value.as_ref()?.clone()),
                    _ => all = false,
                }
            }
            if !all {
                return None;
            }
            let value = Value::tuple(values);
            // Check the actual outer arity and each actual child against a fresh reader.
            // Complexity tradeoff: generic membership may unfold each excluded list
            // prefix repeatedly (quadratic). The fresh Plain checker shares runs and
            // required-terminal/length facts, O(N log N) on the accepted probe class;
            // memory O(N). No sweep classes or search membership facts are consulted.
            check_actual(t, &value).then_some(Verdict::Inhabited)
        }
    }
}

/// Of two classes or more open at one depth, one whose negative heads holding its value are
/// among those of every other open class, when there is one. On a class (inside the meet of the
/// taken heads) the taken threads all go on to their next links, and a negative unit goes on
/// exactly when its head holds the class's value; the lists left are those of the taken next
/// links less those of the negative ones, fewer as more negative units go on. So what is left
/// after any other open class is inside what is left after this one: it is empty when this
/// one's is, and a list after this one is a value. The class's heads are `cof Δ delta` when
/// `flip`, else `delta` ([`Class`]).
///
/// Complexity tradeoff: the naive version builds every open class's set of heads and compares
/// each pair, O(open² · heads). Used: the class with fewest heads is the only candidate, and its
/// heads are compared with another class's through that class's `delta` alone, by counts
/// against the candidate's `delta` split by `cof`: O((|cof| + Σ |delta|) log) per depth, the
/// order of reading the classes there. Given up: a class below every other is not looked for
/// when the fewest heads are shared by classes with different heads, which then fails anyway.
fn dominant(classes: &ClassSet, open: &[usize]) -> Option<usize> {
    let cof = &classes.cof;
    let flip = |c: &Class| c.flip && !cof.is_empty();
    let size = |c: &Class| match flip(c) {
        true => {
            let inside = c.delta.iter().filter(|g| cof.contains(*g)).count();
            cof.len() + (c.delta.len() - inside) - inside
        }
        false => c.delta.len(),
    };
    let ai = *open.iter().min_by_key(|&&ci| size(&classes.list[ci]))?;
    let a = &classes.list[ai];
    let (a_cof, a_out): (BTreeSet<usize>, BTreeSet<usize>) =
        a.delta.iter().partition(|g| cof.contains(*g));
    let below = |b: &Class| -> bool {
        let b_cof = b.delta.iter().filter(|g| cof.contains(*g));
        let b_out = b.delta.iter().filter(|g| !cof.contains(*g));
        // `a_out` (heads holding a's value outside `cof`) must be heads of b in every case.
        let out_ok = b_out.clone().filter(|g| a_out.contains(*g)).count() == a_out.len();
        match (flip(a), flip(b)) {
            // cof \ a.delta ⊆ cof \ b.delta, and a's other heads among b's.
            (true, true) => b_cof.clone().all(|g| a_cof.contains(g)) && out_ok,
            // cof \ a.delta ⊆ b.delta: every cofinite head is in a.delta or b.delta.
            (true, false) => {
                let both = b_cof.clone().filter(|g| a_cof.contains(*g)).count();
                out_ok && a_cof.len() + b_cof.count() - both == cof.len()
            }
            // a.delta ⊆ cof Δ b.delta: no cofinite head of a.delta in b.delta.
            (false, true) => out_ok && !b_cof.clone().any(|g| a_cof.contains(g)),
            (false, false) => out_ok && b_cof.filter(|g| a_cof.contains(*g)).count() == a_cof.len(),
        }
    };
    (open.iter())
        .filter(|&&ci| ci != ai)
        .all(|&ci| below(&classes.list[ci]))
        .then_some(ai)
}

fn check_actual(t: &Type, value: &Value) -> bool {
    let Some(items) = product(&t.p()) else {
        return check_list_value(t, value);
    };
    let Value::Tuple(xs) = value else {
        return false;
    };
    // Complexity tradeoff: the independent checker formerly parsed the same list
    // once per tuple position, Theta(fields * list_size). A shared sequence ID
    // identifies the actual immutable Value, so each (type, shared value) pair
    // needs one fresh check. No sweep result or membership assertion is trusted;
    // unshared values are checked separately. O(distinct checks + fields) space/time
    // in addition to the list checks, with expected O(1) visited lookups.
    let mut checked = std::collections::HashSet::new();
    xs.len() == items.len()
        && items.iter().zip(xs.iter()).all(|(t, v)| {
            if let Some(id) = v.shared_parts()
                && !checked.insert((t.clone(), id))
            {
                return true;
            }
            check_list_value(t, v)
        })
}

fn check_list_value(t: &Type, value: &Value) -> bool {
    let mut sw: Sweep = Sweep::default();
    let Some((root_e, Some(((taken, refused), false)))) = shape(&t.p(), &mut sw.c) else {
        return false;
    };
    let root_e = sw.e_id(root_e);
    let none = sw.e_id(BTreeSet::new());
    let mut roots = Vec::new();
    for (rs, e, sign) in [(&taken, root_e, true), (&refused, none, false)] {
        for r in rs {
            let Some(x) = sw.row(r, e) else {
                return false;
            };
            roots.push((x, sign));
        }
    }
    let Some(c) = sw.c.clone() else {
        return false;
    };
    let mut items = Vec::new();
    let mut v = value;
    let last = loop {
        let Value::Atom(a) = v else {
            return false;
        };
        if !a.fields.is_empty() {
            return false;
        }
        if a.args.is_empty() {
            break a.name.clone();
        }
        if a.name != c || a.args.len() != 2 {
            return false;
        }
        items.push(a.args[0].clone());
        v = &a.args[1];
    };
    let plain = Plain::new(&sw.links, &sw.es);
    sw.check(&plain, &roots, &items, &last)
}

fn build_list(c: &Arc<str>, items: Vec<Value>, last: &Arc<str>) -> Value {
    items
        .into_iter()
        .rev()
        .fold(Value::atom(last), |tail, item| {
            Value::atom_with(c.clone(), vec![item, tail])
        })
}

/// The components of `p` when it is one tuple type and nothing else.
fn product(p: &Parts) -> Option<Vec<Type>> {
    if p.has_scalars()
        || !p.atoms.is_default()
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
        || p.tuples.rest
        || p.tuples.lens.len() != 1
    {
        return None;
    }
    let (_, part) = p.tuples.lens.iter().next()?;
    let (taken, refused) = part.clause()?;
    match (&taken[..], &refused[..]) {
        ([row], []) => Some(row.iter().cloned().collect()),
        _ => None,
    }
}

/// [`front_sweep`] on a type of lists.
fn list_sweep(t: &Type) -> Option<Verdict> {
    let mut actual = None;
    let verdict = list_sweep_value(t, &mut actual)?;
    if verdict == Verdict::Inhabited && !check_actual(t, &actual?) {
        return None;
    }
    Some(verdict)
}

/// [`list_sweep`] with its value: `Some(None)` when `t` is empty, `Some(Some(v))` when `t` holds
/// `v`, checked against `t` by a fresh reader, and `None` outside the sweep's class or when the
/// sweep refuses (the search then decides `t`).
pub(super) fn list_sweep_checked(t: &Type) -> Option<Option<Value>> {
    let mut actual = None;
    match list_sweep_value(t, &mut actual)? {
        Verdict::Empty => Some(None),
        Verdict::Inhabited => {
            let v = actual?;
            check_actual(t, &v).then_some(Some(v))
        }
        Verdict::Refused(_) => None,
    }
}

fn list_sweep_value(t: &Type, actual: &mut Option<Value>) -> Option<Verdict> {
    // A type with no payload name, as a set of failure atoms, has no clause: it is left before
    // `shape` reads its names, which costs O(names log names) for every type asked.
    if t.p().atoms.payloads.len() != 1 {
        return None;
    }
    let mut sw: Sweep = Sweep::default();
    let (root_e, clause) = shape(&t.p(), &mut sw.c)?;
    let ((taken, refused), union) = clause?;
    if union || taken.is_empty() {
        return None;
    }
    // The carrier head: a taken row `(h, X)` with `X` of the one row `(h, X)` puts every item in
    // `h`. All such rows are met, so the result does not depend on their order. O(rows).
    for r in &taken {
        if let Some((_, Some(((xt, xr), false)))) = shape(&r[1].p(), &mut sw.c)
            && xr.is_empty()
            && let [x] = &xt[..]
            && x[0] == r[0]
            && x[1] == r[1]
        {
            sw.carrier = Some(match sw.carrier.take() {
                None => r[0].clone(),
                Some(c) => &c & &r[0],
            });
        }
    }
    let root_e = sw.e_id(root_e);
    let none = sw.e_id(BTreeSet::new());
    let mut roots = Vec::new();
    for r in &taken {
        roots.push((sw.row(r, root_e)?, true));
    }
    for r in &refused {
        roots.push((sw.row(r, none)?, false));
    }
    let plain = Plain::new(&sw.links, &sw.es);
    let plain_roots = roots.clone();
    // Complexity tradeoff: testing every pair of refused roots for inclusion costs O(R²).
    // Equal-tail rows are exactly one row with their heads joined. Index tails, then use
    // balanced unions: O((R + total head size) log R), retaining Plain's original rows for
    // the independent check. This removes redundant partial roots before bounded().
    let mut by_tail: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut normalized = Vec::new();
    for &(x, taken) in &roots {
        if taken {
            normalized.push((x, true));
        } else {
            by_tail.entry(sw.links[x].tail).or_default().push(x);
        }
    }
    for xs in by_tail.values() {
        let hs: BTreeSet<_> = xs.iter().map(|&x| sw.links[x].head).collect();
        let h = if hs.len() == 1 {
            *hs.first()?
        } else {
            sw.join(hs.into_iter().collect())
        };
        let x = xs[0];
        sw.links[x].head = h;
        normalized.push((x, false));
    }
    roots = normalized;
    let rep = sw.merge();
    for r in &mut roots {
        r.0 = rep[r.0];
    }
    sw.rep = rep;
    sw.runs()?;
    if let Some((items, last)) = sw.short_escape(&roots)
        && sw.check(&plain, &plain_roots, &items, &last)
    {
        *actual = Some(build_list(sw.c.as_ref()?, items, &last));
        return Some(Verdict::Inhabited);
    }
    if !sw.bounded(&roots.iter().map(|r| r.0).collect::<Vec<_>>()) {
        return None;
    }
    sw.subs();
    // A link with side rows is read as a union of threads, which only a refused thread is: a
    // taken thread that reaches one puts `t` outside the class. One walk, O(links).
    let mut seen = BTreeSet::new();
    for &(x, _) in roots.iter().filter(|r| r.1) {
        let mut y = x;
        while y != NONE && seen.insert(y) {
            if sw.links[y].sides != NONE {
                return None;
            }
            y = sw.links[y].tail;
        }
    }
    let mut witness = |sw: &mut Sweep, items: Vec<Value>, last: Arc<str>| -> Option<Verdict> {
        if !sw.check(&plain, &plain_roots, &items, &last) {
            return None;
        }
        *actual = Some(build_list(sw.c.as_ref()?, items, &last));
        Some(Verdict::Inhabited)
    };
    let mut th = Threads::default();
    for &(x, taken) in &roots {
        th.start(&sw, x, taken);
    }
    let mut prefix: Vec<Value> = Vec::new();
    let mut depth = 0usize;
    loop {
        // The threads whose signature ends here move; placed after all have left, so a thread
        // ends only on a link another holds at this depth.
        let mut moved = Vec::new();
        while let Some(&(d, i)) = th.events.first() {
            if d != depth {
                break;
            }
            th.events.pop_first();
            if th.alive[i] {
                th.leave(&sw, i);
                moved.push((i, sw.links[th.at[i]].jump));
            }
        }
        for (i, y) in moved {
            th.place(&sw, i, y, depth);
        }
        let pos: Vec<Sig> = (th.kinds.keys()).filter(|k| k.0).map(|k| k.1).collect();
        let neg: Vec<Sig> = (th.kinds.keys()).filter(|k| !k.0).map(|k| k.1).collect();
        // Bare atoms at this depth.
        let mut e: BTreeSet<Arc<str>> = sw.es[pos[0].0].clone();
        for k in &pos[1..] {
            e.retain(|a| sw.es[k.0].contains(a));
        }
        for k in &neg {
            e.retain(|a| !sw.es[k.0].contains(a));
        }
        if let Some(a) = e.into_iter().next() {
            return witness(&mut sw, prefix, a);
        }
        // A taken link with no tuple type holds nothing more.
        if pos.iter().any(|k| k.1 == NONE) {
            return Some(Verdict::Empty);
        }
        if neg.is_empty() {
            let x = th.current(&sw, th.one_taken()?, depth);
            return match sw.walk(x)? {
                None => Some(Verdict::Empty),
                Some((items, last)) => witness(&mut sw, [prefix, items].concat(), last),
            };
        }
        if th.acyclic == 0 {
            // Every thread on a cycle: the states repeat, which the sweep does not close.
            return None;
        }
        let pos_heads: BTreeSet<usize> = pos.iter().map(|k| k.1).collect();
        let head = sw.meet(pos_heads.into_iter().collect());
        let mut pos_tails: BTreeSet<usize> =
            pos.iter().map(|k| k.2).filter(|&y| y != NONE).collect();
        // A negative unit whose tail is `Z` closes its classes too when a taken thread is at a
        // link all of whose lists are `Z`'s: the lists left after this depth are in the next
        // link of that thread, so in `Z`, which the unit takes out on its head.
        if let Some(z) = sw.z
            && th.sub_taken > 0
        {
            pos_tails.insert(z);
        }
        // Negative threads that reach one link at the next depth from links of different heads
        // are one there, so on a class they count as one thread whose head is the union of
        // theirs: what the next state holds depends only on which links it reaches. Of two
        // threads reaching one link from links of different heads, one ends its run here (two
        // in the middle of their runs share the link's head), so they are the events of the
        // next depth and the live thread passing each one's landing link then, found by its key
        // in O(log) ([`Threads::at_link`]). A kind all of whose threads are in such groups is
        // read through the groups only.
        let mut landing: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for &(_, i) in th.events.range((depth + 1, 0)..(depth + 2, 0)) {
            if th.alive[i] && !th.taken[i] && sw.links[th.at[i]].head != NONE {
                landing.entry(sw.links[th.at[i]].jump).or_default().push(i);
            }
        }
        for (&y, ts) in &mut landing {
            if let Some(j) = th.at_link(&sw, false, y, depth + 1)
                && sw.links[th.at[j]].head != NONE
                && !ts.contains(&j)
            {
                ts.push(j);
            }
        }
        landing.retain(|_, ts| ts.len() > 1);
        let mut merged: BTreeMap<Sig, usize> = BTreeMap::new();
        let mut groups: Vec<(usize, usize, Vec<usize>)> = Vec::new();
        for (y, ts) in landing {
            let hs: BTreeSet<usize> = ts.iter().map(|&i| sw.links[th.at[i]].head).collect();
            for &i in &ts {
                *merged.entry(sw.sig(th.at[i])).or_default() += 1;
            }
            let h = match hs.len() {
                1 => *hs.first().expect("one head"),
                _ => sw.join(hs.into_iter().collect()),
            };
            groups.push((h, y, ts));
        }
        let kept: Vec<Sig> = (neg.iter())
            .filter(|k| k.1 != NONE)
            .filter(|k| merged.get(*k).copied().unwrap_or(0) < th.kinds[&(false, **k)].len())
            .copied()
            .collect();
        // Per negative head, its kinds and groups and those of them whose tail is a taken
        // thread's; a class is read as the heads that hold it, so in the size of its `delta`
        // past the cofinite heads' sum.
        // The side rows of the negative kinds, one unit per kind and side row: each reaches a
        // link that is its own tail.
        let side_units: Vec<(usize, usize)> = (neg.iter())
            .filter(|k| k.3 != NONE)
            .flat_map(|k| sw.sides[k.3].iter().map(|&(h, z)| (h, sw.rep[z])))
            .collect();
        let mut per_head: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
        let units = (kept.iter().map(|k| (k.1, k.2)))
            .chain(groups.iter().map(|g| (g.0, g.1)))
            .chain(side_units.iter().copied());
        for (h, y) in units {
            let c = per_head.entry(h).or_default();
            c.0 += 1;
            c.1 += usize::from(pos_tails.contains(&y));
        }
        let classes = sw.classes(head, per_head.keys().copied().collect());
        let mut base = (0usize, 0usize);
        for g in &classes.cof {
            if let Some(c) = per_head.get(g) {
                base = (base.0 + c.0, base.1 + c.1);
            }
        }
        let mut open = Vec::new();
        for (ci, c) in classes.list.iter().enumerate() {
            // The negative kinds on the class, and those closing it.
            let (mut on, mut closing) = if c.flip { base } else { (0, 0) };
            for g in &c.delta {
                let (n, m) = per_head.get(g).copied().unwrap_or_default();
                if c.flip && classes.cof.contains(g) {
                    (on, closing) = (on - n, closing - m);
                } else {
                    (on, closing) = (on + n, closing + m);
                }
            }
            if on == 0 {
                // The class holds what the one taken tail holds; when that is empty, so is every
                // class, all being in it.
                let x = th.current(&sw, th.one_taken()?, depth);
                let tail = sw.links[x].tail;
                let v = c.v.clone();
                return match sw.walk(tail)? {
                    None => Some(Verdict::Empty),
                    Some((items, last)) => {
                        witness(&mut sw, [prefix, vec![v], items].concat(), last)
                    }
                };
            } else if closing == 0 {
                open.push(ci);
            }
        }
        let ci = match open[..] {
            [] => return Some(Verdict::Empty),
            [ci] => ci,
            _ => match dominant(&classes, &open) {
                Some(ci) => ci,
                None => {
                    // Two classes or more open: one whose next state has a bare atom that no
                    // negative thread on it has gives a list that ends there; else the search
                    // decides. Read at most once per sweep, which ends here either way.
                    // Complexity tradeoff: the naive version reads every thread for each open
                    // class, O(open · threads). Used: per negative head, the count of its threads
                    // having each atom of the taken threads' next bare atoms, so a class costs the
                    // atoms its `delta` touches; O(threads · |e| + Σ |delta|) log. Given up: nothing.
                    let mut e: Option<BTreeSet<Arc<str>>> = None;
                    for (_, set) in th.kinds.range((true, (0, 0, 0, 0))..) {
                        for &i in set {
                            let ne = &sw.es[sw.links[th.next(&sw, i, depth)].e];
                            e = Some(match e {
                                None => ne.clone(),
                                Some(s) => s.intersection(ne).cloned().collect(),
                            });
                        }
                    }
                    let e = e.unwrap_or_default();
                    let mut by_head: BTreeMap<usize, BTreeMap<Arc<str>, usize>> = BTreeMap::new();
                    let kinds = (th.kinds.range(..(true, (0, 0, 0, 0))))
                        .filter(|(k, _)| k.1.1 != NONE)
                        .flat_map(|(k, set)| set.iter().map(move |&i| (k.1.1, i)));
                    let grouped = (groups.iter()).flat_map(|g| g.2.iter().map(move |&i| (g.0, i)));
                    for (h, i) in kinds.chain(grouped) {
                        let ne = &sw.es[sw.links[th.next(&sw, i, depth)].e];
                        for a in ne.intersection(&e) {
                            *by_head.entry(h).or_default().entry(a.clone()).or_default() += 1;
                        }
                    }
                    for &(h, z) in &side_units {
                        for a in sw.es[sw.links[z].e].intersection(&e) {
                            *by_head.entry(h).or_default().entry(a.clone()).or_default() += 1;
                        }
                    }
                    let mut base: BTreeMap<Arc<str>, usize> = BTreeMap::new();
                    for g in &classes.cof {
                        for (a, n) in by_head.get(g).into_iter().flatten() {
                            *base.entry(a.clone()).or_default() += n;
                        }
                    }
                    let free: Vec<&Arc<str>> =
                        e.iter().filter(|a| !base.contains_key(*a)).collect();
                    for &ci in &open {
                        let c = &classes.list[ci];
                        let mut adj: BTreeMap<&Arc<str>, isize> = BTreeMap::new();
                        for g in &c.delta {
                            let s = if c.flip && classes.cof.contains(g) {
                                -1
                            } else {
                                1
                            };
                            for (a, n) in by_head.get(g).into_iter().flatten() {
                                *adj.entry(a).or_default() += s * *n as isize;
                            }
                        }
                        let from_base = |a: &Arc<str>| match c.flip {
                            true => base.get(a).copied().unwrap_or(0) as isize,
                            false => 0,
                        };
                        let mut untouched: Box<dyn Iterator<Item = &Arc<str>>> = match c.flip {
                            true => Box::new(free.iter().copied()),
                            false => Box::new(e.iter()),
                        };
                        let a = (adj.iter())
                            .find(|(a, n)| from_base(a) + **n == 0)
                            .map(|(a, _)| (*a).clone())
                            .or_else(|| untouched.find(|a| !adj.contains_key(a)).cloned());
                        if let Some(a) = a {
                            let v = c.v.clone();
                            return witness(&mut sw, [prefix, vec![v]].concat(), a);
                        }
                    }
                    return None;
                }
            },
        };
        let c = &classes.list[ci];
        // A side row on the open class would put a refused thread on its own tail from the next
        // depth, which the sweep does not follow: the search decides.
        if (side_units.iter()).any(|&(h, _)| sw.heads[h].contains(&c.v)) {
            return None;
        }
        // The negative threads whose head misses the class end here: read on the class's value,
        // since a head of a group is not one the classes were cut by (the threads of a group
        // that hold the value reach the group's link, and one does, the union holding it).
        let gone: Vec<Sig> = (neg.into_iter())
            .filter(|k| k.1 == NONE || !sw.heads[k.1].contains(&c.v))
            .collect();
        for k in gone {
            for i in th.kinds.get(&(false, k)).cloned().unwrap_or_default() {
                th.leave(&sw, i);
                th.alive[i] = false;
            }
        }
        prefix.push(c.v.clone());
        depth += 1;
    }
}

#[cfg(test)]
mod r4_checker_tests {
    use super::*;
    #[test]
    fn shared_value_checks_keep_the_type_in_the_key() {
        let ints = Type::atom_with("cons", &Type::tuple(vec![Type::int(), Type::atom("nil")]));
        let bools = Type::atom_with("cons", &Type::tuple(vec![Type::bool(), Type::atom("nil")]));
        let v = Value::atom_with("cons", vec![Value::Int(7), Value::atom("nil")]);
        let same_value = Value::tuple(vec![v.clone(), v.clone()]);
        assert!(check_actual(
            &Type::tuple(vec![ints.clone(), ints.clone()]),
            &same_value
        ));
        assert!(!check_actual(&Type::tuple(vec![ints, bools]), &same_value));
    }

    #[test]
    fn actual_products_and_lists_reject_bad_values() {
        let one = Type::atom_with("cons", &Type::tuple(vec![Type::int(), Type::atom("nil")]));
        let good = Value::atom_with("cons", vec![Value::Int(7), Value::atom("nil")]);
        assert!(check_actual(&one, &good));
        assert!(!check_actual(&one, &Value::atom("nil")));
        assert!(!check_actual(
            &one,
            &Value::atom_with("cons", vec![Value::Bool(true), Value::atom("nil")])
        ));
        assert!(!check_actual(
            &one,
            &Value::atom_with("cons", vec![Value::Int(7)])
        ));
        let product = Type::tuple(vec![one.clone(), one]);
        assert!(check_actual(
            &product,
            &Value::tuple(vec![good.clone(), good.clone()])
        ));
        assert!(!check_actual(&product, &good));
        assert!(!check_actual(&product, &Value::tuple(vec![good.clone()])));
        assert!(!check_actual(
            &product,
            &Value::tuple(vec![good, Value::atom("nil")])
        ));
    }
}
