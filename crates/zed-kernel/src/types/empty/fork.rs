//! The fork stages (PORT-u6-structured-fork, from the Gemini seat's prototype of round 1 of
//! REFUSAL-front-u6-subset, Stages 0 to 2): a list type of integers that the search refused at
//! a fork, `P \ (N_1 | .. | N_r)`, decided where one negative state at a time is enough.
//!
//! The class, read from the type alone. `t` has atoms only: at most a bare stop atom and one
//! link atom whose payload is pairs only, a clause of rows (the taken rows `T_i`, the refused
//! rows `N_k`, and the rest `G`, the payload exactly `T_1 & .. & T_m & G` less `N_1 | .. |
//! N_r`, which holds by `Part::forced`: every value of the payload takes each `T_i` and no
//! `N_k`). `G` is no condition or a union of rows. Every row head is a set of integers (finite,
//! or cofinite within the integers), and from each row tail every type reached is a *state*: a
//! list type `stop? | link(h_1, s_1) | .. | link(h_j, s_j)` with each `h` a set of integers and
//! each `s` a state, one stop name and one link name throughout. A state reads as a state of a
//! nondeterministic automaton over the integers, which accepts where it holds the stop atom.
//!
//! Stage 0 (the positive side). A taken row whose tail is a *carrier* `L = stop | link(H, L)`
//! holds `link(h, L)`, the lists whose first item is in `h` and every later one in `H`: it is
//! absorbed as masks, `C0` (the meet of the `h`) on the first item and `C` (the meet of the `H`)
//! on every later one, which are met with every head read on the positive side. What is left
//! must be one taken row, or the union `G`, or (all taken rows carriers) one carrier row: the
//! positive start `π`. Two positive automata met (a product) are out of the class. The
//! negative start `ν` has the refused rows as its rows.
//!
//! Cells. At a state on each side, the integers split into the cells of the heads of both
//! states' rows: each value written in a head is a cell of its own, and every value written in
//! none is one cell (held exactly by the cofinite heads). Each cell gives the positive and the
//! negative successors; cells with equal successors are one.
//!
//! Stage 1 (exact, unforked). A breadth-first search over pairs `(p, n)` of a positive state
//! and one negative state or none, from `(π, ν)`: a pair with `p` holding the stop and `n`
//! none or not holding it is a list of `t`, built and checked by [`Type::contains`]. A cell
//! with two negative successors or more is a fork: the search does not follow it. With no fork
//! met, no such pair means every list of `P` is in a refused row: `Empty`. Proof: a list of `P`
//! is read by some run `p_0 .. p_l` with `p_l` holding the stop; the negative states reading
//! its first `j` items are one state or none at each `j` (no fork), and the pair `(p_l, n_l)`
//! is reached; it is not a list of `t`, so `n_l` holds the stop and the list is in `N`.
//!
//! Stage 2 (exact `Empty` by a simulation). The largest relation `R` on the pairs `(p, n)`
//! reached from `(π, ν)` such that `p` holding the stop gives `n` holding it, and for each
//! cell and each positive successor `p'`, some negative successor `n'` has `(p', n') ∈ R`. If
//! `(π, ν) ∈ R`, every list of `π` is in `ν`, by induction on its length: `Empty`.
//!
//! Not ported: the prototype's Stage 2b (Stages 1 and 2 on the reversed automata) and Stage 3
//! (the prefix-chain CSP with 2-SAT; the kernel's `escape` module decides a class of that kind
//! before the search). A type outside the class, or that no stage decides, stays refused.
// Complexity tradeoff: the complete decision is the subset construction over the negative
// states, exponential in them (deciding whether a union of list types holds every list of
// another is NFA inclusion, PSPACE-complete); used: Stages 1 and 2 over pairs of one positive
// state and one negative state, at most `|P| * (|N| + 1)` pairs, each pair's cells read once in
// `O(w log w)` for `w` the written size of the two states' heads (values listed in a cofinite
// head times the cofinite heads at the pair), and the simulation's failures spread once along
// each choice that needs them (a counter of the options left per choice, as in unit
// propagation for Horn clauses), linear in the choices made. The pairs are quadratic in the states at worst, and that is needed: a list
// of a positive cycle of `a` states less a negative cycle of `b` states (coprime) has its
// shortest value of length `a * b`, which the answer builds. Given up: a value whose search
// meets a fork on every path, and an `Empty` that needs two negative states at once; both stay
// refused. COMPLEXITY.md K137.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

use super::super::{Parts, Row, Type};
use super::escape::Ints;
use super::shared::{ByType, only_atoms};
use crate::value::Value;

/// The answer of a stage.
pub(super) enum Decided {
    Empty,
    /// A list of the type, checked by [`Type::contains`].
    Inhabited(Value),
}

/// A state: whether it holds the stop atom, and its rows `(head, tail)`.
struct State {
    stop: bool,
    rows: Vec<(Ints, usize)>,
}

/// The states read from the row tails, each type once.
struct Reader {
    states: Vec<State>,
    of: ByType<usize>,
    heads: ByType<Ints>,
    stop: Option<Arc<str>>,
    link: Arc<str>,
}

/// Whether `q`, an atom's payload, holds pairs and nothing else: the pairs part, if so.
fn pairs_only(q: &Parts) -> Option<&super::super::bdd::Part<Row>> {
    if q.structs || q.tuples.rest || q.tuples.lens.len() != 1 || !only_atoms(q) {
        return None;
    }
    if !q.atoms.is_default() {
        return None;
    }
    q.tuples.lens.get(&2)
}

impl Reader {
    fn head(&mut self, t: &Type) -> Option<Ints> {
        if let Some(h) = self.heads.get(t) {
            return Some(h.clone());
        }
        let h = Ints::of(t)?;
        self.heads.insert(t.clone(), h.clone());
        Some(h)
    }

    /// The state of `t`, read with every state after it; `None` outside the class. Each type
    /// is read once, from a stack, so a long list takes no more of the thread's stack than a
    /// short one.
    fn state(&mut self, t: &Type) -> Option<usize> {
        if let Some(&i) = self.of.get(t) {
            return Some(i);
        }
        let first = self.add(t);
        let mut todo = vec![(t.clone(), first)];
        while let Some((t, i)) = todo.pop() {
            let p: &Parts = &t.p();
            if p.structs || p.tuples.rest || !p.tuples.lens.is_empty() || !only_atoms(p) {
                return None;
            }
            if p.atoms.cofinite() {
                return None;
            }
            let mut stop = false;
            for (name, a) in p.atoms.names() {
                if a.bare {
                    if a.payload != Type::empty() {
                        return None;
                    }
                    match &self.stop {
                        None => self.stop = Some(name.clone()),
                        Some(s) if s == name => {}
                        Some(_) => return None,
                    }
                    stop = true;
                    continue;
                }
                if *name != self.link {
                    return None;
                }
                let q = a.payload.p();
                let f = pairs_only(&q)?;
                let rows = match f.is_leaf() {
                    Some(false) => Vec::new(),
                    Some(true) => return None,
                    None => f.union_rows()?,
                };
                for row in rows {
                    let h = self.head(&row[0])?;
                    let s = match self.of.get(&row[1]) {
                        Some(&s) => s,
                        None => {
                            let s = self.add(&row[1]);
                            todo.push((row[1].clone(), s));
                            s
                        }
                    };
                    self.states[i].rows.push((h, s));
                }
            }
            self.states[i].stop = stop;
        }
        Some(first)
    }

    fn add(&mut self, t: &Type) -> usize {
        let i = self.states.len();
        self.states.push(State {
            stop: false,
            rows: Vec::new(),
        });
        self.of.insert(t.clone(), i);
        i
    }

    /// The head of the carrier `stop | link(H, self)`, if `s` is one.
    fn carrier(&self, s: usize) -> Option<&Ints> {
        let st = &self.states[s];
        (st.stop && st.rows.len() == 1 && st.rows[0].1 == s).then(|| &st.rows[0].0)
    }
}

/// One cell: a value in it, and the positive and negative successors, each sorted, no repeats.
type Cell = (Value, Vec<usize>, Vec<usize>);

/// A pair of a positive state and one negative state or none.
type Pair = (usize, Option<usize>);

/// The cells of the positive rows `pos` and the negative rows `neg`, those with a positive
/// successor only.
// Complexity tradeoff: a scan of every integer is no option (the heads are cofinite); a cell for
// each set of heads is exponential in them. Used: one cell per value written in a head and
// one for the rest, `O(w log w)` for `w` the values written plus the values times the cofinite
// heads (each value is tested against each cofinite head), and cells with equal successors
// merged in a map. The prototype's `sparse_dispatch` does the same over symbols.
fn cells(pos: &[(Ints, usize)], neg: &[(Ints, usize)]) -> Vec<Cell> {
    let mut by_value: BTreeMap<&Value, (Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for (side, rows) in [(0, pos), (1, neg)] {
        for (h, s) in rows {
            for v in h.vals.iter() {
                let e = by_value.entry(v).or_default();
                if !h.cof {
                    if side == 0 {
                        e.0.push(*s);
                    } else {
                        e.1.push(*s);
                    }
                }
            }
        }
    }
    let pos_cof: Vec<&(Ints, usize)> = pos.iter().filter(|(h, _)| h.cof).collect();
    let neg_cof: Vec<&(Ints, usize)> = neg.iter().filter(|(h, _)| h.cof).collect();
    let mut out: BTreeMap<(Vec<usize>, Vec<usize>), Value> = BTreeMap::new();
    let mut put = |v: &Value, mut ps: Vec<usize>, mut ns: Vec<usize>| {
        ps.sort_unstable();
        ps.dedup();
        if ps.is_empty() {
            return;
        }
        ns.sort_unstable();
        ns.dedup();
        out.entry((ps, ns)).or_insert_with(|| v.clone());
    };
    for (v, (ps, ns)) in &by_value {
        let mut ps = ps.clone();
        let mut ns = ns.clone();
        ps.extend(
            pos_cof
                .iter()
                .filter(|(h, _)| h.contains(v))
                .map(|(_, s)| *s),
        );
        ns.extend(
            neg_cof
                .iter()
                .filter(|(h, _)| h.contains(v))
                .map(|(_, s)| *s),
        );
        put(v, ps, ns);
    }
    if !pos_cof.is_empty() {
        // A value written in no head: held by every cofinite head and no finite one.
        let other = (0..)
            .map(Value::Int)
            .find(|x| !by_value.contains_key(x))
            .expect("finitely many values are written");
        put(
            &other,
            pos_cof.iter().map(|(_, s)| *s).collect(),
            neg_cof.iter().map(|(_, s)| *s).collect(),
        );
    }
    out.into_iter().map(|((ps, ns), v)| (v, ps, ns)).collect()
}

/// The two automata of a type of the class, with its starts and masks.
struct Fork {
    r: Reader,
    /// The positive start `π` and the negative start `ν`, two states of `r` of their own.
    pi: usize,
    nu: usize,
    /// The mask `C` on every positive item after the first, if a carrier was absorbed.
    later: Option<Ints>,
    /// Each state's rows on the positive side, `C` met with their heads, read once.
    pos: HashMap<usize, Rc<[(Ints, usize)]>>,
}

impl Fork {
    fn pos_rows(&mut self, p: usize) -> Rc<[(Ints, usize)]> {
        if let Some(r) = self.pos.get(&p) {
            return r.clone();
        }
        // `Ints::meet` and `Ints::is_empty` are called by path, and `p` and `union_rows` in
        // `decide` are typed, because the import-graph test (s_01f_import_graph) reads a call
        // whose receiver it cannot type as a call of `TwoSat::meet` or `Type::is_empty`, which
        // are written in empty.rs: an import cycle with empty.rs.
        let rows: Rc<[(Ints, usize)]> = match (&self.later, p == self.pi) {
            (Some(c), false) => self.r.states[p]
                .rows
                .iter()
                .map(|(h, s)| (Ints::meet(h, c), *s))
                .filter(|(h, _)| !Ints::is_empty(h))
                .collect(),
            _ => self.r.states[p].rows.iter().cloned().collect(),
        };
        self.pos.insert(p, rows.clone());
        rows
    }

    fn cells_at(&mut self, p: usize, n: Option<usize>) -> Vec<Cell> {
        let pos = self.pos_rows(p);
        let neg: &[(Ints, usize)] = match n {
            Some(n) => &self.r.states[n].rows,
            None => &[],
        };
        cells(&pos, neg)
    }

    /// Stage 1: `Some` with the answer, or `None` when a fork was met and no list was found.
    fn unforked(&mut self) -> Option<Result<Vec<Value>, ()>> {
        let start = (self.pi, Some(self.nu));
        let mut nodes: Vec<(Pair, Option<(usize, Value)>)> = vec![(start, None)];
        let mut index: HashMap<Pair, usize> = HashMap::from([(start, 0)]);
        let mut forked = false;
        let mut i = 0;
        while i < nodes.len() {
            let (p, n) = nodes[i].0;
            if self.r.states[p].stop && n.is_none_or(|n| !self.r.states[n].stop) {
                let mut items = Vec::new();
                let mut at = i;
                while let Some((parent, v)) = &nodes[at].1 {
                    items.push(v.clone());
                    at = *parent;
                }
                items.reverse();
                return Some(Ok(items));
            }
            for (v, ps, ns) in self.cells_at(p, n) {
                if ns.len() > 1 {
                    forked = true;
                    continue;
                }
                let n2 = ns.first().copied();
                for p2 in ps {
                    if let std::collections::hash_map::Entry::Vacant(e) = index.entry((p2, n2)) {
                        e.insert(nodes.len());
                        nodes.push(((p2, n2), Some((i, v.clone()))));
                    }
                }
            }
            i += 1;
        }
        (!forked).then_some(Err(()))
    }

    /// Stage 2: whether `(π, ν)` is in the largest simulation over the pairs reached from it.
    fn simulated(&mut self) -> bool {
        let start = (self.pi, self.nu);
        let mut pairs: Vec<(usize, usize)> = vec![start];
        let mut index: HashMap<(usize, usize), usize> = HashMap::from([(start, 0)]);
        let mut failed: Vec<bool> = Vec::new();
        // Each choice: the pair it belongs to and how many of its options have not failed.
        let mut choices: Vec<(usize, usize)> = Vec::new();
        // For each pair, the choices it is an option of.
        let mut readers: Vec<Vec<usize>> = Vec::new();
        let mut dead: VecDeque<usize> = VecDeque::new();
        let mut i = 0;
        while i < pairs.len() {
            let (p, n) = pairs[i];
            failed.push(false);
            readers.resize(pairs.len(), Vec::new());
            if self.r.states[p].stop && !self.r.states[n].stop {
                failed[i] = true;
                dead.push_back(i);
                i += 1;
                continue;
            }
            for (_, ps, ns) in self.cells_at(p, Some(n)) {
                for p2 in ps {
                    let c = choices.len();
                    choices.push((i, ns.len()));
                    if ns.is_empty() && !failed[i] {
                        failed[i] = true;
                        dead.push_back(i);
                    }
                    for &n2 in &ns {
                        let j = *index.entry((p2, n2)).or_insert_with(|| {
                            pairs.push((p2, n2));
                            pairs.len() - 1
                        });
                        readers.resize(pairs.len(), Vec::new());
                        readers[j].push(c);
                    }
                }
            }
            i += 1;
        }
        while let Some(j) = dead.pop_front() {
            for &c in &readers[j] {
                let (owner, left) = &mut choices[c];
                *left -= 1;
                if *left == 0 && !failed[*owner] {
                    failed[*owner] = true;
                    dead.push_back(*owner);
                }
            }
        }
        !failed[0]
    }
}

/// The decision of the class above, or `None` outside it or when no stage decides.
pub(super) fn decide(t: &Type) -> Option<Decided> {
    let p: &Parts = &t.p();
    if p.structs || p.tuples.rest || !p.tuples.lens.is_empty() || !only_atoms(p) {
        return None;
    }
    if p.atoms.cofinite() {
        return None;
    }
    let (mut stop, mut link) = (None, None);
    for (name, a) in p.atoms.names() {
        match (a.bare, a.payload == Type::empty()) {
            (true, true) if stop.is_none() => stop = Some(name.clone()),
            (false, false) if link.is_none() => link = Some((name.clone(), a.payload.clone())),
            _ => return None,
        }
    }
    if let Some(s) = &stop {
        let v = Value::atom(s);
        return t.contains(&v).then_some(Decided::Inhabited(v));
    }
    let (link, payload) = link?;
    let q = payload.p();
    let f = pairs_only(&q)?;
    let (taken, refused) = f.forced();
    let taken_set: BTreeSet<&Row> = taken.iter().collect();
    let refused_set: BTreeSet<&Row> = refused.iter().collect();
    let g = f.restrict(&|a: &Row| {
        if taken_set.contains(a) {
            Some(true)
        } else if refused_set.contains(a) {
            Some(false)
        } else {
            None
        }
    });
    let union = match g.is_leaf() {
        Some(false) => return Some(Decided::Empty),
        Some(true) => Vec::new(),
        None => g.union_rows()?,
    };
    let mut r = Reader {
        states: Vec::new(),
        of: ByType::new(),
        heads: ByType::new(),
        stop: None,
        link: link.clone(),
    };
    let read = |r: &mut Reader, rows: &[Row]| -> Option<Vec<(Ints, usize)>> {
        rows.iter()
            .map(|row| Some((r.head(&row[0])?, r.state(&row[1])?)))
            .collect()
    };
    let taken_rows = read(&mut r, &taken)?;
    let union_rows: Vec<(Ints, usize)> = read(&mut r, &union)?;
    let refused_rows = read(&mut r, &refused)?;
    // Stage 0: the taken carriers as masks.
    let (mut first, mut later): (Option<Ints>, Option<Ints>) = (None, None);
    let mut rest: Vec<(Ints, usize)> = Vec::new();
    let mut a_carrier = None;
    for (h, s) in taken_rows {
        if let Some(c) = r.carrier(s) {
            later = Some(later.map_or_else(|| c.clone(), |l| Ints::meet(&l, c)));
            first = Some(first.map_or_else(|| h.clone(), |f| Ints::meet(&f, &h)));
            a_carrier.get_or_insert((h, s));
        } else {
            rest.push((h, s));
        }
    }
    let start: Vec<(Ints, usize)> = match (rest.len(), union_rows.is_empty()) {
        (0, false) => union_rows,
        (1, true) => rest,
        (0, true) => vec![a_carrier?],
        // Two positive automata met: a product, out of the class.
        _ => return None,
    };
    let start: Vec<(Ints, usize)> = start
        .into_iter()
        .map(|(h, s)| {
            (
                first
                    .as_ref()
                    .map_or_else(|| h.clone(), |c| Ints::meet(&h, c)),
                s,
            )
        })
        .filter(|(h, _)| !Ints::is_empty(h))
        .collect();
    let pi = r.states.len();
    r.states.push(State {
        stop: false,
        rows: start,
    });
    let nu = r.states.len();
    r.states.push(State {
        stop: false,
        rows: refused_rows,
    });
    let mut fork = Fork {
        r,
        pi,
        nu,
        later,
        pos: HashMap::new(),
    };
    match fork.unforked() {
        Some(Ok(items)) => {
            let stop = Value::atom(fork.r.stop.as_deref()?);
            let v = items.into_iter().rev().fold(stop, |tail, x| {
                Value::atom_with(link.clone(), vec![x, tail])
            });
            return t.contains(&v).then_some(Decided::Inhabited(v));
        }
        Some(Err(())) => return Some(Decided::Empty),
        None => {}
    }
    fork.simulated().then_some(Decided::Empty)
}
