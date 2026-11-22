//! S4 evaluated in the topological order of the class check, on random systems with holed
//! names on cycles of the base (the S4 base study of round 4,
//! `/home/luke/Work/wt/xst/archive/r4/spec-s4-base/`, command `holed`: `src/engine.rs` and
//! `random_holed`, `shuffled`, `holed_cmd` in `src/main.rs`, logs `logs/holed_*.log`), in the
//! study's sizes and from its seeds.
//!
//! A system is a box of integer intervals, base atoms `sum k x <= c` and parts (disjunctions of
//! one-atom cases). A hole is a part `x <= a - 1 | x >= b + 1` on one name. Every term (the
//! least or greatest value of a name) is a node; an atom used to narrow writes one term from
//! the terms it reads, and a part's case also reads, through the death of the other cases, the
//! terms of their forms. The class check (K3: condition (iii), and the result-1 limit on holes)
//! takes the strongly connected components of that graph and refuses a system where:
//!
//! - one cyclic component holds the edges of two parts;
//! - (iii): a part narrows by its join a term that two of its cases write, on a cyclic
//!   component;
//! - result 1: a cyclic component that is not one simple cycle holds terms of more than two
//!   holed names; or, under the older condition (ii), any cyclic component holds a term of a
//!   holed name.
//!
//! A system in the class is evaluated in topological order of the components, each part's join
//! once per narrowed term; a join that would narrow a second time refuses the system. The
//! reference is `plain`: chaotic iteration of the base, the deaths and promotions of cases, and
//! every part's join, to a fixpoint. The study's counts, 200,000 systems from each seed: K3
//! with the result-1 limit, and with no hole check, never refuses by a second narrowing, always
//! agrees with `plain`, and gives the same class and answer on three shuffles of each system.
//! CONTROLS: the reversed topological order differs from `plain` on 127, 128 and 142 systems;
//! the class without (iii) and with no hole check is refused by a second narrowing on 53, 59
//! and 58.
//!
//! Every range of the systems drawn is finite (`0..=hi` with `hi` in `4..=9`) and every
//! constant small, so the study's saturating arithmetic around infinite bounds, and its least
//! fixpoint of the terms that can become finite (all of them here), are left out: they change
//! nothing on these systems.
//!
//! Pieces. Unlike the projections of [`super::s4_names`], the shuffles draw from the generator
//! only for a system that a mode puts in its class and does not refuse, so finding the first
//! draw of a piece means classifying and evaluating every system before it. Each piece
//! therefore starts from the generator state pinned as the previous piece's end, and asserts
//! that its own end state is the one pinned: the pieces chain back to the seed. A piece whose
//! start is not pinned yet replays the systems before it, without the counts. The pieces print
//! their counts and end state; `per_piece` and the list of piece tests set their size.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::Lcg;
use zed_tests::instances::Rng;

/// `sum k x <= c`.
#[derive(Clone, Debug)]
struct Le {
    terms: Vec<(usize, i64)>,
    c: i64,
}

/// `sum k x <= c`, or `>= c` when `ge`.
fn le(terms: &[(usize, i64)], ge: bool, c: i64) -> Le {
    if ge {
        Le {
            terms: terms.iter().map(|&(v, k)| (v, -k)).collect(),
            c: -c,
        }
    } else {
        Le {
            terms: terms.to_vec(),
            c,
        }
    }
}

#[derive(Clone, Debug)]
struct Input {
    lo: Vec<i64>,
    hi: Vec<i64>,
    base: Vec<Le>,
    parts: Vec<Vec<Le>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Out {
    Bottom,
    Boxes(Vec<(i64, i64)>),
    /// A join narrowed a second time.
    Refused,
}

/// The terms of name `v`: `2v` its least value, `2v + 1` its greatest.
fn term_written(v: usize, k: i64) -> usize {
    if k > 0 { 2 * v + 1 } else { 2 * v }
}

/// The term a term `k v` of an atom reads when the atom narrows another name: the bound that
/// minimizes `k v`.
fn term_read(v: usize, k: i64) -> usize {
    if k > 0 { 2 * v } else { 2 * v + 1 }
}

/// The terms written by two or more cases of a part: the only terms its join can narrow.
fn written_twice(cases: &[Le]) -> Vec<usize> {
    let mut ws: Vec<usize> = cases
        .iter()
        .flat_map(|a| {
            let mut w: Vec<usize> = a.terms.iter().map(|&(v, k)| term_written(v, k)).collect();
            w.sort_unstable();
            w.dedup();
            w
        })
        .collect();
    ws.sort_unstable();
    let mut twice: Vec<usize> = ws
        .windows(2)
        .filter(|w| w[0] == w[1])
        .map(|w| w[0])
        .collect();
    twice.dedup();
    twice
}

/// A linear form of the cases: their terms sorted, the first coefficient positive. Cases
/// `form <= c` die when the form's least value exceeds `c`, cases `form >= c` when its greatest
/// is below `c`; each map holds them by `c`.
struct Form {
    terms: Vec<(usize, i64)>,
    upper: BTreeMap<i64, Vec<(usize, usize)>>,
    lower: BTreeMap<i64, Vec<(usize, usize)>>,
}

/// The form of an atom's terms, and whether the atom is `form <= c` (else `-form <= c`).
fn canon(t: &[(usize, i64)]) -> (Vec<(usize, i64)>, bool) {
    let mut t = t.to_vec();
    t.sort_unstable();
    if t[0].1 < 0 {
        (t.iter().map(|&(v, k)| (v, -k)).collect(), false)
    } else {
        (t, true)
    }
}

/// The kinds of work in the topological queue, which orders by topological index, then kind,
/// then id.
const TERM: u8 = 0;
const JOIN: u8 = 1;

/// The evaluator: the base propagates bounds; a case dies when its form's bounds exclude it; a
/// part with one live case left promotes it to the base; joins narrow by the hull of the live
/// cases.
struct Ev<'a> {
    inp: &'a Input,
    lo: Vec<i64>,
    hi: Vec<i64>,
    base: Vec<Le>,
    base_of: Vec<Vec<usize>>,
    forms: Vec<Form>,
    forms_of: Vec<Vec<usize>>,
    live: Vec<usize>,
    dead: Vec<Vec<bool>>,
    promoted: Vec<bool>,
    /// The names to revisit, last in first out (no topological order).
    queue: Vec<usize>,
    queued: Vec<bool>,
    bottom: bool,
    refused: bool,
    /// The topological index of each term, when evaluating in topological order.
    topo: Option<Vec<usize>>,
    /// `(index, TERM, term)` and `(index, JOIN, part * terms + term)`.
    heap: BTreeSet<(usize, u8, usize)>,
    parts_of_name: Vec<Vec<usize>>,
    jterms: Vec<Vec<usize>>,
    /// The joins that have run: `(part, term)`.
    jran: HashSet<(usize, usize)>,
}

impl<'a> Ev<'a> {
    fn new(inp: &'a Input, topo: Option<Vec<usize>>) -> Self {
        let nn = inp.lo.len();
        let mut ev = Ev {
            inp,
            lo: inp.lo.clone(),
            hi: inp.hi.clone(),
            base: Vec::new(),
            base_of: vec![Vec::new(); nn],
            forms: Vec::new(),
            forms_of: vec![Vec::new(); nn],
            live: inp.parts.iter().map(Vec::len).collect(),
            dead: inp.parts.iter().map(|c| vec![false; c.len()]).collect(),
            promoted: vec![false; inp.parts.len()],
            queue: Vec::new(),
            queued: vec![false; nn],
            bottom: false,
            refused: false,
            topo,
            heap: BTreeSet::new(),
            parts_of_name: vec![Vec::new(); nn],
            jterms: inp.parts.iter().map(|c| written_twice(c)).collect(),
            jran: HashSet::new(),
        };
        for (p, cases) in inp.parts.iter().enumerate() {
            let mut names: Vec<usize> = cases
                .iter()
                .flat_map(|a| a.terms.iter().map(|t| t.0))
                .collect();
            names.sort_unstable();
            names.dedup();
            for v in names {
                ev.parts_of_name[v].push(p);
            }
        }
        let mut form_id: HashMap<Vec<(usize, i64)>, usize> = HashMap::new();
        for (p, cases) in inp.parts.iter().enumerate() {
            for (k, a) in cases.iter().enumerate() {
                let (form, upper) = canon(&a.terms);
                let id = match form_id.get(&form) {
                    Some(&id) => id,
                    None => {
                        let id = ev.forms.len();
                        for &(v, _) in &form {
                            ev.forms_of[v].push(id);
                        }
                        ev.forms.push(Form {
                            terms: form.clone(),
                            upper: BTreeMap::new(),
                            lower: BTreeMap::new(),
                        });
                        form_id.insert(form, id);
                        id
                    }
                };
                if upper {
                    ev.forms[id].upper.entry(a.c).or_default().push((p, k));
                } else {
                    ev.forms[id].lower.entry(-a.c).or_default().push((p, k));
                }
            }
        }
        for a in &inp.base {
            ev.add_base(a.clone());
        }
        for v in 0..nn {
            ev.push_term(2 * v);
            ev.push_term(2 * v + 1);
        }
        if let Some(topo) = &ev.topo {
            let nt = 2 * nn;
            for (p, ts) in ev.jterms.iter().enumerate() {
                for &t in ts {
                    ev.heap.insert((topo[t], JOIN, p * nt + t));
                }
            }
        }
        ev
    }

    fn push_term(&mut self, t: usize) {
        match &self.topo {
            None => {
                let v = t / 2;
                if !self.queued[v] {
                    self.queued[v] = true;
                    self.queue.push(v);
                }
            }
            Some(topo) => {
                self.heap.insert((topo[t], TERM, t));
            }
        }
    }

    fn add_base(&mut self, a: Le) {
        let id = self.base.len();
        for &(v, _) in &a.terms {
            self.base_of[v].push(id);
        }
        self.base.push(a);
        self.prop(id);
    }

    fn set_lo(&mut self, v: usize, x: i64) {
        if x > self.lo[v] {
            self.lo[v] = x;
            self.bottom |= self.lo[v] > self.hi[v];
            self.push_term(2 * v);
        }
    }

    fn set_hi(&mut self, v: usize, x: i64) {
        if x < self.hi[v] {
            self.hi[v] = x;
            self.bottom |= self.lo[v] > self.hi[v];
            self.push_term(2 * v + 1);
        }
    }

    /// Bound propagation of base atom `id`, from the bounds as they are on entry.
    fn prop(&mut self, id: usize) {
        let a = self.base[id].clone();
        let mins: Vec<i64> = a
            .terms
            .iter()
            .map(|&(v, k)| {
                if k > 0 {
                    k * self.lo[v]
                } else {
                    k * self.hi[v]
                }
            })
            .collect();
        let sum: i64 = mins.iter().sum();
        for (i, &(v, k)) in a.terms.iter().enumerate() {
            let room = a.c - (sum - mins[i]);
            if k > 0 {
                self.set_hi(v, room.div_euclid(k));
            } else {
                self.set_lo(v, -(room.div_euclid(-k)));
            }
            if self.bottom {
                return;
            }
        }
    }

    /// Kills the cases of form `f` its bounds exclude, until none dies (a chain of holes on one
    /// name snaps in one call).
    fn check_form(&mut self, f: usize) {
        while self.check_form_once(f) && !self.bottom {}
    }

    fn check_form_once(&mut self, f: usize) -> bool {
        let (mut l, mut h) = (0, 0);
        for &(v, k) in &self.forms[f].terms {
            let (a, b) = (k * self.lo[v], k * self.hi[v]);
            l += a.min(b);
            h += a.max(b);
        }
        let form = &mut self.forms[f];
        let mut dying = Vec::new();
        while let Some(e) = form.upper.first_entry() {
            if *e.key() >= l {
                break;
            }
            dying.extend(e.remove());
        }
        while let Some(e) = form.lower.last_entry() {
            if *e.key() <= h {
                break;
            }
            dying.extend(e.remove());
        }
        let any = !dying.is_empty();
        for (p, k) in dying {
            self.die(p, k);
            if self.bottom {
                return false;
            }
        }
        any
    }

    fn die(&mut self, p: usize, k: usize) {
        if self.dead[p][k] {
            return;
        }
        self.dead[p][k] = true;
        self.live[p] -= 1;
        match self.live[p] {
            0 => self.bottom = true,
            1 if !self.promoted[p] => {
                self.promoted[p] = true;
                let k = self.dead[p]
                    .iter()
                    .position(|&d| !d)
                    .expect("one live case");
                let inp = self.inp;
                self.add_base(inp.parts[p][k].clone());
            }
            _ => {}
        }
    }

    /// The base atoms and the forms on name `v`, after a bound of `v` moved. The atoms promoted
    /// meanwhile wait for the next move.
    fn visit(&mut self, v: usize) {
        for i in 0..self.base_of[v].len() {
            let id = self.base_of[v][i];
            self.prop(id);
            if self.bottom {
                return;
            }
        }
        for i in 0..self.forms_of[v].len() {
            let f = self.forms_of[v][i];
            self.check_form(f);
            if self.bottom {
                return;
            }
        }
    }

    /// The base and the promotions to a fixpoint (no topological order).
    fn run(&mut self) {
        while let Some(v) = self.queue.pop() {
            self.queued[v] = false;
            if self.bottom {
                return;
            }
            self.visit(v);
            if self.bottom {
                return;
            }
        }
    }

    /// The narrowings of the join of part `p`'s live cases, each propagated alone in the box:
    /// `(name, least, greatest)` for each name the hull narrows.
    fn join(&self, p: usize) -> Vec<(usize, i64, i64)> {
        let cases: Vec<&Le> = self.inp.parts[p]
            .iter()
            .enumerate()
            .filter(|&(k, _)| !self.dead[p][k])
            .map(|(_, a)| a)
            .collect();
        if cases.len() < 2 {
            return Vec::new();
        }
        let mut names: Vec<usize> = cases
            .iter()
            .flat_map(|a| a.terms.iter().map(|t| t.0))
            .collect();
        names.sort_unstable();
        names.dedup();
        let mut out = Vec::new();
        for v in names {
            let (mut jl, mut jh) = (i64::MAX, i64::MIN);
            for a in &cases {
                let (mut l, mut h) = (self.lo[v], self.hi[v]);
                if let Some(&(_, k)) = a.terms.iter().find(|t| t.0 == v) {
                    let rest: i64 = a
                        .terms
                        .iter()
                        .filter(|t| t.0 != v)
                        .map(|&(u, ku)| {
                            if ku > 0 {
                                ku * self.lo[u]
                            } else {
                                ku * self.hi[u]
                            }
                        })
                        .sum();
                    let room = a.c - rest;
                    if k > 0 {
                        h = h.min(room.div_euclid(k));
                    } else {
                        l = l.max(-(room.div_euclid(-k)));
                    }
                }
                jl = jl.min(l);
                jh = jh.max(h);
            }
            if jl > self.lo[v] || jh < self.hi[v] {
                out.push((v, jl.max(self.lo[v]), jh.min(self.hi[v])));
            }
        }
        out
    }

    /// Evaluation in topological order: a term's work runs after every term it depends on; a
    /// part's join on a term runs once its inputs are done, and again when they change; a join
    /// that narrows a second time refuses the system.
    fn run_topo(&mut self) {
        let nt = 2 * self.lo.len();
        while let Some((k, kind, id)) = self.heap.pop_first() {
            if self.bottom || self.refused {
                return;
            }
            if kind == TERM {
                let v = id / 2;
                self.visit(v);
                if self.bottom {
                    return;
                }
                for i in 0..self.parts_of_name[v].len() {
                    let p = self.parts_of_name[v][i];
                    if self.live[p] < 2 {
                        continue;
                    }
                    for j in 0..self.jterms[p].len() {
                        let t = self.jterms[p][j];
                        let kt = self.topo.as_ref().expect("topological order")[t];
                        if self.jran.contains(&(p, t)) && k <= kt {
                            self.heap.insert((kt, JOIN, p * nt + t));
                        }
                    }
                }
            } else {
                let (p, t) = (id / nt, id % nt);
                if self.live[p] < 2 {
                    continue;
                }
                let v = t / 2;
                let nar: Vec<(usize, i64, i64)> = self
                    .join(p)
                    .into_iter()
                    .filter(|&(u, l, h)| {
                        u == v
                            && if t % 2 == 0 {
                                l > self.lo[v]
                            } else {
                                h < self.hi[v]
                            }
                    })
                    .collect();
                if self.jran.contains(&(p, t)) && !nar.is_empty() {
                    self.refused = true;
                    return;
                }
                self.jran.insert((p, t));
                for (v, l, h) in nar {
                    if t % 2 == 0 {
                        self.set_lo(v, l);
                    } else {
                        self.set_hi(v, h);
                    }
                }
            }
        }
    }

    fn out(&self) -> Out {
        if self.bottom {
            Out::Bottom
        } else if self.refused {
            Out::Refused
        } else {
            Out::Boxes(
                self.lo
                    .iter()
                    .copied()
                    .zip(self.hi.iter().copied())
                    .collect(),
            )
        }
    }
}

/// The reference: the base and the promotions to a fixpoint, then every live part's join, again
/// until no join narrows.
fn plain(inp: &Input) -> Out {
    let mut ev = Ev::new(inp, None);
    loop {
        ev.run();
        if ev.bottom {
            return Out::Bottom;
        }
        let mut moved = false;
        let live_parts: Vec<usize> = (0..inp.parts.len()).filter(|&p| ev.live[p] >= 2).collect();
        for p in live_parts {
            for (v, l, h) in ev.join(p) {
                moved = true;
                ev.set_lo(v, l);
                ev.set_hi(v, h);
            }
        }
        if !moved {
            return ev.out();
        }
    }
}

fn run_with(inp: &Input, topo: Vec<usize>) -> Out {
    let mut ev = Ev::new(inp, Some(topo));
    ev.run_topo();
    ev.out()
}

/// CONTROL: the topological queue with every term at index 0 and no class check.
fn unordered(inp: &Input) -> Out {
    run_with(inp, vec![0; 2 * inp.lo.len()])
}

// ---------------------------------------------------------------------------------------------
// The class check.

/// For each term an atom writes when it narrows (one per name), the terms it reads.
fn atom_edges(a: &Le) -> Vec<(usize, Vec<usize>)> {
    a.terms
        .iter()
        .map(|&(x, kx)| {
            let reads = a
                .terms
                .iter()
                .filter(|t| t.0 != x)
                .map(|&(y, ky)| term_read(y, ky))
                .collect();
            (term_written(x, kx), reads)
        })
        .collect()
}

/// The terms that decide whether case `a` dies: those that give its form's least value.
fn death_reads(a: &Le) -> Vec<usize> {
    a.terms.iter().map(|&(v, k)| term_read(v, k)).collect()
}

/// The name of a hole: a part whose cases are each one term on one name.
fn unary(cases: &[Le]) -> Option<usize> {
    let v = cases.first()?.terms.first()?.0;
    cases
        .iter()
        .all(|a| a.terms.len() == 1 && a.terms[0].0 == v)
        .then_some(v)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HoleCheck {
    /// Condition (ii): no cyclic component holds a term of a holed name.
    NoneOnACycle,
    /// Result 1: a cyclic component with holed names is one simple cycle or holds at most two.
    ResultOne,
    /// No check on holes.
    Off,
}

#[derive(Debug)]
enum Refusal {
    PartsInACycle,
    ConditionIii,
    HolesOnAComponent,
    HolesOnACycle,
}

/// The class decision, and the topological index of each term (computed either way).
#[derive(Debug)]
struct Class {
    refusal: Option<Refusal>,
    topo: Vec<usize>,
}

/// The class check: the graph of terms, its strongly connected components by Tarjan's
/// algorithm (R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM J. Comput.
/// 1(2), 1972, doi:10.1137/0201010), iterative, roots and edges in the study's order so that the
/// topological indices are the study's.
fn classify(inp: &Input, iii: bool, holes: HoleCheck) -> Class {
    let nn = inp.lo.len();
    let nt = 2 * nn;
    // Edges `(read, written, part)`, `None` for the base. A hole adds no edge.
    let mut edges: Vec<(usize, usize, Option<usize>)> = Vec::new();
    let mut holed = vec![false; nn];
    for a in &inp.base {
        for (w, reads) in atom_edges(a) {
            edges.extend(reads.into_iter().map(|t| (t, w, None)));
        }
    }
    for (p, cases) in inp.parts.iter().enumerate() {
        if let Some(v) = unary(cases) {
            holed[v] = true;
            continue;
        }
        for a in cases {
            for (w, reads) in atom_edges(a) {
                edges.extend(reads.into_iter().map(|t| (t, w, Some(p))));
            }
        }
        for (i, a) in cases.iter().enumerate() {
            for (j, b) in cases.iter().enumerate() {
                if i != j {
                    for t in death_reads(a) {
                        for (w, _) in atom_edges(b) {
                            edges.push((t, w, Some(p)));
                        }
                    }
                }
            }
        }
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); nt];
    for &(s, d, _) in &edges {
        adj[s].push(d);
    }
    const UNSEEN: usize = usize::MAX;
    let (mut index, mut low, mut on) = (vec![UNSEEN; nt], vec![0; nt], vec![false; nt]);
    let (mut comp, mut stack, mut next, mut ncomp) = (vec![UNSEEN; nt], Vec::new(), 0, 0);
    for root in 0..nt {
        if index[root] != UNSEEN {
            continue;
        }
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on[root] = true;
        let mut call: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(top) = call.last_mut() {
            let v = top.0;
            if top.1 < adj[v].len() {
                let w = adj[v][top.1];
                top.1 += 1;
                if index[w] == UNSEEN {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on[w] = true;
                    call.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                call.pop();
                if let Some(&(u, _)) = call.last() {
                    low[u] = low[u].min(low[v]);
                }
                if low[v] == index[v] {
                    loop {
                        let w = stack.pop().expect("v is on the stack");
                        on[w] = false;
                        comp[w] = ncomp;
                        if w == v {
                            break;
                        }
                    }
                    ncomp += 1;
                }
            }
        }
    }
    // Tarjan's algorithm numbers the components in reverse topological order.
    let topo: Vec<usize> = comp.iter().map(|c| ncomp - 1 - c).collect();
    let out = |refusal| Class {
        refusal: Some(refusal),
        topo: topo.clone(),
    };
    let mut size = vec![0usize; ncomp];
    for &c in &comp {
        size[c] += 1;
    }
    let mut cyclic: Vec<bool> = size.iter().map(|&s| s > 1).collect();
    let mut parts_in: Vec<Vec<usize>> = vec![Vec::new(); ncomp];
    for &(s, d, p) in &edges {
        if comp[s] == comp[d] {
            cyclic[comp[s]] = true;
            parts_in[comp[s]].extend(p);
        }
    }
    for ps in &mut parts_in {
        ps.sort_unstable();
        ps.dedup();
        if ps.len() >= 2 {
            return out(Refusal::PartsInACycle);
        }
    }
    if iii {
        for cases in &inp.parts {
            if unary(cases).is_none() && written_twice(cases).iter().any(|&t| cyclic[comp[t]]) {
                return out(Refusal::ConditionIii);
            }
        }
    }
    if holes == HoleCheck::ResultOne {
        let mut holed_names: Vec<Vec<usize>> = vec![Vec::new(); ncomp];
        for v in (0..nn).filter(|&v| holed[v]) {
            for t in [2 * v, 2 * v + 1] {
                if cyclic[comp[t]] {
                    holed_names[comp[t]].push(v);
                }
            }
        }
        let mut inner: Vec<HashSet<(usize, usize)>> = vec![HashSet::new(); ncomp];
        for &(s, d, _) in &edges {
            if comp[s] == comp[d] {
                inner[comp[s]].insert((s, d));
            }
        }
        for c in 0..ncomp {
            holed_names[c].sort_unstable();
            holed_names[c].dedup();
            let simple_cycle = inner[c].len() == size[c];
            if !holed_names[c].is_empty() && !simple_cycle && holed_names[c].len() > 2 {
                return out(Refusal::HolesOnAComponent);
            }
        }
    }
    if holes == HoleCheck::NoneOnACycle && (0..nt).any(|t| holed[t / 2] && cyclic[comp[t]]) {
        return out(Refusal::HolesOnACycle);
    }
    Class {
        refusal: None,
        topo,
    }
}

// ---------------------------------------------------------------------------------------------
// The battery.

fn rnd(g: &mut Lcg, n: u64) -> i64 {
    g.next(n) as i64
}

/// The study's random system: names `0..nn` with `nn` in `4..=7`, each in `0..=hi`; a cycle of
/// difference atoms over the first `m` names of a shuffle, sometimes a chord; up to two more
/// base atoms; holes on one to three names, mostly on the cycle; one to four parts of two or
/// three atoms.
fn random_holed(g: &mut Lcg) -> Input {
    let nn = 4 + g.next(4) as usize;
    let hi: Vec<i64> = (0..nn).map(|_| 4 + rnd(g, 6)).collect();
    let mut base = Vec::new();
    let m = 2 + g.next(nn as u64 - 1) as usize;
    let mut perm: Vec<usize> = (0..nn).collect();
    for i in (1..nn).rev() {
        perm.swap(i, g.next(i as u64 + 1) as usize);
    }
    for i in 0..m {
        let (a, b) = (perm[i], perm[(i + 1) % m]);
        base.push(le(&[(b, 1), (a, -1)], false, rnd(g, 4) - 1));
    }
    if g.next(2) == 0 && m >= 3 {
        let a = perm[g.next(m as u64) as usize];
        let b = perm[g.next(m as u64) as usize];
        if a != b {
            base.push(le(&[(a, 1), (b, -1)], false, rnd(g, 4) - 1));
        }
    }
    let atom = |g: &mut Lcg| {
        let u = g.next(nn as u64) as usize;
        let mut t = vec![(u, if g.next(2) == 0 { 1 } else { -1 })];
        if g.next(3) != 0 {
            let v = (u + 1 + g.next(nn as u64 - 1) as usize) % nn;
            t.push((v, if g.next(2) == 0 { 1 } else { -1 }));
        }
        le(&t, false, rnd(g, 7) - 3)
    };
    for _ in 0..g.next(3) {
        base.push(atom(g));
    }
    let mut parts: Vec<Vec<Le>> = Vec::new();
    for _ in 0..1 + g.next(3) {
        let v = if g.next(4) != 0 {
            perm[g.next(m as u64) as usize]
        } else {
            g.next(nn as u64) as usize
        };
        for _ in 0..1 + g.next(2) {
            let a = 1 + rnd(g, hi[v] as u64 - 1);
            let b = a + rnd(g, 2);
            parts.push(vec![
                le(&[(v, 1)], false, a - 1),
                le(&[(v, 1)], true, b + 1),
            ]);
        }
    }
    for _ in 0..1 + g.next(4) {
        let k = if g.next(4) == 0 { 3 } else { 2 };
        parts.push((0..k).map(|_| atom(g)).collect());
    }
    Input {
        lo: vec![0; nn],
        hi,
        base,
        parts,
    }
}

/// The system with its parts and base atoms in a random order, and each part's cases reversed
/// with even chance.
fn shuffled(inp: &Input, g: &mut Lcg) -> Input {
    let mut q = inp.clone();
    for i in (1..q.parts.len()).rev() {
        q.parts.swap(i, g.next(i as u64 + 1) as usize);
    }
    for i in (1..q.base.len()).rev() {
        q.base.swap(i, g.next(i as u64 + 1) as usize);
    }
    for p in &mut q.parts {
        if g.next(2) == 0 {
            p.reverse();
        }
    }
    q
}

/// The three classes the study compares: `(iii, hole check)`.
const MODES: [(bool, HoleCheck); 3] = [
    (true, HoleCheck::ResultOne),
    (true, HoleCheck::Off),
    // CONTROL: no (iii), no hole check.
    (false, HoleCheck::Off),
];

/// The counts of one class of [`MODES`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ModeCounts {
    in_class: usize,
    /// Of those, the systems condition (ii) refuses (a holed name on a cyclic component).
    holed_on_a_cycle: usize,
    /// Refused by a second narrowing.
    refused: usize,
    differs_from_plain: usize,
    /// Over three shuffles of each system answered: the class decision differs.
    shuffle_class: usize,
    /// The answer differs.
    shuffle_answer: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Counts {
    plain_bottom: usize,
    ii_refuses: usize,
    /// CONTROL: unordered queue with no class check.
    unordered_answers: usize,
    unordered_differs: usize,
    /// CONTROL: the reversed topological order, on the systems K3 with the result-1 limit
    /// takes.
    reversed_refused: usize,
    reversed_differs: usize,
    modes: [ModeCounts; 3],
}

impl Counts {
    fn flat(&self) -> [usize; 24] {
        let mut f = [0; 24];
        f[..6].copy_from_slice(&[
            self.plain_bottom,
            self.ii_refuses,
            self.unordered_answers,
            self.unordered_differs,
            self.reversed_refused,
            self.reversed_differs,
        ]);
        for (i, m) in self.modes.iter().enumerate() {
            f[6 + 6 * i..12 + 6 * i].copy_from_slice(&[
                m.in_class,
                m.holed_on_a_cycle,
                m.refused,
                m.differs_from_plain,
                m.shuffle_class,
                m.shuffle_answer,
            ]);
        }
        f
    }
}

fn in_class(inp: &Input, (iii, holes): (bool, HoleCheck)) -> Option<Vec<usize>> {
    let c = classify(inp, iii, holes);
    c.refusal.is_none().then_some(c.topo)
}

/// The study's `holed` on `systems` systems from `g`. With `counting` false, only what draws
/// from `g` runs (each mode's class and evaluation, which decide whether its shuffles are
/// drawn), to move `g` past the systems.
fn holed(g: &mut Lcg, systems: usize, counting: bool) -> Counts {
    let mut n = Counts::default();
    for _ in 0..systems {
        let inp = random_holed(g);
        if !counting {
            for mode in MODES {
                if let Some(topo) = in_class(&inp, mode)
                    && run_with(&inp, topo) != Out::Refused
                {
                    for _ in 0..3 {
                        shuffled(&inp, g);
                    }
                }
            }
            continue;
        }
        let po = plain(&inp);
        n.plain_bottom += (po == Out::Bottom) as usize;
        let old = matches!(
            classify(&inp, true, HoleCheck::NoneOnACycle).refusal,
            Some(Refusal::HolesOnACycle)
        );
        n.ii_refuses += old as usize;
        let uo = unordered(&inp);
        if uo != Out::Refused {
            n.unordered_answers += 1;
            n.unordered_differs += (uo != po) as usize;
        }
        if in_class(&inp, MODES[0]).is_some() {
            let t = classify(&inp, false, HoleCheck::Off).topo;
            let m = t.iter().copied().max().unwrap_or(0);
            match run_with(&inp, t.iter().map(|k| m - k).collect()) {
                Out::Refused => n.reversed_refused += 1,
                ro => n.reversed_differs += (ro != po) as usize,
            }
        }
        for (mode, t) in MODES.into_iter().zip(&mut n.modes) {
            let Some(topo) = in_class(&inp, mode) else {
                continue;
            };
            t.in_class += 1;
            t.holed_on_a_cycle += old as usize;
            let o = run_with(&inp, topo);
            if o == Out::Refused {
                t.refused += 1;
                continue;
            }
            t.differs_from_plain += (o != po) as usize;
            for _ in 0..3 {
                let q = shuffled(&inp, g);
                match in_class(&q, mode) {
                    None => t.shuffle_class += 1,
                    Some(qt) => t.shuffle_answer += (run_with(&q, qt) != o) as usize,
                }
            }
        }
    }
    n
}

/// The claims of the study on every run: the unordered queue agrees with `plain` where it
/// answers; K3, with the result-1 limit and with no hole check, never refuses, agrees with
/// `plain` and with its shuffles; the CONTROL with no (iii) agrees with `plain` and keeps its
/// class under shuffles where it answers.
fn assert_claims(n: &Counts, what: &str) {
    assert_eq!(
        n.unordered_differs, 0,
        "{what}: unordered queue against plain"
    );
    for (i, m) in n.modes[..2].iter().enumerate() {
        assert_eq!(
            (
                m.refused,
                m.differs_from_plain,
                m.shuffle_class,
                m.shuffle_answer
            ),
            (0, 0, 0, 0),
            "{what}: K3 mode {:?}: refused, differs, shuffle class, shuffle answer",
            MODES[i]
        );
    }
    let c = &n.modes[2];
    assert_eq!(
        (c.differs_from_plain, c.shuffle_class),
        (0, 0),
        "{what}: no (iii): differs, shuffle class"
    );
}

/// One seed's 200,000 systems in pieces.
struct Battery {
    seed: u64,
    per_piece: usize,
    /// The study's counts, from its log.
    study: Counts,
    /// For each piece, its counts ([`Counts::flat`]) and the generator state at its end.
    pinned: &'static [([usize; 24], u64)],
}

const SYSTEMS: usize = 200_000;

impl Battery {
    fn pieces(&self) -> usize {
        SYSTEMS.div_ceil(self.per_piece)
    }

    /// Runs piece `j`, from the state pinned as piece `j - 1`'s end (the seed for piece 0), or
    /// else replayed from the seed; asserts the study's claims, and the counts and end state
    /// pinned for the piece.
    fn piece(&self, j: usize) {
        let from = j * self.per_piece;
        let to = SYSTEMS.min(from + self.per_piece);
        assert!(from < to, "piece {j} starts after the last system");
        let mut g = Lcg(self.seed);
        match j.checked_sub(1).map(|i| self.pinned.get(i)) {
            None => {}
            Some(Some(&(_, end))) => g = Lcg(end),
            Some(None) => {
                holed(&mut g, from, false);
            }
        }
        let start = g.0;
        let n = holed(&mut g, to - from, true);
        let what = format!("holed seed {:#x}, systems {from}..{to}", self.seed);
        eprintln!(
            "{what}: start state {start:#x}, end state {:#x}, counts {:?}",
            g.0,
            n.flat()
        );
        assert_claims(&n, &what);
        if let Some(&(want, end)) = self.pinned.get(j) {
            assert_eq!(n.flat(), want, "{what}: the pinned counts");
            assert_eq!(g.0, end, "{what}: the pinned end state");
        }
    }
}

fn mode(
    in_class: usize,
    holed_on_a_cycle: usize,
    refused: usize,
    shuffle_answer: usize,
) -> ModeCounts {
    ModeCounts {
        in_class,
        holed_on_a_cycle,
        refused,
        differs_from_plain: 0,
        shuffle_class: 0,
        shuffle_answer,
    }
}

// The study's counts (`logs/holed_*.log`), and per piece the counts and end state from runs on
// an 8-core VM with 8 test threads (2026-11-22). A piece of 25,000 systems took 2.8 to 2.9 s
// from the seed; the later pieces, which then replayed the systems before them, took up to
// 8.9 s, so a piece that starts from its pinned state should take about 3 s.

fn holed_4011() -> Battery {
    Battery {
        seed: 0x4011,
        per_piece: 25_000,
        study: Counts {
            plain_bottom: 85_265,
            ii_refuses: 50_141,
            unordered_answers: 199_541,
            unordered_differs: 0,
            reversed_refused: 1,
            reversed_differs: 127,
            modes: [
                mode(48_623, 47_001, 0, 0),
                mode(51_763, 50_141, 0, 0),
                mode(72_292, 50_141, 53, 1),
            ],
        },
        pinned: &[
            (
                [
                    10755, 6273, 24950, 0, 1, 14, 6084, 5887, 0, 0, 0, 0, 6470, 6273, 0, 0, 0, 0,
                    8988, 6273, 3, 0, 0, 0,
                ],
                0x5b6fd677ff3ea362,
            ),
            (
                [
                    10748, 6279, 24942, 0, 0, 12, 6081, 5892, 0, 0, 0, 0, 6468, 6279, 0, 0, 0, 0,
                    8969, 6279, 3, 0, 0, 0,
                ],
                0x46ffaf3f47b8ed5e,
            ),
            (
                [
                    10605, 6232, 24931, 0, 0, 18, 6065, 5852, 0, 0, 0, 0, 6445, 6232, 0, 0, 0, 0,
                    9059, 6232, 11, 0, 0, 0,
                ],
                0x628c362645e53b74,
            ),
            (
                [
                    10620, 6355, 24941, 0, 0, 17, 6137, 5947, 0, 0, 0, 0, 6545, 6355, 0, 0, 0, 0,
                    9079, 6355, 7, 0, 0, 0,
                ],
                0x5a7f56352407f81a,
            ),
            (
                [
                    10667, 6205, 24953, 0, 0, 13, 6044, 5834, 0, 0, 0, 0, 6415, 6205, 0, 0, 0, 0,
                    9034, 6205, 7, 0, 0, 0,
                ],
                0xb9e8b4ee1f191681,
            ),
            (
                [
                    10745, 6347, 24934, 0, 0, 22, 6158, 5931, 0, 0, 0, 0, 6574, 6347, 0, 0, 0, 0,
                    9156, 6347, 6, 0, 0, 1,
                ],
                0x65a98124ee98727e,
            ),
            (
                [
                    10558, 6253, 24936, 0, 0, 16, 6066, 5874, 0, 0, 0, 0, 6445, 6253, 0, 0, 0, 0,
                    9006, 6253, 9, 0, 0, 0,
                ],
                0xe235fdb5f8625b92,
            ),
            (
                [
                    10567, 6197, 24954, 0, 0, 15, 5988, 5784, 0, 0, 0, 0, 6401, 6197, 0, 0, 0, 0,
                    9001, 6197, 7, 0, 0, 0,
                ],
                0x49bab623d52219e5,
            ),
        ],
    }
}

fn holed_5022() -> Battery {
    Battery {
        seed: 0x5022,
        per_piece: 25_000,
        study: Counts {
            plain_bottom: 85_493,
            ii_refuses: 49_945,
            unordered_answers: 199_538,
            unordered_differs: 0,
            reversed_refused: 2,
            reversed_differs: 128,
            modes: [
                mode(48_224, 46_621, 0, 0),
                mode(51_548, 49_945, 0, 0),
                mode(72_544, 49_945, 59, 0),
            ],
        },
        pinned: &[
            (
                [
                    10711, 6242, 24944, 0, 0, 13, 6026, 5829, 0, 0, 0, 0, 6439, 6242, 0, 0, 0, 0,
                    9063, 6242, 7, 0, 0, 0,
                ],
                0x2286bd4f1c4b3a6e,
            ),
            (
                [
                    10712, 6302, 24936, 0, 0, 16, 6084, 5880, 0, 0, 0, 0, 6506, 6302, 0, 0, 0, 0,
                    9082, 6302, 10, 0, 0, 0,
                ],
                0xafaf3e9a990686d3,
            ),
            (
                [
                    10736, 6137, 24936, 0, 0, 13, 5940, 5723, 0, 0, 0, 0, 6354, 6137, 0, 0, 0, 0,
                    8962, 6137, 10, 0, 0, 0,
                ],
                0x8310bfe6f94e6581,
            ),
            (
                [
                    10639, 6245, 24946, 0, 0, 17, 6052, 5827, 0, 0, 0, 0, 6470, 6245, 0, 0, 0, 0,
                    9119, 6245, 3, 0, 0, 0,
                ],
                0xdd3b9d2162a1a29b,
            ),
            (
                [
                    10754, 6327, 24955, 0, 0, 15, 6060, 5877, 0, 0, 0, 0, 6510, 6327, 0, 0, 0, 0,
                    9141, 6327, 7, 0, 0, 0,
                ],
                0x7035d017f6747636,
            ),
            (
                [
                    10578, 6345, 24943, 0, 0, 15, 6113, 5922, 0, 0, 0, 0, 6536, 6345, 0, 0, 0, 0,
                    9119, 6345, 4, 0, 0, 0,
                ],
                0xf13b650e610118c3,
            ),
            (
                [
                    10666, 6129, 24945, 0, 1, 21, 5951, 5757, 0, 0, 0, 0, 6323, 6129, 0, 0, 0, 0,
                    9035, 6129, 6, 0, 0, 0,
                ],
                0x64e5a0f3178c0292,
            ),
            (
                [
                    10697, 6218, 24933, 0, 1, 18, 5998, 5806, 0, 0, 0, 0, 6410, 6218, 0, 0, 0, 0,
                    9023, 6218, 12, 0, 0, 0,
                ],
                0xa9ed35019ecb1962,
            ),
        ],
    }
}

fn holed_6033() -> Battery {
    Battery {
        seed: 0x6033,
        per_piece: 25_000,
        study: Counts {
            plain_bottom: 85_634,
            ii_refuses: 49_950,
            unordered_answers: 199_556,
            unordered_differs: 0,
            reversed_refused: 1,
            reversed_differs: 142,
            modes: [
                mode(48_392, 46_763, 0, 0),
                mode(51_579, 49_950, 0, 0),
                mode(72_564, 49_950, 58, 0),
            ],
        },
        pinned: &[
            (
                [
                    10716, 6245, 24938, 0, 0, 18, 6107, 5876, 0, 0, 0, 0, 6476, 6245, 0, 0, 0, 0,
                    9093, 6245, 9, 0, 0, 0,
                ],
                0x3a9b17d75e0594fa,
            ),
            (
                [
                    10640, 6240, 24955, 0, 0, 14, 6060, 5845, 0, 0, 0, 0, 6455, 6240, 0, 0, 0, 0,
                    9072, 6240, 6, 0, 0, 0,
                ],
                0xe7260ad83c00f3f3,
            ),
            (
                [
                    10581, 6290, 24937, 0, 0, 18, 6088, 5882, 0, 0, 0, 0, 6496, 6290, 0, 0, 0, 0,
                    9090, 6290, 9, 0, 0, 0,
                ],
                0x23a5e7cad049d10,
            ),
            (
                [
                    10679, 6088, 24938, 0, 1, 17, 5893, 5697, 0, 0, 0, 0, 6284, 6088, 0, 0, 0, 0,
                    8941, 6088, 9, 0, 0, 0,
                ],
                0x6f041feb7904be9f,
            ),
            (
                [
                    10764, 6293, 24945, 0, 0, 18, 6124, 5914, 0, 0, 0, 0, 6503, 6293, 0, 0, 0, 0,
                    9102, 6293, 11, 0, 0, 0,
                ],
                0x5f5d46692175cbd7,
            ),
            (
                [
                    10852, 6262, 24944, 0, 0, 21, 6029, 5853, 0, 0, 0, 0, 6438, 6262, 0, 0, 0, 0,
                    9084, 6262, 4, 0, 0, 0,
                ],
                0xcdf73e56f4cb00b,
            ),
            (
                [
                    10681, 6176, 24941, 0, 0, 19, 5979, 5788, 0, 0, 0, 0, 6367, 6176, 0, 0, 0, 0,
                    9002, 6176, 6, 0, 0, 0,
                ],
                0xce05c36d73f8a73c,
            ),
            (
                [
                    10721, 6356, 24958, 0, 0, 17, 6112, 5908, 0, 0, 0, 0, 6560, 6356, 0, 0, 0, 0,
                    9180, 6356, 4, 0, 0, 0,
                ],
                0xd1f7ae940715948f,
            ),
        ],
    }
}

/// Every seed has one pinned row per piece, and the rows add up to the study's counts. With
/// the pieces' own assertions this reproduces the study's log, the CONTROLS included: the
/// reversed order differs from `plain` (127, 128 and 142 systems) and the class without (iii)
/// is refused by a second narrowing (53, 59 and 58), so the comparisons the claims rest on do
/// fail where the study says they fail. Each piece must also have its test below.
#[test]
fn the_pinned_holed_pieces_add_up_to_the_study_counts() {
    for b in [holed_4011(), holed_5022(), holed_6033()] {
        let what = format!("holed seed {:#x}", b.seed);
        assert_eq!(b.pinned.len(), b.pieces(), "{what}: pinned pieces");
        let mut sum = [0; 24];
        for (counts, _) in b.pinned {
            for (s, c) in sum.iter_mut().zip(counts) {
                *s += c;
            }
        }
        assert_eq!(sum, b.study.flat(), "{what}: the pieces' counts added");
    }
}

macro_rules! pieces {
    ($($test:ident: $battery:ident $j:literal;)*) => {
        $(
            #[test]
            fn $test() {
                $battery().piece($j);
            }
        )*
    };
}

pieces! {
    holed_0x4011_piece_0: holed_4011 0;
    holed_0x4011_piece_1: holed_4011 1;
    holed_0x4011_piece_2: holed_4011 2;
    holed_0x4011_piece_3: holed_4011 3;
    holed_0x4011_piece_4: holed_4011 4;
    holed_0x4011_piece_5: holed_4011 5;
    holed_0x4011_piece_6: holed_4011 6;
    holed_0x4011_piece_7: holed_4011 7;
    holed_0x5022_piece_0: holed_5022 0;
    holed_0x5022_piece_1: holed_5022 1;
    holed_0x5022_piece_2: holed_5022 2;
    holed_0x5022_piece_3: holed_5022 3;
    holed_0x5022_piece_4: holed_5022 4;
    holed_0x5022_piece_5: holed_5022 5;
    holed_0x5022_piece_6: holed_5022 6;
    holed_0x5022_piece_7: holed_5022 7;
    holed_0x6033_piece_0: holed_6033 0;
    holed_0x6033_piece_1: holed_6033 1;
    holed_0x6033_piece_2: holed_6033 2;
    holed_0x6033_piece_3: holed_6033 3;
    holed_0x6033_piece_4: holed_6033 4;
    holed_0x6033_piece_5: holed_6033 5;
    holed_0x6033_piece_6: holed_6033 6;
    holed_0x6033_piece_7: holed_6033 7;
}

/// The study's claims on 5,000 systems from a new seed each run.
#[test]
fn the_holed_claims_hold_on_a_fresh_seed() {
    let (_, seed) = Rng::fresh("random holed systems");
    let n = holed(&mut Lcg(seed), 5_000, true);
    eprintln!("seed {seed}: {n:?}");
    assert_claims(&n, &format!("seed {seed}"));
}
