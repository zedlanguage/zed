//! Which tests with `||` alternatives the checker narrows, and the message for the others
//! (DESIGN.md step L1.39, the class of S4, and sec:diagnostics, "A test whose `||` alternatives
//! limit each other's ranges in a loop").
//!
//! A test is read as a conjunction of *parts*, each a disjunction of *cases*, each a
//! conjunction of atoms `lin >= 0`; a part of one case belongs to the base. The class is
//! decided for each component of names joined by a shared atom, after merging the offset
//! equalities `x - y == c` of the base by a union-find with offsets. A component is in it when
//! its *bound graph* (a node for each bound `lo(x)`, `hi(x)` that the box or an atom can make
//! finite; an edge from each bound an atom reads to each bound it writes; an edge from each
//! bound a case's test for being dead reads to each bound the other cases of its part write; a
//! part on one name adds no edge) has (i) no strongly connected component holding edges of two
//! parts and (iii) no bound written by two cases of one part in a cyclic strongly connected
//! component whose edges come from the base and a part or from two parts; or when it is a
//! threshold-implication component ([`threshold::shape`]); or when it
//! is a two-hub octagonal component with a dominating disjunction ([`octagonal`]).
//!
//! Complexity tradeoff: naive, an edge from each bound an atom of k names reads to each of the
//! k bounds it writes, O(k²) per atom, and from each case's reads to each other case's writes,
//! O(m²) per part of m cases. Here prefix and suffix nodes stand for "every read but the
//! writer's own" and "every case but this one", so the graph has O(N) nodes and edges for a
//! test of N atom terms, and a path through them stands for exactly one edge of the naive
//! graph. Tarjan's algorithm (R. Tarjan, "Depth-first search and linear graph algorithms",
//! SIAM J. Comput. 1(2), 1972) then costs O(N). The union-finds link without rank and compress
//! (`Offsets`) or halve (`root`) paths, which is O(N log N) for N operations (R. Tarjan and
//! J. van Leeuwen, "Worst-case analysis of set union algorithms", J. ACM 31(2), 1984), not the
//! O(N α(N)) of union by rank: rank would add a field per name for a factor that the
//! O(N log N) of the other two kinds bounds anyway. The covered-part test, the repair and the
//! steps are O(N log N) too, so the classification is O(N log N). Measured on a chain of k
//! choices, k = 200 and 1600, in instructions and bytes allocated, with the GLIBC_TUNABLES of
//! tools/run_tests.sh (load5 about 57): open chain 8.8x and 8.0x, closed chain with its
//! message 8.3x and 8.0x, the closed chain's opposite
//! 8.8x and 8.0x, against 8 for linear and 12.25 for N log N. Test:
//! `l01_39_reduced_product::loops::classifying_a_chain_of_choices_scales`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

use zedc_int::int::Int;
use zedc_presburger::presburger::{Atom, Con, Formula, Lin, Rel};
use zedc_stage::defs::written_name;

use super::threshold;

/// A test as the class reads it. Every `Lin` is over the scope's integer names alone
/// (`Atom::Sym`) and stands for `lin >= 0`; texts are printed only for a test outside the class.
pub(crate) struct Test {
    /// The atoms of the base, each with the id its text is printed by.
    pub base: Vec<(usize, Lin)>,
    /// The id of the text of each side of the test outside every part, as the repair
    /// keeps it.
    pub kept: Vec<usize>,
    /// The parts of two cases or more.
    pub parts: Vec<Part>,
    /// Each name's box: its least and greatest value when finite, and its range as written,
    /// `int[0..=9]`.
    pub boxes: BTreeMap<Arc<str>, (Option<i128>, Option<i128>, String)>,
}

/// A part of a [`Test`]: its cases.
pub(crate) struct Part {
    /// The id its text is printed by.
    pub text: usize,
    /// The cases.
    pub cases: Vec<Case>,
}

/// A case of a [`Part`].
pub(crate) struct Case {
    /// The id its text is printed by.
    pub text: usize,
    /// Its atoms, each with the id its text is printed by.
    pub atoms: Vec<(usize, Lin)>,
    /// Whether `atoms` is the whole case: no part of it is a test the class does not read,
    /// such as `x != 3` or `f(x) == 2`.
    pub whole: bool,
}

/// A test outside the class, as its message says it: the headline, the steps, and the repair
/// (DESIGN.md sec:diagnostics).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Looped {
    /// What could not be worked out.
    pub headline: String,
    /// The steps of the explanation, in order.
    pub steps: Vec<String>,
    /// The test rewritten, from `repair:`.
    pub repair: String,
}

/// The part label of a base edge.
const BASE: usize = usize::MAX;

/// An atom after the merging of offset equalities: its terms by name index, its constant,
/// the part it belongs to (`BASE` for the base) and its case, and the id of its text.
struct A {
    terms: Vec<(usize, Int)>,
    c: Int,
    part: usize,
    case: usize,
    text: usize,
}

/// What a node of the bound graph is.
#[derive(Clone, Copy)]
enum Node {
    /// A bound: `2 * name` for the least value, `2 * name + 1` for the greatest.
    Bound(usize),
    /// A prefix or suffix of the reads of atom `.0`.
    Atom(usize),
    /// The reads of the test for being dead of case `.1` of part `.0`, or a prefix or suffix of
    /// them.
    Dead(usize, usize),
    /// The writes of a case of a part, by the case.
    Writes(usize),
}

/// The bound graph: its nodes, and each edge with its part label.
struct Graph {
    nodes: Vec<Node>,
    edges: Vec<(usize, usize, usize)>,
}

impl Graph {
    fn add(&mut self, n: Node) -> usize {
        self.nodes.push(n);
        self.nodes.len() - 1
    }
}

/// The bound an atom term with coefficient `a` reads (the side of its greatest contribution),
/// and the bound it writes.
fn read_of(v: usize, a: &Int) -> usize {
    2 * v + usize::from(a.is_positive())
}
fn write_of(v: usize, a: &Int) -> usize {
    2 * v + usize::from(a.is_negative())
}

/// A union-find over name indexes with offsets: `v = parent + offset`.
struct Offsets {
    parent: Vec<usize>,
    off: Vec<Int>,
}

impl Offsets {
    fn new(n: usize) -> Offsets {
        Offsets {
            parent: (0..n).collect(),
            off: vec![Int::ZERO; n],
        }
    }

    /// The root of `v` and `v - root`, compressing the path.
    fn find(&mut self, v: usize) -> (usize, Int) {
        let mut path = Vec::new();
        let mut r = v;
        while self.parent[r] != r {
            path.push(r);
            r = self.parent[r];
        }
        // From the node next to the root down, each offset made relative to the root.
        let mut acc = Int::ZERO;
        for &u in path.iter().rev() {
            acc = &acc + &self.off[u];
            self.off[u] = acc.clone();
            self.parent[u] = r;
        }
        let o = if v == r {
            Int::ZERO
        } else {
            self.off[v].clone()
        };
        (r, o)
    }

    /// Records `a = b + d`.
    fn union(&mut self, a: usize, b: usize, d: &Int) {
        let (ra, oa) = self.find(a);
        let (rb, ob) = self.find(b);
        if ra != rb {
            self.parent[ra] = rb;
            self.off[ra] = &(&ob + d) - &oa;
        }
    }
}

/// A plain union-find over name indexes.
fn root(p: &mut [usize], mut v: usize) -> usize {
    while p[v] != v {
        p[v] = p[p[v]];
        v = p[v];
    }
    v
}

/// Whether `test` is in the class; when it is not, the message, with `text(id)` the program's
/// text of an atom, case or part, and `outcome` the outcome the test narrows by.
pub(crate) fn check(test: &Test, outcome: bool, text: &dyn Fn(usize) -> String) -> Option<Looped> {
    // A part of two cases on two names or more can fail (i) or (iii); with none, nothing can.
    let multi = |p: &Part| {
        let names: BTreeSet<&Atom> = (p.cases.iter())
            .flat_map(|c| c.atoms.iter().flat_map(|(_, l)| l.terms.keys()))
            .collect();
        names.len() >= 2
    };
    if !test.parts.iter().any(multi) {
        return None;
    }
    // The names, by index.
    let mut index: BTreeMap<Arc<str>, usize> = BTreeMap::new();
    let mut names: Vec<Arc<str>> = Vec::new();
    let lins = (test.base.iter().map(|(_, l)| l)).chain(
        test.parts
            .iter()
            .flat_map(|p| p.cases.iter().flat_map(|c| c.atoms.iter().map(|(_, l)| l))),
    );
    for l in lins {
        for a in l.terms.keys() {
            let Atom::Sym(n) = a else { return None };
            index.entry(n.clone()).or_insert_with(|| {
                names.push(n.clone());
                names.len() - 1
            });
        }
    }
    let k = names.len();
    // The offset equalities of the base, written as one atom (two opposite `>=`) or two.
    let mut uf = Offsets::new(k);
    let mut diffs: BTreeMap<(usize, usize), BTreeSet<Int>> = BTreeMap::new();
    for (_, l) in &test.base {
        let t: Vec<(usize, &Int)> = (l.terms.iter())
            .map(|(a, c)| match a {
                Atom::Sym(n) => (index[n], c),
                _ => unreachable!("checked above"),
            })
            .collect();
        if let [(p, cp), (n, cn)] = t[..] {
            let (p, n) = match (cp.to_i128(), cn.to_i128()) {
                (Some(1), Some(-1)) => (p, n),
                (Some(-1), Some(1)) => (n, p),
                _ => continue,
            };
            // `p - n + c >= 0`; with `n - p - c >= 0` too, `p = n - c`.
            if (diffs.get(&(n, p))).is_some_and(|cs| cs.contains(&-&l.constant)) {
                uf.union(p, n, &-&l.constant);
            }
            diffs.entry((p, n)).or_default().insert(l.constant.clone());
        }
    }
    // The atoms over the roots.
    let mut atoms: Vec<A> = Vec::new();
    let mut put = |uf: &mut Offsets, l: &Lin, part: usize, case: usize, text: usize| {
        let mut terms: BTreeMap<usize, Int> = BTreeMap::new();
        let mut c = l.constant.clone();
        for (a, x) in &l.terms {
            let Atom::Sym(n) = a else { unreachable!() };
            let (r, o) = uf.find(index[n]);
            c = &c + &(x * &o);
            let e = terms.entry(r).or_insert(Int::ZERO);
            *e = &*e + x;
        }
        terms.retain(|_, x| !x.is_zero());
        if !terms.is_empty() {
            atoms.push(A {
                terms: terms.into_iter().collect(),
                c,
                part,
                case,
                text,
            });
        }
    };
    for (t, l) in &test.base {
        put(&mut uf, l, BASE, 0, *t);
    }
    for (pi, p) in test.parts.iter().enumerate() {
        for (ci, c) in p.cases.iter().enumerate() {
            for (t, l) in &c.atoms {
                put(&mut uf, l, pi, ci, *t);
            }
        }
    }
    // Each root's box: the meet of its names' boxes moved by their offsets.
    let mut lo: Vec<Option<i128>> = vec![None; k];
    let mut hi: Vec<Option<i128>> = vec![None; k];
    for (v, name) in names.iter().enumerate() {
        let (r, o) = uf.find(v);
        let Some(o) = o.to_i128() else { continue };
        let (l, h, _) = &test.boxes[name];
        if let Some(l) = l {
            lo[r] = Some(lo[r].map_or(l - o, |x| x.max(l - o)));
        }
        if let Some(h) = h {
            hi[r] = Some(hi[r].map_or(h - o, |x| x.min(h - o)));
        }
    }
    // The parts on one name (holes) add no edge.
    let mut part_names: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); test.parts.len()];
    for a in &atoms {
        if a.part != BASE {
            part_names[a.part].extend(a.terms.iter().map(|(v, _)| *v));
        }
    }
    // A part with a case that holds on the whole box narrows nothing, now or after any
    // narrowing: the join of its cases in a box B holds all of B, and in any box B' within B
    // that case still holds everywhere. Such a part adds no edge, so a test such as
    // `z2 <= 6 && … && (2 * a + b >= 7 || z2 <= 8)` is not rejected for a loop through a choice
    // that always holds. The box here is the scope's, met with the base's atoms on one name.
    // Complexity tradeoff: naive, the part's join computed and compared with the box, a
    // narrowing per case; here a case is read off its atoms' least values on the box, O(its
    // terms), O(N) for the test.
    let (mut blo, mut bhi) = (lo.clone(), hi.clone());
    for a in atoms.iter().filter(|a| a.part == BASE) {
        let [(v, x)] = &a.terms[..] else { continue };
        let (Some(x), Some(c)) = (x.to_i128(), a.c.to_i128()) else {
            continue;
        };
        // `x * v + c >= 0`.
        if x > 0 {
            let l = (-c).div_euclid(x) + i128::from((-c).rem_euclid(x) != 0);
            blo[*v] = Some(blo[*v].map_or(l, |y| y.max(l)));
        } else {
            let h = c.div_euclid(-x);
            bhi[*v] = Some(bhi[*v].map_or(h, |y| y.min(h)));
        }
    }
    let least = |a: &A| -> Option<i128> {
        let mut m = a.c.to_i128()?;
        for (v, x) in &a.terms {
            let x = x.to_i128()?;
            let end = if x > 0 { blo[*v]? } else { bhi[*v]? };
            m = m.checked_add(x.checked_mul(end)?)?;
        }
        Some(m)
    };
    let mut holds: BTreeMap<(usize, usize), bool> = BTreeMap::new();
    for a in atoms.iter().filter(|a| a.part != BASE) {
        let whole = test.parts[a.part].cases[a.case].whole;
        let h = holds.entry((a.part, a.case)).or_insert(whole);
        *h = *h && least(a).is_some_and(|m| m >= 0);
    }
    let mut skip: Vec<bool> = part_names.iter().map(|n| n.len() < 2).collect();
    for (&(p, _), &h) in &holds {
        skip[p] |= h;
    }
    let live = |a: &A| a.part == BASE || !skip[a.part];
    // The bounds the box or an atom can make finite: a write is finite once every read but
    // its own is (a Horn fixpoint, one counter per atom, O(N)).
    let mut finite = vec![false; 2 * k];
    for v in 0..k {
        finite[2 * v] = lo[v].is_some();
        finite[2 * v + 1] = hi[v].is_some();
    }
    let mut readers: Vec<Vec<usize>> = vec![Vec::new(); 2 * k];
    let mut unknown: Vec<usize> = vec![0; atoms.len()];
    let mut queue: Vec<usize> = Vec::new();
    for (i, a) in atoms.iter().enumerate() {
        for (v, x) in &a.terms {
            readers[read_of(*v, x)].push(i);
            unknown[i] += usize::from(!finite[read_of(*v, x)]);
        }
        if unknown[i] <= 1 {
            queue.push(i);
        }
    }
    // Only the bounds made finite here are read off: the counts started from the box.
    let mut work: Vec<usize> = Vec::new();
    loop {
        if let Some(i) = queue.pop() {
            let a = &atoms[i];
            for (v, x) in &a.terms {
                let own_unknown = !finite[read_of(*v, x)];
                let w = write_of(*v, x);
                if (unknown[i] == 0 || (unknown[i] == 1 && own_unknown)) && !finite[w] {
                    finite[w] = true;
                    work.push(w);
                }
            }
            continue;
        }
        let Some(b) = work.pop() else { break };
        for &i in &readers[b] {
            unknown[i] -= 1;
            if unknown[i] <= 1 {
                queue.push(i);
            }
        }
    }
    // The bound graph.
    let mut g = Graph {
        nodes: (0..2 * k).map(Node::Bound).collect(),
        edges: Vec::new(),
    };
    for (i, a) in atoms.iter().enumerate().filter(|(_, a)| live(a)) {
        let t = &a.terms;
        let m = t.len();
        // pre[j] holds the reads of terms 0..=j, suf[j] those of j..m.
        let pre: Vec<usize> = (0..m).map(|_| g.add(Node::Atom(i))).collect();
        let suf: Vec<usize> = (0..m).map(|_| g.add(Node::Atom(i))).collect();
        for (j, (v, x)) in t.iter().enumerate() {
            let r = read_of(*v, x);
            if finite[r] {
                g.edges.push((r, pre[j], a.part));
                g.edges.push((r, suf[j], a.part));
            }
            if j > 0 {
                g.edges.push((pre[j - 1], pre[j], a.part));
            }
            if j + 1 < m {
                g.edges.push((suf[j + 1], suf[j], a.part));
            }
        }
        for (j, (v, x)) in t.iter().enumerate() {
            let w = write_of(*v, x);
            if !finite[w] {
                continue;
            }
            if j > 0 {
                g.edges.push((pre[j - 1], w, a.part));
            }
            if j + 1 < m {
                g.edges.push((suf[j + 1], w, a.part));
            }
        }
    }
    // The edges of the tests for being dead: from case c's reads to the other cases' writes.
    let mut by_case: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
    for (i, a) in atoms.iter().enumerate() {
        if a.part != BASE {
            by_case.entry((a.part, a.case)).or_default().push(i);
        }
    }
    for (pi, p) in test.parts.iter().enumerate() {
        if skip[pi] {
            continue;
        }
        let m = p.cases.len();
        let dead: Vec<usize> = (0..m).map(|c| g.add(Node::Dead(pi, c))).collect();
        let writes: Vec<usize> = (0..m).map(|c| g.add(Node::Writes(c))).collect();
        let pre: Vec<usize> = (0..m).map(|c| g.add(Node::Dead(pi, c))).collect();
        let suf: Vec<usize> = (0..m).map(|c| g.add(Node::Dead(pi, c))).collect();
        for c in 0..m {
            for &i in by_case.get(&(pi, c)).map_or(&[][..], |v| &v[..]) {
                for (v, x) in &atoms[i].terms {
                    let (r, w) = (read_of(*v, x), write_of(*v, x));
                    if finite[r] {
                        g.edges.push((r, dead[c], pi));
                    }
                    if finite[w] {
                        g.edges.push((writes[c], w, pi));
                    }
                }
            }
            g.edges.push((dead[c], pre[c], pi));
            g.edges.push((dead[c], suf[c], pi));
            if c > 0 {
                g.edges.push((pre[c - 1], pre[c], pi));
                g.edges.push((pre[c - 1], writes[c], pi));
            }
            if c + 1 < m {
                g.edges.push((suf[c + 1], suf[c], pi));
                g.edges.push((suf[c + 1], writes[c], pi));
            }
        }
    }
    let n = g.nodes.len();
    let mut out: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (e, &(u, _, _)) in g.edges.iter().enumerate() {
        out[u].push(e);
    }
    let comp = tarjan(n, &g.edges, &out);
    // The cases of each part that write each bound.
    let mut writers: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
    for a in atoms.iter().filter(|a| a.part != BASE && live(a)) {
        for (v, x) in &a.terms {
            let w = write_of(*v, x);
            if finite[w] {
                let cs = writers.entry((a.part, w)).or_default();
                if !cs.contains(&a.case) {
                    cs.push(a.case);
                }
            }
        }
    }
    // Whether each edge moves its bound when the loop runs: an edge into a bound that the base
    // or every case of its part writes, or one between the nodes of an atom. The edges of the
    // tests for being dead set a bound from one case only, and the join with the others keeps
    // it from moving further, so a loop through them is shown only when there is no other.
    let moving: Vec<bool> = (g.edges.iter())
        .map(|&(u, w, p)| match (g.nodes[u], g.nodes[w]) {
            (_, Node::Bound(_)) if p == BASE => true,
            (Node::Atom(_), Node::Bound(b)) => {
                (writers.get(&(p, b))).is_some_and(|cs| cs.len() == test.parts[p].cases.len())
            }
            (_, Node::Atom(_)) | (Node::Atom(_), _) => true,
            _ => false,
        })
        .collect();
    // (i): two edges of two parts in one strongly connected component, for each component, a
    // pair of moving edges when it has one; (iii): a bound two cases of a part write in a
    // cyclic one whose edges come from two sources or more, the base one source and each part
    // one. One pass over the edges.
    //
    // A cyclic component whose edges all come from one part is no loop of the narrowing. Its
    // cycles inside one case are a conjunction's, narrowed as the base's are; and narrowing a
    // box B by the part gives B' = hull(∪ Cᵢ ∩ B), where each Cᵢ ∩ B lies in B' and B' in B,
    // so Cᵢ ∩ B' = Cᵢ ∩ B and a second pass gives B' again: a case's test for being dead never
    // changes from the bounds its own part writes. Without this, the opposite of
    // `(x <= 2 || x >= 5) && x <= y`, the one part `x > 2 && x < 5 || x > y`, failed (iii) at
    // the least x, as did the `else` of every test of one `&&` chain of comparisons on two
    // names or more. Cost: one more word per component, O(1) per edge.
    let ncomp = comp.iter().max().map_or(0, |c| c + 1);
    let mut cyclic = vec![false; ncomp];
    let mut source: Vec<Option<usize>> = vec![None; ncomp];
    let mut mixed = vec![false; ncomp];
    let mut first: Vec<[Option<usize>; 2]> = vec![[None; 2]; ncomp];
    let mut pair: Vec<[Option<(usize, usize)>; 2]> = vec![[None; 2]; ncomp];
    for (e, &(u, v, p)) in g.edges.iter().enumerate() {
        if comp[u] != comp[v] {
            continue;
        }
        let c = comp[u];
        cyclic[c] = true;
        match source[c] {
            None => source[c] = Some(p),
            Some(q) if q != p => mixed[c] = true,
            Some(_) => {}
        }
        if p == BASE {
            continue;
        }
        for (m, on) in [(0, true), (1, moving[e])] {
            if !on || pair[c][m].is_some() {
                continue;
            }
            match first[c][m] {
                None => first[c][m] = Some(e),
                Some(f) if g.edges[f].2 != p => pair[c][m] = Some((f, e)),
                Some(_) => {}
            }
        }
    }
    // A name of each strongly connected component that holds a bound.
    let mut scc_name: Vec<Option<usize>> = vec![None; ncomp];
    for b in 0..2 * k {
        scc_name[comp[b]].get_or_insert(b / 2);
    }
    // The components of names joined by a shared atom.
    let mut cp: Vec<usize> = (0..k).collect();
    for a in &atoms {
        let r0 = root(&mut cp, a.terms[0].0);
        for (v, _) in &a.terms[1..] {
            let r = root(&mut cp, *v);
            cp[r] = r0;
        }
    }
    // The failures, by component of names: (i) before (iii), and of (i) a loop of moving edges
    // before any other.
    let mut fails: BTreeMap<usize, Fail> = BTreeMap::new();
    for c in 0..ncomp {
        let (Some(any), Some(v)) = (pair[c][0], scc_name[c]) else {
            continue;
        };
        let r = root(&mut cp, v);
        let new = match pair[c][1] {
            Some((e1, e2)) => Fail::Two(e1, e2, true),
            None => Fail::Two(any.0, any.1, false),
        };
        match fails.get(&r) {
            Some(Fail::Two(_, _, true)) => {}
            Some(Fail::Two(_, _, false)) if !matches!(new, Fail::Two(_, _, true)) => {}
            _ => {
                fails.insert(r, new);
            }
        }
    }
    for ((p, w), cs) in &writers {
        if cs.len() >= 2 && cyclic[comp[*w]] && mixed[comp[*w]] {
            let r = root(&mut cp, *w / 2);
            fails.entry(r).or_insert(Fail::Twice(*p, *w, cs[0], cs[1]));
        }
    }
    if fails.is_empty() {
        return None;
    }
    // A failing component of one of the two other kinds is in the class. Each atom is read
    // for the component it lies in alone: O(N log N) over all of them.
    let mut by_comp: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (i, a) in atoms.iter().enumerate() {
        let r = root(&mut cp, a.terms[0].0);
        if fails.contains_key(&r) {
            by_comp.entry(r).or_default().push(i);
        }
    }
    let lin = |a: &A| Lin {
        terms: (a.terms.iter())
            .map(|(v, x)| (Atom::Sym(names[*v].clone()), x.clone()))
            .collect(),
        constant: a.c.clone(),
    };
    let ge = |a: &A| {
        Formula::Con(Con {
            lin: lin(a),
            rel: Rel::Ge,
        })
    };
    let fail = fails.into_iter().find(|(c, _)| {
        let mut base: Vec<&A> = Vec::new();
        let mut parts: BTreeMap<usize, Vec<Vec<&A>>> = BTreeMap::new();
        for &i in &by_comp[c] {
            let a = &atoms[i];
            if a.part == BASE {
                base.push(a);
            } else {
                let cases = (parts.entry(a.part))
                    .or_insert_with(|| vec![Vec::new(); test.parts[a.part].cases.len()]);
                cases[a.case].push(a);
            }
        }
        let mut fs: Vec<Arc<Formula>> = base.iter().map(|a| Arc::new(ge(a))).collect();
        fs.extend(parts.values().map(|cases| {
            Arc::new(Formula::or(
                (cases.iter())
                    .map(|c| Formula::and(c.iter().map(|a| ge(a)).collect()))
                    .collect(),
            ))
        }));
        threshold::shape(&fs).is_none() && !octagonal(&base, &parts)
    });
    let (c, fail) = fail?;
    let mut by_part: Vec<Vec<usize>> = vec![Vec::new(); test.parts.len()];
    for (i, a) in atoms.iter().enumerate() {
        if a.part != BASE {
            by_part[a.part].push(i);
        }
    }
    // The names of the failing component, as the headline names them.
    let mut shown: Vec<String> = (0..names.len())
        .filter(|&v| root(&mut cp, v) == c)
        .map(|v| format!("`{}`", written_name(&names[v])))
        .collect();
    shown.sort();
    let say = Say {
        test,
        text,
        names: &names,
        atoms: &atoms,
        by_part: &by_part,
        g: &g,
        comp: &comp,
        out: &out,
        moving: &moving,
        finite: &finite,
        lo: &lo,
        hi: &hi,
    };
    Some(say.message(&fail, outcome, &shown))
}

/// Why a component is outside the class.
enum Fail {
    /// (i): edges of two parts, by edge index, in one strongly connected component, and
    /// whether both move their bounds.
    Two(usize, usize, bool),
    /// (iii): part `.0` writes bound `.1` from its cases `.2` and `.3`, in a cyclic component.
    Twice(usize, usize, usize, usize),
}

/// The strongly connected component of each node, by Tarjan's algorithm without recursion.
/// O(nodes + edges).
fn tarjan(n: usize, edges: &[(usize, usize, usize)], out: &[Vec<usize>]) -> Vec<usize> {
    const NONE: usize = usize::MAX;
    let mut idx = vec![NONE; n];
    let mut low = vec![0; n];
    let mut on = vec![false; n];
    let mut stack = Vec::new();
    let mut comp = vec![NONE; n];
    let mut next = 0;
    let mut nc = 0;
    for s in 0..n {
        if idx[s] != NONE {
            continue;
        }
        let mut call: Vec<(usize, usize)> = vec![(s, 0)];
        idx[s] = next;
        low[s] = next;
        next += 1;
        stack.push(s);
        on[s] = true;
        while let Some(&mut (v, ref mut i)) = call.last_mut() {
            if *i < out[v].len() {
                let w = edges[out[v][*i]].1;
                *i += 1;
                if idx[w] == NONE {
                    idx[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on[w] = true;
                    call.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(idx[w]);
                }
                continue;
            }
            call.pop();
            if let Some(&(u, _)) = call.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == idx[v] {
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    comp[w] = nc;
                    if w == v {
                        break;
                    }
                }
                nc += 1;
            }
        }
    }
    comp
}

/// Whether a component, its base atoms `base` and its parts `parts` (each case's atoms), is a
/// two-hub octagonal component with a dominating disjunction: two hub names `x`, `y`, base
/// bounds only on `x`, `y`, `x + y` and `x - y`; every other name a leaf with exactly one base
/// coupling `leaf >= f + c`, `f` one of those forms or its negation, and in no part; every part
/// `f >= a || g >= b` with one pair of forms for all parts; and one part with both the
/// greatest `a` and the greatest `b`. O(N log N).
fn octagonal(base: &[&A], parts: &BTreeMap<usize, Vec<Vec<&A>>>) -> bool {
    let unit = |x: &Int| matches!(x.to_i128(), Some(1 | -1));
    let mut hubs: BTreeSet<usize> = BTreeSet::new();
    // Each part as (form f, a, form g, b), a case `form - a >= 0`.
    type Form = (Vec<(usize, Int)>, Int);
    let mut read: Vec<[Form; 2]> = Vec::new();
    for cases in parts.values() {
        let [c0, c1] = &cases[..] else { return false };
        let ([a0], [a1]) = (&c0[..], &c1[..]) else {
            return false;
        };
        for a in [a0, a1] {
            if a.terms.len() > 2 || !a.terms.iter().all(|(_, x)| unit(x)) {
                return false;
            }
            hubs.extend(a.terms.iter().map(|(v, _)| *v));
        }
        read.push([(a0.terms.clone(), -&a0.c), (a1.terms.clone(), -&a1.c)]);
    }
    if hubs.len() != 2 {
        return false;
    }
    // One pair of forms for all parts, each part ordered to it.
    let (f, g) = (read[0][0].0.clone(), read[0][1].0.clone());
    let mut ab: Vec<(Int, Int)> = Vec::new();
    for [(f1, a1), (g1, b1)] in read {
        if f1 == f && g1 == g {
            ab.push((a1, b1));
        } else if f1 == g && g1 == f {
            ab.push((b1, a1));
        } else {
            return false;
        }
    }
    let top_a = ab.iter().map(|(a, _)| a).max().expect("a part");
    let top_b = ab.iter().map(|(_, b)| b).max().expect("a part");
    if !ab.iter().any(|(a, b)| a == top_a && b == top_b) {
        return false;
    }
    // The base: forms over the hubs, and one coupling for each leaf.
    let mut leaves: BTreeSet<usize> = BTreeSet::new();
    for a in base {
        if !a.terms.iter().all(|(_, x)| unit(x)) {
            return false;
        }
        let (on_hubs, off): (Vec<_>, Vec<_>) = a.terms.iter().partition(|(v, _)| hubs.contains(v));
        match &off[..] {
            [] => {}
            [(l, x)] if x.is_positive() && on_hubs.len() <= 2 && !on_hubs.is_empty() => {
                if !leaves.insert(*l) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// The message for a component outside the class, from the graph that decided it. Built only
/// for a test the checker rejects, once; each step costs O(N log N) at most.
struct Say<'t> {
    test: &'t Test,
    text: &'t dyn Fn(usize) -> String,
    names: &'t [Arc<str>],
    atoms: &'t [A],
    /// The atoms of each part.
    by_part: &'t [Vec<usize>],
    g: &'t Graph,
    comp: &'t [usize],
    out: &'t [Vec<usize>],
    moving: &'t [bool],
    finite: &'t [bool],
    lo: &'t [Option<i128>],
    hi: &'t [Option<i128>],
}

/// A link of a loop: bound `from` limits bound `to`, through an atom, or through the test for
/// being dead of case `dead` of part `part`, when case `by` then sets `to`.
#[derive(Clone)]
enum Link {
    Atom {
        from: usize,
        to: usize,
        atom: usize,
    },
    Dead {
        from: usize,
        to: usize,
        part: usize,
        dead: usize,
        by: usize,
    },
}

impl Link {
    fn from(&self) -> usize {
        match self {
            Link::Atom { from, .. } | Link::Dead { from, .. } => *from,
        }
    }

    fn to(&self) -> usize {
        match self {
            Link::Atom { to, .. } | Link::Dead { to, .. } => *to,
        }
    }

    fn part(&self, atoms: &[A]) -> usize {
        match self {
            Link::Atom { atom, .. } => atoms[*atom].part,
            Link::Dead { part, .. } => *part,
        }
    }
}

/// `n` with a comma between each group of three digits: `-1,000`.
fn grouped(n: i128) -> String {
    let d = n.unsigned_abs().to_string();
    let mut s = String::new();
    for (i, ch) in d.chars().enumerate() {
        if i > 0 && (d.len() - i).is_multiple_of(3) {
            s.push(',');
        }
        s.push(ch);
    }
    if n < 0 { format!("-{s}") } else { s }
}

/// `items` joined by commas and a last "and".
fn and_list(items: &[String]) -> String {
    match items.split_last() {
        None => String::new(),
        Some((last, [])) => last.clone(),
        Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
    }
}

impl Say<'_> {
    /// The written name of name index `v`.
    fn name(&self, v: usize) -> &str {
        written_name(&self.names[v])
    }

    /// "the least x" or "the largest x".
    fn bound(&self, b: usize) -> String {
        let side = if b.is_multiple_of(2) {
            "least"
        } else {
            "largest"
        };
        format!("the {side} {}", self.name(b / 2))
    }

    /// What atom `i` makes of the bound it writes through its term on name `v`: "makes the
    /// least possible x at least the least possible y plus 1".
    fn effect(&self, i: usize, v: usize) -> String {
        let a = &self.atoms[i];
        let x = &a
            .terms
            .iter()
            .find(|(u, _)| *u == v)
            .expect("a term of the atom")
            .1;
        let lower = x.is_positive();
        let mut parts: Vec<String> = Vec::new();
        for (u, y) in a.terms.iter().filter(|(u, _)| *u != v) {
            // The other term moved across: -y*u over a lower bound, y*u over an upper one.
            let m = if lower { -y } else { y.clone() };
            let side = if m.is_positive() == lower {
                "least"
            } else {
                "largest"
            };
            let word = format!("the {side} possible {}", self.name(*u));
            let mag = if m.is_negative() { -&m } else { m.clone() };
            let term = match mag.to_i128() {
                Some(1) => word,
                _ => format!("{mag} times {word}"),
            };
            parts.push(match (parts.is_empty(), m.is_negative()) {
                (true, false) => term,
                (true, true) => format!("minus {term}"),
                (false, false) => format!("plus {term}"),
                (false, true) => format!("minus {term}"),
            });
        }
        let k = if lower { -&a.c } else { a.c.clone() };
        if parts.is_empty() {
            parts.push(k.to_string());
        } else if k.is_positive() {
            parts.push(format!("plus {k}"));
        } else if k.is_negative() {
            parts.push(format!("minus {}", -&k));
        }
        let mut e = parts.join(" ");
        let d = if x.is_negative() { -x } else { x.clone() };
        if d.to_i128() != Some(1) {
            e = format!("{e}, divided by {d}");
        }
        let (side, rel) = if lower {
            ("least", "at least")
        } else {
            ("largest", "at most")
        };
        format!("makes the {side} possible {} {rel} {e}", self.name(v))
    }

    /// What the alternatives of part `p` do: "`x - y >= 1` makes …; `x >= 0` makes …".
    fn choice(&self, p: usize) -> String {
        let part = &self.test.parts[p];
        let mut effects: Vec<Vec<String>> = vec![Vec::new(); part.cases.len()];
        for &i in &self.by_part[p] {
            let a = &self.atoms[i];
            for (v, x) in &a.terms {
                if self.finite[write_of(*v, x)] {
                    effects[a.case].push(self.effect(i, *v));
                }
            }
        }
        let says: Vec<String> = (part.cases.iter().zip(&effects))
            .map(|(c, e)| {
                let what = match e.is_empty() {
                    true => "sets no limit on its own".to_string(),
                    false => and_list(e),
                };
                format!("`{}` {what}", (self.text)(c.text))
            })
            .collect();
        format!(
            "the choice `{}`: {}",
            (self.text)(part.text),
            says.join("; ")
        )
    }

    /// A shortest path from `s` to `t` inside the strongly connected component of `s`, by the
    /// edges `ok` allows: the nodes after `s`, ending with `t`. O(m log m) for the m edges of
    /// the component.
    fn path(&self, s: usize, t: usize, ok: &dyn Fn(usize) -> bool) -> Option<Vec<usize>> {
        let c = self.comp[s];
        let mut prev: BTreeMap<usize, usize> = BTreeMap::new();
        let mut q = VecDeque::from([s]);
        while let Some(u) = q.pop_front() {
            for &e in &self.out[u] {
                let w = self.g.edges[e].1;
                if self.comp[w] != c || !ok(e) || w == s || prev.contains_key(&w) {
                    continue;
                }
                prev.insert(w, u);
                if w == t {
                    let mut p = vec![t];
                    let mut x = t;
                    while prev[&x] != s {
                        x = prev[&x];
                        p.push(x);
                    }
                    p.reverse();
                    return Some(p);
                }
                q.push_back(w);
            }
        }
        None
    }

    /// The links of the closed walk `walk` (nodes, the last joined to the first), read from a
    /// bound on it.
    fn links(&self, walk: &[usize]) -> Vec<Link> {
        let start = (walk.iter())
            .position(|&x| matches!(self.g.nodes[x], Node::Bound(_)))
            .expect("a cycle passes through a bound");
        let w: Vec<usize> = walk[start..]
            .iter()
            .chain(&walk[..start])
            .copied()
            .collect();
        let mut out = Vec::new();
        let mut i = 0;
        while i < w.len() {
            let Node::Bound(from) = self.g.nodes[w[i]] else {
                unreachable!("each link starts at a bound")
            };
            let (mut atom, mut dead, mut by) = (None, None, None);
            let mut j = i + 1;
            loop {
                match self.g.nodes[w[j % w.len()]] {
                    Node::Bound(to) => {
                        out.push(match (atom, dead, by) {
                            (Some(atom), _, _) => Link::Atom { from, to, atom },
                            (None, Some((part, dead)), Some(by)) => Link::Dead {
                                from,
                                to,
                                part,
                                dead,
                                by,
                            },
                            _ => unreachable!("an edge between bounds is an atom's or a case's"),
                        });
                        break;
                    }
                    Node::Atom(a) => atom = atom.or(Some(a)),
                    Node::Dead(p, c) => dead = dead.or(Some((p, c))),
                    Node::Writes(c) => by = Some(c),
                }
                j += 1;
            }
            i = j;
        }
        out
    }

    /// The links of a loop through edges `e1` and `e2` of one strongly connected component, by
    /// moving edges ([`check`]) when it can be.
    fn cycle_through(&self, e1: usize, e2: usize) -> Vec<Link> {
        let (u1, v1, _) = self.g.edges[e1];
        let (u2, v2, _) = self.g.edges[e2];
        let walk = |ok: &dyn Fn(usize) -> bool| -> Option<Vec<usize>> {
            let mut walk = vec![u1, v1];
            if v1 != u2 {
                walk.extend(self.path(v1, u2, ok)?);
            }
            if v2 != u1 {
                walk.push(v2);
                let back = self.path(v2, u1, ok)?;
                walk.extend(&back[..back.len() - 1]);
            }
            Some(walk)
        };
        let w = walk(&|e| self.moving[e]).or_else(|| walk(&|_| true));
        self.links(&w.expect("both edges lie in one strongly connected component"))
    }

    /// The links of a shortest loop through bound `b`, by moving edges when it can be: one
    /// search from `b`, which stops at the first edge back to it. O(m log m).
    fn cycle_at(&self, b: usize) -> Vec<Link> {
        let c = self.comp[b];
        let walk = |ok: &dyn Fn(usize) -> bool| -> Option<Vec<usize>> {
            let mut prev: BTreeMap<usize, usize> = BTreeMap::new();
            let mut q = VecDeque::from([b]);
            while let Some(u) = q.pop_front() {
                for &e in &self.out[u] {
                    let w = self.g.edges[e].1;
                    if self.comp[w] != c || !ok(e) {
                        continue;
                    }
                    if w == b {
                        let mut p = vec![u];
                        let mut x = u;
                        while x != b {
                            x = prev[&x];
                            p.push(x);
                        }
                        p.reverse();
                        return Some(p);
                    }
                    if prev.contains_key(&w) {
                        continue;
                    }
                    prev.insert(w, u);
                    q.push_back(w);
                }
            }
            None
        };
        let w = walk(&|e| self.moving[e]).or_else(|| walk(&|_| true));
        self.links(&w.expect("a cyclic component holds a loop through each of its nodes"))
    }

    /// The sentence of a link.
    fn link(&self, l: &Link) -> String {
        match l {
            Link::Atom { to, atom, .. } => format!(
                "`{}` {}",
                (self.text)(self.atoms[*atom].text),
                self.effect(*atom, to / 2)
            ),
            Link::Dead {
                from,
                to,
                part,
                dead,
                by,
            } => {
                let p = &self.test.parts[*part];
                format!(
                    "whether `{}` can hold depends on {}, and when it cannot, `{}` sets {} alone",
                    (self.text)(p.cases[*dead].text),
                    self.bound(*from),
                    (self.text)(p.cases[*by].text),
                    self.bound(*to)
                )
            }
        }
    }

    /// "the least x limits the least y, which limits the least x: <links>".
    fn loop_text(&self, links: &[Link]) -> String {
        let mut s = format!(
            "{} limits {}",
            self.bound(links[0].from()),
            self.bound(links[0].to())
        );
        for l in &links[1..] {
            s.push_str(&format!(", which limits {}", self.bound(l.to())));
        }
        let ls: Vec<String> = links.iter().map(|l| self.link(l)).collect();
        format!("{s}: {}", ls.join("; "))
    }

    /// For a loop of differences of two names, all on one side of their bounds, that moves
    /// them each time around: what one time around changes, and about how many times the
    /// answer would take. `None` for any other loop, or when a number does not fit.
    fn numbers(&self, links: &[Link]) -> Option<(String, String)> {
        let side = links[0].from() % 2;
        let mut gain: i128 = 0;
        let mut steps: Vec<(usize, i128)> = Vec::new();
        for l in links {
            let Link::Atom { from, to, atom } = l else {
                return None;
            };
            let a = &self.atoms[*atom];
            let unit = |x: &Int| matches!(x.to_i128(), Some(1 | -1));
            if from % 2 != side || to % 2 != side || a.terms.len() != 2 {
                return None;
            }
            if !a.terms.iter().all(|(_, x)| unit(x)) {
                return None;
            }
            let c = a.c.to_i128()?;
            // `to - from + c >= 0` on least values: least(to) >= least(from) - c; on largest
            // values `from - to + c >= 0`: largest(to) <= largest(from) + c.
            let d = if side == 0 { c.checked_neg()? } else { c };
            gain = gain.checked_add(d)?;
            steps.push((*to, d));
        }
        if (side == 0 && gain <= 0) || (side == 1 && gain >= 0) {
            return None;
        }
        let end = |b: usize| {
            if b.is_multiple_of(2) {
                self.lo[b / 2]
            } else {
                self.hi[b / 2]
            }
        };
        let other = |b: usize| {
            if b.is_multiple_of(2) {
                self.hi[b / 2]
            } else {
                self.lo[b / 2]
            }
        };
        let start = links[0].from();
        let v0 = end(start)?;
        let mut cur = v0;
        let mut seen = Vec::new();
        for _ in 0..2 {
            for &(b, d) in &steps {
                let x = cur.checked_add(d)?;
                cur = match end(b) {
                    Some(e) if side == 0 => x.max(e),
                    Some(e) => x.min(e),
                    None => x,
                };
            }
            seen.push(cur);
        }
        // Where the loop stops: the other end of the start's range, or where another
        // alternative of a link's choice, a bound on the link's name alone, holds the bound.
        let mut limit = other(start)?;
        let mut off: i128 = 0;
        for (l, &(_, d)) in links.iter().zip(&steps) {
            off = off.checked_add(d)?;
            let Link::Atom { to, atom, .. } = l else {
                continue;
            };
            let (p, case) = (self.atoms[*atom].part, self.atoms[*atom].case);
            if p == BASE {
                continue;
            }
            for &i in &self.by_part[p] {
                let a = &self.atoms[i];
                let [(v, x)] = &a.terms[..] else { continue };
                if a.case == case || *v != to / 2 || write_of(*v, x) != *to {
                    continue;
                }
                let (xc, cc) = (x.to_i128()?, a.c.to_i128()?);
                // `xc * v + cc >= 0`: v >= ceil(-cc / xc), or v <= floor(cc / -xc).
                let at = match side {
                    0 => (cc.checked_neg()?).div_euclid(xc) + i128::from((-cc).rem_euclid(xc) != 0),
                    _ => cc.div_euclid(xc.checked_neg()?),
                };
                let at_start = at.checked_sub(off)?;
                limit = if side == 0 {
                    limit.min(at_start)
                } else {
                    limit.max(at_start)
                };
            }
        }
        let times = (limit.checked_sub(v0)?.checked_abs()? + gain.abs() - 1) / gain.abs();
        if times < 2 {
            return None;
        }
        let verb = if side == 0 { "rises" } else { "falls" };
        let change = format!(
            "one time around the loop changes {} by {}: it {verb} from {} to {}, then {}",
            self.bound(start),
            grouped(gain.abs()),
            grouped(v0),
            grouped(seen[0]),
            grouped(seen[1])
        );
        let ranges: Vec<String> = (links.iter().map(|l| l.from() / 2))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|v| format!("`{}: {}`", self.name(v), self.test.boxes[&self.names[v]].2))
            .collect();
        let count = format!(
            "the answer would take about {} times around it, a number that grows with the \
             ranges {} and not with the program",
            grouped(times),
            and_list(&ranges)
        );
        Some((change, count))
    }

    /// The test rewritten: the choices `nest` as nested `if` / `else if` on their alternatives,
    /// inside an `if` on the rest of the test as written.
    fn repair(&self, nest: &[usize], outcome: bool) -> String {
        fn lines(say: &Say, nest: &[usize], indent: &str, out: &mut Vec<String>) {
            let Some((&p, rest)) = nest.split_first() else {
                out.push(format!("{indent}…"));
                return;
            };
            for (i, c) in say.test.parts[p].cases.iter().enumerate() {
                let open = if i == 0 { "if" } else { "} else if" };
                out.push(format!("{indent}{open} {} {{", (say.text)(c.text)));
                lines(say, rest, &format!("{indent}    "), out);
            }
            out.push(format!("{indent}}}"));
        }
        let on: BTreeSet<usize> = nest.iter().copied().collect();
        let mut off: Vec<String> = self.test.kept.iter().map(|&t| (self.text)(t)).collect();
        off.extend(
            (0..self.test.parts.len())
                .filter(|p| !on.contains(p))
                .map(|p| format!("({})", (self.text)(self.test.parts[p].text))),
        );
        let mut out = Vec::new();
        if off.is_empty() {
            lines(self, nest, "", &mut out);
        } else {
            out.push(format!("if {} {{", off.join(" && ")));
            lines(self, nest, "    ", &mut out);
            out.push("}".to_string());
        }
        let choices: Vec<String> = (nest.iter())
            .map(|&p| format!("`{}`", (self.text)(self.test.parts[p].text)))
            .collect();
        format!(
            "repair: write the choice {} as an `if` on its alternatives, inside an `if` on the \
             rest of the test, so that no loop of limits passes through it, with the body of \
             the {} at each `…`:\n{}",
            and_list(&choices),
            if outcome { "`if`" } else { "`else`" },
            out.join("\n")
        )
    }

    /// The message for `fail`, a test narrowed by `outcome`, whose failing component holds
    /// the names `shown`.
    fn message(&self, fail: &Fail, outcome: bool, shown: &[String]) -> Looped {
        let (links, mut nest, reason): (_, Vec<usize>, _) = match fail {
            Fail::Two(e1, e2, _) => {
                let links = self.cycle_through(*e1, *e2);
                let mut reason = vec![format!(
                    "these choices form a loop of limits: {}",
                    self.loop_text(&links)
                )];
                match self.numbers(&links) {
                    Some((change, count)) => reason.extend([change, count]),
                    None => reason.push(
                        "each time around the loop can move these limits again, and the number \
                         of times the answer would take grows with the ranges of the names and \
                         not with the program"
                            .to_string(),
                    ),
                }
                reason.push(
                    "the checker does no work whose amount depends on the values in the ranges \
                     rather than on the program text, so it rejects this test instead of \
                     running the loop"
                        .to_string(),
                );
                (links, Vec::new(), reason)
            }
            Fail::Twice(p, w, c1, c2) => {
                let links = self.cycle_at(*w);
                let part = &self.test.parts[*p];
                let (t1, t2) = (
                    (self.text)(part.cases[*c1].text),
                    (self.text)(part.cases[*c2].text),
                );
                let which = if w % 2 == 0 { "smaller" } else { "larger" };
                let b = self.bound(*w);
                let reason = vec![
                    format!(
                        "the choice `{}` sets {b} through two of its alternatives, `{t1}` and \
                         `{t2}`, so {b} is the {which} of the two",
                        (self.text)(part.text),
                    ),
                    format!("{b} lies on a loop of limits: {}", self.loop_text(&links)),
                    format!(
                        "after the loop settles, `{t1}` or `{t2}` would change {b} again, so \
                         the loop would have to be run again, a number of times that grows \
                         with the ranges of the names and not with the program; the checker \
                         does no work whose amount depends on the values in the ranges rather \
                         than on the program text, so it rejects this test"
                    ),
                ];
                (links, vec![*p], reason)
            }
        };
        // One choice on the loop is rewritten, the first as written: an `if` on its
        // alternatives breaks every loop through it, and the rest of the test stays one `if`.
        // Complexity tradeoff: nesting every choice on the loop, as each arm narrowing by `&&`
        // alone would need, prints the product of their numbers of alternatives, 2^k for a loop
        // of k choices of two; one choice prints the test once, O(its size). A loop left
        // through other choices gets its own message on the repaired program. Test:
        // `l01_39_reduced_product::loops::classifying_a_chain_of_choices_scales`.
        // The steps describe every choice on the loop, in the order of its links: O(L log L)
        // for a loop of L links.
        let mut on_loop: Vec<usize> = nest.clone();
        let mut seen: BTreeSet<usize> = nest.iter().copied().collect();
        for l in &links {
            let p = l.part(self.atoms);
            if p != BASE && seen.insert(p) {
                on_loop.push(p);
            }
        }
        if nest.is_empty() {
            nest.extend(on_loop.iter().copied().min());
        }
        let place = match outcome {
            true => "inside this `if`",
            false => "inside the `else` of this `if`",
        };
        // Where the test fails it is read as its negation, whose choices the steps print.
        let (read, there) = match outcome {
            true => ("the test is", "where it holds"),
            false => ("where the test fails, it is read as its opposite,", "there"),
        };
        let mut steps = vec![format!(
            "{read} a list of choices joined by `&&`, each a set of alternatives joined by \
             `||`: {there}, at least one alternative of each choice holds, and the checker \
             narrows each name's range to the values some combination of alternatives allows"
        )];
        steps.extend(on_loop.iter().map(|&p| self.choice(p)));
        steps.extend(reason);
        Looped {
            headline: format!(
                "The ranges of {} {place} cannot be worked out",
                and_list(shown)
            ),
            steps,
            repair: self.repair(&nest, outcome),
        }
    }
}
