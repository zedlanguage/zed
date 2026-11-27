//! REFUSAL-front-u6-subset: a list for the escape solve when the atoms at some place cross, so
//! the laminar 2-SAT of [`super::decide_counted`] does not apply ([`super::forest`] gives
//! `None`). It looks for a list only and never answers `Empty`: its last step refuses what it
//! cannot reduce, and a crossing family with two atoms a row holds 3-colouring (module doc of
//! `escape`), so no polynomial method decides every case.
//!
//! The problem. Each place `j` takes one value of `pl[j]`; each clause, two atoms `(j1, A)` and
//! `(j2, B)` at two places, holds when `x_j1 ∈ A` or `x_j2 ∈ B`. That is a binary constraint
//! network (a constraint per pair of places, on their values), read in five steps.
//!
//! 1. The values. At a place, two values in the same atoms are interchangeable, and a value in
//!    every atom another value is in is at least as good (every literal is positive), so the
//!    place keeps one value per set of atoms, and of those only the sets no other set contains.
//!    Every value the atoms write and every value `pl[j]` writes, if in `pl[j]`, and, when
//!    `pl[j]` is cofinite, one value no set writes (all such values are in the same atoms: the
//!    cofinite ones) cover every set of atoms a value of `pl[j]` is in.
//! 2. The relations. One table per pair of places, the pairs of values that hold every clause
//!    on the two places.
//! 3. The reductions, to a fixed point, each keeping a list of the reduced network extendable
//!    to the network before it (the unwinding below proves it):
//!    - arc consistency: drop a value with no partner in some neighbour (Mackworth 1977, AC-3);
//!    - an edge whose table holds every pair of values alive is dropped;
//!    - a value allowed with every value alive of every neighbour fixes its place, which leaves
//!      the network (degree 0 included);
//!    - a place with one neighbour leaves it, its neighbour keeping the values with a partner
//!      (Freuder 1982: a tree is solved without backtracking once arc consistent, from the
//!      leaves in);
//!    - a place with two neighbours leaves it, the pair of neighbours joined by the table of the
//!      pairs with a common partner (the composition of the two tables, met with any table the
//!      pair has already).
//! 4. What is left. If a place still has three values or more, `None`: the core is refused. Else
//!    each place is a Boolean variable (one value: forced), each forbidden pair of an edge a
//!    clause of two literals, and 2-SAT decides it (`TwoSat::solve`, Aspvall, Plass and Tarjan
//!    1979, quoted there). No model: `None`.
//! 5. The unwinding, last reduction first: a fixed place takes its value; a place with one
//!    neighbour, a value its table allows with the neighbour's; a place with two neighbours, a
//!    value its two tables allow with both. Each exists: the neighbour's value was alive when the
//!    place left (values only die), and the reduction kept only values with a partner (one
//!    neighbour) or only pairs with a common partner (two). Each clause of the place was on one of
//!    those edges, and the place left with no other edge, so the list holds every clause.
//!
//! The answer is checked again by the caller: every refused row written is missed
//! (`orig_live`) and [`super::super::Searching::check_chain_witness`] reads the list against the
//! type itself. So a fault here can cost an answer, never give a wrong one.
//!
//! Sources. A. K. Mackworth, "Consistency in networks of relations", Artificial Intelligence
//! 8(1):99-118, 1977, doi:10.1016/0004-3702(77)90007-8 (AC-3, the arc revision used in step 3).
//! E. C. Freuder, "A sufficient condition for backtrack-free search", J. ACM 29(1):24-32, 1982,
//! doi:10.1145/322290.322292 (a tree-structured network is solved by arc consistency and one
//! pass from the leaves). The degree-two step is series reduction, the elimination of a
//! variable of degree two (Freuder's width 2 for a series-parallel network). The bib entries and
//! quotes are in verification/bib.md of the spec. Prior work: the gemini seat's prototype of
//! round 1 of REFUSAL-front-u6-subset (`structured_fork.rs`, Stage 3), which answers `Empty`
//! as well on no model under a truncation lemma; that half is not taken (the module doc of
//! `escape` lists when an `Empty` holds, and the fallback cannot keep it: a value can die in
//! step 1 or 3 because a clause wide at its fourth atom was cut). Departures from it: a place
//! of degree two is joined whatever its neighbours' sizes (the prototype asked both to have two
//! values or fewer; joining never adds an edge, and the composition costs the product of three
//! domains), and the reductions are driven by a work list of places, not by full passes.
//!
//! Cost. Let `d` be the most values a place keeps, `m_j` the atoms at place `j`, `W_j` the values
//! written at `j` and `E` the edges. Step 1: `O(W_j m_j log)` per place for the sets of atoms and
//! `O(d^2 m_j)` for the comparison. Step 2: `O(d^2)` per clause. Step 3: a place is looked at
//! again only after a change at it or a neighbour (a value dying, an edge dropped or joined, a
//! neighbour leaving), and a look costs `O(deg d^2)` (deg its neighbours); changes are at most
//! the values plus the edges plus the places, each waking at most `deg + 1` places, so
//! `O((V d + E) deg_max^2 d^2)` in all. Step 4: linear in the clauses, at most `d^2` per edge.
//! On the selector reduction of 3-SAT, `d <= 3`, and a variable's degree is the clauses it is
//! in. A place of high degree that is woken by each of its neighbours costs the square of its
//! degree, the case to watch; the module runs only where the forest failed, which answered
//! `None` (a refusal) before.
// Complexity tradeoff: the general method for a binary network is search, exponential in the
// places; the reductions here are polynomial and complete on networks whose constraint graph
// reduces to Boolean places by leaves and series steps (trees and series-parallel graphs of any
// domain, and any graph of Boolean places), and they refuse the rest. Naive alternative: the
// full passes of the prototype, which redo every edge each round, `O(V E d^2)`; the work list
// looks only where something changed.

use std::collections::{BTreeMap, BTreeSet};

use super::super::shared::TwoSat;
use super::Ints;
use crate::value::Value;

/// One step of the reductions, for the unwinding.
enum Left {
    /// The place took this value (step 3, a value allowed with every neighbour's).
    Fixed(usize, usize),
    /// The place `p` left with one neighbour `q` over edge `e`.
    Leaf { p: usize, q: usize, e: usize },
    /// The place `p` left with two neighbours `q1` and `q2` over edges `e1` and `e2`.
    Series {
        p: usize,
        q1: usize,
        e1: usize,
        q2: usize,
        e2: usize,
    },
}

/// The binary network: the values of each place, alive or not, and the tables of its edges.
struct Net {
    alive: Vec<Vec<bool>>,
    /// The edges: the two places (the first less than the second) and the table, `ok[a * d + b]`
    /// for value `a` of the first place and `b` of the second (`d` the second's count).
    edges: Vec<(usize, usize, Vec<bool>)>,
    /// The edges of each place in the network, by neighbour.
    adj: Vec<BTreeMap<usize, usize>>,
}

impl Net {
    /// Whether edge `e` allows value `a` at place `p` with value `b` at its other place.
    fn ok(&self, e: usize, p: usize, a: usize, b: usize) -> bool {
        let (u, v, ref t) = self.edges[e];
        let dv = self.alive[v].len();
        if p == u { t[a * dv + b] } else { t[b * dv + a] }
    }

    /// Whether place `p` has value `a` alive with a partner at `q` over edge `e`.
    fn supported(&self, e: usize, p: usize, a: usize, q: usize) -> bool {
        (0..self.alive[q].len()).any(|b| self.alive[q][b] && self.ok(e, p, a, b))
    }

    /// Kills the values of `p` with no partner at `q` over `e`; whether any died.
    fn revise(&mut self, e: usize, p: usize, q: usize) -> bool {
        let mut died = false;
        for a in 0..self.alive[p].len() {
            if self.alive[p][a] && !self.supported(e, p, a, q) {
                self.alive[p][a] = false;
                died = true;
            }
        }
        died
    }

    fn unlink(&mut self, p: usize, q: usize) {
        self.adj[p].remove(&q);
        self.adj[q].remove(&p);
    }
}

/// A list of values, one per place of `pl` (index 0 unused), each in its place's set, that holds
/// every clause `[i1, i2]` (`x_j ∈ A` for one of the atoms `atom[i] = (j, A)`), found as the
/// module doc says; `None` when the reductions leave a place of three values or more, a place
/// with no value, or a 2-SAT with no model. Every clause's two atoms are at two places: a row
/// meets each place once (the cells of `cells_windows`), and a merged clause of U1 holds the
/// fixed atom and the meet at the other place.
pub(super) fn crossing_witness(
    pl: &[Ints],
    atom: &[(usize, Ints)],
    clause: &[[usize; 2]],
) -> Option<Vec<Value>> {
    let n = pl.len();
    // The atoms at each place, and each atom's index among them.
    let mut at: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut local = vec![0; atom.len()];
    for (i, (j, _)) in atom.iter().enumerate() {
        local[i] = at[*j].len();
        at[*j].push(i);
    }

    // Step 1: the values kept at each place, with the atoms each is in.
    let mut kept: Vec<Vec<(Vec<bool>, Value)>> = vec![Vec::new(); n];
    for j in 1..n {
        if at[j].is_empty() {
            continue;
        }
        let mut written: BTreeSet<&Value> = pl[j].vals.iter().collect();
        for &i in &at[j] {
            written.extend(atom[i].1.vals.iter());
        }
        let mut values: Vec<Value> = (written.iter())
            .filter(|x| pl[j].contains(x))
            .map(|&x| x.clone())
            .collect();
        if pl[j].cof {
            let other = (0..)
                .map(Value::Int)
                .find(|x| !written.contains(x))
                .expect("finitely many values written");
            values.push(other);
        }
        let mut by_set: BTreeMap<Vec<bool>, Value> = BTreeMap::new();
        for x in values {
            let set: Vec<bool> = at[j].iter().map(|&i| atom[i].1.contains(&x)).collect();
            by_set.entry(set).or_insert(x);
        }
        let sets: Vec<(Vec<bool>, Value)> = by_set.into_iter().collect();
        // Keep a set unless another (distinct, so strictly larger) contains it.
        let within = |s: &[bool], t: &[bool]| s.iter().zip(t).all(|(&a, &b)| !a || b);
        kept[j] = (sets.iter().enumerate())
            .filter(|&(k, (s, _))| {
                !(sets.iter().enumerate()).any(|(l, (t, _))| l != k && within(s, t))
            })
            .map(|(_, sv)| sv.clone())
            .collect();
    }

    // Step 2: the tables.
    let mut net = Net {
        alive: kept.iter().map(|k| vec![true; k.len()]).collect(),
        edges: Vec::new(),
        adj: vec![BTreeMap::new(); n],
    };
    for &[i1, i2] in clause {
        let (mut u, mut iu, mut v, mut iv) = (atom[i1].0, i1, atom[i2].0, i2);
        debug_assert_ne!(u, v, "a clause's two atoms are at two places");
        if u > v {
            (u, iu, v, iv) = (v, iv, u, iu);
        }
        let (du, dv) = (kept[u].len(), kept[v].len());
        let e = *net.adj[u].entry(v).or_insert_with(|| {
            net.edges.push((u, v, vec![true; du * dv]));
            net.edges.len() - 1
        });
        net.adj[v].insert(u, e);
        let t = &mut net.edges[e].2;
        for a in 0..du {
            if kept[u][a].0[local[iu]] {
                continue;
            }
            for b in 0..dv {
                if !kept[v][b].0[local[iv]] {
                    t[a * dv + b] = false;
                }
            }
        }
    }

    // Step 3: the reductions, from a work list of places.
    let mut active: Vec<bool> = at.iter().map(|a| !a.is_empty()).collect();
    let mut work: BTreeSet<usize> = (1..n).filter(|&j| active[j]).collect();
    let mut left: Vec<Left> = Vec::new();
    while let Some(p) = work.pop_first() {
        if !active[p] {
            continue;
        }
        // Arc consistency at p, both ways, and the edges that allow every pair alive.
        let mut changed = false;
        let near: Vec<(usize, usize)> = net.adj[p].iter().map(|(&q, &e)| (q, e)).collect();
        for &(q, e) in &near {
            if net.revise(e, p, q) {
                changed = true;
            }
            if net.revise(e, q, p) {
                if !net.alive[q].contains(&true) {
                    return None;
                }
                work.insert(q);
                work.extend(net.adj[q].keys());
            }
        }
        if !net.alive[p].contains(&true) {
            return None;
        }
        if changed {
            work.insert(p);
            work.extend(net.adj[p].keys());
            continue;
        }
        for &(q, e) in &near {
            let all = (0..net.alive[p].len())
                .filter(|&a| net.alive[p][a])
                .all(|a| (0..net.alive[q].len()).all(|b| !net.alive[q][b] || net.ok(e, p, a, b)));
            if all {
                net.unlink(p, q);
                work.insert(q);
            }
        }
        // A value allowed with every neighbour's values.
        let free = (0..net.alive[p].len()).find(|&a| {
            net.alive[p][a]
                && net.adj[p].iter().all(|(&q, &e)| {
                    (0..net.alive[q].len()).all(|b| !net.alive[q][b] || net.ok(e, p, a, b))
                })
        });
        if let Some(a) = free {
            for q in std::mem::take(&mut net.adj[p]).into_keys() {
                net.adj[q].remove(&p);
                work.insert(q);
            }
            active[p] = false;
            left.push(Left::Fixed(p, a));
            continue;
        }
        let near: Vec<(usize, usize)> = net.adj[p].iter().map(|(&q, &e)| (q, e)).collect();
        match near[..] {
            [(q, e)] => {
                // Arc consistent, so every value of q has a partner at p: q keeps them all.
                net.unlink(p, q);
                active[p] = false;
                left.push(Left::Leaf { p, q, e });
                work.insert(q);
            }
            [(q1, e1), (q2, e2)] => {
                // The pairs of q1 and q2 with a common partner at p, met with their own edge.
                let (d1, d2) = (net.alive[q1].len(), net.alive[q2].len());
                let mut t = vec![true; d1 * d2];
                for b1 in 0..d1 {
                    for b2 in 0..d2 {
                        t[b1 * d2 + b2] = net.alive[q1][b1]
                            && net.alive[q2][b2]
                            && (0..net.alive[p].len()).any(|a| {
                                net.alive[p][a] && net.ok(e1, p, a, b1) && net.ok(e2, p, a, b2)
                            });
                    }
                }
                net.unlink(p, q1);
                net.unlink(p, q2);
                match net.adj[q1].get(&q2) {
                    Some(&e) => {
                        let flip = net.edges[e].0 != q1;
                        for b1 in 0..d1 {
                            for b2 in 0..d2 {
                                if !t[b1 * d2 + b2] {
                                    let k = if flip { b2 * d1 + b1 } else { b1 * d2 + b2 };
                                    net.edges[e].2[k] = false;
                                }
                            }
                        }
                    }
                    None => {
                        let (u, v, t) = if q1 < q2 {
                            (q1, q2, t)
                        } else {
                            let mut s = vec![true; d1 * d2];
                            for b1 in 0..d1 {
                                for b2 in 0..d2 {
                                    s[b2 * d1 + b1] = t[b1 * d2 + b2];
                                }
                            }
                            (q2, q1, s)
                        };
                        net.edges.push((u, v, t));
                        let e = net.edges.len() - 1;
                        net.adj[u].insert(v, e);
                        net.adj[v].insert(u, e);
                    }
                }
                active[p] = false;
                left.push(Left::Series { p, q1, e1, q2, e2 });
                work.insert(q1);
                work.insert(q2);
            }
            _ => {}
        }
    }

    // Step 4: what is left, as 2-SAT.
    let mut sat = TwoSat {
        vars: 0,
        clauses: Vec::new(),
        meets: Default::default(),
    };
    let mut var = vec![usize::MAX; n];
    let mut two: Vec<Vec<usize>> = vec![Vec::new(); n];
    for p in (1..n).filter(|&p| active[p]) {
        two[p] = (0..net.alive[p].len())
            .filter(|&a| net.alive[p][a])
            .collect();
        if two[p].len() > 2 {
            return None;
        }
        var[p] = sat.fresh();
        if two[p].len() == 1 {
            sat.clauses.push((var[p], var[p]));
        }
    }
    // The literal "place p takes its value two[p][i]" is `var[p] + i`; its complement `^ 1`.
    for p in (1..n).filter(|&p| active[p]) {
        for (&q, &e) in net.adj[p].range(p + 1..) {
            for (i, &a) in two[p].iter().enumerate() {
                for (k, &b) in two[q].iter().enumerate() {
                    if !net.ok(e, p, a, b) {
                        sat.clauses.push(((var[p] + i) ^ 1, (var[q] + k) ^ 1));
                    }
                }
            }
        }
    }
    let model = sat.solve()?;

    // Step 5: the unwinding.
    let mut chosen = vec![usize::MAX; n];
    for p in (1..n).filter(|&p| active[p]) {
        chosen[p] = two[p][usize::from(!model[var[p] / 2])];
    }
    let partner = |net: &Net, p: usize, fits: &dyn Fn(usize) -> bool| {
        (0..net.alive[p].len())
            .find(|&a| net.alive[p][a] && fits(a))
            .expect("a value kept with a partner (module doc, step 5)")
    };
    for step in left.iter().rev() {
        match *step {
            Left::Fixed(p, a) => chosen[p] = a,
            Left::Leaf { p, q, e } => {
                chosen[p] = partner(&net, p, &|a| net.ok(e, p, a, chosen[q]));
            }
            Left::Series { p, q1, e1, q2, e2 } => {
                chosen[p] = partner(&net, p, &|a| {
                    net.ok(e1, p, a, chosen[q1]) && net.ok(e2, p, a, chosen[q2])
                });
            }
        }
    }
    Some(
        (0..n)
            .map(|j| match chosen[j] {
                usize::MAX if j == 0 => Value::Int(0),
                usize::MAX => pl[j].pick(),
                a => kept[j][a].1.clone(),
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::super::forest_tests::{cofinite, finite};
    use super::*;

    fn int(k: i64) -> Value {
        Value::Int(k)
    }

    /// Whether `x` holds every clause.
    fn holds(x: &[Value], atom: &[(usize, Ints)], clause: &[[usize; 2]]) -> bool {
        (clause.iter()).all(|c| c.iter().any(|&i| atom[i].1.contains(&x[atom[i].0])))
    }

    /// The selector reduction of 3-SAT as the escape solve sees it: variables at places 1 to `k`
    /// (values 1 false, 2 true), a selector place per clause after them (values 1 to 3), and per
    /// literal `l` of clause `c` the clause "selector `c` is not `l`, or the literal holds".
    fn selector(
        k: usize,
        clauses: &[[(usize, bool); 3]],
    ) -> (Vec<Ints>, Vec<(usize, Ints)>, Vec<[usize; 2]>) {
        let mut pl = vec![finite([]); 1];
        pl.extend((0..k).map(|_| finite([int(1), int(2)])));
        pl.extend(clauses.iter().map(|_| finite([int(1), int(2), int(3)])));
        let (mut atom, mut clause) = (Vec::new(), Vec::new());
        for (c, cl) in clauses.iter().enumerate() {
            for (l, &(v, b)) in cl.iter().enumerate() {
                let others = (1..=3).filter(|&x| x != l as i64 + 1).map(int);
                atom.push((k + 1 + c, finite(others)));
                atom.push((v + 1, finite([int(if b { 2 } else { 1 })])));
                clause.push([atom.len() - 2, atom.len() - 1]);
            }
        }
        (pl, atom, clause)
    }

    fn satisfiable(k: usize, clauses: &[[(usize, bool); 3]]) -> bool {
        (0..1u32 << k)
            .any(|a| (clauses.iter()).all(|c| c.iter().any(|&(i, b)| (a >> i & 1 == 1) == b)))
    }

    /// The selector atoms `{2, 3}`, `{1, 3}`, `{1, 2}` cross, so `forest` refuses them; a 2-SAT
    /// formula in the selector reduction (each clause's literals on two variables at most, a
    /// chain `x0 -> x1 -> x2 -> x3` with a tautology beside each link: t04 of the prototype) is
    /// answered with a list that holds every clause.
    #[test]
    fn a_selector_reduction_of_2_sat_is_answered_with_a_list() {
        let mut cls = Vec::new();
        for i in 0..3 {
            cls.push([(i, false), (i + 1, true), (i + 1, true)]);
            cls.push([(i, true), (i, false), (i + 1, true)]);
        }
        let (pl, atom, clause) = selector(4, &cls);
        let at_sel: Vec<usize> = (0..atom.len()).filter(|&i| atom[i].0 == 5).collect();
        let mut parent = vec![None; atom.len()];
        assert_eq!(super::super::forest(&at_sel, &atom, &mut parent), None);
        let x = crossing_witness(&pl, &atom, &clause).expect("a list");
        assert!(holds(&x, &atom, &clause), "{x:?}");
        for (j, v) in x.iter().enumerate().skip(1) {
            assert!(pl[j].contains(v), "place {j}: {v:?}");
        }
    }

    /// Each list found holds every clause, and no unsatisfiable formula gets one, over every
    /// formula of up to three clauses on three variables with literals from a small pool, and
    /// the satisfiable formulas whose variables sit in at most two clauses each are all
    /// answered (their constraint graphs reduce by leaves and series steps).
    #[test]
    fn lists_found_hold_and_reducible_formulas_are_answered() {
        let lits: Vec<(usize, bool)> = (0..3).flat_map(|v| [(v, false), (v, true)]).collect();
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let (mut found, mut reducible) = (0, 0);
        for _ in 0..600 {
            let m = 1 + (next() % 3) as usize;
            let cls: Vec<[(usize, bool); 3]> = (0..m)
                .map(|_| std::array::from_fn(|_| lits[(next() % 6) as usize]))
                .collect();
            let (pl, atom, clause) = selector(3, &cls);
            let sat = satisfiable(3, &cls);
            let got = crossing_witness(&pl, &atom, &clause);
            if let Some(x) = &got {
                assert!(sat, "{cls:?}: a list of an unsatisfiable formula");
                assert!(holds(x, &atom, &clause), "{cls:?}: {x:?}");
                found += 1;
            }
            let uses = |v: usize| cls.iter().filter(|c| c.iter().any(|l| l.0 == v)).count();
            if sat && (0..3).all(|v| uses(v) <= 2) {
                assert!(
                    got.is_some(),
                    "{cls:?}: reducible and satisfiable, not answered"
                );
                reducible += 1;
            }
        }
        assert!(
            found > 100 && reducible > 50,
            "{found} found, {reducible} reducible"
        );
    }

    /// `(x0 | x1 | x2) & (!x0 | !x1 | !x2)` (t06 of the prototype, which refuses it: its
    /// degree-two step asks both neighbours for two values at most, and here they are selectors
    /// of three) is answered: each variable is in two clauses, so it leaves by the series step,
    /// and then the two selectors share one edge. The `_u6gad` gadget is refused: each variable
    /// is in four clauses with both signs, each selector has three values and three neighbours,
    /// and every value has a partner, so no step applies and three values are left.
    #[test]
    fn a_series_reducible_3_sat_is_answered_and_a_coupled_core_refused() {
        let signs = |m: usize| std::array::from_fn(|i| (i, m >> i & 1 == 1));
        let (pl, atom, clause) = selector(3, &[signs(7), signs(0)]);
        let x = crossing_witness(&pl, &atom, &clause).expect("a list");
        assert!(holds(&x, &atom, &clause), "{x:?}");
        let gad = [
            [(0, true), (1, true), (2, true)],
            [(0, true), (1, false), (2, false)],
            [(0, false), (1, true), (2, false)],
            [(0, false), (1, false), (2, true)],
        ];
        let (pl, atom, clause) = selector(3, &gad);
        assert_eq!(crossing_witness(&pl, &atom, &clause), None);
    }

    /// Cofinite places and atoms: the atoms `int \ {1}` and `int \ {2}` at place 1, each in a
    /// clause with the atom `{6}` at place 2, which holds `{5}` only, so never that atom. Place 1
    /// must take a value outside `{1, 2}`, one no set writes: 1 and 2 are each in one of the two
    /// atoms and 0 in both, so step 1 keeps 0 alone.
    #[test]
    fn a_cofinite_place_takes_a_value_no_set_writes() {
        let pl = vec![finite([]), cofinite([]), finite([int(5)])];
        let atom = vec![
            (1, cofinite([int(1)])),
            (2, finite([int(6)])),
            (1, cofinite([int(2)])),
        ];
        let clause = vec![[0, 1], [2, 1]];
        let x = crossing_witness(&pl, &atom, &clause).expect("a list");
        assert!(holds(&x, &atom, &clause), "{x:?}");
        assert_eq!(x[1], int(0), "{x:?}");
        // With every value of place 1 out of some atom, no list: a place left with no value.
        let pl = vec![finite([]), finite([int(1), int(2)]), finite([int(5)])];
        assert_eq!(crossing_witness(&pl, &atom, &clause), None);
    }
}
