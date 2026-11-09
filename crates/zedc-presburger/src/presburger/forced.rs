//! The answer of a formula whose equations fix every variable one at a time (PRES-small-cost).
//!
//! A formula such as `((x >= 1 && x == q0) || (!(x >= 1) && q0 == 1)) && x == 6 && y == 4`,
//! which the preimage of `if x >= 1 { x } else { 1 }` at a point gives, has one point, and
//! every value of it follows from the one before: `x == 6` fixes `x`, which decides
//! `x >= 1`, which leaves one disjunct, whose `x == q0` fixes `q0`. [`forced`] reads such a
//! formula by propagation alone, in time linear in its size, where the whole solver's front
//! end (normal form, canonical order, coloring, settling) cost 25 to 140 times as much on it.
//!
//! Each atom is read as a variable of its own, a product of two variables included, as the
//! solver reads it ([`super::Formula::holds`] reads a product as the product of its factors;
//! the solver does not).
//!
//! A part of the formula is *forced* when it holds at every point of the formula: the formula
//! itself, each operand of a forced conjunction, and the one operand of a forced disjunction
//! whose other operands are false. A forced equation with one variable whose value is not yet
//! known fixes that variable, so every value the propagation gives holds at every point of the
//! formula. The answer is therefore exact:
//! - a forced part that is false, or a forced equation whose variable would need a value that
//!   is not an integer, leaves the formula no point;
//! - a formula that is true at the values given, once each of its variables has one, has that
//!   point and no other. The whole solver gives the same point, but leaves out the atoms that
//!   only a disjunction it drops as removing no point reads ([`super::absorb`]), which its
//!   callers then read as zero; here every atom of the formula has its value;
//! - a formula that is true at the values given while some variable has none holds at some
//!   point, whatever the others' values ([`super::decide`]);
//! - anything else is left to the solver, after O(n) work.

use std::collections::HashMap;

use zedc_int::int::Int;

use super::formula::{Atom, Con, Formula, Id, Model, Rel};

/// What the propagation of [`forced`] shows.
pub(super) enum Forced {
    /// The formula has no point.
    Empty,
    /// The formula's one point, each atom of the formula with its value.
    Point(Model),
    /// The formula holds at some point, but not every variable has a value.
    Holds,
}

/// The connective of a part of the formula.
enum Kind<'f> {
    And,
    Or,
    Not,
    Con(&'f Con),
}

/// An event of the propagation.
enum Event {
    /// The part has its value now.
    Valued(u32),
    /// The part is forced.
    Force(u32),
    /// The variable has its value now.
    Known(u32),
}

/// The formula as a graph of its parts, each shared part once, with the state of the
/// propagation.
struct Graph<'f> {
    kind: Vec<Kind<'f>>,
    /// Each part's operands, as a range of `kid_list`.
    kids: Vec<(u32, u32)>,
    kid_list: Vec<u32>,
    /// Each part's parents, as a range of `parent_list` (one entry per occurrence).
    parents: Vec<(u32, u32)>,
    parent_list: Vec<u32>,
    /// Each variable's atom, and the number of each atom.
    atoms: Vec<Atom>,
    numbers: HashMap<Atom, u32>,
    /// Each constraint's distinct variables, as a range of `var_list`.
    vars: Vec<(u32, u32)>,
    var_list: Vec<u32>,
    /// The constraints that read each variable, as a range of `watch_list`.
    watches: Vec<(u32, u32)>,
    watch_list: Vec<u32>,
    value: Vec<Option<bool>>,
    forced: Vec<bool>,
    /// Of a conjunction, its operands not yet true; of a disjunction, its operands not yet
    /// false; of a constraint, its variables not yet known.
    left: Vec<u32>,
    known: Vec<Option<Int>>,
    events: Vec<Event>,
}

/// What [`forced`] shows of `f`, or `None` when propagation leaves it undecided. O(n) for `n`
/// the size of `f` with each shared part counted once, plus hashing each atom.
pub(super) fn forced(f: &Formula) -> Option<Forced> {
    let mut g = Graph::of(f);
    g.events.push(Event::Force(0));
    if !g.run() {
        return Some(Forced::Empty);
    }
    match g.value[0] {
        Some(true) if g.known.iter().all(Option::is_some) => Some(Forced::Point(g.point())),
        Some(true) => Some(Forced::Holds),
        _ => None,
    }
}

impl<'f> Graph<'f> {
    /// The graph of `f`, each part reached once (a visited set keyed by the shared parts' ids),
    /// with each part that has its value already (a constraint of no variable, an empty
    /// conjunction or disjunction) queued.
    fn of(f: &'f Formula) -> Graph<'f> {
        let mut g = Graph {
            kind: Vec::new(),
            kids: Vec::new(),
            kid_list: Vec::new(),
            parents: Vec::new(),
            parent_list: Vec::new(),
            atoms: Vec::new(),
            numbers: HashMap::new(),
            vars: Vec::new(),
            var_list: Vec::new(),
            watches: Vec::new(),
            watch_list: Vec::new(),
            value: Vec::new(),
            forced: Vec::new(),
            left: Vec::new(),
            known: Vec::new(),
            events: Vec::new(),
        };
        let mut seen: HashMap<Id, u32> = HashMap::new();
        let mut stack = vec![(f, g.add(f))];
        while let Some((h, n)) = stack.pop() {
            let start = g.kid_list.len() as u32;
            for k in h.kids() {
                let shared = Id::of(k);
                let i = match shared.and_then(|id| seen.get(&id)) {
                    Some(&i) => i,
                    None => {
                        let i = g.add(k);
                        if let Some(id) = shared {
                            seen.insert(id, i);
                        }
                        stack.push((k, i));
                        i
                    }
                };
                g.kid_list.push(i);
            }
            g.kids[n as usize] = (start, g.kid_list.len() as u32);
        }
        g.link();
        g
    }

    /// A new part for `f`, with its variables when it is a constraint.
    fn add(&mut self, f: &'f Formula) -> u32 {
        let n = self.kind.len() as u32;
        let start = self.var_list.len() as u32;
        let kind = match f {
            Formula::And(_) => Kind::And,
            Formula::Or(_) => Kind::Or,
            Formula::Not(_) => Kind::Not,
            Formula::Con(c) => {
                for a in c.lin.terms.keys() {
                    let v = self.number(a.clone());
                    self.var_list.push(v);
                }
                let vs = &mut self.var_list[start as usize..];
                vs.sort_unstable();
                let distinct = start as usize + dedup_sorted(vs);
                self.var_list.truncate(distinct);
                Kind::Con(c)
            }
        };
        self.kind.push(kind);
        self.vars.push((start, self.var_list.len() as u32));
        self.kids.push((0, 0));
        n
    }

    /// The number of the variable `a`.
    fn number(&mut self, a: Atom) -> u32 {
        let next = self.atoms.len() as u32;
        *self.numbers.entry(a).or_insert_with_key(|a| {
            self.atoms.push(a.clone());
            next
        })
    }

    /// The parents and watch lists (counting sorts), the counts of `left`, and the parts that
    /// have their values already, queued.
    fn link(&mut self) {
        let parts = self.kind.len();
        self.parents = ranges(parts, self.kid_list.iter().map(|&k| k as usize));
        self.parent_list = vec![0; self.kid_list.len()];
        let mut at: Vec<u32> = self.parents.iter().map(|r| r.0).collect();
        for (n, &(s, e)) in self.kids.iter().enumerate() {
            for &k in &self.kid_list[s as usize..e as usize] {
                self.parent_list[at[k as usize] as usize] = n as u32;
                at[k as usize] += 1;
            }
        }
        let vars = self.atoms.len();
        self.watches = ranges(vars, self.var_list.iter().map(|&v| v as usize));
        self.watch_list = vec![0; self.var_list.len()];
        let mut at: Vec<u32> = self.watches.iter().map(|r| r.0).collect();
        for (n, &(s, e)) in self.vars.iter().enumerate() {
            for &v in &self.var_list[s as usize..e as usize] {
                self.watch_list[at[v as usize] as usize] = n as u32;
                at[v as usize] += 1;
            }
        }
        self.known = vec![None; vars];
        self.value = vec![None; parts];
        self.forced = vec![false; parts];
        self.left = (0..parts)
            .map(|n| match self.kind[n] {
                Kind::Con(_) => self.vars[n].1 - self.vars[n].0,
                _ => self.kids[n].1 - self.kids[n].0,
            })
            .collect();
        for n in 0..parts {
            if self.left[n] == 0 {
                let v = match self.kind[n] {
                    Kind::And => true,
                    Kind::Or => false,
                    Kind::Con(c) => self.holds(c),
                    Kind::Not => unreachable!("a negation has one operand"),
                };
                self.set(n as u32, v);
            }
        }
    }

    /// Gives part `n` its value and queues its parents' update.
    fn set(&mut self, n: u32, v: bool) {
        self.value[n as usize] = Some(v);
        self.events.push(Event::Valued(n));
    }

    /// Runs the queued events to the end; `false` when a forced part is false.
    fn run(&mut self) -> bool {
        while let Some(e) = self.events.pop() {
            let ok = match e {
                Event::Valued(n) => self.valued(n),
                Event::Force(n) => self.force(n),
                Event::Known(x) => self.known_var(x),
            };
            if !ok {
                return false;
            }
        }
        true
    }

    /// Part `n` has its value: its parents learn it.
    fn valued(&mut self, n: u32) -> bool {
        let v = self.value[n as usize].expect("valued");
        if self.forced[n as usize] && !v {
            return false;
        }
        let (s, e) = self.parents[n as usize];
        for i in s..e {
            let p = self.parent_list[i as usize];
            let pu = p as usize;
            if self.value[pu].is_some() {
                continue;
            }
            match self.kind[pu] {
                Kind::Not => self.set(p, !v),
                Kind::And if !v => self.set(p, false),
                Kind::Or if v => self.set(p, true),
                Kind::And | Kind::Or => {
                    self.left[pu] -= 1;
                    if self.left[pu] == 0 {
                        self.set(p, v);
                    } else if self.left[pu] == 1 && self.forced[pu] {
                        self.force_last(p);
                    }
                }
                Kind::Con(_) => unreachable!("a constraint has no operands"),
            }
        }
        true
    }

    /// Part `n` holds at every point.
    fn force(&mut self, n: u32) -> bool {
        let nu = n as usize;
        if self.forced[nu] {
            return true;
        }
        self.forced[nu] = true;
        if let Some(v) = self.value[nu] {
            return v;
        }
        match self.kind[nu] {
            Kind::And => {
                let (s, e) = self.kids[nu];
                for i in s..e {
                    let k = self.kid_list[i as usize];
                    self.events.push(Event::Force(k));
                }
            }
            Kind::Or if self.left[nu] == 1 => self.force_last(n),
            Kind::Or | Kind::Not => {}
            Kind::Con(c) => return self.solve(n, c),
        }
        true
    }

    /// Forces the one operand of the forced disjunction or conjunction `p` not yet decided
    /// the other way. For a conjunction every operand is forced already.
    fn force_last(&mut self, p: u32) {
        if !matches!(self.kind[p as usize], Kind::Or) {
            return;
        }
        let (s, e) = self.kids[p as usize];
        let last = (s..e)
            .map(|i| self.kid_list[i as usize])
            .find(|&k| self.value[k as usize] != Some(false));
        if let Some(k) = last {
            self.events.push(Event::Force(k));
        }
    }

    /// Variable `x` has its value: each constraint that reads it learns it.
    fn known_var(&mut self, x: u32) -> bool {
        let (s, e) = self.watches[x as usize];
        for i in s..e {
            let c = self.watch_list[i as usize];
            let cu = c as usize;
            if self.value[cu].is_some() {
                continue;
            }
            self.left[cu] -= 1;
            let Kind::Con(con) = self.kind[cu] else {
                unreachable!("a watch is a constraint")
            };
            if self.left[cu] == 0 {
                let v = self.holds(con);
                self.set(c, v);
            } else if self.left[cu] == 1 && self.forced[cu] && !self.solve(c, con) {
                return false;
            }
        }
        true
    }

    /// When the forced constraint `n` is an equation with one variable not yet known, which it
    /// reads linearly, gives that variable its value; `false` when the value is not an integer.
    fn solve(&mut self, n: u32, c: &Con) -> bool {
        let nu = n as usize;
        if c.rel != Rel::Eq || self.left[nu] != 1 {
            return true;
        }
        let (s, e) = self.vars[nu];
        let Some(x) = (s..e)
            .map(|i| self.var_list[i as usize])
            .find(|&v| self.known[v as usize].is_none())
        else {
            return true;
        };
        // `a·x + b == 0`.
        let mut a = Int::ZERO;
        let mut b = c.lin.constant.clone();
        for (atom, k) in &c.lin.terms {
            match &self.known[self.numbers[atom] as usize] {
                Some(v) => b = &b + &(k * v),
                None => a = &a + k,
            }
        }
        if a.is_zero() {
            return true;
        }
        let nb = -&b;
        if !nb.mod_floor(&a).is_zero() {
            return false;
        }
        self.known[x as usize] = Some(nb.div_floor(&a));
        self.events.push(Event::Known(x));
        true
    }

    /// Whether `c` holds at the known values, all of its variables known.
    fn holds(&self, c: &Con) -> bool {
        let mut v = c.lin.constant.clone();
        for (atom, k) in &c.lin.terms {
            let x = self.known[self.numbers[atom] as usize]
                .as_ref()
                .expect("known");
            v = &v + &(k * x);
        }
        if c.rel == Rel::Eq {
            v.is_zero()
        } else {
            !v.is_negative()
        }
    }

    /// The point: every atom with its value.
    fn point(&self) -> Model {
        (self.atoms.iter().cloned())
            .zip(self.known.iter().map(|v| v.clone().expect("known")))
            .collect()
    }
}

/// Moves the distinct values of sorted `xs` to its front; gives how many there are.
fn dedup_sorted(xs: &mut [u32]) -> usize {
    let mut w = 0;
    for r in 0..xs.len() {
        if w == 0 || xs[r] != xs[w - 1] {
            xs[w] = xs[r];
            w += 1;
        }
    }
    w
}

/// The ranges of a counting sort of `keys` into `n` buckets.
fn ranges(n: usize, keys: impl Iterator<Item = usize>) -> Vec<(u32, u32)> {
    let mut count = vec![0u32; n];
    for k in keys {
        count[k] += 1;
    }
    let mut at = 0;
    count
        .into_iter()
        .map(|c| {
            let r = (at, at + c);
            at += c;
            r
        })
        .collect()
}
