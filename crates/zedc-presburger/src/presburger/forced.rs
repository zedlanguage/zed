//! The answer of a formula whose constraints fix every variable one at a time
//! (PRES-small-cost, PRES-small-front).
//!
//! A formula such as `((x >= 1 && x == q0) || (!(x >= 1) && q0 == 1)) && x == 6 && y == 4`,
//! which the preimage of `if x >= 1 { x } else { 1 }` at a point gives, has one point, and
//! every value of it follows from the one before: `x == 6` fixes `x`, which decides
//! `x >= 1`, which leaves one disjunct, whose `x == q0` fixes `q0`. [`forced`] reads such a
//! formula by propagation alone, in time linear in its size, where the whole solver's front
//! end (normal form, canonical order, coloring, settling) cost 25 to 140 times as much on it.
//! The inputs may as well be fixed by two rows each, `x >= 6 && 6 >= x`: a forced row with one
//! variable not yet known bounds it, and a variable whose bounds meet is fixed.
//!
//! Each atom is read as a variable of its own, a product of two variables included, as the
//! solver reads it ([`super::Formula::holds`] reads a product as the product of its factors;
//! the solver does not).
//!
//! A part of the formula is *forced* when it holds at every point of the formula: the formula
//! itself, each operand of a forced conjunction, and the one operand of a forced disjunction
//! whose other operands are false. A forced equation with one variable whose value is not yet
//! known fixes that variable; a forced row `t >= 0` with one such variable bounds it, and two
//! bounds that meet fix it. So every value the propagation gives holds at every point of the
//! formula, and the answer is exact:
//! - a forced part that is false, a forced equation whose variable would need a value that is
//!   not an integer, or bounds of one variable that cross, leave the formula no point;
//! - a formula that is true at the values given, once each of its variables has one, has that
//!   point and no other. The whole solver gives the same point, but leaves out the atoms that
//!   only a disjunction it drops as removing no point reads ([`super::absorb`]), which its
//!   callers then read as zero; here every atom of the formula has its value;
//! - a formula that is true at the values given while some variable has none holds at some
//!   point, whatever the others' values ([`super::decide`]);
//! - a formula still undecided is tried once at its bounds (PRES-small-point): each variable
//!   not known that has a bound is given it, its lower one when it has two, all at once, and
//!   the propagation runs on. A formula true there holds at that point, with zero for each
//!   atom still not known, which it does not read: `x >= 6 && 7 >= x && y == 4` is answered
//!   `x == 6, y == 4`, one point of several, and exact. The bounds are the same in every
//!   order of the propagation, so the answer does not depend on the names or order of the
//!   atoms;
//! - anything else is left to the solver, after O(n) work.

use std::collections::HashMap;
use std::hash::BuildHasherDefault;

use rustc_hash::FxHasher;
use zedc_int::int::Int;

use super::formula::{Atom, Con, Formula, Id, Model, Rel};

/// What the propagation of [`forced`] shows.
pub(super) enum Forced {
    /// The formula has no point.
    Empty,
    /// A point of the formula, each atom of the formula with its value: its one point when
    /// propagation fixes every variable, else the point at its bounds.
    Point(Model),
    /// The formula holds at some point, but not every variable has a value, or its point at
    /// the bounds was not asked for.
    Holds,
}

/// A map hashed by [`FxHasher`]: its keys are ids and atoms of one formula, which no one
/// chooses to collide, and nothing iterates it, so its order reaches no result.
type FxMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

/// The connective of a part of the formula.
enum Kind<'f> {
    And,
    Or,
    Not,
    Con(&'f Con),
}

/// A part of the formula, with the state of the propagation at it.
struct Part<'f> {
    kind: Kind<'f>,
    /// Of a compound part, its operands, as a range of `kid_list`; of a constraint, its
    /// variables and their coefficients, as a range of `terms`.
    span: (u32, u32),
    /// The parts that hold it, as a range of `parent_list` (one entry per occurrence).
    parents: (u32, u32),
    value: Option<bool>,
    forced: bool,
    /// Of a conjunction, its operands not yet true; of a disjunction, its operands not yet
    /// false; of a constraint, its variables not yet known.
    left: u32,
}

/// A variable, with what the propagation knows of it.
struct Var<'f> {
    atom: &'f Atom,
    known: Option<Int>,
    /// The bounds that forced rows put on it.
    lo: Option<Int>,
    hi: Option<Int>,
    /// The constraints that read it, as a range of `watch_list`.
    watches: (u32, u32),
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
    parts: Vec<Part<'f>>,
    kid_list: Vec<u32>,
    parent_list: Vec<u32>,
    /// The variables of each constraint, in the order of its terms, which are distinct, each
    /// with its coefficient.
    terms: Vec<(u32, &'f Int)>,
    /// The number of each atom.
    numbers: FxMap<&'f Atom, u32>,
    vars: Vec<Var<'f>>,
    watch_list: Vec<u32>,
    events: Vec<Event>,
}

/// What [`forced`] shows of `f`, or `None` when propagation leaves it undecided; without
/// `point`, a formula with one point is answered [`Forced::Holds`], its point not built. O(n)
/// for `n` the size of `f` with each shared part counted once, plus hashing each atom.
pub(super) fn forced(f: &Formula, point: bool) -> Option<Forced> {
    let mut g = Graph::of(f);
    g.events.push(Event::Force(0));
    if !g.run() {
        return Some(Forced::Empty);
    }
    let root = g.parts[0].value;
    match root {
        Some(true) if point && g.vars.iter().all(|v| v.known.is_some()) => {
            Some(Forced::Point(g.point()))
        }
        Some(true) => Some(Forced::Holds),
        _ if !g.at_bounds() => None,
        _ if point => Some(Forced::Point(g.point())),
        _ => Some(Forced::Holds),
    }
}

impl<'f> Graph<'f> {
    /// The graph of `f`, each part reached once (a visited set keyed by the shared parts' ids),
    /// with each part that has its value already (a constraint of no variable, an empty
    /// conjunction or disjunction) queued.
    fn of(f: &'f Formula) -> Graph<'f> {
        // A first walk counts the parts, operands and terms, so each list is allocated once.
        let (mut parts, mut kids, mut terms) = (0, 0, 0);
        let mut seen: FxMap<Id, u32> = FxMap::default();
        let mut stack = vec![(f, 0)];
        while let Some((h, _)) = stack.pop() {
            parts += 1;
            if let Formula::Con(c) = h {
                terms += c.lin.terms.len();
            }
            for k in h.kids() {
                kids += 1;
                if Id::of(k).is_none_or(|id| seen.insert(id, 0).is_none()) {
                    stack.push((k, 0));
                }
            }
        }
        seen.clear();
        let mut g = Graph {
            parts: Vec::with_capacity(parts),
            kid_list: Vec::with_capacity(kids),
            parent_list: Vec::new(),
            terms: Vec::with_capacity(terms),
            numbers: FxMap::with_capacity_and_hasher(terms, Default::default()),
            vars: Vec::with_capacity(terms),
            watch_list: Vec::new(),
            events: Vec::with_capacity(parts),
        };
        stack.push((f, g.add(f)));
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
            if !matches!(h, Formula::Con(_)) {
                g.parts[n as usize].span = (start, g.kid_list.len() as u32);
            }
        }
        g.link();
        g
    }

    /// A new part for `f`, with its variables and coefficients when it is a constraint.
    fn add(&mut self, f: &'f Formula) -> u32 {
        let n = self.parts.len() as u32;
        let start = self.terms.len() as u32;
        let kind = match f {
            Formula::And(_) => Kind::And,
            Formula::Or(_) => Kind::Or,
            Formula::Not(_) => Kind::Not,
            Formula::Con(c) => {
                for (a, k) in &c.lin.terms {
                    let v = self.number(a);
                    self.terms.push((v, k));
                }
                Kind::Con(c)
            }
        };
        self.parts.push(Part {
            kind,
            span: (start, self.terms.len() as u32),
            parents: (0, 0),
            value: None,
            forced: false,
            left: 0,
        });
        n
    }

    /// The number of the variable `a`.
    fn number(&mut self, a: &'f Atom) -> u32 {
        let next = self.vars.len() as u32;
        *self.numbers.entry(a).or_insert_with(|| {
            self.vars.push(Var {
                atom: a,
                known: None,
                lo: None,
                hi: None,
                watches: (0, 0),
            });
            next
        })
    }

    /// The parents and watch lists (counting sorts, each range filled from its end), the counts
    /// of `left`, and the parts that have their values already, queued.
    fn link(&mut self) {
        let Graph {
            parts,
            kid_list,
            parent_list,
            terms,
            vars,
            watch_list,
            ..
        } = self;
        // Each part's number of parents, then the end of its range, then its range.
        for &k in kid_list.iter() {
            parts[k as usize].parents.1 += 1;
        }
        let mut at = 0;
        for p in parts.iter_mut() {
            at += p.parents.1;
            p.parents = (at, at);
        }
        *parent_list = vec![0; kid_list.len()];
        for n in 0..parts.len() {
            if matches!(parts[n].kind, Kind::Con(_)) {
                continue;
            }
            let (s, e) = parts[n].span;
            for &k in &kid_list[s as usize..e as usize] {
                let r = &mut parts[k as usize].parents;
                r.0 -= 1;
                parent_list[r.0 as usize] = n as u32;
            }
        }
        // Likewise each variable's watches.
        for &(v, _) in terms.iter() {
            vars[v as usize].watches.1 += 1;
        }
        let mut at = 0;
        for v in vars.iter_mut() {
            at += v.watches.1;
            v.watches = (at, at);
        }
        *watch_list = vec![0; terms.len()];
        for (n, p) in parts.iter_mut().enumerate() {
            p.left = p.span.1 - p.span.0;
            if !matches!(p.kind, Kind::Con(_)) {
                continue;
            }
            for &(v, _) in &terms[p.span.0 as usize..p.span.1 as usize] {
                let r = &mut vars[v as usize].watches;
                r.0 -= 1;
                watch_list[r.0 as usize] = n as u32;
            }
        }
        for n in 0..self.parts.len() {
            if self.parts[n].left == 0 {
                let v = match self.parts[n].kind {
                    Kind::And => true,
                    Kind::Or => false,
                    Kind::Con(c) => self.holds(n, c),
                    Kind::Not => unreachable!("a negation has one operand"),
                };
                self.set(n as u32, v);
            }
        }
    }

    /// Gives part `n` its value and queues its parents' update.
    fn set(&mut self, n: u32, v: bool) {
        self.parts[n as usize].value = Some(v);
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
        let part = &self.parts[n as usize];
        let v = part.value.expect("valued");
        if part.forced && !v {
            return false;
        }
        let (s, e) = part.parents;
        for i in s..e {
            let p = self.parent_list[i as usize];
            let pp = &mut self.parts[p as usize];
            if pp.value.is_some() {
                continue;
            }
            match pp.kind {
                Kind::Not => self.set(p, !v),
                Kind::And if !v => self.set(p, false),
                Kind::Or if v => self.set(p, true),
                Kind::And | Kind::Or => {
                    pp.left -= 1;
                    if pp.left == 0 {
                        self.set(p, v);
                    } else if pp.left == 1 && pp.forced {
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
        let part = &mut self.parts[n as usize];
        if part.forced {
            return true;
        }
        part.forced = true;
        if let Some(v) = part.value {
            return v;
        }
        match part.kind {
            Kind::And => {
                let (s, e) = part.span;
                (self.events).extend(
                    self.kid_list[s as usize..e as usize]
                        .iter()
                        .map(|&k| Event::Force(k)),
                );
            }
            Kind::Or if part.left == 1 => self.force_last(n),
            Kind::Or | Kind::Not => {}
            Kind::Con(c) => return self.solve(n, c),
        }
        true
    }

    /// Forces the one operand of the forced disjunction or conjunction `p` not yet decided
    /// the other way. For a conjunction every operand is forced already.
    fn force_last(&mut self, p: u32) {
        let part = &self.parts[p as usize];
        if !matches!(part.kind, Kind::Or) {
            return;
        }
        let (s, e) = part.span;
        let last = (self.kid_list[s as usize..e as usize].iter())
            .copied()
            .find(|&k| self.parts[k as usize].value != Some(false));
        if let Some(k) = last {
            self.events.push(Event::Force(k));
        }
    }

    /// Variable `x` has its value: each constraint that reads it learns it.
    fn known_var(&mut self, x: u32) -> bool {
        let (s, e) = self.vars[x as usize].watches;
        for i in s..e {
            let c = self.watch_list[i as usize];
            let part = &mut self.parts[c as usize];
            if part.value.is_some() {
                continue;
            }
            part.left -= 1;
            let Kind::Con(con) = part.kind else {
                unreachable!("a watch is a constraint")
            };
            if part.left == 0 {
                let v = self.holds(c as usize, con);
                self.set(c, v);
            } else if part.left == 1 && part.forced && !self.solve(c, con) {
                return false;
            }
        }
        true
    }

    /// When the forced constraint `n` has one variable not yet known: an equation gives it its
    /// value, a row `t >= 0` bounds it, and bounds that meet give it its value. `false` when the
    /// value is not an integer or the bounds cross.
    fn solve(&mut self, n: u32, c: &Con) -> bool {
        let part = &self.parts[n as usize];
        if part.left != 1 {
            return true;
        }
        // `a·x + b` with `x` the variable not yet known.
        let (mut x, mut a) = (None, &Int::ZERO);
        let mut b = c.lin.constant.clone();
        for i in part.span.0 as usize..part.span.1 as usize {
            let (v, k) = self.terms[i];
            match &self.vars[v as usize].known {
                Some(value) => b = &b + &(k * value),
                None => (x, a) = (Some(v), k),
            }
        }
        // All known: the `Known` event of the last one evaluates it.
        let Some(x) = x else {
            return true;
        };
        if a.is_zero() {
            return true;
        }
        let var = &mut self.vars[x as usize];
        match c.rel {
            Rel::Eq => {
                let nb = -&b;
                if !nb.mod_floor(a).is_zero() {
                    return false;
                }
                var.known = Some(nb.div_floor(a));
            }
            // `a·x >= -b`: `x >= ceil(-b / a)` for `a > 0`, `x <= floor(b / -a)` for `a < 0`.
            Rel::Ge => {
                if a.is_positive() {
                    let lo = -&b.div_floor(a);
                    if var.lo.as_ref().is_none_or(|l| *l < lo) {
                        var.lo = Some(lo);
                    }
                } else {
                    let hi = b.div_floor(&-a);
                    if var.hi.as_ref().is_none_or(|h| hi < *h) {
                        var.hi = Some(hi);
                    }
                }
                match (&var.lo, &var.hi) {
                    (Some(lo), Some(hi)) if lo > hi => return false,
                    (Some(lo), Some(hi)) if lo == hi => var.known = Some(lo.clone()),
                    _ => return true,
                }
            }
        }
        self.events.push(Event::Known(x));
        true
    }

    /// Whether the formula holds once every variable not yet known that has a bound is given
    /// that bound, its lower one when it has two, all at once, and the propagation is run again
    /// from there. Called when the propagation has ended with the formula undecided; afterward
    /// the graph's state is that of the trial, so nothing else reads it.
    ///
    /// The answer is exact when it is `true`: the formula's value then follows by evaluation
    /// from values that are integers (the bounds, and what forced constraints give from them),
    /// so it is true wherever the variables still not known are. It does not depend on the
    /// names or order of the atoms: the bounds are those of the propagation's end, which every
    /// order of its events reaches, since each rule only adds what the formula and the values
    /// before imply; all the bounds are set before any event runs; and from there too each
    /// event only adds what the formula and the trial imply, so a contradiction ends every
    /// order or none (`names::disjunctions_whose_atoms_share_a_color`,
    /// `forced_against_solver::the_point_at_the_bounds_does_not_depend_on_names_or_order`).
    // Complexity tradeoff: a formula that holds at some point but not at this one (a bound
    // excluded by a disjunct, a parity row the bounds miss) is left to the solver, as before
    // this trial; trying other values (each bound in turn, or the other end) would depend on
    // the order tried or be a search exponential in the number of bounded variables, which
    // is the solver's work. Naive version: none, the solver for every undecided formula,
    // O(n log n) on the two-valued chain (`small_cost`) at about 70 times this trial's
    // constant; used: one more pass of the same propagation, O(n). COMPLEXITY.md row
    // PRES-small-point.
    fn at_bounds(&mut self) -> bool {
        let Graph { vars, events, .. } = self;
        for (x, v) in vars.iter_mut().enumerate() {
            if v.known.is_none()
                && let Some(b) = v.lo.as_ref().or(v.hi.as_ref())
            {
                v.known = Some(b.clone());
                events.push(Event::Known(x as u32));
            }
        }
        !self.events.is_empty() && self.run() && self.parts[0].value == Some(true)
    }

    /// Whether the constraint `c` of part `n` holds at the known values, all of its variables
    /// known.
    fn holds(&self, n: usize, c: &Con) -> bool {
        let (s, e) = self.parts[n].span;
        let mut v = c.lin.constant.clone();
        for i in s as usize..e as usize {
            let (x, k) = self.terms[i];
            let x = self.vars[x as usize].known.as_ref().expect("known");
            v = &v + &(k * x);
        }
        if c.rel == Rel::Eq {
            v.is_zero()
        } else {
            !v.is_negative()
        }
    }

    /// The point: every atom with its value, zero for one still not known, which the formula,
    /// true at the values known, does not read.
    fn point(&self) -> Model {
        let mut m = Model::new();
        for v in &self.vars {
            m.insert(v.atom.clone(), v.known.clone().unwrap_or(Int::ZERO));
        }
        m
    }
}
