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
//!   point, whatever the others' values: that point, with zero for each atom it does not
//!   read, when a point is asked for ([`super::satisfiable`]), and `true` otherwise
//!   ([`super::decide`]);
//! - a formula still undecided is set at its bounds in rounds (PRES-small-point): each round
//!   gives each variable not known that has gained a bound since the round before that bound,
//!   its lower one when it has two, all at once, and the same propagation runs on, which may
//!   bound more variables for the next round. The rounds stop when one sets nothing, at a
//!   contradiction, or when the formula is decided. A formula true there holds at that point,
//!   with zero for each atom still not known, which it does not read: `x >= 6 && 7 >= x &&
//!   y == 4` is answered `x == 6, y == 4`, one point of several, and exact. No round tries a
//!   second value or undoes one, so the rounds search nothing; there are at most as many as
//!   variables, and together they cost one propagation. The state only tightens, and every
//!   order of the propagation reaches the same state ([`trial::Trial::holds`] proves both),
//!   so the answer does not depend on the names or order of the atoms;
//! - anything else is left to the solver, after O(n) work, with the facts the propagation
//!   proved before the rounds ([`Facts`]): each atom it fixed replaced by its value. A value
//!   a round sets is never passed, not even as a hint, since it holds at one point at most
//!   and would remove the others.

use std::collections::HashMap;
use std::hash::BuildHasherDefault;

use rustc_hash::FxHasher;
use zedc_int::int::Int;

use super::Conjuncts;
use super::formula::{Atom, Con, Formula, Id, Model, Rel};
use state::{Countdown, Interval, Latch, Meet, Once};
use trial::Trial;

/// What the propagation of [`forced`] shows.
pub(super) enum Forced<'f> {
    /// The formula has no point.
    Empty,
    /// A point of the formula, each atom of the formula with its value, zero for an atom the
    /// formula, true at the others' values, does not read: its one point when propagation
    /// fixes every variable, else the point the propagation or the rounds at the bounds reach.
    Point(Model),
    /// The formula holds at some point; its point was not asked for.
    Holds,
    /// The propagation and the rounds at the bounds leave the formula undecided; what the
    /// propagation proved before the rounds, for the solver.
    Undecided(Facts<'f>),
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
    value: Once<bool>,
    forced: Latch,
    /// Of a conjunction, its operands not yet true; of a disjunction, its operands not yet
    /// false; of a constraint, its variables not yet known.
    left: Countdown,
}

/// A variable, with what the propagation knows of it.
struct Var<'f> {
    atom: &'f Atom,
    known: Once<Int>,
    /// The bounds that forced rows put on it.
    bounds: Interval,
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
    /// The variables that a forced row has bounded, each once, in the order bounded: those
    /// still not known are the ones a round of [`Trial::holds`] sets.
    bounded: Vec<u32>,
}

/// What [`forced`] shows of `f`; without `point`, a formula that holds is answered
/// [`Forced::Holds`], its point not built. O(n) for `n` the size of `f` with each shared part
/// counted once, plus hashing each atom.
pub(super) fn forced(f: &Formula, point: bool) -> Forced<'_> {
    let mut g = Graph::of(f);
    g.events.push(Event::Force(0));
    if !g.run() {
        return Forced::Empty;
    }
    match g.parts[0].value.get() {
        Some(true) if point => Forced::Point(g.point()),
        Some(true) => Forced::Holds,
        _ => {
            let facts = g.facts(f);
            let mut trial = Trial::of(g);
            match (trial.holds().0 == Some(true), point) {
                (false, _) => Forced::Undecided(facts),
                (true, true) => Forced::Point(trial.point()),
                (true, false) => Forced::Holds,
            }
        }
    }
}

/// Whether [`forced`] answers `f`, of top-level conjuncts `conjuncts` (`Formula::conjunct_list`),
/// [`Forced::Empty`]: the propagation alone, with no facts read out and no trial point, which
/// only answer a formula it does not show empty, and with no graph built for a formula whose
/// top-level conjuncts give it no first step ([`may_start`]). O(n) as [`forced`].
pub(super) fn empty(f: &Formula, conjuncts: &Conjuncts) -> bool {
    if !may_start(conjuncts) {
        return false;
    }
    let mut g = Graph::of(f);
    g.events.push(Event::Force(0));
    !g.run()
}

/// Whether the propagation can take a first step on `f` from its top-level conjuncts, the parts
/// forced from the start. With no atom known, a forced constraint gives a step only with one
/// atom ([`Graph::solve`]): an equation fixes it, or shows it has no integer value; rows `t >= 0`
/// of one atom bound it, and fix it or cross only where its least value is at or above its
/// greatest. A constraint of no atom, or a disjunction of one operand or none, gives a step
/// too. Where none of these is among the conjuncts, no atom is ever known and no part ever has
/// its value, so the propagation ends with nothing shown.
// Complexity tradeoff: the answer reads the top-level conjuncts alone, O(c) for c conjuncts and
// O(b) expected for the b rows of one atom, so a constraint of no atom below a top-level
// disjunction or negation, which the propagation would value at once and which could decide that
// disjunction, is not seen: such a formula is projected without the proof of emptiness, at the
// cost of the projection itself. Why: seeing it walks the whole formula, the O(n) pass this
// test saves (about 15K instructions on a formula of a dozen parts, where the projection costs
// about 500K). The constructors (`Formula::and`, `Formula::or`) absorb `true` and `false` but
// keep a constraint of no atom. Trigger: a projected formula whose only seed is such a part.
// Tests: `l01_38_presburger::one_row::a_forced_contradiction_projects_to_empty_in_linear_work`
// and `l01_38_presburger::one_row::a_formula_with_no_first_step_is_projected_without_the_propagation`.
fn may_start(conjuncts: &Conjuncts) -> bool {
    let mut ends: Vec<(&Atom, Option<Int>, Option<Int>)> = Vec::new();
    for g in conjuncts.iter() {
        match g {
            Formula::Con(c) if c.lin.terms.is_empty() => return true,
            Formula::Con(c) if c.rel == Rel::Eq && c.lin.terms.len() == 1 => return true,
            Formula::Con(c) => ends.extend(super::one_bound(c)),
            Formula::Or(ds) if ds.len() <= 1 => return true,
            Formula::Or(_) | Formula::And(_) | Formula::Not(_) => {}
        }
    }
    if ends.len() < 2 {
        return false;
    }
    let mut at: FxMap<&Atom, (Option<Int>, Option<Int>)> =
        FxMap::with_capacity_and_hasher(ends.len(), Default::default());
    for (a, lo, hi) in ends {
        let (l, h) = at.entry(a).or_default();
        if let Some(lo) = lo
            && l.as_ref().is_none_or(|v| lo > *v)
        {
            *l = Some(lo);
        }
        if let Some(hi) = hi
            && h.as_ref().is_none_or(|v| hi < *v)
        {
            *h = Some(hi);
        }
        if let (Some(l), Some(h)) = (&*l, &*h)
            && l >= h
        {
            return true;
        }
    }
    false
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
            bounded: Vec::new(),
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
            value: Once::unknown(),
            forced: Latch::lowered(),
            left: Countdown::new(0),
        });
        n
    }

    /// The number of the variable `a`.
    fn number(&mut self, a: &'f Atom) -> u32 {
        let next = self.vars.len() as u32;
        *self.numbers.entry(a).or_insert_with(|| {
            self.vars.push(Var {
                atom: a,
                known: Once::unknown(),
                bounds: Interval::whole(),
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
            p.left = Countdown::new(p.span.1 - p.span.0);
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
            if self.parts[n].left.get() == 0 {
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
        self.parts[n as usize].value.fix(v);
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
            #[cfg(test)]
            trace::record(self);
            if !ok {
                return false;
            }
        }
        true
    }

    /// Part `n` has its value: its parents learn it.
    fn valued(&mut self, n: u32) -> bool {
        let part = &self.parts[n as usize];
        let v = *part.value.get().expect("valued");
        if part.forced.is_raised() && !v {
            return false;
        }
        let (s, e) = part.parents;
        for i in s..e {
            let p = self.parent_list[i as usize];
            let pp = &mut self.parts[p as usize];
            if pp.value.get().is_some() {
                continue;
            }
            match pp.kind {
                Kind::Not => self.set(p, !v),
                Kind::And if !v => self.set(p, false),
                Kind::Or if v => self.set(p, true),
                Kind::And | Kind::Or => match pp.left.fall() {
                    0 => self.set(p, v),
                    1 if pp.forced.is_raised() => self.force_last(p),
                    _ => {}
                },
                Kind::Con(_) => unreachable!("a constraint has no operands"),
            }
        }
        true
    }

    /// Part `n` holds at every point.
    fn force(&mut self, n: u32) -> bool {
        let part = &mut self.parts[n as usize];
        if !part.forced.raise() {
            return true;
        }
        if let Some(&v) = part.value.get() {
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
            Kind::Or if part.left.get() == 1 => self.force_last(n),
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
            .find(|&k| self.parts[k as usize].value.get() != Some(&false));
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
            if part.value.get().is_some() {
                continue;
            }
            let left = part.left.fall();
            let Kind::Con(con) = part.kind else {
                unreachable!("a watch is a constraint")
            };
            if left == 0 {
                let v = self.holds(c as usize, con);
                self.set(c, v);
            } else if left == 1 && part.forced.is_raised() && !self.solve(c, con) {
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
        if part.left.get() != 1 {
            return true;
        }
        // `a·x + b` with `x` the variable not yet known.
        let (mut x, mut a) = (None, &Int::ZERO);
        let mut b = c.lin.constant.clone();
        for i in part.span.0 as usize..part.span.1 as usize {
            let (v, k) = self.terms[i];
            match self.vars[v as usize].known.get() {
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
        let value = match c.rel {
            Rel::Eq => {
                let nb = -&b;
                if !nb.mod_floor(a).is_zero() {
                    return false;
                }
                nb.div_floor(a)
            }
            // `a·x >= -b`: `x >= ceil(-b / a)` for `a > 0`, `x <= floor(b / -a)` for `a < 0`.
            Rel::Ge => {
                if var.bounds.is_whole() {
                    self.bounded.push(x);
                }
                let meet = if a.is_positive() {
                    var.bounds.meet_lo(-&b.div_floor(a))
                } else {
                    var.bounds.meet_hi(b.div_floor(&-a))
                };
                match meet {
                    Meet::Empty => return false,
                    Meet::Wide => return true,
                    Meet::One(v) => v,
                }
            }
        };
        var.known.fix(value);
        self.events.push(Event::Known(x));
        true
    }

    /// Whether the constraint `c` of part `n` holds at the known values, all of its variables
    /// known.
    fn holds(&self, n: usize, c: &Con) -> bool {
        let (s, e) = self.parts[n].span;
        let mut v = c.lin.constant.clone();
        for i in s as usize..e as usize {
            let (x, k) = self.terms[i];
            let x = self.vars[x as usize].known.get().expect("known");
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
            m.insert(v.atom.clone(), v.known.get().cloned().unwrap_or(Int::ZERO));
        }
        m
    }

    /// What the propagation has proved so far: each variable it has fixed, with its value.
    /// Read before any round at the bounds ([`Trial`]), which takes the graph whole, so no
    /// value a round sets is among them.
    fn facts(&self, f: &'f Formula) -> Facts<'f> {
        let known = (self.vars.iter())
            .filter_map(|v| Some((v.atom, v.known.get()?.clone())))
            .collect();
        Facts { formula: f, known }
    }
}

/// What the propagation proved of a formula it left undecided, before any round at the bounds:
/// each atom it fixed, with its value. Each value holds at every point of the formula, since
/// only forced parts fix a value; so the formula is the same as the formula with each fixed
/// atom replaced by its value, together with an equation for each fixed atom. The bounds it
/// proved come from forced rows with one variable left once the fixed atoms are replaced,
/// which the replaced formula holds as rows of that one variable, and the parts it decided are
/// decided there by their constants; so the replaced formula carries every fact the
/// propagation proved. No value a round at the bounds sets is among them ([`Trial`]): such a
/// value holds at some point of the formula at most, not at every point, and as a row it
/// would remove the others.
pub(super) struct Facts<'f> {
    /// The formula the propagation read.
    pub(super) formula: &'f Formula,
    /// Each atom it fixed, with its value.
    pub(super) known: FxMap<&'f Atom, Int>,
}

impl Facts<'_> {
    /// A point of the formula from a point of its reduced form ([`super::reduced`]): the fixed
    /// atoms with their values added.
    pub(super) fn fill(&self, m: &mut Model) {
        for (a, v) in &self.known {
            m.insert((*a).clone(), v.clone());
        }
    }

    /// The fixed atoms with their values.
    #[cfg(test)]
    pub(super) fn fixed(&self) -> Model {
        let mut m = Model::new();
        self.fill(&mut m);
        m
    }
}

/// The rounds at the bounds, in a module of their own so that the graph they change is held
/// only by [`Trial`], whose methods give out the trial's answer and point and nothing else:
/// no value a round sets can reach [`Facts`], read from the graph before.
mod trial {
    use super::{Event, Graph, Model};

    /// A graph whose propagation has ended with the formula undecided, tried at its bounds.
    pub(super) struct Trial<'f>(Graph<'f>);

    impl<'f> Trial<'f> {
        /// The trial of `g`, whose propagation has ended undecided.
        pub(super) fn of(g: Graph<'f>) -> Trial<'f> {
            Trial(g)
        }

        /// Whether the formula holds once the variables are tried at their bounds in rounds
        /// (`Some(false)` when it is false there or a contradiction is found, `None` when it is
        /// still undecided), and how many rounds set some variable. A round gives every variable not yet known
        /// that has a bound that bound, its lower one when it has two, all at once, and the
        /// propagation then continues; the next round sets the variables that propagation has
        /// bounded since. The rounds end when one sets nothing, the formula has its value, or a
        /// contradiction is found. No round tries a second value for a variable, and no value
        /// is undone: the rounds search nothing.
        ///
        /// The answer is exact when it is `true`: the formula's value then follows by
        /// evaluation from values that are integers (the bounds, and what forced constraints
        /// give from them), so it is true wherever the variables still not known are.
        ///
        /// The rounds are monotone, end, and do not depend on the order of the events or the
        /// names of the atoms. The state of the propagation is a product of lattices, ordered
        /// by what it knows, lower knowing more, with a least element, the contradiction:
        /// - each part's value, unknown above `true` and above `false` ([`super::Once`]);
        /// - each part's mark, not forced above forced ([`super::Latch`]);
        /// - each variable's value, unknown above each integer ([`super::Once`]);
        /// - each variable's interval, ordered by inclusion ([`super::Interval`]).
        ///
        /// The types allow no change but a step down: `Once::fix` fixes an unknown value and
        /// keeps a fixed one, `Interval::meet_lo` and `Interval::meet_hi` intersect, and
        /// `Latch::raise` raises; `Countdown::fall` lowers the count of a part's operands or
        /// variables still open, a function of the rest of the state. Their fields are private
        /// to module `state`, and their constructors, which give the top, are called only
        /// while the graph is built. Each step down is one event, and a part's value, a part's
        /// mark and a variable's value each step down once, an interval once per bound a row
        /// gives it (each forced row with one variable left gives one bound, the values it
        /// reads fixed for good); so a run has finitely many events, linear in the formula.
        ///
        /// Each rule reads the state only through conditions that stay true as the state goes
        /// down, and only writes it down, so each is monotone and deflationary:
        /// - linear row (`solve`): a forced constraint with every variable but `x` fixed meets
        ///   `x`'s interval with the bound the row gives, or for an equation fixes `x`; the
        ///   bound is a function of the fixed values, the same in every state that has them.
        ///   Bounds that cross, or an equation with no integer solution, give the
        ///   contradiction. When `x` is fixed too, the row is evaluated, with the same result:
        ///   false, which is the contradiction for a forced row, when `x` lies outside. `solve`
        ///   reads "unknown" to find `x`, but only to name the variable the rule writes; the
        ///   count of variables not fixed, which only falls, decides whether the rule applies;
        /// - conjunction (`valued`, `force`): an operand false makes it false, every operand
        ///   true makes it true; forced, it forces each operand;
        /// - disjunction (`valued`, `force`, `force_last`): an operand true makes it true,
        ///   every operand false makes it false; forced with every operand but one false, it
        ///   forces that one, which `force_last` finds as the one not false, again only to
        ///   name it;
        /// - negation: its operand's value, negated;
        /// - product atom: no rule of its own; a product is a variable, fixed or bounded only
        ///   by the rows that read it, as the solver reads it;
        /// - contradiction: a forced part false; the run stops there, in every order.
        ///
        /// A round sets each variable not fixed that has a bound to a value inside its
        /// interval, a step down too. So every state is below the one before. A run of events
        /// reaches the greatest state below its start that no rule changes: every rule fires
        /// whenever its condition becomes true (it is checked when the last value it reads
        /// arrives), so every order of events is a fair chaotic iteration of monotone,
        /// deflationary rules on a lattice of finite height below the start, and all such
        /// iterations reach that one fixpoint (Knaster–Tarski on the finite lattice). The
        /// first propagation, and each round with its propagation, therefore end in the same
        /// state in every order, a renaming of the atoms renames that state, and a
        /// contradiction is reached in every order or none, in the same round. A round runs
        /// only after the one before fixed at least one more variable, so there are at most as
        /// many rounds as variables. Tests:
        /// `forced_against_solver::the_state_never_loosens`,
        /// `forced_against_solver::rounds_at_the_bounds_do_not_depend_on_names_or_order`,
        /// `forced_against_solver::the_point_at_the_bounds_does_not_depend_on_names_or_order`
        /// and `names::disjunctions_whose_atoms_share_a_color`; they check the proof, which
        /// does not rest on them.
        // Complexity tradeoff: a formula that holds at some point but not at this one (a bound
        // excluded by a disjunct, a parity row the bounds miss) is left to the solver, as
        // before this trial; trying other values (each bound in turn, or the other end) would
        // depend on the order tried or be a search exponential in the number of bounded
        // variables, which is the solver's work. Naive version: none, the solver for every
        // undecided formula, O(n log n) on the two-valued chain (`small_cost`) at about 70
        // times this trial's constant; or each round as a scan of every variable and a
        // propagation from the start, O(n^2) on a ladder that bounds one new variable per
        // round. Used: the rounds continue the one propagation, each variable enters
        // `bounded` once and is set at most once, and each round reads only the variables
        // bounded since the last, so all rounds together cost one propagation, O(n)
        // (`small_cost::a_ladder_of_bounds_costs_its_size`). COMPLEXITY.md row
        // PRES-small-point.
        pub(super) fn holds(&mut self) -> (Option<bool>, u32) {
            let g = &mut self.0;
            let (mut round, mut rounds, mut start) = (Vec::new(), 0, 0);
            loop {
                // The variables bounded since the last round, which `solve` keeps appending to.
                round.clear();
                round.extend_from_slice(&g.bounded[start..]);
                start = g.bounded.len();
                let mut set = false;
                for &x in &round {
                    let v = &mut g.vars[x as usize];
                    if v.known.get().is_none() {
                        v.known.fix(v.bounds.end().expect("bounded").clone());
                        g.events.push(Event::Known(x));
                        set = true;
                    }
                }
                if !set {
                    return (None, rounds);
                }
                rounds += 1;
                if !g.run() {
                    return (Some(false), rounds);
                }
                if let Some(&v) = g.parts[0].value.get() {
                    return (Some(v), rounds);
                }
            }
        }

        /// The point the trial reached ([`Graph::point`]).
        pub(super) fn point(&self) -> Model {
            self.0.point()
        }
    }
}

/// The state of the propagation, in types whose only changes are steps down the lattice
/// that [`Trial::holds`] describes: a value goes from unknown to fixed and stays, an interval
/// only shrinks, a mark is only raised, a count only falls. Their fields are private to this
/// module, so every change elsewhere goes through these methods.
mod state {
    use zedc_int::int::Int;

    /// A value unknown at first and then fixed for good; [`Once::fix`] is its only change.
    pub(super) struct Once<T>(Option<T>);

    impl<T> Once<T> {
        /// Unknown.
        pub(super) const fn unknown() -> Once<T> {
            Once(None)
        }

        /// The value, once fixed.
        pub(super) fn get(&self) -> Option<&T> {
            self.0.as_ref()
        }

        /// Fixes the value when it is unknown; a fixed value is kept.
        pub(super) fn fix(&mut self, v: T) {
            self.0.get_or_insert(v);
        }
    }

    /// An interval of integers, at first all of them, that only shrinks:
    /// [`Interval::meet_lo`] and [`Interval::meet_hi`] are its only changes.
    pub(super) struct Interval {
        lo: Option<Int>,
        hi: Option<Int>,
    }

    /// What an interval is after a meet.
    pub(super) enum Meet {
        /// No integer.
        Empty,
        /// One integer.
        One(Int),
        /// More than one.
        Wide,
    }

    impl Interval {
        /// Every integer.
        pub(super) const fn whole() -> Interval {
            Interval { lo: None, hi: None }
        }

        /// Whether it is every integer.
        pub(super) fn is_whole(&self) -> bool {
            self.lo.is_none() && self.hi.is_none()
        }

        /// Its lower end, else its upper end; `None` when it is every integer.
        pub(super) fn end(&self) -> Option<&Int> {
            self.lo.as_ref().or(self.hi.as_ref())
        }

        /// Its ends, `None` where it is open.
        #[cfg(test)]
        pub(super) fn ends(&self) -> (Option<&Int>, Option<&Int>) {
            (self.lo.as_ref(), self.hi.as_ref())
        }

        /// The interval met with the integers of at least `lo`.
        pub(super) fn meet_lo(&mut self, lo: Int) -> Meet {
            if self.lo.as_ref().is_none_or(|l| *l < lo) {
                self.lo = Some(lo);
            }
            self.shape()
        }

        /// The interval met with the integers of at most `hi`.
        pub(super) fn meet_hi(&mut self, hi: Int) -> Meet {
            if self.hi.as_ref().is_none_or(|h| hi < *h) {
                self.hi = Some(hi);
            }
            self.shape()
        }

        fn shape(&self) -> Meet {
            match (&self.lo, &self.hi) {
                (Some(lo), Some(hi)) if lo > hi => Meet::Empty,
                (Some(lo), Some(hi)) if lo == hi => Meet::One(lo.clone()),
                _ => Meet::Wide,
            }
        }
    }

    /// A mark, at first lowered, that is only raised.
    pub(super) struct Latch(bool);

    impl Latch {
        /// Lowered.
        pub(super) const fn lowered() -> Latch {
            Latch(false)
        }

        /// Whether it is raised.
        pub(super) fn is_raised(&self) -> bool {
            self.0
        }

        /// Raises it; whether it was lowered.
        pub(super) fn raise(&mut self) -> bool {
            !std::mem::replace(&mut self.0, true)
        }
    }

    /// A count that only falls.
    pub(super) struct Countdown(u32);

    impl Countdown {
        /// The count `n`.
        pub(super) const fn new(n: u32) -> Countdown {
            Countdown(n)
        }

        /// The count.
        pub(super) fn get(&self) -> u32 {
            self.0
        }

        /// Lowers the count by one; the count after.
        pub(super) fn fall(&mut self) -> u32 {
            self.0 -= 1;
            self.0
        }
    }
}

/// The rounds a formula takes at its bounds: `None` when the propagation decides it before
/// any round, else what [`Trial::holds`] gives.
#[cfg(test)]
pub(super) fn rounds(f: &Formula) -> Option<(Option<bool>, u32)> {
    let mut g = Graph::of(f);
    g.events.push(Event::Force(0));
    if !g.run() || g.parts[0].value.get().is_some() {
        return None;
    }
    Some(Trial::of(g).holds())
}

/// A record of the propagation's state after each event, for the test that it never
/// loosens (`forced_against_solver::the_state_never_loosens`).
#[cfg(test)]
pub(super) mod trace {
    use std::cell::RefCell;

    use zedc_int::int::Int;

    use super::{Formula, Graph};

    /// The state after one event.
    #[derive(Clone, PartialEq, Eq, Debug)]
    pub(in super::super) struct State {
        values: Vec<Option<bool>>,
        forced: Vec<bool>,
        left: Vec<u32>,
        known: Vec<Option<Int>>,
        bounds: Vec<(Option<Int>, Option<Int>)>,
    }

    thread_local! {
        static STATES: RefCell<Option<Vec<State>>> = const { RefCell::new(None) };
    }

    /// Records the state of `g` when a trace is being taken.
    pub(super) fn record(g: &Graph) {
        STATES.with(|s| {
            if let Some(states) = s.borrow_mut().as_mut() {
                states.push(State {
                    values: g.parts.iter().map(|p| p.value.get().copied()).collect(),
                    forced: g.parts.iter().map(|p| p.forced.is_raised()).collect(),
                    left: g.parts.iter().map(|p| p.left.get()).collect(),
                    known: g.vars.iter().map(|v| v.known.get().cloned()).collect(),
                    bounds: (g.vars.iter())
                        .map(|v| {
                            let (lo, hi) = v.bounds.ends();
                            (lo.cloned(), hi.cloned())
                        })
                        .collect(),
                });
            }
        });
    }

    /// The states after each event of [`super::forced`] on `f`, its rounds at the bounds
    /// included.
    pub(in super::super) fn states(f: &Formula) -> Vec<State> {
        STATES.with(|s| *s.borrow_mut() = Some(Vec::new()));
        super::forced(f, true);
        STATES.with(|s| s.borrow_mut().take()).expect("the trace")
    }

    /// Whether `b` knows at least what `a` knows: each value fixed in `a` is fixed alike in
    /// `b`, each mark raised in `a` is raised in `b`, each count is no larger, and each
    /// interval lies within `a`'s.
    pub(in super::super) fn below(b: &State, a: &State) -> bool {
        fn fixed<T: PartialEq>(x: &Option<T>, y: &Option<T>) -> bool {
            x.is_none() || x == y
        }
        let within = |(alo, ahi): &(Option<Int>, Option<Int>),
                      (blo, bhi): &(Option<Int>, Option<Int>)| {
            alo.as_ref()
                .is_none_or(|l| blo.as_ref().is_some_and(|m| l <= m))
                && ahi
                    .as_ref()
                    .is_none_or(|h| bhi.as_ref().is_some_and(|m| m <= h))
        };
        (a.values.iter().zip(&b.values)).all(|(x, y)| fixed(x, y))
            && (a.forced.iter().zip(&b.forced)).all(|(x, y)| !x || *y)
            && (a.left.iter().zip(&b.left)).all(|(x, y)| y <= x)
            && (a.known.iter().zip(&b.known)).all(|(x, y)| fixed(x, y))
            && (a.bounds.iter().zip(&b.bounds)).all(|(x, y)| within(x, y))
    }
}
