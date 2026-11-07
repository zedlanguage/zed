//! Questions over shared conjunctions, each decided from the answers of the conjunction it
//! extends (LOAD-chain-share). The relation of a test `p(x) = q(x: x) && x > 3` is the
//! conjunction of `q`'s relation, kept whole as one part ([`Formula::and_keeping`]), and the
//! new constraint; the relation of a chain of n such tests so holds each callee's relation
//! once, shared, and not n²/2 copies. [`Extending`] remembers the answers of each conjunction
//! it decides, by the part it is (`Id`), and decides a conjunction that holds a decided one
//! from those answers and its other parts.
//!
//! A relation's auxiliary variables are defined apart from its body (LOAD-chain-aux): `x div
//! 3` is a variable `q` with `x == 3 * q + r` and `0 <= r <= 2`. Each question is asked of the
//! body and the definitions it reaches, `defs && body` and `defs && !body`, and a part's
//! definitions are reached from the part alone, so a conjunction is decided from its kept
//! part's answers and its other parts with their own definitions.
//!
//! A question decided with its definitions reads each definition's chain through a summary of
//! it (`Summaries`, LOAD-chain-sep): the chain projected exactly onto the variables of its
//! last definition and the atoms it does not define, made from the summary of the definition
//! before, so separate tests over the links of one chain (`t{i}(x) = h{i}(x: x) > 0`, `h{i} =
//! h{i-1} div 2 + 1`) read one definition and one summary each, not the chain.

use std::collections::{HashMap, HashSet};

use super::formula::Id;
use super::{Atom, Con, Factor, Formula, Lin, Model, Refusal, decide, satisfiable, shadow};
use zedc_int::int::Int;

/// Whether a formula holds somewhere and whether its negation does, each with the refusal that
/// left it undecided.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Answers {
    /// Whether the formula holds somewhere.
    pub holds: Result<bool, Refusal>,
    /// Whether its negation holds somewhere.
    pub fails: Result<bool, Refusal>,
}

/// A point, shared: adding the values of a part's new atoms to its kept part's point costs
/// O(log n) each, and copies nothing.
type Point = imbl::OrdMap<Atom, Int>;

/// What is remembered of a decided conjunction: its answers, and a point where it and its
/// definitions hold when it holds and the solver gave one. The point gives a value to every
/// atom of the conjunction and of its definitions, so that a part added beside it, with
/// atoms of its own, is met by giving values to those alone.
struct Known {
    answers: Answers,
    point: Option<Point>,
}

/// The answers of conjunctions decided so far, by the part each is, and the summaries of the
/// definitions read so far.
#[derive(Default)]
pub struct Extending {
    known: HashMap<Id, Known>,
    sums: Summaries,
}

/// The definitions a definition reaches, projected exactly: by the definition (the formula
/// `def` gives, held as a key, so that the quotient and the remainder it defines share it), its
/// summary, or `None` where none is made.
#[derive(Default)]
struct Summaries {
    by: HashMap<Id, Option<Summary>>,
}

/// A definition `d` and the definitions it reaches, projected onto the variables `d` defines and
/// the atoms none of them defines (the inputs, and variables with no definition): the integer
/// points of `rows` are those of the conjunction read on these atoms (exact, [`shadow`] with its
/// dark shadows). Made only where each definition reads the variables of one definition at
/// most, so the definitions reached form a path down to the one that reads none, `bottom`; two
/// summaries with different bottoms share no definition.
struct Summary {
    rows: Formula,
    bottom: Id,
}

impl Extending {
    /// An empty memory.
    pub fn new() -> Extending {
        Extending::default()
    }

    /// [`Extending::defined`] of a formula with no auxiliary variable, or whose auxiliary
    /// variables are free.
    pub fn answers(&mut self, f: &Formula) -> Answers {
        self.defined(f, &|_| Formula::top())
    }

    /// Whether `f` holds somewhere and whether `!f` does, where each auxiliary variable `n` is
    /// defined by `def(n)` (a formula over the atoms it is made of, which holds for some value
    /// of `n` whatever their values, and whose own auxiliary variables are defined the same
    /// way): [`decide`] of `defs && f` and of `defs && !f`, with `defs` the definitions `f`
    /// reaches. But a conjunction one of whose parts is a conjunction kept whole is decided from
    /// that part's answers, which are found first and remembered, and its other parts with the
    /// definitions they reach:
    ///
    /// - it holds nowhere when the part holds nowhere; it holds where the part's point meets
    ///   every other part, or where the other parts hold with the atoms the part's point gives
    ///   a value fixed to it and their other atoms free; otherwise it is decided whole;
    /// - its negation holds somewhere when the part's negation does; when the part holds
    ///   everywhere, it is the negation of the other parts that is decided: first with only the
    ///   definitions they reach past the part's point, which settles it when that never holds
    ///   or holds at a point extending the part's, then with all they reach; otherwise it is
    ///   decided whole.
    ///
    /// The definitions of the other parts may be left out of the part's questions, and those of
    /// the part out of the other parts', since a definition holds for some value of its variable
    /// whatever the values of the atoms it is made of. Each answer is the one [`decide`] gives
    /// the whole, where [`decide`] answers it: a conjunction that holds nowhere because a part
    /// does, or holds at a point, holds there. The answer of a conjunction does not depend on
    /// the order in which conjunctions are asked, since its kept part is always decided first,
    /// the same way. The time is that of the parts beside each kept part and the definitions
    /// they reach past the part's point (LOAD-chain-defs), for a chain of conjunctions each
    /// extending the one before whose point meets the next part and whose negation holds or
    /// never holds; a conjunction decided whole costs what [`decide`] costs on it. Every formula
    /// asked of one `Extending` is read with the same `def`, since the answers it remembers are
    /// those under it.
    // Complexity tradeoff: a conjunction whose new parts exclude the point found for the part it
    // extends, or whose part's question was refused, is decided whole, in time of the whole
    // conjunction and not of its new parts; the answer is [`decide`]'s. Why: deciding integer
    // feasibility after adding a constraint has no procedure in time of the constraint alone
    // (an added constraint may move every point, and the elimination the solver does is not
    // kept). Trigger: a chain of tests whose constraints each exclude the point of the test it
    // calls. Test `l01_38_presburger::extend::a_chain_whose_points_move_is_decided_whole`, which
    // measures it, and `l01_38_presburger::one_scope::the_questions_of_a_chain_of_tests_scale`
    // for the chain whose points serve. COMPLEXITY.md row LOAD-chain-share. A complete
    // solution needs an incremental integer procedure: a simplex kept from the callee, with
    // its basis, to which the new rows are added, and the branch of an integer search redone
    // only where the new rows cut it.
    // A negation the part's point and the new definitions do not settle, and a question with
    // no kept part (`t(x) = h(x: x) > 0`), are decided with the summaries of the definitions
    // they read ([`Summaries`], LOAD-chain-sep), so separate tests over the links of one chain
    // of n definitions read O(n) rows in all; where a summary is not made, with every
    // definition they reach (the tradeoff at [`Summaries::summary`]). A conjunction with no
    // kept part finds its point with every definition it reaches, as above, since a summary
    // gives no value to the atoms it projects out.
    pub fn defined(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Answers {
        // The chain of kept conjunctions from `f` down to the first one known or with no kept
        // part, each decided after the one it holds: an explicit stack, since the chain is as
        // deep as the chain of calls.
        let mut chain: Vec<Formula> = Vec::new();
        let mut g = f.clone();
        while matches!(g, Formula::And(_)) && !self.known.contains_key(&Id::any(&g)) {
            let next = kept(&g).cloned();
            chain.push(g);
            match next {
                Some(h) => g = h,
                None => break,
            }
        }
        while let Some(g) = chain.pop() {
            let k = self.extend(&g, def);
            self.known.insert(Id::any(&g), k);
        }
        match f {
            Formula::And(_) => self.known[&Id::any(f)].answers.clone(),
            _ => Answers {
                holds: decide_defined(&mut self.sums, f.clone(), def),
                fails: decide_defined(&mut self.sums, Formula::negate(f.clone()), def),
            },
        }
    }

    /// The answers of the conjunction `g`, its kept part's answers known when it has one.
    fn extend(&mut self, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Known {
        let Some(at) = kept_at(g) else {
            return whole(&mut self.sums, g, def);
        };
        let kids = g.kids();
        let Some(part) = self.known.get(&Id::any(&kids[at])) else {
            return whole(&mut self.sums, g, def);
        };
        // The other parts, O(their number), and the definitions they reach; a refusal on them
        // is answered by deciding the whole, so a refused question prints the refusal it
        // printed before.
        let others = kids.iter().enumerate().filter(|&(i, _)| i != at);
        let rest = Formula::and(others.map(|(_, h)| h.clone()).collect());
        // The definitions the other parts reach past the auxiliary variables the part's point
        // gives a value: those it gives hold there with their own definitions, so a point that
        // extends it needs values for the new ones alone, and a link whose new constraint reads
        // a long chain of definitions (`h{i}(x: x) > 0`, `h{i} = h{i-1} div 2`) reads only the
        // definitions its link added, not the chain again (LOAD-chain-defs).
        let new = |f: &Formula, m: &Point| with(&reached_past(f, def, m), f.clone());
        let (holds, point) = match (&part.answers.holds, &part.point) {
            (Ok(false), _) => (Ok(false), None),
            (Ok(true), Some(m)) => match met(m, &new(&rest, m)) {
                Some(p) => (Ok(true), Some(p)),
                None => holds_whole(g, def),
            },
            _ => holds_whole(g, def),
        };
        // The part holds everywhere, so the whole fails where the other parts do. Their
        // negation with only the new definitions holds where the full one does (the others'
        // variables left free), so it never holding settles it; one point of it that extends
        // the part's point satisfies every definition, so that settles it too; otherwise it is
        // decided with all the definitions it reaches.
        let fails = match part.answers.fails {
            Ok(true) => Ok(true),
            Ok(false) => {
                let not = Formula::negate(rest);
                let short = part.point.as_ref().and_then(|m| {
                    let f = new(&not, m);
                    match decide(&f) {
                        Ok(false) => Some(false),
                        _ => met(m, &f).map(|_| true),
                    }
                });
                match short {
                    Some(b) => Ok(b),
                    None => match decide_defined(&mut self.sums, not, def) {
                        Ok(b) => Ok(b),
                        Err(_) => fails_whole(&mut self.sums, g, def),
                    },
                }
            }
            Err(_) => fails_whole(&mut self.sums, g, def),
        };
        Known {
            answers: Answers { holds, fails },
            point,
        }
    }
}

/// Where the first part of the conjunction `g` that is a conjunction kept whole lies among
/// its parts.
fn kept_at(g: &Formula) -> Option<usize> {
    g.kids().iter().position(|h| matches!(h, Formula::And(_)))
}

/// The first part of the conjunction `g` that is a conjunction kept whole.
fn kept(g: &Formula) -> Option<&Formula> {
    kept_at(g).map(|i| &g.kids()[i])
}

/// The auxiliary variables of an atom.
fn auxes(a: &Atom) -> impl Iterator<Item = u32> {
    let (f, g) = match a {
        Atom::Aux(n) => (Some(*n), None),
        Atom::Product(f, g) => {
            let aux = |f: &Factor| match f {
                Factor::Aux(n) => Some(*n),
                Factor::Sym(_) => None,
            };
            (aux(f), aux(g))
        }
        Atom::Sym(_) => (None, None),
    };
    f.into_iter().chain(g)
}

/// The definitions `f` reaches: those of its auxiliary variables, and of theirs. Time of `f`
/// and of the definitions, each read once.
fn reached(f: &Formula, def: &dyn Fn(u32) -> Formula) -> Vec<Formula> {
    reached_past(f, def, &Point::new())
}

/// The definitions `f` reaches through the auxiliary variables `m` gives no value: those of
/// its auxiliary variables not in `m`, and of theirs. Time of `f` and of the definitions read,
/// each read once, and O(log n) for each variable looked up in `m`.
fn reached_past(f: &Formula, def: &dyn Fn(u32) -> Formula, m: &Point) -> Vec<Formula> {
    let mut seen: HashSet<u32> = HashSet::new();
    let mut todo: Vec<u32> = f.atoms().iter().flat_map(auxes).collect();
    let mut out = Vec::new();
    while let Some(n) = todo.pop() {
        if !seen.insert(n) || m.contains_key(&Atom::Aux(n)) {
            continue;
        }
        let d = def(n);
        if matches!(&d, Formula::And(gs) if gs.is_empty()) {
            continue;
        }
        todo.extend(d.atoms().iter().flat_map(auxes));
        out.push(d);
    }
    out
}

/// `f` with the definitions `defs`: `f` alone when there are none, so that a formula with no
/// auxiliary variable is decided as it was written.
fn with(defs: &[Formula], f: Formula) -> Formula {
    if defs.is_empty() {
        return f;
    }
    let mut parts = defs.to_vec();
    parts.push(f);
    Formula::and(parts)
}

/// A point where `f` holds that gives each atom of `m` its value there: `m` itself, each atom of
/// `f` it does not hold given 0, when `f` holds at it; otherwise `m` with the values of a point
/// the solver gives `f` with the atoms of `m` fixed to their values. `None` when neither is
/// found. Time of `f`, and O(log n) for each atom added to `m`.
fn met(m: &Point, f: &Formula) -> Option<Point> {
    let atoms = f.atoms();
    // The values `f` reads at `m`, with the factors of its products.
    let mut at = Model::new();
    for a in &atoms {
        let factors = auxes(a).map(Atom::Aux).chain(match a {
            Atom::Product(f, g) => vec![f.atom(), g.atom()],
            Atom::Sym(_) | Atom::Aux(_) => Vec::new(),
        });
        for b in std::iter::once(a.clone()).chain(factors) {
            if let Some(v) = m.get(&b) {
                at.insert(b, v.clone());
            }
        }
    }
    let mut out = m.clone();
    if f.holds(&at) {
        for a in atoms {
            out.entry(a).or_default();
        }
        return Some(out);
    }
    let mut fixed = vec![f.clone()];
    for a in atoms.iter().filter(|&a| m.contains_key(a)) {
        let v = Lin::constant(m[a].clone());
        fixed.push(Formula::Con(Con::eq(&Lin::atom(a.clone()), &v)));
    }
    let found = satisfiable(&Formula::and(fixed)).ok()??;
    for a in atoms {
        if !m.contains_key(&a) {
            let v = found.get(&a).cloned().unwrap_or_default();
            out.insert(a, v);
        }
    }
    Some(out)
}

/// Whether `g` and its definitions hold somewhere, decided whole, with a point when they hold
/// and the solver gives one, every atom of them given a value.
fn holds_whole(
    g: &Formula,
    def: &dyn Fn(u32) -> Formula,
) -> (Result<bool, Refusal>, Option<Point>) {
    let f = with(&reached(g, def), g.clone());
    match decide(&f) {
        Ok(true) => {
            let point = satisfiable(&f).ok().flatten().map(|m| {
                let mut p: Point = m.into_iter().collect();
                for a in f.atoms() {
                    p.entry(a).or_default();
                }
                p
            });
            (Ok(true), point)
        }
        other => (other, None),
    }
}

/// Whether the negation of `g` and its definitions hold somewhere, decided whole.
fn fails_whole(
    sums: &mut Summaries,
    g: &Formula,
    def: &dyn Fn(u32) -> Formula,
) -> Result<bool, Refusal> {
    decide_defined(sums, Formula::negate(g.clone()), def)
}

/// The answers of `g`, decided whole.
fn whole(sums: &mut Summaries, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Known {
    let (holds, point) = holds_whole(g, def);
    Known {
        answers: Answers {
            holds,
            fails: fails_whole(sums, g, def),
        },
        point,
    }
}

/// Whether `f` holds somewhere with the definitions it reaches: decided with their summaries
/// ([`Summaries::read`]) where each is made and the answer is given, and otherwise with the
/// definitions themselves, so that a question the solver refuses with the summaries prints the
/// refusal it printed before. The answers agree where the solver gives both, since each summary
/// is exact; a question it refuses whole may be answered with the summaries, which are smaller.
fn decide_defined(
    sums: &mut Summaries,
    f: Formula,
    def: &dyn Fn(u32) -> Formula,
) -> Result<bool, Refusal> {
    if let Some(d) = sums.read(&f, def)
        && let Ok(b) = decide(&with(&d, f.clone()))
    {
        return Ok(b);
    }
    decide(&with(&reached(&f, def), f))
}

impl Summaries {
    /// The summaries of the definitions of `f`'s auxiliary variables, one for each definition,
    /// in place of every definition `f` reaches: `None` when one has none, or when two have the
    /// same bottom, so that they may share definitions and their projections, each exact, may
    /// not be together. Time of `f` and of the summaries made, each made once.
    fn read(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Option<Vec<Formula>> {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut bottoms: HashSet<Id> = HashSet::new();
        let mut out = Vec::new();
        for n in f.atoms().iter().flat_map(auxes) {
            let d = def(n);
            if matches!(&d, Formula::And(gs) if gs.is_empty()) {
                continue;
            }
            if !matches!(d, Formula::And(_)) {
                return None;
            }
            let id = Id::any(&d);
            if !seen.insert(id.clone()) {
                continue;
            }
            let s = self.summary(&d, def)?;
            if !bottoms.insert(s.bottom.clone()) {
                return None;
            }
            out.push(s.rows.clone());
        }
        Some(out)
    }

    /// The summary of the definition `d`, a conjunction, made from the summary of the one
    /// definition its variables read, which is made first: an explicit stack, since the path is
    /// as deep as the chain of definitions. Each definition is read once, and its summary is
    /// `shadow` of its constraints and its input's summary, so the time is that of the
    /// definitions and the summaries along the path, each made once and remembered.
    // Complexity tradeoff: no summary is made, and the question is decided with every
    // definition it reaches as before, for a definition that is not a conjunction of
    // constraints (`min`, `max`, `abs`, an `if`, a `div` by a variable, each a disjunction), one
    // with products of variables, one that reads the variables of two definitions, one whose
    // input has none, and one whose projection `shadow` does not finish (an atom of the input
    // left in it); and for a question that reads two variables on one path (`h3(x: x) > 0 &&
    // h7(x: x) > 0`). Separate tests over the links of such a chain read O(n²) definitions.
    // Why: projecting a disjunction keeps one case per branch, which may double at each link,
    // and two definitions read together need the conjunction of their paths, which no single
    // summary is. Trigger: these definitions in a chain of separate tests. Test
    // `l01_38_presburger::one_scope::summaries_of_definitions_give_the_answers_of_the_definitions`,
    // which checks the answers, COMPLEXITY.md row LOAD-chain-sep. A complete solution keeps
    // a summary per case of a disjunction, merged where cases agree, and for two variables on
    // one path the summary of the lower projected onto both, made from the higher's path.
    // The coefficients of a summary are those of the composed definitions (`2^i` after i
    // halvings), so its numbers have O(i) bits; the solver's own elimination of the whole chain
    // makes the same numbers.
    fn summary(&mut self, d: &Formula, def: &dyn Fn(u32) -> Formula) -> Option<&Summary> {
        let mut stack: Vec<Formula> = vec![d.clone()];
        let mut open: HashSet<Id> = HashSet::new();
        while let Some(top) = stack.last() {
            let id = Id::any(top);
            if self.by.contains_key(&id) {
                open.remove(&id);
                stack.pop();
                continue;
            }
            open.insert(id.clone());
            match self.make(top, &id, def) {
                Made::Done(s) => {
                    self.by.insert(id.clone(), s);
                    open.remove(&id);
                    stack.pop();
                }
                Made::First(g) if !open.contains(&Id::any(&g)) => stack.push(g),
                Made::First(_) => {
                    self.by.insert(id.clone(), None);
                    open.remove(&id);
                    stack.pop();
                }
            }
        }
        self.by.get(&Id::any(d))?.as_ref()
    }

    /// The summary of the definition `d` (whose key is `id`) when the summary of its input is
    /// known, or the input to make first. Time of `d` and of its input's summary.
    fn make(&self, d: &Formula, id: &Id, def: &dyn Fn(u32) -> Formula) -> Made {
        let none = Made::Done(None);
        let mut rows: Vec<Con> = Vec::new();
        for h in d.kids() {
            match h {
                Formula::Con(c) => rows.push(c.clone()),
                _ => return none,
            }
        }
        // The atoms the summary keeps: the inputs (the variables without a definition and
        // those of no other definition) and the variables `d` defines.
        let mut keep: HashSet<Atom> = HashSet::new();
        let mut input: Option<(Id, Formula)> = None;
        for c in &rows {
            for a in c.lin.terms.keys() {
                match a {
                    Atom::Product(..) => return none,
                    Atom::Sym(_) => {
                        keep.insert(a.clone());
                    }
                    Atom::Aux(n) => {
                        let e = def(*n);
                        if matches!(&e, Formula::And(gs) if gs.is_empty()) {
                            keep.insert(a.clone());
                            continue;
                        }
                        if !matches!(e, Formula::And(_)) {
                            return none;
                        }
                        let eid = Id::any(&e);
                        if eid == *id {
                            keep.insert(a.clone());
                        } else {
                            match &input {
                                None => input = Some((eid, e)),
                                Some((j, _)) if *j == eid => {}
                                Some(_) => return none,
                            }
                        }
                    }
                }
            }
        }
        let Some((gid, g)) = input else {
            return Made::Done(Some(Summary {
                rows: d.clone(),
                bottom: id.clone(),
            }));
        };
        let Some(known) = self.by.get(&gid) else {
            return Made::First(g);
        };
        let Some(below) = known else {
            return none;
        };
        // The input's summary reads the inputs and the input definition's variables, which
        // are projected out.
        for a in below.rows.atoms() {
            if matches!(a, Atom::Sym(_))
                || matches!(&a, Atom::Aux(n) if matches!(&def(*n), Formula::And(gs) if gs.is_empty()))
            {
                keep.insert(a);
            }
        }
        rows.extend(below.rows.cons().into_iter().cloned());
        let Some(out) = shadow(&rows, &|a| keep.contains(a), true) else {
            return none;
        };
        if out
            .iter()
            .any(|c| c.lin.terms.keys().any(|a| !keep.contains(a)))
        {
            return none;
        }
        Made::Done(Some(Summary {
            rows: Formula::and(out.into_iter().map(Formula::Con).collect()),
            bottom: below.bottom.clone(),
        }))
    }
}

/// What [`Summaries::make`] gives: the summary, `None` where none is made, or the input
/// definition whose summary is made first.
enum Made {
    Done(Option<Summary>),
    First(Formula),
}
