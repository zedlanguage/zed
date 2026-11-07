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

use super::formula::{Id, Rel};
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
    /// A point where its negation and its definitions hold, when it fails and the solver or
    /// an extension gave one, every atom of them given a value as in `point`.
    miss: Option<Point>,
    /// How many atoms it holds, its parts' counted once for each part they are in: which of
    /// two kept parts is the larger ([`Extending::extend`]).
    size: usize,
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
/// summaries with different bottoms share no definition. The symbols a definition binds, an
/// equality with none of its variables that sets a symbol its input's summary reads (`c ==
/// x + 1` of a claimed call, LOAD-chain-affine: `c` a canonical atom of the callee), are
/// projected out too, `hidden`: the summary stands for the definitions only where nothing
/// else read with it reads them ([`Summaries::read`]).
struct Summary {
    rows: Formula,
    bottom: Id,
    hidden: HashSet<Atom>,
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
    /// that part's answers (of several, the one with the most atoms; `Extending::extend`),
    /// which are found first and remembered, and its other parts with the definitions they
    /// reach:
    ///
    /// - it holds nowhere when the part holds nowhere; it holds where the part's point meets
    ///   every other part, or where the other parts hold with the atoms the part's point gives
    ///   a value fixed to it and their other atoms free; otherwise it is decided whole;
    /// - its negation holds somewhere when the part's point of negation extends to the
    ///   definitions the other parts reach past it, or when the negation of the other parts
    ///   holds with the definitions it reaches, since a definition binding the part's atoms to
    ///   a call's arguments gives them one value at each point (LOAD-chain-affine); otherwise
    ///   it is decided whole; when the part holds everywhere, it is the negation of the other
    ///   parts that is decided: first with only the definitions they reach past the part's
    ///   point, which settles it when that never holds or holds at a point extending the
    ///   part's, then with all they reach; otherwise it is decided whole.
    ///
    /// The definitions of the other parts may be left out of the part's questions, and those of
    /// the part out of the other parts', since a definition holds for some value of its variable
    /// whatever the values of the atoms it is made of. Each answer is the one [`decide`] gives
    /// the whole, where [`decide`] answers it: a conjunction that holds nowhere because a part
    /// does, or holds at a point, holds there. The answer of a conjunction does not depend on
    /// the order in which conjunctions are asked, since its kept parts are always decided first,
    /// the same way, and the one kept is chosen by their sizes alone. The time is that of the
    /// parts beside each kept part and the definitions they reach past the part's point
    /// (LOAD-chain-defs), for a chain of conjunctions each extending the one before whose point
    /// meets the next part and whose negation holds or never holds; a conjunction decided whole
    /// costs what [`decide`] costs on it. Every formula asked of one `Extending` is read with
    /// the same `def`, since the answers it remembers are those under it.
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
    // gives no value to the atoms it projects out. The same holds for the negation of a
    // conjunction whose part fails only at points its call's arguments do not reach (`p(x) =
    // q(x: 2 * x)`, `q` failing at odd values alone) and whose other parts never fail: decided
    // whole (LOAD-chain-affine).
    pub fn defined(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Answers {
        // The kept conjunctions under `f` not yet known, each decided after every one it holds
        // (LOAD-chain-affine: `q(x: x) && p(x: x + 1)` holds two), so that the largest is kept:
        // an explicit stack, since the conjunctions nest as deep as the chain of calls. The
        // known ones are the visited set; one met twice before it is decided is decided once.
        let mut todo = vec![(f.clone(), false)];
        while let Some((g, after)) = todo.pop() {
            if !matches!(g, Formula::And(_)) || self.known.contains_key(&Id::any(&g)) {
                continue;
            }
            if after {
                let k = self.extend(&g, def);
                self.known.insert(Id::any(&g), k);
                continue;
            }
            let kids: Vec<Formula> = (g.kids().iter())
                .filter(|h| matches!(h, Formula::And(_)) && !self.known.contains_key(&Id::any(h)))
                .cloned()
                .collect();
            todo.push((g, true));
            todo.extend(kids.into_iter().rev().map(|h| (h, false)));
        }
        match f {
            Formula::And(_) => self.known[&Id::any(f)].answers.clone(),
            _ => Answers {
                holds: decide_defined(&mut self.sums, f.clone(), def),
                fails: decide_defined(&mut self.sums, Formula::negate(f.clone()), def),
            },
        }
    }

    /// The answers of the conjunction `g`, from those of its kept part when it has one: the
    /// part, among its conjunctions kept whole, with the most atoms, the first of those with as
    /// many, so that a call of a small function beside a long chain (`q(x: x) && p(x: x + 1)`)
    /// extends the chain and reads `q` beside it (LOAD-chain-affine). O(its parts).
    fn extend(&mut self, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Known {
        let kids = g.kids();
        // The kept parts, the largest first, the first of those with as many.
        let mut parts: Vec<(usize, &Known)> = Vec::new();
        for (i, h) in kids.iter().enumerate() {
            if !matches!(h, Formula::And(_)) {
                continue;
            }
            let Some(k) = self.known.get(&Id::any(h)) else {
                return whole(&mut self.sums, g, def);
            };
            parts.push((i, k));
        }
        parts.sort_by_key(|&(i, k)| (std::cmp::Reverse(k.size), i));
        let Some(&(at, part)) = parts.first() else {
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
        // A point of the whole that extends some kept part's point: the largest part's first,
        // then each other's, so that a link whose callee's point lies outside it (`q(x: x) &&
        // p(x: x + 3)`, `p`'s point at its lowest `x`, below `q`'s range once moved) extends the
        // point of `q` with the callee's constraints fixed there, as it did when `p` was
        // translated at `x + 3`, instead of being decided whole twice, once for the answer and
        // once for the point (80 links: 1.6 to 2.2 s with the largest part alone, 0.39 s now, 0.44 s
        // when each link translated its callee again). A part that holds nowhere settles it.
        // Otherwise it is decided whole.
        // Complexity tradeoff: each other part tried reads the rest of the conjunction, the
        // largest part among it, so a link that extends none costs O(its kept parts times the
        // whole) before it is decided whole. Why: which part's point extends is not known
        // before it is tried. Trigger: a link whose callees' points all fall outside it; a link
        // calls few functions, so the factor is small. Test
        // `l01_38_presburger::one_scope::each_answer_through_arguments_that_are_not_names_is_the_answer_of_the_relation_whole`
        // (the chain `p{i}(x) = q(x: x) && p{i-1}(x: x + 3)`).
        // COMPLEXITY.md row LOAD-chain-affine.
        let mut holds = None;
        for &(j, k) in &parts {
            let (Ok(true), Some(m)) = (&k.answers.holds, &k.point) else {
                if matches!(k.answers.holds, Ok(false)) {
                    holds = Some((Ok(false), None));
                    break;
                }
                continue;
            };
            let rest_j = match j == at {
                true => rest.clone(),
                false => Formula::and(
                    (kids.iter().enumerate())
                        .filter(|&(i, _)| i != j)
                        .map(|(_, h)| h.clone())
                        .collect(),
                ),
            };
            if let Some(p) = met(m, &new(&rest_j, m)) {
                holds = Some((Ok(true), Some(p)));
                break;
            }
        }
        let (holds, point) = holds.unwrap_or_else(|| holds_whole(g, def));
        // The part holds everywhere, so the whole fails where the other parts do. Their
        // negation with only the new definitions holds where the full one does (the others'
        // variables left free), so it never holding settles it; one point of it that extends
        // the part's point satisfies every definition, so that settles it too; otherwise it is
        // decided with all the definitions it reaches.
        let not = Formula::negate(rest.clone());
        let (fails, miss) = match part.answers.fails {
            // The part fails somewhere, but a call binds the part's atoms to its arguments
            // (LOAD-chain-affine), and arguments whose map is not onto, as `x: 2 * x`, may reach
            // no point where it fails. So the whole fails where the part's point of negation
            // extends to the definitions the other parts reach past it, which bind the part's
            // atoms to the whole's: the part fails there, whatever the other parts do.
            // Otherwise it fails where the other parts fail, with the definitions they reach:
            // each binding gives the part's atoms one value at any point of the whole's own
            // atoms, and the part's definitions hold there for some value of their variables.
            // Otherwise it is decided whole.
            Ok(true) => {
                let extended = (part.miss.as_ref())
                    .and_then(|m| met(m, &with(&reached_past(&rest, def, m), Formula::top())));
                match extended {
                    Some(p) => (Ok(true), Some(p)),
                    None => match decide_defined(&mut self.sums, not, def) {
                        Ok(true) => (Ok(true), None),
                        _ => fails_whole(&mut self.sums, g, def),
                    },
                }
            }
            Ok(false) => {
                let short = part.point.as_ref().and_then(|m| {
                    let f = new(&not, m);
                    match decide(&f) {
                        Ok(false) => Some((false, None)),
                        _ => met(m, &f).map(|p| (true, Some(p))),
                    }
                });
                match short {
                    Some((b, miss)) => (Ok(b), miss),
                    None => match decide_defined(&mut self.sums, not, def) {
                        Ok(b) => (Ok(b), None),
                        Err(_) => fails_whole(&mut self.sums, g, def),
                    },
                }
            }
            Err(_) => fails_whole(&mut self.sums, g, def),
        };
        Known {
            answers: Answers { holds, fails },
            point,
            miss,
            size: part.size + rest.atoms().len(),
        }
    }
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
    found(&with(&reached(g, def), g.clone()))
}

/// Whether `f` holds somewhere, with a point when it does and the solver gives one, every atom
/// of `f` given a value.
fn found(f: &Formula) -> (Result<bool, Refusal>, Option<Point>) {
    match decide(f) {
        Ok(true) => (Ok(true), point(f)),
        other => (other, None),
    }
}

/// A point where `f` holds, every atom of `f` given a value, when the solver gives one.
fn point(f: &Formula) -> Option<Point> {
    satisfiable(f).ok().flatten().map(|m| {
        let mut p: Point = m.into_iter().collect();
        for a in f.atoms() {
            p.entry(a).or_default();
        }
        p
    })
}

/// Whether the negation of `g` and its definitions hold somewhere, decided whole (with the
/// summaries of the definitions where they answer, [`decide_defined`]), with a point where it
/// holds as [`holds_whole`] gives one, found with every definition it reaches.
fn fails_whole(
    sums: &mut Summaries,
    g: &Formula,
    def: &dyn Fn(u32) -> Formula,
) -> (Result<bool, Refusal>, Option<Point>) {
    let not = Formula::negate(g.clone());
    match decide_defined(sums, not.clone(), def) {
        Ok(true) => (Ok(true), point(&with(&reached(g, def), not))),
        other => (other, None),
    }
}

/// The answers of `g`, decided whole.
fn whole(sums: &mut Summaries, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Known {
    let (holds, point) = holds_whole(g, def);
    let (fails, miss) = fails_whole(sums, g, def);
    Known {
        answers: Answers { holds, fails },
        point,
        miss,
        size: g.atoms().len(),
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
    /// not be together, or when a symbol one summary projects out ([`Summary::hidden`]) is
    /// read by `f` or by another summary. Time of `f` and of the summaries made, each made
    /// once.
    fn read(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Option<Vec<Formula>> {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut bottoms: HashSet<Id> = HashSet::new();
        let mut read: HashSet<Atom> = f.atoms().into_iter().collect();
        let mut hidden: HashSet<Atom> = HashSet::new();
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
            for h in &s.hidden {
                if !hidden.insert(h.clone()) {
                    return None;
                }
            }
            read.extend(s.rows.atoms());
            out.push(s.rows.clone());
        }
        hidden.is_disjoint(&read).then_some(out)
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
                hidden: HashSet::new(),
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
        // The symbols `d` binds: each set with coefficient ±1 by an equality of `d` that holds
        // no variable `d` defines, and read by the input's summary. A question is asked of
        // the summaries and `f` together, existentially, so projecting a symbol out of one
        // summary is exact when no other part reads it: `read` checks `f` and the other
        // summaries' rows. The definitions a summary projected out are on its own path, which
        // another summary reaches only with the same bottom, refused there. Only `d`'s own
        // symbols are kept, not those of the summaries below, which are on the same path, so a
        // path of n bindings holds n symbols in all and not n²/2.
        let below_atoms = below.rows.atoms();
        let mut hidden = HashSet::new();
        let own = |a: &Atom| matches!(a, Atom::Aux(n) if Id::any(&def(*n)) == *id);
        for c in &rows {
            if c.rel != Rel::Eq || c.lin.terms.keys().any(own) {
                continue;
            }
            for (a, k) in &c.lin.terms {
                if matches!(a, Atom::Sym(_)) && k.is_unit() && below_atoms.contains(a) {
                    keep.remove(a);
                    hidden.insert(a.clone());
                }
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
            hidden,
        }))
    }
}

/// What [`Summaries::make`] gives: the summary, `None` where none is made, or the input
/// definition whose summary is made first.
enum Made {
    Done(Option<Summary>),
    First(Formula),
}
