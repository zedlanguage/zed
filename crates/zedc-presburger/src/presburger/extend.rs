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
//!
//! A kept conjunction whose caller reads it at a few atoms is read beside another kept part
//! through its face (LOAD-call-summary): the conjunction and its definitions projected exactly
//! onto those atoms, made from the faces of its own kept parts, so a link of a chain that
//! extends the point of a small callee beside the chain (`p{i}(x) = q(x: x) && p{i-1}(x: x + 3)
//! && x < 1000 * i`) reads O(1) rows, not the chain.
//!
//! A face of a conjunction with a disjunction keeps it as a clause, projected exactly, the rows
//! beside one disjunction copied into each of its disjuncts (LOAD-disj-residue), and keeps each
//! clause once: two clauses that differ only in the names of their quotients and their written
//! order say the same once each quotient's equality is read as the congruence it says. So a
//! chain whose callee is `q(x) = (x mod 3 == 1 || x mod 5 == 2) && ...` reads at most five
//! clauses a link, one for each residue of the shift modulo 5. The face never lists residue
//! classes, so its size is bounded by the clauses written and not by the least common
//! multiple of the moduli.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use super::formula::Rel;
use super::{
    Atom, Con, Factor, Formula, Id, Lin, Model, Refusal, decide, nnf, satisfiable, shadow,
};
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

/// A set of atoms, shared: the atoms of a conjunction are its largest part's with the others'
/// added, O(log n) each, and copy nothing.
type Atoms = imbl::OrdSet<Atom>;

/// The atoms a caller reads of each kept part, by the part: those its call binds
/// ([`Extending::defined_with`]), `None` for a part no call binds.
pub type Interface<'a> = &'a dyn Fn(&Formula) -> Option<Vec<Atom>>;

/// What is remembered of a decided conjunction: its answers, and a point where it and its
/// definitions hold when it holds and the solver gave one. The point gives a value to every
/// atom of the conjunction and of its definitions, so that a part added beside it, with
/// atoms of its own, is met by giving values to those alone; but a point found with a kept
/// part read through its face ([`Face`]) gives none to the atoms the face projects out, which a
/// question that reads one may not use ([`given`]).
struct Known {
    answers: Answers,
    point: Option<Point>,
    /// A point where its negation and its definitions hold, when it fails and the solver or
    /// an extension gave one, every atom of them given a value as in `point`.
    miss: Option<Point>,
    /// How many atoms it holds, its parts' counted once for each part they are in: which of
    /// two kept parts is the larger ([`Extending::extend`]).
    size: usize,
    /// Every atom of the conjunction and of the definitions it reaches.
    closure: Atoms,
}

/// A kept conjunction and the definitions it reaches, projected exactly onto the atoms its
/// caller reads ([`Interface`]), with every atom [`shadow`] does not eliminate kept: a point of
/// `rows` extends to a point of the conjunction and its definitions with the same values on
/// `atoms`, and on no other atom, so the rows stand for the conjunction in a question that
/// reads none of its other atoms. Rows of atoms none of the caller's reads are dropped, since
/// the conjunction holds and so they hold somewhere apart. A conjunction with a disjunction
/// keeps it as a clause (LOAD-disj-residue): `rows` and `clauses` together are the projection
/// ([`projected`]), each clause a disjunction, and `atoms` holds the atoms of the clauses too:
/// a quotient a clause alone reads, and an atom two disjunctions share, which is kept and not
/// projected out ([`project`]); a clause that says what another says is kept once
/// ([`Face::of`]).
struct Face {
    rows: Vec<Con>,
    clauses: Vec<Formula>,
    atoms: HashSet<Atom>,
}

/// The answers of conjunctions decided so far, by the part each is, and the summaries of the
/// definitions read so far.
#[derive(Default)]
pub struct Extending {
    known: HashMap<Id, Known>,
    sums: Summaries,
    faces: Faces,
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
        self.defined_with(f, def, &|_| None)
    }

    /// [`Extending::defined`], where `iface` gives the atoms a caller reads of each kept part
    /// (the canonical atoms a claimed call binds, or the atoms of the arguments of a callee's
    /// body read again: `preimage::Scoped::interface`), so that a link whose point is found
    /// beside a kept part reads that part through its face (`Face`, LOAD-call-summary). The
    /// answers are those [`Extending::defined`] gives, since each face is exact; every formula
    /// asked of one `Extending` is read with the same `iface`.
    pub fn defined_with(
        &mut self,
        f: &Formula,
        def: &dyn Fn(u32) -> Formula,
        iface: Interface,
    ) -> Answers {
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
                let mut k = self.extend(&g, def, iface);
                k.closure = self.closure(&g, def);
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
    fn extend(&mut self, g: &Formula, def: &dyn Fn(u32) -> Formula, iface: Interface) -> Known {
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
        // A part other than the largest is tried with each other kept part read through its face
        // where one is made and nothing beside it reads an atom it projects out ([`Face`],
        // LOAD-call-summary), so the drifting chain `p{i}(x) = q(x: x) && p{i-1}(x: x + 3) && x
        // < 1000 * i`, whose `q` point serves each link, reads O(1) rows a link and not the
        // chain (160 links: 1.80 s before, 0.13 s now; test
        // `l01_38_presburger::one_scope::the_questions_of_a_drifting_chain_scale`). Each face is exact, so the point is
        // found where the whole one would be; where the solver refuses the question with faces,
        // or none is read, the question is asked with the parts themselves, as before.
        // A part with a disjunction or a negation (an `if`, `min`, `max`, `abs`, `!=`, an
        // `||`, a `div` or `mod` by a variable) has a face too, its disjunctions kept as
        // clauses, each clause said once (LOAD-disj-residue, [`clauses_once`]): the chain with
        // `q = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 1000000` keeps five clauses a
        // link, one for each residue of the shift modulo 5, and not one for each link (160
        // links: 5.40 s before, 0.27 s now; test
        // `l01_38_presburger::one_scope::the_questions_of_a_drifting_disjunctive_chain_scale`).
        // Complexity tradeoff: a kept part with no face is read whole, as before: one that
        // holds a product, a let-bound name (no call binds it, so its caller's atoms are not
        // known), one that does not hold, and one beside which an atom it projects out is
        // read; and a face holds one clause for each link whose clause differs from every
        // other's, so a link reads O(its depth) clauses and the chain O(n²): a disjunction of
        // bounds that the call moves (`(x < 10 || x > 20)` read at `x + 3`), a residue whose
        // modulus exceeds the chain's length, and an atom two disjunctions share ([`project`]),
        // which keeps its name in each link. Why: the clauses are merged where they say the
        // same, not where one implies another or several say what one says; deciding that a
        // clause of congruences is implied by others is co-NP-hard (simultaneous incongruences,
        // Garey and Johnson problem AN2), and the union of moved holes is one interval each
        // where they do not overlap. Trigger: the chain above with `q = (x < 10 || x > 20) &&
        // x > 0 && x < 1000000`: 1.68 s at 80 links, 1.91 s before (measured once, debug). Test
        // `l01_38_presburger::one_scope::each_answer_of_a_random_disjunctive_chain_is_the_answer_of_the_relation_whole`.
        // COMPLEXITY.md row LOAD-disj-residue. A complete solution for bounds keeps the holes of
        // the clauses over one term as an ordered map of disjoint intervals, merged at each
        // link in O(log n).
        let mut holds = None;
        for &(j, k) in &parts {
            let (Ok(true), Some(m)) = (&k.answers.holds, &k.point) else {
                if matches!(k.answers.holds, Ok(false)) {
                    holds = Some((Ok(false), None));
                    break;
                }
                continue;
            };
            if j != at {
                let others = (kids.iter().enumerate()).filter(|&(i, _)| i != j);
                self.faces
                    .make(&self.known, others.map(|(_, h)| h), def, iface);
                match self.faces.met(&self.known, kids, j, m, def) {
                    Some(Ok(Some(p))) => {
                        holds = Some((Ok(true), Some(p)));
                        break;
                    }
                    Some(Ok(None)) => continue,
                    Some(Err(_)) | None => {}
                }
            }
            let rest_j = match j == at {
                true => rest.clone(),
                false => Formula::and(
                    (kids.iter().enumerate())
                        .filter(|&(i, _)| i != j)
                        .map(|(_, h)| h.clone())
                        .collect(),
                ),
            };
            let f = new(&rest_j, m);
            if given(&k.closure, m, &f)
                && let Ok(Some(p)) = met(m, &f)
            {
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
                let extended = (part.miss.as_ref()).and_then(|m| {
                    met(m, &with(&reached_past(&rest, def, m), Formula::top()))
                        .ok()
                        .flatten()
                });
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
                        _ => met(m, &f).ok().flatten().map(|p| (true, Some(p))),
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
            closure: Atoms::new(),
        }
    }

    /// The atoms of the conjunction `g`, whose kept parts are known, and of the definitions it
    /// reaches: its largest kept part's, with the others' added, the atoms of its other parts,
    /// and those of the definitions they reach past these. O(log n) for each atom added, so a
    /// chain of n links costs O(n log n) in all, each link's own atoms added once.
    fn closure(&self, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Atoms {
        let mut parts: Vec<&Atoms> = Vec::new();
        let mut own: Vec<Atom> = Vec::new();
        for h in g.kids() {
            match h {
                Formula::And(_) if let Some(k) = self.known.get(&Id::any(h)) => {
                    parts.push(&k.closure)
                }
                _ => own.extend(h.atoms()),
            }
        }
        parts.sort_by_key(|s| std::cmp::Reverse(s.len()));
        let mut out = parts.first().map(|&s| s.clone()).unwrap_or_default();
        for s in parts.iter().skip(1) {
            out.extend(s.iter().cloned());
        }
        let mut seen: HashSet<u32> = HashSet::new();
        let mut todo: Vec<u32> = own.iter().flat_map(auxes).collect();
        out.extend(own);
        while let Some(n) = todo.pop() {
            if !seen.insert(n) || parts_hold(&parts, n) {
                continue;
            }
            let d = def(n);
            let atoms = d.atoms();
            todo.extend(atoms.iter().flat_map(auxes));
            out.extend(atoms);
        }
        out
    }
}

/// The faces of the kept conjunctions, each once asked: `None` where none is made.
#[derive(Default)]
struct Faces {
    by: HashMap<Id, Option<Face>>,
}

impl Faces {
    /// The faces of the kept parts among `roots` and of the kept parts under them, each made
    /// once, after those of its own kept parts: an explicit stack, since the parts nest as deep
    /// as the chain of calls, and the faces made are the visited set.
    fn make<'f>(
        &mut self,
        known: &HashMap<Id, Known>,
        roots: impl Iterator<Item = &'f Formula>,
        def: &dyn Fn(u32) -> Formula,
        iface: Interface,
    ) {
        let unmade = |by: &HashMap<Id, Option<Face>>, h: &Formula| {
            matches!(h, Formula::And(_))
                && known.contains_key(&Id::any(h))
                && !by.contains_key(&Id::any(h))
        };
        let mut stack: Vec<Formula> = roots.filter(|h| unmade(&self.by, h)).cloned().collect();
        while let Some(g) = stack.last() {
            if !unmade(&self.by, g) {
                stack.pop();
                continue;
            }
            let below: Vec<Formula> = (g.kids().iter())
                .filter(|h| unmade(&self.by, h))
                .cloned()
                .collect();
            if !below.is_empty() {
                stack.extend(below);
                continue;
            }
            let face = self.face(known, g, def, iface);
            self.by.insert(Id::any(g), face);
            stack.pop();
        }
    }

    /// The face of the known conjunction `g`, whose kept parts' faces are made: `shadow` of its
    /// constraints, the definitions they reach past its kept parts, and its kept parts' faces,
    /// onto the atoms its caller reads, or, where any of them holds a disjunction or a
    /// negation, their projection by [`projected`]. Exact: each part's face stands for it
    /// where nothing else read with it reads an atom the face projects out, which is checked,
    /// and `shadow` eliminates an atom only where that is exact. `None` where `g` does not
    /// hold, no call binds it, it or a definition it reaches holds a product, or a kept part
    /// has no face or is read at an atom its face projects out. Time of `g`'s own parts and
    /// definitions and of its parts' faces, and, for each two kept parts, of the smaller of
    /// their atoms, and of [`projected`].
    fn face(
        &self,
        known: &HashMap<Id, Known>,
        g: &Formula,
        def: &dyn Fn(u32) -> Formula,
        iface: Interface,
    ) -> Option<Face> {
        let k = known.get(&Id::any(g))?;
        if k.answers.holds != Ok(true) {
            return None;
        }
        let mut keep: HashSet<Atom> = iface(g)?.into_iter().collect();
        let mut rows: Vec<Con> = Vec::new();
        // Its disjunctions and negations, and the definitions it reaches that are not
        // conjunctions of constraints (LOAD-disj-residue).
        let mut ors: Vec<Formula> = Vec::new();
        let mut parts: Vec<(&Known, &Face)> = Vec::new();
        for h in g.kids() {
            match h {
                Formula::Con(c) => rows.push(c.clone()),
                Formula::And(_) => {
                    let id = Id::any(h);
                    parts.push((known.get(&id)?, self.by.get(&id)?.as_ref()?));
                }
                Formula::Not(_) | Formula::Or(_) => ors.push(h.clone()),
            }
        }
        // The definitions its own constraints reach past its kept parts, whose own are in
        // their faces.
        let mut seen: HashSet<u32> = HashSet::new();
        let mut todo: Vec<u32> = (rows.iter())
            .flat_map(|c| c.lin.terms.keys().flat_map(auxes).collect::<Vec<_>>())
            .chain(
                ors.iter()
                    .flat_map(|h| h.atoms().iter().flat_map(auxes).collect::<Vec<_>>()),
            )
            .collect();
        while let Some(n) = todo.pop() {
            let a = Atom::Aux(n);
            if !seen.insert(n) || parts.iter().any(|(p, _)| p.closure.contains(&a)) {
                continue;
            }
            let d = def(n);
            match constraints(&d) {
                Some(cs) => {
                    for c in cs {
                        todo.extend(c.lin.terms.keys().flat_map(auxes));
                        rows.push(c.clone());
                    }
                }
                None => {
                    todo.extend(d.atoms().iter().flat_map(auxes));
                    ors.push(d);
                }
            }
        }
        let own: HashSet<Atom> = (rows.iter())
            .flat_map(|c| c.lin.terms.keys().cloned())
            .chain(ors.iter().flat_map(Formula::atoms))
            .collect();
        if own.iter().any(|a| matches!(a, Atom::Product(..))) {
            return None;
        }
        for (i, &(p, face)) in parts.iter().enumerate() {
            let others = (parts.iter().enumerate()).filter(|&(j, _)| j != i);
            if own.iter().any(|a| hidden(p, face, a))
                || others
                    .into_iter()
                    .any(|(_, (o, _))| !apart(&o.closure, p, face))
            {
                return None;
            }
        }
        for (_, face) in &parts {
            rows.extend(face.rows.iter().cloned());
            ors.extend(face.clauses.iter().cloned());
        }
        if ors.is_empty() {
            let rows = shadow(&rows, &|a| keep.contains(a), true)?;
            return Some(Face::of(rows, Vec::new(), &keep));
        }
        let (rows, clauses) = projected(rows, ors, &mut keep)?;
        Some(Face::of(rows, clauses, &keep))
    }

    /// A point of the conjunction `g` (whose parts are `kids`) that extends the point `m` of its
    /// kept part `kids[j]`, found with each other kept part that has a face read through it,
    /// with the definitions the question reaches past `m` and those faces' parts: `None` when
    /// no other part has a face or an atom a face projects out is read beside it, and
    /// otherwise what [`met`] gives, `Ok(None)` too when the question reads an atom of the part
    /// `m` gives no value ([`given`]). Time of the faces, the other parts and the definitions
    /// reached, and, for each part read through its face, of the smaller of its atoms and each
    /// other part's.
    fn met(
        &self,
        known: &HashMap<Id, Known>,
        kids: &[Formula],
        j: usize,
        m: &Point,
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<Result<Option<Point>, Refusal>> {
        let kj = &known[&Id::any(&kids[j])];
        let mut faced: Vec<(&Known, &Face)> = Vec::new();
        let mut whole: Vec<&Known> = vec![kj];
        let mut rows: Vec<Formula> = Vec::new();
        let mut beside: HashSet<Atom> = HashSet::new();
        for (i, h) in kids.iter().enumerate() {
            if i == j {
                continue;
            }
            let id = matches!(h, Formula::And(_)).then(|| Id::any(h));
            let k = id.as_ref().and_then(|id| known.get(id));
            match k.and_then(|k| Some((k, self.by.get(id.as_ref()?)?.as_ref()?))) {
                Some((k, face)) => {
                    faced.push((k, face));
                    rows.extend(face.rows.iter().cloned().map(Formula::Con));
                    rows.extend(face.clauses.iter().cloned());
                }
                None => {
                    match k {
                        Some(k) => whole.push(k),
                        None => beside.extend(h.atoms()),
                    }
                    rows.push(h.clone());
                }
            }
        }
        if faced.is_empty() {
            return None;
        }
        let base = Formula::and(rows);
        let past = |a: &Atom| m.contains_key(a) || faced.iter().any(|(k, _)| k.closure.contains(a));
        let defs = reached_by(&base, def, &past);
        for d in &defs {
            beside.extend(d.atoms());
        }
        for (i, &(k, face)) in faced.iter().enumerate() {
            let others = (faced.iter().enumerate())
                .filter(|&(n, _)| n != i)
                .map(|(_, (o, _))| *o);
            if beside.iter().any(|a| hidden(k, face, a))
                || (whole.iter().copied().chain(others)).any(|o| !apart(&o.closure, k, face))
            {
                return None;
            }
        }
        let f = with(&defs, base);
        if !given(&kj.closure, m, &f) {
            return Some(Ok(None));
        }
        Some(met(m, &f))
    }
}

impl Face {
    /// The face of `rows` and `clauses`, a projection onto `keep` of a conjunction that holds:
    /// each row once, each congruence once ([`congruences_once`]), each clause once
    /// ([`clauses_once`]), and the rows and clauses of each group linked by shared atoms that
    /// reads none of `keep` dropped, since the conjunction holds and so each such group holds
    /// somewhere apart. Time of the rows and clauses, near linear.
    fn of(rows: Vec<Con>, clauses: Vec<Formula>, keep: &HashSet<Atom>) -> Face {
        let rows: Vec<Con> = (rows.into_iter())
            .filter(|c| !c.lin.terms.is_empty())
            .collect::<std::collections::BTreeSet<Con>>()
            .into_iter()
            .collect();
        let in_clauses: HashSet<Atom> = clauses.iter().flat_map(Formula::atoms).collect();
        let rows = congruences_once(rows, keep, &in_clauses);
        drop(in_clauses);
        let clauses = clauses_once(clauses, &rows, keep);
        // The atoms of each row and then of each clause.
        let reads: Vec<Vec<Atom>> = (rows.iter())
            .map(|c| c.lin.terms.keys().cloned().collect())
            .chain(clauses.iter().map(|f| f.atoms().into_iter().collect()))
            .collect();
        // The groups, by a union of the atoms each row or clause reads: each atom's index, and
        // the index each points to, followed to its group's by halving.
        let mut index: HashMap<&Atom, usize> = HashMap::new();
        for a in reads.iter().flatten() {
            let n = index.len();
            index.entry(a).or_insert(n);
        }
        let mut up: Vec<usize> = (0..index.len()).collect();
        for atoms in &reads {
            let mut atoms = atoms.iter().map(|a| index[a]);
            let Some(first) = atoms.next() else { continue };
            for a in atoms {
                let (r, s) = (root(&mut up, first), root(&mut up, a));
                up[s] = r;
            }
        }
        let kept: HashSet<usize> = (keep.iter())
            .filter_map(|a| index.get(a).copied())
            .map(|a| root(&mut up, a))
            .collect();
        // A clause with no atom holds, since the conjunction does, and is dropped.
        let mut read = (reads.iter())
            .map(|atoms| (atoms.first()).is_some_and(|a| kept.contains(&root(&mut up, index[a]))));
        let rows: Vec<Con> = (rows.into_iter())
            .filter(|_| read.next().expect("a row's group"))
            .collect();
        let clauses: Vec<Formula> = (clauses.into_iter())
            .filter(|_| read.next().expect("a clause's group"))
            .collect();
        drop(read);
        drop(index);
        let atoms = (rows.iter())
            .flat_map(|c| c.lin.terms.keys().cloned())
            .chain(clauses.iter().flat_map(Formula::atoms))
            .collect();
        Face {
            rows,
            clauses,
            atoms,
        }
    }
}

/// The group of the atom at `a`, by the index each points to, the path halved on the way.
fn root(up: &mut [usize], mut a: usize) -> usize {
    while up[a] != a {
        up[a] = up[up[a]];
        a = up[a];
    }
    a
}

/// The terms and constant of a congruence, each a residue modulo `modulus`.
#[derive(PartialEq, Eq, Hash)]
struct Congruence {
    modulus: Int,
    terms: Vec<(Atom, Int)>,
    constant: Int,
}

impl Congruence {
    /// The congruence the equality `c` says when it reads an atom `lone` holds of: that the
    /// rest of its term is a multiple of that atom's coefficient. Of the residues of the rest
    /// and of its negation, which say it alike, the smaller names it. `None` for an inequality
    /// or an equality with no such atom.
    fn of(c: &Con, lone: &dyn Fn(&Atom) -> bool) -> Option<Congruence> {
        let q = (c.lin.terms.iter()).find(|(a, _)| lone(a));
        let (Rel::Eq, Some((q, d))) = (c.rel, q) else {
            return None;
        };
        let d = d.abs();
        let residues = |sign: &Int| {
            let terms: Vec<(Atom, Int)> = (c.lin.terms.iter())
                .filter(|(a, _)| *a != q)
                .map(|(a, e)| (a.clone(), (e * sign).mod_floor(&d)))
                .filter(|(_, r)| !r.is_zero())
                .collect();
            (terms, (&c.lin.constant * sign).mod_floor(&d))
        };
        let (terms, constant) = residues(&Int::from(1)).min(residues(&Int::from(-1)));
        Some(Congruence {
            modulus: d,
            terms,
            constant,
        })
    }

    /// The congruence written as one equality, its lone atom replaced by a product of two
    /// auxiliary variables numbered `u32::MAX`: no face holds a product ([`Faces::face`]), so
    /// the equality is that of no row, and two rows that say the same congruence give the same
    /// one. Read only as a key ([`clauses_once`]).
    fn key(self) -> Con {
        let stand = Atom::Product(Factor::Aux(u32::MAX), Factor::Aux(u32::MAX));
        Con {
            lin: Lin {
                terms: std::iter::once((stand, self.modulus))
                    .chain(self.terms)
                    .collect(),
                constant: self.constant,
            },
            rel: Rel::Eq,
        }
    }
}

/// `rows` with each congruence said once. An equality that reads an atom outside `keep` no other
/// row reads, nor any atom of `also` (the clauses beside the rows), says only that the rest of
/// its term is a multiple of that atom's coefficient ([`Congruence::of`]): the atom is a
/// quotient `shadow` could not eliminate, since it substitutes unit equalities only. Of the
/// rows that say the same congruence one is kept, and a row whose congruence always holds is
/// dropped; this keeps the face of a chain of `x mod 3 == 1` tests at one row however long the
/// chain (LOAD-call-summary). Exact: the dropped row's lone atom is read nowhere else, so the
/// rows kept, with that atom projected out, say the same of every other atom. Time of the rows,
/// near linear.
fn congruences_once(rows: Vec<Con>, keep: &HashSet<Atom>, also: &HashSet<Atom>) -> Vec<Con> {
    enum Says {
        Row,
        Nothing,
        Congruence(Congruence),
    }
    let mut reads: HashMap<&Atom, usize> = HashMap::new();
    for c in &rows {
        for a in c.lin.terms.keys() {
            *reads.entry(a).or_default() += 1;
        }
    }
    let lone = |a: &Atom| reads[a] == 1 && !keep.contains(a) && !also.contains(a);
    let says: Vec<Says> = (rows.iter())
        .map(|c| match Congruence::of(c, &lone) {
            None => Says::Row,
            Some(k) => match (k.terms.is_empty(), k.constant.is_zero()) {
                (true, true) => Says::Nothing,
                // A congruence that never holds: kept, though a face is made only where its
                // rows hold.
                (true, false) => Says::Row,
                (false, _) => Says::Congruence(k),
            },
        })
        .collect();
    drop(reads);
    let mut said: HashSet<Congruence> = HashSet::new();
    (rows.into_iter().zip(says))
        .filter_map(|(c, s)| match s {
            Says::Row => Some(c),
            Says::Nothing => None,
            Says::Congruence(k) => said.insert(k).then_some(c),
        })
        .collect()
}

/// `clauses` with each said once (LOAD-disj-residue): two clauses say the same when they are
/// alike once each equality that reads a quotient is read as the congruence it says
/// ([`Congruence::of`]) and the parts of each conjunction and disjunction are sorted. A
/// quotient of a clause is an atom outside `keep` that no row and no other clause reads, and
/// that no two parts of one conjunction in the clause read and no negation in it reads
/// ([`joined`]). Exact: the existential of such an atom distributes over each disjunction and
/// each conjunction of the clause down to its constraints, and that of an equality that reads it
/// is the congruence the equality says, so a clause with its quotients projected out is its
/// key, and a clause whose key is that of one kept adds nothing to the projection. So a link of
/// the chain `p{i}(x) = q(x: x) && p{i-1}(x: x + 3)` with `q = (x mod 3 == 1 || x mod 5 == 2)
/// && ...` keeps one clause for each residue of the shift modulo 5, five in all, however long
/// the chain. Time of the clauses and rows, near linear.
fn clauses_once(clauses: Vec<Formula>, rows: &[Con], keep: &HashSet<Atom>) -> Vec<Formula> {
    let mut reads: HashMap<Atom, usize> = HashMap::new();
    let atoms = (rows
        .iter()
        .map(|c| c.lin.terms.keys().cloned().collect::<Vec<Atom>>()))
    .chain(clauses.iter().map(|f| f.atoms().into_iter().collect()));
    for a in atoms.flatten() {
        *reads.entry(a).or_default() += 1;
    }
    let mut said: HashSet<Formula> = HashSet::new();
    (clauses.into_iter())
        .filter(|f| {
            let joined = joined(f);
            let lone = |a: &Atom| reads[a] == 1 && !keep.contains(a) && !joined.contains(a);
            said.insert(clause_key(f, &lone))
        })
        .collect()
}

/// The atoms of `f` that two parts of one conjunction in it read, or a negation in it reads:
/// those whose existential does not distribute down to the constraints of `f`. One fold over
/// the distinct parts of `f`, each part's atoms merged into its largest part's, so each atom
/// is moved O(log n) times.
fn joined(f: &Formula) -> HashSet<Atom> {
    let mut out: HashSet<Atom> = HashSet::new();
    f.fold(
        (),
        |_, ()| (),
        |g, (), mut parts: Vec<HashSet<Atom>>| match g {
            Formula::Con(c) => c.lin.terms.keys().cloned().collect(),
            Formula::Not(_) => {
                let read = parts.pop().expect("one part");
                out.extend(read.iter().cloned());
                read
            }
            Formula::And(_) | Formula::Or(_) => {
                let Some(big) = (0..parts.len()).max_by_key(|&i| parts[i].len()) else {
                    return HashSet::new();
                };
                let mut read = parts.swap_remove(big);
                for a in parts.into_iter().flatten() {
                    if !read.contains(&a) {
                        read.insert(a);
                    } else if matches!(g, Formula::And(_)) {
                        out.insert(a);
                    }
                }
                read
            }
        },
    );
    out
}

/// The key of the clause `f` ([`clauses_once`]): each equality that reads an atom `lone` holds
/// of read as its congruence ([`Congruence::key`]), and the parts of each conjunction and
/// disjunction flattened, sorted and said once. One pass over the distinct parts of `f`.
fn clause_key(f: &Formula, lone: &dyn Fn(&Atom) -> bool) -> Formula {
    f.fold(
        (),
        |_, ()| (),
        |g, (), parts: Vec<Formula>| match g {
            Formula::Con(c) => {
                Formula::Con(Congruence::of(c, lone).map_or_else(|| c.clone(), Congruence::key))
            }
            Formula::Not(_) => Formula::Not(Arc::new(parts.into_iter().next().expect("one part"))),
            Formula::And(_) | Formula::Or(_) => {
                let and = matches!(g, Formula::And(_));
                let mut kids: Vec<Formula> = Vec::new();
                for h in parts {
                    match h {
                        Formula::And(_) if and => {
                            kids.extend(h.into_parts().expect("a conjunction"))
                        }
                        Formula::Or(_) if !and => {
                            kids.extend(h.into_parts().expect("a disjunction"))
                        }
                        h => kids.push(h),
                    }
                }
                kids.sort();
                kids.dedup();
                match and {
                    true => Formula::And(Arc::new(kids)),
                    false => Formula::Or(Arc::new(kids)),
                }
            }
        },
    )
}

/// The conjunction of `rows` and `ors` (disjunctions and negations) projected exactly onto
/// `keep` (LOAD-disj-residue): rows over `keep` and atoms [`shadow`] could not eliminate, and
/// clauses, each a disjunction, an atom of a clause outside `keep` read by that clause alone.
/// `keep` gains the atoms that had to be kept to make it so ([`project`]). `None` where the
/// conjunction holds nowhere.
fn projected(
    rows: Vec<Con>,
    ors: Vec<Formula>,
    keep: &mut HashSet<Atom>,
) -> Option<(Vec<Con>, Vec<Formula>)> {
    let items: Vec<Formula> = (rows.into_iter().map(Formula::Con))
        .chain(ors.iter().map(|h| nnf(h, true)))
        .collect();
    let (mut rows, mut clauses) = (Vec::new(), Vec::new());
    let mut todo = vec![project(items, keep)];
    while let Some(h) = todo.pop() {
        match h {
            Formula::Con(ref c) => rows.push(c.clone()),
            Formula::And(_) => todo.extend(h.into_parts().expect("a conjunction")),
            Formula::Or(ref gs) if gs.is_empty() => return None,
            Formula::Or(_) | Formula::Not(_) => clauses.push(h),
        }
    }
    Some((rows, clauses))
}

/// The conjunction of `items` (in negation normal form) with the atoms outside `keep`
/// projected out, exactly: `false` where it holds nowhere. Each step splits a conjunction into
/// groups linked by the atoms outside `keep` they read ([`split`]); a group of rows alone is
/// projected by [`shadow`], and a group with one disjunction is the disjunction, over its
/// disjuncts, of the projection of the group's rows with that disjunct, each projected in turn;
/// a group with two disjunctions or more keeps the atoms its disjunctions read that another of
/// its parts reads (added to `keep`), which leaves each disjunction in a group of its own. Each
/// projection is exact: the existential of a conjunction of parts with no projected atom in
/// common is the conjunction of their existentials, and the existential of a disjunction is the
/// disjunction of its disjuncts'. An explicit stack, since disjunctions nest as deep as the
/// formula.
// Complexity tradeoff: a group's rows are copied into each disjunct of its disjunction, so a
// group of r rows beside a disjunction of d disjuncts costs O(r d), as the solver's own
// projection, the union over each disjunct of the base with that disjunct, does; and two
// disjunctions that read one projected atom keep it, so the face holds that atom and is read
// with it, and is not smaller than the formula. Why: projecting two disjunctions that share an
// atom exactly writes out their product, d1 d2 disjuncts and more with each further one, which
// is exponential in the number of disjunctions; one variable under congruences with distinct
// moduli encodes the satisfiability of clauses (simultaneous incongruences, NP-complete: Garey
// and Johnson, problem AN2), so no exact projection of polynomial size is known for it.
// Trigger: two disjunctions over one `x mod n`, as `(x mod 6 == 1 || y > 0) && (x mod 6 == 5
// || z > 0)`. Test
// `l01_38_presburger::one_scope::each_answer_of_a_random_disjunctive_chain_is_the_answer_of_the_relation_whole`.
// COMPLEXITY.md row LOAD-disj-residue. A complete solution needs a projection that keeps such
// disjunctions in a shared form, a decision diagram over their cases.
fn project(items: Vec<Formula>, keep: &mut HashSet<Atom>) -> Formula {
    enum Step {
        Split(Vec<Formula>),
        /// The conjunction of these parts and the results of the next `n` steps.
        And(usize, Vec<Formula>),
        /// The disjunction of the results of the next `n` steps.
        Or(usize),
    }
    let mut steps = vec![Step::Split(items)];
    let mut out: Vec<Formula> = Vec::new();
    while let Some(step) = steps.pop() {
        let items = match step {
            Step::And(n, mut own) => {
                own.extend(out.split_off(out.len() - n));
                out.push(Formula::and(own));
                continue;
            }
            Step::Or(n) => {
                let ds = out.split_off(out.len() - n);
                out.push(Formula::or(ds));
                continue;
            }
            Step::Split(items) => items,
        };
        let Some((own, groups)) = split(items, keep) else {
            out.push(Formula::bottom());
            continue;
        };
        steps.push(Step::And(groups.len(), own));
        for group in groups {
            match group {
                Group::Or(rows, ds) => {
                    steps.push(Step::Or(ds.len()));
                    for d in ds {
                        let mut items = rows.clone();
                        items.push(d);
                        steps.push(Step::Split(items));
                    }
                }
                Group::Again(items) => steps.push(Step::Split(items)),
            }
        }
    }
    out.pop().expect("the projection")
}

/// A group of a conjunction left to project ([`split`]).
enum Group {
    /// Rows and the disjuncts of the one disjunction beside them.
    Or(Vec<Formula>, Vec<Formula>),
    /// Parts to split again, `keep` having gained the atoms their disjunctions share.
    Again(Vec<Formula>),
}

/// One step of [`project`] on the conjunction of `items`: the parts that need no more, its rows
/// over `keep` and those of groups of rows alone, projected by [`shadow`], and its disjunctions
/// that read only `keep`; and the groups left. Each atom outside `keep` that a disjunction reads
/// and a two-term equality among the rows sets with coefficient 1 or -1 (`x@3 == x@4 + 3`, the
/// binding of a call's argument) is first replaced in the disjunctions by what it equals, which
/// the rows make the same, so that a callee's clauses read the caller's atom and not the bound
/// one. `None` where the rows hold nowhere. Time of the items, near linear, and of [`shadow`].
fn split(items: Vec<Formula>, keep: &mut HashSet<Atom>) -> Option<(Vec<Formula>, Vec<Group>)> {
    let (mut rows, mut ors): (Vec<Con>, Vec<Formula>) = (Vec::new(), Vec::new());
    let mut flat = items;
    while let Some(f) = flat.pop() {
        match f {
            Formula::Con(ref c) => rows.push(c.clone()),
            Formula::And(_) => flat.extend(f.into_parts().expect("a conjunction")),
            Formula::Or(ref gs) if gs.is_empty() => return None,
            Formula::Or(_) => ors.push(f),
            Formula::Not(_) => flat.push(nnf(&f, true)),
        }
    }
    let read: HashSet<Atom> = (ors.iter())
        .flat_map(Formula::atoms)
        .filter(|a| !keep.contains(a))
        .collect();
    let mut to: HashMap<Atom, Lin> = HashMap::new();
    for c in &rows {
        if c.rel != Rel::Eq || c.lin.terms.len() != 2 {
            continue;
        }
        let set = (c.lin.terms.iter())
            .find(|(a, k)| k.abs() == Int::ONE && read.contains(*a) && !to.contains_key(*a));
        if let Some((a, k)) = set {
            // k·a + rest == 0, so a == -k·rest.
            let mut rest = c.lin.clone();
            rest.terms.remove(a);
            to.insert(a.clone(), rest.times(-k));
        }
    }
    drop(read);
    if !to.is_empty() {
        let put = |c: &Con| {
            Formula::Con(Con {
                lin: substituted(&c.lin, &to),
                rel: c.rel,
            })
        };
        ors = ors.iter().map(|f| f.map_cons(&put)).collect();
    }
    // The atoms outside `keep` of each row and then of each disjunction, and their groups.
    let reads: Vec<Vec<Atom>> = (rows.iter())
        .map(|c| {
            c.lin
                .terms
                .keys()
                .filter(|a| !keep.contains(*a))
                .cloned()
                .collect()
        })
        .chain(ors.iter().map(|f| {
            f.atoms()
                .into_iter()
                .filter(|a| !keep.contains(a))
                .collect()
        }))
        .collect();
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    for a in reads.iter().flatten() {
        let n = index.len();
        index.entry(a).or_insert(n);
    }
    let mut up: Vec<usize> = (0..index.len()).collect();
    for atoms in &reads {
        let mut atoms = atoms.iter().map(|a| index[a]);
        let Some(first) = atoms.next() else { continue };
        for a in atoms {
            let (r, s) = (root(&mut up, first), root(&mut up, a));
            up[s] = r;
        }
    }
    // Each group's rows and disjunctions, by the index of each item, in the order met.
    let mut at: HashMap<usize, usize> = HashMap::new();
    let mut groups: Vec<(Vec<usize>, Vec<usize>)> = Vec::new();
    let mut plain: Vec<Con> = Vec::new();
    let mut own: Vec<Formula> = Vec::new();
    for (i, atoms) in reads.iter().enumerate() {
        let Some(a) = atoms.first() else {
            match i < rows.len() {
                true => plain.push(rows[i].clone()),
                false => own.push(ors[i - rows.len()].clone()),
            }
            continue;
        };
        let r = root(&mut up, index[a]);
        let g = *at.entry(r).or_insert_with(|| {
            groups.push((Vec::new(), Vec::new()));
            groups.len() - 1
        });
        match i < rows.len() {
            true => groups[g].0.push(i),
            false => groups[g].1.push(i),
        }
    }
    drop(index);
    let mut left: Vec<Group> = Vec::new();
    for (rs, os) in groups {
        let rows_of = |rs: &[usize]| -> Vec<Formula> {
            rs.iter().map(|&i| Formula::Con(rows[i].clone())).collect()
        };
        match os.len() {
            0 => plain.extend(rs.iter().map(|&i| rows[i].clone())),
            1 => left.push(Group::Or(
                rows_of(&rs),
                ors[os[0] - rows.len()].kids().to_vec(),
            )),
            _ => {
                // The atoms its disjunctions read that another of its parts reads.
                let mut by: HashMap<&Atom, (usize, bool)> = HashMap::new();
                for &i in rs.iter().chain(&os) {
                    for a in &reads[i] {
                        let e = by.entry(a).or_insert((0, false));
                        e.0 += 1;
                        e.1 |= i >= rows.len();
                    }
                }
                keep.extend(
                    (by.into_iter())
                        .filter(|&(_, (n, or))| n >= 2 && or)
                        .map(|(a, _)| a.clone()),
                );
                let mut items = rows_of(&rs);
                items.extend(os.iter().map(|&i| ors[i - rows.len()].clone()));
                left.push(Group::Again(items));
            }
        }
    }
    let plain = shadow(&plain, &|a| keep.contains(a), true)?;
    own.extend(paired(plain).into_iter().map(Formula::Con));
    Some((own, left))
}

/// `rows` with each pair `t >= 0` and `-t >= 0` written as the one equality `t == 0`, so that
/// a congruence projected from a disjunct, as `x - 3 * q >= 0 && 3 * q - x >= 0`, is read as
/// one ([`Congruence::of`]). Time of the rows.
fn paired(rows: Vec<Con>) -> Vec<Con> {
    let ge: HashSet<&Lin> = (rows.iter())
        .filter(|c| c.rel == Rel::Ge)
        .map(|c| &c.lin)
        .collect();
    let mut out: Vec<Con> = Vec::new();
    let mut said: HashSet<Lin> = HashSet::new();
    for c in &rows {
        if c.rel == Rel::Ge {
            let neg = c.lin.times(-1);
            if ge.contains(&neg) {
                let lin = neg.min(c.lin.clone());
                if said.insert(lin.clone()) {
                    out.push(Con { lin, rel: Rel::Eq });
                }
                continue;
            }
        }
        out.push(c.clone());
    }
    out
}

/// `l` with each atom `to` holds replaced by what it gives. Time of `l` and of what replaces
/// its atoms.
fn substituted(l: &Lin, to: &HashMap<Atom, Lin>) -> Lin {
    let mut terms: BTreeMap<Atom, Int> = BTreeMap::new();
    let mut constant = l.constant.clone();
    let mut add = |a: &Atom, k: Int| {
        let v = terms.remove(a).map_or_else(|| k.clone(), |o| &o + &k);
        if !v.is_zero() {
            terms.insert(a.clone(), v);
        }
    };
    for (a, k) in &l.terms {
        match to.get(a) {
            Some(v) => {
                for (b, e) in &v.terms {
                    add(b, e * k);
                }
                constant = &constant + &(&v.constant * k);
            }
            None => add(a, k.clone()),
        }
    }
    Lin { terms, constant }
}

/// Whether the closure of a kept part holds the auxiliary variable `n`, so that its definition
/// is among the part's atoms already.
fn parts_hold(parts: &[&Atoms], n: u32) -> bool {
    parts.iter().any(|s| s.contains(&Atom::Aux(n)))
}

/// The constraints of a definition, a conjunction of constraints: `None` for one that holds
/// a disjunction or a negation.
fn constraints(d: &Formula) -> Option<Vec<&Con>> {
    match d {
        Formula::Con(c) => Some(vec![c]),
        Formula::And(gs) => (gs.iter())
            .map(|h| match h {
                Formula::Con(c) => Some(c),
                _ => None,
            })
            .collect(),
        Formula::Not(_) | Formula::Or(_) => None,
    }
}

/// Whether `a` is an atom of the part `k` that its face projects out.
fn hidden(k: &Known, face: &Face, a: &Atom) -> bool {
    k.closure.contains(a) && !face.atoms.contains(a)
}

/// Whether no atom of `atoms` is one the face of the part `k` projects out: the smaller side
/// read, each atom looked up in the other.
fn apart(atoms: &Atoms, k: &Known, face: &Face) -> bool {
    match atoms.len() <= k.closure.len() {
        true => !atoms.iter().any(|a| hidden(k, face, a)),
        false => !(k.closure.iter())
            .filter(|a| !face.atoms.contains(*a))
            .any(|a| atoms.contains(a)),
    }
}

/// Whether the point `m` of a part whose atoms are `closure` gives a value to every atom of the
/// part that `f` reads, with the factors of its products: a point found with a part read
/// through its face gives none to the atoms the face projects out, and a question that reads
/// one would be met at a value the part may not hold at. Time of `f`, O(log n) an atom.
fn given(closure: &Atoms, m: &Point, f: &Formula) -> bool {
    f.atoms().iter().all(|a| {
        let factors = auxes(a).map(Atom::Aux).chain(match a {
            Atom::Product(f, g) => vec![f.atom(), g.atom()],
            Atom::Sym(_) | Atom::Aux(_) => Vec::new(),
        });
        std::iter::once(a.clone())
            .chain(factors)
            .all(|b| !closure.contains(&b) || m.contains_key(&b))
    })
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
    reached_by(f, def, &|a| m.contains_key(a))
}

/// The definitions `f` reaches through the auxiliary variables not `past`: those of its
/// auxiliary variables not `past`, and of theirs. Time of `f` and of the definitions read, each
/// read once, and of `past` for each variable.
fn reached_by(
    f: &Formula,
    def: &dyn Fn(u32) -> Formula,
    past: &dyn Fn(&Atom) -> bool,
) -> Vec<Formula> {
    let mut seen: HashSet<u32> = HashSet::new();
    let mut todo: Vec<u32> = f.atoms().iter().flat_map(auxes).collect();
    let mut out = Vec::new();
    while let Some(n) = todo.pop() {
        if !seen.insert(n) || past(&Atom::Aux(n)) {
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
/// `f` it does not hold given 0, when `f` holds at it, or else when it holds with the atoms the
/// equalities of `f` set given those values ([`solved`]: the quotients of a face's clauses,
/// LOAD-disj-residue); otherwise `m` with the values of a point the solver gives `f` with the
/// atoms of `m` fixed to their values. `Ok(None)` when `f` holds nowhere with them so fixed,
/// and the refusal when the solver refuses that question. Time of `f`, and O(log n) for each
/// atom added to `m`.
fn met(m: &Point, f: &Formula) -> Result<Option<Point>, Refusal> {
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
    if f.holds(&at) || (solved(&mut at, f) && f.holds(&at)) {
        for a in atoms {
            let v = at.get(&a).cloned().unwrap_or_default();
            out.entry(a).or_insert(v);
        }
        return Ok(Some(out));
    }
    let mut fixed = vec![f.clone()];
    for a in atoms.iter().filter(|&a| m.contains_key(a)) {
        let v = Lin::constant(m[a].clone());
        fixed.push(Formula::Con(Con::eq(&Lin::atom(a.clone()), &v)));
    }
    let Some(found) = satisfiable(&Formula::and(fixed))? else {
        return Ok(None);
    };
    for a in atoms {
        if !m.contains_key(&a) {
            let v = found.get(&a).cloned().unwrap_or_default();
            out.insert(a, v);
        }
    }
    Ok(Some(out))
}

/// Gives each atom of `f` absent from `at` that an equality of `f` sets, the equality's other
/// atoms having values in `at` and its term at them divisible by the atom's coefficient, that
/// value, the first such equality in the order of `f`'s constraints setting it; whether any was
/// given. A quotient of a face's clause is so set once its caller's atoms are, and [`met`]
/// checks the values against `f` before it uses them. Time of `f`.
fn solved(at: &mut Model, f: &Formula) -> bool {
    let mut any = false;
    for c in f.cons() {
        if c.rel != Rel::Eq {
            continue;
        }
        // The one atom without a value, with its coefficient, and the term at the others.
        let mut unknown: Option<(&Atom, &Int)> = None;
        let mut rest = c.lin.constant.clone();
        let mut two = false;
        for (a, k) in &c.lin.terms {
            match (at.get(a), unknown) {
                (Some(v), _) => rest = &rest + &(k * v),
                (None, None) => unknown = Some((a, k)),
                (None, Some(_)) => two = true,
            }
        }
        let (false, Some((a, k))) = (two, unknown) else {
            continue;
        };
        // A product is read from its factors' values.
        if matches!(a, Atom::Product(..)) || !rest.mod_floor(k).is_zero() {
            continue;
        }
        // k·a + rest == 0.
        let v = (-&rest).div_floor(k);
        at.insert(a.clone(), v);
        any = true;
    }
    any
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
        closure: Atoms::new(),
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
