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

mod holes;
use holes::{Holes, hole_of};

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
    /// The holes of its clauses over one atom, by the atom (LOAD-bound-holes): kept apart from
    /// `clauses`, which hold none of them.
    holes: BTreeMap<Atom, Holes>,
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
    // calls, and a chain with no point at all, such as `q = (x < 10 || x > 20) && x mod 4 !=
    // 1` moved by 3 (from the fourth link `x + 3k` takes every residue mod 4): each link is
    // decided whole and refused (`Shadows`), 6.3 s at 12 links and 24.6 s at 16 on
    // LOAD-bound-holes, as slow on main. Test `l01_38_presburger::extend::a_chain_whose_points_move_is_decided_whole`, which
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
    /// answers are those [`Extending::defined`] gives, since each face is exact, but that a
    /// point the faces give (`Faces::free`) answers where the conjunction decided whole is
    /// refused (LOAD-bound-holes); every formula asked of one `Extending` is read with the same
    /// `iface`.
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
        // The clauses over one atom that say it lies outside a hole (`x < 10 || x > 20`, moved
        // by each call) are kept as an ordered map of disjoint intervals, read through each
        // call's binding and merged in O(log n) ([`Holes`], LOAD-bound-holes); the clauses
        // `d || x <= b` that share `d` keep the tightest `b` ([`rays_once`]); and the
        // divisions of one term by one modulus read one remainder ([`same_divisions`]), so a
        // chain whose two disjunctions share `x mod 6` keeps two clauses a link and not two
        // for each link below it.
        // Complexity tradeoff: a kept part with no face is read whole, as before: one that
        // holds a product, a let-bound name (no call binds it, so its caller's atoms are not
        // known), one that does not hold, and one beside which an atom it projects out is
        // read; and a face holds one clause for each link whose clause differs from every
        // other's and is neither a hole nor a bound beside a condition another shares, so a
        // link reads O(its depth) clauses and the chain O(n²): a residue whose modulus exceeds
        // the chain's length, and a clause over two moved atoms. Why: the clauses are merged
        // where they say the same, where they are holes, and where they bound one atom beside
        // one condition, not where one implies another in general; deciding that a clause of
        // congruences is implied by others is co-NP-hard (simultaneous incongruences, Garey
        // and Johnson problem AN2). Trigger: `q = (x mod 1009 == 0 || x mod 3 == 1) && ...`
        // in the chain above. Test
        // `l01_38_presburger::one_scope::each_answer_of_a_random_disjunctive_chain_is_the_answer_of_the_relation_whole`.
        // COMPLEXITY.md row LOAD-disj-residue.
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
        // No kept part's point extends: a point of the parts read through their faces, nothing
        // fixed ([`Faces::free`]), before the whole is decided.
        if holds.is_none() {
            self.faces.make(&self.known, kids.iter(), def, iface);
            holds = (self.faces.free(&self.known, kids, def)).map(|p| (Ok(true), Some(p)));
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
        // Each part's holes over an atom its caller reads are kept; those over an atom `a` that a
        // two-term equality sets to `c * b + d`, `b` an atom the caller reads (`x@3 == x@4 + 3`,
        // the binding of a call's argument), are read over `b`, in O(1); the others are written
        // out as clauses (LOAD-bound-holes).
        let bound = bindings(&rows, &keep);
        let mut holes: BTreeMap<Atom, Holes> = BTreeMap::new();
        for (_, face) in &parts {
            rows.extend(face.rows.iter().cloned());
            ors.extend(face.clauses.iter().cloned());
            for (a, h) in &face.holes {
                match (keep.contains(a), bound.get(a)) {
                    (true, _) => put(&mut holes, a.clone(), h.clone()),
                    (false, Some((c, b, d))) => put(&mut holes, b.clone(), h.through(c, d)),
                    (false, None) => ors.extend(h.clauses(a)),
                }
            }
        }
        if ors.is_empty() {
            let rows = shadow(&rows, &|a| keep.contains(a), true)?;
            return Some(Face::of(rows, Vec::new(), &keep, holes));
        }
        let (rows, clauses) = projected(rows, ors, &mut keep)?;
        Some(Face::of(rows, clauses, &keep, holes))
    }

    /// A point of the conjunction `g` (whose parts are `kids`) that extends the point `m` of its
    /// kept part `kids[j]`, found with each other kept part that has a face read through it,
    /// with the definitions the question reaches past `m` and those faces' parts ([`read`]):
    /// `None` when no other part has a face or an atom a face projects out is read beside it,
    /// and otherwise what [`met_outside`] gives, `Ok(None)` too when the question reads an atom
    /// of the part `m` gives no value ([`given`]). Time of [`read`] and [`met_outside`].
    ///
    /// [`read`]: Faces::read
    fn met(
        &self,
        known: &HashMap<Id, Known>,
        kids: &[Formula],
        j: usize,
        m: &Point,
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<Result<Option<Point>, Refusal>> {
        let kj = &known[&Id::any(&kids[j])];
        let (f, holes) = self.read(known, kids, Some(j), m, def)?;
        let read = |a: &Atom| !kj.closure.contains(a) || m.contains_key(a);
        if !given(&kj.closure, m, &f) || !holes.iter().all(|(a, _)| read(a)) {
            return Some(Ok(None));
        }
        Some(met_outside(m, &f, &holes))
    }

    /// A point of the conjunction `g` (whose parts are `kids`) found with each kept part that
    /// has a face read through it and nothing fixed, the holes of the faces written out
    /// (LOAD-bound-holes): for a link no kept part's point extends to, as a chain whose call
    /// moves a hole over the point of each part (`p{i}(x) = q(x: x) && p{i-1}(x: x + 3)`, `q`
    /// holding outside `10..=20`), which was otherwise decided whole, the chain read again at
    /// each link. Exact: each face stands for its part where nothing beside it reads an atom
    /// it projects out, as in [`Faces::met`], and the point gives no value to those atoms.
    /// `None` where no part has a face, an atom a face projects out is read beside it, or the
    /// solver finds no point or refuses, so that the conjunction is then decided whole, as
    /// before. A point found here is a point of the conjunction, so it answers where the
    /// solver refuses the conjunction whole (`Err(Shadows)` on chains whose congruences meet
    /// moved holes); those answers are checked point by point in the random tests. Time of
    /// [`Faces::read`], and of the solver on the faces and the holes.
    fn free(
        &self,
        known: &HashMap<Id, Known>,
        kids: &[Formula],
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<Point> {
        let (f, holes) = self.read(known, kids, None, &Point::new(), def)?;
        let mut written = vec![f];
        for (a, h) in &holes {
            written.extend(h.clauses(a));
        }
        point(&Formula::and(written))
    }

    /// The question of the conjunction whose parts are `kids`, each kept part but `kids[j]`
    /// that has a face read through it, with the definitions it reaches past `m` and those
    /// faces' parts, and the holes of those faces: `None` when no part has a face, or an atom a
    /// face projects out is read beside it. Time of the faces, the other parts and the
    /// definitions reached, and, for each part read through its face, of the smaller of its
    /// atoms and each other part's.
    fn read<'s>(
        &'s self,
        known: &HashMap<Id, Known>,
        kids: &[Formula],
        j: Option<usize>,
        m: &Point,
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<(Formula, Vec<(&'s Atom, &'s Holes)>)> {
        let mut faced: Vec<(&Known, &Face)> = Vec::new();
        let mut whole: Vec<&Known> = j.map(|j| &known[&Id::any(&kids[j])]).into_iter().collect();
        let mut rows: Vec<Formula> = Vec::new();
        let mut beside: HashSet<Atom> = HashSet::new();
        for (i, h) in kids.iter().enumerate() {
            if Some(i) == j {
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
        let holes = (faced.iter())
            .flat_map(|(_, face)| face.holes.iter())
            .collect();
        Some((with(&defs, base), holes))
    }
}

impl Face {
    /// The face of `rows` and `clauses`, a projection onto `keep` of a conjunction that holds:
    /// each row once, each congruence once ([`congruences_once`]), each clause once
    /// ([`clauses_once`]), and the rows and clauses of each group linked by shared atoms that
    /// reads none of `keep` dropped, since the conjunction holds and so each such group holds
    /// somewhere apart. Time of the rows and clauses, near linear.
    fn of(
        rows: Vec<Con>,
        clauses: Vec<Formula>,
        keep: &HashSet<Atom>,
        holes: BTreeMap<Atom, Holes>,
    ) -> Face {
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
        // The clauses over one atom of `keep` that say it lies outside a hole, added to its
        // holes (LOAD-bound-holes), and those that always hold dropped.
        let mut holes = holes;
        let clauses: Vec<Formula> = (clauses.into_iter())
            .filter(|f| match hole_of(f) {
                Some((a, hole)) if keep.contains(&a) => {
                    if let Some((lo, hi)) = hole {
                        holes.entry(a).or_insert_with(Holes::new).cut(&lo, &hi);
                    }
                    false
                }
                _ => true,
            })
            .collect();
        let clauses = rays_once(clauses);
        let atoms = (rows.iter())
            .flat_map(|c| c.lin.terms.keys().cloned())
            .chain(clauses.iter().flat_map(Formula::atoms))
            .chain(holes.keys().cloned())
            .collect();
        Face {
            rows,
            clauses,
            holes,
            atoms,
        }
    }
}

/// `clauses` with the clauses `d || y >= b` that share `d` and the side of the bound on `y`
/// said once, by the tightest bound, where `d` does not read `y` (LOAD-bound-holes):
/// `(d || y >= b) && (d || y >= b')` is `d || y >= max(b, b')`. A clause `d || (r && !d)` is
/// read as `d || r` first, which it is. So a chain whose links move the bound of
/// `x mod 6 == 5 || x < 50`, read at one remainder ([`same_divisions`]), keeps two clauses and
/// not two a link. The merged clause stands where the first of its clauses stood. Time of the
/// clauses, near linear.
fn rays_once(clauses: Vec<Formula>) -> Vec<Formula> {
    // `d || r` from `d || (r && !d)`, and the bound `r` on its one atom as `(y, upper, b)`:
    // `y >= b`, or `y <= b` when `upper`.
    let bound = |d: &Formula, x: &Formula| -> Option<(Formula, Atom, bool, Int)> {
        let not_d = nnf(d, false);
        let r: Vec<&Formula> = (x.kids().iter()).filter(|h| **h != not_d).collect();
        let r = match (x, &r[..]) {
            (Formula::And(_), [r]) if x.kids().len() == 2 => *r,
            (Formula::Con(_), _) => x,
            _ => return None,
        };
        let Formula::Con(c) = r else { return None };
        let mut terms = c.lin.terms.iter();
        let (Rel::Ge, Some((y, k)), None) = (c.rel, terms.next(), terms.next()) else {
            return None;
        };
        if d.atoms().contains(y) {
            return None;
        }
        // k·y + c0 >= 0: y >= ceil(-c0 / k) for k > 0, y <= floor(c0 / -k) for k < 0.
        let c0 = &c.lin.constant;
        Some(match k.is_positive() {
            true => (d.clone(), y.clone(), false, -&(c0.div_floor(k))),
            false => (d.clone(), y.clone(), true, c0.div_floor(&-k)),
        })
    };
    let ray = |f: &Formula| -> Option<(Formula, Atom, bool, Int)> {
        let Formula::Or(gs) = f else { return None };
        let [p, q] = &gs[..] else { return None };
        [(p, q), (q, p)].into_iter().find_map(|(d, x)| bound(d, x))
    };
    let mut at: HashMap<(Formula, Atom, bool), usize> = HashMap::new();
    let mut out: Vec<(Formula, Option<Int>)> = Vec::new();
    for f in clauses {
        let Some((d, y, upper, b)) = ray(&f) else {
            out.push((f, None));
            continue;
        };
        match at.get(&(d.clone(), y.clone(), upper)) {
            Some(&i) => {
                let (_, Some(o)) = &mut out[i] else {
                    unreachable!("a ray's slot")
                };
                *o = match upper {
                    true => o.clone().min(b),
                    false => o.clone().max(b),
                };
            }
            None => {
                at.insert((d, y, upper), out.len());
                out.push((f, Some(b)));
            }
        }
    }
    let mut back: HashMap<usize, (Formula, Atom, bool)> =
        at.into_iter().map(|(k, i)| (i, k)).collect();
    (out.into_iter().enumerate())
        .map(|(i, (f, b))| {
            let Some(b) = b else { return f };
            let (d, y, upper) = back.remove(&i).expect("a ray's key");
            let one = |k: i64, c: Int| Lin {
                terms: std::iter::once((y.clone(), Int::from(k))).collect(),
                constant: c,
            };
            let r = match upper {
                // y <= b: -y + b >= 0.
                true => one(-1, b),
                // y >= b: y - b >= 0.
                false => one(1, -&b),
            };
            Formula::or(vec![
                d,
                Formula::Con(Con {
                    lin: r,
                    rel: Rel::Ge,
                }),
            ])
        })
        .collect()
}

/// The holes `h` over `a` added to those of `holes` over it ([`Holes::merged`]).
fn put(holes: &mut BTreeMap<Atom, Holes>, a: Atom, h: Holes) {
    let h = match holes.remove(&a) {
        Some(o) => o.merged(h),
        None => h,
    };
    holes.insert(a, h);
}

/// The atoms outside `keep` that a two-term equality among `rows`, their coefficient 1 or -1 in
/// it, sets to `c * b + d` with `b` in `keep`, by the atom: `(c, b, d)`, the first such row in the order of `rows` setting it.
/// Time of the rows.
fn bindings(rows: &[Con], keep: &HashSet<Atom>) -> HashMap<Atom, (Int, Atom, Int)> {
    let mut out: HashMap<Atom, (Int, Atom, Int)> = HashMap::new();
    for c in rows {
        let mut terms = c.lin.terms.iter();
        let (Rel::Eq, Some(x), Some(y), None) = (c.rel, terms.next(), terms.next(), terms.next())
        else {
            continue;
        };
        for ((a, k), (b, e)) in [(x, y), (y, x)] {
            if k.abs() != Int::ONE || !keep.contains(b) || keep.contains(a) {
                continue;
            }
            // k·a + e·b + c0 == 0, so a == -k·e·b - k·c0.
            let to = (-&(k * e), b.clone(), -&(k * &c.lin.constant));
            out.entry(a.clone()).or_insert(to);
        }
    }
    out
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
    let (classes, also) = unit_classes(&rows, &read, keep);
    drop(read);
    let sub = |rows: Vec<Con>, to: &HashMap<Atom, Lin>| -> Vec<Con> {
        (rows.into_iter())
            .map(|c| Con {
                lin: substituted(&c.lin, to),
                rel: c.rel,
            })
            .collect()
    };
    if !classes.is_empty() {
        rows = sub(rows, &classes);
    }
    let divisions = same_divisions(&rows, keep);
    if !divisions.is_empty() {
        rows = sub(rows, &divisions);
    }
    // A row the substitutions leave with no atom holds, or no row holds.
    let mut empty = false;
    rows.retain(|c| match c.lin.terms.is_empty() {
        false => true,
        true => {
            let k = &c.lin.constant;
            empty |= !(k.is_zero() || (c.rel == Rel::Ge && k.is_positive()));
            false
        }
    });
    if empty {
        return None;
    }
    for to in [&classes, &also, &divisions] {
        if !to.is_empty() {
            let put = |c: &Con| {
                Formula::Con(Con {
                    lin: substituted(&c.lin, to),
                    rel: c.rel,
                })
            };
            ors = ors.iter().map(|f| f.map_cons(&put)).collect();
        }
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

/// What each atom of `read` equals by the two-term equalities among `rows`, for [`split`]: the
/// atoms that equalities `a == b + c` and `a == -b + c` link form classes, each written as
/// `s * r + d` (`s` 1 or -1) of one atom `r` of its class, an atom of `keep` where the class
/// holds one, else the least; an atom of `read` that is the `r` of its class, or in none, and
/// that an equality `k * a + e * b + c == 0` with `k` 1 or -1 sets, equals `-k * (e * b + c)`,
/// `b` written as its class's, by the first such row. So the clauses of a chain whose links
/// bind `x@{i-1} == x@i + 12` read the caller's atom however deep the chain, and not that of
/// the link below (LOAD-bound-holes). Exact, since the rows stay. Time of the rows, near
/// linear: a union of the classes by their atoms, each path compressed on the way.
fn unit_classes(
    rows: &[Con],
    read: &HashSet<Atom>,
    keep: &HashSet<Atom>,
) -> (HashMap<Atom, Lin>, HashMap<Atom, Lin>) {
    // Each atom's index, and for each index the one it is set by: `(s, up, d)`, the atom
    // equal to `s` times that at `up` plus `d`.
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut atoms: Vec<&Atom> = Vec::new();
    let mut up: Vec<(Int, usize, Int)> = Vec::new();
    type Term<'c> = (&'c Atom, &'c Int);
    fn unit(c: &Con) -> Option<(Term<'_>, Term<'_>)> {
        let mut terms = c.lin.terms.iter();
        match (c.rel, terms.next(), terms.next(), terms.next()) {
            (Rel::Eq, Some(x), Some(y), None) => Some((x, y)),
            _ => None,
        }
    }
    for c in rows {
        let Some(((a, _), (b, _))) = unit(c) else {
            continue;
        };
        for x in [a, b] {
            if !index.contains_key(x) {
                index.insert(x, atoms.len());
                up.push((Int::ONE, atoms.len(), Int::ZERO));
                atoms.push(x);
            }
        }
    }
    // The root of `i`, as `(s, r, d)`: the atom at `i` equals `s` times that at `r` plus `d`.
    fn find(up: &mut [(Int, usize, Int)], i: usize) -> (Int, usize, Int) {
        let (mut s, mut r, mut d) = (Int::ONE, i, Int::ZERO);
        let mut path: Vec<usize> = Vec::new();
        while up[r].1 != r {
            path.push(r);
            let (t, n, e) = up[r].clone();
            // x == s·r + d and r == t·n + e, so x == s·t·n + s·e + d.
            d = &(&s * &e) + &d;
            s = &s * &t;
            r = n;
        }
        // Each atom on the path set by the root directly, its value as above.
        let (mut t, mut e) = (Int::ONE, Int::ZERO);
        for &p in path.iter().rev() {
            let (u, _, f) = up[p].clone();
            // p == u·next + f and next == t·root + e.
            e = &(&u * &e) + &f;
            t = &u * &t;
            up[p] = (t.clone(), r, e.clone());
        }
        (s, r, d)
    }
    let prefer = |x: &Atom, y: &Atom| (!keep.contains(x), x) < (!keep.contains(y), y);
    for c in rows {
        let Some(((a, k), (b, e))) = unit(c) else {
            continue;
        };
        if k.abs() != Int::ONE || e.abs() != Int::ONE {
            continue;
        }
        // k·a + e·b + c0 == 0, so a == -k·e·b - k·c0.
        let (m, c0) = (-&(k * e), -&(k * &c.lin.constant));
        let (sa, ra, da) = find(&mut up, index[a]);
        let (sb, rb, db) = find(&mut up, index[b]);
        if ra == rb {
            continue;
        }
        // sa·ra + da == m·(sb·rb + db) + c0.
        match prefer(atoms[ra], atoms[rb]) {
            // rb == m·sb·(sa·ra + da - m·db - c0).
            true => {
                let f = &m * &sb;
                let d = &f * &(&(&da - &(&m * &db)) - &c0);
                up[rb] = (&f * &sa, ra, d);
            }
            // ra == sa·(m·sb·rb + m·db + c0 - da).
            false => {
                let d = &sa * &(&(&(&m * &db) + &c0) - &da);
                up[ra] = (&(&sa * &m) * &sb, rb, d);
            }
        }
    }
    let lin = |s: Int, r: usize, d: Int| Lin {
        terms: std::iter::once((atoms[r].clone(), s)).collect(),
        constant: d,
    };
    let mut to: HashMap<Atom, Lin> = HashMap::new();
    for (i, &a) in atoms.iter().enumerate() {
        let (s, r, d) = find(&mut up, i);
        if r != i && !keep.contains(a) {
            to.insert(a.clone(), lin(s, r, d));
        }
    }
    let mut also: HashMap<Atom, Lin> = HashMap::new();
    for c in rows {
        let Some(((x, kx), (y, ky))) = unit(c) else {
            continue;
        };
        for ((a, k), (b, e)) in [((x, kx), (y, ky)), ((y, ky), (x, kx))] {
            if k.abs() != Int::ONE
                || !read.contains(a)
                || to.contains_key(a)
                || also.contains_key(a)
            {
                continue;
            }
            let (s, r, d) = find(&mut up, index[b]);
            if r == index[a] {
                continue;
            }
            // k·a + e·(s·r + d) + c0 == 0, so a == -k·e·s·r - k·(e·d + c0).
            let set = Lin {
                terms: std::iter::once((atoms[r].clone(), -&(&(k * e) * &s))).collect(),
                constant: -&(k * &(&(e * &d) + &c.lin.constant)),
            };
            also.insert(a.clone(), set);
        }
    }
    (to, also)
}

/// The quotients and remainders of the divisions among `rows` that another division of the same
/// term by the same modulus sets, for [`split`]: an equality `t + c == m * q + r` with
/// `0 <= r <= m - 1` among the rows, `q` and `r` outside `keep`, after one `t + c' == m * q' +
/// r'` with `c' == c` modulo `m` in the order of `rows`, sets `r` to `r'` and `q` to `q' + (c' -
/// c) / m`, since the remainders of one value are one. So the residue tests of a chain's links,
/// each `x@i mod 6` read through the bindings at its own shift, read one remainder however deep
/// the chain (LOAD-bound-holes). Exact, since the rows stay. Time of the rows.
fn same_divisions(rows: &[Con], keep: &HashSet<Atom>) -> HashMap<Atom, Lin> {
    let lin = |terms: Vec<(Atom, Int)>, constant: Int| Lin {
        terms: terms.into_iter().collect(),
        constant,
    };
    let ge: HashSet<&Lin> = (rows.iter())
        .filter(|c| c.rel == Rel::Ge)
        .map(|c| &c.lin)
        .collect();
    // The rows bounding `r` to `0..=m - 1`.
    let bounded = |r: &Atom, m: &Int| {
        ge.contains(&lin(vec![(r.clone(), Int::ONE)], Int::ZERO))
            && ge.contains(&lin(vec![(r.clone(), -&Int::ONE)], m - &Int::ONE))
    };
    // By the term, the modulus and the constant's residue: the first division's `q`, `r` and
    // constant.
    let mut first: HashMap<(Lin, Int, Int), (Atom, Atom, Int)> = HashMap::new();
    let mut to: HashMap<Atom, Lin> = HashMap::new();
    for c in rows {
        if c.rel != Rel::Eq {
            continue;
        }
        // `r` with coefficient -1 and `q` with -m, `m >= 2`, the row read as `t + c - m q - r`.
        let pair = |l: &Lin| {
            let r = (l.terms.iter()).find(|(a, k)| **k == -&Int::ONE && !keep.contains(*a))?;
            let q = (l.terms.iter()).find(|(a, k)| {
                *a != r.0 && !keep.contains(*a) && k.is_negative() && bounded(r.0, &-(*k))
            })?;
            Some((q.0.clone(), r.0.clone(), -q.1))
        };
        let negated = c.lin.times(-1);
        let Some((l, (q, r, m))) = [&c.lin, &negated]
            .into_iter()
            .find_map(|l| pair(l).map(|p| (l, p)))
        else {
            continue;
        };
        if to.contains_key(&q) || to.contains_key(&r) {
            continue;
        }
        let mut t = l.clone();
        t.terms.remove(&q);
        t.terms.remove(&r);
        let constant = std::mem::replace(&mut t.constant, Int::ZERO);
        let key = (t, constant.mod_floor(&m), m.clone());
        match first.get(&key) {
            None => {
                first.insert(key, (q, r, constant));
            }
            Some((q1, r1, c1)) if q1 != &q => {
                to.insert(r, lin(vec![(r1.clone(), Int::ONE)], Int::ZERO));
                let d = (&constant - c1).div_floor(&m);
                to.insert(q, lin(vec![(q1.clone(), Int::ONE)], d));
            }
            Some(_) => {}
        }
    }
    to
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
    let mut at = read_at(m, &atoms);
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

/// The values of `atoms` at `m`, with the factors of their products. O(log n) an atom.
fn read_at(m: &Point, atoms: &std::collections::BTreeSet<Atom>) -> Model {
    let mut at = Model::new();
    for a in atoms {
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
    at
}

/// [`met`] of `f` and the clauses of `holes`, each hole set over its atom (LOAD-bound-holes):
/// the point is checked against each set in O(log n), and the holes are written out as clauses
/// only where the solver is asked. Time of `f`, O(log n) for each set of holes, and, where the
/// solver is asked, of the holes.
fn met_outside(
    m: &Point,
    f: &Formula,
    holes: &[(&Atom, &Holes)],
) -> Result<Option<Point>, Refusal> {
    if holes.is_empty() {
        return met(m, f);
    }
    let mut atoms = f.atoms();
    atoms.extend(holes.iter().map(|(a, _)| (*a).clone()));
    let mut at = read_at(m, &atoms);
    let outside =
        |at: &Model| (holes.iter()).all(|(a, h)| !h.holds(at.get(*a).unwrap_or(&Int::ZERO)));
    if (f.holds(&at) && outside(&at)) || (solved(&mut at, f) && f.holds(&at) && outside(&at)) {
        let mut out = m.clone();
        for a in atoms {
            let v = at.get(&a).cloned().unwrap_or_default();
            out.entry(a).or_insert(v);
        }
        return Ok(Some(out));
    }
    let mut written = vec![f.clone()];
    for (a, h) in holes {
        written.extend(h.clauses(a));
    }
    met(m, &Formula::and(written))
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
    match decided(f) {
        Ok(true) => (Ok(true), point(f)),
        other => (other, None),
    }
}

/// A point where `f` holds, every atom of `f` given a value, when the solver gives one: of `f`,
/// or, where the solver refuses `f`, of `f` with its bindings in place ([`Bound`]).
fn point(f: &Formula) -> Option<Point> {
    let filled = |g: &Formula, m: Model| {
        let mut p: Point = m.into_iter().collect();
        for a in g.atoms() {
            p.entry(a).or_default();
        }
        p
    };
    match satisfiable(f) {
        Ok(m) => m.map(|m| filled(f, m)),
        Err(_) => {
            let mut b = Bound::of(f)?;
            let m = satisfiable(&b.f).ok().flatten()?;
            let mut p = filled(&b.f, m);
            b.back(&mut p);
            Some(p)
        }
    }
}

/// [`decide`] of a whole question (LOAD-extend-refuses): where the solver refuses `f`, `f` is
/// asked again with its bindings in place ([`Bound`]), and the first refusal is kept when that
/// is refused too, so a question refused both ways prints the refusal it printed before. A
/// question [`Extending`] decides whole reads its kept parts over the atoms their calls bind,
/// tied to the caller's by equalities (`x@3 == x@4 + 3`), while the relation written whole
/// reads the caller's atoms alone; the solver's search depends on that shape, and refused the
/// first where it decided the second (Shadows on the chain of
/// `l01_38_presburger::one_scope::a_link_decided_whole_is_answered_where_its_relation_is`).
// Complexity tradeoff: a question the solver refuses is asked twice, so it costs that refusal,
// the substitution (time of `f`, times a logarithm) and the second ask. Why: neither shape is
// refused less often, since the search depends on the rows it is given: over every whole
// question of l01_38 (measured once, both forms asked), the answers never differ, the form
// with bindings in place answers 42 that the form with them as rows refuses, and refuses 34
// that it answers (the tie of
// `checker::a_refused_question_through_a_call_prints_what_the_question_written_out_prints`:
// with its bindings as rows, eight variables that the structure tells apart; in place, four
// that tie). Asking the bound form alone would refuse those and print its own atoms in a tie,
// so the form asked first is the one asked before and the second runs only on a refusal. Trigger: a
// whole question refused with its bindings as rows. Tests
// `l01_38_presburger::one_scope::a_link_decided_whole_is_answered_where_its_relation_is` and
// `no_question_of_a_random_chain_with_negations_is_refused_where_its_relation_is_decided`.
// COMPLEXITY.md row LOAD-extend-refuses. A complete solution is a solver whose answer does not
// depend on how unit equalities are written, substituting them before its search.
fn decided(f: &Formula) -> Result<bool, Refusal> {
    decide(f).or_else(|e| match Bound::of(f) {
        Some(b) => decide(&b.f).map_err(|_| e),
        None => Err(e),
    })
}

/// `f` with its bindings in place, as a whole question refused with them as rows is asked again
/// (`Bound`), or `None` when it has none: for tests. Time of `f` times a logarithm.
pub fn with_bindings_in_place(f: &Formula) -> Option<Formula> {
    Bound::of(f).map(|b| b.f)
}

/// A formula with its bindings in place: each atom that a top-level equality of one or two
/// terms with coefficients 1 or -1 sets (`x@3 == x@4 + 3`, a call's argument bound to its
/// callee's atom, or `q12 == 12`, a binding variable) replaced, everywhere in the formula, by
/// what it equals, so that one atom of each binding is left, as in the relation written over
/// its inputs; and the quotient and remainder of a division read twice, through two calls,
/// replaced by those of its first reading ([`Bound::merge_divisions`]), as the relation written
/// whole reads it once. Exact: the formula with them in place holds where the formula does,
/// with the replaced atoms given back by [`Bound::back`]. An atom that is a factor of a product
/// is not replaced.
struct Bound {
    f: Formula,
    /// Each replaced atom `a`, with `(k, b, c)` for `a == k * b + c`, `k` 1 or -1: `b` the atom
    /// left, or another replaced atom ([`Bound::resolve`]); or `None`, with `k` 0, for `a == c`.
    up: HashMap<Atom, (Int, Option<Atom>, Int)>,
}

/// A top-level division row `l + s·(m·q + r) == 0`, `s` 1 or -1, with `0 <= r <= m - 1` at the
/// top level too: `q` and `r` are the quotient and remainder of `-s·l` by `m`.
struct Division<'a> {
    row: &'a Con,
    q: Atom,
    r: Atom,
    m: Int,
}

impl Bound {
    /// `f` with its bindings in place, `None` when it has none. Each top-level constraint is
    /// read once and each atom resolved through the replaced ones with the path compressed (a
    /// union of classes), so the time is that of `f` times a logarithm.
    fn of(f: &Formula) -> Option<Bound> {
        let mut factors: HashSet<Atom> = HashSet::new();
        for a in &f.atoms() {
            if let Atom::Product(x, y) = a {
                factors.insert(x.atom());
                factors.insert(y.atom());
            }
        }
        let free = |a: &Atom| !matches!(a, Atom::Product(..)) && !factors.contains(a);
        let mut b = Bound {
            f: Formula::top(),
            up: HashMap::new(),
        };
        // The top-level constraints, through the kept conjunctions, each part once.
        let mut rows: Vec<&Con> = Vec::new();
        let mut seen: HashSet<Id> = HashSet::new();
        let mut todo: Vec<&Formula> = vec![f];
        while let Some(g) = todo.pop() {
            match g {
                Formula::And(gs) if seen.insert(Id::any(g)) => todo.extend(gs.iter().rev()),
                Formula::Con(c) => rows.push(c),
                _ => {}
            }
        }
        for c in &rows {
            if c.rel == Rel::Eq
                && c.lin.terms.len() <= 2
                && c.lin.terms.iter().all(|(a, k)| k.is_unit() && free(a))
            {
                b.bind(&c.lin);
            }
        }
        b.merge_divisions(&rows, &free);
        if b.up.is_empty() {
            return None;
        }
        // Each replaced atom pointed at the atom left, so that each is read with one lookup.
        let replaced: Vec<Atom> = b.up.keys().cloned().collect();
        for a in &replaced {
            b.resolve(a);
        }
        let up = &b.up;
        let put = |c: &Con| {
            let lin = Bound::through(up, &c.lin, &[]);
            match lin.terms.is_empty() {
                true => match (c.rel, lin.constant.is_zero(), lin.constant.is_negative()) {
                    (Rel::Eq, true, _) | (Rel::Ge, _, false) => Formula::top(),
                    _ => Formula::bottom(),
                },
                false => Formula::Con(Con { lin, rel: c.rel }),
            }
        };
        b.f = f.map_cons(&put);
        Some(b)
    }

    /// Reads the equality `lin == 0`, of at most two atoms each with coefficient 1 or -1, over
    /// the atoms left: one atom left with coefficient 1 or -1 is set to a constant, and of two
    /// left, each with coefficient 1 or -1, the larger is set by the other. O(log n) amortized.
    fn bind(&mut self, lin: &Lin) {
        let mut left: Vec<(Atom, Int)> = Vec::new();
        let mut rest = lin.constant.clone();
        for (a, k) in &lin.terms {
            let (j, r, d) = self.resolve(a);
            rest = &rest + &(k * &d);
            let Some(r) = r else { continue };
            match left.iter_mut().find(|(s, _)| *s == r) {
                Some((_, e)) => *e = &*e + &(k * &j),
                None => left.push((r, k * &j)),
            }
        }
        left.retain(|(_, e)| !e.is_zero());
        left.sort_by(|x, y| y.0.cmp(&x.0));
        // e·r + o·s + rest == 0, r the larger atom: r == -(o·s + rest) / e, e being 1 or -1.
        match left.as_slice() {
            [(r, e)] if e.is_unit() => {
                self.up.insert(r.clone(), (Int::ZERO, None, -&(&rest * e)));
            }
            [(r, e), (s, o)] if e.is_unit() && o.is_unit() => {
                self.up
                    .insert(r.clone(), (-&(o * e), Some(s.clone()), -&(&rest * e)));
            }
            _ => {}
        }
    }

    /// Merges the divisions of `rows` that divide the same term by the same number: rows
    /// `l == m·q + r` and `l == m·q' + r'`, with `0 <= r <= m - 1` and `0 <= r' <= m - 1` among
    /// `rows` too, give `q == q'` and `r == r'`, since the quotient and remainder of a division
    /// are unique. A call reads its callee's definitions over the callee's atoms, so a
    /// definition reached through two calls is two divisions, which the bindings put in place
    /// ([`Bound::bind`]) make divisions of one term. The divisions are taken with those their
    /// terms use first (a visited set), so a term is read over the merged atoms of the
    /// divisions inside it; time of `rows` times a logarithm.
    fn merge_divisions(&mut self, rows: &[&Con], free: &dyn Fn(&Atom) -> bool) {
        // The atoms bounded below by 0 or more, and the least upper bound of each.
        let mut from0: HashSet<&Atom> = HashSet::new();
        let mut upper: HashMap<&Atom, &Int> = HashMap::new();
        for c in rows {
            if c.rel != Rel::Ge || c.lin.terms.len() != 1 {
                continue;
            }
            let Some((a, k)) = c.lin.terms.iter().next() else {
                continue;
            };
            // a + c >= 0 is a >= -c; -a + c >= 0 is a <= c.
            if *k == Int::ONE && !c.lin.constant.is_positive() {
                from0.insert(a);
            } else if *k == -&Int::ONE {
                let u = upper.entry(a).or_insert(&c.lin.constant);
                if c.lin.constant < **u {
                    *u = &c.lin.constant;
                }
            }
        }
        let kept = |a: &Atom, up: &HashMap<Atom, _>| free(a) && !up.contains_key(a);
        let mut divs: Vec<Division> = Vec::new();
        for c in rows {
            if c.rel != Rel::Eq || c.lin.terms.len() < 3 {
                continue;
            }
            let found = c.lin.terms.iter().find_map(|(r, kr)| {
                if !(kr.is_unit() && from0.contains(r) && kept(r, &self.up)) {
                    return None;
                }
                let u = upper.get(r)?;
                c.lin.terms.iter().find_map(|(q, kq)| {
                    let m = kq.abs();
                    (q != r && kq.is_positive() == kr.is_positive() && **u < m && kept(q, &self.up))
                        .then(|| (q.clone(), r.clone(), m))
                })
            });
            if let Some((q, r, m)) = found {
                divs.push(Division { row: c, q, r, m });
            }
        }
        // Each division after those whose quotient or remainder its term uses.
        let mut owner: HashMap<&Atom, usize> = HashMap::new();
        for (i, d) in divs.iter().enumerate() {
            owner.insert(&d.q, i);
            owner.insert(&d.r, i);
        }
        let mut order: Vec<usize> = Vec::with_capacity(divs.len());
        let mut visited = vec![false; divs.len()];
        for start in 0..divs.len() {
            if visited[start] {
                continue;
            }
            visited[start] = true;
            let mut stack: Vec<(usize, std::collections::btree_map::Iter<Atom, Int>)> =
                vec![(start, divs[start].row.lin.terms.iter())];
            while let Some((i, it)) = stack.last_mut() {
                let i = *i;
                match it.next() {
                    Some((a, _)) => {
                        if let Some(&j) = owner.get(a)
                            && !visited[j]
                        {
                            visited[j] = true;
                            stack.push((j, divs[j].row.lin.terms.iter()));
                        }
                    }
                    None => {
                        order.push(i);
                        stack.pop();
                    }
                }
            }
        }
        let mut first: HashMap<(Lin, Int), usize> = HashMap::new();
        for i in order {
            let d = &divs[i];
            for a in d.row.lin.terms.keys() {
                self.resolve(a);
            }
            let mut l = Bound::through(&self.up, &d.row.lin, &[&d.q, &d.r]);
            // l + s·(m·q + r) == 0: the term divided is -s·l.
            if d.row.lin.terms[&d.r].is_positive() {
                l = l.times(-1);
            }
            match first.entry((l, d.m.clone())) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(i);
                }
                std::collections::hash_map::Entry::Occupied(o) => {
                    let e = &divs[*o.get()];
                    for (x, y) in [(&d.q, &e.q), (&d.r, &e.r)] {
                        let tie = Lin {
                            terms: BTreeMap::from([(x.clone(), Int::ONE), (y.clone(), -&Int::ONE)]),
                            constant: Int::ZERO,
                        };
                        self.bind(&tie);
                    }
                }
            }
        }
    }

    /// `lin` over the atoms left, each atom but `skip` read through `up` with one lookup (each
    /// replaced atom pointing at the atom left, [`Bound::resolve`]).
    fn through(up: &HashMap<Atom, (Int, Option<Atom>, Int)>, lin: &Lin, skip: &[&Atom]) -> Lin {
        let mut terms: BTreeMap<Atom, Int> = BTreeMap::new();
        let mut constant = lin.constant.clone();
        for (a, k) in &lin.terms {
            if skip.contains(&a) {
                continue;
            }
            let (j, r, d) = match up.get(a) {
                Some((j, r, d)) => (j.clone(), r.clone(), d.clone()),
                None => (Int::ONE, Some(a.clone()), Int::ZERO),
            };
            constant = &constant + &(k * &d);
            let Some(r) = r else { continue };
            let v = terms.remove(&r).map_or_else(|| k * &j, |v| &v + &(k * &j));
            if !v.is_zero() {
                terms.insert(r, v);
            }
        }
        Lin { terms, constant }
    }

    /// `(k, r, d)` with `a == k * r + d` and `r` an atom not replaced, or `(0, None, d)` for
    /// `a == d`: the path from `a` followed to its end, and each atom on it then pointed at
    /// that end directly. O(log n) amortized.
    fn resolve(&mut self, a: &Atom) -> (Int, Option<Atom>, Int) {
        let up = &mut self.up;
        let mut path: Vec<(Atom, Int, Int)> = Vec::new();
        let mut at = Some(a.clone());
        while let Some(x) = at.take() {
            match up.get(&x) {
                Some((k, b, d)) => {
                    path.push((x, k.clone(), d.clone()));
                    at = b.clone();
                }
                None => {
                    at = Some(x);
                    break;
                }
            }
        }
        // From the end back to `a`: x == k·y + d and y == j·r + e give x == kj·r + kd + d.
        let (mut j, mut e) = (Int::ONE, Int::ZERO);
        for (x, k, d) in path.into_iter().rev() {
            e = &(&k * &e) + &d;
            j = &k * &j;
            up.insert(x, (j.clone(), at.clone(), e.clone()));
        }
        (j, at, e)
    }

    /// Gives each replaced atom its value at `p`, a point of the formula with the bindings in
    /// place: a point of the formula itself.
    fn back(&mut self, p: &mut Point) {
        let replaced: Vec<Atom> = self.up.keys().cloned().collect();
        for a in replaced {
            let (k, r, d) = self.resolve(&a);
            let v = r.and_then(|r| p.get(&r).cloned()).unwrap_or_default();
            p.insert(a, &(&k * &v) + &d);
        }
    }
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
    decided(&with(&reached(&f, def), f))
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

#[cfg(test)]
mod tests {
    use super::*;

    fn a(n: u32) -> Atom {
        Atom::Aux(n)
    }

    /// `k1 * a1 + k2 * a2 + ... + c` related to 0 by `rel`.
    fn con(terms: &[(u32, i64)], c: i64, rel: Rel) -> Con {
        Con {
            lin: Lin {
                terms: (terms.iter()).map(|&(n, k)| (a(n), Int::from(k))).collect(),
                constant: Int::from(c),
            },
            rel,
        }
    }

    /// `x + c == m * q + r` with `0 <= r <= m - 1`: the rows of `(x + c) mod m`.
    fn division(x: u32, c: i64, m: i64, q: u32, r: u32) -> Vec<Con> {
        vec![
            con(&[(x, 1), (q, -m), (r, -1)], c, Rel::Eq),
            con(&[(r, 1)], 0, Rel::Ge),
            con(&[(r, -1)], m - 1, Rel::Ge),
        ]
    }

    fn lin(terms: &[(u32, i64)], c: i64) -> Lin {
        con(terms, c, Rel::Ge).lin
    }

    #[test]
    fn divisions_of_one_term_by_one_modulus_read_one_remainder() {
        // `x + 2` and `x + 14` by 6: one remainder, the quotients 2 apart; `x + 3` by 6 and
        // `x + 2` by 4 differ, and a division whose remainder has no bounds is no division.
        let keep: HashSet<Atom> = [a(0)].into_iter().collect();
        let mut rows = division(0, 2, 6, 1, 2);
        rows.extend(division(0, 14, 6, 3, 4));
        rows.extend(division(0, 3, 6, 5, 6));
        rows.extend(division(0, 2, 4, 7, 8));
        rows.push(con(&[(0, 1), (9, -6), (10, -1)], 2, Rel::Eq));
        let to = same_divisions(&rows, &keep);
        assert_eq!(to.len(), 2, "{to:?}");
        assert_eq!(to[&a(4)], lin(&[(2, 1)], 0));
        // x + 14 == 6 q3 + r, x + 2 == 6 q1 + r, so q3 == q1 + 2.
        assert_eq!(to[&a(3)], lin(&[(1, 1)], 2));
        // The same rows written negated, and the second division's constant below the first's.
        let mut rows: Vec<Con> = division(0, 14, 6, 1, 2);
        rows.extend(division(0, 2, 6, 3, 4));
        rows[3].lin = rows[3].lin.times(-1);
        let to = same_divisions(&rows, &keep);
        assert_eq!(to[&a(3)], lin(&[(1, 1)], -2));
        // A remainder the caller reads is not set.
        let keep: HashSet<Atom> = [a(0), a(4)].into_iter().collect();
        let mut rows = division(0, 2, 6, 1, 2);
        rows.extend(division(0, 14, 6, 3, 4));
        assert!(same_divisions(&rows, &keep).is_empty());
    }

    #[test]
    fn atoms_bound_by_unit_equalities_read_the_atom_the_caller_reads() {
        // a1 == a0 + 12, a2 == a1 + 24, a3 == -a2 + 1: each read as a0's, the caller's.
        let keep: HashSet<Atom> = [a(0)].into_iter().collect();
        let read: HashSet<Atom> = [a(1), a(2), a(3)].into_iter().collect();
        let rows = vec![
            con(&[(1, 1), (0, -1)], -12, Rel::Eq),
            con(&[(2, 1), (1, -1)], -24, Rel::Eq),
            con(&[(3, 1), (2, 1)], -1, Rel::Eq),
            // a4 == 3 * a3: a4 is set by a3's, a0's, by the row that sets it alone.
            con(&[(4, 1), (3, -3)], 0, Rel::Eq),
        ];
        let read: HashSet<Atom> = read.into_iter().chain([a(4)]).collect();
        let (to, also) = unit_classes(&rows, &read, &keep);
        assert_eq!(to[&a(1)], lin(&[(0, 1)], 12));
        assert_eq!(to[&a(2)], lin(&[(0, 1)], 36));
        assert_eq!(to[&a(3)], lin(&[(0, -1)], -35));
        assert!(!to.contains_key(&a(0)));
        // a4 == 3 * a3 == 3 * (-a0 - 35).
        assert_eq!(also[&a(4)], lin(&[(0, -3)], -105));
    }

    #[test]
    fn bounds_beside_one_condition_keep_the_tightest() {
        let ge = |terms: &[(u32, i64)], c: i64| Formula::Con(con(terms, c, Rel::Ge));
        let eq = |terms: &[(u32, i64)], c: i64| Formula::Con(con(terms, c, Rel::Eq));
        // d is a1 == 5.
        let d = eq(&[(1, 1)], -5);
        let not_d = nnf(&d, false);
        let clauses = vec![
            // d || (a0 <= 37 && !d), d || a0 <= 13, d || a0 <= 25: d || a0 <= 13.
            Formula::or(vec![
                d.clone(),
                Formula::and(vec![ge(&[(0, -1)], 37), not_d.clone()]),
            ]),
            Formula::or(vec![d.clone(), ge(&[(0, -1)], 13)]),
            // d || 2 a0 >= 7, that is a0 >= 4, beside d || a0 >= 3: d || a0 >= 4.
            Formula::or(vec![d.clone(), ge(&[(0, 2)], -7)]),
            Formula::or(vec![d.clone(), ge(&[(0, -1)], 25)]),
            Formula::or(vec![d.clone(), ge(&[(0, 1)], -3)]),
            // A bound on an atom the condition reads is kept as it is.
            Formula::or(vec![d.clone(), ge(&[(1, 1)], -2)]),
            Formula::or(vec![d.clone(), ge(&[(1, 1)], -3)]),
            // So is a clause of three parts.
            Formula::or(vec![d.clone(), ge(&[(0, 1)], -9), ge(&[(2, 1)], 0)]),
        ];
        let out = rays_once(clauses.clone());
        let want = vec![
            Formula::or(vec![d.clone(), ge(&[(0, -1)], 13)]),
            Formula::or(vec![d.clone(), ge(&[(0, 1)], -4)]),
            clauses[5].clone(),
            clauses[6].clone(),
            clauses[7].clone(),
        ];
        assert_eq!(out, want);
    }
}
