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

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use super::formula::{Rel, Shared};
use super::{
    Atom, Con, Factor, Formula, Id, Lin, Model, Refusal, decide, nnf, satisfiable, shadow,
    shadow_whole,
};
use zedc_int::int::Int;

mod holes;
mod residues;
use holes::{Holes, hole_of};
use residues::{Reading, unit_classes};

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
    /// Whether `point`, `miss` and `closure` are still to be found: a conjunction decided
    /// whole ([`whole`]) finds them only when a conjunction reads it as a part
    /// ([`Extending::fill`]), so that separate questions over one chain do not each read
    /// every definition they reach.
    later: bool,
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

/// The definitions a definition reaches, projected exactly ([`Summary`]): by the definition (the
/// formula `def` gives, held as a key, so that the quotient and the remainder it defines share
/// it) and the atoms kept beside its own variables, `None` where none is made; and the
/// symbols, cone and non-leaf cone of each definition ([`Summaries::syms`]).
#[derive(Default)]
struct Summaries {
    rays: Rays,
    by: HashMap<Key, Option<Summary>>,
    syms: HashMap<Id, Arc<imbl::OrdSet<Atom>>>,
    cone: HashMap<Id, Arc<imbl::OrdSet<Id>>>,
    branch_cone: HashMap<Id, Arc<imbl::OrdSet<Id>>>,
    branch_roots: HashMap<Id, Arc<imbl::OrdSet<Id>>>,
    cyclic: HashSet<Id>,
}

/// The key of a summary: the definition's, and the atoms kept beside its own variables, in
/// order.
type Key = (Id, Vec<Atom>);

/// A definition `d` and the definitions it reaches (its cone), projected onto the atoms of its
/// key, which holds the variables `d` defines that others read: the integer points of the disjunction of `pieces`,
/// each a conjunction, read on these atoms, are those of the cone (exact, [`shadow`] with its
/// dark shadows). Each piece is one case of `d` (a branch of an `if`, of `min`, `max` or `abs`,
/// one side of a `!=`) with one piece of the summary below it, those with no point dropped
/// ([`decide`]) and those written alike kept once (LOAD-chain-sep-rest). Every
/// other atom of the cone is projected out, the symbols too: a question is asked of the
/// summaries and the parts beside them together, existentially, so projecting an atom out is
/// exact when nothing else read with the summary reads it, and each atom anything else reads
/// is in the key ([`Summaries::key`]). Some atoms outside the key stay in a piece, where
/// projecting them out needs a remainder ([`kept_quotients`], a symbol left by the projection,
/// and a variable of a definition that reads symbols alone, as `x div 3` does, left or kept
/// with the symbols when a projection leaves any atom): read existentially with the rest, they
/// keep the piece exact (LOAD-max-div-xr). Such a variable is a function of the symbols, one of
/// a fixed set, so the atoms of the pieces stay bounded along a chain.
#[derive(Clone)]
struct Summary {
    pieces: Vec<Vec<Con>>,
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
    // calls, and a chain with no point that its faces do not show empty. A chain with no
    // point whose faces hold nowhere by their holes and the residues of one modulus, such as
    // `q = (x < 10 || x > 20) && x mod 4 != 1` moved by 3, is answered from the faces
    // ([`Faces::free`], LOAD-holes-mod: 24.6 s at 16 links, refused, before; 0.05 s now), and
    // so is a chain of remainders, `p{i}(x) = x mod 3 < 2 && p{i-1}(x: x + 1)`, whose faces keep
    // the residues as rows over one quotient, read together (LOAD-mod-chain: 21.9 s at 200
    // links, refused, before; 0.12 s now); one emptied only by two moduli together
    // (`x mod 2 == 1 && x mod 3 == 1` between holes) is left to the solver on the faces, and
    // decided whole where it refuses. Test
    // `l01_38_presburger::extend::a_chain_whose_points_move_is_decided_whole`, which measures
    // it, `l01_38_presburger::one_scope::the_questions_of_a_chain_of_tests_scale` for the
    // chain whose points serve, and
    // `one_scope::the_questions_of_a_chain_of_holes_beside_one_modulus_scale` for the chains
    // the faces show empty, and `one_scope::the_questions_of_a_chain_of_remainders_scale`.
    // COMPLEXITY.md rows LOAD-chain-share, LOAD-holes-mod and LOAD-mod-chain. A complete
    // solution needs an incremental integer procedure: a simplex kept from the callee, with
    // its basis, to which the new rows are added, and the branch of an integer search redone
    // only where the new rows cut it.
    // A negation the part's point and the new definitions do not settle, and a question with
    // no kept part (`t(x) = h(x: x) > 0`), are decided with the summaries of the definitions
    // they read ([`Summaries`], LOAD-chain-sep), so separate tests over the links of one chain
    // of n definitions read O(n) rows in all; where a summary is not made, with every
    // definition they reach (the tradeoff at [`Summaries::summary`]). A conjunction with no
    // kept part is decided with the summaries as well, and its point, which a summary does not
    // give since it projects out the atoms of the definitions, is found only when a conjunction
    // that extends it is asked ([`Extending::fill`], LOAD-chain-sep-rest): with every
    // definition it reaches, as above, once for each such conjunction. The same holds for the negation of a
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
                if !k.later {
                    k.closure = self.closure(&g, def);
                }
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
        let answer = match f {
            Formula::And(_) => self.known[&Id::any(f)].answers.clone(),
            _ => Answers {
                holds: decide_defined(&mut self.sums, f.clone(), def),
                fails: decide_defined(&mut self.sums, Formula::negate(f.clone()), def),
            },
        };

        answer
    }

    /// The answers of the conjunction `g`, from those of its kept part when it has one: the
    /// part, among its conjunctions kept whole, with the most atoms, the first of those with as
    /// many, so that a call of a small function beside a long chain (`q(x: x) && p(x: x + 1)`)
    /// extends the chain and reads `q` beside it (LOAD-chain-affine). O(its parts).
    fn extend(&mut self, g: &Formula, def: &dyn Fn(u32) -> Formula, iface: Interface) -> Known {
        let kids = g.kids();
        for h in kids {
            if matches!(h, Formula::And(_)) {
                self.fill(h, def);
            }
        }
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
        // fixed, or the faces holding nowhere ([`Faces::free`]), before the whole is decided.
        if holds.is_none() {
            self.faces.make(&self.known, kids.iter(), def, iface);
            holds = self.faces.free(&self.known, kids, def);
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
            later: false,
        }
    }

    /// Finds the point, the point of negation and the atoms of the known conjunction `h`, and
    /// of the known conjunctions under it, where they are still to be found ([`Known::later`]):
    /// with every definition each reaches, as [`holds_whole`] and [`fails_whole`] find them,
    /// the parts under one first, since its atoms are theirs with its own added
    /// ([`Extending::closure`]). An explicit stack, since the parts nest as deep as the chain
    /// of calls; each is found once, and those found are the visited set. Time of each
    /// conjunction found and the definitions it reaches.
    fn fill(&mut self, h: &Formula, def: &dyn Fn(u32) -> Formula) {
        let later = |known: &HashMap<Id, Known>, g: &Formula| {
            matches!(g, Formula::And(_)) && known.get(&Id::any(g)).is_some_and(|k| k.later)
        };
        let mut todo = vec![(h.clone(), false)];
        while let Some((g, after)) = todo.pop() {
            if !later(&self.known, &g) {
                continue;
            }
            if !after {
                let kids: Vec<Formula> = (g.kids().iter())
                    .filter(|k| later(&self.known, k))
                    .cloned()
                    .collect();
                todo.push((g, true));
                todo.extend(kids.into_iter().map(|k| (k, false)));
                continue;
            }
            let id = Id::any(&g);
            let answers = &self.known[&id].answers;
            let (holds, fails) = (
                matches!(answers.holds, Ok(true)),
                matches!(answers.fails, Ok(true)),
            );
            let closure = self.closure(&g, def);
            let all = reached(&g, def);
            let found = |f: Formula| point(&with(&all, f)).ok().flatten();
            let at = holds.then(|| found(g.clone())).flatten();
            let miss = fails.then(|| found(Formula::negate(g.clone()))).flatten();
            if let Some(k) = self.known.get_mut(&id) {
                k.point = at;
                k.miss = miss;
                k.closure = closure;
                k.later = false;
            }
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
// Complexity tradeoff: naive version, a link whose largest kept part's point does not extend
// reads the rest of the conjunction, the whole chain, O(n²) over a chain of n links. Used:
// each kept conjunction has a face, made lazily and once on an explicit stack (the faces
// made are the visited set): `shadow` of its own constraints and the definitions they reach
// onto the atoms its call binds, so a chain's face stays a few rows however long the chain;
// other parts are read through their faces, O(the faces' rows) a link (8.2 times the bytes
// from 50 to 400 links). Tradeoffs: a face stands for its part only where nothing else in
// the question reads an atom it projects out, checked where it is made and where it is read;
// otherwise the question is asked with the parts, as before. Test
// `l01_38_presburger::one_scope::the_questions_of_a_drifting_chain_scale`; COMPLEXITY.md row
// LOAD-call-summary.
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
    /// `(Ok(true), Some(point))` where the solver finds a point, `(Ok(false), None)` where the
    /// faces hold nowhere (by their intervals and residues left, [`residues::read`], or by the
    /// solver), and `None` where no part has a face, an atom a face projects out is read
    /// beside it, or the solver refuses, so that the conjunction is then decided whole, as
    /// before. A point found here is a point of the conjunction, so it answers where the solver
    /// refuses the conjunction whole (`Err(Shadows)` on chains whose congruences meet moved
    /// holes); those answers are checked point by point in the random tests. The faces holding
    /// nowhere shows that the conjunction holds nowhere (LOAD-holes-mod): each face is the
    /// projection of its part and the definitions it reaches, so a point of the conjunction
    /// and its definitions gives one of every face and of every other part; so `q(x) = (x < 10
    /// || x > 20) && x mod 4 != 1` moved by 3 holds at no link from the fourth on, each answer
    /// `Ok(false)` from the faces, where the conjunction decided whole is refused (`Shadows`)
    /// and every link above it was decided whole too, about cubic in the chain. The point is
    /// sought first in the first interval between the holes that meets the residues left, by
    /// two bounds in place of the holes written as clauses, since the solver's time grows with
    /// the clauses (the chain moving `x < 10 || x > 12` by 4 below `x mod 4 != 1`: 2.5 s at its
    /// twentieth link with the clauses); where it finds none there, with the holes written out.
    /// Time of [`Faces::read`], of [`residues::read`], and of the solver on the faces and two
    /// bounds, or, where the point lies in no first interval, on the faces and the holes.
    fn free(
        &self,
        known: &HashMap<Id, Known>,
        kids: &[Formula],
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<(Result<bool, Refusal>, Option<Point>)> {
        let (f, holes) = self.read(known, kids, None, &Point::new(), def)?;
        let within = match residues::read(&f, &holes) {
            Reading::Empty => return Some((Ok(false), None)),
            Reading::Within(within) => within,
        };
        if !within.is_empty() {
            let narrow = Formula::and(std::iter::once(f.clone()).chain(within).collect());
            if let Ok(Some(p)) = point(&narrow) {
                return Some((Ok(true), Some(p)));
            }
        }
        let mut written = vec![f];
        for (a, h) in &holes {
            written.extend(h.clauses(a));
        }
        match point(&Formula::and(written)) {
            Ok(Some(p)) => Some((Ok(true), Some(p))),
            Ok(None) => Some((Ok(false), None)),
            Err(_) => None,
        }
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
/// the chain. A clause that keeps one atom in residues of one modulus through quotients no row
/// and no other clause reads (`a - 4 * q` bounded to a window in each disjunct) is keyed by
/// the atom, the modulus and the residues ([`residues::key`]), the quotients being free even
/// where two bounds of one conjunction read them (LOAD-holes-mod): such a clause comes from
/// each link of a chain moved by a multiple of the modulus, with its own quotient and its
/// window moved, and is kept once. Time of the clauses and rows, near linear.
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
    let mut kept_in: HashSet<residues::Key> = HashSet::new();
    (clauses.into_iter())
        .filter(|f| {
            let quotient = |a: &Atom| reads[a] == 1 && !keep.contains(a);
            if let Some(k) = residues::key(f, &quotient) {
                return kept_in.insert(k);
            }
            let joined = joined(f);
            let lone = |a: &Atom| quotient(a) && !joined.contains(a);
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
            Formula::Not(_) => {
                Formula::Not(Shared::new(parts.into_iter().next().expect("one part")))
            }
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
                    true => Formula::And(Shared::new(kids)),
                    false => Formula::Or(Shared::new(kids)),
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
// Complexity tradeoff: naive version, a link's new parts read with every definition they
// reach, the whole chain of definitions, so a chain of n tests over a chain of definitions
// costs O(n²) (74.6 times the instructions from 25 to 200 links). Used: only the definitions
// reached past the auxiliary variables the kept part's point already gives a value, each
// read once, O(new parts and their definitions) a link (8.1 times). Tradeoffs: where the
// point does not extend, or the shortened question does not settle it, the question is
// decided with all it reaches, O(n) that link, as before; the answers are `decide`'s. Test
// `l01_38_presburger::one_scope::the_questions_of_a_chain_of_tests_over_a_chain_of_definitions_scale`;
// COMPLEXITY.md row LOAD-chain-defs.
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
    // [`met`] fixes each atom of `m` to its value there, and the equalities conjoined in `f`
    // then fix others ([`fixed`]), so a set of holes over such an atom is checked at its value
    // and not written out (LOAD-holes-mod): a link whose callee's point lies in a hole asked
    // the solver with each hole as a clause, O(n) clauses at link n.
    let fixed = fixed(m, f);
    let mut written = vec![f.clone()];
    for (a, h) in holes {
        match fixed.get(*a).or_else(|| m.get(*a)) {
            Some(v) if h.holds(v) => return Ok(None),
            Some(_) => {}
            None => written.extend(h.clauses(a)),
        }
    }
    met(m, &Formula::and(written))
}

/// The values `m` gives the atoms of the equalities conjoined in `f`, and those these
/// equalities then fix: one with a single atom left without a value fixes it where its term at
/// the others is divisible by the atom's coefficient. Each equality is read once its other
/// atoms have values, whatever their order in `f`, so the time is that of `f`.
fn fixed(m: &Point, f: &Formula) -> Model {
    let mut eqs: Vec<&Con> = Vec::new();
    // Each shared conjunction read once.
    let mut seen: HashSet<Id> = HashSet::new();
    let mut todo = vec![f];
    while let Some(g) = todo.pop() {
        match g {
            Formula::And(gs) => {
                if seen.insert(Id::any(g)) {
                    todo.extend(gs.iter());
                }
            }
            Formula::Con(c) if c.rel == Rel::Eq => eqs.push(c),
            _ => {}
        }
    }
    let mut at = Model::new();
    // The equalities that read each atom without a value, and how many such atoms each reads.
    let mut by: HashMap<&Atom, Vec<usize>> = HashMap::new();
    let mut left: Vec<usize> = Vec::with_capacity(eqs.len());
    for (i, c) in eqs.iter().enumerate() {
        let mut n = 0;
        for a in c.lin.terms.keys() {
            match m.get(a) {
                Some(v) => {
                    at.insert(a.clone(), v.clone());
                }
                None => {
                    by.entry(a).or_default().push(i);
                    n += 1;
                }
            }
        }
        left.push(n);
    }
    let mut ready: Vec<usize> = (0..eqs.len()).filter(|&i| left[i] == 1).collect();
    while let Some(i) = ready.pop() {
        let c = eqs[i];
        let mut rest = c.lin.constant.clone();
        let mut unknown: Option<(&Atom, &Int)> = None;
        for (a, k) in &c.lin.terms {
            match at.get(a) {
                Some(v) => rest = &rest + &(k * v),
                None => unknown = Some((a, k)),
            }
        }
        // `None` where another equality fixed the atom first.
        let Some((a, k)) = unknown else { continue };
        if !rest.mod_floor(k).is_zero() {
            continue;
        }
        at.insert(a.clone(), -&rest.div_floor(k));
        for &j in by.get(a).into_iter().flatten() {
            left[j] -= 1;
            if left[j] == 1 {
                ready.push(j);
            }
        }
    }
    at
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
        Ok(true) => (Ok(true), point(f).ok().flatten()),
        other => (other, None),
    }
}

/// A point where `f` holds, every atom of `f` given a value, when the solver gives one: of `f`,
/// or, where the solver refuses `f`, of `f` with its bindings in place ([`Bound`]); `Ok(None)`
/// when either form holds nowhere, which is exact, and the first refusal when both are refused
/// or `f` has no bindings to put in place.
fn point(f: &Formula) -> Result<Option<Point>, Refusal> {
    let filled = |g: &Formula, m: Model| {
        let mut p: Point = m.into_iter().collect();
        for a in g.atoms() {
            p.entry(a).or_default();
        }
        p
    };
    match satisfiable(f) {
        Ok(m) => Ok(m.map(|m| filled(f, m))),
        Err(e) => {
            let Some(mut b) = Bound::of(f) else {
                return Err(e);
            };
            let Some(m) = satisfiable(&b.f).map_err(|_| e)? else {
                return Ok(None);
            };
            let mut p = filled(&b.f, m);
            b.back(&mut p);
            Ok(Some(p))
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
        Ok(true) => (Ok(true), point(&with(&reached(g, def), not)).ok().flatten()),
        other => (other, None),
    }
}

/// The answers of `g`, decided whole, with the summaries of the definitions it reads where
/// they answer ([`decide_defined`]); its points and atoms are found later, when a conjunction
/// reads it as a part ([`Extending::fill`]).
fn whole(sums: &mut Summaries, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Known {
    Known {
        answers: Answers {
            holds: decide_defined(sums, g.clone(), def),
            fails: decide_defined(sums, Formula::negate(g.clone()), def),
        },
        point: None,
        miss: None,
        size: g.atoms().len(),
        closure: Atoms::new(),
        later: true,
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
    if sums.rays.holds(&f, def) {
        return Ok(true);
    }
    if let Some(d) = sums.read(&f, def)
        && let Ok(b) = decide(&with(&d, f.clone()))
    {
        return Ok(b);
    }
    decided(&with(&reached(&f, def), f))
}

/// A one-sided eventual bound along the common input ray: `Some(false)` is a finite
/// bound, `Some(true)` diverges towards that side, and `None` proves nothing.
#[derive(Clone, Copy, Default, Debug)]
struct RayBound {
    lower: Option<bool>,
    upper: Option<bool>,
}

#[derive(Default)]
struct Rays {
    by: HashMap<Id, Option<[BTreeMap<Atom, RayBound>; 2]>>,
    total: HashMap<Id, bool>,
    rejected_shape: HashSet<(Id, Atom)>,
}

impl Rays {
    /// An existential inequality needs a witness, not the graph of its output. Along
    /// each of the two rays all free symbols equal +t or -t. Each accepted definition
    /// is total over its inputs, and every branch proves eventual bounds on its outputs.
    /// A lower bound diverging to +infinity proves the inequality for sufficiently large t.
    // Complexity tradeoff: explicit graph summaries of successive halvings carry k-bit
    // coefficients at link k (I13). These certificates keep two constant-sized bounds per
    // output atom and share the definition DAG, O(V+E) storage and traversal, plus local
    // projections and decisions proving totality. No coefficient is composed across links.
    // Local totality can itself be hard; its solver cost is not claimed O(n log n) in general.
    // Unsupported questions and certificates use the existing graph-summary path.
    fn holds(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> bool {
        // Both cofinal directions below witness every threshold and either nonzero
        // coefficient sign. Inspect the borrowed row first, avoiding allocation on the
        // unsupported equality and multiple-value questions (I29).
        let row = match f {
            Formula::Con(c) if c.rel == Rel::Ge => c,
            Formula::Not(g) => match &**g {
                Formula::Con(c) if c.rel == Rel::Ge => c,
                _ => return false,
            },
            _ => return false,
        };
        if row.lin.terms.len() != 1 {
            return false;
        }
        let (a, k) = row.lin.terms.first_key_value().expect("one term");
        if k.is_zero() {
            return false;
        }
        let Atom::Aux(n) = a else {
            return false;
        };
        let a = a.clone();
        let root = def(*n);
        let id = Id::any(&root);
        let trigger_key = (id, a.clone());
        if self.rejected_shape.contains(&trigger_key) {
            return false;
        }
        // Reject sign-changing local output definitions before walking their cones. This
        // is only a trigger: passing it proves nothing. It keeps abs chains on their cheap
        // existing summary path. Unsupported multiple-value questions were rejected above.
        if !self.by.contains_key(&id)
            && (!Self::consistent_slopes(&root, &a)
                || Def::of(root.clone(), def).is_some_and(|d| {
                    d.inputs
                        .iter()
                        .any(|&n| !Self::consistent_slopes(&def(n), &Atom::Aux(n)))
                }))
        {
            // A multi-output definition can reflect one output and leave another cofinal.
            // Cache this trigger per output, never for the whole definition (R5-C37).
            self.rejected_shape.insert(trigger_key);
            return false;
        }
        self.ensure(root.clone(), def);
        let cofinal = (0..2).any(|d| {
            self.bound(&a, d, def)
                .is_some_and(|b| b.lower == Some(true))
        }) && (0..2).any(|d| {
            self.bound(&a, d, def)
                .is_some_and(|b| b.upper == Some(true))
        });
        // Potential bounds from impossible definitions are not witnesses. Demand totality
        // only when both sides would avoid the graph-summary path (I29).
        if !cofinal {
            return false;
        }
        self.ensure_total(root, def);
        self.total.get(&id) == Some(&true)
    }

    // Complexity tradeoff: building a sign map and a visited DAG walk just to reject
    // binary reflection definitions allocates on every abs link. Recognize that grammar
    // directly in borrowed rows, O(T) term probes without allocations. This is only a
    // trigger, not a claim that every other local formula has consistent slopes.
    fn consistent_slopes(f: &Formula, output: &Atom) -> bool {
        fn equation<'a>(f: &'a Formula, output: &Atom) -> Option<&'a Con> {
            let row = |g: &'a Formula| match g {
                Formula::Con(c)
                    if c.rel == Rel::Eq && c.lin.terms.get(output).is_some_and(Int::is_unit) =>
                {
                    Some(c)
                }
                _ => None,
            };
            match f {
                Formula::And(gs) => gs.iter().find_map(row),
                _ => row(f),
            }
        }
        let Formula::Or(gs) = f else { return true };
        let [left, right] = gs.as_slice() else {
            return true;
        };
        let (Some(left), Some(right)) = (equation(left, output), equation(right, output)) else {
            return true;
        };
        let (kl, kr) = (&left.lin.terms[output], &right.lin.terms[output]);
        for (a, k) in &left.lin.terms {
            if a == output || k.is_zero() {
                continue;
            }
            if let Some(r) = right.lin.terms.get(a).filter(|r| !r.is_zero()) {
                if (kl.is_positive() != k.is_positive()) != (kr.is_positive() != r.is_positive()) {
                    return false;
                }
            }
        }
        true
    }

    fn bound(&self, a: &Atom, direction: usize, def: &dyn Fn(u32) -> Formula) -> Option<RayBound> {
        match a {
            Atom::Sym(_) => Some(if direction == 0 {
                RayBound {
                    lower: Some(true),
                    upper: None,
                }
            } else {
                RayBound {
                    lower: None,
                    upper: Some(true),
                }
            }),
            Atom::Aux(n) => {
                let f = def(*n);
                if free(&f) {
                    return Some(RayBound {
                        lower: Some(false),
                        upper: Some(false),
                    });
                }
                self.by.get(&Id::any(&f))?.as_ref()?[direction]
                    .get(a)
                    .copied()
            }
            Atom::Product(..) => None,
        }
    }

    fn ensure(&mut self, f: Formula, def: &dyn Fn(u32) -> Formula) {
        if free(&f) || self.by.contains_key(&Id::any(&f)) {
            return;
        }
        let mut open = HashSet::new();
        let mut stack = vec![(f, false)];
        while let Some((f, exit)) = stack.pop() {
            let id = Id::any(&f);
            if self.by.contains_key(&id) || free(&f) {
                continue;
            }
            let Some(d) = Def::of(f.clone(), def) else {
                self.by.insert(id, None);
                continue;
            };
            if !exit {
                if !open.insert(id) {
                    self.by.insert(id, None);
                    continue;
                }
                stack.push((f, true));
                let mut seen = HashSet::new();
                for &n in d.inputs.iter().rev() {
                    let child = def(n);
                    if seen.insert(Id::any(&child)) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            open.remove(&id);
            let result = (|| {
                if d.reads.iter().any(|a| matches!(a, Atom::Product(..))) {
                    return None;
                }
                for &n in &d.inputs {
                    self.by.get(&Id::any(&def(n)))?.as_ref()?;
                }
                let own: BTreeSet<Atom> = d.own.iter().map(|&n| Atom::Aux(n)).collect();
                let mut branches = cases(&d.f)?;
                // Canonical local proof obligations keep a permutation of rows/cases
                // from changing the totality solver's elimination order.
                for rows in &mut branches {
                    rows.sort();
                    rows.dedup();
                }
                branches.sort();
                branches.dedup();
                let mut result = [BTreeMap::new(), BTreeMap::new()];
                for (direction, out) in result.iter_mut().enumerate() {
                    let mut first = true;
                    for rows in &branches {
                        let got = ray_branch(rows, &own, &|a| self.bound(a, direction, def));
                        if first {
                            *out = got;
                            first = false;
                        } else {
                            for (a, b) in out.iter_mut() {
                                let c = got.get(a)?;
                                b.lower = b.lower.zip(c.lower).map(|(x, y)| x && y);
                                b.upper = b.upper.zip(c.upper).map(|(x, y)| x && y);
                            }
                        }
                    }
                    if first {
                        return None;
                    }
                }
                Some(result)
            })();
            self.by.insert(id, result);
        }
    }
    // Complexity tradeoff: eagerly proving every visited definition total paid for local
    // projections even on queries no ray can answer (R4 I29: abs +18%). Used: cache cheap
    // potential bounds first, then prove totality only for a cofinal single-value query.
    // Traversal is O(V+E), with each original local projection/decision performed once.
    // Solver cost on an arbitrary local formula remains structural, not a linear guarantee.
    fn ensure_total(&mut self, f: Formula, def: &dyn Fn(u32) -> Formula) {
        let mut stack = vec![(f, false)];
        let mut open = HashSet::new();
        while let Some((f, exit)) = stack.pop() {
            if free(&f) {
                continue;
            }
            let id = Id::any(&f);
            if self.total.contains_key(&id) {
                continue;
            }
            let Some(d) = Def::of(f.clone(), def) else {
                self.total.insert(id, false);
                continue;
            };
            if !exit {
                if !open.insert(id) {
                    self.total.insert(id, false);
                    continue;
                }
                stack.push((f, true));
                let mut seen = HashSet::new();
                for &n in d.inputs.iter().rev() {
                    let child = def(n);
                    if seen.insert(Id::any(&child)) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            open.remove(&id);
            let result = (|| {
                if d.reads.iter().any(|a| matches!(a, Atom::Product(..))) {
                    return None;
                }
                if d.inputs
                    .iter()
                    .any(|&n| self.total.get(&Id::any(&def(n))) != Some(&true))
                {
                    return None;
                }
                let own: BTreeSet<Atom> = d.own.iter().map(|&n| Atom::Aux(n)).collect();
                let mut branches = cases(&d.f)?;
                for rows in &mut branches {
                    rows.sort();
                    rows.dedup();
                }
                branches.sort();
                branches.dedup();
                // Prove totality for arbitrary values of all inputs, not merely the
                // chosen ray. Each projection is exact; any own atom left rejects it.
                let mut guards = Vec::new();
                for rows in &branches {
                    let keep = |a: &Atom| !own.contains(a);
                    let rows = remainders_as_pairs(rows, &keep);
                    let rows = without_free_pairs_for(rows, &|a| own.contains(a));
                    let mut projected = shadow_whole(&rows, &keep)?;
                    projected.sort();
                    projected.dedup();
                    if projected
                        .iter()
                        .any(|c| c.lin.terms.keys().any(|a| own.contains(a)))
                    {
                        return None;
                    }
                    guards.push(Formula::and(
                        projected.into_iter().map(Formula::Con).collect(),
                    ));
                }
                guards.sort();
                guards.dedup();
                if decide(&Formula::negate(Formula::or(guards))) != Ok(false) {
                    return None;
                }

                Some(())
            })()
            .is_some();
            self.total.insert(id, result);
        }
    }
}

/// Infer one-sided bounds by a monotone worklist. A row derives a bound for a term
/// when the other terms all have upper bounds; an equality also supplies its negation.
// Complexity tradeoff: rescanning all rows after each discovered bound is O(r v t).
// Row aggregates count unknown and negatively diverging terms; each atom-side is updated
// at most twice. Only the transitions to one/zero unknowns and one/two diverging terms
// scan candidates, O(T log T) work and O(T) storage for T term occurrences. Finite bounds
// retain only existence of a constant, deliberately losing its numerical value.
fn ray_branch(
    rows: &[Con],
    own: &BTreeSet<Atom>,
    input: &dyn Fn(&Atom) -> Option<RayBound>,
) -> BTreeMap<Atom, RayBound> {
    struct Row {
        terms: BTreeMap<Atom, Int>,
        unknown: BTreeSet<Atom>,
        falling: BTreeSet<Atom>,
    }
    let mut bounds: BTreeMap<Atom, RayBound> = own
        .iter()
        .cloned()
        .map(|a| (a, RayBound::default()))
        .collect();
    let mut rs: Vec<Row> = Vec::new();
    let mut at: HashMap<Atom, Vec<usize>> = HashMap::new();
    for c in rows {
        let neg = c.lin.times(-1);
        for terms in std::iter::once(&c.lin.terms).chain((c.rel == Rel::Eq).then_some(&neg.terms)) {
            let mut unknown = BTreeSet::new();
            let mut falling = BTreeSet::new();
            for (a, k) in terms {
                let b = if own.contains(a) {
                    RayBound::default()
                } else {
                    input(a).unwrap_or_default()
                };
                let side = if k.is_positive() { b.upper } else { b.lower };
                match side {
                    None => {
                        unknown.insert(a.clone());
                    }
                    Some(true) => {
                        falling.insert(a.clone());
                    }
                    _ => {}
                }
                at.entry(a.clone()).or_default().push(rs.len());
            }
            rs.push(Row {
                terms: terms.clone(),
                unknown,
                falling,
            });
        }
    }
    let mut queue: Vec<usize> = (0..rs.len()).collect();
    let mut pending: HashSet<usize> = queue.iter().copied().collect();
    while let Some(i) = queue.pop() {
        pending.remove(&i);
        let row = &rs[i];
        if row.unknown.len() > 1 {
            continue;
        }
        let candidates: Vec<(Atom, bool, bool)> = row
            .terms
            .iter()
            .filter(|(a, _)| own.contains(*a))
            .filter_map(|(a, k)| {
                if !row.unknown.is_empty() && !row.unknown.contains(a) {
                    return None;
                }
                let falling = row.falling.len() - usize::from(row.falling.contains(a)) > 0;
                Some((a.clone(), k.is_positive(), falling))
            })
            .collect();
        for (a, lower, diverges) in candidates {
            let b = bounds.get_mut(&a).unwrap();
            let side = if lower { &mut b.lower } else { &mut b.upper };
            if side.is_some_and(|old| old || !diverges) {
                continue;
            }
            *side = Some(diverges);
            for &j in &at[&a] {
                let row = &mut rs[j];
                // The bound we derived is an upper bound on this row's term only
                // when that term has the opposite sign.
                if row.terms[&a].is_positive() == lower {
                    continue;
                }
                let old = (row.unknown.len().min(2), row.falling.len().min(2));
                row.unknown.remove(&a);
                if diverges {
                    row.falling.insert(a.clone());
                }
                let new = (row.unknown.len().min(2), row.falling.len().min(2));
                if new != old && new.0 <= 1 && pending.insert(j) {
                    queue.push(j);
                }
            }
        }
    }
    bounds
}

impl Summaries {
    /// The definitions `f` reaches, in place of all of them, for a question asked of `f`: the
    /// definitions [`Summaries::local`] reads beside `f`, with summaries of the frontiers left
    /// below them, each keeping every atom of its cone that `f` or they read. `None` where a
    /// summary is not made. Time of `f`, of the definitions read beside it and of the
    /// summaries made, each made once.
    fn read(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Option<Vec<Formula>> {
        let reads = reads(f);
        let own = BTreeSet::new();
        loop {
            match self.local(&reads, &own, None, &[], def) {
                Local::Need(n) => self.made(n, def),
                Local::Unmade => return None,
                Local::Ready(mut beside, below) => {
                    beside.extend(below.into_iter().map(Summary::rows));
                    return Some(beside);
                }
            }
        }
    }

    /// Makes what `n` names: a summary, with those below it first, or a set of symbols.
    fn made(&mut self, n: Need, def: &dyn Fn(u32) -> Formula) {
        match n {
            Need::RootsMany(fs) => {
                for f in fs {
                    self.roots(f, def);
                }
            }
            Need::SymsMany(fs) => {
                for f in fs {
                    self.syms(f, def);
                }
            }
            Need::Summaries(js) => {
                for (k, h) in js {
                    self.summary(k, h, def);
                }
            }
            Need::Syms(h) => self.syms(h, def),
        }
    }

    /// The summary of the definition `g` under the key `k`, made after those it is made from,
    /// each made once and remembered: an explicit stack, since the path is as deep as the
    /// chain of definitions. A summary needed while it is being made (a cycle, which a scope's
    /// numbering does not make) is not made.
    // Complexity tradeoff: deciding every question with its whole reached chain visits
    // Theta(n²) definition incidences over n links. Cache each (definition, kept-atom key)
    // summary and project it from the summaries below, made once with an explicit stack.
    // Cost is the sum of local case products, projections, simplifications and merges,
    // plus metadata/decomposition work. A fixed-input, bounded-piece, bounded-coefficient
    // chain can take O(n) such local steps; this is not a bound for arbitrary DAGs or bit
    // widths. Composed coefficients can gain a bit a link (I13), keys and case products can
    // grow, and numeric quotient-offset splitting can enumerate an unbounded interval
    // (I26/I31/I34). Unsupported projections still use the exact whole decision; its cost
    // is not thereby within the author's shipping bound. Those gaps remain under review.
    //
    // Rows through verified division pairs, kept input/leaf atoms, envelope reduction,
    // integer-empty-gap merges and wide-key retry retain the accepted I1--I4/I8/I14 rules.
    // Unit-bounded free-pair folding (I28) keeps composed coefficients out of many decision
    // calls. Periodic offsets and linear-value bindings handle the fixed-period cases
    // (I12/I26), without a general near-linear splitter proof. Single-value half-line
    // questions can instead use Rays' total cofinal certificates before graph construction.
    //
    // Symbols and cones use persistent ordered sets and shared-node differences (R5-C36);
    // metadata cost is unshared tree contents plus new insertions, rather than rescanning
    // every shared prefix. local batches missing prerequisites and indexes root/key
    // incidences (I21/I30); its comment gives the remaining parametric cost, not a general
    // amortized O(n log n) claim. Tradeoffs: caches per distinct key, persistent membership
    // trees, and exact union-of-row pieces; whole fallback and difficult local projection
    // remain potentially superlinear. No size cutoff, iteration budget or sampled answer.
    //
    // Tests: one_scope::summaries_of_definitions_give_the_answers_of_the_definitions compares
    // forward/reverse/alone queries with whole definitions (including I21); the max/min/div
    // value oracle checks integer arithmetic, and the entire one_scope scale table measures
    // n and 8n. Unit guards cover metadata diamonds, wide frontiers and convex integer joins.
    fn summary(&mut self, k: Key, g: Formula, def: &dyn Fn(u32) -> Formula) {
        let mut stack: Vec<(Key, Formula)> = vec![(k, g)];
        let mut open: HashSet<Key> = HashSet::new();
        while let Some((k, g)) = stack.last() {
            if self.by.contains_key(k) {
                open.remove(k);
                stack.pop();
                continue;
            }
            open.insert(k.clone());
            match self.make(k, g, def) {
                Made::First(Need::RootsMany(fs)) => {
                    for f in fs {
                        self.roots(f, def);
                    }
                }
                Made::First(Need::SymsMany(fs)) => {
                    for f in fs {
                        self.syms(f, def);
                    }
                }
                Made::First(Need::Syms(h)) => self.syms(h, def),
                Made::First(Need::Summaries(js)) if js.iter().all(|(k, _)| !open.contains(k)) => {
                    stack.extend(js.into_iter().rev());
                }
                made => {
                    let (s, extra) = match made {
                        Made::Done(s, extra) => (s, extra),
                        Made::First(_) => (None, None),
                    };
                    if let Some((k, _)) = stack.pop() {
                        open.remove(&k);
                        if let (Some(k2), Some(s)) = (extra, &s) {
                            self.by.entry(k2).or_insert_with(|| Some(s.clone()));
                        }
                        self.by.insert(k, s);
                    }
                }
            }
        }
    }

    /// The summary of the definition `g` under the key `k`, when the summary below it is known,
    /// or what to make first: the projection of each case of `g` and of the definitions read
    /// beside it ([`Summaries::local`]) with each piece of the summary below them, onto the
    /// atoms of `k`. Time of `g`, of those beside it and of the pieces below, times the number
    /// of cases, and of one decision of each piece made (and of each of its rows, where
    /// [`lean`] runs).
    fn make(&self, k: &Key, g: &Formula, def: &dyn Fn(u32) -> Formula) -> Made {
        let Some(d) = Def::of(g.clone(), def) else {
            return Made::Done(None, None);
        };
        let own: BTreeSet<Atom> = d.own.iter().map(|&n| Atom::Aux(n)).collect();
        let (beside, below) = match self.local(&d.reads, &own, Some(d.id), &k.1, def) {
            Local::Ready(beside, below) => (beside, below),
            Local::Need(n) => return Made::First(n),
            Local::Unmade => return Made::Done(None, None),
        };
        let mut all = cases(g);
        for f in &beside {
            all = all.and_then(|a| Some(cross(&a, &cases(f)?)));
        }
        let Some(all) = all else {
            return Made::Done(None, None);
        };
        let key: HashSet<&Atom> = k.1.iter().collect();
        // A variable of a definition that reads symbols alone (`q2` of `x div 3`): a function of
        // the inputs, as a symbol is, and one of a fixed set, so one left is kept as a symbol.
        let leaf = |a: &Atom| match a {
            Atom::Aux(n) => Def::of(def(*n), def).is_some_and(|m| m.inputs.is_empty()),
            _ => false,
        };
        let alone = [Vec::new()];
        let crossed: Vec<Vec<Con>>;
        let below_pieces: &[Vec<Con>] = match below.as_slice() {
            [] => &alone,
            [s] => &s.pieces,
            [first, rest @ ..] => {
                crossed = rest
                    .iter()
                    .fold(first.pieces.clone(), |acc, s| cross(&acc, &s.pieces));
                &crossed
            }
        };
        let mut pieces: BTreeSet<Vec<Con>> = BTreeSet::new();
        let mut all_wide = true;
        for c in &all {
            for p in below_pieces {
                let mut rows0: Vec<Con> = c.iter().chain(p).cloned().collect();
                rows0.sort();
                rows0.dedup();
                let mut work: Vec<(Vec<Con>, bool)> = vec![(rows0, false)];
                'piece: while let Some((rows, mut wide)) = work.pop() {
                    if decide_cons(rows.clone()) == Ok(false) {
                        continue 'piece;
                    }
                    // The atoms kept beside the key: those whose elimination needs a remainder of
                    // a kept atom ([`kept_quotients`]). They stay in the piece, read as any value.
                    let more =
                        kept_quotients(&remainders_as_pairs(&rows, &|a| key.contains(a)), &|a| {
                            key.contains(a)
                        });
                    let syms: HashSet<&Atom> = (rows.iter())
                        .flat_map(|c| c.lin.terms.keys())
                        .filter(|a| matches!(a, Atom::Sym(_)) || leaf(a))
                        .collect();
                    let out = loop {
                        let keep = |a: &Atom| {
                            key.contains(a) || more.contains(a) || (wide && syms.contains(a))
                        };
                        let elim = |a: &Atom| !keep(a);
                        let Some(mut out) = shadow_whole(&by_pairs(rows.clone(), &elim), &keep)
                        else {
                            continue 'piece;
                        };
                        out = envelope(out);
                        // Before that, the rows the projection made are read through their
                        // division pairs again ([`by_pairs`]), which leaves the projection one
                        // atom fewer to eliminate across coefficients above 1.
                        let left =
                            |out: &[Con]| (out.iter()).any(|c| c.lin.terms.keys().any(&elim));
                        if left(&out) {
                            match shadow_whole(&by_pairs(out, &elim), &keep) {
                                Some(o) => out = envelope(o),
                                None => continue 'piece,
                            }
                        }
                        let other = |c: &Con| {
                            c.lin
                                .terms
                                .keys()
                                .any(|a| elim(a) && !matches!(a, Atom::Sym(_)) && !leaf(a))
                        };
                        if !wide
                            && out
                                .iter()
                                .any(|c| c.lin.terms.keys().any(|a| elim(a) && leaf(a)))
                        {
                            wide = true;
                            continue;
                        }
                        // A piece with no point is dropped: [`shadow`] shows it only where an
                        // elimination makes a false row, and not by two bounds of a kept atom
                        // (`q <= 4 && q >= 9`) or when it cannot eliminate an atom. A piece that
                        // keeps an atom outside the key otherwise leaves no summary.
                        if decide_cons(out.clone()) == Ok(false) {
                            continue 'piece;
                        }
                        // A row the others imply may pair with a remainder's bound so that the
                        // dark shadow is not the real one (`x >= 2 * q` beside `x >= 4 * q` and
                        // `x >= -1`, with `4 * r` on both sides of `x`): such rows are dropped,
                        // and the piece projected again.
                        if left(&out) {
                            match shadow_whole(&lean(out), &keep) {
                                Some(o) => out = o,
                                None => continue 'piece,
                            }
                        }
                        // A symbol left (`x` of `2 * x == q + 9`, whose projection is a
                        // congruence of `q`) is kept, read as any value: the symbols of a chain
                        // are its inputs, read through the key. Any other atom left leaves no
                        // summary unless its periodic quotient offset is finitely bounded
                        // ([`quotient_offsets`]).
                        if !wide
                            && out.iter().any(|c| {
                                c.lin
                                    .terms
                                    .keys()
                                    .any(|a| elim(a) && !matches!(a, Atom::Sym(_)))
                            })
                        {
                            wide = true;
                            continue;
                        }
                        if out.iter().any(other) {
                            if let Some(split) = quotient_offsets(&rows, &keep, &leaf, def) {
                                all_wide = false;
                                for mut branch in split.into_iter().rev() {
                                    branch.sort();
                                    branch.dedup();
                                    work.push((branch, true));
                                }
                                continue 'piece;
                            }
                            return Made::Done(None, None);
                        }
                        if !wide
                            || kept_quotients(
                                &remainders_as_pairs(&rows, &|a| {
                                    key.contains(a) || syms.contains(a)
                                }),
                                &|a| key.contains(a) || syms.contains(a),
                            ) != more
                        {
                            all_wide = false;
                        }
                        break out;
                    };
                    let Some(out) = normalize_own_leaf(out, &d.own, &leaf) else {
                        continue 'piece;
                    };
                    let mut out = lean(out);
                    out.sort();
                    out.dedup();
                    pieces.insert(out);
                }
            }
        }
        let pieces = merge_pieces(pieces);
        let atoms: BTreeSet<Atom> = (pieces.iter().flatten())
            .flat_map(|c| c.lin.terms.keys().cloned())
            .collect();
        let extra = if all_wide && !pieces.is_empty() {
            let wide_atoms: Vec<Atom> =
                k.1.iter()
                    .chain(&atoms)
                    .filter(|a| key.contains(a) || matches!(a, Atom::Sym(_)) || leaf(a))
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
            (wide_atoms != k.1
                && matches!(
                    self.local(&d.reads, &own, Some(d.id), &wide_atoms, def),
                    Local::Ready(b2, s2)
                        if b2 == beside
                            && s2.len() == below.len()
                            && s2.iter().zip(&below).all(|(a, b)| std::ptr::eq(*a, *b))
                ))
            .then_some((k.0, wide_atoms))
        } else {
            None
        };
        Made::Done(
            Some(Summary {
                pieces: pieces.into_iter().collect(),
            }),
            extra,
        )
    }

    /// The definitions read beside `reads`, the atoms of a definition whose own variables are
    /// `own` and whose key is `self_id`, or of a question (`self_id` none), and the summaries of
    /// the definitions left below them with pairwise-disjoint non-leaf cones, whose keys keep
    /// `keep` and any symbol shared between two of those cones: the definitions of the variables
    /// `reads` reads are a frontier; any definition strictly inside another frontier definition's
    /// cone (`Summaries::cone`) is dropped; with two or more left, leaf definitions (reading
    /// symbols alone) are read beside, and among definitions whose non-leaf cones overlap
    /// (`Summaries::branch_cone`) all tied at the smallest cone size are read beside, their
    /// inputs joining the frontier, until the remaining non-leaf cones are pairwise disjoint.
    /// Functional symbol leaves (`v == e(syms)` and Euclidean division pairs over symbols) are
    /// single-valued functions of the symbols, so two chains sharing them keep both summaries
    /// once their shared symbols are in `keep`. Because cone membership and size depend only on
    /// the definition DAG and never on `Aux` numbering, answers do not depend on query or
    /// numbering order (LOAD-max-div-xr I21).
    // Complexity tradeoff: highest-Aux frontier selection unrolled O(depth) definitions
    // per question and made I21 order-dependent; all-pairs cone tests added Omega(F²) work
    // at width F, repeated F times for cold missing prerequisites (I30). Used: batch missing
    // metadata/summaries, remove contained frontiers, index terminal non-leaf roots to mark
    // overlapping owners, and expand every minimum-size overlapping cone. Route key atoms
    // by root/symbol ownership, confirming Aux membership against the actual cone. Per plan
    // work is the parsed input, persistent ancestor unions, root/symbol incidences and
    // distributed key incidences (with set/map lookup factors); repeated expansion and
    // unshared set contents/interfaces do not yet have a general O(n log n) bound.
    // Tradeoffs: persistent full-cone and lazily built root indexes. Functional symbol leaves
    // are read beside and shared symbols kept, preserving the exact relational decomposition.
    fn local<'a>(
        &'a self,
        reads: &BTreeSet<Atom>,
        own: &BTreeSet<Atom>,
        self_id: Option<Id>,
        keep: &[Atom],
        def: &dyn Fn(u32) -> Formula,
    ) -> Local<'a> {
        let mut frontier: Vec<Def> = Vec::new();
        let mut seen_init: HashSet<Id> = HashSet::new();
        for a in reads {
            for n in auxes(a) {
                let f = def(n);
                if free(&f) || own.contains(&Atom::Aux(n)) {
                    continue;
                }
                let id = Id::any(&f);
                if Some(id) == self_id {
                    return Local::Unmade;
                }
                if !seen_init.insert(id) {
                    continue;
                }
                let Some(d) = Def::of(f, def) else {
                    return Local::Unmade;
                };
                frontier.push(d);
            }
        }
        // Complexity tradeoff: requesting one uncached cone at a time reparsed the whole
        // width-F initial frontier F times. Collect all symbol/cone prerequisites together;
        // their visited caches share descendants, and the initial frontier is built twice.
        let mut missing_syms = Vec::new();
        for d in &frontier {
            if !self.cone.contains_key(&d.id) && !self.cyclic.contains(&d.id) {
                missing_syms.push(d.f.clone());
                continue;
            }
            if self.cyclic.contains(&d.id)
                || self_id.is_some_and(|sid| self.cone[&d.id].contains(&sid))
            {
                return Local::Unmade;
            }
        }
        if !missing_syms.is_empty() {
            return Local::Need(Need::SymsMany(missing_syms));
        }
        let mut beside: Vec<Def> = Vec::new();
        let mut expanded: HashSet<Id> = HashSet::new();
        loop {
            if frontier.len() <= 1 {
                break;
            }
            // Complexity tradeoff: pairwise/smaller-side containment can still do F²
            // probes on F unequal-height suffixes over one long shared prefix (I30).
            // A largest cone covering the frontier is a direct certificate. Otherwise
            // union each persistent cone minus its own Id: membership in that union means
            // exactly that another frontier contains the definition. Work is F lookups,
            // F persistent removals and shared_set_union's directed-difference cost, not
            // an enumeration of frontier pairs. Shared-prefix suffixes cost O(F log V).
            // This remains a parametric set-union bound, not a general DAG amortization.
            // Equal-size distinct cones cannot strictly contain each other.
            if !frontier
                .iter()
                .all(|d| self.cone[&d.id].len() == self.cone[&frontier[0].id].len())
            {
                let largest = frontier
                    .iter()
                    .max_by_key(|d| self.cone[&d.id].len())
                    .expect("nonempty frontier")
                    .id;
                let all_covered = frontier.iter().all(|d| {
                    #[cfg(test)]
                    FRONTIER_VISITS.with(|v| v.set(v.get() + 1));
                    self.cone[&largest].contains(&d.id)
                });
                if all_covered {
                    frontier.retain(|d| d.id == largest);
                } else {
                    let ancestors = frontier_ancestors(&frontier, &self.cone);
                    frontier.retain(|d| {
                        #[cfg(test)]
                        FRONTIER_VISITS.with(|v| v.set(v.get() + 1));
                        !ancestors.contains(&d.id)
                    });
                }
            }
            if frontier.is_empty() {
                break;
            }
            if frontier.len() > 1 && frontier.iter().any(|m| m.inputs.is_empty()) {
                let mut next_f = Vec::with_capacity(frontier.len());
                for m in frontier {
                    if m.inputs.is_empty() {
                        if expanded.insert(m.id) {
                            beside.push(m);
                        }
                    } else {
                        next_f.push(m);
                    }
                }
                frontier = next_f;
                continue;
            }
            if frontier.len() <= 1 {
                break;
            }
            let missing_roots: Vec<Formula> = frontier
                .iter()
                .filter(|d| !self.branch_roots.contains_key(&d.id))
                .map(|d| d.f.clone())
                .collect();
            if !missing_roots.is_empty() {
                return Local::Need(Need::RootsMany(missing_roots));
            }
            // Complexity tradeoff: all-pairs set intersection rescans each independent
            // cone F times. A reverse index from branch member to first frontier owner
            // marks all overlapping owners in one incidence pass, O(B+F) expected per step
            // for B terminal-root memberships, without enumerating pairs of owners.
            let mut owner: HashMap<Id, usize> = HashMap::new();
            let mut overlap_flags = vec![false; frontier.len()];
            for (i, d) in frontier.iter().enumerate() {
                for id in self.branch_roots[&d.id].iter() {
                    #[cfg(test)]
                    FRONTIER_VISITS.with(|v| v.set(v.get() + 1));
                    match owner.entry(*id) {
                        std::collections::hash_map::Entry::Vacant(e) => {
                            e.insert(i);
                        }
                        std::collections::hash_map::Entry::Occupied(e) => {
                            overlap_flags[i] = true;
                            overlap_flags[*e.get()] = true;
                        }
                    }
                }
            }
            let overlap: Vec<usize> = overlap_flags
                .into_iter()
                .enumerate()
                .filter_map(|(i, yes)| yes.then_some(i))
                .collect();
            if overlap.is_empty() {
                break;
            }
            let min_cone = overlap
                .iter()
                .map(|&i| self.cone[&frontier[i].id].len())
                .min()
                .expect("non-empty overlap");
            let to_expand: HashSet<Id> = overlap
                .into_iter()
                .map(|i| frontier[i].id)
                .filter(|id| self.cone[id].len() == min_cone)
                .collect();
            let mut next_f: Vec<Def> = Vec::new();
            let mut next_seen: HashSet<Id> = HashSet::new();
            for m in frontier {
                if to_expand.contains(&m.id) {
                    for &inp in &m.inputs {
                        let df = def(inp);
                        if free(&df) || own.contains(&Atom::Aux(inp)) {
                            continue;
                        }
                        let cid = Id::any(&df);
                        if Some(cid) == self_id || self.cyclic.contains(&cid) {
                            return Local::Unmade;
                        }
                        if expanded.contains(&cid) || !next_seen.insert(cid) {
                            continue;
                        }
                        let Some(child) = Def::of(df, def) else {
                            return Local::Unmade;
                        };
                        if !self.cone.contains_key(&child.id) {
                            return Local::Need(Need::Syms(child.f));
                        }
                        next_f.push(child);
                    }
                    if expanded.insert(m.id) {
                        beside.push(m);
                    }
                } else if next_seen.insert(m.id) {
                    next_f.push(m);
                }
            }
            frontier = next_f;
        }
        frontier.sort_by(|a, b| {
            self.cone[&a.id]
                .len()
                .cmp(&self.cone[&b.id].len())
                .then_with(|| self.syms[&a.id].cmp(&self.syms[&b.id]))
                .then_with(|| a.own.cmp(&b.own))
        });
        let mut full_keep: Vec<Atom> = keep.to_vec();
        if frontier.len() > 1 {
            let mut sym_sets: Vec<&Arc<imbl::OrdSet<Atom>>> =
                frontier.iter().map(|d| &self.syms[&d.id]).collect();
            sym_sets.sort_by_key(|s| std::cmp::Reverse(s.len()));
            let (big, rest) = sym_sets.split_first().expect("at least two");
            let mut rest_counts: BTreeMap<&Atom, usize> = BTreeMap::new();
            for s in rest {
                if Arc::ptr_eq(s, big) {
                    full_keep.extend(big.iter().cloned());
                } else {
                    for a in s.iter() {
                        *rest_counts.entry(a).or_default() += 1;
                    }
                }
            }
            for (a, c) in rest_counts {
                if c >= 2 || big.contains(a) {
                    full_keep.push(a.clone());
                }
            }
        }
        // Complexity tradeoff: calling key with all query/beside atoms for each of F
        // independent frontiers costs O(F*A) probes and produces only A kept atoms. Build
        // reverse cone/symbol ownership and distribute relevant atoms once. Work is the
        // memberships indexed plus candidate/kept incidences, not all pairs of frontiers.
        // Single-frontier calls keep the original path to avoid enumerating a long cone.
        let bucketed = if frontier.len() > 1 {
            let mut nodes: HashMap<Id, Vec<usize>> = HashMap::new();
            let mut syms: HashMap<Atom, Vec<usize>> = HashMap::new();
            for (i, d) in frontier.iter().enumerate() {
                for id in self.branch_roots[&d.id].iter() {
                    nodes.entry(*id).or_default().push(i);
                }
                for a in self.syms[&d.id].iter() {
                    syms.entry(a.clone()).or_default().push(i);
                }
            }
            let defined: HashSet<u32> = beside.iter().flat_map(|d| d.own.iter().copied()).collect();
            let owners = |a: &Atom| -> Vec<usize> {
                match a {
                    Atom::Aux(n) if defined.contains(n) || own.contains(a) => Vec::new(),
                    Atom::Aux(n) => {
                        let f = def(*n);
                        if free(&f) {
                            return syms.get(a).cloned().unwrap_or_default();
                        }
                        let id = Id::any(&f);
                        let mut candidates = BTreeSet::new();
                        if let Some(roots) = self.branch_roots.get(&id) {
                            if roots.is_empty() {
                                // Functional leaves have no branch root. Their symbols find
                                // possible owners; cone membership confirms each candidate.
                                if let Some(ss) = self.syms.get(&id) {
                                    for a in ss.iter() {
                                        if let Some(ids) = syms.get(a) {
                                            candidates.extend(ids);
                                        }
                                    }
                                }
                            } else {
                                for root in roots.iter() {
                                    if let Some(ids) = nodes.get(root) {
                                        candidates.extend(ids);
                                    }
                                }
                            }
                        }
                        candidates
                            .into_iter()
                            .filter(|&&i| self.cone[&frontier[i].id].contains(&id))
                            .copied()
                            .collect()
                    }
                    Atom::Sym(_) => syms.get(a).cloned().unwrap_or_default(),
                    Atom::Product(..) => Vec::new(),
                }
            };
            let mut buckets = vec![BTreeSet::new(); frontier.len()];
            let candidates: BTreeSet<&Atom> = full_keep
                .iter()
                .chain(reads)
                .chain(beside.iter().flat_map(|d| &d.reads))
                .collect();
            for a in candidates {
                let ids = match a {
                    Atom::Product(f, g) => {
                        let left = owners(&f.atom());
                        let right = owners(&g.atom());
                        let mut both = Vec::new();
                        let (mut i, mut j) = (0, 0);
                        while i < left.len() && j < right.len() {
                            match left[i].cmp(&right[j]) {
                                std::cmp::Ordering::Less => i += 1,
                                std::cmp::Ordering::Greater => j += 1,
                                std::cmp::Ordering::Equal => {
                                    both.push(left[i]);
                                    i += 1;
                                    j += 1;
                                }
                            }
                        }
                        both
                    }
                    _ => owners(a),
                };
                for i in ids {
                    buckets[i].insert(a.clone());
                }
            }
            Some(buckets)
        } else {
            None
        };
        let mut summaries: Vec<&'a Summary> = Vec::with_capacity(frontier.len());
        let mut missing = Vec::new();
        // Complexity tradeoff: returning the first missing summary repeated the entire
        // frontier construction F times (I30), O(F³) on a cold width-F fixed-depth DAG.
        // Collect all missing prerequisites in one plan and build them before retrying.
        // Two plans suffice on an acyclic ready frontier, plus the dependencies' own work.

        for (i, h) in frontier.iter().enumerate() {
            let key = match &bucketed {
                Some(bs) => self.key(h, &bs[i], own, &[], &[], def),
                None => self.key(h, reads, own, &full_keep, &beside, def),
            };
            let k = match key {
                Ok(k) => k,
                Err(n) => return Local::Need(n),
            };
            match self.by.get(&k) {
                None => missing.push((k, h.f.clone())),
                Some(None) => return Local::Unmade,
                Some(Some(s)) => summaries.push(s),
            }
        }
        if !missing.is_empty() {
            return Local::Need(Need::Summaries(missing));
        }
        Local::Ready(beside.into_iter().map(|d| d.f).collect(), summaries)
    }

    /// The key of the summary of `h`, read beside `reads` (whose own variables are `own`), the
    /// definitions `beside` and an outer key `keep`: the atoms of these that `h` or its cone
    /// hold, except those `own` and `beside` define (`Summaries::cone` and `Summaries::syms`).
    /// Where the key keeps a variable of a leaf definition in `h`'s cone (`x div 3`), the
    /// symbols of the cone and the first variable of that leaf definition join it.
    fn key(
        &self,
        h: &Def,
        reads: &BTreeSet<Atom>,
        own: &BTreeSet<Atom>,
        keep: &[Atom],
        beside: &[Def],
        def: &dyn Fn(u32) -> Formula,
    ) -> Result<Key, Need> {
        let (Some(syms), Some(cone)) = (self.syms.get(&h.id), self.cone.get(&h.id)) else {
            return Err(Need::Syms(h.f.clone()));
        };
        let defined: HashSet<u32> = beside.iter().flat_map(|d| d.own.iter().copied()).collect();
        let atoms = (keep.iter().chain(reads)).chain(beside.iter().flat_map(|d| &d.reads));
        let kept = |a: &Atom| match a {
            Atom::Aux(n) => {
                if defined.contains(n) || own.contains(a) {
                    return false;
                }
                if h.own.binary_search(n).is_ok() {
                    return true;
                }
                let dn = def(*n);
                if free(&dn) {
                    syms.contains(a)
                } else {
                    !h.inputs.is_empty() && cone.contains(&Id::any(&dn))
                }
            }
            Atom::Sym(_) => syms.contains(a),
            Atom::Product(..) => false,
        };
        let mut out: BTreeSet<Atom> = atoms
            .filter(|a| match a {
                // A product the cone may hold, one whose factors it may hold: the solver reads
                // it as an atom of its own, so a summary keeps it as it keeps a variable.
                Atom::Product(f, g) => kept(&f.atom()) && kept(&g.atom()),
                a => kept(a),
            })
            .cloned()
            .collect();
        let earlier: Vec<u32> = (out.iter())
            .filter_map(|a| match a {
                Atom::Aux(n) if h.own.binary_search(n).is_err() && !free(&def(*n)) => Some(*n),
                _ => None,
            })
            .collect();
        for n in earlier {
            if let Some(m) = Def::of(def(n), def)
                && m.inputs.is_empty()
            {
                out.extend(syms.iter().filter(|a| matches!(a, Atom::Sym(_))).cloned());
                out.insert(Atom::Aux(m.own[0]));
            }
        }
        Ok((h.id, out.into_iter().collect()))
    }

    /// Finds the symbols, cone and non-leaf cone of the definition `h`: those it reads and those
    /// of the definitions it reaches, each definition's found once and remembered, after its
    /// distinct inputs': an explicit stack, since the chain is as deep as the program. Each
    /// definition on the stack holds its distinct inputs (`seen_in`, LOAD-max-div-xr I24), read
    /// once, and the place of the next one to visit, so that every input is visited before the
    /// union is made (cross-review of LOAD-max-div-xr, round 2). A definition whose symbols are
    /// those of its largest input with none added shares its input's set. Time of the
    /// definitions and distinct inputs reached and of the persistent sets made.
    fn syms(&mut self, h: Formula, def: &dyn Fn(u32) -> Formula) {
        struct Frame {
            id: Id,
            atoms: Vec<Atom>,
            inputs: Vec<Formula>,
            func_leaf: bool,
            invalid: bool,
            next: usize,
        }
        let frame = |f: &Formula| {
            let id = Id::any(f);
            let parsed = Def::of(f.clone(), def);
            let func_leaf = parsed.as_ref().is_some_and(is_func_sym_leaf);
            let invalid = parsed.is_none();
            let atoms: Vec<Atom> = reads(f).into_iter().collect();
            // Complexity tradeoff: naive version collects every `Aux` input occurrence (`q` and
            // `r` of one division pair push the same `Formula` twice), revisiting shared inputs
            // and re-merging their `OrdSet`s in `sets`, O(n log^2 n) or worse on fresh-symbol
            // division chains (LOAD-max-div-xr I24). Used: deduplicate `inputs` per frame by
            // `seen_in`, O(d) per definition. Tradeoffs: one small `HashSet<Id>` per frame.
            let mut seen_in = HashSet::from([id]);
            let inputs: Vec<Formula> = (atoms.iter().flat_map(auxes))
                .map(def)
                .filter(|d| !free(d) && seen_in.insert(Id::any(d)))
                .collect();
            Frame {
                id,
                atoms,
                inputs,
                func_leaf,
                invalid,
                next: 0,
            }
        };
        let root_id = Id::any(&h);
        if self.cone.contains_key(&root_id) || self.cyclic.contains(&root_id) {
            return;
        }
        // The keys of the definitions on the stack: an input among them is on a cycle.
        let mut open: HashSet<Id> = HashSet::from([root_id]);
        let mut stack: Vec<Frame> = vec![frame(&h)];
        while let Some(top) = stack.last_mut() {
            // Complexity tradeoff: searching the inputs from the first at each return to a
            // definition costs O(d^2) for d inputs; the place kept in the frame visits each
            // input once, O(d).
            let child = loop {
                let Some(d) = top.inputs.get(top.next) else {
                    break None;
                };
                top.next += 1;
                let k = Id::any(d);
                if !self.cone.contains_key(&k) && !self.cyclic.contains(&k) && !open.contains(&k) {
                    break Some(d.clone());
                }
            };
            if let Some(d) = child {
                open.insert(Id::any(&d));
                stack.push(frame(&d));
                continue;
            }
            let Some(top) = stack.pop() else { break };
            open.remove(&top.id);
            if top.invalid
                || top.inputs.iter().any(|d| {
                    let k = Id::any(d);
                    open.contains(&k) || self.cyclic.contains(&k) || !self.cone.contains_key(&k)
                })
            {
                self.cyclic.insert(top.id);
                continue;
            }
            let mut sets: Vec<&Arc<imbl::OrdSet<Atom>>> = (top.inputs.iter())
                .filter_map(|d| self.syms.get(&Id::any(d)))
                .collect();
            sets.sort_by_key(|s| std::cmp::Reverse(s.len()));
            let mine: Vec<Atom> = top
                .atoms
                .iter()
                .filter(|a| match a {
                    Atom::Sym(_) => true,
                    Atom::Aux(n) => free(&def(*n)),
                    Atom::Product(..) => false,
                })
                .cloned()
                .collect();
            // Complexity tradeoff: scanning/reinserting every smaller input set is O(n²)
            // over n diamonds whose two distinct branches add one symbol to a shared prefix
            // (R5-C36, beyond I24's duplicate-Id case). A persistent-tree diff skips shared
            // nodes and inserts only additions, O(U + D log n) for U unshared tree contents
            // and D new entries; on that diamond chain O(n log n), with persistent storage.
            // Arbitrary unrelated input sets may still have U equal to their full sizes.
            let set = shared_set_union(sets, mine);
            let cones: Vec<&Arc<imbl::OrdSet<Id>>> = (top.inputs.iter())
                .filter_map(|d| self.cone.get(&Id::any(d)))
                .collect();
            // Complexity tradeoff: the cone unions had the same smaller-set rescan as
            // symbols. Ordered persistent sets support structural diffs as well; Id order
            // is used only inside membership metadata, never to select a definition.
            let cone = shared_set_union(cones, [top.id]);
            let branch_cone = if top.func_leaf {
                Arc::new(imbl::OrdSet::new())
            } else {
                let bsets: Vec<&Arc<imbl::OrdSet<Id>>> = (top.inputs.iter())
                    .filter_map(|d| self.branch_cone.get(&Id::any(d)))
                    .collect();
                shared_set_union(bsets, [top.id])
            };
            self.syms.insert(top.id, set);
            self.cone.insert(top.id, cone);
            self.branch_cone.insert(top.id, branch_cone);
        }
    }
    // Complexity tradeoff: eagerly storing root metadata for every definition adds work to
    // single-frontier abs/two-link chains that never intersect cones. Request it only after
    // containment/leaf peeling leaves several non-leaf frontiers. An explicit postorder stack
    // visits each distinct needed definition once; unions use shared_set_union's bound.
    fn roots(&mut self, h: Formula, def: &dyn Fn(u32) -> Formula) {
        let mut stack = vec![(h, false)];
        while let Some((f, exit)) = stack.pop() {
            let id = Id::any(&f);
            if self.branch_roots.contains_key(&id) {
                continue;
            }
            let Some(d) = Def::of(f.clone(), def) else {
                continue;
            };
            if is_func_sym_leaf(&d) {
                self.branch_roots.insert(id, Arc::new(imbl::OrdSet::new()));
                continue;
            }
            let mut seen = HashSet::new();
            let inputs: Vec<Formula> = d
                .inputs
                .iter()
                .map(|&n| def(n))
                .filter(|f| seen.insert(Id::any(f)))
                .collect();
            if !exit {
                stack.push((f, true));
                for g in inputs.into_iter().rev() {
                    if !self.branch_roots.contains_key(&Id::any(&g)) {
                        stack.push((g, false));
                    }
                }
            } else {
                let parents = inputs
                    .iter()
                    .map(|g| &self.branch_roots[&Id::any(g)])
                    .collect();
                let mut roots = shared_set_union(parents, std::iter::empty());
                if roots.is_empty() {
                    roots = Arc::new(imbl::OrdSet::unit(id));
                }
                self.branch_roots.insert(id, roots);
            }
        }
    }
}

/// Union persistent sets using exact directed differences from the largest input.
// Complexity tradeoff: iterating every smaller set costs O(S log V) even where its S
// entries are shared through a fork (R5-C36). Symmetric diff alone instead visits O(V)
// removals per singleton beside a large set, quadratic over a wide join. Advance the
// direct-membership and structural-diff iterators together until one finite iterator is
// exhausted. Cost includes O(d log d) ordering of d inputs, O(K log V) checks of K
// local additions, membership probes and unshared diff nodes visited, followed by
// O(D log V) insertions of additions; neither removal-only outputs nor shared prefixes
// force a full scan. On diamonds and a large set beside singleton inputs, O(log V) per
// input/local addition. Unrelated, unshared sets can still cost their full contents.
// Tradeoffs: two transient addition vectors. The exit is iterator completion, never a
// size switch or solver-work budget; both complete iterators compute identical additions.
fn shared_set_union<T: Ord + Clone>(
    mut sets: Vec<&Arc<imbl::OrdSet<T>>>,
    mine: impl IntoIterator<Item = T>,
) -> Arc<imbl::OrdSet<T>> {
    sets.sort_by_key(|s| std::cmp::Reverse(s.len()));
    let Some((big, rest)) = sets.split_first() else {
        return Arc::new(mine.into_iter().collect());
    };
    let mut added: Vec<T> = mine.into_iter().filter(|x| !big.contains(x)).collect();
    for s in rest {
        if Arc::ptr_eq(big, s) {
            continue;
        }
        // Both finite iterators compute s\big exactly. Structural diff skips common
        // subtrees; direct membership avoids enumerating big\s when s is tiny. Advance
        // each until either finishes, using that complete result. No count/size threshold,
        // proof budget or approximation: the two results are the same directed difference.
        let mut scan = s.iter();
        let mut diff = big.diff(s);
        let (mut from_scan, mut from_diff) = (Vec::new(), Vec::new());
        loop {
            let Some(x) = scan.next() else {
                added.extend(from_scan);
                break;
            };
            if !big.contains(x) {
                from_scan.push(x.clone());
            }
            match diff.next() {
                None => {
                    added.extend(from_diff);
                    break;
                }
                Some(imbl::ordset::DiffItem::Add(x)) => from_diff.push(x.clone()),
                Some(imbl::ordset::DiffItem::Remove(_)) => {}
            }
        }
    }
    if added.is_empty() {
        return Arc::clone(big);
    }
    let mut out = (***big).clone();
    for x in added {
        out.insert(x);
    }
    Arc::new(out)
}

/// Members contained by another frontier: union all cones after removing their own Ids.
// Complexity tradeoff: all F² frontier pairs test membership even when many cones share
// a long prefix. Persistent removal copies O(log V) tree paths per frontier; the exact
// directed union shares common subtrees. Cost O(F log V) plus directed-union work; it can
// still visit large unshared contents, but does not enumerate frontier pairs.
fn frontier_ancestors(
    frontier: &[Def],
    cones: &HashMap<Id, Arc<imbl::OrdSet<Id>>>,
) -> Arc<imbl::OrdSet<Id>> {
    let sets: Vec<Arc<imbl::OrdSet<Id>>> = frontier
        .iter()
        .map(|d| {
            let mut c = (*cones[&d.id]).clone();
            c.remove(&d.id);
            Arc::new(c)
        })
        .collect();
    shared_set_union(sets.iter().collect(), std::iter::empty())
}

impl Summary {
    /// The summary as one formula: the disjunction of its pieces.
    fn rows(&self) -> Formula {
        let and = |p: &Vec<Con>| Formula::and(p.iter().cloned().map(Formula::Con).collect());
        Formula::or(self.pieces.iter().map(and).collect())
    }
}

/// A definition as the summaries read it: its formula and key, the variables it defines in
/// order, the variables of other definitions it reads, and every atom it reads.
struct Def {
    f: Formula,
    id: Id,
    own: Vec<u32>,
    inputs: Vec<u32>,
    reads: BTreeSet<Atom>,
}

impl Def {
    /// The definition `f`, `None` where no summary is made of it: one that defines no variable it
    /// reads. A product of variables is read as an atom of its own, as the solver reads it
    /// ([`decide`]), and the definitions of its factors as inputs. Time of `f`.
    fn of(f: Formula, def: &dyn Fn(u32) -> Formula) -> Option<Def> {
        let id = Id::any(&f);
        let reads = reads(&f);
        let (mut own, mut inputs) = (Vec::new(), Vec::new());
        for a in &reads {
            match a {
                Atom::Product(..) | Atom::Sym(_) => {}
                Atom::Aux(n) => {
                    let d = def(*n);
                    if Id::any(&d) == id {
                        own.push(*n);
                    } else if !free(&d) {
                        inputs.push(*n);
                    }
                }
            }
        }
        (!own.is_empty()).then_some(Def {
            f,
            id,
            own,
            inputs,
            reads,
        })
    }
}

/// Whether `d` is a single-valued symbol leaf: `d` reads no other definition or product, and
/// defines either one variable by a unit linear equation `v == e(syms)` or a Euclidean quotient
/// and remainder `e(syms) == m * q + r, 0 <= r <= m - 1`. Such variables are uniquely determined
/// by the symbols at every integer assignment, so two chains sharing `d` may summarize their cones
/// apart once their shared symbols are kept.
fn is_func_sym_leaf(d: &Def) -> bool {
    if !d.inputs.is_empty()
        || d.reads.iter().any(|a| match a {
            Atom::Sym(_) => false,
            Atom::Aux(n) => d.own.binary_search(n).is_err(),
            Atom::Product(..) => true,
        })
    {
        return false;
    }
    let Some(cs) = cases(&d.f) else {
        return false;
    };
    let [rows] = cs.as_slice() else {
        return false;
    };
    match d.own.as_slice() {
        [v] => {
            rows.len() == 1
                && rows[0].rel == Rel::Eq
                && rows[0]
                    .lin
                    .terms
                    .get(&Atom::Aux(*v))
                    .is_some_and(Int::is_unit)
        }
        [u, w] => {
            rows.len() == 3
                && [(*u, *w), (*w, *u)].into_iter().any(|(q, _)| {
                    let qa = Atom::Aux(q);
                    let rp = remainders_as_pairs(rows, &|a| *a == qa);
                    rp.len() == 2 && pairs(&rp).iter().any(|(_, v, _, _)| *v == qa)
                })
        }
        _ => false,
    }
}

type Terms = BTreeMap<Atom, Int>;
type LineGroup = (Atom, Terms, bool);

/// The lines `e * y >= m * f + b` of `rows` by `(y, f, lower)`, the explicit 1-form bounds
/// `[lo, hi]` on each primitive form `f`, and whether those bounds are consistent. The groups
/// and form bounds are ordered by key, so that [`lean`] and [`quotient_offsets`] read them in
/// one order on every run.
// Complexity tradeoff: naive version, the groups in a hash map, O(t) a row, whose order of
// iteration changes from run to run, so the rows `lean` keeps, and the summary's key and cost,
// could too (LOAD-max-div-xr I23). Used: ordered maps, O(t log g) a row for g groups, O(r t
// log r) in all. Tradeoffs: a log factor on the grouping.
fn group_lines(
    rows: &[Con],
) -> (
    BTreeMap<LineGroup, Vec<(Int, Int, usize)>>,
    BTreeMap<Terms, (Option<Int>, Option<Int>)>,
    bool,
) {
    let mut groups: BTreeMap<LineGroup, Vec<(Int, Int, usize)>> = BTreeMap::new();
    let mut bounds: BTreeMap<Terms, (Option<Int>, Option<Int>)> = BTreeMap::new();
    let mut ok = true;
    let tighten = |b: &mut (Option<Int>, Option<Int>), lo: Option<Int>, hi: Option<Int>| {
        if let Some(l) = lo {
            b.0 = Some(b.0.take().map_or(l.clone(), |o| o.max(l)));
        }
        if let Some(h) = hi {
            b.1 = Some(b.1.take().map_or(h.clone(), |o| o.min(h)));
        }
    };
    for (i, r) in rows.iter().enumerate() {
        if r.lin.terms.is_empty() {
            continue;
        }
        let g = r.lin.terms.values().fold(Int::ZERO, |g, k| g.gcd(k));
        let neg = r.lin.terms.values().next().is_some_and(Int::is_negative);
        let signed = if neg { -&g } else { g.clone() };
        let t: Terms = (r.lin.terms.iter())
            .map(|(a, k)| (a.clone(), k.div_floor(&signed)))
            .collect();
        let c = &r.lin.constant;
        match (r.rel, neg) {
            (Rel::Ge, false) => {
                tighten(bounds.entry(t).or_default(), Some(-&c.div_floor(&g)), None)
            }
            (Rel::Ge, true) => tighten(bounds.entry(t).or_default(), None, Some(c.div_floor(&g))),
            (Rel::Eq, _) if c.mod_floor(&g).is_zero() => {
                let v = -&c.div_floor(&signed);
                tighten(bounds.entry(t).or_default(), Some(v.clone()), Some(v));
            }
            (Rel::Eq, _) => ok = false,
        }
        if r.rel != Rel::Ge || r.lin.terms.len() < 2 {
            continue;
        }
        let Some((y, e)) = r.lin.terms.iter().find(|(_, k)| k.is_unit()) else {
            continue;
        };
        let g = (r.lin.terms.iter())
            .filter(|(a, _)| *a != y)
            .fold(Int::ZERO, |g, (_, k)| g.gcd(k));
        let first = r
            .lin
            .terms
            .iter()
            .find(|(a, _)| *a != y)
            .map(|(_, k)| k.is_negative());
        let g = if first == Some(true) { -&g } else { g };
        let f: Terms = (r.lin.terms.iter())
            .filter(|(a, _)| *a != y)
            .map(|(a, k)| (a.clone(), k.div_floor(&g)))
            .collect();
        let lower = e.is_positive();
        groups
            .entry((y.clone(), f, lower))
            .or_default()
            .push((-&g, -c, i));
    }
    for lines in groups.values_mut() {
        lines.sort();
    }
    if (bounds.values()).any(|(lo, hi)| matches!((lo, hi), (Some(l), Some(h)) if l > h)) {
        ok = false;
    }
    (groups, bounds, ok)
}

/// The indices of the rows of each group's upper hull in `groups`.
fn hull_of(
    lines: &[(Int, Int, usize)],
    bounds: Option<&(Option<Int>, Option<Int>)>,
) -> (Vec<usize>, HashSet<usize>) {
    let mut drop: HashSet<usize> = HashSet::new();
    let mut hull: Vec<usize> = Vec::new();
    for j in 0..lines.len() {
        // Of one slope the highest, the last, holds the others.
        if j + 1 < lines.len() && lines[j + 1].0 == lines[j].0 {
            drop.insert(lines[j].2);
            continue;
        }
        while let [.., p, q] = hull[..] {
            let ((ma, ba, _), (mb, bb, _), (mc, bc, _)) = (&lines[p], &lines[q], &lines[j]);
            // Slopes ma < mb < mc: line b is under max(a, c) everywhere when at the
            // crossing of a and c, t = (ba - bc) / (mc - ma), it is under a.
            if &(mb - ma) * &(ba - bc) <= &(ba - bb) * &(mc - ma) {
                drop.insert(lines[q].2);
                hull.pop();
            } else {
                break;
            }
        }
        hull.push(j);
    }
    if let Some((lo, hi)) = bounds {
        if let Some(u) = hi {
            while let [.., p, q] = hull[..] {
                let ((ma, ba, _), (mb, bb, _)) = (&lines[p], &lines[q]);
                if &(mb - ma) * u <= (ba - bb) {
                    drop.insert(lines[q].2);
                    hull.pop();
                } else {
                    break;
                }
            }
        }
        if let Some(l) = lo {
            // Complexity tradeoff: naive version, `hull.remove(0)` for each line dropped from
            // the front, O(h) each and O(h²) over the sweep. Used: a start index advanced, the
            // dropped front drained once, O(h). Tradeoffs: none.
            let mut s = 0;
            while let [p, q, ..] = hull[s..] {
                let ((ma, ba, _), (mb, bb, _)) = (&lines[p], &lines[q]);
                if &(mb - ma) * l >= (ba - bb) {
                    drop.insert(lines[p].2);
                    s += 1;
                } else {
                    break;
                }
            }
            hull.drain(..s);
        }
    }
    (hull, drop)
}

/// `rows` without the inequalities that bound one atom `y` (coefficient 1 or -1, the first such
/// in the row) by a multiple of one form `f` of the other atoms (the row's other terms over
/// their greatest common divisor, the first coefficient positive), and that lie on no open part
/// of the envelope of the others of their group (`y`, `f`, lower or upper) within the 1-form
/// bounds `[lo, hi]` on `f`: `y >= m * f + b` read as a line in `f`. Such a row holds wherever
/// the lines kept and the bounds on `f` do, over the reals and so over the integers, whatever
/// values `f` and the rest take. Of lines of one slope the highest alone is kept.
/// `x >= 2^k * (q3 + q4) - 9 * 2^k` for k = 1 to 7 (the bounds of
/// `max(H div 2, x mod 5 + x div 7 - 9)` after k halvings) leave k = 1 and 7, and only k = 1
/// once `q3 + q4 <= 9` is in `rows`.
// Complexity tradeoff: naive version, each row tried against the others by [`decide`] as
// [`lean`] does, one decision for each row, and refused here. Used: the rows grouped by key,
// each group sorted by slope and swept once keeping the upper hull over the interval `[lo, hi]`
// of 1-form bounds on `f`, O(r log r) for r rows of t terms each, O(r t) for
// the forms. Tradeoffs: a row implied by rows of other groups, or by several forms together, is
// left to [`lean`]'s decisions.
fn envelope(rows: Vec<Con>) -> Vec<Con> {
    let (groups, bounds, _) = group_lines(&rows);
    let mut drop: HashSet<usize> = HashSet::new();
    for ((_, f, _), lines) in groups {
        let (_, d) = hull_of(&lines, bounds.get(&f));
        drop.extend(d);
    }
    (rows.into_iter().enumerate())
        .filter(|(i, _)| !drop.contains(i))
        .map(|(_, r)| r)
        .collect()
}

/// Every atom that occurs as a factor of an [`Atom::Product`] in `rows`: dropping or folding a
/// linear row that constrains such an atom while leaving its product in `rows` would unconstrain
/// the factor inside the product.
fn product_factors(rows: &[Con]) -> HashSet<Atom> {
    let mut out = HashSet::new();
    for r in rows {
        for a in r.lin.terms.keys() {
            if let Atom::Product(x, y) = a {
                out.insert(x.atom());
                out.insert(y.atom());
            }
        }
    }
    out
}

/// `rows` without division pairs `(m, v, i, j)` of `elim` whose quotient `v` occurs in no other
/// row or product: `0 <= e - m * v <= m - 1` holds for `v == e div m` at every integer point of
/// the other atoms, so dropping the pair preserves integer satisfiability.
// Complexity tradeoff: naive version, rescan `rows` and `pairs` in a loop until no free pair
// remains, O(p r t). Used: a worklist queue of quotients whose occurrence count reaches 2,
// decrementing the counts of the dividend's atoms as each pair is dropped, O(r t),
// plus O(r log r) row comparisons for the sort and deduplication. Tradeoffs:
// a hash map of atom counts and an ordered map of pairs.
fn without_free_pairs_for(mut rows: Vec<Con>, elim: &dyn Fn(&Atom) -> bool) -> Vec<Con> {
    rows.sort();
    rows.dedup();
    let factors = product_factors(&rows);
    let mut count: HashMap<Atom, usize> = HashMap::new();
    for r in &rows {
        for a in r.lin.terms.keys() {
            *count.entry(a.clone()).or_default() += 1;
        }
    }
    let mut pair_of: BTreeMap<Atom, (usize, usize)> = BTreeMap::new();
    for (_, v, i, j) in pairs(&rows) {
        if elim(&v) && !factors.contains(&v) {
            pair_of.entry(v).or_insert((i, j));
        }
    }
    let mut queue: Vec<Atom> = (pair_of.keys())
        .filter(|v| count.get(*v) == Some(&2))
        .cloned()
        .collect();
    let mut drop: HashSet<usize> = HashSet::new();
    while let Some(v) = queue.pop() {
        let Some(&(i, j)) = pair_of.get(&v) else {
            continue;
        };
        if drop.contains(&i) || drop.contains(&j) {
            continue;
        }
        drop.insert(i);
        drop.insert(j);
        for r in [&rows[i], &rows[j]] {
            for a in r.lin.terms.keys() {
                if let Some(c) = count.get_mut(a) {
                    *c -= 1;
                    if *c == 2 && pair_of.contains_key(a) {
                        queue.push(a.clone());
                    }
                }
            }
        }
    }
    (rows.into_iter().enumerate())
        .filter(|(i, _)| !drop.contains(i))
        .map(|(_, r)| r)
        .collect()
}

#[cfg(test)]
thread_local! {
    /// Entries of occurrence lists read by [`without_free_pairs`] (tests of its cost only).
    static OCCURRENCE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Rows read to make the rests of the forms of a piece in [`merge_pieces`] (tests of its
    /// cost only).
    static FRONTIER_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static FOLD_ROW_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static REST_ROW_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `rows` with division pairs `(m, v, i, j)` outside `factors` whose quotient `v` occurs in every
/// other row only as an inequality (`Rel::Ge`) with coefficient 1 or -1 folded into those
/// inequalities and dropped, repeated until none applies. Substituting `v = e div m` into
/// `v >= L` (`e >= m * L`) and `v <= U` (`e <= m * U + m - 1`) is exact over the integers, and
/// leaves `v` in `(i, j)` alone, where `v = e div m` witnesses every integer point of the rest.
/// A quotient with any non-unit or equality occurrence (`q5` in `x >= 2^k * (q5 + q7) - 9 * 2^k`
/// beside `q5 + q7 <= 9`) is left untouched so 1-form bounds on kept quotients stay intact.
// Complexity tradeoff: naive version, leave non-free auxiliary quotients (`q_H = h_{k-1} div 2`
// and `h_{k-1} = x div 2^{k-1}`) in `decide_cons`, hiding the upper ray `x <= 2^k * (r5 + q7) -
// (9 * 2^k + 1)` from the two-pointer hull check and sending every candidate piece of `max(H div
// 2, x mod 5 + x div 7 - 9)` into `Omega::run` and `live3` over k-bit coefficients (55.6% of
// cycles at 320 links). Used: peel free pairs first (`without_free_pairs_for`), then fold only
// division pairs whose remaining occurrences are all unit `Rel::Ge` rows and drop the folded
// pair, O(r t + w t) term visits for w rewrites per pass over at most p <= r / 2 passes (at most
// 2 passes per chain link). Tradeoffs: quotients with wide coefficients or equations are left to
// `decide`.
fn fold_free_unit_pairs(mut rows: Vec<Con>, factors: &HashSet<Atom>) -> Vec<Con> {
    loop {
        #[cfg(test)]
        FOLD_ROW_VISITS.with(|v| v.set(v.get() + rows.len()));
        rows = without_free_pairs_for(rows, &|_| true);
        let mut pairs = pairs(&rows);
        pairs.retain(|(_, v, _, _)| !factors.contains(v));
        if pairs.is_empty() {
            return rows;
        }
        pairs.sort();
        let mut at: HashMap<Atom, Vec<usize>> = HashMap::new();
        for (n, r) in rows.iter().enumerate() {
            for a in r.lin.terms.keys() {
                at.entry(a.clone()).or_default().push(n);
            }
        }
        let mut done: HashSet<Atom> = HashSet::new();
        let mut dropped: HashSet<usize> = HashSet::new();
        for (m, v, i, j) in pairs {
            if dropped.contains(&i) || dropped.contains(&j) || !done.insert(v.clone()) {
                continue;
            }
            let (a, b) = (rows[i].clone(), rows[j].clone());
            if a.lin.terms.get(&v) != Some(&-&m)
                || b.lin.terms.get(&v) != Some(&m)
                || a.lin.plus(&b.lin) != Lin::constant(&m - &Int::ONE)
            {
                continue;
            }
            let mut holders = at.remove(&v).unwrap_or_default();
            holders.sort_unstable();
            holders.dedup();
            holders.retain(|&n| {
                n != i && n != j && !dropped.contains(&n) && rows[n].lin.terms.contains_key(&v)
            });
            if holders.is_empty()
                || !holders
                    .iter()
                    .all(|&n| rows[n].rel == Rel::Ge && rows[n].lin.terms[&v].is_unit())
            {
                continue;
            }
            for n in holders {
                let r = &mut rows[n];
                let side = if r.lin.terms.get(&v) == Some(&Int::ONE) {
                    &a
                } else {
                    &b
                };
                let lin = r.lin.times(m.clone()).plus(&side.lin);
                let g = lin.terms.values().fold(Int::ZERO, |g, c| g.gcd(c));
                r.lin = if g.is_zero() || g == Int::ONE {
                    lin
                } else {
                    Lin {
                        terms: (lin.terms.iter())
                            .map(|(k, c)| (k.clone(), c.div_floor(&g)))
                            .collect(),
                        constant: lin.constant.div_floor(&g),
                    }
                };
                for t in r.lin.terms.keys() {
                    at.entry(t.clone()).or_default().push(n);
                }
            }
            dropped.insert(i);
            dropped.insert(j);
        }
        if dropped.is_empty() {
            return rows;
        }
        rows = (rows.into_iter().enumerate())
            .filter(|(n, _)| !dropped.contains(n))
            .map(|(_, r)| r)
            .collect();
    }
}

/// `rows` simplified preserving integer satisfiability: remainders converted to division pairs,
/// equations with a single-use unit variable dropped, and free or unit-bounded division pairs
/// peeled.
// Complexity tradeoff: naive version, pass all definition rows to [`decide`], which eliminates
// auxiliary quotients and remainders alongside big-integer bounds in `live3`. Used: peel
// single-use unit equations by queue, with the rows left that use each atom counted down as
// rows are dropped, and run [`fold_free_unit_pairs`], O(r t) plus O(r log r) row comparisons
// for its sort and any unit-pair folds. Counting the uses left by a scan of the atom's
// occurrence list after each drop costs O(r²) on `y_i == x` (cross-review of LOAD-max-div-xr,
// round 3, Codex). Tradeoffs: maps of occurrences and counts.
fn without_free_pairs(rows: Vec<Con>) -> Vec<Con> {
    let mut rows = remainders_as_pairs(&rows, &|_| false);
    let factors = product_factors(&rows);
    let mut at: BTreeMap<Atom, Vec<usize>> = BTreeMap::new();
    for (i, r) in rows.iter().enumerate() {
        for a in r.lin.terms.keys() {
            at.entry(a.clone()).or_default().push(i);
        }
    }
    // The rows not dropped that use each atom.
    let mut left: HashMap<Atom, usize> = (at.iter()).map(|(a, ns)| (a.clone(), ns.len())).collect();
    let mut queue: Vec<Atom> = (at.iter())
        .filter_map(|(a, ns)| {
            (ns.len() == 1 && !matches!(a, Atom::Product(..)) && !factors.contains(a))
                .then_some(a.clone())
        })
        .collect();
    let mut drop: HashSet<usize> = HashSet::new();
    while let Some(a) = queue.pop() {
        let Some(&i) = at
            .get(&a)
            .and_then(|ns| ns.iter().find(|&&i| !drop.contains(&i)))
        else {
            continue;
        };
        if rows[i].rel != Rel::Eq || !rows[i].lin.terms.get(&a).is_some_and(Int::is_unit) {
            continue;
        }
        drop.insert(i);
        for b in rows[i].lin.terms.keys() {
            #[cfg(test)]
            OCCURRENCE_VISITS.with(|v| v.set(v.get() + 1));
            if let Some(n) = left.get_mut(b) {
                *n -= 1;
                if *n == 1 && !matches!(b, Atom::Product(..)) && !factors.contains(b) {
                    queue.push(b.clone());
                }
            }
        }
    }
    rows = (rows.into_iter().enumerate())
        .filter(|(i, _)| !drop.contains(i))
        .map(|(_, r)| r)
        .collect();
    fold_free_unit_pairs(rows, &factors)
}

/// Whether the conjunction of `rows` has an integer point: `Ok(false)` when two bounds on a
/// form contradict each other ([`group_lines`]), and otherwise [`decide`] of `rows` without its
/// free division pairs ([`without_free_pairs`]).
// Complexity tradeoff: naive version, [`decide`] of `rows` as written, whose elimination meets
// each free division pair's quotient (multiplying rows by its modulus) and may refuse where the
// bounds of one form already contradict. Used: free pairs dropped (O(r t)), [`envelope`], and
// the lower and upper hulls of each `(y, f)` merged by two pointers to find an empty interval
// of `f` (O(r log r)), before one [`decide`] of what is left. Tradeoffs: a contradiction among
// several forms is left to [`decide`]; the answer is that of the rows, since a free pair holds
// for any value of the rest and the hull bounds are implied by the rows.
fn decide_cons(rows: Vec<Con>) -> Result<bool, Refusal> {
    let rows = envelope(without_free_pairs(rows));
    let (groups, bounds, ok) = group_lines(&rows);
    if !ok {
        return Ok(false);
    }
    for ((y, f, lower), lo_lines) in &groups {
        if !*lower {
            continue;
        }
        let Some(hi_lines) = groups.get(&(y.clone(), f.clone(), false)) else {
            continue;
        };
        let (h1, _) = hull_of(lo_lines, bounds.get(f));
        let (h2, _) = hull_of(hi_lines, bounds.get(f));
        let (mut lo, mut hi) = bounds.get(f).cloned().unwrap_or((None, None));
        let (mut i, mut j) = (0, 0);
        while i < h1.len() && j < h2.len() {
            let ((m1, b1, _), (m2, b2, _)) = (&lo_lines[h1[i]], &hi_lines[h2[j]]);
            let m = m1 + m2;
            let rhs = -&(b1 + b2);
            if m.is_positive() {
                let u = rhs.div_floor(&m);
                hi = Some(hi.take().map_or(u.clone(), |o| o.min(u)));
            } else if m.is_negative() {
                let l = -&rhs.div_floor(&-&m);
                lo = Some(lo.take().map_or(l.clone(), |o| o.max(l)));
            } else if rhs.is_negative() {
                return Ok(false);
            }
            if matches!((&lo, &hi), (Some(l), Some(h)) if l > h) {
                return Ok(false);
            }
            if i + 1 == h1.len() {
                j += 1;
            } else if j + 1 == h2.len() {
                i += 1;
            } else {
                let (ma1, ba1, _) = &lo_lines[h1[i + 1]];
                let (ma2, ba2, _) = &hi_lines[h2[j + 1]];
                if &(b1 - ba1) * &(ma2 - m2) <= &(b2 - ba2) * &(ma1 - m1) {
                    i += 1;
                } else {
                    j += 1;
                }
            }
        }
    }
    decide(&Formula::and(rows.into_iter().map(Formula::Con).collect()))
}

/// `rows` without each row the others imply over the integers, each tried in turn against
/// those left: [`decide_cons`] shows the others and the row's negation have no point, after
/// [`envelope`] and capping the steepest ray of any multi-line group by a 1-form bound on `f`
/// where the piece has no integer point beyond the crossing. A row whose question is refused is
/// kept, and rows of a free division pair are kept without a decision. Time of one decision of
/// the rows for each non-free row and each multi-line group, after [`envelope`].
fn lean(rows: Vec<Con>) -> Vec<Con> {
    let mut rows = envelope(rows);
    let (groups, bounds, _) = group_lines(&rows);
    let mut changed = false;
    for ((_, f, lower), lines) in groups {
        if !lower || f.len() < 2 {
            continue;
        }
        let (hull, _) = hull_of(&lines, bounds.get(&f));
        let [first, .., last] = hull[..] else {
            continue;
        };
        let ((m1, b1, _), (ms, bs, is)) = (&lines[first], &lines[last]);
        if !m1.is_positive() {
            continue;
        }
        let f_lin = Lin {
            terms: f,
            constant: Int::ZERO,
        };
        // Line `last` is above line `first` only where `f >= c + 1`, for
        // `c = floor((b1 - bs) / (ms - m1))`. Where the piece has no point there, `f <= c`
        // holds on the piece and with line `first` implies line `last`.
        let c = (b1 - bs).div_floor(&(ms - m1));
        let mut above = rows.clone();
        above.push(Con::ge(&f_lin, &Lin::constant(&c + &Int::ONE)));
        if decide_cons(above) == Ok(false) {
            rows[*is] = Con::ge(&Lin::constant(c), &f_lin);
            changed = true;
        }
    }
    if changed {
        rows.sort();
        rows.dedup();
        rows = envelope(rows);
    }
    let mut free_rows: HashSet<Con> = HashSet::new();
    if rows.len() > 2 && decide_cons(rows.clone()) == Ok(true) {
        let mut count: HashMap<&Atom, usize> = HashMap::new();
        for r in &rows {
            for a in r.lin.terms.keys() {
                *count.entry(a).or_default() += 1;
            }
        }
        for (_, v, i, j) in pairs(&rows) {
            if count.get(&v) == Some(&2) {
                free_rows.insert(rows[i].clone());
                free_rows.insert(rows[j].clone());
            }
        }
    }
    let mut i = 0;
    while i < rows.len() {
        if free_rows.contains(&rows[i]) {
            i += 1;
            continue;
        }
        let mut others: Vec<Con> = (rows.iter().enumerate())
            .filter(|&(j, _)| j != i)
            .map(|(_, c)| c.clone())
            .collect();
        let implied = match rows[i].rel {
            Rel::Ge => {
                others.push(Con::ge(&Lin::constant(-1), &rows[i].lin));
                decide_cons(others) == Ok(false)
            }
            Rel::Eq => {
                let others = without_free_pairs(others);
                let not = Formula::negate(Formula::Con(rows[i].clone()));
                let f = Formula::and(others.into_iter().map(Formula::Con).chain([not]).collect());
                decide(&f) == Ok(false)
            }
        };
        if implied {
            rows.swap_remove(i);
        } else {
            i += 1;
        }
    }
    rows
}

/// The division pairs of `rows`: rows `i` and `j`, `e - m * v >= 0` and `m * v + m - 1 - e >=
/// 0` for an atom `v` (no product), whose terms are opposite and whose constants add to `m -
/// 1`, and which hold together exactly where `v == e div m`; each as `(m, v, i, j)`. Time of
/// the rows' terms, each row's looked up by hash.
fn pairs(rows: &[Con]) -> Vec<(Int, Atom, usize, usize)> {
    let mut by_terms: HashMap<&BTreeMap<Atom, Int>, usize> = HashMap::new();
    for (i, r) in rows.iter().enumerate() {
        if r.rel == Rel::Ge {
            by_terms.entry(&r.lin.terms).or_insert(i);
        }
    }
    let mut out = Vec::new();
    for (i, a) in rows.iter().enumerate() {
        if a.rel != Rel::Ge {
            continue;
        }
        let neg: BTreeMap<Atom, Int> = a.lin.terms.iter().map(|(k, c)| (k.clone(), -c)).collect();
        let Some(&j) = by_terms.get(&neg) else {
            continue;
        };
        let k = &a.lin.constant + &rows[j].lin.constant;
        if k.is_negative() {
            continue;
        }
        let m = &k + &Int::ONE;
        for (v, c) in &a.lin.terms {
            if *c == -&m && !matches!(v, Atom::Product(..)) {
                out.push((m.clone(), v.clone(), i, j));
            }
        }
    }
    out
}

/// `rows` read through their division pairs ([`pairs`]) of the atoms `elim` names: for a pair
/// `v == e div m`, each other inequality holding `v` with coefficient 1 is combined with the
/// pair's first row into one without `v` (`v >= L` into `e >= m * L`), and each holding it
/// with coefficient -1 with the second (`v <= U` into `e <= m * U + m - 1`), both exact since
/// `v` is `e div m` and `L` and `U` are integers; the pair itself stays, so the rows hold
/// exactly where they held. The projection that follows then meets `v` in the pair alone
/// (`x <= 2 * q + 10` beside `8 * q <= x <= 8 * q + 7` becomes `x <= 2 * (x div 8)` read
/// through the pair). Pairs are taken by `m`, then atom; a pair a rewrite has changed is
/// skipped: its rows must still be opposite with constants adding to `m - 1`, since rows that
/// bound `m * v` more loosely (`y <= 3 * q <= y + 5`) leave `v` two values, and reading another
/// row through them is not exact (`q <= 0 && q >= 1` would become `-2 <= y <= 0`). Time of the rows rewritten, each found through the rows holding its atom.
// Complexity tradeoff: naive version, each pair scans every row for its atom, O(p r t) for
// p pairs over r rows of t terms. Used: the rows holding each atom, kept as rows are
// rewritten, so each pair reads only its atom's rows, O(r t + w t) term visits for w
// rewrites in all, besides the sorts: of the rows, O(r log r) comparisons of rows, of the
// pairs, O(p log p), and of the holder lists, whose E <= r t + w t entries in all cost
// O(E log E) comparisons (cross-review of LOAD-max-div-xr, round 2). Tradeoffs: one hash map
// of row lists; a list keeps an entry of a row that no longer holds the atom, skipped where
// it is read.
fn by_pairs(mut rows: Vec<Con>, elim: &dyn Fn(&Atom) -> bool) -> Vec<Con> {
    rows.sort();
    let mut pairs = pairs(&rows);
    pairs.retain(|(_, v, _, _)| elim(v));
    pairs.sort();
    // The rows holding each atom: a rewritten row is added under its new atoms, and an entry
    // whose row no longer holds the atom is skipped.
    let mut at: HashMap<Atom, Vec<usize>> = HashMap::new();
    for (n, r) in rows.iter().enumerate() {
        for a in r.lin.terms.keys() {
            at.entry(a.clone()).or_default().push(n);
        }
    }
    let mut done: HashSet<Atom> = HashSet::new();
    for (m, v, i, j) in pairs {
        if !done.insert(v.clone()) {
            continue;
        }
        let (a, b) = (rows[i].clone(), rows[j].clone());
        if a.lin.terms.get(&v) != Some(&-&m)
            || b.lin.terms.get(&v) != Some(&m)
            || a.lin.plus(&b.lin) != Lin::constant(&m - &Int::ONE)
        {
            continue;
        }
        let mut holders = at.remove(&v).unwrap_or_default();
        holders.sort_unstable();
        holders.dedup();
        for n in holders {
            let r = &mut rows[n];
            if n == i || n == j || r.rel != Rel::Ge {
                continue;
            }
            let side = match r.lin.terms.get(&v) {
                Some(c) if *c == Int::ONE => &a,
                Some(c) if *c == -&Int::ONE => &b,
                _ => continue,
            };
            let lin = r.lin.times(m.clone()).plus(&side.lin);
            let g = lin.terms.values().fold(Int::ZERO, |g, c| g.gcd(c));
            r.lin = if g.is_zero() || g == Int::ONE {
                lin
            } else {
                Lin {
                    terms: (lin.terms.iter())
                        .map(|(k, c)| (k.clone(), c.div_floor(&g)))
                        .collect(),
                    constant: lin.constant.div_floor(&g),
                }
            };
            for t in r.lin.terms.keys() {
                at.entry(t.clone()).or_default().push(n);
            }
        }
    }
    rows
}

/// The atoms outside `keep` to keep beside it in a projection of `rows`, read as any value
/// there: an atom `v` with a division pair `v == e div m` ([`pairs`]) whose `e` holds only kept
/// atoms and that another row holds with a coefficient other than 1 or -1 (`2 * q` in `x <=
/// 2 * q + 10` beside `8 * q <= x <= 8 * q + 7`), whose elimination needs a remainder of `e`
/// in general; and, for a pair with `m` above 1 and a kept `v`, the symbols of its `e` (the
/// `x` of `q == x div 3` with `q` kept), which the next link would otherwise need a remainder
/// of `q` to eliminate. Time of the rows' terms.
// Complexity tradeoff: naive version, each pair scans every row for its atom with a
// coefficient other than 1 or -1, O(p r t). Used: those rows of each atom gathered once,
// O(r t) and a lookup for each pair. Tradeoffs: one hash map of row lists.
fn kept_quotients(rows: &[Con], keep: &dyn Fn(&Atom) -> bool) -> HashSet<Atom> {
    // The rows holding each atom with a coefficient other than 1 or -1.
    let mut wide: HashMap<&Atom, Vec<usize>> = HashMap::new();
    for (n, r) in rows.iter().enumerate() {
        for (a, c) in &r.lin.terms {
            if *c != Int::ONE && *c != -&Int::ONE {
                wide.entry(a).or_default().push(n);
            }
        }
    }
    let mut out = HashSet::new();
    for (m, v, i, j) in pairs(rows) {
        let e = rows[i].lin.terms.keys().filter(|b| **b != v);
        if keep(&v) {
            if m != Int::ONE {
                out.extend(e.filter(|b| !keep(b) && matches!(b, Atom::Sym(_))).cloned());
            }
            continue;
        }
        let other = || {
            wide.get(&v)
                .is_some_and(|ns| ns.iter().any(|&n| n != i && n != j))
        };
        if e.clone().all(keep) && other() {
            out.insert(v);
        }
    }
    out
}

/// `rows` with each remainder written as a division pair: an atom `r` outside `keep` (no
/// product or product factor) with coefficient 1 or -1 in an equation and held by exactly two
/// other rows, each a bound of `r` alone, is solved from the equation into the bounds, so that
/// `e == m * v + r, 0 <= r <= m - 1` reads as `m * v <= e <= m * v + m - 1`; the three rows are
/// replaced by the two. The rows hold where they held with some `r`. Time of the rows' terms.
fn remainders_as_pairs(rows: &[Con], keep: &dyn Fn(&Atom) -> bool) -> Vec<Con> {
    let mut rows: Vec<Con> = rows.to_vec();
    rows.sort();
    rows.dedup();
    let factors = product_factors(&rows);
    let mut at: HashMap<&Atom, Vec<usize>> = HashMap::new();
    for (i, r) in rows.iter().enumerate() {
        for a in r.lin.terms.keys() {
            at.entry(a).or_default().push(i);
        }
    }
    let mut gone: HashSet<usize> = HashSet::new();
    let mut out: Vec<Con> = Vec::new();
    for (i, e) in rows.iter().enumerate() {
        if e.rel != Rel::Eq || gone.contains(&i) {
            continue;
        }
        for (r, c) in &e.lin.terms {
            if keep(r)
                || matches!(r, Atom::Product(..))
                || factors.contains(r)
                || (*c != Int::ONE && *c != -&Int::ONE)
            {
                continue;
            }
            let uses = &at[r];
            if uses.len() != 3 {
                continue;
            }
            let bounds: Vec<usize> = uses.iter().copied().filter(|&n| n != i).collect();
            if (bounds.iter()).any(|&n| {
                gone.contains(&n) || rows[n].rel != Rel::Ge || rows[n].lin.terms.len() != 1
            }) {
                continue;
            }
            // `e` is `c * r + rest == 0`, so `r == -c * rest` for `c` 1 or -1.
            let mut rest = e.lin.clone();
            rest.terms.remove(r);
            let val = rest.times(-c);
            for &n in &bounds {
                let k = &rows[n].lin.terms[r];
                let lin = val
                    .times(k.clone())
                    .plus(&Lin::constant(rows[n].lin.constant.clone()));
                out.push(Con { lin, rel: Rel::Ge });
            }
            gone.insert(i);
            gone.extend(bounds);
            break;
        }
    }
    out.extend(
        (rows.iter().enumerate())
            .filter(|(n, _)| !gone.contains(n))
            .map(|(_, r)| r.clone()),
    );
    out
}

/// `rows` with each row mentioning `own` reduced by the piece's own non-`own` leaf equations:
/// a division equation `m * q0 + unit_rest == 0` (`|m| > 1`, `q0` a leaf atom) eliminates any
/// exact multiple of `m * q0` from an `own` row (`h1 - 2 * x + 7 * q0 == 0` beside `x - 7 * q0 -
/// r0 == 0` becomes `h1 - x - r0 == 0`), and a unary leaf equation `r0 == c` substitutes `c` into
/// an `own` row (`h1 - x - 1 == 0`). Both equations stay in `rows`, so integer points are
/// unchanged; `None` if a reduced `own` row contradicts itself.
fn normalize_own_leaf(
    mut rows: Vec<Con>,
    own: &[u32],
    leaf: &dyn Fn(&Atom) -> bool,
) -> Option<Vec<Con>> {
    rows.sort();
    rows.dedup();
    let is_own = |a: &Atom| matches!(a, Atom::Aux(n) if own.binary_search(n).is_ok());
    let eqs: Vec<Con> = (rows.iter())
        .filter(|c| c.rel == Rel::Eq && !c.lin.terms.keys().any(&is_own))
        .cloned()
        .collect();
    if eqs.is_empty() {
        return Some(rows);
    }
    let quot_eqs: Vec<(Atom, Int, Con)> = (eqs.iter())
        .filter_map(|eq| {
            let mut non_unit = (eq.lin.terms.iter())
                .filter(|(a, k)| !k.is_unit() || (!matches!(a, Atom::Sym(_)) && !leaf(a)));
            let (q0, kq) = non_unit.next()?;
            if non_unit.next().is_some() || !leaf(q0) || kq.is_unit() {
                return None;
            }
            let others_ok = (eq.lin.terms.iter())
                .filter(|(a, _)| *a != q0)
                .all(|(a, k)| k.is_unit() && (matches!(a, Atom::Sym(_)) || leaf(a)));
            others_ok.then(|| (q0.clone(), kq.clone(), eq.clone()))
        })
        .collect();
    let fixed_eqs: Vec<(Atom, Int, Con)> = (eqs.iter())
        .filter_map(|eq| {
            if eq.lin.terms.len() != 1 {
                return None;
            }
            let (a, ca) = eq.lin.terms.iter().next()?;
            (leaf(a) && ca.is_unit()).then(|| (a.clone(), ca.clone(), eq.clone()))
        })
        .collect();
    if quot_eqs.is_empty() && fixed_eqs.is_empty() {
        return Some(rows);
    }
    let mut out = Vec::with_capacity(rows.len());
    for mut r in rows {
        if !r.lin.terms.keys().any(&is_own) {
            out.push(r);
            continue;
        }
        let mut changed = false;
        for (q0, kq, eq) in &quot_eqs {
            if let Some(cr) = r.lin.terms.get(q0).cloned()
                && cr.mod_floor(kq).is_zero()
            {
                r.lin = r.lin.minus(&eq.lin.times(cr.div_floor(kq)));
                changed = true;
            }
        }
        for (a, ca, eq) in &fixed_eqs {
            if let Some(cr) = r.lin.terms.get(a).cloned() {
                r.lin = r.lin.minus(&eq.lin.times(&cr * ca));
                changed = true;
            }
        }
        if changed {
            if r.lin.terms.is_empty() {
                let holds = match r.rel {
                    Rel::Eq => r.lin.constant.is_zero(),
                    Rel::Ge => !r.lin.constant.is_negative(),
                };
                if !holds {
                    return None;
                }
                continue;
            }
            let g = r.lin.terms.values().fold(Int::ZERO, |g, k| g.gcd(k));
            if r.rel == Rel::Eq && !r.lin.constant.mod_floor(&g).is_zero() {
                return None;
            }
            if !g.is_unit() {
                r.lin = Lin {
                    terms: (r.lin.terms.iter())
                        .map(|(a, k)| (a.clone(), k.div_floor(&g)))
                        .collect(),
                    constant: r.lin.constant.div_floor(&g),
                };
            }
        }
        out.push(r);
    }
    Some(out)
}

/// `rows` split on the integer values of the narrowest finitely bounded periodic quotient-offset
/// form `Q = q + sum c_i * b_i` (`q` an uneliminated non-leaf variable, one or more `b_i`
/// unbounded kept leaf variables), when projecting `rows` onto `{q}` and the kept leaf variables
/// bounds `Q` to `[lo, hi]` directly or through leaf remainders narrower than `q`'s modulus (`r`
/// of `x mod m` with `0 <= r <= m - 1`): each branch adds `Q == d` (`lo <= d <= hi`), giving `q`
/// coefficient 1 over kept variables so the next [`shadow_whole`] eliminates `q` in one step.
/// Exact over the integers (`rows` implies `lo <= Q <= hi`), and `None` when no non-leaf variable
/// has a finitely bounded multi-term quotient offset (`(3 * H + 1) div 2`, `(x mod M) div 2`).
// Complexity tradeoff: naive version, branch on every residue `0..m - 1` of a bounded remainder,
// O(m) pieces per step (exploding on large moduli `m`), or inline multi-term call values so the
// key gains one remainder atom a link, O(n²) (LOAD-max-div-xr I12). Used: project onto `{q}` and
// the kept leaf variables, bound `Q = q + sum c_i * b_i` over at least one unbounded kept leaf
// quotient `b_i` from the projected rows and leaf remainders narrower than `m`, and split only on
// `lo <= Q <= hi` (width at most 1 for `H mod m + H`, independent of `m`). Tradeoffs: one
// `shadow_whole` per uneliminated non-leaf variable when normal projection fails (`0` calls when
// normal projection succeeds); non-periodic steps (`(3 * H + 1) div 2`) leave `Q` unbounded and
// return `None` in one pass.
fn quotient_offsets(
    rows: &[Con],
    keep: &dyn Fn(&Atom) -> bool,
    leaf: &dyn Fn(&Atom) -> bool,
    def: &dyn Fn(u32) -> Formula,
) -> Option<Vec<Vec<Con>>> {
    let ceil_div = |x: &Int, g: &Int| -(&(-x).div_floor(g));
    let tighten = |b: &mut (Option<Int>, Option<Int>), lo: Option<Int>, hi: Option<Int>| {
        if let Some(l) = lo {
            b.0 = Some(b.0.take().map_or(l.clone(), |o| o.max(l)));
        }
        if let Some(h) = hi {
            b.1 = Some(b.1.take().map_or(h.clone(), |o| o.min(h)));
        }
    };
    let unary_bounds = |cs: &[Con], target: &Atom| -> Option<(Option<Int>, Option<Int>)> {
        let mut b = (None, None);
        for r in cs {
            if r.lin.terms.is_empty() {
                let ok = if r.rel == Rel::Eq {
                    r.lin.constant.is_zero()
                } else {
                    !r.lin.constant.is_negative()
                };
                if !ok {
                    return None;
                }
                continue;
            }
            if r.lin.terms.len() != 1 {
                continue;
            }
            let Some(ka) = r.lin.terms.get(target) else {
                continue;
            };
            let g = ka.abs();
            let c = &r.lin.constant;
            match (r.rel, ka.is_positive()) {
                (Rel::Ge, true) => tighten(&mut b, Some(ceil_div(&(-c), &g)), None),
                (Rel::Ge, false) => tighten(&mut b, None, Some(c.div_floor(&g))),
                (Rel::Eq, _) => {
                    if !c.mod_floor(&g).is_zero() {
                        return None;
                    }
                    let v = if ka.is_positive() {
                        -&c.div_floor(&g)
                    } else {
                        c.div_floor(&g)
                    };
                    tighten(&mut b, Some(v.clone()), Some(v));
                }
            }
            if let (Some(l), Some(h)) = (&b.0, &b.1)
                && l > h
            {
                return None;
            }
        }
        Some(b)
    };
    let is_other = |a: &Atom| !keep(a) && !matches!(a, Atom::Sym(_)) && !leaf(a);
    let mut targets: BTreeSet<Atom> = BTreeSet::new();
    let mut def_bounds: BTreeMap<Atom, (Int, Int)> = BTreeMap::new();
    for r in rows {
        for a in r.lin.terms.keys() {
            if is_other(a) {
                targets.insert(a.clone());
            } else if let Atom::Aux(n) = a
                && leaf(a)
                && keep(a)
                && !def_bounds.contains_key(a)
                && let Some(cs) = cases(&def(*n))
                && !cs.is_empty()
            {
                let mut all_lo: Option<Int> = None;
                let mut all_hi: Option<Int> = None;
                let mut every_bounded = true;
                for c in &cs {
                    match unary_bounds(c, a) {
                        None => {}
                        Some((Some(l), Some(h))) => {
                            all_lo = Some(all_lo.take().map_or(l.clone(), |o| o.min(l)));
                            all_hi = Some(all_hi.take().map_or(h.clone(), |o| o.max(h)));
                        }
                        Some(_) => {
                            every_bounded = false;
                            break;
                        }
                    }
                }
                if every_bounded {
                    match (all_lo, all_hi) {
                        (Some(l), Some(h)) => {
                            def_bounds.insert(a.clone(), (l, h));
                        }
                        _ => return Some(Vec::new()),
                    }
                }
            }
        }
    }
    let mut best: Option<(Int, Terms, Int, Int)> = None;
    for q_star in targets {
        let keep_q = |a: &Atom| *a == q_star || (!matches!(a, Atom::Sym(_)) && leaf(a) && keep(a));
        let elim_q = |a: &Atom| !keep_q(a);
        let Some(mut proj) = shadow_whole(&by_pairs(rows.to_vec(), &elim_q), &keep_q) else {
            return Some(Vec::new());
        };
        proj.retain(|c| c.lin.terms.keys().all(&keep_q));
        let (_, form_bounds, ok) = group_lines(&proj);
        if !ok {
            return Some(Vec::new());
        }
        let mut rem_bounds = def_bounds.clone();
        // Tighten unary remainder rows first, then propagate once across multi-remainder rows.
        for unary_pass in [true, false] {
            for r in &proj {
                if r.lin.terms.is_empty()
                    || (r.lin.terms.len() == 1) != unary_pass
                    || !r.lin.terms.keys().all(|a| rem_bounds.contains_key(a))
                {
                    continue;
                }
                if unary_pass {
                    let (_a, ka) = r.lin.terms.iter().next().expect("one term");
                    if r.rel == Rel::Eq && !r.lin.constant.mod_floor(&ka.abs()).is_zero() {
                        return Some(Vec::new());
                    }
                }
                let atoms: Vec<(Atom, Int)> = (r.lin.terms.iter())
                    .map(|(a, k)| (a.clone(), k.clone()))
                    .collect();
                for (a, ka) in &atoms {
                    let mut rest_lo = r.lin.constant.clone();
                    let mut rest_hi = r.lin.constant.clone();
                    for (b, kb) in &atoms {
                        if b == a {
                            continue;
                        }
                        let (lb, hb) = &rem_bounds[b];
                        if kb.is_positive() {
                            rest_lo = &rest_lo + &(kb * lb);
                            rest_hi = &rest_hi + &(kb * hb);
                        } else {
                            rest_lo = &rest_lo + &(kb * hb);
                            rest_hi = &rest_hi + &(kb * lb);
                        }
                    }
                    let g = ka.abs();
                    let entry = rem_bounds.get_mut(a).expect("bounded leaf");
                    match (r.rel, ka.is_positive()) {
                        (Rel::Ge, true) => {
                            let lo = ceil_div(&(-&rest_hi), &g);
                            if lo > entry.0 {
                                entry.0 = lo;
                            }
                        }
                        (Rel::Ge, false) => {
                            let hi = rest_hi.div_floor(&g);
                            if hi < entry.1 {
                                entry.1 = hi;
                            }
                        }
                        (Rel::Eq, true) => {
                            let lo = ceil_div(&(-&rest_hi), &g);
                            let hi = (-&rest_lo).div_floor(&g);
                            if lo > entry.0 {
                                entry.0 = lo;
                            }
                            if hi < entry.1 {
                                entry.1 = hi;
                            }
                        }
                        (Rel::Eq, false) => {
                            let lo = ceil_div(&rest_lo, &g);
                            let hi = rest_hi.div_floor(&g);
                            if lo > entry.0 {
                                entry.0 = lo;
                            }
                            if hi < entry.1 {
                                entry.1 = hi;
                            }
                        }
                    }
                    if entry.0 > entry.1 {
                        return Some(Vec::new());
                    }
                }
            }
        }
        let mut cand: BTreeMap<Terms, (Option<Int>, Option<Int>)> = BTreeMap::new();
        for (t, (lo, hi)) in &form_bounds {
            let Some(kq) = t.get(&q_star) else { continue };
            if !kq.is_unit() || t.keys().any(|a| rem_bounds.contains_key(a)) {
                continue;
            }
            if kq.is_positive() {
                tighten(cand.entry(t.clone()).or_default(), lo.clone(), hi.clone());
            } else {
                let neg_t: Terms = t.iter().map(|(a, k)| (a.clone(), -k)).collect();
                tighten(
                    cand.entry(neg_t).or_default(),
                    hi.as_ref().map(|h| -h),
                    lo.as_ref().map(|l| -l),
                );
            }
        }
        let leaf_eqs: Vec<&Con> = (proj.iter())
            .filter(|c| c.rel == Rel::Eq && !c.lin.terms.contains_key(&q_star))
            .collect();
        for r in &proj {
            let Some(kq) = r.lin.terms.get(&q_star) else {
                continue;
            };
            let m = kq.abs();
            let mut lin = r.lin.clone();
            loop {
                let bad = (lin.terms.iter()).find(|&(a, k)| {
                    *a != q_star && !rem_bounds.contains_key(a) && !k.mod_floor(&m).is_zero()
                });
                let Some((u, ku)) = bad.map(|(a, k)| (a.clone(), k.clone())) else {
                    break;
                };
                let rep = leaf_eqs.iter().find_map(|eq| {
                    let cu = eq.lin.terms.get(&u)?;
                    if !ku.mod_floor(cu).is_zero() {
                        return None;
                    }
                    let next = lin.minus(&eq.lin.times(ku.div_floor(cu)));
                    let fewer = next
                        .terms
                        .iter()
                        .filter(|&(a, k)| {
                            *a != q_star
                                && !rem_bounds.contains_key(a)
                                && !k.mod_floor(&m).is_zero()
                        })
                        .count()
                        < lin
                            .terms
                            .iter()
                            .filter(|&(a, k)| {
                                *a != q_star
                                    && !rem_bounds.contains_key(a)
                                    && !k.mod_floor(&m).is_zero()
                            })
                            .count();
                    fewer.then_some(next)
                });
                match rep {
                    Some(next) => lin = next,
                    None => break,
                }
            }
            let Some(kq) = lin.terms.get(&q_star) else {
                continue;
            };
            let m = kq.abs();
            let neg_q = kq.is_negative();
            let mut q_terms: Terms = BTreeMap::new();
            let mut r_min = Int::ZERO;
            let mut r_max = Int::ZERO;
            let mut bounded = true;
            for (a, raw_k) in &lin.terms {
                let k = if neg_q { -raw_k } else { raw_k.clone() };
                if let Some((lo_a, hi_a)) = rem_bounds.get(a) {
                    if &(hi_a - lo_a) >= &m {
                        bounded = false;
                        break;
                    }
                    if k.is_positive() {
                        r_min = &r_min + &(&k * lo_a);
                        r_max = &r_max + &(&k * hi_a);
                    } else {
                        r_min = &r_min + &(&k * hi_a);
                        r_max = &r_max + &(&k * lo_a);
                    }
                } else if k.mod_floor(&m).is_zero() {
                    let qk = k.div_floor(&m);
                    if !qk.is_zero() {
                        q_terms.insert(a.clone(), qk);
                    }
                } else {
                    bounded = false;
                    break;
                }
            }
            if !bounded {
                continue;
            }
            let c = &lin.constant;
            match (r.rel, neg_q) {
                (Rel::Ge, false) => {
                    let lo = ceil_div(&-&(c + &r_max), &m);
                    tighten(cand.entry(q_terms).or_default(), Some(lo), None);
                }
                (Rel::Ge, true) => {
                    let cap = c - &r_min;
                    let hi = cap.div_floor(&m);
                    tighten(cand.entry(q_terms).or_default(), None, Some(hi));
                }
                (Rel::Eq, _) => {
                    let c_pos = if neg_q { -c } else { c.clone() };
                    let lo = ceil_div(&-&(&c_pos + &r_max), &m);
                    let hi = (-&(&c_pos + &r_min)).div_floor(&m);
                    tighten(cand.entry(q_terms).or_default(), Some(lo), Some(hi));
                }
            }
        }
        for (q_terms, (lo, hi)) in cand {
            if let (Some(l), Some(h)) = (&lo, &hi)
                && l > h
            {
                return Some(Vec::new());
            }
            if q_terms.len() < 2 {
                continue;
            }
            let (Some(l), Some(h)) = (lo, hi) else {
                continue;
            };
            let q_lin = Lin {
                terms: q_terms.clone(),
                constant: Int::ZERO,
            };
            let eq_l = Con::eq(&q_lin, &Lin::constant(l.clone()));
            let eq_neg = Con::eq(&Lin::constant(l.clone()), &q_lin);
            if l == h && (rows.contains(&eq_l) || rows.contains(&eq_neg)) {
                continue;
            }
            let width = &h - &l;
            let take = match &best {
                None => true,
                Some((bw, _, _, _)) => width < *bw,
            };
            if take {
                best = Some((width, q_terms, l, h));
            }
        }
    }
    let (_, q_terms, lo, hi) = best?;
    let q_lin = Lin {
        terms: q_terms,
        constant: Int::ZERO,
    };
    let mut out = Vec::new();
    let mut d = lo;
    while d <= hi {
        let mut b = rows.to_vec();
        b.push(Con::eq(&q_lin, &Lin::constant(d.clone())));
        out.push(b);
        d = &d + &Int::ONE;
    }
    Some(out)
}

/// Join integer vertical rays at consecutive abscissas when their heights form a convex
/// sequence. The secants of adjacent vertices recover exactly those heights on the integer
/// interval; they do not assert an interpolation identity at noninteger abscissas.
// Complexity tradeoff: pairwise cross-rest merging materializes every tangent's rest for
// every growing intermediate piece, O(p^3) row visits on x=i, y>=2*i*x-i² (I27). Used:
// recognize two-row vertical rays, sort and coalesce equal abscissas, check consecutive
// spacing and nondecreasing secants, and emit all distinct secants once, O(p log p) integer
// operations and O(p) output. Tradeoffs: this fast path handles convex integer sequences
// over two atoms only; arbitrary cross-rest unions still use the exact general merger.
fn convex_integer_rays(pieces: &BTreeSet<Vec<Con>>) -> Option<Vec<Con>> {
    let mut axes: Option<(Atom, Atom)> = None;
    let mut points: BTreeMap<Int, Int> = BTreeMap::new();
    for p in pieces {
        let [r, s] = p.as_slice() else {
            return None;
        };
        let (eq, ge) = match (r.rel, s.rel) {
            (Rel::Eq, Rel::Ge) => (r, s),
            (Rel::Ge, Rel::Eq) => (s, r),
            _ => return None,
        };
        if eq.lin.terms.len() != 1 {
            return None;
        }
        let (x, kx) = eq.lin.terms.first_key_value()?;
        if !kx.is_unit() {
            return None;
        }
        let x = (*x).clone();
        let xi = -&(&eq.lin.constant * kx);
        let mut others = ge.lin.terms.iter().filter(|(a, _)| **a != x);
        let (y, ky) = others.next()?;
        if !ky.is_positive() || others.next().is_some() {
            return None;
        }
        let this = (x.clone(), y.clone());
        if axes.as_ref().is_some_and(|old| *old != this) {
            return None;
        }
        axes = Some(this);
        let at_x = &ge.lin.constant + &(ge.lin.terms.get(&x).unwrap_or(&Int::ZERO) * &xi);
        let height = -&at_x.div_floor(ky);
        points
            .entry(xi)
            .and_modify(|h| *h = h.clone().min(height.clone()))
            .or_insert(height);
    }
    let (x, y) = axes?;
    let ps: Vec<_> = points.into_iter().collect();
    let (lo, _) = ps.first()?;
    let (hi, _) = ps.last()?;
    let mut rows = Vec::with_capacity(ps.len() + 2);
    let mut old_slope: Option<Int> = None;
    for two in ps.windows(2) {
        let [(a, ha), (b, hb)] = two else {
            unreachable!()
        };
        if b != &(a + &Int::ONE) {
            return None;
        }
        let slope = hb - ha;
        if old_slope.as_ref().is_some_and(|s| *s > slope) {
            return None;
        }
        if old_slope.as_ref() != Some(&slope) {
            let mut terms = BTreeMap::from([(y.clone(), Int::ONE)]);
            if !slope.is_zero() {
                terms.insert(x.clone(), -&slope);
            }
            rows.push(Con {
                lin: Lin {
                    terms,
                    constant: &(&slope * a) - ha,
                },
                rel: Rel::Ge,
            });
            old_slope = Some(slope);
        }
    }
    if ps.len() == 1 {
        rows.push(Con::ge(&Lin::atom(y), &Lin::constant(ps[0].1.clone())));
    }
    if lo == hi {
        rows.push(Con::eq(&Lin::atom(x), &Lin::constant(lo.clone())));
    } else {
        rows.push(Con::ge(&Lin::atom(x.clone()), &Lin::constant(lo.clone())));
        rows.push(Con::ge(&Lin::constant(hi.clone()), &Lin::atom(x)));
    }
    rows.sort();
    rows.dedup();
    Some(rows)
}

/// `pieces` with any two equal but for the bounds of one linear form, whose intervals of
/// integers for it overlap or touch, or whose rest holds at no integer point with the form
/// between them ([`decide`]), merged into one with the interval holding both, until no two
/// merge: the union of the two is the merged piece's points, since the rest is the same and
/// the rest's points with the form between the two intervals are none. A form is a row's
/// terms with the first coefficient positive. `min(H div 2, x)` cases split at `x` meet again
/// this way, and the values `max(H - 1, x mod 5 + x div 7 - 9)` takes as its second
/// argument, at intervals of `x - (x mod 5) - (x div 7)` with no integer point between them.
///
/// Two pieces next to each other on one form whose rests `A` and `B` differ merge too, into
/// `A`, `B` and the interval holding both, when `B` holds wherever the piece of `A` does, `A`
/// wherever the piece of `B` does, and `A` and `B` hold at no integer point with the form
/// between the two intervals: each piece lies in the merged one, and a point of the merged one
/// with the form in the interval of one piece is a point of that piece. `max(H div 2, x + y -
/// 9)` cases at each link `k` where the chain takes `x + y - 9`, bounded by `(2^k - 1) x + 2^k
/// y >= c_k` and by the form of link `k - 1`, meet again this way.
// Here r is the maximum intermediate rest size, which can grow with p (I27); the convex
// integer-ray batch above avoids that growth for its structural class, not all merges.
// Complexity tradeoff: naive version, each pass groups all pieces by form and merges, and
// passes repeat while one merges, O(p) passes over p pieces of r rows, O(p² r²). Used: a work
// list, each piece put in the groups of its forms, where the intervals of the pieces in a
// group never overlap, touch or hold an empty gap and so are ordered by their lower bounds: a
// piece meets the one before and the one after its interval only, found in O(log p) (one
// further off has a piece with a point in the gap), and two that merge are taken out and
// their merge put back on the list; each merge leaves one piece fewer, so p pieces are put
// in at most 2p times, O(p r² + p r log p) (the rest of a piece for each of its forms is
// O(r) to make), and at most two decisions of the rest with a gap for each form tried, O(p r)
// decisions of O(r) rows (cross-review of LOAD-max-div-xr, round 2: pieces fixing each of r
// coordinates to 0 or 2 try every form). The pieces of different rests: for each form, the
// pieces by upper bound and by lower bound, where a piece no group merges finds the one with
// the nearest upper bound below its interval and the one with the nearest lower bound above,
// O(log p); for each, O(r) decisions that one rest holds on the other piece and one with the
// gap, O(r) forms tried per piece put in, O(p r²) decisions of O(r) rows in all (naive: each
// pair of pieces with a shared form, O(p² r) decisions). The forms of a piece are made once
// when it is put in and kept beside it: made again for each neighbor read, O(r) forms of O(r)
// rows for each of O(r) forms tried, O(p r³) row visits (cross-review of LOAD-max-div-xr,
// round 3, Codex); kept, O(r) to find the one form, O(p r²) in all, for the storage of the
// forms of the pieces put in. Ties of one bound keep the piece put
// in last, so a piece hidden by a tie, or the nearer one where it fails, stays apart: exact,
// more pieces. `max(H div 2, x + y - 9)`: n^2.06 to 80 links before (21.4 G instructions), 4
// pieces at each link and n^1.1 to n^1.6 with it (2.8 G at 80 links, 20.6 G at 320); the
// rest is the coefficients growing one bit a link, LOAD-max-div-bits. Tradeoffs: one hash map and one ordered map for each group; two pieces whose
// union is no interval of one form (`x <= 2` and `x >= 4` with a point at 3, or two forms
// changing at once) stay apart, exact but more pieces; a gap whose decision is refused is
// taken to have a point. `max(H - 1, x mod 5 + x div 7 - 9)`: n^2.0 from 10 to 80 links
// before the gap test (0.67 to 32.6 G instructions, one piece more every few links), n^1.0
// with it (0.63 to 5.8 G).
fn merge_pieces(pieces: BTreeSet<Vec<Con>>) -> Vec<Vec<Con>> {
    // Complexity tradeoff: indexing every form constructs r rests of r rows, O(r²),
    // even when the union has no pair that could merge (R5-C38, beyond I18's cached forms).
    // Empty/singleton unions are the identity: transfer their owned row vectors directly,
    // O(1) container work. This is the merger's intrinsic arity, not a work/size budget.
    if pieces.iter().nth(1).is_none() {
        return pieces.into_iter().collect();
    }

    if let Some(joined) = convex_integer_rays(&pieces) {
        return vec![joined];
    }
    type Terms = BTreeMap<Atom, Int>;
    type Group = (Vec<Con>, Terms);
    // The pieces of one group by lower bound: upper bound and index in `live`.
    type Intervals = BTreeMap<Option<Int>, (Option<Int>, usize)>;
    // Each form of piece `p`: `p` without its rows of the form, the form, and the lower and
    // upper bounds the rows give it (`None` none).
    fn forms(p: &[Con]) -> Vec<(Group, Option<Int>, Option<Int>)> {
        let form = |c: &Con| -> (Terms, bool) {
            let neg = c.lin.terms.values().next().is_some_and(|k| k.is_negative());
            let t = if neg {
                c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect()
            } else {
                c.lin.terms.clone()
            };
            (t, neg)
        };
        let mut bounds: BTreeMap<Terms, (Option<Int>, Option<Int>)> = BTreeMap::new();
        for r in p.iter().filter(|r| !r.lin.terms.is_empty()) {
            let (t, neg) = form(r);
            let b = bounds.entry(t).or_insert((None, None));
            // The row is `t + c` (or `-t + c`) `>= 0` or `== 0`.
            let c = &r.lin.constant;
            let (lo, hi) = match (r.rel, neg) {
                (Rel::Ge, false) => (Some(-c), None),
                (Rel::Ge, true) => (None, Some(c.clone())),
                (Rel::Eq, false) => (Some(-c), Some(-c)),
                (Rel::Eq, true) => (Some(c.clone()), Some(c.clone())),
            };
            if let Some(l) = lo {
                b.0 = Some(b.0.take().map_or(l.clone(), |o| o.max(l)));
            }
            if let Some(h) = hi {
                b.1 = Some(b.1.take().map_or(h.clone(), |o| o.min(h)));
            }
        }
        (bounds.into_iter())
            .map(|(t, (lo, hi))| {
                #[cfg(test)]
                REST_ROW_VISITS.with(|v| v.set(v.get() + p.len()));
                let rest = (p.iter())
                    .filter(|r| r.lin.terms.is_empty() || form(r).0 != t)
                    .cloned()
                    .collect();
                ((rest, t), lo, hi)
            })
            .collect()
    }
    // Whether `[lo, hi]` and `[l, h]` of the form of group `g` overlap or touch, `None`
    // unbounded, or the rest of `g` holds at no integer point with the form between them.
    let touch = |g: &Group, hi: &Option<Int>, l: &Option<Int>| match (hi, l) {
        (Some(h), Some(l)) if &(h + &Int::ONE) < l => {
            let t = Lin {
                terms: g.1.clone(),
                constant: Int::ZERO,
            };
            let gap = [
                Con::ge(&t, &Lin::constant(h + &Int::ONE)),
                Con::ge(&Lin::constant(l - &Int::ONE), &t),
            ];
            decide_cons(g.0.iter().chain(&gap).cloned().collect()) == Ok(false)
        }
        _ => true,
    };
    // Whether `r` holds wherever `piece` does: `piece` with `r` negated has no integer point (a
    // decision refused counts as a point).
    let implied = |piece: &[Con], r: &Con| {
        let neg = |l: &Lin| Con {
            lin: l.times(-&Int::ONE).plus(&Lin::constant(-&Int::ONE)),
            rel: Rel::Ge,
        };
        let not: Vec<Con> = match r.rel {
            Rel::Ge => vec![neg(&r.lin)],
            Rel::Eq => vec![neg(&r.lin), neg(&r.lin.times(-&Int::ONE))],
        };
        not.iter()
            .all(|n| decide_cons(piece.iter().chain([n]).cloned().collect()) == Ok(false))
    };
    // The rest of `g` with its form between `lo` and `hi`, `None` unbounded.
    let joined = |g: &Group, lo: Option<Int>, hi: Option<Int>| {
        let t = Lin {
            terms: g.1.clone(),
            constant: Int::ZERO,
        };
        let mut merged = g.0.clone();
        match (&lo, &hi) {
            (Some(l), Some(h)) if l == h => merged.push(Con::eq(&t, &Lin::constant(l.clone()))),
            _ => {
                if let Some(l) = &lo {
                    merged.push(Con::ge(&t, &Lin::constant(l.clone())));
                }
                if let Some(h) = &hi {
                    merged.push(Con::ge(&Lin::constant(h.clone()), &t));
                }
            }
        }
        merged.sort();
        merged.dedup();
        merged
    };
    let unindex =
        |id: usize,
         forms_of: &mut [Vec<(Group, Option<Int>, Option<Int>)>],
         groups: &mut HashMap<Group, Intervals>,
         sides: &mut HashMap<Terms, (BTreeMap<Int, usize>, BTreeMap<Int, usize>)>| {
            for (gq, lq, hq) in std::mem::take(&mut forms_of[id]) {
                if let Some(m) = groups.get_mut(&gq) {
                    m.remove(&lq);
                }
                // Another piece with the same bound may hold the entry since.
                if let Some((u, w)) = sides.get_mut(&gq.1) {
                    if let Some(hq) = hq
                        && u.get(&hq) == Some(&id)
                    {
                        u.remove(&hq);
                    }
                    if let Some(lq) = lq
                        && w.get(&lq) == Some(&id)
                    {
                        w.remove(&lq);
                    }
                }
            }
        };
    // For each form, the pieces holding a bound of it, by upper bound and by lower bound (an
    // entry of a piece merged since is skipped where read).
    let mut sides: HashMap<Terms, (BTreeMap<Int, usize>, BTreeMap<Int, usize>)> = HashMap::new();
    let mut live: Vec<Option<Vec<Con>>> = Vec::new();
    // The forms of each piece put in, by its index in `live`, made once when it is put in.
    let mut forms_of: Vec<Vec<(Group, Option<Int>, Option<Int>)>> = Vec::new();
    let mut groups: HashMap<Group, Intervals> = HashMap::new();
    let mut work: Vec<Vec<Con>> = pieces.into_iter().collect();
    while let Some(p) = work.pop() {
        let fs = forms(&p);
        let hit = fs.iter().find_map(|(g, lo, hi)| {
            let m = groups.get(g)?;
            let before = (m.range(..=lo.clone()).next_back()).filter(|(_, (h, _))| touch(g, h, lo));
            let after = (m.range((
                std::ops::Bound::Excluded(lo.clone()),
                std::ops::Bound::Unbounded,
            )))
            .next()
            .filter(|(l, _)| touch(g, hi, l));
            let (l, (h, id)) = before.or(after)?;
            Some((g, lo, hi, l.clone(), h.clone(), *id))
        });
        // A piece in a group is live: its entries leave the groups and sides when it is merged.
        let hit = hit.and_then(|(g, lo, hi, l, h, id)| {
            live[id].take()?;
            Some((g, lo, hi, l, h, id))
        });
        let Some((g, lo, hi, l, h, id)) = hit else {
            // Else the piece next to it on one of its forms whose rest differs: they merge when
            // each rest holds wherever the other piece does and the two rests hold at no integer
            // point with the form between them.
            let cross = fs.iter().find_map(|(g, lo, hi)| {
                let (uppers, lowers) = sides.get(&g.1)?;
                let below = lo
                    .as_ref()
                    .and_then(|lo| uppers.range(..lo.clone()).next_back())
                    .map(|(_, id)| *id);
                let above = hi
                    .as_ref()
                    .and_then(|hi| {
                        lowers
                            .range((
                                std::ops::Bound::Excluded(hi.clone()),
                                std::ops::Bound::Unbounded,
                            ))
                            .next()
                    })
                    .map(|(_, id)| *id);
                // `up`: the other piece lies above this one on the form, so the gap is between
                // this one's upper bound and its lower bound; else between its upper bound and
                // this one's lower bound (cross-review of LOAD-max-div-xr, round 3: read from a
                // comparison of the lower bounds, the gap of a piece with no lower bound and one
                // above it went unchecked).
                [below.map(|id| (id, false)), above.map(|id| (id, true))]
                    .into_iter()
                    .flatten()
                    .find_map(|(id, up)| {
                        let q = live[id].as_ref()?;
                        let (b, l, h) = (forms_of[id].iter())
                            .find(|(gq, _, _)| gq.1 == g.1)
                            .cloned()?;
                        let b = b.0;
                        if b == g.0
                            || !g.0.iter().all(|r| implied(q, r))
                            || !b.iter().all(|r| implied(&p, r))
                        {
                            return None;
                        }
                        let rest: Vec<Con> = g.0.iter().chain(&b).cloned().collect();
                        let both = (rest.clone(), g.1.clone());
                        let ok = if up {
                            touch(&both, hi, &l)
                        } else {
                            touch(&both, &h, lo)
                        };
                        ok.then(|| (both, lo.clone(), hi.clone(), l, h, id))
                    })
            });
            if let Some((both, lo, hi, l, h, id)) = cross {
                if live[id].take().is_some() {
                    unindex(id, &mut forms_of, &mut groups, &mut sides);
                    let mut m = lean(joined(
                        &both,
                        lo.min(l),
                        match (hi, h) {
                            (Some(a), Some(b)) => Some(a.max(b)),
                            _ => None,
                        },
                    ));
                    m.sort();
                    m.dedup();
                    work.push(m);
                    continue;
                }
            }
            for (g, lo, hi) in &fs {
                let (u, w) = sides.entry(g.1.clone()).or_default();
                if let Some(hi) = hi {
                    u.insert(hi.clone(), live.len());
                }
                if let Some(lo) = lo {
                    w.insert(lo.clone(), live.len());
                }
                (groups.entry(g.clone()).or_default()).insert(lo.clone(), (hi.clone(), live.len()));
            }
            forms_of.push(fs);
            live.push(Some(p));
            continue;
        };
        unindex(id, &mut forms_of, &mut groups, &mut sides);
        let lo = lo.clone().min(l);
        let hi = match (hi, h) {
            (Some(a), Some(b)) => Some(a.clone().max(b)),
            _ => None,
        };
        work.push(joined(g, lo, hi));
    }
    live.into_iter().flatten().collect()
}

/// Whether `f` is the definition of a variable with no definition: `true`.
fn free(f: &Formula) -> bool {
    matches!(f, Formula::And(gs) if gs.is_empty())
}

/// The atoms `f` reads, a product with its factors: the solver reads a product as an atom of
/// its own ([`decide`]), and its factors' definitions are among those `f` reaches ([`reached`]).
fn reads(f: &Formula) -> BTreeSet<Atom> {
    let mut out = BTreeSet::new();
    for a in f.atoms() {
        if let Atom::Product(g, h) = &a {
            out.insert(g.atom());
            out.insert(h.atom());
        }
        out.insert(a);
    }
    out
}

/// The cases of `f`: conjunctions of constraints whose disjunction holds where `f` holds, a
/// negated constraint written as the constraints of the points it leaves (`!(e >= 0)` is `-e -
/// 1 >= 0`, `!(e == 0)` the two cases `e >= 1` and `-e >= 1`); `None` for a negation of
/// anything else. Time of the cases: those of a conjunction are the products of its parts',
/// and a definition is one operation, with a few. Recursive, as deep as one definition's
/// formula, which holds one operation.
fn cases(f: &Formula) -> Option<Vec<Vec<Con>>> {
    match f {
        Formula::Con(c) => Some(vec![vec![c.clone()]]),
        Formula::Not(g) => {
            let Formula::Con(c) = &**g else {
                return None;
            };
            let below = Con::ge(&Lin::constant(-1), &c.lin);
            Some(match c.rel {
                Rel::Ge => vec![vec![below]],
                Rel::Eq => vec![vec![Con::ge(&c.lin, &Lin::constant(1))], vec![below]],
            })
        }
        Formula::And(gs) => gs
            .iter()
            .try_fold(vec![Vec::new()], |a, g| Some(cross(&a, &cases(g)?))),
        Formula::Or(gs) => {
            let mut out = Vec::new();
            for g in gs.iter() {
                out.extend(cases(g)?);
            }
            Some(out)
        }
    }
}

/// Each case of `a` with each of `b`. Time of the result.
fn cross(a: &[Vec<Con>], b: &[Vec<Con>]) -> Vec<Vec<Con>> {
    (a.iter())
        .flat_map(|x| b.iter().map(move |y| x.iter().chain(y).cloned().collect()))
        .collect()
}

/// What [`Summaries::local`] gives.
enum Local<'a> {
    /// The definitions read beside, and the summaries of those left below them with pairwise
    /// disjoint non-leaf cones.
    Ready(Vec<Formula>, Vec<&'a Summary>),
    /// What to make first.
    Need(Need),
    /// No summary is made.
    Unmade,
}

/// What to make first: the summary of a definition under a key, or the symbols of a
/// definition's cone.
enum Need {
    Summaries(Vec<(Key, Formula)>),
    Syms(Formula),
    SymsMany(Vec<Formula>),
    RootsMany(Vec<Formula>),
}

/// What [`Summaries::make`] gives: the summary, `None` where none is made, or what to make
/// first.
enum Made {
    Done(Option<Summary>, Option<Key>),
    First(Need),
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

    #[test]
    fn the_cases_of_a_definition_are_its_disjunctive_normal_form() {
        // `!(x >= 3)` is `x <= 2`; `!(x == 3)` is `x >= 4` or `x <= 2`; a conjunction of two
        // disjunctions has a case for each pair; a negated conjunction has no cases.
        let ge = con(&[(0, 1)], -3, Rel::Ge);
        let eq = con(&[(0, 1)], -3, Rel::Eq);
        let below = con(&[(0, -1)], 2, Rel::Ge);
        let above = con(&[(0, 1)], -4, Rel::Ge);
        let not = |c: &Con| Formula::Not(Shared::new(Formula::Con(c.clone())));
        assert_eq!(cases(&not(&ge)), Some(vec![vec![below.clone()]]));
        assert_eq!(
            cases(&not(&eq)),
            Some(vec![vec![above.clone()], vec![below.clone()]])
        );
        let y = con(&[(1, 1)], 0, Rel::Ge);
        let either = Formula::or(vec![Formula::Con(y.clone()), not(&eq)]);
        let both = Formula::and(vec![either.clone(), Formula::Con(ge.clone())]);
        let got = cases(&both).expect("cases");
        assert_eq!(got.len(), 3, "{got:?}");
        for case in [
            vec![y, ge.clone()],
            vec![above, ge.clone()],
            vec![below, ge.clone()],
        ] {
            assert!(got.iter().any(|g| {
                let (mut g, mut case) = (g.clone(), case.clone());
                g.sort();
                case.sort();
                g == case
            }));
        }
        let pair = Formula::and(vec![Formula::Con(ge), either]);
        assert_eq!(cases(&Formula::Not(Shared::new(pair))), None);
    }

    #[test]
    fn rows_the_others_imply_are_dropped_so_a_remainder_is_eliminated() {
        // The rows of `min(q5 div 2, x)` read beside the summary of `q5`'s link, `4·q5 <= x <=
        // 4·q5 + 3` with `x >= -1`: `x >= 2·q5` and `x >= q5` follow from these, and paired with
        // `x <= 4·q5 + 3` they leave the remainder `q7` of `q5 == 2·q6 + q7`, whose bounds then
        // have coefficients 4 and 2. Without them the projection onto `x` and `q6` is exact:
        // `8·q6 <= x <= 8·q6 + 7` and `x >= -1`. x is atom 0.
        let rows = vec![
            con(&[(5, 1), (6, -2), (7, -1)], 0, Rel::Eq),
            con(&[(7, 1)], 0, Rel::Ge),
            con(&[(7, -1)], 1, Rel::Ge),
            con(&[(0, -1), (5, 4)], 3, Rel::Ge),
            con(&[(0, 1)], 1, Rel::Ge),
            con(&[(0, 1), (5, -4)], 0, Rel::Ge),
            con(&[(0, 1), (5, -2)], 0, Rel::Ge),
            con(&[(0, 1), (5, -1)], 0, Rel::Ge),
        ];
        let keep = |b: &Atom| *b == a(0) || *b == a(6);
        let left = |out: &[Con]| out.iter().any(|c| c.lin.terms.keys().any(|b| !keep(b)));
        let whole = shadow_whole(&rows, &keep).expect("a point");
        assert!(left(&whole), "{whole:?}");
        let lean_rows = lean(rows.clone());
        assert_eq!(lean_rows.len(), rows.len() - 2, "{lean_rows:?}");
        let out = shadow_whole(&lean_rows, &keep).expect("a point");
        assert!(!left(&out), "{out:?}");
        // The projection holds at `x`, `q6` exactly where the rows hold for some `q5`, `q7`.
        let and = |rows: &[Con], x: i64, q: i64| {
            let mut f: Vec<Formula> = rows.iter().cloned().map(Formula::Con).collect();
            f.push(Formula::Con(con(&[(0, 1)], -x, Rel::Eq)));
            f.push(Formula::Con(con(&[(6, 1)], -q, Rel::Eq)));
            decide(&Formula::and(f))
        };
        for x in -20..=40 {
            for q in -4..=5 {
                assert_eq!(and(&rows, x, q), and(&out, x, q), "x = {x}, q6 = {q}");
            }
        }
        // A row that no other implies is kept, and a lone row too.
        let lone = vec![con(&[(0, 1)], 1, Rel::Ge)];
        assert_eq!(lean(lone.clone()), lone);
    }

    #[test]
    fn symbols_of_a_fork_include_every_input() {
        // `q2 = q0 + q1` reads `x` through `q0` and `y` through `q1`; `q3 = q0 + q2` reaches
        // `q0` twice. Each set holds the symbols of every input (cross-review of
        // LOAD-max-div-xr, round 2: the second input of a fork was left out).
        let (x, y) = (Atom::Sym("x".into()), Atom::Sym("y".into()));
        let eq = |l: Lin, r: Lin| Formula::And(Shared::new(vec![Formula::Con(Con::eq(&l, &r))]));
        let defs = [
            eq(Lin::atom(a(0)), Lin::atom(x.clone())),
            eq(Lin::atom(a(1)), Lin::atom(y.clone())),
            eq(Lin::atom(a(2)), lin(&[(0, 1), (1, 1)], 0)),
            eq(Lin::atom(a(3)), lin(&[(0, 1), (2, 1)], 0)),
        ];
        let mut summaries = Summaries::default();
        summaries.syms(defs[3].clone(), &|n| defs[n as usize].clone());
        for (i, want) in [
            (0, vec![&x]),
            (1, vec![&y]),
            (2, vec![&x, &y]),
            (3, vec![&x, &y]),
        ] {
            let got: Vec<&Atom> = summaries.syms[&Id::any(&defs[i])].iter().collect();
            assert_eq!(got, want, "q{i}");
        }
    }

    #[test]
    fn envelope_drops_the_bounds_under_the_others_of_their_form() {
        // `x >= 2^k * (q3 + q4) - 9 * 2^k`, k = 1 to 7: lines through one point, so the middle
        // ones lie under the steepest and the flattest. `decide` refuses to show it (k = 2 to 6
        // stay in `lean` without the envelope).
        let powers: Vec<Con> = (1..=7)
            .map(|k| {
                let m = 1i64 << k;
                con(&[(0, 1), (3, -m), (4, -m)], 9 * m, Rel::Ge)
            })
            .collect();
        assert_eq!(
            envelope(powers.clone()),
            vec![powers[0].clone(), powers[6].clone()]
        );
        // Of one slope the highest; upper bounds likewise (`x <= 2 * q1` under `x <= q1` and
        // `x <= 3 * q1`); the rows of other forms or other atoms kept.
        let rows = vec![
            con(&[(0, 1), (1, -2)], -3, Rel::Ge),
            con(&[(0, 1), (1, -2)], -5, Rel::Ge),
            con(&[(0, -1), (1, 1)], 0, Rel::Ge),
            con(&[(0, -1), (1, 3)], 0, Rel::Ge),
            con(&[(0, -1), (1, 2)], 0, Rel::Ge),
            con(&[(0, 1), (2, -2)], 0, Rel::Ge),
            con(&[(0, 1), (1, -2)], 0, Rel::Eq),
        ];
        let kept = envelope(rows.clone());
        let want = [1, 2, 3, 5, 6].map(|i| rows[i].clone());
        assert_eq!(kept, want);
        // Each line on the envelope is kept: `x >= 2 * q1 + 1` is above `x >= q1` and `x >= 3 *
        // q1 - 10` where they cross (q1 = 5).
        let hull = vec![
            con(&[(0, 1), (1, -1)], 0, Rel::Ge),
            con(&[(0, 1), (1, -2)], -1, Rel::Ge),
            con(&[(0, 1), (1, -3)], 10, Rel::Ge),
        ];
        assert_eq!(envelope(hull.clone()), hull);
    }

    #[test]
    fn merge_pieces_joins_intervals_whose_gap_has_no_point() {
        // `x == 0` and `x == 2` beside `x == 2 * y`: `x == 1` has no point there, so the two are
        // `0 <= x <= 2` beside it.
        let even = con(&[(0, 1), (1, -2)], 0, Rel::Eq);
        let at = |c: i64| con(&[(0, 1)], -c, Rel::Eq);
        let pieces = BTreeSet::from([vec![even.clone(), at(0)], vec![even.clone(), at(2)]]);
        let mut want = vec![
            even,
            con(&[(0, 1)], 0, Rel::Ge),
            con(&[(0, -1)], 2, Rel::Ge),
        ];
        want.sort();
        assert_eq!(merge_pieces(pieces), vec![want]);
        // Alone, `x == 1` is a point between them: the two stay apart.
        let pieces = BTreeSet::from([vec![at(0)], vec![at(2)]]);
        assert_eq!(merge_pieces(pieces.clone()).len(), 2);
        // Two wedges of `max(H div 2, x + y - 9)` parted at `x + 2 * y <= 18` and
        // `x + 2 * y >= 19` whose remaining rows imply each other merge into one piece.
        let h_eq = con(&[(2, 1), (0, -1), (1, -1)], 9, Rel::Eq);
        let p1 = vec![
            h_eq.clone(),
            con(&[(0, -1), (1, -1)], 9, Rel::Ge),
            con(&[(0, -1), (1, -2)], 18, Rel::Ge),
        ];
        let p2 = vec![
            h_eq.clone(),
            con(&[(0, 1), (1, 2)], -19, Rel::Ge),
            con(&[(0, -3), (1, -4)], 36, Rel::Ge),
        ];
        let merged = merge_pieces(BTreeSet::from([p1, p2]));
        assert_eq!(merged.len(), 1, "{merged:?}");
    }

    #[test]
    fn by_pairs_skips_a_pair_whose_constant_sum_shrunk_below_m_less_one() {
        // `u0 == (3 * v0 + y + 1) div 2` (`m = 2`: `3 * v0 + y - 2 * u0 + 1 >= 0` and
        // `-3 * v0 - y + 2 * u0 >= 0`), beside `u0 - 3 * v0 + 2 >= 0` and `-u0 + 3 * v0 >= 0`
        // (which `pairs` also sees as a pair for `v0` with `m = 3` and constant sum 2), plus
        // contradictory bounds `v0 >= 1` and `v0 <= 0`. Rewriting `u0` first turns the `m = 3`
        // pair into `-3 * v0 + y + 5 >= 0` and `3 * v0 - y >= 0`, whose constant sum is 5 !=
        // m - 1 = 2; `by_pairs` must skip it and not rewrite `v0 >= 1` and `v0 <= 0` into the
        // satisfiable `-2 <= y <= 0`.
        let rows = vec![
            con(&[(0, 3), (1, 1), (2, -2)], 1, Rel::Ge),
            con(&[(0, -3), (1, -1), (2, 2)], 0, Rel::Ge),
            con(&[(2, 1), (0, -3)], 2, Rel::Ge),
            con(&[(2, -1), (0, 3)], 0, Rel::Ge),
            con(&[(0, 1)], -1, Rel::Ge),
            con(&[(0, -1)], 0, Rel::Ge),
        ];
        let out = by_pairs(rows.clone(), &|v| *v == a(0) || *v == a(2));
        let sat = |rs: &[Con]| {
            decide(&Formula::and(
                rs.iter().cloned().map(Formula::Con).collect(),
            ))
        };
        assert_eq!(sat(&rows), Ok(false));
        assert_eq!(sat(&out), Ok(false), "{out:?}");
    }

    #[test]
    fn envelope_and_lean_cap_rays_by_form_bounds() {
        // `x >= 2^k * (r5 + q7) - 9 * 2^k` for k = 1 and 7, beside `x <= 7 * q7 + 6`,
        // `0 <= r5 <= 4` and `x <= 2 * (r5 + q7) - 17`: `r5 + q7 >= 10` has no integer point, so
        // `lean` caps the k = 7 ray by `r5 + q7 <= 9`, and `envelope` then drops any steeper ray.
        let rows = vec![
            con(&[(0, 1), (3, -2), (4, -2)], 18, Rel::Ge),
            con(&[(0, 1), (3, -128), (4, -128)], 9 * 128, Rel::Ge),
            con(&[(0, -1), (3, 2), (4, 2)], -17, Rel::Ge),
            con(&[(0, -1), (4, 7)], 6, Rel::Ge),
            con(&[(3, 1)], 0, Rel::Ge),
            con(&[(3, -1)], 4, Rel::Ge),
        ];
        let out = lean(rows);
        assert!(
            !out.iter()
                .any(|r| r.lin.terms.values().any(|c| c.abs() >= Int::from(128))),
            "{out:?}"
        );
    }

    #[test]
    fn merge_pieces_joins_pieces_whose_rests_hold_on_each_other() {
        // `y >= max(x + 3, 2 * x)` for `0 <= x <= 6`, cut at `x = 3` (cross-review of
        // LOAD-max-div-xr, round 2, I8): `y >= x + 3` for `x <= 3`, where `y >= 2 * x` holds
        // too, and `y >= 2 * x` for `x >= 4`, where `y >= x + 3` holds too. One piece holds both.
        let x_at_least = |c: i64| con(&[(0, 1)], -c, Rel::Ge);
        let x_at_most = |c: i64| con(&[(0, -1)], c, Rel::Ge);
        let above_x_plus_3 = con(&[(0, -1), (1, 1)], -3, Rel::Ge);
        let above_2x = con(&[(0, -2), (1, 1)], 0, Rel::Ge);
        let piece = |rest: &Con, lo: i64, hi: i64| {
            let mut p = vec![rest.clone(), x_at_least(lo), x_at_most(hi)];
            p.sort();
            p
        };
        let pieces = BTreeSet::from([piece(&above_x_plus_3, 0, 3), piece(&above_2x, 4, 6)]);
        let mut want = vec![
            above_x_plus_3.clone(),
            above_2x.clone(),
            x_at_least(0),
            x_at_most(6),
        ];
        want.sort();
        assert_eq!(merge_pieces(pieces), vec![want]);
        // Swapped, `y >= 2 * x` for `x <= 3` and `y >= x + 3` for `x >= 4`: `(0, 0)` is a point
        // of the first and of no piece holding both rests, so the two stay apart.
        let pieces = BTreeSet::from([piece(&above_2x, 0, 3), piece(&above_x_plus_3, 4, 6)]);
        assert_eq!(merge_pieces(pieces).len(), 2);
        // With a point between them, `x = 4` left out: they stay apart.
        let pieces = BTreeSet::from([piece(&above_x_plus_3, 0, 3), piece(&above_2x, 5, 6)]);
        assert_eq!(merge_pieces(pieces).len(), 2);
    }

    #[test]
    fn by_pairs_reads_no_row_through_a_pair_a_rewrite_has_loosened() {
        // `p == (y + 3 * q + 1) div 2` and `q == (p + 2) div 3`, with `q <= 0 && q >= 1`
        // (cross-review of LOAD-max-div-xr, round 2, Gemini's indicator sum): reading the rows
        // of `q`'s pair through `p`'s makes `y <= 3 * q <= y + 5`, which leaves `q` two values.
        // Read through that as a pair, `q <= 0 && q >= 1` became `-2 <= y <= 0`, a point
        // where the rows have none.
        let (p, q, y) = (0, 1, 2);
        let rows = vec![
            con(&[(y, 1), (q, 3), (p, -2)], 1, Rel::Ge),
            con(&[(p, 2), (y, -1), (q, -3)], 0, Rel::Ge),
            con(&[(p, 1), (q, -3)], 2, Rel::Ge),
            con(&[(q, 3), (p, -1)], 0, Rel::Ge),
            con(&[(q, -1)], 0, Rel::Ge),
            con(&[(q, 1)], -1, Rel::Ge),
        ];
        let out = by_pairs(rows, &|v| *v != a(y));
        assert_eq!(
            decide(&Formula::and(out.into_iter().map(Formula::Con).collect())),
            Ok(false)
        );
    }

    #[test]
    fn merge_pieces_checks_the_gap_below_a_neighbor_above_a_piece_unbounded_below() {
        // Cross-review of LOAD-max-div-xr, round 3 (Claude): `y >= x` for `x <= 5` (no lower
        // bound on `x`) and `y >= 2 * x - 10` for `x >= 10`: each rest holds on the other piece,
        // but `(7, 7)` holds both rests and lies in neither piece, so the two stay apart.
        // Mirrored in `x` too, so that each of the two pieces is the one put in first.
        let (x, y) = (0, 1);
        let at =
            |px: i64, py: i64| vec![con(&[(x, 1)], -px, Rel::Eq), con(&[(y, 1)], -py, Rel::Eq)];
        for s in [1i64, -1] {
            let mut p = vec![
                con(&[(x, -s)], 5, Rel::Ge),
                con(&[(y, 1), (x, -s)], 0, Rel::Ge),
            ];
            let mut q = vec![
                con(&[(x, s)], -10, Rel::Ge),
                con(&[(y, 1), (x, -2 * s)], 10, Rel::Ge),
            ];
            p.sort();
            q.sort();
            let out = merge_pieces(BTreeSet::from([p, q]));
            for piece in &out {
                let rows: Vec<Con> = piece.iter().cloned().chain(at(7 * s, 7)).collect();
                assert_eq!(
                    decide(&Formula::and(rows.into_iter().map(Formula::Con).collect())),
                    Ok(false),
                    "sign {s}: {out:?}"
                );
            }
        }
    }

    #[test]
    fn single_use_equations_of_one_shared_atom_are_dropped_in_linear_work() {
        // Cross-review of LOAD-max-div-xr, round 3 (Codex): `y_i == x` for i = 1..n. Counting
        // the uses of `x` left after each drop by a scan of its occurrence list read O(n²)
        // entries; a count kept per atom reads O(n). Limit for 8 times the rows: 24 times the
        // work.
        let work = |n: u32| {
            let rows = (1..=n)
                .map(|i| con(&[(0, 1), (i, -1)], 0, Rel::Eq))
                .collect();
            OCCURRENCE_VISITS.with(|v| v.set(0));
            assert!(without_free_pairs(rows).is_empty());
            OCCURRENCE_VISITS.with(|v| v.get())
        };
        let (small, large) = (work(100), work(800));
        assert!(
            large <= 24 * small,
            "occurrence visits {small} at 100 rows, {large} at 800"
        );
    }

    #[test]
    fn forms_of_a_piece_in_a_merge_are_made_once() {
        // Cross-review of LOAD-max-div-xr, round 3 (Codex): `x_i == 0` for every i and
        // `x_i == 2` for every i, r atoms: the rests differ on every form, so each of the r
        // forms tried reads the other piece's forms. Made again for each, O(r³) rows read; made
        // once when the piece is put in, O(r²). Limit for 8 times the atoms: 128 times the work
        // (64 for r², 512 for r³).
        let work = |r: u32| {
            let p = (0..r).map(|i| con(&[(i, 1)], 0, Rel::Eq)).collect();
            let q = (0..r).map(|i| con(&[(i, 1)], -2, Rel::Eq)).collect();
            REST_ROW_VISITS.with(|v| v.set(0));
            assert_eq!(merge_pieces(BTreeSet::from([p, q])).len(), 2);
            REST_ROW_VISITS.with(|v| v.get())
        };
        let (small, large) = (work(10), work(80));
        assert!(
            large <= 128 * small,
            "rest rows read {small} at 10 atoms, {large} at 80"
        );
    }

    #[test]
    fn envelope_lean_merge_and_decide_keep_the_integer_points_of_small_systems() {
        // Cross-review of LOAD-max-div-xr, round 3 (Codex): 180 random systems of five rows over
        // three atoms in the box [-2, 2]³, fixed seed. `envelope` and `lean` (rows forward and
        // reversed) keep exactly the integer points of the box, `merge_pieces` of two such
        // pieces keeps their union, and `decide_cons` agrees with the points. The control (the
        // box alone) must differ somewhere, so the comparison can fail.
        let holds = |rows: &[Con], xyz: [i64; 3]| {
            rows.iter().all(|r| {
                let mut v = r.lin.constant.clone();
                for (a, k) in &r.lin.terms {
                    let Atom::Aux(n) = a else { panic!("aux") };
                    v = &v + &(k * &Int::from(xyz[*n as usize]));
                }
                match r.rel {
                    Rel::Eq => v.is_zero(),
                    Rel::Ge => !v.is_negative(),
                }
            })
        };
        let mut seed = 789123u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            (seed >> 32) as i64
        };
        let mut control_differs = 0;
        for case in 0..180 {
            let mut box_rows = Vec::new();
            for n in 0..3 {
                box_rows.push(con(&[(n, 1)], 2, Rel::Ge));
                box_rows.push(con(&[(n, -1)], 2, Rel::Ge));
            }
            let mut pieces = Vec::new();
            for _ in 0..2 {
                let mut rows = box_rows.clone();
                for _ in 0..5 {
                    let ts: Vec<(u32, i64)> = (0..3)
                        .filter_map(|n| {
                            let k = next() % 7 - 3;
                            (k != 0).then_some((n, k))
                        })
                        .collect();
                    rows.push(con(&ts, next() % 9 - 4, Rel::Ge));
                }
                pieces.push(rows);
            }
            let mut reversed = pieces[0].clone();
            reversed.reverse();
            let outs = [
                envelope(pieces[0].clone()),
                lean(pieces[0].clone()),
                lean(reversed),
            ];
            let merged = merge_pieces(pieces.clone().into_iter().collect());
            let mut any = false;
            for x in -2..=2 {
                for y in -2..=2 {
                    for z in -2..=2 {
                        let xyz = [x, y, z];
                        let original = holds(&pieces[0], xyz);
                        any |= original;
                        for out in &outs {
                            assert_eq!(original, holds(out, xyz), "case {case} at {xyz:?}");
                        }
                        assert_eq!(
                            pieces.iter().any(|p| holds(p, xyz)),
                            merged.iter().any(|p| holds(p, xyz)),
                            "merge, case {case} at {xyz:?}"
                        );
                        if holds(&box_rows, xyz) != original {
                            control_differs += 1;
                        }
                    }
                }
            }
            assert_eq!(decide_cons(pieces[0].clone()), Ok(any), "case {case}");
        }
        assert!(control_differs > 0);
    }

    #[test]
    fn ray_cap_keeps_the_points_above_a_crossing() {
        // Cross-review of LOAD-max-div-xr, round 3 (Codex): `y >= 2 * (x + z)` and
        // `y >= 4 * (x + z) - 3` cross at `x + z == 3 / 2`; (y, x, z) = (5, 1, 1), on
        // `x + z == 2` above the crossing, holds both, and holds every row `lean` leaves.
        let rows = vec![
            con(&[(0, 1), (1, -2), (2, -2)], 0, Rel::Ge),
            con(&[(0, 1), (1, -4), (2, -4)], 3, Rel::Ge),
        ];
        for r in lean(rows) {
            let mut v = r.lin.constant;
            for (a, k) in r.lin.terms {
                let Atom::Aux(n) = a else { panic!("aux") };
                v = &v + &(&k * &Int::from([5, 1, 1][n as usize]));
            }
            assert!(!v.is_negative(), "a point of the rows was capped away");
        }
    }

    #[test]
    fn hull_check_keeps_a_strip_between_parallel_lines() {
        // Cross-review of LOAD-max-div-xr, round 3 (Codex): `2 * y <= x <= 2 * y + 1` with
        // `0 <= y <= 2` has the point x = y = 0.
        let rows = vec![
            con(&[(0, 1), (1, -2)], 0, Rel::Ge),
            con(&[(0, -1), (1, 2)], 1, Rel::Ge),
            con(&[(1, 1)], 0, Rel::Ge),
            con(&[(1, -1)], 2, Rel::Ge),
        ];
        assert_eq!(decide_cons(rows), Ok(true));
    }

    #[test]
    fn a_quotient_read_outside_its_pair_is_not_dropped() {
        // Cross-review of LOAD-max-div-xr, round 3 (Claude's control NC3): `q == x div 3` with
        // `q >= 5` and `x <= 10` has no point (q >= 5 makes x >= 15). The pair of `q` is read
        // by a third row, so it is not free; dropped, the rest would have points.
        let (x, q) = (0, 1);
        let rows = vec![
            con(&[(x, 1), (q, -3)], 0, Rel::Ge),
            con(&[(q, 3), (x, -1)], 2, Rel::Ge),
            con(&[(q, 1)], -5, Rel::Ge),
            con(&[(x, -1)], 10, Rel::Ge),
        ];
        assert_eq!(decide_cons(rows.clone()), Ok(false));
        assert_eq!(
            decide(&Formula::and(
                without_free_pairs(rows)
                    .into_iter()
                    .map(Formula::Con)
                    .collect()
            )),
            Ok(false)
        );
    }

    #[test]
    fn lean_keeps_the_same_rows_on_every_run() {
        // Several groups of lines `y >= m * (u + v) + b` of two-atom forms, which `lean` caps
        // group by group, each cap rewriting a row that the later groups' decisions read
        // (LOAD-max-div-xr I23: the groups came from a hash map, whose order changes between
        // maps). Each system is leaned 4 times, each run with new maps, and must give the
        // same rows. Atoms 0 and 1 are the `y`s, 2 to 5 the form atoms. Not red on the hash map:
        // each rewrite is implied by the rows, and these decisions are not refused, so the order
        // did not change the rows here; the ordered map makes the order fixed by construction.
        let mut seed = 4242u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut capped = 0;
        for _ in 0..30 {
            let mut rows = Vec::new();
            for n in 2..6 {
                rows.push(con(&[(n, 1)], next() % 4 + 1, Rel::Ge));
                rows.push(con(&[(n, -1)], next() % 9 + 1, Rel::Ge));
            }
            for y in 0..2u32 {
                for (u, v) in [(2u32, 3u32), (4, 5), (2, 4)] {
                    for _ in 0..3 {
                        let m = next() % 6 + 1;
                        rows.push(con(&[(y, 1), (u, -m), (v, -m)], next() % 20 - 10, Rel::Ge));
                    }
                }
                rows.push(con(&[(y, -1), (2, 1), (5, 1)], next() % 30, Rel::Ge));
            }
            let first = lean(rows.clone());
            capped += usize::from(first.iter().any(|r| !rows.contains(r)));
            for _ in 0..3 {
                assert_eq!(lean(rows.clone()), first, "{rows:?}");
            }
        }
        assert!(capped > 0, "no system had a capped ray");
    }

    #[test]
    fn a_ray_cap_refused_in_one_group_order_is_answered_in_another() {
        // Red witness for I23 (`group_lines` ordered by `BTreeMap` vs `HashMap`):
        // `yA = Aux(0)` (form `f_A = 2*z + x0 + x2`) and `yB = Aux(1)` (form `f_B = 2*z + x1 + x2`)
        // have no upper bounds, while `z = Aux(2)` starts with 1 lower bound (`z - x0 + 10 >= 0`)
        // and 2 unit upper bounds (`-z + x0 >= 0`, `-z + x1 >= 0`). Before either group is capped,
        // adding `f >= 1` gives `z` 2 lower bounds and 2 unit upper bounds (exact dark shadow,
        // 2 * 2 <= 4 rows), so `Omega` eliminates `z` and `live3` on `(x0, x1, x2)` (`Aux(3..=5)`)
        // answers `Ok(false)`. Whichever group runs first replaces its steeper ray with `-f >= 0`
        // (`-2*z - ... >= 0`, a non-unit upper bound on `z`); when the second group tries `f' >= 1`
        // (`+2*z + ... - 1 >= 0`), `z` has `+2*z` against `-2*z` (inexact dark shadow) and 2 * 3 >
        // 5 rows, so `decide_cons` refuses with `Err(Growth)`. Thus order `(A, B)` caps Group A and
        // leaves Group B uncapped, whereas order `(B, A)` caps Group B and leaves Group A uncapped;
        // `HashMap` visits both orders across runs.
        let base = vec![
            con(&[(3, 1)], 4, Rel::Ge),
            con(&[(3, -1)], 0, Rel::Ge),
            con(&[(4, 1)], 4, Rel::Ge),
            con(&[(4, -1)], 0, Rel::Ge),
            con(&[(5, 1)], 4, Rel::Ge),
            con(&[(5, -1)], 4, Rel::Ge),
            con(&[(3, -2), (4, 2), (5, 3)], 2, Rel::Ge),
            con(&[(3, -4), (4, -3), (5, -3)], -13, Rel::Ge),
            con(&[(3, 4), (4, -3), (5, -2)], 2, Rel::Ge),
            con(&[(3, 4), (4, 4), (5, 3)], 19, Rel::Ge),
            con(&[(2, 1), (3, -1)], 10, Rel::Ge),
            con(&[(2, -1), (3, 1)], 0, Rel::Ge),
            con(&[(2, -1), (4, 1)], 0, Rel::Ge),
            con(&[(0, 1), (2, -2), (3, -1), (5, -1)], 0, Rel::Ge),
            con(&[(0, 1), (2, -4), (3, -2), (5, -2)], 0, Rel::Ge),
            con(&[(1, 1), (2, -2), (4, -1), (5, -1)], 0, Rel::Ge),
            con(&[(1, 1), (2, -4), (4, -2), (5, -2)], 0, Rel::Ge),
        ];
        assert_eq!(decide_cons(base.clone()), Ok(true));

        let mut above_a_first = base.clone();
        above_a_first.push(con(&[(2, 2), (3, 1), (5, 1)], -1, Rel::Ge));
        assert_eq!(decide_cons(above_a_first), Ok(false));

        let mut above_b_first = base.clone();
        above_b_first.push(con(&[(2, 2), (4, 1), (5, 1)], -1, Rel::Ge));
        assert_eq!(decide_cons(above_b_first), Ok(false));

        let mut after_a = base.clone();
        after_a[14] = con(&[(2, -2), (3, -1), (5, -1)], 0, Rel::Ge);
        let mut above_b_after_a = after_a;
        above_b_after_a.push(con(&[(2, 2), (4, 1), (5, 1)], -1, Rel::Ge));
        assert_eq!(decide_cons(above_b_after_a), Err(Refusal::Growth));

        let mut after_b = base.clone();
        after_b[16] = con(&[(2, -2), (4, -1), (5, -1)], 0, Rel::Ge);
        let mut above_a_after_b = after_b;
        above_a_after_b.push(con(&[(2, 2), (3, 1), (5, 1)], -1, Rel::Ge));
        assert_eq!(decide_cons(above_a_after_b), Err(Refusal::Growth));

        let first = lean(base.clone());
        assert!(
            !first.contains(&con(&[(0, 1), (2, -4), (3, -2), (5, -2)], 0, Rel::Ge)),
            "ordered groups cap Group A and drop its steep ray: {first:?}"
        );
        assert!(
            first.contains(&con(&[(1, 1), (2, -4), (4, -2), (5, -2)], 0, Rel::Ge)),
            "Group B stays uncapped after Group A's cap blocks z elimination: {first:?}"
        );
        for _ in 0..40 {
            assert_eq!(lean(base.clone()), first);
        }
    }

    #[test]
    fn factors_of_a_product_keep_their_equations_and_division_pairs() {
        // Row-simplifier invariant for `product_factors` in `without_free_pairs`,
        // `without_free_pairs_for`, `fold_free_unit_pairs` and `remainders_as_pairs` (matching
        // `Bound::of`, `twins_merged` and `shift_free`): an atom occurring as a factor of an
        // `Atom::Product` is not dropped as single-use or folded out of its division pair.
        let prod_on_0 = Con {
            lin: Lin {
                terms: BTreeMap::from([(Atom::Product(Factor::Aux(0), Factor::Aux(1)), Int::ONE)]),
                constant: Int::from(-1),
            },
            rel: Rel::Eq,
        };
        let prod_other = Con {
            lin: Lin {
                terms: BTreeMap::from([(Atom::Product(Factor::Aux(2), Factor::Aux(1)), Int::ONE)]),
                constant: Int::from(-1),
            },
            rel: Rel::Eq,
        };
        let unit_eq = vec![con(&[(0, 1)], -2, Rel::Eq), prod_on_0.clone()];
        assert_eq!(without_free_pairs(unit_eq).len(), 2);
        assert_eq!(
            without_free_pairs(vec![con(&[(0, 1)], -2, Rel::Eq), prod_other.clone()]),
            vec![prod_other.clone()]
        );

        let div_pair = vec![
            con(&[(0, -2)], 5, Rel::Ge),
            con(&[(0, 2)], -4, Rel::Ge),
            prod_on_0.clone(),
        ];
        assert_eq!(without_free_pairs(div_pair.clone()).len(), 3);
        assert_eq!(without_free_pairs_for(div_pair, &|_| true).len(), 3);
        assert_eq!(
            without_free_pairs(vec![
                con(&[(0, -2)], 5, Rel::Ge),
                con(&[(0, 2)], -4, Rel::Ge),
                prod_other,
            ])
            .len(),
            1
        );

        let rem_eq = vec![
            con(&[(3, -2), (0, -1)], 5, Rel::Eq),
            con(&[(0, 1)], 0, Rel::Ge),
            con(&[(0, -1)], 1, Rel::Ge),
            prod_on_0,
        ];
        assert_eq!(remainders_as_pairs(&rem_eq, &|_| false).len(), 4);
    }

    #[test]
    fn merge_pieces_leans_the_rest_of_a_cross_merge() {
        // I27: 13 pieces `[t == k, u == 0, z + k * u >= 0]` (`k = 1..=13`) have pairwise-implied
        // distinct rests (`u == 0` makes `z + k * u >= 0` equivalent to `z >= 0`). Without `lean`
        // on the cross-rest merge, `joined` concatenates all 13 `z + k * u >= 0` rows into a
        // 16-row piece; with `lean`, redundant rows are dropped at each merge, leaving <= 4 rows.
        let pieces: BTreeSet<Vec<Con>> = (1..=13i64)
            .map(|k| {
                let mut p = vec![
                    con(&[(0, 1)], -k, Rel::Eq),
                    con(&[(1, 1)], 0, Rel::Eq),
                    con(&[(2, 1), (1, k)], 0, Rel::Ge),
                ];
                p.sort();
                p
            })
            .collect();
        let out = merge_pieces(pieces);
        assert_eq!(out.len(), 1, "{out:?}");
        assert!(
            out[0].len() <= 4,
            "unleaned rest grew to {} rows: {:?}",
            out[0].len(),
            out[0]
        );
    }

    #[test]
    fn merge_pieces_drops_sides_of_a_same_rest_merge() {
        // Same-rest `hit` must remove the merged piece's bounds from `sides` as well as `groups`:
        // `p1` (`x <= -3, x == 4*w + 1, y >= x`, `hi = -3`) and `p4` (`x >= 1, x == 4*w + 1,
        // y >= 2*x - 1`, `lo = 1`) have empty gap `-2 <= x <= 0` and mutually implied rests, while
        // `p2` (`x == 0, y == -100`, `hi = 0`) and `p3` (`1 <= x <= 2, y == -100`) merge by the
        // same-rest path into `0 <= x <= 2, y == -100` (`hi = 2`). If `p2`'s `hi = 0` stays in
        // `sides`, `uppers.range(..1).next_back()` for `p4` hits dead `hi = 0` instead of live
        // `hi = -3` and misses the cross-rest merge of `p1` and `p4`.
        let mod4 = con(&[(0, 1), (2, -4)], -1, Rel::Eq);
        let mut p1 = vec![
            con(&[(0, -1)], -3, Rel::Ge),
            mod4.clone(),
            con(&[(1, 1), (0, -1)], 0, Rel::Ge),
        ];
        let mut p2 = vec![con(&[(0, 1)], 0, Rel::Eq), con(&[(1, 1)], 100, Rel::Eq)];
        let mut p3 = vec![
            con(&[(0, 1)], -1, Rel::Ge),
            con(&[(0, -1)], 2, Rel::Ge),
            con(&[(1, 1)], 100, Rel::Eq),
        ];
        let mut p4 = vec![
            con(&[(0, 1)], -1, Rel::Ge),
            mod4,
            con(&[(1, 1), (0, -2)], 1, Rel::Ge),
        ];
        for p in [&mut p1, &mut p2, &mut p3, &mut p4] {
            p.sort();
        }
        let out = merge_pieces(BTreeSet::from([p1, p2, p3, p4]));
        assert_eq!(
            out.len(),
            2,
            "stale sides entry blocked cross-rest merge: {out:?}"
        );
    }
    #[test]
    fn r5_fold_unit_pairs_agree_with_bounded_integer_search() {
        fn holds(rs: &[Con], xyz: [i64; 3]) -> bool {
            rs.iter().all(|r| {
                let mut v = r.lin.constant.clone();
                for (a, k) in &r.lin.terms {
                    let Atom::Aux(n) = a else { panic!("aux") };
                    v = &v + &(k * &Int::from(xyz[*n as usize]));
                }
                if r.rel == Rel::Eq {
                    v.is_zero()
                } else {
                    !v.is_negative()
                }
            })
        }
        let mut seed = 0x8e4971u64;
        let mut rand = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut changed = 0;
        let mut control_caught = 0;
        // Box every input so exhaustive satisfiability is a complete oracle, even when a
        // modulus-one pair eliminates a different variable than the named quotient.
        for case in 0..180 {
            let m = 1 + rand() % 7;
            let (kx, ky, c) = (rand() % 7 - 3, rand() % 7 - 3, rand() % 11 - 5);
            let mut rs = vec![
                con(&[(0, kx), (1, ky), (2, -m)], c, Rel::Ge),
                con(&[(0, -kx), (1, -ky), (2, m)], m - 1 - c, Rel::Ge),
            ];
            // Omit explicit zero terms, as real Lin constructors do.
            for r in &mut rs {
                r.lin.terms.retain(|_, k| !k.is_zero());
            }
            for a in 0..3 {
                let b = if a == 2 { 30 } else { 3 };
                rs.push(con(&[(a, 1)], b, Rel::Ge));
                rs.push(con(&[(a, -1)], b, Rel::Ge));
            }
            rs.push(con(
                &[(2, if case % 2 == 0 { 1 } else { -1 }), (0, rand() % 5 - 2)],
                rand() % 9 - 4,
                Rel::Ge,
            ));
            rs.last_mut().unwrap().lin.terms.retain(|_, k| !k.is_zero());
            if case % 3 == 0 {
                // A second pair for the same quotient, including inconsistent pairs.
                let d = rand() % 5 - 2;
                rs.extend([
                    con(&[(1, 1), (2, -m)], d, Rel::Ge),
                    con(&[(1, -1), (2, m)], m - 1 - d, Rel::Ge),
                ]);
            }
            if case % 5 == 0 {
                rs.push(con(&[(2, 1), (1, -1)], rand() % 5 - 2, Rel::Eq));
            }
            let got = fold_free_unit_pairs(rs.clone(), &HashSet::new());
            changed += usize::from(got != rs);
            let sat = |rows: &[Con]| {
                (-3..=3).any(|x| (-3..=3).any(|y| (-30..=30).any(|q| holds(rows, [x, y, q]))))
            };
            let want = sat(&rs);
            assert_eq!(sat(&got), want, "case {case}: {rs:?} -> {got:?}");
            let mut rev = rs.clone();
            rev.reverse();
            assert_eq!(
                sat(&fold_free_unit_pairs(rev, &HashSet::new())),
                want,
                "reversed {case}"
            );
            // NC: forgetting the division pair while retaining its holders changes SAT.
            control_caught += usize::from(sat(&rs[2..]) != want);
        }
        assert!(changed > 0 && control_caught > 0);
        eprintln!("R5 fold cases=180 changed={changed} missing-pair-control={control_caught}");
    }

    fn r5_frontier_fixture(
        width: u32,
        depth: u32,
        shared: bool,
    ) -> (Summaries, Vec<Formula>, BTreeSet<Atom>) {
        let mut defs = Vec::new();
        let mut ends = BTreeSet::new();
        // A long common prefix and many private suffixes. Its leaves are functionally
        // determined symbols; non-leaf prefix nodes must still be recognized as shared.
        let prefix = if shared { depth } else { 0 };
        for i in 0..prefix {
            let input = if i == 0 {
                Lin::atom(Atom::Sym("shared".into()))
            } else {
                Lin::atom(a(i - 1))
            };
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(a(i)),
                &input.plus(&Lin::constant(1)),
            ))])));
        }
        for j in 0..width {
            for k in 0..depth {
                let n = defs.len() as u32;
                let input = if k > 0 {
                    Lin::atom(a(n - 1))
                } else if shared {
                    Lin::atom(a(prefix - 1))
                } else {
                    Lin::atom(Atom::Sym(format!("s{j}").into()))
                };
                defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                    &Lin::atom(a(n)),
                    &input.plus(&Lin::constant(1)),
                ))])));
                if k + 1 == depth {
                    ends.insert(a(n));
                }
            }
        }
        let def = |n: u32| defs[n as usize].clone();
        let mut sums = Summaries::default();
        for f in &defs {
            sums.syms(f.clone(), &def);
        }
        (sums, defs, ends)
    }

    #[test]
    #[ignore]
    fn r5_frontier_measurement() {
        let mut meter = crate::scaling::Meter::new();
        for (name, depth, shared) in [
            ("leaves", 1, false),
            ("private-chains", 4, false),
            ("shared-prefix", 20, true),
        ] {
            for n in [100, 800] {
                let (mut sums, defs, reads) = r5_frontier_fixture(n, depth, shared);
                let def = |n: u32| defs[n as usize].clone();
                let own = BTreeSet::new();
                // Warm only the requested summaries, never the decomposition. Both cold and
                // warm local calls are measured; the cost counter concerns one warm call.
                let mut cold_calls = 0;
                let cold = meter.work(|| {
                    loop {
                        cold_calls += 1;
                        match sums.local(&reads, &own, None, &[], &def) {
                            Local::Need(Need::RootsMany(fs)) => {
                                for f in fs {
                                    sums.roots(f, &def);
                                }
                            }
                            Local::Need(Need::Summaries(js)) => {
                                for (k, _) in js {
                                    sums.by.insert(
                                        k,
                                        Some(Summary {
                                            pieces: vec![Vec::new()],
                                        }),
                                    );
                                }
                            }
                            Local::Ready(_, _) => break,
                            _ => panic!("fixture must be decomposable"),
                        }
                    }
                });
                FRONTIER_VISITS.with(|v| v.set(0));
                let work = meter.work(|| {
                    assert!(matches!(
                        sums.local(&reads, &own, None, &[], &def),
                        Local::Ready(_, _)
                    ));
                });
                let visits = FRONTIER_VISITS.with(|v| v.get());
                eprintln!(
                    "R5 local {name} n={n} depth={depth} cold_calls={cold_calls} cold_instr={} warm_instr={} visits={visits}",
                    cold.units, work.units
                );
            }
        }
    }

    #[test]
    #[ignore]
    fn r5_parabola_rests_measurement() {
        let mut meter = crate::scaling::Meter::new();
        let sizes: Vec<i64> = std::env::var("R5_PARABOLA_SIZES")
            .unwrap_or("8,64".into())
            .split(',')
            .map(|s| s.parse().unwrap())
            .collect();
        for n in sizes {
            let ps: BTreeSet<Vec<Con>> = (0..n)
                .map(|i: i64| {
                    let mut p = vec![
                        con(&[(0, 1)], -i, Rel::Eq),
                        con(&[(1, 1), (0, -2 * i)], i * i, Rel::Ge),
                    ];
                    for r in &mut p {
                        r.lin.terms.retain(|_, k| !k.is_zero());
                    }
                    p.sort();
                    p
                })
                .collect();
            REST_ROW_VISITS.with(|v| v.set(0));
            let mut out = Vec::new();
            let w = meter.work(|| out = merge_pieces(ps));
            let visits = REST_ROW_VISITS.with(|v| v.get());
            assert_eq!(out.len(), 1);
            eprintln!(
                "R5 parabola n={n} instr={} rows={} rest_visits={visits}",
                w.units,
                out[0].len()
            );
            // All tangents are necessary in the old representation. Every integer vertex
            // must retain its original height; a row deleted blindly would admit i²-1.
            for i in 0..n {
                for y in [i * i - 1, i * i, i * i + 1] {
                    let holds = out[0].iter().all(|r| {
                        let z = &r.lin.constant
                            + &(&r.lin.terms.get(&a(0)).cloned().unwrap_or(Int::ZERO)
                                * &Int::from(i));
                        let z = &z
                            + &(&r.lin.terms.get(&a(1)).cloned().unwrap_or(Int::ZERO)
                                * &Int::from(y));
                        if r.rel == Rel::Eq {
                            z.is_zero()
                        } else {
                            !z.is_negative()
                        }
                    });
                    assert_eq!(holds, y >= i * i);
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn r5_folding_chain_measurement() {
        let mut meter = crate::scaling::Meter::new();
        for n in [100u32, 800] {
            let mut rows = Vec::new();
            for i in 1..=n {
                rows.push(con(&[(i - 1, 1), (i, -2)], 0, Rel::Ge));
                rows.push(con(&[(i - 1, -1), (i, 2)], 1, Rel::Ge));
            }
            rows.push(con(&[(n, 1)], 0, Rel::Ge));
            FOLD_ROW_VISITS.with(|v| v.set(0));
            let mut out = Vec::new();
            let w = meter.work(|| out = fold_free_unit_pairs(rows, &HashSet::new()));
            let visits = FOLD_ROW_VISITS.with(|v| v.get());
            eprintln!(
                "R5 folding-chain n={n} instr={} visits={visits} rows={}",
                w.units,
                out.len()
            );
            assert_eq!(out.len(), 1);
            assert_eq!(out[0], con(&[(0, 1)], 0, Rel::Ge));
        }
    }

    #[test]
    #[ignore]
    fn r5_shared_prefix_symbol_unions_measurement() {
        let mut meter = crate::scaling::Meter::new();
        for n in [100u32, 800] {
            let defs = r5_diamond_defs(n);
            let def = |n: u32| defs[n as usize].clone();
            let root = defs.last().unwrap().clone();
            let id = Id::any(&root);
            let mut sums = Summaries::default();
            let w = meter.work(|| sums.syms(root, &def));
            assert_eq!(sums.syms[&id].len(), 2 * n as usize + 1);
            assert_eq!(sums.cone[&id].len(), 3 * n as usize);
            eprintln!(
                "R5 diamond n={n} instr={} bytes={} symbols={} cone={}",
                w.units,
                w.bytes,
                sums.syms[&id].len(),
                sums.cone[&id].len()
            );
        }
    }

    fn r5_diamond_defs(n: u32) -> Vec<Formula> {
        let mut defs = Vec::new();
        let mut prev = None;
        for i in 0..n {
            let first = defs.len() as u32;
            let input =
                prev.map_or_else(|| Lin::atom(Atom::Sym("base".into())), |n| Lin::atom(a(n)));
            for branch in 0..2 {
                let own = Lin::atom(a(first + branch));
                let fresh = Lin::atom(Atom::Sym(format!("s{:08}", 2 * i + branch).into()));
                defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                    &own,
                    &input.plus(&fresh),
                ))])));
            }
            defs.push(Formula::And(Shared::new(vec![Formula::Con(con(
                &[(first + 2, 1), (first, -1), (first + 1, -1)],
                0,
                Rel::Eq,
            ))])));
            prev = Some(first + 2);
        }
        defs
    }

    #[test]
    fn r5_diamond_unions_scale() {
        let inputs = crate::scaling::inputs(100, |n| r5_diamond_defs(n as u32));
        crate::scaling::check_order(
            "symbol/cone unions through overlapping diamonds",
            100,
            1,
            |n| {
                let defs = &inputs[&n];
                let def = |n: u32| defs[n as usize].clone();
                let root = defs.last().unwrap().clone();
                let id = Id::any(&root);
                let mut sums = Summaries::default();
                sums.syms(root, &def);
                assert_eq!(sums.syms[&id].len(), 2 * n + 1);
                assert_eq!(sums.cone[&id].len(), 3 * n);
            },
        );
    }

    #[test]
    fn r5_independent_leaf_frontiers_scale() {
        let inputs = crate::scaling::inputs(100, |n| r5_frontier_fixture(n as u32, 1, false));
        crate::scaling::check_order("wide independent leaf frontier", 100, 1, |n| {
            let (sums, defs, reads) = &inputs[&n];
            let def = |n: u32| defs[n as usize].clone();
            assert!(matches!(
                sums.local(reads, &BTreeSet::new(), None, &[], &def),
                Local::Ready(_, _)
            ));
        });
    }

    #[test]
    fn r5_convex_vertical_rays_scale() {
        let inputs = crate::scaling::inputs(16, |n| {
            (0..n as i64)
                .map(|i| {
                    let mut ps = vec![
                        con(&[(0, 1)], -i, Rel::Eq),
                        con(&[(1, 1), (0, -2 * i)], i * i, Rel::Ge),
                    ];
                    for r in &mut ps {
                        r.lin.terms.retain(|_, k| !k.is_zero());
                    }
                    ps.sort();
                    ps
                })
                .collect::<BTreeSet<_>>()
        });
        crate::scaling::check_order("batch join of convex integer vertical rays", 16, 1, |n| {
            let out = merge_pieces(inputs[&n].clone());
            assert_eq!(out.len(), 1);
        });
    }

    #[test]
    fn r5_branch_roots_detect_exactly_the_nonleaf_intersections() {
        let mut state = 789213u64;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            state >> 32
        };
        for _ in 0..8 {
            let mut defs = Vec::new();
            for n in 0..60u32 {
                let rhs = if n < 3 {
                    Lin::atom(Atom::Sym(format!("s{n}").into()))
                } else {
                    Lin::atom(a(next() as u32 % n)).plus(&Lin::atom(a(next() as u32 % n)))
                };
                let f = if n % 7 == 0 {
                    Formula::And(Shared::new(vec![
                        Formula::Con(con(&[(n, 1)], 0, Rel::Ge)),
                        Formula::Con(con(&[(n, -1)], 3, Rel::Ge)),
                    ]))
                } else {
                    Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                        &Lin::atom(a(n)),
                        &rhs,
                    ))]))
                };
                defs.push(f);
            }
            let def = |n: u32| defs[n as usize].clone();
            let mut sums = Summaries::default();
            for f in &defs {
                sums.syms(f.clone(), &def);
            }
            for f in &defs {
                sums.roots(f.clone(), &def);
            }
            for f in &defs {
                for g in &defs {
                    let (f, g) = (Id::any(f), Id::any(g));
                    let full = sums.branch_cone[&f]
                        .iter()
                        .any(|x| sums.branch_cone[&g].contains(x));
                    let roots = sums.branch_roots[&f]
                        .iter()
                        .any(|x| sums.branch_roots[&g].contains(x));
                    assert_eq!(roots, full);
                }
            }
        }
    }

    #[test]
    fn r5_ray_potentials_require_totality_before_becoming_witnesses() {
        let x = Atom::Sym("x".into());
        let v = a(0);
        let eq = Formula::Con(Con::eq(&Lin::atom(v.clone()), &Lin::atom(x.clone())));
        let total = Formula::And(Shared::new(vec![eq.clone()]));
        let partial = Formula::And(Shared::new(vec![
            eq,
            Formula::Con(Con::ge(&Lin::atom(x), &Lin::constant(0))),
        ]));
        let ge = Formula::Con(Con::ge(&Lin::atom(v.clone()), &Lin::constant(100)));
        let le = Formula::Con(Con::ge(&Lin::constant(-100), &Lin::atom(v.clone())));
        let mut rays = Rays::default();
        assert!(rays.holds(&ge, &|_| total.clone()));
        assert!(rays.holds(&le, &|_| total.clone()));
        let mut rays = Rays::default();
        assert!(!rays.holds(&le, &|_| partial.clone()));
        assert_eq!(rays.total.get(&Id::any(&partial)), Some(&false));
        let zero = Formula::Con(con(&[(0, 0)], -1, Rel::Ge));
        assert!(!Rays::default().holds(&zero, &|_| total.clone()));
    }

    #[test]
    fn r5_batched_secants_keep_every_point_of_convex_vertical_rays() {
        let mut seed = 713731u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            (seed >> 33) as i64
        };
        for case in 0..80 {
            let n = 2 + next() % 9;
            let start = next() % 11 - 5;
            let mut h = next() % 11 - 5;
            let mut slope = next() % 7 - 3;
            let mut ps = BTreeSet::new();
            let mut hs = BTreeMap::new();
            for i in start..start + n {
                hs.insert(i, h);
                let mut p = vec![
                    con(&[(0, 1)], -i, Rel::Eq),
                    con(&[(1, 2), (0, -2 * next() % 5)], 0, Rel::Ge),
                ];
                // Different original slopes and non-unit y coefficients give the same
                // integer height after x is fixed. Duplicate abscissas test union-min.
                let k = p[1].lin.terms[&a(0)].clone();
                p[1].lin.constant = -&(&(&k * &Int::from(i)) + &Int::from(2 * h));
                for r in &mut p {
                    r.lin.terms.retain(|_, k| !k.is_zero());
                }
                p.sort();
                ps.insert(p);
                slope += next() % 3;
                h += slope;
            }
            let out = convex_integer_rays(&ps).unwrap_or_else(|| panic!("case {case}"));
            for x in start - 1..=start + n {
                let min = hs.get(&x).copied().unwrap_or(0);
                for y in min - 2..=min + 2 {
                    let holds = out.iter().all(|r| {
                        let mut value = r.lin.constant.clone();
                        for (a, k) in &r.lin.terms {
                            value =
                                &value + &(k * &Int::from(if *a == Atom::Aux(0) { x } else { y }));
                        }
                        if r.rel == Rel::Eq {
                            value.is_zero()
                        } else {
                            !value.is_negative()
                        }
                    });
                    assert_eq!(
                        holds,
                        hs.get(&x).is_some_and(|&h| y >= h),
                        "case {case} at {x},{y}"
                    );
                }
            }
        }
        // Concave and gapped sequences must stay on the general exact merge path.
        let p = |x: i64, h: i64| vec![con(&[(0, 1)], -x, Rel::Eq), con(&[(1, 1)], -h, Rel::Ge)];
        assert!(convex_integer_rays(&BTreeSet::from([p(0, 0), p(1, 2), p(2, 0)])).is_none());
        assert!(convex_integer_rays(&BTreeSet::from([p(0, 0), p(2, 4)])).is_none());
    }
    fn r5_actual_frontier_defs(width: u32, depth: u32, prefix: u32) -> (Vec<Formula>, Formula) {
        let mut defs = Vec::new();
        let mut sum = Lin::constant(0);
        for i in 0..prefix {
            let input = if i == 0 {
                Lin::atom(Atom::Sym("shared".into()))
            } else {
                Lin::atom(a(i - 1))
            };
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(a(i)),
                &input.plus(&Lin::constant(1)),
            ))])));
        }
        for i in 0..width {
            for j in 0..depth {
                let n = defs.len() as u32;
                let input = if j != 0 {
                    Lin::atom(a(n - 1))
                } else if prefix != 0 {
                    Lin::atom(a(prefix - 1))
                } else {
                    Lin::atom(Atom::Sym(format!("s{i}").into()))
                };
                defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                    &Lin::atom(a(n)),
                    &input.plus(&Lin::constant(1)),
                ))])));
                if j + 1 == depth {
                    sum = sum.plus(&Lin::atom(a(n)));
                }
            }
        }
        (
            defs,
            Formula::Con(Con {
                lin: sum,
                rel: Rel::Ge,
            }),
        )
    }

    #[test]
    #[ignore]
    fn r5_actual_wide_questions_measurement() {
        let mut meter = crate::scaling::Meter::new();
        for (name, depth, prefix) in [
            ("leaves", 1, 0),
            ("private", 4, 0),
            ("shared-prefix", 4, 200),
        ] {
            for n in [100, 800] {
                let (defs, q) = r5_actual_frontier_defs(n, depth, prefix);
                let def = |n: u32| defs[n as usize].clone();
                let mut ext = Extending::new();
                let mut answer = None;
                let w = meter.work(|| answer = Some(ext.defined(&q, &def)));
                assert_eq!(
                    answer,
                    Some(Answers {
                        holds: Ok(true),
                        fails: Ok(true)
                    })
                );
                eprintln!(
                    "R5 actual-frontier {name} width={n} depth={depth} prefix={prefix} nodes={} instr={} bytes={}",
                    defs.len(),
                    w.units,
                    w.bytes
                );
            }
        }
    }

    #[test]
    #[ignore]
    fn r5_actual_wide_questions_scale() {
        let inputs = crate::scaling::inputs(100, |n| r5_actual_frontier_defs(n as u32, 4, 0));
        crate::scaling::check_order(
            "cold questions over independent four-link chains",
            100,
            1,
            |n| {
                let (defs, q) = &inputs[&n];
                let def = |n: u32| defs[n as usize].clone();
                assert_eq!(
                    Extending::new().defined(q, &def),
                    Answers {
                        holds: Ok(true),
                        fails: Ok(true)
                    }
                );
            },
        );
    }
    #[test]
    fn r5_ray_certificates_have_direct_integer_witnesses() {
        enum Op {
            Input,
            Affine(usize, i64, i64),
            Div(usize, i64, i64),
            Abs(usize, i64),
            Max(usize, usize, i64),
        }
        let mut seed = 0xe721947u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed >> 32
        };
        let mut certificates = 0;
        for case in 0..64 {
            let mut ops = vec![Op::Input];
            let mut defs = Vec::new();
            for n in 0..7u32 {
                if n > 0 {
                    let input = (next() % u64::from(n)) as usize;
                    let other = (next() % u64::from(n)) as usize;
                    let c = (next() % 41) as i64 - 20;
                    ops.push(match next() % 4 {
                        0 => Op::Affine(input, (next() % 7) as i64 - 3, c),
                        1 => Op::Div(input, 1 + (next() % 7) as i64, c),
                        2 => Op::Abs(input, c),
                        _ => Op::Max(input, other, c),
                    });
                }
                let out = Lin::atom(a(n));
                let val = |i: usize, c: i64| Lin::atom(a(i as u32)).plus(&Lin::constant(c));
                let eq = |x: &Lin| Formula::Con(Con::eq(&out, x));
                let branch = |guard: Con, x: &Lin| {
                    Formula::And(Shared::new(vec![Formula::Con(guard), eq(x)]))
                };
                let f = match &ops[n as usize] {
                    Op::Input => {
                        Formula::And(Shared::new(vec![eq(&Lin::atom(Atom::Sym("x".into())))]))
                    }
                    Op::Affine(i, k, c) => {
                        Formula::And(Shared::new(vec![eq(&Lin::atom(a(*i as u32))
                            .times(*k)
                            .plus(&Lin::constant(*c)))]))
                    }
                    Op::Div(i, m, c) => {
                        let v = val(*i, *c);
                        let q = out.times(*m);
                        Formula::And(Shared::new(vec![
                            Formula::Con(Con::ge(&v, &q)),
                            Formula::Con(Con::ge(&q.plus(&Lin::constant(*m - 1)), &v)),
                        ]))
                    }
                    Op::Abs(i, c) => {
                        let v = val(*i, *c);
                        Formula::Or(Shared::new(vec![
                            branch(Con::ge(&v, &Lin::constant(0)), &v),
                            branch(Con::ge(&Lin::constant(-1), &v), &v.times(-1)),
                        ]))
                    }
                    Op::Max(i, j, c) => {
                        let left = val(*i, *c);
                        let right = val(*j, 0);
                        Formula::Or(Shared::new(vec![
                            branch(Con::ge(&left, &right), &left),
                            branch(Con::ge(&right, &left.plus(&Lin::constant(1))), &right),
                        ]))
                    }
                };
                defs.push(f);
            }
            let direct = |x: Int| {
                let mut values: Vec<Int> = Vec::new();
                for op in &ops {
                    let v = match op {
                        Op::Input => x.clone(),
                        Op::Affine(i, k, c) => &(&values[*i] * &Int::from(*k)) + &Int::from(*c),
                        Op::Div(i, m, c) => {
                            (&values[*i] + &Int::from(*c)).div_floor(&Int::from(*m))
                        }
                        Op::Abs(i, c) => (&values[*i] + &Int::from(*c)).abs(),
                        Op::Max(i, j, c) => (&values[*i] + &Int::from(*c)).max(values[*j].clone()),
                    };
                    values.push(v);
                }
                values.pop().unwrap()
            };
            let t = Int::from(1i128 << 120);
            let witnesses = [direct(t.clone()), direct(-&t)];
            let def = |n: u32| defs[n as usize].clone();
            let mut rays = Rays::default();
            for threshold in [
                Int::from(-(1i128 << 70)),
                Int::from(-10),
                Int::ZERO,
                Int::from(9),
                Int::from(1i128 << 70),
            ] {
                for k in [-3, -1, 1, 3] {
                    let row = Formula::Con(Con {
                        lin: Lin::atom(a(6)).times(k).plus(&Lin::constant(-&threshold)),
                        rel: Rel::Ge,
                    });
                    for negated in [false, true] {
                        let q = if negated {
                            Formula::negate(row.clone())
                        } else {
                            row.clone()
                        };
                        if rays.holds(&q, &def) {
                            certificates += 1;
                            assert!(
                                witnesses.iter().any(|v| {
                                    let value = &(v * &Int::from(k)) - &threshold;
                                    if negated {
                                        value.is_negative()
                                    } else {
                                        !value.is_negative()
                                    }
                                }),
                                "case {case} k={k} threshold={threshold} negated={negated}"
                            );
                        }
                    }
                }
            }
        }
        assert!(
            certificates > 40,
            "nonvacuous certificate coverage: {certificates}"
        );
        eprintln!(
            "R5 direct arbitrary-precision witness checks={certificates}, 64 seven-definition DAGs"
        );
    }
    fn r5_unbalanced_union_defs(n: u32) -> Vec<Formula> {
        let mut defs = Vec::new();
        for i in 0..n {
            let fresh = Lin::atom(Atom::Sym(format!("p{i}").into()));
            let rhs = if i == 0 {
                fresh
            } else {
                fresh.plus(&Lin::atom(a(i - 1)))
            };
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(a(i)),
                &rhs,
            ))])));
        }
        let mut rhs = Lin::atom(a(n - 1));
        for i in 0..n {
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(a(n + i)),
                &Lin::atom(Atom::Sym(format!("q{i}").into())),
            ))])));
            rhs = rhs.plus(&Lin::atom(a(n + i)));
        }
        defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
            &Lin::atom(a(2 * n)),
            &rhs,
        ))])));
        defs
    }
    fn r5_unequal_shared_frontier(n: u32) -> (Summaries, Vec<Formula>, BTreeSet<Atom>) {
        let mut defs = Vec::new();
        let mut ends = BTreeSet::new();
        for i in 0..n {
            let rhs = if i == 0 {
                Lin::atom(Atom::Sym("x".into()))
            } else {
                Lin::atom(a(i - 1)).plus(&Lin::constant(1))
            };
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(a(i)),
                &rhs,
            ))])));
        }
        for i in 0..n {
            let mut parent = n - 1;
            for _ in 0..1 + i % 2 {
                let k = defs.len() as u32;
                defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                    &Lin::atom(a(k)),
                    &Lin::atom(a(parent)).plus(&Lin::constant(1)),
                ))])));
                parent = k;
            }
            ends.insert(a(parent));
        }
        let def = |n: u32| defs[n as usize].clone();
        let mut sums = Summaries::default();
        for f in &defs {
            sums.syms(f.clone(), &def);
        }
        loop {
            match sums.local(&ends, &BTreeSet::new(), None, &[], &def) {
                Local::Need(Need::RootsMany(fs)) => {
                    for f in fs {
                        sums.roots(f, &def);
                    }
                }
                Local::Need(Need::Summaries(js)) => {
                    for (k, _) in js {
                        sums.by.insert(
                            k,
                            Some(Summary {
                                pieces: vec![Vec::new()],
                            }),
                        );
                    }
                }
                Local::Ready(_, _) => break,
                _ => panic!("valid fixture"),
            }
        }
        (sums, defs, ends)
    }
    #[test]
    #[ignore]
    fn r5_second_adversaries_measurement() {
        let mut meter = crate::scaling::Meter::new();
        for n in [100, 800] {
            let defs = r5_unbalanced_union_defs(n);
            let def = |n: u32| defs[n as usize].clone();
            let mut sums = Summaries::default();
            let work = meter.work(|| sums.syms(defs.last().unwrap().clone(), &def));
            let id = Id::any(defs.last().unwrap());
            assert_eq!(sums.syms[&id].len(), 2 * n as usize);
            eprintln!(
                "R5 unbalanced-union n={n} nodes={} instr={} bytes={}",
                defs.len(),
                work.units,
                work.bytes
            );
            let (sums, defs, reads) = r5_unequal_shared_frontier(n);
            let def = |n: u32| defs[n as usize].clone();
            FRONTIER_VISITS.with(|v| v.set(0));
            let work = meter.work(|| {
                assert!(matches!(
                    sums.local(&reads, &BTreeSet::new(), None, &[], &def),
                    Local::Ready(_, _)
                ))
            });
            eprintln!(
                "R5 unequal-shared-frontier n={n} nodes={} instr={} bytes={} visits={}",
                defs.len(),
                work.units,
                work.bytes,
                FRONTIER_VISITS.with(|v| v.get())
            );
        }
    }
    #[test]
    fn r5_unbalanced_unions_scale() {
        let inputs = crate::scaling::inputs(100, |n| r5_unbalanced_union_defs(n as u32));
        crate::scaling::check_order(
            "one large persistent set beside independent singleton inputs",
            100,
            1,
            |n| {
                let defs = &inputs[&n];
                let def = |n: u32| defs[n as usize].clone();
                let mut sums = Summaries::default();
                sums.syms(defs.last().unwrap().clone(), &def);
            },
        );
    }
    #[test]
    fn r5_unequal_shared_frontiers_scale() {
        let inputs = crate::scaling::inputs(100, |n| r5_unequal_shared_frontier(n as u32));
        crate::scaling::check_order(
            "unequal-height frontiers above a shared prefix",
            100,
            1,
            |n| {
                let (sums, defs, reads) = &inputs[&n];
                let def = |n: u32| defs[n as usize].clone();
                assert!(matches!(
                    sums.local(reads, &BTreeSet::new(), None, &[], &def),
                    Local::Ready(_, _)
                ));
            },
        );
    }

    #[test]
    fn r5_directed_shared_unions_equal_elementwise_union() {
        let mut seed = 13729291u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed >> 32
        };
        for _ in 0..120 {
            let base: imbl::OrdSet<i64> = (0..160).filter(|_| next() % 3 != 0).collect();
            let mut sets = Vec::new();
            let mut expected = BTreeSet::new();
            for i in 0..8 {
                let mut set = if i % 2 == 0 {
                    base.clone()
                } else {
                    imbl::OrdSet::new()
                };
                for _ in 0..next() % 40 {
                    set.insert((next() % 300) as i64);
                }
                if i % 3 == 0 {
                    for x in 0..80 {
                        set.remove(&x);
                    }
                }
                expected.extend(set.iter().copied());
                sets.push(Arc::new(set));
            }
            let mine = [-1, 301];
            expected.extend(mine);
            let actual = shared_set_union(sets.iter().collect(), mine);
            assert_eq!(actual.iter().copied().collect::<BTreeSet<_>>(), expected);
        }
    }
    #[test]
    fn r5_ancestor_union_matches_pairwise_containment() {
        let mut seed = 917373u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed >> 32
        };
        let mut defs = Vec::new();
        for n in 0..100u32 {
            let rhs = if n == 0 {
                Lin::atom(Atom::Sym("x".into()))
            } else {
                Lin::atom(a((next() % u64::from(n)) as u32))
                    .plus(&Lin::atom(a((next() % u64::from(n)) as u32)))
            };
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(a(n)),
                &rhs,
            ))])));
        }
        let def = |n: u32| defs[n as usize].clone();
        let mut sums = Summaries::default();
        for f in &defs {
            sums.syms(f.clone(), &def);
        }
        for _ in 0..80 {
            let ids: BTreeSet<usize> = (0..20).map(|_| (next() % 100) as usize).collect();
            let fs: Vec<Def> = ids
                .into_iter()
                .map(|n| Def::of(defs[n].clone(), &def).unwrap())
                .collect();
            let union = frontier_ancestors(&fs, &sums.cone);
            for f in &fs {
                let expected = fs
                    .iter()
                    .any(|g| g.id != f.id && sums.cone[&g.id].contains(&f.id));
                assert_eq!(union.contains(&f.id), expected);
            }
        }
    }
    #[test]
    fn r5_reflection_rejection_is_keyed_by_the_queried_output() {
        let x = Lin::atom(Atom::Sym("x".into()));
        let root = Formula::Or(Shared::new(vec![
            Formula::And(Shared::new(vec![
                Formula::Con(Con::eq(&Lin::atom(a(0)), &x)),
                Formula::Con(Con::eq(&Lin::atom(a(1)), &x)),
            ])),
            Formula::And(Shared::new(vec![
                Formula::Con(Con::eq(&Lin::atom(a(0)), &x.times(-1))),
                Formula::Con(Con::eq(&Lin::atom(a(1)), &x)),
            ])),
        ]));
        let def = |_| root.clone();
        let reflected = Formula::Con(Con::ge(&Lin::atom(a(0)), &Lin::constant(100)));
        let identity = Formula::Con(Con::ge(&Lin::atom(a(1)), &Lin::constant(100)));
        assert!(Rays::default().holds(&identity, &def));
        let mut warm = Rays::default();
        assert!(!warm.holds(&reflected, &def));
        assert!(
            warm.holds(&identity, &def),
            "one output's reflection trigger must not reject another output's certificate"
        );
    }
    #[test]
    fn r5_a_merge_with_no_pair_does_no_quadratic_index_work() {
        assert!(merge_pieces(BTreeSet::new()).is_empty());
        let impossible = vec![Con {
            lin: Lin::constant(1),
            rel: Rel::Eq,
        }];
        assert_eq!(
            merge_pieces(BTreeSet::from([impossible.clone()])),
            vec![impossible]
        );
        let inputs = crate::scaling::inputs(100, |n| {
            let piece: Vec<Con> = (0..n as u32).map(|i| con(&[(i, 1)], 0, Rel::Ge)).collect();
            BTreeSet::from([piece])
        });
        crate::scaling::check_order(
            "a singleton union with many distinct row forms",
            100,
            1,
            |n| {
                let before = inputs[&n].clone();
                let expected: Vec<_> = before.iter().cloned().collect();
                assert_eq!(merge_pieces(before), expected);
            },
        );
    }
}
