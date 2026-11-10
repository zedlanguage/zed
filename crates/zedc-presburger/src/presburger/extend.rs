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
/// symbols the definitions each definition reaches read ([`Summaries::syms`]).
#[derive(Default)]
struct Summaries {
    by: HashMap<Key, Option<Summary>>,
    syms: HashMap<Id, Arc<imbl::OrdSet<Atom>>>,
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
    /// Every atom of `pieces`.
    atoms: BTreeSet<Atom>,
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
    if let Some(d) = sums.read(&f, def)
        && let Ok(b) = decide(&with(&d, f.clone()))
    {
        return Ok(b);
    }
    decided(&with(&reached(&f, def), f))
}

impl Summaries {
    /// The definitions `f` reaches, in place of all of them, for a question asked of `f`: the
    /// definitions [`Summaries::local`] reads beside `f`, with the summary of the one left
    /// below them, which keeps every atom of its cone that `f` or they read. `None` where a
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
                    beside.extend(below.map(Summary::rows));
                    return Some(beside);
                }
            }
        }
    }

    /// Makes what `n` names: a summary, with those below it first, or a set of symbols.
    fn made(&mut self, n: Need, def: &dyn Fn(u32) -> Formula) {
        match n {
            Need::Summary(k, g) => self.summary(k, g, def),
            Need::Syms(h) => self.syms(h, def),
        }
    }

    /// The summary of the definition `g` under the key `k`, made after those it is made from,
    /// each made once and remembered: an explicit stack, since the path is as deep as the
    /// chain of definitions. A summary needed while it is being made (a cycle, which a scope's
    /// numbering does not make) is not made.
    // Complexity tradeoff: naive version, each question decided with every definition it
    // reaches, so separate tests over the n links of one chain read O(n²) definitions in all.
    // Used: the summary of each definition, made from the one below it, so the tests read O(n)
    // rows in all (LOAD-chain-sep), for links that are conjunctions of constraints, cases of
    // one (an `if`, `min`, `max`, `abs`, `!=`: one piece for each case and each piece below,
    // those with no point dropped and those written alike kept once), and that read the
    // variables of several definitions (`min(H div 2, H div 3 + 1)`: those read beside the
    // link down to one whose cone holds the rest, [`Summaries::local`]); and for questions
    // that read two variables on one path (`h{i}(x: x) > h1(x: x)`: the lower kept in the
    // higher's key) (LOAD-chain-sep-rest). A summary keeps only the variables of its
    // definition that others read, so the remainder of `(2 * H) div 3` is projected out with
    // `H` and leaves no congruence. A piece is projected with [`shadow_whole`], which
    // eliminates an atom however many rows that makes, and where that leaves an atom, again
    // without the rows the others imply ([`lean`]: `min(H div 2, x)`). Measured from 25 to
    // 200 links, 8.1 to 10.0 times the instructions for each shape (limit 14.5); seconds at
    // 50 and 100 links before (load about 35): `if H > 3 { H div 2 } else { H + 1 }` 3.35 and
    // 20.2, `abs(H - 5) div 2` 3.06 and 18.0, `min(H div 2, H div 3 + 1)` 18.5 and over 60;
    // now 0.04, 0.05 and 0.10 at 50 links and 0.39, 0.47 and 0.97 at 400.
    // A product of variables (`H * x`, the `x * q` of a `div` by a variable) is an atom of its
    // own in the pieces, as the solver reads it ([`decide`]), kept in a key where its factors
    // are (LOAD-chain-sep-nonlinear): 8.3 times the instructions from 25 to 200 links for
    // `H div x`, against 74.5 times from 10 to 80 before. Values that are no union of
    // polyhedra without a remainder of a kept atom (`max(H div 2, x - 9)` keeping `x` holds
    // where `x - 10 <= 2 * (x div 8)`) are summarized with the quotients they need kept in
    // the pieces (LOAD-max-div-xr): each row holding a quotient to be projected out with
    // coefficient 1 or -1 is read through its division pair ([`by_pairs`]), so the
    // projection meets the quotient in the pair alone; a quotient of kept atoms that another
    // row holds with a coefficient above 1, and the symbols under a kept quotient by more
    // than 1, stay in the piece ([`kept_quotients`]), as does a symbol the projection
    // leaves, all read existentially with the rest; where the projection still leaves an
    // atom, the piece is projected again keeping every symbol of its rows and every variable
    // of a definition that reads symbols alone (`x mod 3`; [`Summaries::key`]), which mean
    // the same at every link; [`lean`] runs on every piece, after [`envelope`] keeps, of the
    // bounds `y >= a * f + b` of one form, only those on the upper envelope over the form's
    // bounds (the bounds `x >= 2^k * (q3 + q4) - 9 * 2^k` piling up at each link of `max(H div
    // 2, x mod 5 + x div 7 - 9)`, which `decide` refuses to compare, and whose steepest ray
    // [`lean`] caps by `q3 + q4 <= 9` where `q3 + q4 >= 10` has no point in the piece); and
    // pieces equal but for one interval of one form are merged where the intervals touch or the
    // gap between them has no point, as are neighbors on one form whose rests differ where each
    // rest holds on the other ([`merge_pieces`]), so the values of `h{i}`, `max(x div 2^i, x -
    // 9)`, stay two pieces.
    // Instructions from 10 to 160 links, doubling: `max(H div 2, x - 9)` 0.056, 0.119,
    // 0.245, 0.500 and 1.02 G (exponents 1.10, 1.04, 1.03, 1.03), against 0.16, 0.72, 3.68
    // and 21.3 G from 10 to 80 before (2.15, 2.35, 2.53); `max(H div 2, x div 3 - 9)` 0.41
    // to 10.1 G (1.37, 1.15, 1.07, 1.05), against n^4.7 before; `max(H div 2, x mod 3 - 9)`
    // 0.22 to 3.96 G (1.06, 1.03, 1.02, 1.05), against 12.8 and 138 G at 10 and 20 before
    // (n^3.4); `max(H - 1, x mod 5 + x div 7 - 9)` 0.63 to 5.8 G from 10 to 80 (1.14, 1.07,
    // 1.01), against n^2.0 without the gap test; `max(H div 2, x div 5 + x div 7 - 9)` 1.07,
    // 1.87, 3.48, 6.70 and 13.5 G from 10 to 160 (0.81, 0.89, 0.95, 1.01), against 7.6 to 356 G
    // from 10 to 80 (n^2.4) with a leaf quotient left after the projection read only after
    // [`lean`] (one quotient was multiplied out of the piece and the other kept); twelve other
    // `max`, `min` and `if` chains 1.01 to 1.10 from 80 to 160. `max(H div 2, x mod 5 + x div
    // 7 - 9)` gets summaries of seven pieces at most: 1.79, 3.35, 7.10, 18.0 and 60.9 G from
    // 10 to 160 links (0.91, 1.08, 1.35, 1.75), against 6.7 to 316 G from 10 to 80 (n^2.4)
    // before that retry, the ray cap in [`lean`] and [`decide_cons`]; still above n log n from
    // 80 to 160, open, LOAD-max-div-bits. Tradeoffs: no
    // summary is made, and the question is decided with every definition it reaches as
    // before, O(n) for each and O(n²) or worse over the chain, for a piece whose projection
    // leaves any other atom outside the key: values that need a remainder modulo m^i at depth
    // i (`(3 * H + 1) div 2`, `(5 * H + 2) div 3`, `H div 2 + H div 3`: n^2 to n^3.5 from 10
    // to 40 links, as before), whose exact pieces are shown to grow exponentially with depth
    // (round 1 for `(3 * H) div 2`, round 2 for the three), and `H mod 7 + H`, whose values
    // have period 7 and at most seven pieces but whose lowering adds one remainder a link to
    // the key (open). Keeping such a quotient too was tried and made
    // them slower, n^3.1 to n^4.5, its rows growing at each link. `max((3 * H) div 2, x - 9)` is
    // summarized but its pieces grow with the depth: n^2.4 to n^2.7 from 10 to 40 links (n^3.7
    // from 5 to 10 before). Also a definition whose formula holds a negation of more than one
    // constraint.
    // The pieces of a summary are merged only where written alike, equal but for one
    // interval with no point between, or neighbors whose rests hold on each other, so a link
    // whose values on the kept atoms take a new
    // shape at each depth keeps O(depth) pieces and the chain O(n²). Two definitions read
    // together whose cones are apart are read beside each other down to where they meet, O(their depth). The
    // symbols of each definition's cone are a persistent set made once for it, sharing the
    // largest input's tree, so a chain whose links each read a new symbol costs O(n log n) time
    // and storage; the other inputs' sets of a definition of several are still visited. The
    // coefficients of a summary are those of the composed definitions (`2^i` after i halvings
    // in `min(H div 2, x)`), so its numbers have O(i) bits; the solver's own elimination of
    // the whole chain makes the same numbers. Trigger: these definitions in a chain of
    // separate tests. Tests
    // `l01_38_presburger::one_scope::summaries_of_definitions_give_the_answers_of_the_definitions`,
    // which checks the answers against the definitions decided whole,
    // `summaries_of_max_min_div_chains_give_the_values_of_the_chains`, which checks the
    // values of sixteen `max`, `min` and `div` chains against integer arithmetic, and the
    // `separate_*_scale` tests there, which measure each shape; COMPLEXITY.md rows
    // LOAD-chain-sep, LOAD-chain-sep-rest and LOAD-max-div-xr. A complete solution keeps
    // congruences in the pieces (rows with a modulus, as the Omega test's projection keeps
    // them, or the splinters of its exact shadow), merges pieces where one holds another (a
    // test of inclusion between unions of polyhedra over the integers, co-NP-hard in
    // general), and keeps products as a piecewise polynomial form.
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
                Made::First(Need::Summary(j, h)) if !open.contains(&j) => stack.push((j, h)),
                Made::First(Need::Syms(h)) => self.syms(h, def),
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
        let (beside, below) = match self.local(&d.reads, &own, Some(d.own[0]), &k.1, def) {
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
        let below_pieces = below.map_or(&alone[..], |s| &s.pieces[..]);
        let mut pieces: BTreeSet<Vec<Con>> = BTreeSet::new();
        let mut all_wide = true;
        for c in &all {
            'piece: for p in below_pieces {
                let mut rows: Vec<Con> = c.iter().chain(p).cloned().collect();
                rows.sort();
                rows.dedup();
                if decide_cons(rows.clone()) == Ok(false) {
                    continue 'piece;
                }
                // The atoms kept beside the key: those whose elimination needs a remainder of a
                // kept atom ([`kept_quotients`]). They stay in the piece, read as any value.
                let more =
                    kept_quotients(&remainders_as_pairs(&rows, &|a| key.contains(a)), &|a| {
                        key.contains(a)
                    });
                let syms: HashSet<&Atom> = (rows.iter())
                    .flat_map(|c| c.lin.terms.keys())
                    .filter(|a| matches!(a, Atom::Sym(_)) || leaf(a))
                    .collect();
                let mut wide = false;
                let out = loop {
                    let keep = |a: &Atom| {
                        key.contains(a) || more.contains(a) || (wide && syms.contains(a))
                    };
                    let elim = |a: &Atom| !keep(a);
                    let Some(mut out) = shadow_whole(&by_pairs(rows.clone(), &elim), &keep) else {
                        continue 'piece;
                    };
                    out = envelope(out);
                    // Before that, the rows the projection made are read through their division
                    // pairs again ([`by_pairs`]), which leaves the projection one atom fewer to
                    // eliminate across coefficients above 1.
                    let left = |out: &[Con]| (out.iter()).any(|c| c.lin.terms.keys().any(&elim));
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
                    // A row the others imply may pair with a remainder's bound so that the dark
                    // shadow is not the real one (`x >= 2 * q` beside `x >= 4 * q` and `x >= -1`,
                    // with `4 * r` on both sides of `x`): such rows are dropped, and the piece
                    // projected again.
                    if left(&out) {
                        match shadow_whole(&lean(out), &keep) {
                            Some(o) => out = o,
                            None => continue 'piece,
                        }
                    }
                    // A symbol left (`x` of `2 * x == q + 9`, whose projection is a congruence of
                    // `q`) is kept, read as any value: the symbols of a chain are its inputs, read
                    // through the key. Any other atom left leaves no summary.
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
                        return Made::Done(None, None);
                    }
                    if !wide
                        || kept_quotients(
                            &remainders_as_pairs(&rows, &|a| key.contains(a) || syms.contains(a)),
                            &|a| key.contains(a) || syms.contains(a),
                        ) != more
                    {
                        all_wide = false;
                    }
                    break out;
                };
                let mut out = lean(out);
                out.sort();
                out.dedup();
                pieces.insert(out);
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
                    self.local(&d.reads, &own, Some(d.own[0]), &wide_atoms, def),
                    Local::Ready(b2, s2)
                        if b2 == beside && s2.map(std::ptr::from_ref) == below.map(std::ptr::from_ref)
                ))
            .then_some((k.0, wide_atoms))
        } else {
            None
        };
        Made::Done(
            Some(Summary {
                pieces: pieces.into_iter().collect(),
                atoms,
            }),
            extra,
        )
    }

    /// The definitions read beside `reads`, the atoms of a definition whose own variables are
    /// `own`, the first numbered `first`, or of a question (`first` none), and the summary of
    /// the one definition left below them, whose key keeps `keep` too: the definitions of the
    /// variables `reads` reads are a frontier, and while it holds two or more, the one with the
    /// highest numbers is read beside, its inputs joining the frontier, unless the others are
    /// all in its cone, which its summary keeping their variables shows (their variables are
    /// in it); where its summary shows some are not, those are read beside in its place, so
    /// that what is read does not depend on the order the definitions were numbered in; so
    /// that a question reading two variables on one path (`h{i}(x: x) > h1(x: x)`)
    /// reads the higher's summary alone, and a link reading two definitions over one input
    /// (`min(H div 2, H div 3 + 1)`) reads them beside it down to the input. The conjunction of
    /// `reads`'s formula, those beside it and the summary below, projected onto the atoms of
    /// `own`, `keep` and `reads`, is then that of all the definitions it reaches: the summary
    /// keeps every atom of its cone the others read, and every other definition reached is in
    /// its cone or beside. Time of the definitions read beside and of the summaries looked up.
    fn local<'a>(
        &'a self,
        reads: &BTreeSet<Atom>,
        own: &BTreeSet<Atom>,
        first: Option<u32>,
        keep: &[Atom],
        def: &dyn Fn(u32) -> Formula,
    ) -> Local<'a> {
        let mut beside: Vec<Def> = Vec::new();
        // By the highest number each defines.
        let mut frontier: BTreeMap<u32, Def> = BTreeMap::new();
        let mut seen: HashSet<Id> = HashSet::new();
        let ins: Vec<u32> = reads.iter().flat_map(auxes).collect();
        if !enter(&ins, own, first, def, &mut seen, &mut frontier) {
            return Local::Unmade;
        }
        while let Some((top, h)) = frontier.pop_last() {
            if frontier.is_empty() {
                let k = match self.key(&h, reads, own, keep, &beside, def) {
                    Ok(k) => k,
                    Err(n) => return Local::Need(n),
                };
                return match self.by.get(&k) {
                    None => Local::Need(Need::Summary(k, h.f)),
                    Some(None) => Local::Unmade,
                    Some(Some(s)) => {
                        Local::Ready(beside.into_iter().map(|d| d.f).collect(), Some(s))
                    }
                };
            }
            // The others may be in `h`'s cone only when numbered before it.
            if !h.inputs.is_empty() && frontier.keys().next_back().is_some_and(|&n| n < h.own[0]) {
                let k = match self.key(&h, reads, own, keep, &beside, def) {
                    Ok(k) => k,
                    Err(n) => return Local::Need(n),
                };
                match self.by.get(&k) {
                    None => return Local::Need(Need::Summary(k, h.f)),
                    Some(None) => return Local::Unmade,
                    Some(Some(s)) => {
                        let inside =
                            |m: &Def| m.own.iter().any(|&n| s.atoms.contains(&Atom::Aux(n)));
                        if frontier.values().all(inside) {
                            let beside = beside.into_iter().map(|d| d.f).collect();
                            return Local::Ready(beside, Some(s));
                        }
                        // Those outside `h`'s summary are read beside in its place, and `h`
                        // stays: a question reading a definition apart from a chain
                        // (`h{i}(x: x) < x div 64 - 1`, its `x div 64` numbered before the
                        // links where an earlier test made it) reads the chain through its
                        // summary, as when that definition is numbered after the links, and not
                        // every link beside (cross-review of LOAD-max-div-xr, round 2).
                        let out: Vec<u32> = (frontier.iter())
                            .filter(|(_, m)| !inside(m))
                            .map(|(&n, _)| n)
                            .collect();
                        frontier.insert(top, h);
                        for n in out {
                            let Some(m) = frontier.remove(&n) else {
                                continue;
                            };
                            if !enter(
                                &m.inputs,
                                own,
                                Some(m.own[0]),
                                def,
                                &mut seen,
                                &mut frontier,
                            ) {
                                return Local::Unmade;
                            }
                            beside.push(m);
                        }
                        continue;
                    }
                }
            }
            if !enter(
                &h.inputs,
                own,
                Some(h.own[0]),
                def,
                &mut seen,
                &mut frontier,
            ) {
                return Local::Unmade;
            }
            beside.push(h);
        }
        Local::Ready(beside.into_iter().map(|d| d.f).collect(), None)
    }

    /// The key of the summary of `h`, read beside `reads` (whose own variables are `own`), the
    /// definitions `beside` and an outer key `keep`: the atoms of these that `h` or its cone
    /// may hold, but those `own` and `beside` define: a variable of `h`'s own, so that one no
    /// other reads (the remainder of `(2 * H) div 3`) is projected out of the summary, a
    /// variable numbered before `h`'s own (every variable of its cone is, [`enter`]) and a
    /// symbol of `h`'s cone
    /// ([`Summaries::syms`]), so that a question reading a symbol the chain does not
    /// (`h{i}(x: x) > 0 && x < 1000`, its own `x`) shares the chain's summaries. A variable
    /// numbered before `h`'s own is kept only when `h` reads another definition: the
    /// variables of a definition of symbols alone (`x div 3`) are in no cone of its. Where the
    /// key keeps such a variable, the symbols of the cone and the first variable of its
    /// definition join it, so the pieces meet it beside the symbols it is a function of (a
    /// summary keyed without it is then never read with its definition, which [`Summaries::local`]
    /// enters only through an atom of the key). `Err` with the symbols to find first. Time of
    /// the atoms, O(log n) each, and of one [`Def::of`] for each variable numbered before
    /// `h`'s own.
    fn key(
        &self,
        h: &Def,
        reads: &BTreeSet<Atom>,
        own: &BTreeSet<Atom>,
        keep: &[Atom],
        beside: &[Def],
        def: &dyn Fn(u32) -> Formula,
    ) -> Result<Key, Need> {
        let Some(syms) = self.syms.get(&h.id) else {
            return Err(Need::Syms(h.f.clone()));
        };
        let defined: HashSet<u32> = beside.iter().flat_map(|d| d.own.iter().copied()).collect();
        let atoms = (keep.iter().chain(reads)).chain(beside.iter().flat_map(|d| &d.reads));
        let kept = |a: &Atom| match a {
            Atom::Aux(n) => {
                (!h.inputs.is_empty() && *n < h.own[0] && !defined.contains(n) && !own.contains(a))
                    || h.own.binary_search(n).is_ok()
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
                Atom::Aux(n) if *n < h.own[0] => Some(*n),
                _ => None,
            })
            .collect();
        for n in earlier {
            if let Some(m) = Def::of(def(n), def)
                && m.inputs.is_empty()
            {
                out.extend(syms.iter().cloned());
                out.insert(Atom::Aux(m.own[0]));
            }
        }
        Ok((h.id, out.into_iter().collect()))
    }

    /// Finds the symbols of the cone of the definition `h`: those it reads and those of the
    /// definitions it reaches, each definition's found once and remembered, after its inputs':
    /// an explicit stack, since the chain is as deep as the program. Each definition on the
    /// stack holds its inputs, read once, and the place of the next one to visit, so that
    /// every input is visited before the union is made (a definition that reads two others
    /// whose sets are not yet found visits both: cross-review of LOAD-max-div-xr, round 2). A
    /// definition whose symbols are those of its input with none added shares its input's
    /// set. Time of the definitions and inputs reached and of the sets made.
    fn syms(&mut self, h: Formula, def: &dyn Fn(u32) -> Formula) {
        // A definition on the stack: its key, the atoms it reads, its inputs, and the place
        // of the next input to visit.
        struct Frame {
            id: Id,
            atoms: Vec<Atom>,
            inputs: Vec<Formula>,
            next: usize,
        }
        let frame = |f: &Formula| {
            let id = Id::any(f);
            let atoms: Vec<Atom> = reads(f).into_iter().collect();
            let inputs: Vec<Formula> = (atoms.iter().flat_map(auxes))
                .map(def)
                .filter(|d| !free(d) && Id::any(d) != id)
                .collect();
            Frame {
                id,
                atoms,
                inputs,
                next: 0,
            }
        };
        if self.syms.contains_key(&Id::any(&h)) {
            return;
        }
        // The keys of the definitions on the stack: an input among them is on a cycle.
        let mut open: HashSet<Id> = HashSet::from([Id::any(&h)]);
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
                if !self.syms.contains_key(&k) && !open.contains(&k) {
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
            // Its inputs' sets, the largest first, those missing (on a cycle) left out; the
            // definition is in no summary then ([`Def::of`] numbers each input before it).
            let mut sets: Vec<&Arc<imbl::OrdSet<Atom>>> = (top.inputs.iter())
                .filter_map(|d| self.syms.get(&Id::any(d)))
                .collect();
            sets.sort_by_key(|s| std::cmp::Reverse(s.len()));
            let mine = top.atoms.iter().filter(|a| matches!(a, Atom::Sym(_)));
            let set = match sets.split_first() {
                Some((big, rest))
                    if mine.clone().all(|a| big.contains(a))
                        && rest.iter().all(|s| s.iter().all(|a| big.contains(a))) =>
                {
                    Arc::clone(big)
                }
                _ => {
                    // Complexity tradeoff: copying the largest input's set and adding to it
                    // costs O(n) per link on a chain that reads a new symbol at each link,
                    // O(n^2) time and storage over n links (cross-review of LOAD-max-div-xr,
                    // round 1, I7). A persistent ordered set shares the largest input's tree;
                    // each added symbol costs O(log n), O(n log n) over that chain. The other
                    // inputs' sets are still visited to form the union, O(their sizes · log n).
                    let mut set: imbl::OrdSet<Atom> = sets
                        .first()
                        .map_or_else(imbl::OrdSet::new, |s| (***s).clone());
                    for a in sets.iter().skip(1).flat_map(|s| s.iter()).chain(mine) {
                        set.insert(a.clone());
                    }
                    Arc::new(set)
                }
            };
            self.syms.insert(top.id, set);
        }
    }
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

/// Puts the definitions of the variables `ins` on `frontier`, by the highest number each
/// defines, each once (`seen`), but those of `own`, and of variables with no definition: false
/// where no summary is made of one ([`Def::of`]), or where one defines a variable numbered at
/// or after `first`, the first variable of the definition that reads it, so that every
/// variable of a definition's cone is numbered before its own (the order a scope numbers them
/// in, `preimage::Scoped::def`), which [`Summaries::key`] reads.
fn enter(
    ins: &[u32],
    own: &BTreeSet<Atom>,
    first: Option<u32>,
    def: &dyn Fn(u32) -> Formula,
    seen: &mut HashSet<Id>,
    frontier: &mut BTreeMap<u32, Def>,
) -> bool {
    for &n in ins {
        let f = def(n);
        if free(&f) || own.contains(&Atom::Aux(n)) || !seen.insert(Id::any(&f)) {
            continue;
        }
        let Some(d) = Def::of(f, def) else {
            return false;
        };
        let last = d.own[d.own.len() - 1];
        if first.is_some_and(|m| last >= m) {
            return false;
        }
        frontier.insert(last, d);
    }
    true
}

type Terms = BTreeMap<Atom, Int>;
type LineGroup = (Atom, Terms, bool);

/// The lines `e * y >= m * f + b` of `rows` by `(y, f, lower)`, the explicit 1-form bounds
/// `[lo, hi]` on each primitive form `f`, and whether those bounds are consistent.
fn group_lines(
    rows: &[Con],
) -> (
    HashMap<LineGroup, Vec<(Int, Int, usize)>>,
    HashMap<Terms, (Option<Int>, Option<Int>)>,
    bool,
) {
    let mut groups: HashMap<LineGroup, Vec<(Int, Int, usize)>> = HashMap::new();
    let mut bounds: HashMap<Terms, (Option<Int>, Option<Int>)> = HashMap::new();
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
// [`lean`] does, one decision for each row, and refused here. Used: the rows grouped by hash,
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

/// `rows` without division pairs `(m, v, i, j)` of `elim` whose quotient `v` occurs in no other
/// row: `0 <= e - m * v <= m - 1` holds for `v == e div m` at every integer point of the other
/// atoms, so dropping the pair preserves integer satisfiability.
// Complexity tradeoff: naive version, rescan `rows` and `pairs` in a loop until no free pair
// remains, O(p r t). Used: a worklist queue of quotients whose occurrence count reaches 2,
// decrementing the counts of the dividend's atoms as each pair is dropped, O(r t),
// plus O(r log r) row comparisons for the sort and deduplication. Tradeoffs:
// two hash maps of atom counts and pairs.
fn without_free_pairs_for(mut rows: Vec<Con>, elim: &dyn Fn(&Atom) -> bool) -> Vec<Con> {
    rows.sort();
    rows.dedup();
    let mut count: HashMap<Atom, usize> = HashMap::new();
    for r in &rows {
        for a in r.lin.terms.keys() {
            *count.entry(a.clone()).or_default() += 1;
        }
    }
    let mut pair_of: HashMap<Atom, (usize, usize)> = HashMap::new();
    for (_, v, i, j) in pairs(&rows) {
        if elim(&v) {
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
    static REST_ROW_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `rows` simplified preserving integer satisfiability: remainders converted to division pairs,
/// equations with a single-use unit variable dropped, and free division pairs peeled.
// Complexity tradeoff: naive version, pass all definition rows to [`decide`], which eliminates
// auxiliary quotients and remainders alongside big-integer bounds in `live3`. Used: peel
// single-use unit equations by queue, with the rows left that use each atom counted down as
// rows are dropped, and run [`without_free_pairs_for`], O(r t) plus O(r log r) row comparisons
// for its sort. Counting the uses left by a scan of the atom's occurrence list after each drop
// costs O(r²) on `y_i == x` (cross-review of LOAD-max-div-xr, round 3, Codex). Tradeoffs: hash
// maps of occurrences and counts.
fn without_free_pairs(rows: Vec<Con>) -> Vec<Con> {
    let mut rows = remainders_as_pairs(&rows, &|_| false);
    let mut at: HashMap<Atom, Vec<usize>> = HashMap::new();
    for (i, r) in rows.iter().enumerate() {
        for a in r.lin.terms.keys() {
            at.entry(a.clone()).or_default().push(i);
        }
    }
    // The rows not dropped that use each atom.
    let mut left: HashMap<Atom, usize> = (at.iter()).map(|(a, ns)| (a.clone(), ns.len())).collect();
    let mut queue: Vec<Atom> = (at.iter())
        .filter_map(|(a, ns)| {
            (ns.len() == 1 && !matches!(a, Atom::Product(..))).then_some(a.clone())
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
                if *n == 1 && !matches!(b, Atom::Product(..)) {
                    queue.push(b.clone());
                }
            }
        }
    }
    rows = (rows.into_iter().enumerate())
        .filter(|(i, _)| !drop.contains(i))
        .map(|(_, r)| r)
        .collect();
    without_free_pairs_for(rows, &|_| true)
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
/// product) with coefficient 1 or -1 in an equation and held by exactly two other rows, each
/// a bound of `r` alone, is solved from the equation into the bounds, so that `e == m * v +
/// r, 0 <= r <= m - 1` reads as `m * v <= e <= m * v + m - 1`; the three rows are replaced by
/// the two. The rows hold where they held with some `r`. Time of the rows' terms.
fn remainders_as_pairs(rows: &[Con], keep: &dyn Fn(&Atom) -> bool) -> Vec<Con> {
    let mut rows: Vec<Con> = rows.to_vec();
    rows.sort();
    rows.dedup();
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
            if keep(r) || matches!(r, Atom::Product(..)) || (*c != Int::ONE && *c != -&Int::ONE) {
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
        // A piece in a group is live: its entries leave the groups when it is merged.
        let hit = hit.and_then(|(g, lo, hi, l, h, id)| Some((g, lo, hi, l, h, live[id].take()?)));
        let Some((g, lo, hi, l, h, q)) = hit else {
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
                if let Some(q) = live[id].take() {
                    for (gq, lq, hq) in forms(&q) {
                        if let Some(m) = groups.get_mut(&gq) {
                            m.remove(&lq);
                        }
                        // Another piece with the same bound may hold the entry since.
                        if let Some((u, w)) = sides.get_mut(&gq.1) {
                            if let Some(hq) = hq {
                                if u.get(&hq) == Some(&id) {
                                    u.remove(&hq);
                                }
                            }
                            if let Some(lq) = lq {
                                if w.get(&lq) == Some(&id) {
                                    w.remove(&lq);
                                }
                            }
                        }
                    }
                    work.push(joined(
                        &both,
                        lo.min(l),
                        match (hi, h) {
                            (Some(a), Some(b)) => Some(a.max(b)),
                            _ => None,
                        },
                    ));
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
        for (g, lo, _) in forms(&q) {
            if let Some(m) = groups.get_mut(&g) {
                m.remove(&lo);
            }
        }
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
    /// The definitions read beside, and the summary of the one left below them, if any.
    Ready(Vec<Formula>, Option<&'a Summary>),
    /// What to make first.
    Need(Need),
    /// No summary is made.
    Unmade,
}

/// What to make first: the summary of a definition under a key, or the symbols of a
/// definition's cone.
enum Need {
    Summary(Key, Formula),
    Syms(Formula),
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
}
