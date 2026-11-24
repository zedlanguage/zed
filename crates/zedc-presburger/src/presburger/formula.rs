//! The formulas of the solver (`super`): atoms, linear terms, constraints and formulas over
//! them, and the key of a compound part held by more than one parent ([`Id`]), with the
//! arithmetic of terms, the value of a constraint at a model, the rank of a formula's
//! variant and how each is written. The solver and the operations that follow a formula's
//! nesting (`super::deep`) both read these, so they are kept in a file below both
//! (ZED_PORT_GAPS.md gap 10).

use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::ops::Deref;
use std::slice;
use std::sync::{Arc, OnceLock};

use zed_kernel::value::fresh_id;
use zedc_int::int::Int;
use zedc_lattice::affine::write_sum;

/// A variable of a relation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Atom {
    /// A symbol: an input, a parameter, a key.
    Sym(Arc<str>),
    /// The product of two factors, in order.
    Product(Factor, Factor),
    /// An auxiliary variable, defined by the relation's definitions.
    Aux(u32),
}

/// A factor of a product atom: a symbol, or an auxiliary variable such as the quotient `q` of
/// `x div n` in `x == n * q + r`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Factor {
    /// A symbol.
    Sym(Arc<str>),
    /// An auxiliary variable.
    Aux(u32),
}

/// A linear term: each atom times its coefficient, plus a constant. No coefficient is zero.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Lin {
    /// The coefficients.
    pub terms: BTreeMap<Atom, Int>,
    /// The constant.
    pub constant: Int,
}

impl PartialOrd for Lin {
    fn partial_cmp(&self, other: &Lin) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Lin {
    /// The derived order: the terms as a sequence of pairs, then the constant.
    // Complexity tradeoff: naive version, the derived order, which walks both maps of terms
    // with their iterators from the first pair: about 160 instructions for two constraints of
    // two terms, most of it setting up the iterators, and a set keyed by constraints makes
    // O(log n) such comparisons per lookup, so their cost grew 12.5 times from 32 to 256 tests
    // of the chain raise in reverse (`xst::s4`). Used: the first pairs read directly and
    // compared, which decides the order alone when they differ, as they do for most pairs of
    // constraints of a set; the walk only when they are equal. The same order, O(1) when the
    // first pairs differ and O(t) at worst as before. Test
    // `l01_38_presburger::shared::terms_compare_as_their_derived_order`, COMPLEXITY.md row
    // ST-chain-raise-reverse-log. When the first pairs are equal and either term has only
    // that pair, it is a prefix of the other, so the terms are ordered by their number of
    // pairs, and by the constant when both have one: O(1) without the walk, which the
    // constraints `x - c >= 0` of a set, all with the first pair `(x, 1)`, took at each
    // comparison (COMPLEXITY.md row PERF-l139-lin-prefix). When both have two pairs, the
    // last pairs are the second, so they are read directly too, as for `x + j * y - 1 >= 0`
    // and `x - j * y - 1 >= 0`.
    fn cmp(&self, other: &Lin) -> std::cmp::Ordering {
        if let (Some(a), Some(b)) = (self.terms.first_key_value(), other.terms.first_key_value()) {
            match a.cmp(&b) {
                std::cmp::Ordering::Equal => {}
                o => return o,
            }
            let (m, n) = (self.terms.len(), other.terms.len());
            if m == 1 || n == 1 {
                return m.cmp(&n).then_with(|| self.constant.cmp(&other.constant));
            }
            if m == 2 && n == 2 {
                let (p, q) = (self.terms.last_key_value(), other.terms.last_key_value());
                return p.cmp(&q).then_with(|| self.constant.cmp(&other.constant));
            }
        }
        self.terms
            .cmp(&other.terms)
            .then_with(|| self.constant.cmp(&other.constant))
    }
}

/// How a constraint's term compares with zero.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Rel {
    /// `t >= 0`.
    Ge,
    /// `t == 0`.
    Eq,
}

/// A linear constraint.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Con {
    /// The term.
    pub lin: Lin,
    /// Its comparison with zero.
    pub rel: Rel,
}

/// A quantifier-free formula over linear constraints. Each compound node holds its parts
/// behind a [`Shared`] handle, so a copy costs O(1) and shares them, and a part may be held by
/// many parents: the formula of a `let`-bound test is held once at each use (COMPLEXITY.md
/// S31). Every pass over a formula reads a shared part once per call (`deep`), so its cost is
/// the number of distinct parts. Drop, compare, hash and show do not recurse on its depth. Two
/// formulas are compared as the derived order would compare their trees written out, but a
/// part compared with itself is equal at once: a lookup of a conjunct in the maps keyed by
/// formulas finds the very formula it holds, and would otherwise walk the whole of it.
pub enum Formula {
    /// A constraint.
    Con(Con),
    /// Negation.
    Not(Shared<Formula>),
    /// Conjunction; empty is `true`.
    And(Shared<Vec<Formula>>),
    /// Disjunction; empty is `false`.
    Or(Shared<Vec<Formula>>),
    /// The call node: "the term lies in no hole of the set" ([`BoundHoles`]), one leaf for
    /// what was a clause for each hole.
    Holes(Shared<BoundHoles>),
}

/// The holes of a callee (LOAD-call-disj-spread, the call node: the values it excludes), as
/// maximal disjoint runs of integers in increasing order, built once and shared by every call
/// that reads it ([`BoundHoles`]). Immutable, so its id ([`Shared`]) names one content for good.
// Complexity tradeoff (design-b22-load5.md section 2, META3 H5 of XR-load-call-node): the design
// names the persistent treap of `extend::holes` as the payload. A payload is never cut after it
// is built, so a sorted array of runs is used instead: membership, successor and predecessor by
// binary search in O(log n) worst case, where the treap is O(log n) expected, with no
// priorities to seed, and the build from runs already merged is O(n) (O(n log n) from any
// order). The face's own holes, which are cut link by link, stay in the treap.
pub struct HoleSet {
    /// The runs `(lo, hi)`, `lo <= hi`, each at least 2 below the next (touching runs merge).
    runs: Vec<(Int, Int)>,
    /// A fixed hash of the runs, found once: two sets of equal runs have equal keys in every
    /// run of the compiler, so order and hash do not depend on which set was built first
    /// (META3 H5, Codex B3: order by a deterministic content key, identity only as the fast
    /// path).
    key: u64,
}

impl HoleSet {
    /// The set of the integers in the closed intervals `runs`, given in any order and possibly
    /// overlapping or touching. O(n log n) for n intervals; intervals with `lo > hi` are empty.
    pub fn of(mut runs: Vec<(Int, Int)>) -> Shared<HoleSet> {
        runs.retain(|(lo, hi)| lo <= hi);
        runs.sort();
        let mut out: Vec<(Int, Int)> = Vec::with_capacity(runs.len());
        for (lo, hi) in runs {
            match out.last_mut() {
                Some(prev) if lo <= &prev.1 + &Int::ONE => prev.1 = prev.1.clone().max(hi),
                _ => out.push((lo, hi)),
            }
        }
        let mut h = zed_kernel::digest::fixed_hasher();
        for (lo, hi) in &out {
            std::hash::Hash::hash(lo, &mut h);
            std::hash::Hash::hash(hi, &mut h);
        }
        let key = std::hash::Hasher::finish(&h);
        Shared::new(HoleSet { runs: out, key })
    }

    /// The runs, in increasing order.
    pub fn runs(&self) -> &[(Int, Int)] {
        &self.runs
    }

    /// The run holding `v`, or `None` when `v` lies in no hole. O(log n) by binary search: the
    /// runs are sorted and disjoint, so the first run whose upper end is at least `v` is the
    /// only one that can hold it.
    pub fn run_of(&self, v: &Int) -> Option<&(Int, Int)> {
        let i = self.runs.partition_point(|(_, hi)| hi < v);
        self.runs.get(i).filter(|(lo, _)| lo <= v)
    }

    /// The order of two sets by content: the key, then the runs, so equal content compares
    /// equal whatever was built first. O(1) when the keys differ, O(n) when they tie.
    fn cmp_content(&self, other: &HoleSet) -> std::cmp::Ordering {
        self.key
            .cmp(&other.key)
            .then_with(|| self.runs.cmp(&other.runs))
    }
}

/// A call of a callee with holes ([`HoleSet`]) through the binding `y = term`: it holds where
/// the term's value lies in no run (design-b22-load5.md section 2, E1: `Holes::holds` is true
/// inside a hole, so the node is its complement). The set is shared and never rewritten; a
/// substitution changes the term alone and makes a new node with a new id, and a copy of the
/// formula shares the node and its id (META3 H5).
pub struct BoundHoles {
    set: Shared<HoleSet>,
    term: Lin,
    /// The node written as one clause a run, `term <= lo - 1 || term >= hi + 1`, made the first
    /// time a reader with no route of its own for the node asks for it, and counted then
    /// (`extend::counts::HOLES_LOWERED`, `HOLES_CLAUSES`).
    lowered: OnceLock<Formula>,
}

impl BoundHoles {
    /// The set of holes.
    pub fn set(&self) -> &Shared<HoleSet> {
        &self.set
    }

    /// The term the holes are read at.
    pub fn term(&self) -> &Lin {
        &self.term
    }

    /// Whether the node holds at `values`, each atom absent from them zero and each product
    /// read as the product of its factors' values ([`Lin::eval`]). O(t + log n), t the term's
    /// size.
    pub(super) fn holds(&self, values: &Model) -> bool {
        self.set.run_of(&self.term.eval(values)).is_none()
    }

    /// The node written as a conjunction of one clause a run, the generic decision of the node
    /// for a reader with no route of its own (META3 H7: the fallback, counted). Made once a
    /// node, in O(n) for n runs.
    pub(super) fn lowered(&self) -> &Formula {
        self.lowered.get_or_init(|| {
            super::extend::counts::add(super::extend::counts::HOLES_LOWERED, 1);
            super::extend::counts::add(super::extend::counts::HOLES_CLAUSES, self.set.runs.len());
            let mut clauses: Vec<Formula> = (self.set.runs.iter())
                .map(|(lo, hi)| {
                    let below = Con::ge(&Lin::constant(lo - &Int::ONE), &self.term);
                    let above = Con::ge(&self.term, &Lin::constant(hi + &Int::ONE));
                    Formula::Or(Shared::new(vec![Formula::Con(below), Formula::Con(above)]))
                })
                .collect();
            // One hole is its clause alone (`Formula::outside` makes no node without a hole).
            match clauses.len() {
                1 => clauses.pop().expect("one clause"),
                _ => Formula::And(Shared::new(clauses)),
            }
        })
    }

    /// The order of two nodes: the sets by content ([`HoleSet::cmp_content`]), then the terms.
    /// Two nodes of one set are compared by their terms alone.
    pub(super) fn cmp_content(&self, other: &BoundHoles) -> std::cmp::Ordering {
        let sets = match Shared::same(&self.set, &other.set) {
            true => std::cmp::Ordering::Equal,
            false => self.set.cmp_content(&other.set),
        };
        sets.then_with(|| self.term.cmp(&other.term))
    }

    /// Writes the node's content to `h`: the set's key and the term, so that nodes equal under
    /// [`BoundHoles::cmp_content`] write the same.
    pub(super) fn hash_content(&self, h: &mut impl std::hash::Hasher) {
        h.write_u64(self.set.key);
        std::hash::Hash::hash(&self.term, h);
    }
}

impl Formula {
    /// "`term` lies in no hole of `set`", the call node (META3 H5). A set with no holes gives
    /// `true`. A term with no atom is one value, so the node is decided here by one membership
    /// test (design section 2, G8: a constant argument folds to the complement of membership;
    /// META3 H6: on a fixed value the node holds exactly when the value is no member). O(t +
    /// log n).
    // `true` and `false` are written as `joining`'s `top` and `bottom` write them, since this
    // file is below `joining` (no import cycle, s_01f_import_graph).
    pub fn outside(set: &Shared<HoleSet>, term: Lin) -> Formula {
        let top = || Formula::And(Shared::new(Vec::new()));
        if set.runs.is_empty() {
            return top();
        }
        if term.terms.is_empty() {
            return match set.run_of(&term.constant) {
                Some(_) => Formula::Or(Shared::new(Vec::new())),
                None => top(),
            };
        }
        Formula::Holes(Shared::new(BoundHoles {
            set: set.clone(),
            term,
            lowered: OnceLock::new(),
        }))
    }

    /// The formula itself, or for a call node its clauses ([`BoundHoles::lowered`], written
    /// once a node and counted): the generic route of a walker that reads a formula down to its
    /// constraints (META3 H7). A node's clauses hold no node, so one step suffices. O(1) after
    /// the node's first lowering, which is O(runs).
    pub fn opened(&self) -> &Formula {
        match self {
            Formula::Holes(b) => b.lowered(),
            Formula::Con(_) | Formula::Not(_) | Formula::And(_) | Formula::Or(_) => self,
        }
    }
}

/// The parts of a compound node of a [`Formula`], shared: a copy is a reference count. They
/// carry the id they were given when they were made: copies share it, no other parts have it,
/// and parts changed in place ([`Shared::change`]) take a new one. So a pass that meets a
/// shared part again knows it by its id ([`Id`]): memo and visited keys are ids or structure,
/// never addresses (SYNTHESIS fact 2), as with `zed_kernel::Shared`. The id does not change what
/// the formula means: equality, order, hash and show read the parts alone. The parts also keep
/// the hash of the node that holds them once it is found (`Sig`), so that it is found once.
pub struct Shared<T>(Arc<Held<T>>);

struct Held<T> {
    id: u64,
    /// The hash of the node holding the parts, found the first time it is asked for.
    sig: OnceLock<Sig>,
    body: T,
}

/// The hash of a node of a [`Formula`] (`deep`): `n`, the number its `Hash` writes, and for a
/// conjunction or disjunction its parts' numbers read as flattened, as one polynomial `seq`
/// and the power `pow` of its base to their count, which a parent of the same variant reads
/// in their place. `rank` is the variant it was found for ([`Formula::rank`]). Two formulas
/// equal under `Ord` have equal hashes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct Sig {
    pub(super) rank: u8,
    pub(super) n: u64,
    pub(super) seq: u64,
    pub(super) pow: u64,
}

impl<T> Shared<T> {
    /// `body`, shared, with a new id.
    pub fn new(body: T) -> Shared<T> {
        Shared(Arc::new(Held {
            id: fresh_id(),
            sig: OnceLock::new(),
            body,
        }))
    }

    /// The parts, to change in place when `this` is their only holder. They take a new id,
    /// since what the old id named is no longer these parts, and lose their hash.
    pub fn change(this: &mut Shared<T>) -> Option<&mut T> {
        let held = Arc::get_mut(&mut this.0)?;
        held.id = fresh_id();
        held.sig = OnceLock::new();
        Some(&mut held.body)
    }

    /// The parts, when `this` is their only holder, only to move them out before the node
    /// goes, so the id is kept; the hash is dropped, since the parts are no longer these.
    pub(super) fn get_mut(this: &mut Shared<T>) -> Option<&mut T> {
        Arc::get_mut(&mut this.0).map(|h| {
            h.sig = OnceLock::new();
            &mut h.body
        })
    }

    /// The hash kept for the node holding the parts, when one was kept for a node of the
    /// variant `rank`.
    pub(super) fn sig(this: &Shared<T>, rank: u8) -> Option<Sig> {
        this.0.sig.get().copied().filter(|s| s.rank == rank)
    }

    /// Keeps `sig` as the hash of the node holding the parts, unless one is kept already;
    /// whether `sig` is the one kept.
    pub(super) fn keep_sig(this: &Shared<T>, sig: Sig) -> bool {
        *this.0.sig.get_or_init(|| sig) == sig
    }

    /// The number of holders of the parts.
    pub fn strong_count(this: &Shared<T>) -> usize {
        Arc::strong_count(&this.0)
    }

    /// Whether the two handles hold the same parts.
    pub fn same(a: &Shared<T>, b: &Shared<T>) -> bool {
        a.0.id == b.0.id
    }
}

impl<T> Clone for Shared<T> {
    fn clone(&self) -> Shared<T> {
        Shared(Arc::clone(&self.0))
    }
}

impl<T> Deref for Shared<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0.body
    }
}

/// A satisfying assignment, each atom absent from it zero.
pub type Model = BTreeMap<Atom, Int>;

/// The key of a compound part of a formula: the id of its [`Shared`] parts, so two keys are
/// equal when they name the same part, and a part that two parents hold is found by either.
/// Ids are never reused, so a key needs not hold its part, and no result may depend on their
/// values: they are only compared and hashed, and no map keyed by them is iterated.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Id(u64);

impl Id {
    /// The key of `f`, a compound part.
    pub fn any(f: &Formula) -> Id {
        match f {
            Formula::Con(_) => unreachable!("a key names a compound part"),
            Formula::Not(g) => Id(g.0.id),
            Formula::And(gs) | Formula::Or(gs) => Id(gs.0.id),
            Formula::Holes(b) => Id(b.0.id),
        }
    }

    /// The key of `f` when another holder shares it, so that a pass may reach it again, or
    /// `None` for a constraint or a part held by its parent alone.
    pub(super) fn of(f: &Formula) -> Option<Id> {
        f.is_shared().then(|| Id::any(f))
    }

    /// The key of `f` when `f` is one of `twice` ([`Id::reached_twice`]), or `None`.
    pub(super) fn among(f: &Formula, twice: &HashSet<Id>) -> Option<Id> {
        if matches!(f, Formula::Con(_)) {
            return None;
        }
        let id = Id::any(f);
        twice.contains(&id).then_some(id)
    }

    /// The compound parts of `f` that `f` reaches through more than one parent, found in one
    /// walk with a visited set, so in time near the number of distinct parts. A pass that
    /// treats these parts apart reads `f`'s own sharing, not the handles held outside it.
    pub(super) fn reached_twice(f: &Formula) -> HashSet<Id> {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut twice: HashSet<Id> = HashSet::new();
        // The root is held by nothing below it, so its id in `seen` changes nothing.
        zed_graph::reach(
            [f],
            |&h| {
                if matches!(h, Formula::Con(_)) {
                    return false;
                }
                let id = Id::any(h);
                if seen.insert(id) {
                    return true;
                }
                twice.insert(id);
                false
            },
            |&g| g.kids(),
        );
        twice
    }
}

impl Formula {
    /// The formulas directly under `self`, in order.
    pub(super) fn kids(&self) -> &[Formula] {
        match self {
            Formula::Con(_) => &[],
            Formula::Not(g) => slice::from_ref(&**g),
            Formula::And(gs) | Formula::Or(gs) => gs,
            // A leaf: its clauses are no parts of it, and a pass reads them only through its
            // own arm for the node (`BoundHoles::lowered`).
            Formula::Holes(_) => &[],
        }
    }

    /// Whether another holder shares the part, so that a pass may reach it twice.
    pub(super) fn is_shared(&self) -> bool {
        match self {
            Formula::Con(_) => false,
            Formula::Not(g) => Shared::strong_count(g) > 1,
            Formula::And(gs) | Formula::Or(gs) => Shared::strong_count(gs) > 1,
            Formula::Holes(b) => Shared::strong_count(b) > 1,
        }
    }

    /// The rank of the variant, in the order in which [`Ord`] puts them.
    pub(super) fn rank(&self) -> u8 {
        match self {
            Formula::Con(_) => 0,
            Formula::Not(_) => 1,
            Formula::And(_) => 2,
            Formula::Or(_) => 3,
            Formula::Holes(_) => 4,
        }
    }

    /// Whether `self` is a conjunction or disjunction of the variant `kind`, so that it is read
    /// as flattened into a parent of that variant (`deep::Flat`).
    pub(super) fn flattens_into(&self, kind: u8) -> bool {
        matches!(self, Formula::And(_) | Formula::Or(_)) && self.rank() == kind
    }

    /// The top-level conjuncts, with a conjunction kept among them ([`Formula::and_keeping`])
    /// read as flattened into it; a conjunction kept at more than one place is read at its first.
    pub(super) fn conjuncts(&self) -> Vec<&Formula> {
        match self.conjunct_list() {
            Conjuncts::Read(out) => out,
            flat => flat.iter().collect(),
        }
    }

    /// [`Formula::conjuncts`], borrowed from the formula where no list need be made.
    // A conjunction that holds no conjunction, or a formula that is none, is read as it stands,
    // with no set of the conjunctions seen and no list made: O(1), where a list costs an
    // allocation on each call. Only a conjunction that holds one is read into a list, O(c).
    pub(super) fn conjunct_list(&self) -> Conjuncts<'_> {
        match self {
            Formula::And(gs) if !gs.iter().any(|g| matches!(g, Formula::And(_))) => {
                return Conjuncts::Flat(gs);
            }
            Formula::And(_) => {}
            g => return Conjuncts::Flat(std::slice::from_ref(g)),
        }
        let mut out = Vec::new();
        // An id is one number the compiler drew, so the seen set is a `DigestSet`, not the
        // default hasher, which reads a per-thread seed on each call and costs more per id.
        let mut seen: zed_kernel::digest::DigestSet<Id> = HashSet::default();
        let mut stack = vec![self];
        while let Some(g) = stack.pop() {
            match g {
                Formula::And(gs) => {
                    if seen.insert(Id::any(g)) {
                        stack.extend(gs.iter().rev());
                    }
                }
                g => out.push(g),
            }
        }
        Conjuncts::Read(out)
    }
}

/// The top-level conjuncts of a formula ([`Formula::conjunct_list`]): the operands of a
/// conjunction that holds none, or the formula alone, as written; or a list read from nested
/// conjunctions.
pub(super) enum Conjuncts<'f> {
    Flat(&'f [Formula]),
    Read(Vec<&'f Formula>),
}

impl<'f> Conjuncts<'f> {
    /// Each conjunct, in order.
    pub(super) fn iter(&self) -> impl Iterator<Item = &'f Formula> + '_ {
        let (flat, read): (&'f [Formula], &[&'f Formula]) = match self {
            Conjuncts::Flat(gs) => (gs, &[]),
            Conjuncts::Read(gs) => (&[], gs),
        };
        flat.iter().chain(read.iter().copied())
    }

    /// The number of conjuncts.
    pub(super) fn len(&self) -> usize {
        match self {
            Conjuncts::Flat(gs) => gs.len(),
            Conjuncts::Read(gs) => gs.len(),
        }
    }
}

impl Factor {
    /// The factor as an atom of its own.
    pub fn atom(&self) -> Atom {
        match self {
            Factor::Sym(s) => Atom::Sym(s.clone()),
            Factor::Aux(n) => Atom::Aux(*n),
        }
    }

    /// The atom `a` as a factor; `None` for a product.
    pub fn of(a: &Atom) -> Option<Factor> {
        match a {
            Atom::Sym(s) => Some(Factor::Sym(s.clone())),
            Atom::Aux(n) => Some(Factor::Aux(*n)),
            Atom::Product(..) => None,
        }
    }

    /// Whether the factor is the symbol `sym`.
    pub fn is(&self, sym: &Arc<str>) -> bool {
        matches!(self, Factor::Sym(s) if s == sym)
    }
}

/// How a symbol is written: [`as_is`], or the function a message gives to write each symbol
/// by the name the program wrote ([`Formula::written`]).
pub(super) type Names = fn(&str) -> &str;

/// A symbol written as it is.
pub(super) fn as_is(s: &str) -> &str {
    s
}

impl Factor {
    /// Writes the factor, each symbol through `name`.
    fn show(&self, f: &mut fmt::Formatter<'_>, name: Names) -> fmt::Result {
        match self {
            Factor::Sym(s) => f.write_str(name(s)),
            Factor::Aux(n) => write!(f, "q{n}"),
        }
    }
}

impl fmt::Display for Factor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.show(f, as_is)
    }
}

impl Atom {
    /// The product of two symbols.
    pub fn product(a: &Arc<str>, b: &Arc<str>) -> Atom {
        Atom::product_of(Factor::Sym(a.clone()), Factor::Sym(b.clone()))
    }

    /// The product of two factors.
    pub fn product_of(a: Factor, b: Factor) -> Atom {
        if a <= b {
            Atom::Product(a, b)
        } else {
            Atom::Product(b, a)
        }
    }

    /// The auxiliary variables of the atom: itself, or each factor of a product that is one.
    /// The one routine for this (DRY): `extend.rs` and `placing.rs` each had a copy, and
    /// zedc-preimage reads it for the newest atom a key names (`Tx::forget`). O(1).
    pub fn auxes(&self) -> impl Iterator<Item = u32> {
        let aux = |f: &Factor| match f {
            Factor::Aux(n) => Some(*n),
            Factor::Sym(_) => None,
        };
        let (f, g) = match self {
            Atom::Aux(n) => (Some(*n), None),
            Atom::Product(f, g) => (aux(f), aux(g)),
            Atom::Sym(_) => (None, None),
        };
        f.into_iter().chain(g)
    }
}

impl Atom {
    /// Writes the atom, each symbol through `name`.
    fn show(&self, f: &mut fmt::Formatter<'_>, name: Names) -> fmt::Result {
        match self {
            Atom::Sym(s) => f.write_str(name(s)),
            Atom::Product(a, b) => {
                a.show(f, name)?;
                f.write_str(" * ")?;
                b.show(f, name)
            }
            Atom::Aux(n) => write!(f, "q{n}"),
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.show(f, as_is)
    }
}
impl Lin {
    /// The constant `k`.
    pub fn constant(k: impl Into<Int>) -> Lin {
        Lin {
            terms: BTreeMap::new(),
            constant: k.into(),
        }
    }

    /// The atom `a`.
    pub fn atom(a: Atom) -> Lin {
        Lin {
            terms: BTreeMap::from([(a, Int::ONE)]),
            constant: Int::ZERO,
        }
    }

    /// One more than the largest auxiliary variable the term names, itself or as a factor of
    /// a product ([`Atom::auxes`]); 0 when it names none. A caller that numbers auxiliary
    /// variables in order of making reads from it whether the term names one made at or after
    /// a mark (zedc-preimage `Tx::forget`). O(the terms).
    pub fn aux_end(&self) -> u32 {
        (self.terms.keys().flat_map(Atom::auxes))
            .map(|n| n.saturating_add(1))
            .max()
            .unwrap_or(0)
    }

    /// `self + other`.
    pub fn plus(&self, other: &Lin) -> Lin {
        let mut out = self.clone();
        out.plus_assign(other);
        out
    }

    /// `self += other`, in time near `other` alone.
    pub fn plus_assign(&mut self, other: &Lin) {
        for (a, c) in &other.terms {
            let v = self.terms.get(a).map_or_else(|| c.clone(), |o| o + c);
            if v.is_zero() {
                self.terms.remove(a);
            } else {
                self.terms.insert(a.clone(), v);
            }
        }
        self.constant = &self.constant + &other.constant;
    }

    /// `self * k`.
    pub fn times(&self, k: impl Into<Int>) -> Lin {
        let k = k.into();
        if k.is_zero() {
            return Lin::default();
        }
        Lin {
            terms: self
                .terms
                .iter()
                .map(|(a, c)| (a.clone(), c * &k))
                .collect(),
            constant: &self.constant * &k,
        }
    }

    /// `self - other`.
    pub fn minus(&self, other: &Lin) -> Lin {
        self.plus(&other.times(-1))
    }

    /// Whether every atom is a symbol or an auxiliary variable.
    pub fn is_linear(&self) -> bool {
        !self.terms.keys().any(|a| matches!(a, Atom::Product(..)))
    }

    /// The product of two terms, its products of two factors (symbols or auxiliary variables)
    /// as atoms; `None` when neither is a constant and either holds a product atom.
    pub fn product(&self, other: &Lin) -> Option<Lin> {
        if self.terms.is_empty() {
            return Some(other.times(self.constant.clone()));
        }
        if other.terms.is_empty() {
            return Some(self.times(other.constant.clone()));
        }
        fn factors(l: &Lin) -> Option<Vec<(Factor, &Int)>> {
            (l.terms.iter())
                .map(|(a, c)| Some((Factor::of(a)?, c)))
                .collect()
        }
        let (xs, ys) = (factors(other)?, factors(self)?);
        // Each term is added in place, O(|self| × |other| × log) in all; adding each as a new
        // `Lin` with `plus` copied the sum so far at every term, O((|self| × |other|)²).
        let mut out = self.times(other.constant.clone());
        for (x, c) in &xs {
            out.plus_assign(&Lin::atom(x.atom()).times(*c * &self.constant));
            for (y, d) in &ys {
                out.plus_assign(&Lin::atom(Atom::product_of(x.clone(), y.clone())).times(*c * *d));
            }
        }
        Some(out)
    }

    /// The value at `values`, each atom absent from it zero and each product atom read as the
    /// product of its factors' values.
    pub(super) fn eval(&self, values: &Model) -> Int {
        let sym = |s: &Factor| values.get(&s.atom()).cloned().unwrap_or(Int::ZERO);
        let mut v = self.constant.clone();
        for (a, c) in &self.terms {
            match a {
                Atom::Product(x, y) => v = &v + &(c * &(&sym(x) * &sym(y))),
                _ => {
                    if let Some(x) = values.get(a) {
                        v = &v + &(c * x);
                    }
                }
            }
        }
        v
    }

    /// The value at `values` with each atom, a product included, read as a variable of its own,
    /// an atom absent from it zero: the linear reading, the one the solver decides, in which a
    /// product is not tied to its factors (`entails` reads a countermodel back as products).
    pub(super) fn eval_linear(&self, values: &Model) -> Int {
        let mut v = self.constant.clone();
        for (a, c) in &self.terms {
            if let Some(x) = values.get(a) {
                v = &v + &(c * x);
            }
        }
        v
    }
}

impl Lin {
    /// Writes the term, each symbol through `name` ([`write_sum`]).
    fn show(&self, f: &mut fmt::Formatter<'_>, name: Names) -> fmt::Result {
        write_sum(f, &self.terms, &self.constant, |f, a| a.show(f, name))
    }
}

impl fmt::Display for Lin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.show(f, as_is)
    }
}

impl Con {
    /// `a >= b`.
    pub fn ge(a: &Lin, b: &Lin) -> Con {
        Con {
            lin: a.minus(b),
            rel: Rel::Ge,
        }
    }

    /// `a == b`.
    pub fn eq(a: &Lin, b: &Lin) -> Con {
        Con {
            lin: a.minus(b),
            rel: Rel::Eq,
        }
    }

    /// The constraint divided by the greatest common divisor `g` of its coefficients, when `g`
    /// is more than one: an equation whose constant `g` does not divide is `false`, and an
    /// inequality's constant is rounded down, which at integer points changes no point
    /// (`2x - 1 >= 0` is `x - 1 >= 0`, `2x == 1` is `false`). `None` when `g` is one or the
    /// constraint has no term, so that a constraint written so already is kept as it is.
    ///
    /// Proof. With `g` dividing every coefficient, the terms' sum is `g*s` for an integer `s`
    /// at every integer point, and `s` is the sum of the divided terms. An equation `g*s + k ==
    /// 0` needs `g | k`, else no point holds it; when `g | k` it is `s + k/g == 0`. An
    /// inequality `g*s + k >= 0` is `s >= -k/g`, and for integer `s` that is `s >=
    /// ceil(-k/g) = -floor(k/g)`, so `s + floor(k/g) >= 0`, which `div_floor` gives (it rounds
    /// toward `-inf` for either sign of `k`, as `g > 0` from `gcd`).
    pub fn reduced(&self) -> Option<Formula> {
        let mut g = Int::ZERO;
        for k in self.lin.terms.values() {
            g = g.gcd(k);
            if g.is_unit() {
                return None;
            }
        }
        if g.is_zero() {
            return None;
        }
        let k = &self.lin.constant;
        if self.rel == Rel::Eq && !k.mod_floor(&g).is_zero() {
            // `false`, written here rather than as `Formula::bottom`, which is defined in the
            // file above this one.
            return Some(Formula::Or(Shared::new(Vec::new())));
        }
        let lin = Lin {
            terms: (self.lin.terms.iter())
                .map(|(a, c)| (a.clone(), c.div_floor(&g)))
                .collect(),
            constant: k.div_floor(&g),
        };
        Some(Formula::Con(Con { lin, rel: self.rel }))
    }

    /// Whether the constraint holds at `values` ([`Formula::holds`]).
    pub(super) fn holds(&self, values: &Model) -> bool {
        self.compares(self.lin.eval(values))
    }

    /// Whether the constraint holds at `values` as the solver reads it ([`Lin::eval_linear`]):
    /// each atom, a product included, a variable of its own. The solver's search tests its
    /// points with this reading, since they give a product a value of its own.
    pub(super) fn holds_linear(&self, values: &Model) -> bool {
        self.compares(self.lin.eval_linear(values))
    }

    /// Whether the value `v` of the constraint's term meets its comparison with zero.
    fn compares(&self, v: Int) -> bool {
        if self.rel == Rel::Eq {
            v.is_zero()
        } else {
            !v.is_negative()
        }
    }
}

impl fmt::Display for Con {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.show(f, as_is)
    }
}

impl Con {
    /// Writes the constraint, each symbol through `name`: the terms with the sign of the
    /// first atom's on the left, positive, and the rest on the right: `a + b <= 49`,
    /// `i <= n - 2`.
    pub(super) fn show(&self, f: &mut fmt::Formatter<'_>, name: Names) -> fmt::Result {
        let Some((_, first)) = self.lin.terms.iter().next() else {
            return write!(
                f,
                "{} {} 0",
                self.lin.constant,
                if self.rel == Rel::Eq { "==" } else { ">=" }
            );
        };
        let neg = first.is_negative();
        let (mut left, mut right) = (Lin::default(), Lin::default());
        for (a, c) in &self.lin.terms {
            if c.is_negative() == neg {
                left.terms.insert(a.clone(), c.abs());
            } else {
                right.terms.insert(a.clone(), c.abs());
            }
        }
        // left_sign * left - right_sign * right + k (rel) 0, with left positive.
        right.constant = if neg {
            self.lin.constant.clone()
        } else {
            -&self.lin.constant
        };
        let op = match (self.rel, neg) {
            (Rel::Eq, _) => "==",
            (Rel::Ge, false) => ">=",
            (Rel::Ge, true) => "<=",
        };
        left.show(f, name)?;
        write!(f, " {op} ")?;
        right.show(f, name)
    }
}

/// The atom of a constraint of one atom, with the least and the greatest value it allows that
/// atom; a least above the greatest allows none.
pub(super) fn one_bound(c: &Con) -> Option<(&Atom, Option<Int>, Option<Int>)> {
    if c.lin.terms.len() != 1 {
        return None;
    }
    let (a, coef) = c.lin.terms.first_key_value()?;
    // `coef·a + k` compared with zero.
    let k = &c.lin.constant;
    let m = coef.abs();
    let (lo, hi) = match c.rel {
        // `a >= -k / coef`, rounded up.
        Rel::Ge if coef.is_positive() => (Some(-&k.div_floor(&m)), None),
        // `a <= k / |coef|`, rounded down.
        Rel::Ge => (None, Some(k.div_floor(&m))),
        Rel::Eq if k.mod_floor(&m).is_zero() => {
            let v = -&k.div_floor(&m);
            let v = if coef.is_positive() { v } else { -&v };
            (Some(v.clone()), Some(v))
        }
        // No integer `a` has `coef·a == -k`.
        Rel::Eq => (Some(Int::ONE), Some(Int::ZERO)),
    };
    Some((a, lo, hi))
}

/// The least and greatest value of each atom, `None` where there is none.
/// The meet of two is [`zedc_int::int::range_meet`], the one copy for `exact`, `local`,
/// `presburger`, zedc-solvers and zedc-preimage (dryA5 row 18; DRY-numeric-shared).
pub(super) type Ends = zedc_int::int::IntRange;
