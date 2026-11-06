//! The formulas of the solver (`super`): atoms, linear terms, constraints and formulas over
//! them, and the key of a compound part held by more than one parent ([`Id`]). The solver
//! and the operations that follow a formula's nesting (`super::deep`) both read these, so
//! they are kept in a file below both.

use std::collections::{BTreeMap, HashSet};
use std::hash::{Hash, Hasher};
use std::slice;
use std::sync::Arc;

use crate::store::int::Int;

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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Lin {
    /// The coefficients.
    pub terms: BTreeMap<Atom, Int>,
    /// The constant.
    pub constant: Int,
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
/// behind an [`Arc`], so a copy costs O(1) and shares them, and a part may be held by many
/// parents: the formula of a `let`-bound test is held once at each use (COMPLEXITY.md S31).
/// Every pass over a formula reads a shared part once per call (`deep`), so its cost is the
/// number of distinct parts. Drop, compare, hash and show do not recurse on its depth. Two
/// formulas are compared as the derived order would compare their trees written out, but a
/// part compared with itself is equal at once: a lookup of a conjunct in the maps keyed by
/// formulas finds the very formula it holds, and would otherwise walk the whole of it.
pub enum Formula {
    /// A constraint.
    Con(Con),
    /// Negation.
    Not(Arc<Formula>),
    /// Conjunction; empty is `true`.
    And(Arc<Vec<Formula>>),
    /// Disjunction; empty is `false`.
    Or(Arc<Vec<Formula>>),
}

/// A satisfying assignment, each atom absent from it zero.
pub type Model = BTreeMap<Atom, Int>;

/// A compound part of a formula, held, so that it lives as long as the key, and compared and
/// hashed as the one part it is, not by its content. Two keys are equal when they hold the
/// same part, so a part that two parents hold is found by either.
pub(super) struct Id(Formula);

impl Clone for Id {
    fn clone(&self) -> Id {
        Id(self.0.clone())
    }
}

impl Id {
    /// The key of `f`, a compound part.
    pub(super) fn any(f: &Formula) -> Id {
        debug_assert!(!matches!(f, Formula::Con(_)), "a compound part");
        Id(f.clone())
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
        let mut stack = vec![f];
        while let Some(g) = stack.pop() {
            for h in g.kids() {
                if matches!(h, Formula::Con(_)) {
                    continue;
                }
                let id = Id::any(h);
                if seen.contains(&id) {
                    twice.insert(id);
                } else {
                    seen.insert(id);
                    stack.push(h);
                }
            }
        }
        twice
    }

    /// Where the part is kept, which names it while the key holds it.
    fn at(&self) -> *const () {
        match &self.0 {
            Formula::Con(_) => unreachable!("a key holds a compound part"),
            Formula::Not(g) => Arc::as_ptr(g).cast(),
            Formula::And(gs) | Formula::Or(gs) => Arc::as_ptr(gs).cast(),
        }
    }
}

impl PartialEq for Id {
    fn eq(&self, other: &Id) -> bool {
        self.at() == other.at()
    }
}

impl Eq for Id {}

impl Hash for Id {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.at().hash(state)
    }
}

impl Formula {
    /// The formulas directly under `self`, in order.
    pub(super) fn kids(&self) -> &[Formula] {
        match self {
            Formula::Con(_) => &[],
            Formula::Not(g) => slice::from_ref(&**g),
            Formula::And(gs) | Formula::Or(gs) => gs,
        }
    }

    /// Whether another holder shares the part, so that a pass may reach it twice.
    pub(super) fn is_shared(&self) -> bool {
        match self {
            Formula::Con(_) => false,
            Formula::Not(g) => Arc::strong_count(g) > 1,
            Formula::And(gs) | Formula::Or(gs) => Arc::strong_count(gs) > 1,
        }
    }
}
