//! The linear-relation domain (DESIGN.md sec:domains, "linear-integer relations among in-scope
//! keys and cardinalities (Presburger)", and sec:verification, rung 2; step L1.38).
//!
//! A relation is a quantifier-free formula over linear constraints with integer coefficients,
//! `t >= 0` and `t == 0`, joined by `&&`, `||` and `!`. A constraint's term is a sum of atoms,
//! each times a coefficient, plus a constant. An atom is a symbol, the product of two symbols,
//! or an auxiliary variable that names a quotient or a remainder by a constant; the formula
//! that defines an auxiliary variable is kept apart from the body, since it fixes the variable
//! for each value of the symbols, so that negating the body never negates a definition.
//!
//! Satisfiability is decided by the Omega test [Omega] on the fragment it settles in a number
//! of steps polynomial in the rows, though not in the bit length of the coefficients, with no
//! budget (docs/thresholds.md, replacement 4), in one loop over a
//! system that holds each set of coefficients once and knows each variable's rows and bound
//! counts, so that a step touches only the rows of the variable it removes. Arithmetic is
//! exact, over unbounded integers. Equalities are solved, with Pugh's symmetric remainder
//! where no coefficient is a unit; two opposite rows that meet become an equality; a variable
//! bounded on one side only is dropped with its rows. Otherwise the variable whose elimination
//! adds the fewest rows, of those the one that writes the fewest terms, is eliminated, exact
//! eliminations first, and only while the system holds no more terms than it was given: each
//! step removes a variable and the terms never pass the input's count. An elimination is
//! exact when every lower or every upper coefficient of the variable is a unit.
//!
//! Before the parts are split, variables whose columns are multiples of one column are merged
//! into one variable ([`quotient`]), a unimodular change of variables that keeps every
//! integer point. Two cases are then decided exactly whatever the eliminations would do. Rows
//! over two variables or fewer are decided by counting the integer points under each piece of
//! their upper and lower envelopes ([`super::twovar`]). Rows `±x ± y + k >= 0` are decided by
//! the parity test on the zero-weight cycles of their tight constraint graph
//! ([`super::utvpi`]); once they are shown to have a point, exact eliminations that add terms
//! are allowed, since each keeps that form, and they are taken only when a model is wanted.
//!
//! When every elimination left would add terms and three variables are live, one with a unit
//! coefficient in every row on one side, its rows are replaced by the O(m) pairs of bounds that
//! [`super::hull3`] chooses, which cut out the same shadow as all pairs. Otherwise the box test
//! decides what it can, in one pass over the terms and with no linear program: each
//! variable's bounds are tightened once by every row from the bounds its bound rows give
//! ([`bounds`]); the rows are empty when one of
//! them is below zero at every point of that box, have a point when one of five points of the
//! box holds every row (the point nearest zero, the lower and upper corners, and the two
//! midpoints, [`box_point`]), and are refused otherwise. At the first inexact elimination
//! the real shadow is tested once ([`relaxed_empty`]): real-shadow eliminations are taken
//! while each adds no terms, and the box test ends it; empty, it shows the problem empty. From
//! there on the dark shadow is solved, whose points are points of the problem. When it has
//! none, the splinters of each dark elimination are searched [Omega, sec. 2.3]: for each lower
//! row `a·x + l >= 0` of the eliminated `x` and `m` its largest upper coefficient, the problem
//! with `a·x + l == k` for a fresh variable `0 <= k <= (a·m - a - m) / m`. The problem has a
//! point exactly when the dark shadow or a splinter has one. A splinter that itself takes a
//! dark shadow with no point is not split again: that, and a system every elimination of which
//! would add terms and which the box test does not decide, are the refusals ([`Refusal`]),
//! each a property of the system's shape. A
//! satisfiable problem yields a model, built only when one is wanted: each eliminated variable
//! takes the value nearest zero that its bounds allow under the values of the variables
//! eliminated after it.
//!
//! A formula with disjunctions is not split into all its conjunctions. Its top-level
//! constraints are the base; a disjunct whose own top-level constraints meet the base nowhere
//! is removed, and a disjunction with one disjunct left adds it to the base, with its own
//! disjunctions read in the same round, until nothing is removed: each round but the last
//! removes a disjunct, so the rounds are at most the disjuncts. No
//! disjunct left is no point. A point is then sought by taking, for each disjunction in turn,
//! the first disjunct that meets the base with the disjuncts already taken, disjuncts and
//! disjunctions being sorted first, so that the order they are written in changes nothing. Where none does,
//! each disjunct whose addition to the base empties it by the rule above is removed, until
//! none is, and the search runs again; where it fails again, the question is refused. A
//! projection is the meet, over the disjunctions, of the union over each one's disjuncts of
//! the projection of the base with that disjunct; with two disjunctions or more left, each
//! finite bound is then moved inward by halving the step, only where the formula with the
//! value past it is shown empty. Each loop removes a disjunct or halves a step, so each ends.
//!
//! Entailment from premises to a goal is the unsatisfiability of the premises with the negated
//! goal. A product of two symbols is an atom of its own, so the test still decides linear
//! facts; before it, for each product the formulas mention, the premises on its factors are
//! multiplied in pairs, once: a premise on a symbol is a top-level linear inequality of the
//! premises that mentions it, or a bound on the symbol that the linear premises imply.
//!
//! A refused question leaves the relation unused, which is sound: the written constraint is
//! kept, and [`Entailment::Refused`] carries the cause. No compiler path calls [`entails`] yet,
//! and a refusal met in narrowing is kept in `product::Scope::refusals`, which
//! `product::Scope::warnings` reports as one warning each, with the constraint it was asked of.
//! Every integer, written or derived, is unbounded.

use std::cell::{Cell, OnceCell};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::mem;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use imbl::OrdSet;

use super::int::Int;
use super::interval::{End, IntervalSet};
use super::linear::Term;
use super::{hull3, twovar, utvpi};

mod deep;

/// A variable of a relation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Atom {
    /// A symbol: an input, a parameter, a key.
    Sym(Arc<str>),
    /// The product of two symbols, in name order.
    Product(Arc<str>, Arc<str>),
    /// An auxiliary variable, defined by the relation's definitions.
    Aux(u32),
}

impl Atom {
    /// The product of two symbols.
    pub fn product(a: &Arc<str>, b: &Arc<str>) -> Atom {
        if a <= b {
            Atom::Product(a.clone(), b.clone())
        } else {
            Atom::Product(b.clone(), a.clone())
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Sym(s) => write!(f, "{s}"),
            Atom::Product(a, b) => write!(f, "{a} * {b}"),
            Atom::Aux(n) => write!(f, "q{n}"),
        }
    }
}

/// Why a question lies outside the fragment the solver decides. Each is reported in its own
/// words (sec:diagnostics), and each is a property of the system's shape, never of its size;
/// narrowing keeps the written constraint, which is sound.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Refusal {
    /// Every elimination of a variable would enlarge the system, which has three variables or
    /// more and is not of the form `±x ± y + k >= 0`; no row is below zero over the box its
    /// bounds give its variables, and each of the five points of that box that `box_point`
    /// tries misses some row.
    Growth,
    /// The integer points could lie only in a splinter of a splinter: a gray shadow within a
    /// gray shadow, whose search is exponential in the variables.
    Shadows,
    /// The search through the disjunctions found no point and removed no disjunct.
    Disjuncts,
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Refusal::Growth => {
                "the integer constraints have three variables or more, each of whose \
                 elimination would enlarge them, so whether they hold at an integer point \
                 is not decided"
            }
            Refusal::Shadows => {
                "an integer point of the integer constraints could lie only in a splinter of a \
                 splinter of their projection, so whether one exists is not decided"
            }
            Refusal::Disjuncts => {
                "no choice among the disjunctions of the integer constraints was settled"
            }
        })
    }
}

/// A linear term: each atom times its coefficient, plus a constant. No coefficient is zero.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Lin {
    /// The coefficients.
    pub terms: BTreeMap<Atom, Int>,
    /// The constant.
    pub constant: Int,
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

    /// `self + other`.
    pub fn plus(&self, other: &Lin) -> Lin {
        let mut out = self.clone();
        for (a, c) in &other.terms {
            let v = out.terms.get(a).map_or_else(|| c.clone(), |o| o + c);
            if v.is_zero() {
                out.terms.remove(a);
            } else {
                out.terms.insert(a.clone(), v);
            }
        }
        out.constant = &out.constant + &other.constant;
        out
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

    /// The product of two terms, its products of two symbols as atoms; `None` when neither
    /// is a constant and either holds an atom that is not a symbol.
    pub fn product(&self, other: &Lin) -> Option<Lin> {
        if self.terms.is_empty() {
            return Some(other.times(self.constant.clone()));
        }
        if other.terms.is_empty() {
            return Some(self.times(other.constant.clone()));
        }
        let sym = |a: &Atom| match a {
            Atom::Sym(x) => Some(x.clone()),
            _ => None,
        };
        let xs: Vec<(Arc<str>, &Int)> = other
            .terms
            .iter()
            .map(|(a, c)| Some((sym(a)?, c)))
            .collect::<Option<_>>()?;
        let ys: Vec<(Arc<str>, &Int)> = self
            .terms
            .iter()
            .map(|(a, c)| Some((sym(a)?, c)))
            .collect::<Option<_>>()?;
        let mut out = self.times(other.constant.clone());
        for (x, c) in &xs {
            out = out.plus(&Lin::atom(Atom::Sym(x.clone())).times(*c * &self.constant));
            for (y, d) in &ys {
                out = out.plus(&Lin::atom(Atom::product(x, y)).times(*c * *d));
            }
        }
        Some(out)
    }

    /// The value at `values`, each atom absent from it zero and each product atom read as the
    /// product of its symbols' values.
    fn eval(&self, values: &Model) -> Int {
        let sym = |s: &Arc<str>| {
            values
                .get(&Atom::Sym(s.clone()))
                .cloned()
                .unwrap_or(Int::ZERO)
        };
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
}

impl fmt::Display for Lin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (a, c) in &self.terms {
            let (sign, m) = if c.is_negative() {
                ("-", -c)
            } else {
                ("+", c.clone())
            };
            match (first, sign) {
                (true, "-") => write!(f, "-")?,
                (true, _) => {}
                (false, s) => write!(f, " {s} ")?,
            }
            if m == Int::ONE {
                write!(f, "{a}")?;
            } else {
                write!(f, "{m} * {a}")?;
            }
            first = false;
        }
        if first {
            write!(f, "{}", self.constant)
        } else if self.constant.is_positive() {
            write!(f, " + {}", self.constant)
        } else if self.constant.is_negative() {
            write!(f, " - {}", -&self.constant)
        } else {
            Ok(())
        }
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

    /// Whether the constraint holds at `values` ([`Formula::holds`]).
    fn holds(&self, values: &Model) -> bool {
        let v = self.lin.eval(values);
        if self.rel == Rel::Eq {
            v.is_zero()
        } else {
            !v.is_negative()
        }
    }
}

impl fmt::Display for Con {
    /// The terms with the sign of the first atom's on the left, positive, and the rest on the
    /// right: `a + b <= 49`, `i <= n - 2`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        write!(f, "{left} {op} {right}")
    }
}

/// A quantifier-free formula over linear constraints. Drop, copy, compare, hash and show do
/// not recurse on its depth (`deep`). Two formulas are compared as the derived order would
/// compare them, but a formula compared with itself is equal at once: a lookup of a conjunct
/// in the maps keyed by formulas finds the very formula it holds, and would otherwise walk the
/// whole of it, a cost of its size per lookup (COMPLEXITY.md S31).
pub enum Formula {
    /// A constraint.
    Con(Con),
    /// Negation.
    Not(Box<Formula>),
    /// Conjunction; empty is `true`.
    And(Vec<Formula>),
    /// Disjunction; empty is `false`.
    Or(Vec<Formula>),
}

impl Formula {
    /// `true`.
    pub fn top() -> Formula {
        Formula::And(Vec::new())
    }

    /// `false`.
    pub fn bottom() -> Formula {
        Formula::Or(Vec::new())
    }

    /// The conjunction, flattened, `true` dropped and `false` absorbing.
    pub fn and(fs: Vec<Formula>) -> Formula {
        let mut flat = Vec::new();
        for f in fs {
            match f {
                Formula::And(_) => flat.extend(f.into_parts().expect("a conjunction")),
                Formula::Or(ref gs) if gs.is_empty() => return Formula::bottom(),
                g => flat.push(g),
            }
        }
        // Of two constraints on one term, the tighter alone, in the place of the first.
        let mut out: Vec<Formula> = Vec::new();
        let mut at: BTreeMap<(BTreeMap<Atom, Int>, Rel), usize> = BTreeMap::new();
        for g in flat {
            let Formula::Con(c) = &g else {
                out.push(g);
                continue;
            };
            let key = (c.lin.terms.clone(), c.rel);
            match at.get(&key) {
                Some(&i) => {
                    let Formula::Con(old) = &out[i] else {
                        unreachable!("a constraint")
                    };
                    if c.rel == Rel::Ge && c.lin.constant < old.lin.constant {
                        out[i] = g;
                    } else if c.rel == Rel::Eq && c.lin.constant != old.lin.constant {
                        return Formula::bottom();
                    }
                }
                None => {
                    at.insert(key, out.len());
                    out.push(g);
                }
            }
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::And(out)
        }
    }

    /// The disjunction, flattened, `false` dropped and `true` absorbing, and `true` when two
    /// disjuncts are complements (`Formula::complementary`).
    pub fn or(fs: Vec<Formula>) -> Formula {
        let mut out = Vec::new();
        for f in fs {
            match f {
                Formula::Or(_) => out.extend(f.into_parts().expect("a disjunction")),
                Formula::And(ref gs) if gs.is_empty() => return Formula::top(),
                g => out.push(g),
            }
        }
        if Formula::complementary(&out) {
            return Formula::top();
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::Or(out)
        }
    }

    /// Whether two of `fs` are each other's complements, so that their disjunction is `true`:
    /// a constraint `c` and `!c`, or `t >= 0` and `s >= 0` with `t + s` a constant of at least
    /// `-1`, since at an integer point `t <= -1` makes `s >= 0`. Each disjunct that is a
    /// constraint or the negation of one is looked up once by its content, so the check costs
    /// the size of the constraints in `fs` and never the depth of a compound disjunct.
    // Complexity tradeoff: a compound `g || !g`, with `g` a conjunction or disjunction, is not
    // found and stays a disjunction. That is sound, since the disjunction holds at every point,
    // but each later test splits into its cases, as before this check (COMPLEXITY.md S20).
    // Looking `g` up by its content hashes it through its whole depth on every `Formula::or`,
    // and `map_cons`, `nnf` and `forget` call `or` once per `Or` node, so a nested or/and
    // formula would cost its size times its depth (62 times the work for 8 times the depth,
    // measured at d = 500 to 4000). The trigger is a disjunct that is not a constraint. Tests
    // in `l01_39_reduced_product::linked`: `a_disjunction_of_a_constraint_and_its_complement_is_true`
    // and `a_nested_or_and_formula_is_built_and_mapped_in_time_near_its_size`. A complete check
    // needs a hash of each formula kept in its node when it is built, so that the lookup costs
    // O(1) per disjunct.
    fn complementary(fs: &[Formula]) -> bool {
        if fs.len() < 2 {
            return false;
        }
        let mut ge: HashMap<&BTreeMap<Atom, Int>, &Int> = HashMap::new();
        let mut whole: std::collections::HashSet<&Con> = std::collections::HashSet::new();
        for f in fs {
            let Formula::Con(c) = f else { continue };
            whole.insert(c);
            if c.rel == Rel::Ge {
                // Of two disjuncts on one term, the weaker, the larger constant, decides.
                let k = ge.entry(&c.lin.terms).or_insert(&c.lin.constant);
                if c.lin.constant > **k {
                    *k = &c.lin.constant;
                }
            }
        }
        fs.iter().any(|f| match f {
            Formula::Not(g) => matches!(&**g, Formula::Con(c) if whole.contains(c)),
            Formula::Con(c) if c.rel == Rel::Ge => {
                let neg: BTreeMap<Atom, Int> =
                    c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect();
                ge.get(&neg)
                    .is_some_and(|k| &c.lin.constant + *k >= Int::from(-1i64))
            }
            _ => false,
        })
    }

    /// The disjunction of `a` and `b` with the conjuncts they share taken out of it, so that
    /// joining two narrowings of one relation does not copy the relation into each disjunct.
    /// Each constraint of the rest of each side is replaced by `rest` of it.
    pub fn either(a: &Formula, b: &Formula, rest: &dyn Fn(&Con) -> Formula) -> Formula {
        fn parts(f: &Formula) -> &[Formula] {
            match f {
                Formula::And(gs) => gs,
                g => std::slice::from_ref(g),
            }
        }
        let (pa, pb) = (parts(a), parts(b));
        let in_b: std::collections::HashSet<&Formula> = pb.iter().collect();
        let shared: std::collections::HashSet<&Formula> =
            pa.iter().filter(|g| in_b.contains(g)).collect();
        let left = |p: &[Formula]| {
            Formula::and(
                p.iter()
                    .filter(|g| !shared.contains(g))
                    .map(|g| g.map_cons(rest))
                    .collect(),
            )
        };
        let mut out: Vec<Formula> = pa.iter().filter(|g| shared.contains(g)).cloned().collect();
        out.push(Formula::or(vec![left(pa), left(pb)]));
        Formula::and(out)
    }

    /// The formula with every constraint that mentions `sym`, alone or in a product,
    /// replaced by `true` where it occurs under an even number of negations and by `false`
    /// where under an odd number: a formula implied by `self` that says nothing of `sym`.
    pub fn forget(&self, sym: &Arc<str>) -> Formula {
        // The context is whether the part is under an even number of negations.
        self.fold(
            true,
            |g, pos| pos != matches!(g, Formula::Not(_)),
            |g, pos, parts| match g {
                Formula::Con(c) => {
                    let mentions = c.lin.terms.keys().any(|a| match a {
                        Atom::Sym(n) => n == sym,
                        Atom::Product(x, y) => x == sym || y == sym,
                        Atom::Aux(_) => false,
                    });
                    match (mentions, pos) {
                        (false, _) => g.clone(),
                        (true, true) => Formula::top(),
                        (true, false) => Formula::bottom(),
                    }
                }
                Formula::Not(_) | Formula::And(_) | Formula::Or(_) => g.rebuild(parts),
            },
        )
    }

    /// The formula with each constraint `c` replaced by `f(c)`.
    pub fn map_cons(&self, f: &dyn Fn(&Con) -> Formula) -> Formula {
        self.fold(
            (),
            |_, ()| (),
            |g, (), parts| match g {
                Formula::Con(c) => f(c),
                Formula::Not(_) | Formula::And(_) | Formula::Or(_) => g.rebuild(parts),
            },
        )
    }

    /// The node `self` with `parts` in place of its parts, through [`Formula::negate`],
    /// [`Formula::and`] or [`Formula::or`]; a constraint has no parts and is copied.
    fn rebuild(&self, mut parts: Vec<Formula>) -> Formula {
        match self {
            Formula::Con(c) => Formula::Con(c.clone()),
            Formula::Not(_) => Formula::negate(parts.pop().expect("one part")),
            Formula::And(_) => Formula::and(parts),
            Formula::Or(_) => Formula::or(parts),
        }
    }

    /// The negation, with double negations and constants removed.
    pub fn negate(f: Formula) -> Formula {
        match f {
            Formula::Not(_) => f.into_negated().expect("a negation"),
            Formula::And(ref gs) if gs.is_empty() => Formula::bottom(),
            Formula::Or(ref gs) if gs.is_empty() => Formula::top(),
            g => Formula::Not(Box::new(g)),
        }
    }

    /// Each constraint, in order.
    pub fn cons(&self) -> Vec<&Con> {
        let mut out = Vec::new();
        self.walk(&mut |c| out.push(c));
        out
    }

    /// Each atom, in order.
    pub fn atoms(&self) -> BTreeSet<Atom> {
        self.cons()
            .into_iter()
            .flat_map(|c| c.lin.terms.keys().cloned())
            .collect()
    }

    /// Whether the formula holds at `values`; an absent atom is zero, and a product atom is
    /// read as the product of its symbols' values.
    /// Each product is read where it is met, so a disjunct that is decided by its first part is
    /// not walked through.
    pub fn holds(&self, values: &Model) -> bool {
        self.holds_as(values)
    }

    /// The top-level conjuncts.
    fn conjuncts(&self) -> Vec<&Formula> {
        match self {
            Formula::And(gs) => gs.iter().collect(),
            g => vec![g],
        }
    }
}

/// A relation: a body, and the definitions of its auxiliary variables, each of which fixes
/// one auxiliary variable for every value of the others.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Relation {
    /// The body.
    pub body: Formula,
    /// The definitions, each an auxiliary variable and the formula that fixes it.
    pub defs: Vec<(u32, String, Formula)>,
}

impl Relation {
    /// The relation `body`, with no auxiliary variable.
    pub fn of(body: Formula) -> Relation {
        Relation {
            body,
            defs: Vec::new(),
        }
    }

    /// The definitions, as one formula.
    pub fn defined(&self) -> Formula {
        Formula::and(self.defs.iter().map(|(_, _, f)| f.clone()).collect())
    }
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body)?;
        for (i, (n, what, _)) in self.defs.iter().enumerate() {
            write!(f, "{} q{n} = {what}", if i == 0 { " where" } else { "," })?;
        }
        Ok(())
    }
}

/// A satisfying assignment, each atom absent from it zero.
pub type Model = BTreeMap<Atom, Int>;

/// Whether `f` holds somewhere, and where.
pub fn satisfiable(f: &Formula) -> Result<Option<Model>, Refusal> {
    match propagate(f)? {
        None => Ok(None),
        Some(p) => found(p),
    }
}

/// Whether `f` holds somewhere. A conjunction is decided without building a point; a point is
/// built only to search the disjunctions that propagation leaves.
pub fn decide(f: &Formula) -> Result<bool, Refusal> {
    match propagate(f)? {
        None => Ok(false),
        Some(p) if p.ors.is_empty() => Ok(true),
        Some(p) => Ok(found(p)?.is_some()),
    }
}

/// A point of the propagated parts `p`, or `None` when the search removes every disjunct of
/// a disjunction.
fn found(p: Parts) -> Result<Option<Model>, Refusal> {
    if let Ok(m) = pick(&p, true) {
        return Ok(Some(m));
    }
    match probe(p)? {
        None => Ok(None),
        Some(p) => pick(&p, true).map(Some),
    }
}

/// `c` with each atom outside `free` replaced by its value in `model`.
fn specialize_con(c: &Con, free: &BTreeSet<Atom>, model: &Model) -> Con {
    let mut terms = BTreeMap::new();
    let mut k = c.lin.constant.clone();
    for (a, coef) in &c.lin.terms {
        if free.contains(a) {
            terms.insert(a.clone(), coef.clone());
        } else if let Some(val) = model.get(a) {
            k = &k + &(coef * val);
        }
    }
    Con {
        lin: Lin { terms, constant: k },
        rel: c.rel,
    }
}
/// The variables of `extra` re-solved with their neighbors fixed at `model`: with `extra`, the
/// constraints taken so far that link a variable of `extra` to others, specialized at `model`,
/// and each variable's bounds.
fn local_repair(acc: &[Con], near: &Near, model: &Model, extra: &[Con]) -> Option<Model> {
    let seed: BTreeSet<Atom> = extra
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect();
    if seed.is_empty() {
        return None;
    }
    let mut ids = BTreeSet::new();
    let mut local: Vec<Con> = extra.to_vec();
    for a in &seed {
        if let Some(v) = near.by_atom.get(a) {
            ids.extend(v.iter().copied());
        }
        near.bounds(a, &mut local);
    }
    for id in ids {
        local.push(specialize_con(&acc[id], &seed, model));
    }
    let mut m = solve(&local, true).ok()??;
    for a in seed {
        m.entry(a).or_insert(Int::ZERO);
    }
    Some(m)
}

thread_local! {
    /// The parts [`Parts::witness`] has tested on this thread since [`parts_tested`] was last
    /// called.
    static TESTED: Cell<u64> = const { Cell::new(0) };
}

/// The number of parts (a disjunct and its own constraints) that the search for a point has
/// tested against its values on this thread since the last call, which resets it. A test reads
/// it to count that work directly.
pub fn parts_tested() -> u64 {
    TESTED.replace(0)
}

/// A stamp no search has used before ([`Parts::witness`]); zero is never one.
fn fresh_stamp() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_add(1, AtomicOrdering::Relaxed)
}

/// A point of `p`, taking for each disjunction in turn the first disjunct that meets the
/// constraints taken so far, or a refusal when none does. Unless `deep`, the disjunctions
/// within a disjunct are not read: the model is then a point of the parts with each disjunct
/// cut to its own constraints, which have more points than the parts.
///
/// Complexity tradeoff: the choice of a disjunct is never undone, so a formula whose point
/// needs an earlier disjunction decided another way gets `Refusal::Disjuncts` ("not decided")
/// here; `probe` then removes the disjuncts it shows empty, and what is still refused stays
/// refused. Why: finding a point of a conjunction of disjunctions of linear rows is
/// NP-complete (graph 3-coloring is such a formula: one disjunction of three colors per
/// node, one row per edge), so a search that backtracks is exponential in the disjunctions.
/// Trigger: two or more disjunctions whose disjuncts conflict through shared variables,
/// whatever the size. Tests: `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`
/// (four tasks in three slots), `l01_38_presburger::omega::a_disjunct_refused_by_the_solver_is_reported_by_its_own_cause`.
/// COMPLEXITY.md rows S16 and S18. A complete solution would backtrack over the disjuncts
/// (DPLL(T) with learned conflicts), exponential in the worst case.
fn pick(p: &Parts, deep: bool) -> Result<Model, Refusal> {
    let mut model = solve(&p.cons, true)?.ok_or(Refusal::Disjuncts)?;
    let mut acc = Linked::default();
    let mut near = Near::default();
    // Adds the constraints of a disjunct taken, a bound taken again kept once ([`Linked::meet`]).
    // A bound on one atom that [`Linked::meet`] puts in the place of a weaker one still tightens
    // that atom's bounds in `near`; a constraint of more atoms put in place keeps its atoms, so
    // its entries in `near` stand.
    fn take(cons: &[Con], acc: &mut Linked, near: &mut Near) {
        for c in cons {
            let i = acc.cons.len();
            if acc.meet(c.clone()) || c.lin.terms.len() == 1 {
                near.add(i, c);
            }
        }
    }
    take(&p.cons, &mut acc, &mut near);
    // The disjunctions left, read in place: only the disjuncts taken are entered.
    let mut queue: Vec<&[Rc<Parts>]> = p.ors.iter().map(Vec::as_slice).collect();
    // The disjuncts that hold at the model, found by [`Parts::witness`].
    let mut held: Vec<&Parts> = Vec::new();
    // A new stamp each time the model changes, under which a part found not to hold at the
    // model is not read again ([`Parts::witness`]).
    let mut stamp = fresh_stamp();
    'next: while let Some(ds) = queue.pop() {
        // A disjunct that holds at the model is taken with the disjunct that holds first in
        // each disjunction below it, which reading those disjunctions one by one would take,
        // the model being unchanged; so the nest below is read once, not again at each level.
        for d in ds {
            held.clear();
            let holds = if deep {
                d.witness(&model, stamp, &mut held)
            } else {
                held.push(d);
                d.cons.iter().all(|c| c.holds(&model))
            };
            if holds {
                held.iter().for_each(|h| take(&h.cons, &mut acc, &mut near));
                continue 'next;
            }
        }
        let mut taken: Option<(&Parts, Model)> = None;
        let mut why = Refusal::Disjuncts;
        for d in ds {
            // A disjunct whose constraints hold at the model, though the disjunctions below it
            // may not, is taken with the model unchanged, so that the parts found not to hold
            // below it are not read again.
            if d.cons.iter().all(|c| c.holds(&model)) {
                taken = Some((d, Model::new()));
                break;
            }
            if let Some(m) = local_repair(&acc.cons, &near, &model, &d.cons) {
                taken = Some((d, m));
                break;
            }
        }
        for d in ds {
            if taken.is_some() {
                break;
            }
            let mut cs = acc.around(&d.cons);
            cs.extend(d.cons.iter());
            match solve(&cs, true) {
                Ok(Some(m)) => {
                    taken = Some((d, m));
                    break;
                }
                Ok(None) => {}
                Err(r) => why = r,
            }
        }
        let Some((d, m)) = taken else {
            return Err(why);
        };
        // A change of any value drops every mark, not only the marks of the parts that mention
        // it, yet no part is read again below each level: a part is marked by the first walk
        // that reaches it and fails, at the disjunction `D` popped then. The disjunctions
        // popped after `D` and before the one that holds the part are those of the disjuncts
        // taken on the way down, read last to first as that walk read them; each was found to
        // hold by that walk, and each disjunct on the way has its constraints holding, so it is
        // taken with the model unchanged. A disjunct taken earlier in its disjunction leaves
        // the part unread. So the model is the same when the part is reached again, and its
        // mark holds. Test `l01_39_reduced_product::deep_condition::the_search_for_a_point_tests_each_part_of_a_deep_test_a_bounded_number_of_times`
        // counts the parts tested ([`parts_tested`]) (COMPLEXITY S31).
        if m.iter().any(|(a, v)| model.get(a) != Some(v)) {
            stamp = fresh_stamp();
        }
        model.extend(m);
        take(&d.cons, &mut acc, &mut near);
        if deep {
            queue.extend(d.ors.iter().map(Vec::as_slice));
        }
    }
    Ok(model)
}

/// The constraints taken so far by [`pick`], indexed for [`local_repair`]: each constraint of
/// two or more atoms under each of its atoms, and the constraints of one atom as that atom's
/// bounds. A repair then costs the constraints that link its atoms to others and two bounds
/// for each atom, not every constraint an atom has had alone: on a chain of `k` guards
/// `i >= j` on one input, listing them made the repair of each of the `k` levels cost `k`.
#[derive(Default)]
struct Near {
    by_atom: BTreeMap<Atom, Vec<usize>>,
    /// The least and the greatest value of an atom; a least above the greatest leaves none.
    one: BTreeMap<Atom, (Option<Int>, Option<Int>)>,
}

impl Near {
    /// Adds the constraint `c`, numbered `i` among those taken.
    fn add(&mut self, i: usize, c: &Con) {
        let mut terms = c.lin.terms.iter();
        let (Some((a, coef)), None) = (terms.next(), terms.next()) else {
            for a in c.lin.terms.keys() {
                self.by_atom.entry(a.clone()).or_default().push(i);
            }
            return;
        };
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
        let (l, h) = self.one.entry(a.clone()).or_default();
        if let Some(lo) = lo
            && l.as_ref().is_none_or(|l| lo > *l)
        {
            *l = Some(lo);
        }
        if let Some(hi) = hi
            && h.as_ref().is_none_or(|h| hi < *h)
        {
            *h = Some(hi);
        }
    }

    /// Pushes the bounds of `a` onto `out` as constraints.
    fn bounds(&self, a: &Atom, out: &mut Vec<Con>) {
        let Some((lo, hi)) = self.one.get(a) else {
            return;
        };
        let x = Lin::atom(a.clone());
        if let Some(lo) = lo {
            out.push(Con::ge(&x, &Lin::constant(lo.clone())));
        }
        if let Some(hi) = hi {
            out.push(Con::ge(&Lin::constant(hi.clone()), &x));
        }
    }
}

/// Constraints grouped by the variables they share, so that a question about a few variables
/// solves only the constraints it can meet: variables that share no constraint do not interact,
/// and the rest are known to have a point.
#[derive(Default)]
struct Linked {
    cons: Vec<Con>,
    ids: BTreeMap<Atom, usize>,
    parent: Vec<usize>,
    /// At each root, its constraints.
    held: Vec<Vec<usize>>,
    /// For the constraints added by [`Linked::meet`], the index of each term's constraint,
    /// keyed by the term without its constant and by the comparison.
    by_terms: HashMap<(BTreeMap<Atom, Int>, Rel), usize>,
}

impl Linked {
    fn of(cons: Vec<Con>) -> Linked {
        let mut l = Linked::default();
        cons.into_iter().for_each(|c| l.add(c));
        l
    }

    /// [`Linked::of`] with each constraint added by [`Linked::meet`].
    fn reduced(cons: Vec<Con>) -> Linked {
        let mut l = Linked::default();
        cons.into_iter().for_each(|c| {
            l.meet(c);
        });
        l
    }

    /// Adds a constraint unless one with the same term and comparison already implies it: of
    /// `t + a >= 0` and `t + b >= 0` only the one with the smaller constant is kept, in the
    /// place of the other, and an equality is not added twice. A bound written again at each
    /// level of a nest then adds nothing to the group of its atoms.
    /// Whether it is added at the end of `cons`; a constraint put in the place of another has
    /// the same atoms.
    fn meet(&mut self, c: Con) -> bool {
        let key = (c.lin.terms.clone(), c.rel);
        match self.by_terms.get(&key) {
            Some(&i) => {
                let old = &self.cons[i].lin.constant;
                match c.rel {
                    Rel::Ge if c.lin.constant < *old => self.cons[i] = c,
                    Rel::Ge => {}
                    Rel::Eq if c.lin.constant == *old => {}
                    Rel::Eq => {
                        self.add(c);
                        return true;
                    }
                }
                false
            }
            None => {
                self.by_terms.insert(key, self.cons.len());
                self.add(c);
                true
            }
        }
    }

    fn id(&mut self, a: &Atom) -> usize {
        if let Some(i) = self.ids.get(a) {
            return *i;
        }
        let i = self.parent.len();
        self.ids.insert(a.clone(), i);
        self.parent.push(i);
        self.held.push(Vec::new());
        i
    }

    fn root(&self, mut i: usize) -> usize {
        while self.parent[i] != i {
            i = self.parent[i];
        }
        i
    }

    /// Adds a constraint; the smaller group joins the larger, so a root is found in `log` steps.
    fn add(&mut self, c: Con) {
        let n = self.cons.len();
        let ids: Vec<usize> = c.lin.terms.keys().map(|a| self.id(a)).collect();
        self.cons.push(c);
        let Some(first) = ids.first() else {
            return;
        };
        let mut r = self.root(*first);
        for i in &ids[1..] {
            let o = self.root(*i);
            if o != r {
                let (big, small) = if self.held[r].len() < self.held[o].len() {
                    (o, r)
                } else {
                    (r, o)
                };
                let moved = std::mem::take(&mut self.held[small]);
                self.held[big].extend(moved);
                self.parent[small] = big;
                r = big;
            }
        }
        self.held[r].push(n);
    }

    /// The constraints in the groups of the atoms of `cs`, in no particular order.
    fn around(&self, cs: &[Con]) -> Vec<&Con> {
        let roots: BTreeSet<usize> = cs
            .iter()
            .flat_map(|c| c.lin.terms.keys())
            .filter_map(|a| self.ids.get(a).map(|i| self.root(*i)))
            .collect();
        roots
            .into_iter()
            .flat_map(|r| self.held[r].iter().map(|i| &self.cons[*i]))
            .collect()
    }
}

/// `p` with each disjunct removed whose addition, propagated, leaves no point, until none is
/// removed, or `None` when `p` has no point. Each round but the last removes a disjunct, and
/// each tests every disjunct by one propagation, so the work is polynomial in the disjuncts.
///
/// A disjunct that holds at a point of the formula is kept without its test: removing a
/// disjunct that meets the rest nowhere leaves the formula's points as they were, so a point
/// found once is a point of every later state, and propagation, which removes a disjunct only
/// on a proof that it has no point with the rest, never removes one that holds there. The
/// result is the one the tests give. The points are found by [`pick`] on the parts of a test,
/// trying first the disjuncts that no point found so far holds: on a chain of `k` guards
/// `i >= j` on one input, two points (at the least and the greatest `i` the chain allows)
/// keep every disjunct but the `O(1)` that propagation removes, where testing each of the
/// `2k` disjuncts by a propagation of all `2k` disjunctions cost `k^2` (ledger LIN-probe).
fn probe(mut p: Parts) -> Result<Option<Parts>, Refusal> {
    let mut points: Vec<Model> = Vec::new();
    loop {
        let mut changed = false;
        // For each disjunct of each disjunction, whether a point found so far holds it.
        let mut held: Vec<Vec<bool>> = p
            .ors
            .iter()
            .map(|o| {
                o.iter()
                    .map(|d| points.iter().any(|m| d.holds(m)))
                    .collect()
            })
            .collect();
        for i in 0..p.ors.len() {
            let ds = std::mem::take(&mut p.ors[i]);
            let flags = std::mem::take(&mut held[i]);
            // The points found while this disjunction is tested, which its flags do not count.
            let since = points.len();
            let n = ds.len();
            let mut live = Vec::with_capacity(n);
            let mut live_held = Vec::with_capacity(n);
            for (d, h) in ds.into_iter().zip(flags) {
                if h || points[since..].iter().any(|m| d.holds(m)) {
                    live.push(d);
                    live_held.push(true);
                    continue;
                }
                if let Some(m) = point_with(&p, &held, &d) {
                    for (o, hs) in p.ors.iter().zip(held.iter_mut()) {
                        for (e, h) in o.iter().zip(hs.iter_mut()) {
                            *h = *h || e.holds(&m);
                        }
                    }
                    points.push(m);
                    live.push(d);
                    live_held.push(true);
                    continue;
                }
                // Complexity tradeoff: a disjunct that no point holds is still tested by one
                // propagation of all the parts, so `r` disjuncts that propagation removes cost
                // `r` propagations of the whole formula, and failed-literal probing stays
                // polynomial, not `O(n log n)`, when `r` grows with `n` (`cross` from `k = 51`
                // to `99`, the `k - 50` guards no input meets: COMPLEXITY.md S22). Tests:
                // `l01_25_preimage_catalog::s22::chains_on_two_inputs_keep_their_boxes`
                // reaches it (cross at `k = 51`), and `chain_cross_above_its_width_scales`
                // (cross at 12 and 96, `#[ignore]`, ledger LIN-probe-refute: 256 times) measures it.
                // Keeping the results identical needs the same proof of each removal; a
                // removal proved once for several disjuncts would need a propagation that
                // reports which disjuncts it refutes, which `settle` does not, or undoable
                // (trail-based) propagation so a test costs only what it touches.
                let mut q = Parts {
                    cons: p.cons.clone(),
                    ors: p.ors.iter().filter(|o| !o.is_empty()).cloned().collect(),
                    atoms: OnceCell::new(),
                    failed: Cell::new(0),
                };
                q.put(&d);
                if !matches!(settle(q), Ok(None)) {
                    live.push(d);
                    live_held.push(false);
                }
            }
            changed |= live.len() < n;
            if live.is_empty() {
                return Ok(None);
            }
            p.ors[i] = live;
            held[i] = live_held;
        }
        if !changed {
            return Ok(Some(p));
        }
        match settle(p)? {
            None => return Ok(None),
            Some(q) => p = q,
        }
    }
}

/// A point of the formula of [`probe`]'s parts `p` where the disjunct `d` holds, `d` being a
/// disjunct of the disjunction that `p` lacks while it is tested, or `None` when [`pick`]
/// finds none. In each other disjunction `pick` tries first the disjuncts that `held` marks as
/// held by no point, so that the point holds as many of them as its search reaches. The point
/// is checked against every part, so that a disjunct is kept by a point and not by trust in
/// the search.
fn point_with(p: &Parts, held: &[Vec<bool>], d: &Parts) -> Option<Model> {
    let others = || p.ors.iter().zip(held).filter(|(o, _)| !o.is_empty());
    let mut q = Parts {
        cons: p.cons.clone(),
        ors: others()
            .map(|(o, hs)| {
                let new = o.iter().zip(hs).filter(|(_, h)| !**h);
                let old = o.iter().zip(hs).filter(|(_, h)| **h);
                new.chain(old).map(|(e, _)| e.clone()).collect()
            })
            .collect(),
        atoms: OnceCell::new(),
        failed: Cell::new(0),
    };
    q.put(d);
    let m = pick(&q, true).ok()?;
    let meets = d.holds(&m)
        && p.cons.iter().all(|c| c.holds(&m))
        && others().all(|(o, _)| o.iter().any(|e| e.holds(&m)));
    meets.then_some(m)
}

/// A formula in negation normal form as its top-level constraints and its top-level
/// disjunctions, each a list of disjuncts, each disjunct the parts of it. A disjunct is shared,
/// not copied, when it is handed to a search or a level below, so that a disjunction nested
/// `d` deep is copied at no level above it.
#[derive(Clone, Default)]
struct Parts {
    cons: Vec<Con>,
    ors: Vec<Vec<Rc<Parts>>>,
    /// The atoms of the parts, found the first time they are asked for ([`Parts::atoms`]).
    /// They are asked only of a disjunct, which is not changed once it is made.
    atoms: OnceCell<OrdSet<Atom>>,
    /// The stamp of the last search ([`Parts::witness`]) that found the parts not to hold at its
    /// values, so that the search does not read them again while its values are unchanged.
    failed: Cell<u64>,
}

/// Drops the disjuncts nested below on an explicit stack, not by recursion on their depth
/// (COMPLEXITY.md S27). A disjunct still shared elsewhere is left to its other holders.
impl Drop for Parts {
    fn drop(&mut self) {
        if self.ors.is_empty() {
            return;
        }
        let mut stack: Vec<Rc<Parts>> = self.ors.drain(..).flatten().collect();
        while let Some(d) = stack.pop() {
            if let Ok(mut p) = Rc::try_unwrap(d) {
                stack.extend(p.ors.drain(..).flatten());
            }
        }
    }
}

impl Parts {
    /// The parts of a formula in negation normal form. The disjuncts nested below are made on
    /// an explicit stack, each before the disjunct that holds it, so that a nest of any depth
    /// is read without recursion (COMPLEXITY.md S27).
    fn of(f: Formula) -> Parts {
        /// A part being made: its disjunctions not yet entered, last first, and the disjunction
        /// being entered, as its disjuncts left and those made.
        struct Frame {
            p: Parts,
            todo: Vec<Vec<Formula>>,
            arms: Option<(std::vec::IntoIter<Formula>, Vec<Rc<Parts>>)>,
        }
        fn open(f: Formula) -> Frame {
            let mut p = Parts::default();
            let mut todo = Vec::new();
            let mut stack = vec![f];
            while let Some(mut g) = stack.pop() {
                match &mut g {
                    Formula::Con(c) => p.cons.push(Con::take(c)),
                    // Reversed, so the conjuncts are added in order.
                    Formula::And(gs) => stack.extend(mem::take(gs).into_iter().rev()),
                    Formula::Or(gs) => todo.push(mem::take(gs)),
                    Formula::Not(_) => unreachable!("a formula in negation normal form"),
                }
            }
            todo.reverse();
            Frame {
                p,
                todo,
                arms: None,
            }
        }
        let mut stack = vec![open(f)];
        let mut made: Option<Parts> = None;
        while let Some(top) = stack.last_mut() {
            if let (Some(q), Some((_, done))) = (made.take(), &mut top.arms) {
                done.push(Rc::new(q));
            }
            if let Some((left, done)) = &mut top.arms {
                if let Some(g) = left.next() {
                    stack.push(open(g));
                    continue;
                }
                top.p.ors.push(mem::take(done));
                top.arms = None;
            }
            if let Some(ds) = top.todo.pop() {
                top.arms = Some((ds.into_iter(), Vec::new()));
                continue;
            }
            let p = stack.pop().expect("the top frame").p;
            if stack.is_empty() {
                return p;
            }
            made = Some(p);
        }
        unreachable!("the root returns")
    }

    /// Adds the parts of the disjunct `d`, sharing its disjunctions.
    fn put(&mut self, d: &Parts) {
        self.cons.extend(d.cons.iter().cloned());
        self.ors.extend(d.ors.iter().cloned());
    }

    /// Whether the parts hold at `values` ([`Formula::holds`]).
    fn holds(&self, values: &Model) -> bool {
        self.witness(values, fresh_stamp(), &mut Vec::new())
    }

    /// Whether the parts hold at `values` ([`Formula::holds`]), and if so, in `out`, the parts
    /// and, below them, the first disjunct of each disjunction that holds there, each before
    /// the disjuncts taken below it and the disjunctions read last to first, the order in
    /// which [`pick`] reads them. A disjunction is read until a disjunct holds, and each part
    /// is entered at most once, so the cost is at most the size of the parts. A part found not
    /// to hold is marked with `stamp`, and a part so marked is not entered again: a caller
    /// passes a new stamp whenever `values` change.
    fn witness<'a>(&'a self, values: &Model, stamp: u64, out: &mut Vec<&'a Parts>) -> bool {
        let fails = |p: &Parts| {
            let no = p.failed.get() == stamp || {
                TESTED.set(TESTED.get() + 1);
                !p.cons.iter().all(|c| c.holds(values))
            };
            if no {
                p.failed.set(stamp);
            }
            no
        };
        /// A part entered: the disjunctions not yet shown to hold are `p.ors[..left]`, the
        /// last of them read at its disjunct `at`, and `mark` is the length of `out` before
        /// that disjunct was entered.
        struct Frame<'a> {
            p: &'a Parts,
            left: usize,
            at: usize,
            mark: usize,
        }
        let start = out.len();
        if fails(self) {
            return false;
        }
        out.push(self);
        // An explicit stack, since a nest can be deeper than a thread's stack allows.
        let mut stack = vec![Frame {
            p: self,
            left: self.ors.len(),
            at: 0,
            mark: out.len(),
        }];
        while let Some(top) = stack.last_mut() {
            if top.left == 0 {
                // Every disjunction of the part holds: the part holds, and the disjunct of the
                // part above it that it is holds.
                stack.pop();
                if let Some(up) = stack.last_mut() {
                    up.left -= 1;
                    up.at = 0;
                    up.mark = out.len();
                }
                continue;
            }
            let ds = &top.p.ors[top.left - 1];
            let Some(d) = ds.get(top.at) else {
                // No disjunct holds: the part fails, and the part above tries its next one.
                top.p.failed.set(stamp);
                stack.pop();
                let Some(up) = stack.last_mut() else {
                    out.truncate(start);
                    return false;
                };
                out.truncate(up.mark);
                up.at += 1;
                continue;
            };
            if !fails(d) {
                out.push(d);
                stack.push(Frame {
                    p: d,
                    left: d.ors.len(),
                    at: 0,
                    mark: out.len(),
                });
            } else {
                top.at += 1;
            }
        }
        true
    }

    /// The atoms of the parts. Each disjunct's set is found once, from its disjuncts' sets:
    /// it starts as the largest of them, shared, and the atoms of the others and of its own
    /// constraints are added to it. An atom is then added only to a set at least twice the
    /// size of the one it came from, so the sets of a nest of `n` constraints cost
    /// O(n log² n) together, however deep it is, and asking again costs nothing.
    fn atoms(&self) -> &OrdSet<Atom> {
        // An explicit stack, since a nest can be deeper than a thread's stack allows; a
        // disjunct shared by two disjunctions is found once, its set marking it as visited.
        let mut stack: Vec<&Parts> = vec![self];
        while let Some(&p) = stack.last() {
            if p.atoms.get().is_some() {
                stack.pop();
                continue;
            }
            let open = stack.len();
            let below = p.ors.iter().flatten().map(|d| &**d);
            stack.extend(below.filter(|d| d.atoms.get().is_none()));
            if stack.len() > open {
                continue;
            }
            stack.pop();
            let mut sets: Vec<&OrdSet<Atom>> = (p.ors.iter().flatten())
                .map(|d| d.atoms.get().expect("a set found below"))
                .collect();
            let largest = (0..sets.len()).max_by_key(|&i| sets[i].len());
            let mut set = largest.map_or_else(OrdSet::new, |i| sets.swap_remove(i).clone());
            for a in sets.into_iter().flatten() {
                set.insert(a.clone());
            }
            for c in &p.cons {
                for a in c.lin.terms.keys() {
                    set.insert(a.clone());
                }
            }
            let _ = p.atoms.set(set);
        }
        self.atoms.get().expect("the set just found")
    }
}

/// `f`, negated when `!sign`, with each negation pushed to the constraints: not `t >= 0` is
/// `-t - 1 >= 0`, and not `t == 0` is `t >= 1 || -t >= 1`. The parts of each conjunction and
/// disjunction are sorted, so that the search through them, which takes the first that serves,
/// does not depend on the order they are written in.
fn nnf(f: &Formula, sign: bool) -> Formula {
    f.fold(
        sign,
        |g, s| s != matches!(g, Formula::Not(_)),
        |g, sign, mut parts| {
            let mut out = match (g, sign) {
                (Formula::Not(_), _) => parts.pop().expect("one part"),
                (Formula::And(_), true) | (Formula::Or(_), false) => Formula::and(parts),
                (Formula::And(_), false) | (Formula::Or(_), true) => Formula::or(parts),
                (Formula::Con(c), true) => Formula::Con(c.clone()),
                (Formula::Con(c), false) => {
                    let one = Lin::constant(1);
                    let neg = Formula::Con(Con::ge(&Lin::default(), &c.lin.plus(&one)));
                    if c.rel == Rel::Ge {
                        neg
                    } else {
                        Formula::or(vec![Formula::Con(Con::ge(&c.lin, &one)), neg])
                    }
                }
            };
            if let Formula::And(gs) | Formula::Or(gs) = &mut out {
                gs.sort();
            }
            out
        },
    )
}

/// The formula's base and disjunctions once no disjunct can be removed, or `None` when it has
/// no point. A disjunct is removed when its top-level constraints meet the base nowhere; a
/// disjunction left with one disjunct adds it to the base. Each round but the last removes a
/// disjunct, so there are at most as many rounds as disjuncts, each a test of every disjunct.
fn propagate(f: &Formula) -> Result<Option<Parts>, Refusal> {
    settle(Parts::of(nnf(f, true)))
}

/// [`propagate`] from parts.
fn settle(mut p: Parts) -> Result<Option<Parts>, Refusal> {
    // The base, with a bound written again (at each level of a nest, say) kept once
    // ([`Linked::meet`]), so that the groups a disjunct is tested with do not grow with the
    // depth.
    let mut base = Linked::reduced(std::mem::take(&mut p.cons));
    loop {
        // A point of the base serves only to keep, unasked, the disjuncts whose own constraints
        // hold at it, so none is built when no disjunction is left.
        let Some(model) = solve(&base.cons, !p.ors.is_empty())? else {
            return Ok(None);
        };
        if p.ors.is_empty() {
            p.cons = base.cons;
            return Ok(Some(p));
        }
        let mut changed = false;
        // The disjunctions to test, with those of a disjunct added to the base appended, so
        // that a chain of disjunctions each left with one disjunct is read in one round, not
        // one level of it per round; the disjunct's constraints join the base at once.
        let mut todo = std::mem::take(&mut p.ors);
        let mut next = 0;
        while next < todo.len() {
            let ds = std::mem::take(&mut todo[next]);
            next += 1;
            let n = ds.len();
            let mut live: Vec<Rc<Parts>> = ds
                .into_iter()
                .filter(|d| {
                    // The question below is of the disjunct's own constraints, so the point
                    // answers it when they hold there, whatever holds below them; reading
                    // only them keeps a nest from being read once for each level above it.
                    if d.cons.iter().all(|c| c.holds(&model)) {
                        return true;
                    }
                    let mut cs = base.around(&d.cons);
                    cs.extend(d.cons.iter());
                    !matches!(solve(&cs, false), Ok(None))
                })
                .collect();
            changed |= live.len() < n;
            match live.len() {
                0 => return Ok(None),
                1 => {
                    let d = live.pop().expect("one");
                    d.cons.iter().for_each(|c| {
                        base.meet(c.clone());
                    });
                    todo.extend(d.ors.iter().cloned());
                }
                _ => p.ors.push(live),
            }
        }
        if !changed {
            p.cons = base.cons;
            return Ok(Some(p));
        }
    }
}

/// Whether a conjunction of constraints holds somewhere, and, when `want`, where; without
/// `want` a point is answered by an empty model, and none is built.
fn solve<C: std::borrow::Borrow<Con>>(cons: &[C], want: bool) -> Result<Option<Model>, Refusal> {
    let cons: Vec<&Con> = cons.iter().map(|c| c.borrow()).collect();
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let (atoms, keys) = canonical(atoms, &cons);
    let index: BTreeMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    // Sorted, so that neither the order of the constraints nor the names of the variables
    // decide the order of the work, except among variables that refinement cannot tell apart.
    let mut sorted: Vec<(u64, &Con)> = cons.iter().map(|c| (row_key(c, &keys), *c)).collect();
    sorted.sort();
    // Each equality `x - y == d` ties `x` to `y`: every row is written over one variable of
    // each tied class, the others being offsets from it, so no row is rewritten for them.
    let mut ties = Ties::new(atoms.len());
    for (_, c) in &sorted {
        if c.rel != Rel::Eq || c.lin.terms.len() != 2 {
            continue;
        }
        let mut terms = c.lin.terms.iter();
        let (x, a) = terms.next().expect("two terms");
        let (y, b) = terms.next().expect("two terms");
        if !a.is_unit() || *b != -a {
            continue;
        }
        // `a·x - a·y + k == 0`, so `x - y == -k·a`.
        if !ties.equate(index[x], index[y], -&(&c.lin.constant * a)) {
            return Ok(None);
        }
    }
    let mut base: Vec<(Row, Rel)> = Vec::with_capacity(sorted.len());
    for (_, c) in sorted {
        let mut sum: BTreeMap<usize, Int> = BTreeMap::new();
        let mut k = c.lin.constant.clone();
        for (a, coef) in &c.lin.terms {
            let (r, d) = ties.root(index[a]);
            k = &k + &(coef * &d);
            let at = sum.entry(r).or_insert(Int::ZERO);
            *at = &*at + coef;
        }
        let a = sum.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        base.push((Row { a, k }, c.rel));
    }
    let Some(vals) = quotient(atoms.len(), base, want)? else {
        return Ok(None);
    };
    if !want {
        return Ok(Some(Model::new()));
    }
    let mut model: Model = atoms.iter().cloned().zip(vals).collect();
    for (i, a) in atoms.iter().enumerate() {
        let (r, d) = ties.root(i);
        if r != i {
            let v = &model[&atoms[r]] + &d;
            model.insert(a.clone(), v);
        }
    }
    Ok(Some(model))
}

/// Variables whose columns are multiples of one column, merged into one variable: the
/// greatest common divisor of their multiples, and for each, by place, the Bézout factors
/// `(j, s, t)` of the step that took it in, `s` on the divisor before and `t` on its own
/// multiple.
struct Merged {
    gcd: Int,
    links: Vec<(usize, Int, Int)>,
}

/// `(g, s, t)` with `g` the greatest common divisor of `a` and `b` and `s·a + t·b == g`, for
/// `a` not below zero, by the extended Euclidean algorithm.
fn bezout(a: &Int, b: &Int) -> (Int, Int, Int) {
    let (mut r, mut next) = (a.clone(), b.abs());
    let (mut s, mut ns) = (Int::ONE, Int::ZERO);
    let (mut t, mut nt) = (Int::ZERO, Int::ONE);
    while !next.is_zero() {
        let q = r.div_floor(&next);
        let rem = &r - &(&q * &next);
        r = std::mem::replace(&mut next, rem);
        let ns2 = &s - &(&q * &ns);
        s = std::mem::replace(&mut ns, ns2);
        let nt2 = &t - &(&q * &nt);
        t = std::mem::replace(&mut nt, nt2);
    }
    if b.is_negative() {
        t = -&t;
    }
    (r, s, t)
}

/// [`parts`] on `base` with the variables whose columns are multiples of one primitive column
/// merged. Where `x[j]` and `x[l]` enter every row as `c·p` and `d·p`, the rows see only
/// `c·x[j] + d·x[l]`, whose values over the integers are the multiples of `gcd(c, d)`; so
/// one variable `y` with column `gcd(c, d)·p` has a point exactly when they have one, and a
/// point of `y` lifts by the Bézout factors `s·c + t·d == gcd(c, d)` to `x[j] = s·y`,
/// `x[l] = t·y`. The substitution is unimodular on each group, so no integer point is lost or
/// added. A primitive column has coprime entries and its first entry above zero; columns are
/// grouped by sorting them, O(T log T) comparisons for T terms, and the factors grow by
/// O(log² C) bits for coefficients of C. With no two columns grouped, `base` goes on as it is.
fn quotient(vars: usize, base: Vec<(Row, Rel)>, want: bool) -> Result<Option<Vec<Int>>, Refusal> {
    // Each column, as its signed content and its primitive part, by row.
    let mut cols: Vec<Vec<(usize, &Int)>> = vec![Vec::new(); vars];
    for (i, (r, _)) in base.iter().enumerate() {
        for (j, c) in r.a.iter() {
            cols[*j].push((i, c));
        }
    }
    let split: Vec<Option<(Int, Vec<Term>)>> = cols
        .iter()
        .map(|col| {
            let &(_, first) = col.first()?;
            let g = col.iter().fold(Int::ZERO, |g, (_, c)| g.gcd(c));
            let prim = col
                .iter()
                .map(|(i, c)| {
                    let q = c.div_floor(&g);
                    (*i, if first.is_negative() { -&q } else { q })
                })
                .collect();
            Some((if first.is_negative() { -&g } else { g }, prim))
        })
        .collect();
    drop(cols);
    // The groups in the order of their first variable, each with that variable.
    let mut group: BTreeMap<&[Term], usize> = BTreeMap::new();
    let mut groups: Vec<(usize, Merged)> = Vec::new();
    for (j, (content, prim)) in split
        .iter()
        .enumerate()
        .filter_map(|(j, s)| Some((j, s.as_ref()?)))
    {
        let id = *group.entry(prim).or_insert_with(|| {
            groups.push((
                j,
                Merged {
                    gcd: Int::ZERO,
                    links: Vec::new(),
                },
            ));
            groups.len() - 1
        });
        let m = &mut groups[id].1;
        let (g, s, t) = bezout(&m.gcd, content);
        m.gcd = g;
        m.links.push((j, s, t));
    }
    if groups.iter().all(|(_, m)| m.links.len() == 1) {
        return parts(vars, base, want);
    }
    let mut rows: Vec<Vec<Term>> = vec![Vec::new(); base.len()];
    for (id, (first, m)) in groups.iter().enumerate() {
        let (_, prim) = split[*first].as_ref().expect("a group's first column");
        for (i, p) in prim {
            rows[*i].push((id, p * &m.gcd));
        }
    }
    let reduced = base
        .into_iter()
        .zip(rows)
        .map(|((r, rel), a)| {
            (
                Row {
                    a: a.into(),
                    k: r.k,
                },
                rel,
            )
        })
        .collect();
    let Some(y) = parts(groups.len(), reduced, want)? else {
        return Ok(None);
    };
    if !want {
        return Ok(Some(Vec::new()));
    }
    let mut x = vec![Int::ZERO; vars];
    for ((_, m), value) in groups.iter().zip(y) {
        let mut carry = value;
        for (j, s, t) in m.links.iter().rev() {
            x[*j] = t * &carry;
            carry = s * &carry;
        }
    }
    Ok(Some(x))
}

/// A part of a system: its variables, and its rows.
type Part = (Vec<usize>, Vec<(Row, Rel)>);

/// [`search`] on each part of `base` that shares no variable with the others: the rows hold
/// at a point exactly when each part's rows do at its own variables. So the answer is empty
/// when one part is empty, whatever the others give; otherwise the least of the parts'
/// refusals; otherwise the parts' points together, a variable in no row taking 0. A part of
/// two variables is decided exactly, however many such parts there are.
fn parts(vars: usize, base: Vec<(Row, Rel)>, want: bool) -> Result<Option<Vec<Int>>, Refusal> {
    // The parts, by union-find over the variables each row mentions.
    let mut parent: Vec<usize> = (0..vars).collect();
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    for (r, _) in &base {
        if let Some(&(first, _)) = r.a.first() {
            let a = find(&mut parent, first);
            for &(j, _) in &r.a[1..] {
                let b = find(&mut parent, j);
                parent[b] = a;
            }
        }
    }
    // Each part's rows, in the order of `base`, and its variables renumbered from 0 in
    // increasing order; the parts in the order of their least variable.
    let mut of_root: BTreeMap<usize, Part> = BTreeMap::new();
    for v in 0..vars {
        let root = find(&mut parent, v);
        of_root.entry(root).or_default().0.push(v);
    }
    for (r, rel) in base {
        let Some(&(first, _)) = r.a.first() else {
            // A row with no variable holds or fails alone.
            let holds = match rel {
                Rel::Ge => !r.k.is_negative(),
                Rel::Eq => r.k.is_zero(),
            };
            if !holds {
                return Ok(None);
            }
            continue;
        };
        let root = find(&mut parent, first);
        of_root
            .get_mut(&root)
            .expect("a part per root")
            .1
            .push((r, rel));
    }
    let mut vals = vec![Int::ZERO; vars];
    let mut refused: Option<Refusal> = None;
    let mut points = Vec::new();
    for (vs, rows) in of_root.into_values() {
        if rows.is_empty() {
            continue;
        }
        let local: BTreeMap<usize, usize> = vs.iter().enumerate().map(|(i, &v)| (v, i)).collect();
        let rows: Vec<(Row, Rel)> = rows
            .into_iter()
            .map(|(r, rel)| {
                // The renumbering keeps the order, so the row stays sorted.
                let a = r.a.iter().map(|(j, c)| (local[j], c.clone())).collect();
                (Row { a, k: r.k }, rel)
            })
            .collect();
        match search(vs.len(), &rows, want) {
            Ok(None) => return Ok(None),
            Ok(Some(p)) => points.push((vs, p)),
            Err(r) => refused = Some(refused.map_or(r, |q| q.min(r))),
        }
    }
    if let Some(r) = refused {
        return Err(r);
    }
    for (vs, p) in points {
        for (v, x) in vs.into_iter().zip(p) {
            vals[v] = x;
        }
    }
    Ok(Some(vals))
}

/// The Omega test on `base` over `vars` variables, with the splinters of its dark
/// eliminations: by Pugh's lemma [Omega, sec. 2.3] the problem has an integer point exactly
/// when its dark shadow has one or one of the splinters of a dark elimination has one. The
/// splinters are searched only when the dark shadows have no point, each once, without
/// splinters of their own. Pugh's lemma holds for either side of an elimination (for the
/// upper bounds, it is the lemma for `-x`), so the splinters taken are those of the side with
/// fewer bounds. They are tried in the order of the steps and of the rows, which is fixed by
/// the problem: the first point is the answer, and so is the first refusal, since a splinter
/// that is refused leaves the answer refused unless a later one has a point, and searching on
/// for that point would run the test again for every bound when none has one. A refused dark
/// shadow is the answer likewise: the splinters hold only the points it misses, so they could
/// turn the refusal into a point but never into an empty answer.
fn search(vars: usize, base: &[(Row, Rel)], want: bool) -> Result<Option<Vec<Int>>, Refusal> {
    let mut top = Omega::new(vars, base, want, true);
    match top.run() {
        Leaf::Point(v) => return Ok(Some(v)),
        Leaf::Empty => {}
        Leaf::Refused(r) => return Err(r),
    }
    for &(at, n) in &top.gray {
        let Step::Chosen(j, rows) = &top.steps[at] else {
            unreachable!("a dark elimination is a chosen step")
        };
        let (lowers, uppers): (Vec<&Row>, Vec<&Row>) =
            rows.iter().partition(|r| r.at(*j).is_positive());
        // The splinters of the side with fewer rows, each bound measured against the largest
        // coefficient of the other side; the lower side on a tie.
        let (side, other) = if uppers.len() < lowers.len() {
            (uppers, lowers)
        } else {
            (lowers, uppers)
        };
        let m = other
            .iter()
            .map(|r| r.at(*j).abs())
            .max()
            .expect("an inexact elimination has both bounds");
        for bound in side {
            let Some(mut child) = top.splinter(base, at, n, bound, *j, &m) else {
                continue;
            };
            match child.run() {
                Leaf::Point(v) => return Ok(Some(v)),
                Leaf::Empty if !child.gap => {}
                // Complexity tradeoff: a splinter whose own elimination leaves a gray shadow
                // (a splinter of a splinter) is not searched; the question gets
                // `Refusal::Shadows` ("not decided") even when a point lies there. Why: each
                // level of splinters multiplies the searches by the bounds of one side and
                // their coefficients, so nested splinters cost time exponential in the
                // variables. Trigger: an inexact elimination inside a splinter, which needs
                // coefficients other than ±1 on both sides of a variable at two levels.
                // Tests: `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`,
                // `l01_38_presburger::checker::a_question_whose_point_lies_past_one_splinter_is_rejected`,
                // `l01_38_presburger::scaling::pughs_example_in_a_chain_scales`. COMPLEXITY.md
                // row S18. A complete solution would recurse into nested splinters as Pugh's
                // Omega test does, at a cost exponential in the depth of the nesting.
                Leaf::Empty => return Err(Refusal::Shadows),
                Leaf::Refused(r) => return Err(r),
            }
        }
    }
    Ok(None)
}

/// The equalities `x - y == d` as a forest with union by rank, so that each root is found in
/// a number of steps logarithmic in the variables: each variable is its parent plus its offset.
struct Ties {
    parent: Vec<usize>,
    rank: Vec<usize>,
    offset: Vec<Int>,
}

impl Ties {
    fn new(n: usize) -> Ties {
        Ties {
            parent: (0..n).collect(),
            rank: vec![0; n],
            offset: vec![Int::ZERO; n],
        }
    }

    /// The root of `x[i]` and `d` with `x[i] == root + d`.
    fn root(&self, mut i: usize) -> (usize, Int) {
        let mut d = Int::ZERO;
        while self.parent[i] != i {
            d = &d + &self.offset[i];
            i = self.parent[i];
        }
        (i, d)
    }

    /// Adds `x[x] - x[y] == d`; false when the ties already make it something else.
    fn equate(&mut self, x: usize, y: usize, d: Int) -> bool {
        let (x, dx) = self.root(x);
        let (y, dy) = self.root(y);
        // `x - y == d - dx + dy` between the roots.
        let delta = &(&d - &dx) + &dy;
        if x == y {
            return delta.is_zero();
        }
        if self.rank[x] < self.rank[y] {
            self.parent[x] = y;
            self.offset[x] = delta;
        } else {
            self.parent[y] = x;
            self.offset[y] = -&delta;
            if self.rank[x] == self.rank[y] {
                self.rank[x] += 1;
            }
        }
        true
    }
}

fn xv_mix(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

/// A key of an integer of any size, the same for equal integers.
fn int_key(k: &Int) -> u64 {
    match k.to_i128() {
        Some(v) => (v as u64) ^ ((v >> 64) as u64),
        None => {
            let mut h = std::hash::DefaultHasher::new();
            std::hash::Hash::hash(k, &mut h);
            std::hash::Hasher::finish(&h)
        }
    }
}

fn row_key(c: &Con, keys: &BTreeMap<Atom, u64>) -> u64 {
    let mut t: Vec<(u64, u64)> = c
        .lin
        .terms
        .iter()
        .map(|(a, k)| (int_key(k), keys[a]))
        .collect();
    t.sort();
    let mut h = xv_mix(int_key(&c.lin.constant) ^ (c.rel == Rel::Eq) as u64);
    for (k, v) in t {
        h = xv_mix(h ^ k).wrapping_add(v);
    }
    h
}
/// `atoms`, in name order, sorted by their colors in the coarsest stable coloring of the
/// system ([`stable_colors`]), names breaking ties between equal colors; with the colors.
fn canonical(atoms: Vec<Atom>, cons: &[&Con]) -> (Vec<Atom>, BTreeMap<Atom, u64>) {
    let colors = stable_colors(&atoms, cons);
    let mut order: Vec<(u64, Atom)> = colors.into_iter().zip(atoms).collect();
    order.sort();
    let keys = order.iter().map(|(k, a)| (a.clone(), *k)).collect();
    (order.into_iter().map(|(_, a)| a).collect(), keys)
}

/// The colors of the variables of the conjunction `cons`, by which the solver orders them:
/// two variables have one color exactly when the structure of the rows does not tell them
/// apart, and the numbers depend on that structure only, not on the names.
pub fn colors(cons: &[Con]) -> BTreeMap<Atom, u64> {
    let cons: Vec<&Con> = cons.iter().collect();
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    canonical(atoms, &cons).1
}

/// The color of each of `atoms` (sorted, each in some row of `cons`) in the coarsest stable
/// coloring of the system's graph. The graph has a vertex for each variable, each row and each
/// term of a row, a term joined to its row and to its variable. A row starts colored by its
/// relation and constant, a term by its coefficient, and every variable alike. A coloring is
/// stable when any two vertices of one color have, for every color, as many neighbors of that
/// color. So two variables keep one color exactly when no number of rounds of comparing the
/// multisets of (row color, coefficient) of their rows tells them apart: refinement runs until
/// the partition is stable, with no count of rounds.
///
/// The method is the canonical color refinement of Berkholz, Bonsma and Grohe, "Tight lower and
/// upper bounds for the complexity of canonical colour refinement" (Theory Comput. Syst. 60,
/// 2017; arXiv:1509.08251), section 3, with edge colors by the subdivision of their
/// edge-colored theorem, which is the term vertex here. A popped color class R refines every
/// class by the number of neighbors in R each of its vertices has. After a split, the largest
/// new class is not pushed unless the old one was waiting (Hopcroft's rule), so a vertex is in
/// O(log N) refining classes in all. New colors are numbered in the increasing order of
/// (old color, number of neighbors), never by a hash, so equal colors mean equal structure and
/// the numbers depend on the structure alone, not on the names or the order of the rows.
/// O((n + m + t) log(n + m + t)) for n variables, m rows and t terms, with the sorts of the
/// starting colors.
fn stable_colors(atoms: &[Atom], cons: &[&Con]) -> Vec<u64> {
    let (n, m) = (atoms.len(), cons.len());
    let mut terms: Vec<(usize, usize, &Int)> = Vec::new();
    for (r, c) in cons.iter().enumerate() {
        for (a, k) in &c.lin.terms {
            let x = atoms.binary_search(a).expect("an atom of the system");
            terms.push((r, x, k));
        }
    }
    let size = n + m + terms.len();
    // Vertices: the variables, then the rows, then the terms.
    let mut color = vec![0; size];
    let mut next = usize::from(n > 0);
    let mut rows: Vec<usize> = (0..m).collect();
    let row = |r: usize| (cons[r].rel, &cons[r].lin.constant);
    rows.sort_by(|&p, &q| row(p).cmp(&row(q)));
    for (i, &r) in rows.iter().enumerate() {
        if i > 0 && row(rows[i - 1]) != row(r) {
            next += 1;
        }
        color[n + r] = next;
    }
    next += usize::from(m > 0);
    let mut by_coef: Vec<usize> = (0..terms.len()).collect();
    by_coef.sort_by(|&p, &q| terms[p].2.cmp(terms[q].2));
    for (i, &e) in by_coef.iter().enumerate() {
        if i > 0 && terms[by_coef[i - 1]].2 != terms[e].2 {
            next += 1;
        }
        color[n + m + e] = next;
    }
    next += usize::from(!terms.is_empty());
    // The neighbors of vertex v are `adj[start[v]..start[v + 1]]`.
    let mut start = vec![0; size + 1];
    for (e, &(r, x, _)) in terms.iter().enumerate() {
        start[x + 1] += 1;
        start[n + r + 1] += 1;
        start[n + m + e + 1] = 2;
    }
    for v in 0..size {
        start[v + 1] += start[v];
    }
    let mut adj = vec![0; start[size]];
    let mut cursor = start[..size].to_vec();
    let mut link = |a: usize, b: usize| {
        adj[cursor[a]] = b;
        cursor[a] += 1;
    };
    for (e, &(r, x, _)) in terms.iter().enumerate() {
        let e = n + m + e;
        link(x, e);
        link(e, x);
        link(n + r, e);
        link(e, n + r);
    }
    let degree = (0..size)
        .map(|v| start[v + 1] - start[v])
        .max()
        .unwrap_or(0);
    let mut refine = Refine::new(color, next, degree);
    refine.run(&start, &adj);
    refine.color[..n].iter().map(|&c| c as u64).collect()
}

/// The state of [`stable_colors`]' refinement, after Berkholz, Bonsma and Grohe's
/// Algorithms 2 and 3. Arrays by color have one entry for each vertex, the most colors there
/// can be.
struct Refine {
    /// The color of each vertex.
    color: Vec<usize>,
    /// The vertices of each color, in no particular order.
    members: Vec<Vec<usize>>,
    /// The place of each vertex in its color's `members`.
    at: Vec<usize>,
    /// How many colors there are.
    colors: usize,
    /// The colors waiting to refine the others, and whether each is waiting.
    stack: Vec<usize>,
    queued: Vec<bool>,
    /// For the class being refined by: each vertex's number of neighbors in it.
    count: Vec<usize>,
    /// For each color, its vertices with a neighbor in the class, the most and least of their
    /// numbers, and whether it is in `adjacent`.
    hit: Vec<Vec<usize>>,
    most: Vec<usize>,
    least: Vec<usize>,
    seen: Vec<bool>,
    /// The colors with a vertex next to the class, and those of them that split.
    adjacent: Vec<usize>,
    splits: Vec<usize>,
    /// By number of neighbors, for one split: how many vertices have it, and their new color.
    tally: Vec<usize>,
    new: Vec<usize>,
}

impl Refine {
    /// The refinement of the coloring `color`, with colors `0..colors`, of a graph whose
    /// vertices have at most `degree` neighbors.
    fn new(color: Vec<usize>, colors: usize, degree: usize) -> Refine {
        let size = color.len();
        let mut members = vec![Vec::new(); size];
        let mut at = vec![0; size];
        for (v, &c) in color.iter().enumerate() {
            at[v] = members[c].len();
            members[c].push(v);
        }
        let mut queued = vec![false; size];
        queued[..colors].fill(true);
        Refine {
            color,
            members,
            at,
            colors,
            stack: (0..colors).collect(),
            queued,
            count: vec![0; size],
            hit: vec![Vec::new(); size],
            most: vec![0; size],
            least: vec![0; size],
            seen: vec![false; size],
            adjacent: Vec::new(),
            splits: Vec::new(),
            tally: vec![0; degree + 1],
            new: vec![0; degree + 1],
        }
    }

    /// Refines until no waiting color splits another: the coloring is then stable.
    fn run(&mut self, start: &[usize], adj: &[usize]) {
        while let Some(r) = self.stack.pop() {
            self.queued[r] = false;
            let Refine {
                color,
                members,
                count,
                hit,
                most,
                least,
                seen,
                adjacent,
                splits,
                ..
            } = self;
            for &v in &members[r] {
                for &w in &adj[start[v]..start[v + 1]] {
                    let c = color[w];
                    count[w] += 1;
                    if count[w] == 1 {
                        hit[c].push(w);
                    }
                    if !seen[c] {
                        seen[c] = true;
                        adjacent.push(c);
                    }
                    most[c] = most[c].max(count[w]);
                }
            }
            for &c in adjacent.iter() {
                least[c] = if hit[c].len() < members[c].len() {
                    0
                } else {
                    hit[c]
                        .iter()
                        .map(|&v| count[v])
                        .min()
                        .expect("a vertex hit")
                };
                if least[c] < most[c] {
                    splits.push(c);
                }
            }
            splits.sort_unstable();
            let mut splits = mem::take(&mut self.splits);
            for &c in &splits {
                self.split(c);
            }
            splits.clear();
            self.splits = splits;
            for &c in &self.adjacent {
                for &v in &self.hit[c] {
                    self.count[v] = 0;
                }
                self.hit[c].clear();
                self.most[c] = 0;
                self.seen[c] = false;
            }
            self.adjacent.clear();
        }
    }

    /// Splits color `c` by the numbers of neighbors its vertices have in the refining class.
    /// The vertices with the least number keep `c`; the others take new colors in increasing
    /// order of their number. Every new class waits to refine except the largest, unless `c`
    /// was waiting already, and then all do.
    fn split(&mut self, c: usize) {
        let top = self.most[c];
        let hit = mem::take(&mut self.hit[c]);
        self.tally[..=top].fill(0);
        self.tally[0] = self.members[c].len() - hit.len();
        for &v in &hit {
            self.tally[self.count[v]] += 1;
        }
        let mut big = 0;
        for i in 1..=top {
            if self.tally[i] > self.tally[big] {
                big = i;
            }
        }
        let waiting = self.queued[c];
        for i in 0..=top {
            if self.tally[i] == 0 {
                continue;
            }
            let k = if i == self.least[c] {
                c
            } else {
                self.colors += 1;
                self.colors - 1
            };
            self.new[i] = k;
            if (waiting && k != c) || (!waiting && i != big) {
                self.queued[k] = true;
                self.stack.push(k);
            }
        }
        for &v in &hit {
            let k = self.new[self.count[v]];
            if k != c {
                let place = self.at[v];
                self.members[c].swap_remove(place);
                if let Some(&u) = self.members[c].get(place) {
                    self.at[u] = place;
                }
                self.at[v] = self.members[k].len();
                self.members[k].push(v);
                self.color[v] = k;
            }
        }
        self.hit[c] = hit;
    }
}

/// The coefficients of a row, nonzero, in variable order. Rows are shared, not copied, among
/// the system, its index and the steps.
type Coefs = Rc<[Term]>;

/// `Σ a[i]·x[i] + k`, compared with zero by `>=`, or by `==` among the equalities.
#[derive(Clone)]
struct Row {
    a: Coefs,
    k: Int,
}

/// What normalizing a row gives.
enum Norm {
    True,
    False,
    Row(Row),
}

/// `f·x + g·y`, without the variable `skip`.
fn merge(x: &[Term], f: &Int, y: &[Term], g: &Int, skip: usize) -> Coefs {
    let mut out = Vec::with_capacity(x.len() + y.len());
    let (mut xs, mut ys) = (x.iter().peekable(), y.iter().peekable());
    loop {
        let order = match (xs.peek(), ys.peek()) {
            (Some(p), Some(q)) => p.0.cmp(&q.0),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => break,
        };
        let (v, c) = match order {
            Ordering::Less => {
                let (v, c) = xs.next().expect("peeked");
                (*v, c * f)
            }
            Ordering::Greater => {
                let (v, d) = ys.next().expect("peeked");
                (*v, d * g)
            }
            Ordering::Equal => {
                let (v, c) = xs.next().expect("peeked");
                let (_, d) = ys.next().expect("peeked");
                (*v, &(c * f) + &(d * g))
            }
        };
        if v != skip && !c.is_zero() {
            out.push((v, c));
        }
    }
    out.into()
}

/// The coefficients of the opposite row.
fn opposite(a: &[Term]) -> Vec<Term> {
    a.iter().map(|(i, c)| (*i, -c)).collect()
}

impl Row {
    /// The coefficient at `x[j]`, which the row holds.
    fn at(&self, j: usize) -> &Int {
        let i = self.a.binary_search_by_key(&j, |t| t.0);
        &self.a[i.expect("the row holds the variable")].1
    }

    fn eval(&self, m: &[Int]) -> Int {
        self.a
            .iter()
            .fold(self.k.clone(), |v, (i, c)| &v + &(c * &m[*i]))
    }

    /// The row divided by the gcd of its coefficients, an inequality's constant rounded down.
    fn normal(self, eq: bool) -> Norm {
        let mut g = Int::ZERO;
        for (_, c) in self.a.iter() {
            g = g.gcd(c);
            if g.is_unit() {
                return Norm::Row(self);
            }
        }
        if g.is_zero() {
            let holds = if eq {
                self.k.is_zero()
            } else {
                !self.k.is_negative()
            };
            return if holds { Norm::True } else { Norm::False };
        }
        if eq && !self.k.mod_floor(&g).is_zero() {
            return Norm::False;
        }
        Norm::Row(Row {
            a: self.a.iter().map(|(i, c)| (*i, c.div_floor(&g))).collect(),
            k: self.k.div_floor(&g),
        })
    }

    /// The row, which holds `x[j]`, with `x[j]` replaced by `def`.
    fn subst(&self, j: usize, def: &Row) -> Row {
        let c = self.at(j);
        Row {
            a: merge(&self.a, &Int::ONE, &def.a, c, j),
            k: &self.k + &(c * &def.k),
        }
    }
}

/// The symmetric remainder of `a` by `m`, of either sign.
fn mod_hat(a: &Int, m: &Int) -> Int {
    let m = m.abs();
    let r = a.mod_floor(&m);
    if (&r + &r) >= m { &r - &m } else { r }
}

/// How a variable occurs in the inequalities: as a lower or an upper bound, and how often with
/// a coefficient that is not a unit.
#[derive(Default)]
struct Sides {
    lo: usize,
    hi: usize,
    lo_wide: usize,
    hi_wide: usize,
    /// The terms of its rows on each side.
    lo_terms: usize,
    hi_terms: usize,
    /// Its rows of one term, at most one on each side: a row of one term is normalized to a
    /// unit coefficient, and two with the same coefficient are held as one.
    lo_unary: usize,
    hi_unary: usize,
}

impl Sides {
    /// Whether no elimination of the variable is exact.
    fn inexact(&self) -> bool {
        self.lo_wide > 0 && self.hi_wide > 0
    }

    /// The terms its elimination writes less the terms it removes, the variable's own terms
    /// in the new rows not counted.
    fn fill(&self) -> isize {
        let written = self.lo * self.hi_terms + self.hi * self.lo_terms;
        written as isize
            - 2 * (self.lo * self.hi) as isize
            - (self.lo_terms + self.hi_terms) as isize
    }

    /// Whether every row but its bounds pulls the variable to one bound it has.
    fn fixable(&self) -> bool {
        self.lo > 0
            && self.hi > 0
            && ((self.lo == self.lo_unary && self.lo_unary > 0)
                || (self.hi == self.hi_unary && self.hi_unary > 0))
    }

    /// Where the variable stands among those to eliminate.
    fn rank(&self, j: usize) -> Rank {
        (self.fill(), j)
    }
}

/// The fill of a variable's elimination, and the variable.
type Rank = (isize, usize);

/// A row of a [`System`]: its constant, and its place in the system's list.
struct Held {
    k: Int,
    id: usize,
}

/// A variable of a [`System`]: its rows, by place, and how it occurs in them.
#[derive(Default)]
struct Var {
    rows: BTreeSet<usize>,
    sides: Sides,
}

/// A system of inequalities, kept normalized as rows are added and removed: each set of
/// coefficients is held once, with its least constant, and each variable knows its rows and
/// how it occurs in them, so that a step touches only the rows of the variable it eliminates.
struct System {
    rows: BTreeMap<Coefs, Held>,
    /// The coefficients of each row ever added, by place, while it is held.
    ids: Vec<Option<Coefs>>,
    vars: Vec<Var>,
    /// The variables whose elimination is exact, by rank.
    exact: BTreeSet<Rank>,
    /// The variables whose elimination is inexact, likewise.
    inexact: BTreeSet<Rank>,
    /// The variables bounded on one side only.
    one_sided: BTreeSet<usize>,
    /// The variables [`Sides::fixable`] holds of.
    fixable: BTreeSet<usize>,
    /// The lesser coefficients of two opposite rows whose constants sum to zero; a pair may
    /// since have changed, and is checked when taken.
    meets: BTreeSet<Coefs>,
    /// Whether a row is false, or two opposite rows meet nowhere.
    empty: bool,
    /// The variables some row holds.
    live: usize,
    /// The rows not of the form `±x ± y + k >= 0` or `±x + k >= 0`.
    wide_rows: usize,
}

impl System {
    fn new(vars: usize) -> System {
        System {
            rows: BTreeMap::new(),
            ids: Vec::new(),
            vars: std::iter::repeat_with(Var::default).take(vars).collect(),
            exact: BTreeSet::new(),
            inexact: BTreeSet::new(),
            one_sided: BTreeSet::new(),
            fixable: BTreeSet::new(),
            meets: BTreeSet::new(),
            empty: false,
            live: 0,
            wide_rows: 0,
        }
    }

    fn add(&mut self, r: Row) {
        let r = match r.normal(false) {
            Norm::False => {
                self.empty = true;
                return;
            }
            Norm::True => return,
            Norm::Row(r) => r,
        };
        if let Some(old) = self.rows.get_mut(&r.a) {
            if old.k <= r.k {
                return;
            }
            old.k = r.k.clone();
        } else {
            let id = self.ids.len();
            self.ids.push(Some(r.a.clone()));
            self.count(&r.a, id, true);
            let k = r.k.clone();
            self.rows.insert(r.a.clone(), Held { k, id });
        }
        let opp = opposite(&r.a);
        if let Some((key, o)) = self.rows.get_key_value(opp.as_slice()) {
            let s = &r.k + &o.k;
            if s.is_negative() {
                self.empty = true;
            } else if s.is_zero() {
                let lesser = if r.a < *key { r.a } else { key.clone() };
                self.meets.insert(lesser);
            }
        }
    }

    /// Counts the row `a` at place `id` in, or out when `!add`, at each of its variables.
    fn count(&mut self, a: &Coefs, id: usize, add: bool) {
        if a.len() > 2 || a.iter().any(|(_, c)| !c.is_unit()) {
            if add {
                self.wide_rows += 1;
            } else {
                self.wide_rows -= 1;
            }
        }
        for (i, c) in a.iter() {
            let v = &mut self.vars[*i];
            let set = if v.sides.inexact() {
                &mut self.inexact
            } else {
                &mut self.exact
            };
            set.remove(&v.sides.rank(*i));
            self.one_sided.remove(i);
            self.fixable.remove(i);
            let s = &mut v.sides;
            let was = s.lo + s.hi > 0;
            let (side, wide, terms, unary) = if c.is_positive() {
                (&mut s.lo, &mut s.lo_wide, &mut s.lo_terms, &mut s.lo_unary)
            } else {
                (&mut s.hi, &mut s.hi_wide, &mut s.hi_terms, &mut s.hi_unary)
            };
            if add {
                *side += 1;
                *wide += usize::from(!c.is_unit());
                *terms += a.len();
                *unary += usize::from(a.len() == 1);
                v.rows.insert(id);
            } else {
                *side -= 1;
                *wide -= usize::from(!c.is_unit());
                *terms -= a.len();
                *unary -= usize::from(a.len() == 1);
                v.rows.remove(&id);
            }
            match (was, s.lo + s.hi > 0) {
                (false, true) => self.live += 1,
                (true, false) => self.live -= 1,
                _ => {}
            }
            if s.lo + s.hi == 0 {
                continue;
            }
            let set = if s.inexact() {
                &mut self.inexact
            } else {
                &mut self.exact
            };
            set.insert(s.rank(*i));
            if s.lo == 0 || s.hi == 0 {
                self.one_sided.insert(*i);
            }
            if s.fixable() {
                self.fixable.insert(*i);
            }
        }
    }

    /// Removes the held row at place `id`, and returns it.
    fn remove(&mut self, id: usize) -> Row {
        let a = self.ids[id].take().expect("a row held");
        let k = self.rows.remove(&a).expect("a row held").k;
        self.count(&a, id, false);
        Row { a, k }
    }

    /// Removes the rows that hold `x[j]`, and returns them.
    fn take(&mut self, j: usize) -> Vec<Row> {
        let ids = std::mem::take(&mut self.vars[j].rows);
        ids.into_iter().map(|id| self.remove(id)).collect()
    }

    /// One of two opposite rows that meet in an equality, both removed.
    fn meeting(&mut self) -> Option<Row> {
        while let Some(a) = self.meets.pop_first() {
            let opp = opposite(&a);
            if let (Some(r), Some(o)) = (self.rows.get(&a), self.rows.get(opp.as_slice()))
                && (&r.k + &o.k).is_zero()
            {
                let (r, o) = (r.id, o.id);
                self.remove(o);
                return Some(self.remove(r));
            }
        }
        None
    }

    /// The variable of least fill among the exact eliminations, the first on a tie, whose
    /// elimination adds no terms unless `fill_ok`. So the terms of the system never rise,
    /// whatever its size, until a point is known to exist.
    fn exact_step(&self, fill_ok: bool) -> Option<usize> {
        self.exact
            .first()
            .filter(|r| fill_ok || r.0 <= 0)
            .map(|r| r.1)
    }

    /// The variable of least fill among the inexact eliminations whose elimination adds no
    /// terms, the first on a tie.
    fn inexact_step(&self) -> Option<usize> {
        self.inexact.first().filter(|r| r.0 <= 0).map(|r| r.1)
    }

    /// The value of the bound row of `x[j]` on the side `upper`, if it has one.
    fn bound(&self, j: usize, upper: bool) -> Option<Int> {
        let c = if upper { -&Int::ONE } else { Int::ONE };
        let held = self.rows.get([(j, c)].as_slice())?;
        Some(if upper { held.k.clone() } else { -&held.k })
    }

    /// Eliminates `x[j]` by its real shadow, or its dark one when `dark`; returns its rows.
    fn eliminate(&mut self, j: usize, dark: bool) -> Vec<Row> {
        let with = self.take(j);
        let (lowers, uppers): (Vec<&Row>, Vec<&Row>) =
            with.iter().partition(|r| r.at(j).is_positive());
        for lo in &lowers {
            for hi in &uppers {
                self.add(combine(lo, hi, j, dark));
            }
        }
        with
    }
}

/// Whether the inequalities have no rational point once each row is normalized, which keeps
/// every integer point: real shadows while an elimination adds no terms, and the box test of
/// [`box_empty`] on what is left.
fn relaxed_empty(gs: &System) -> bool {
    let mut sys = System::new(gs.vars.len());
    for (a, r) in &gs.rows {
        sys.add(Row {
            a: a.clone(),
            k: r.k.clone(),
        });
    }
    while !sys.empty {
        let least = sys.exact.first().into_iter().chain(sys.inexact.first());
        let Some(&(fill, j)) = least.min() else {
            return false;
        };
        if fill > 0 {
            return box_empty(&sys);
        }
        sys.eliminate(j, false);
    }
    true
}

/// The lower and the upper bound of each variable, where it has one.
type Bounds = (Vec<Option<Int>>, Vec<Option<Int>>);

/// The bounds of each variable: those of its bound rows, each then tightened once by every
/// wide row `Σ a[i]·x[i] + k >= 0` from those bounds, all rows at the same time, so the
/// result does not depend on the order of the rows. With each other term at its largest value
/// in the box, the row leaves `a[i]·x[i] >= -rest`, a bound every integer point keeps; `rest`
/// is known when at most `x[i]` itself lacks the bound the row needs. `None` when some
/// variable is left with no value, which shows the rows empty. One pass over the terms.
fn bounds(sys: &System) -> Option<Bounds> {
    let n = sys.vars.len();
    let lo: Vec<Option<Int>> = (0..n).map(|j| sys.bound(j, false)).collect();
    let hi: Vec<Option<Int>> = (0..n).map(|j| sys.bound(j, true)).collect();
    let (mut tlo, mut thi) = (lo.clone(), hi.clone());
    for (a, held) in sys.rows.iter().filter(|(a, _)| a.len() > 1) {
        // The largest value of `c·x[i]` in the box.
        let top = |i: usize, c: &Int| {
            if c.is_positive() { &hi[i] } else { &lo[i] }
                .as_ref()
                .map(|b| c * b)
        };
        let mut sum = held.k.clone();
        let mut open: Vec<usize> = Vec::new();
        for (i, c) in a.iter() {
            match top(*i, c) {
                Some(m) => sum = &sum + &m,
                None => open.push(*i),
            }
        }
        for (i, c) in a.iter() {
            let rest = match (open.as_slice(), top(*i, c)) {
                ([], Some(m)) => &sum - &m,
                ([o], None) if o == i => sum.clone(),
                _ => continue,
            };
            if c.is_positive() {
                let b = -&rest.div_floor(c);
                if tlo[*i].as_ref().is_none_or(|l| *l < b) {
                    tlo[*i] = Some(b);
                }
            } else {
                let b = rest.div_floor(&-c);
                if thi[*i].as_ref().is_none_or(|h| b < *h) {
                    thi[*i] = Some(b);
                }
            }
        }
    }
    let empty = (0..n).any(|j| matches!((&tlo[j], &thi[j]), (Some(l), Some(h)) if h < l));
    (!empty).then_some((tlo, thi))
}

/// Whether some wide row `Σ a[i]·x[i] + k >= 0` is below zero at every point of the box
/// `lo`, `hi`: its largest value there, `k` plus each `a[i]` times the upper bound of `x[i]`
/// when `a[i]` is above zero and the lower one when below, is negative. Every point of the
/// rows lies in the box, so such a row shows them empty.
fn box_empty_in(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> bool {
    sys.rows.iter().any(|(a, held)| {
        a.len() > 1
            && a.iter()
                .try_fold(held.k.clone(), |m, (i, c)| {
                    let b = if c.is_positive() { &hi[*i] } else { &lo[*i] }.as_ref()?;
                    Some(&m + &(c * b))
                })
                .is_some_and(|m| m.is_negative())
    })
}

/// Whether the rows are empty by [`bounds`] or by [`box_empty_in`] in the box it gives.
fn box_empty(sys: &System) -> bool {
    bounds(sys).is_none_or(|(lo, hi)| box_empty_in(sys, &lo, &hi))
}

/// The value of one variable in one candidate point of the box stage, from its two bounds, or
/// none where a bound it reads is missing.
type Coordinate = fn(&Option<Int>, &Option<Int>) -> Option<Int>;

/// The five candidate points of the box stage, one coordinate at a time: the value nearest
/// zero ([`nearest_zero`], which also stands in wherever a bound is missing), the lower bound,
/// the upper bound, and the midpoint of the bounds rounded down and rounded up.
const CANDIDATES: [Coordinate; 5] = [
    |_, _| None,
    |lo, _| lo.clone(),
    |_, hi| hi.clone(),
    |lo, hi| Some((lo.as_ref()? + hi.as_ref()?).div_floor(&Int::from(2))),
    |lo, hi| Some((&(lo.as_ref()? + hi.as_ref()?) + &Int::ONE).div_floor(&Int::from(2))),
];

/// The value nearest zero between the bounds `lo` and `hi`.
fn nearest_zero(lo: &Option<Int>, hi: &Option<Int>) -> Int {
    match (lo, hi) {
        (Some(l), _) if l.is_positive() => l.clone(),
        (_, Some(h)) if h.is_negative() => h.clone(),
        _ => Int::ZERO,
    }
}

/// The first of five points of the box `lo`, `hi` that holds every row: the point nearest
/// zero, the lower corner, the upper corner, and the two midpoints, rounded down and rounded
/// up ([`CANDIDATES`]), each taken variable by variable. Each costs one pass over the terms of
/// the rows. They depend on the rows and the box alone, not on the names of the variables or
/// the order of the rows.
fn box_point(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> Option<Vec<Int>> {
    CANDIDATES.iter().find_map(|at| {
        let v: Vec<Int> = lo
            .iter()
            .zip(hi)
            .map(|(l, h)| at(l, h).unwrap_or_else(|| nearest_zero(l, h)))
            .collect();
        let holds = sys.rows.iter().all(|(a, held)| {
            !a.iter()
                .fold(held.k.clone(), |s, (i, c)| &s + &(c * &v[*i]))
                .is_negative()
        });
        holds.then_some(v)
    })
}

/// The shadow row of the lower bound `a·x + l >= 0` and the upper bound `-b·x + u >= 0` on
/// `x = x[j]`: the real shadow `a·u + b·l >= 0`, or the dark one
/// `a·u + b·l >= (a - 1)(b - 1)` when `dark`.
fn combine(lo: &Row, hi: &Row, j: usize, dark: bool) -> Row {
    let (a, b) = (lo.at(j), &-hi.at(j));
    let k = &(&hi.k * a) + &(&lo.k * b);
    Row {
        a: merge(&hi.a, a, &lo.a, b, j),
        k: if dark {
            &k - &(&(a - &Int::ONE) * &(b - &Int::ONE))
        } else {
            k
        },
    }
}

/// The equalities as a stack, a slot emptied when its row holds everywhere, with the slots of
/// each variable.
struct Equalities {
    rows: Vec<Option<Row>>,
    of: Vec<BTreeSet<usize>>,
}

impl Equalities {
    fn new(vars: usize) -> Equalities {
        Equalities {
            rows: Vec::new(),
            of: vec![BTreeSet::new(); vars],
        }
    }

    /// The slot of the last equality, if any.
    fn last(&mut self) -> Option<usize> {
        while matches!(self.rows.last(), Some(None)) {
            self.rows.pop();
        }
        self.rows.len().checked_sub(1)
    }

    fn push(&mut self, r: Row, sys: &mut System) {
        self.rows.push(None);
        self.put(self.rows.len() - 1, r, sys);
    }

    fn put(&mut self, s: usize, r: Row, sys: &mut System) {
        match r.normal(true) {
            Norm::False => sys.empty = true,
            Norm::True => {}
            Norm::Row(r) => {
                for (i, _) in r.a.iter() {
                    self.of[*i].insert(s);
                }
                self.rows[s] = Some(r);
            }
        }
    }

    /// Empties the slot `s`, and returns its row.
    fn clear(&mut self, s: usize) -> Row {
        let r = self.rows[s].take().expect("a slot in use");
        for (i, _) in r.a.iter() {
            self.of[*i].remove(&s);
        }
        r
    }

    /// Replaces `x[j]` by `def` in each equality that holds it.
    fn subst(&mut self, j: usize, def: &Row, sys: &mut System) {
        for s in std::mem::take(&mut self.of[j]) {
            let r = self.clear(s);
            self.put(s, r.subst(j, def), sys);
        }
    }
}

/// A step the model is built back through, last step first.
enum Step {
    /// `x[j]` defined by an equality.
    Defined(usize, Row),
    /// `x[j]` chosen within the rows that held it.
    Chosen(usize, Vec<Row>),
}

/// What one run of the Omega test finds.
enum Leaf {
    /// A point, the values by variable; empty when no model was wanted.
    Point(Vec<Int>),
    /// No point; where a dark shadow was taken on the way, no point in the dark shadow.
    Empty,
    /// The system is outside the fragment decided.
    Refused(Refusal),
}

/// The Omega test. Each step solves an equality, turns two opposite rows that meet into one,
/// drops a variable bounded on one side only, fixes a variable at a bound, or eliminates a
/// variable, until no row is left; the model is then built back through the steps.
struct Omega {
    sys: System,
    es: Equalities,
    steps: Vec<Step>,
    /// The definitions not yet written into the inequalities: each inequality is rewritten once
    /// for all of them, however many of its variables they define.
    pending: Vec<(usize, Row)>,
    /// Whether a model is wanted.
    want: bool,
    /// Whether the real shadow was tested, at the first inexact elimination.
    tested: bool,
    /// Whether the dark eliminations are kept for the search of their splinters; false within a
    /// splinter.
    may_splinter: bool,
    /// The dark eliminations kept: the place of each one's step, and the number of variables
    /// then.
    gray: Vec<(usize, usize)>,
    /// Whether a dark shadow was taken whose splinters are not searched.
    gap: bool,
    /// Whether an exact elimination may add terms: set once a system of rows `±x ± y + k >= 0`
    /// is shown to have a point, since its eliminations are all exact and keep that form.
    fill_ok: bool,
}

impl Omega {
    /// The test on the rows `base`, each `>= 0` or `== 0`, over `vars` variables.
    fn new(vars: usize, base: &[(Row, Rel)], want: bool, may_splinter: bool) -> Omega {
        let mut sys = System::new(vars);
        let mut es = Equalities::new(vars);
        for (r, rel) in base {
            match rel {
                Rel::Eq => es.push(r.clone(), &mut sys),
                Rel::Ge => sys.add(r.clone()),
            }
        }
        Omega {
            sys,
            es,
            steps: Vec::new(),
            pending: Vec::new(),
            want,
            tested: false,
            may_splinter,
            gray: Vec::new(),
            gap: false,
            fill_ok: false,
        }
    }

    fn run(&mut self) -> Leaf {
        // The values of the variables left when the loop ends, zero where none is given.
        let mut start: Vec<Int> = Vec::new();
        loop {
            if self.sys.empty {
                return Leaf::Empty;
            }
            if let Some(s) = self.es.last() {
                self.equality(s);
                continue;
            }
            if !self.pending.is_empty() {
                self.flush();
                continue;
            }
            if let Some(r) = self.sys.meeting() {
                self.es.push(r, &mut self.sys);
                continue;
            }
            if self.sys.rows.is_empty() {
                break;
            }
            if let Some(&j) = self.sys.one_sided.first() {
                let rows = self.sys.take(j);
                self.steps.push(Step::Chosen(j, rows));
                continue;
            }
            if !self.sys.fixable.is_empty() {
                self.fix();
                continue;
            }
            if let Some(j) = self.sys.exact_step(self.fill_ok) {
                let rows = self.sys.eliminate(j, false);
                self.steps.push(Step::Chosen(j, rows));
                continue;
            }
            if self.sys.live <= 2 {
                let Some((x, v)) = self.pair() else {
                    return Leaf::Empty;
                };
                if !self.want {
                    return Leaf::Point(Vec::new());
                }
                for (j, v) in x.into_iter().zip(v) {
                    self.sys.take(j);
                    let a = Vec::new().into();
                    self.steps.push(Step::Defined(j, Row { a, k: v }));
                }
                continue;
            }
            if self.sys.wide_rows == 0 {
                // Every elimination is exact, and each adds terms.
                let rows: Vec<(&[Term], &Int)> =
                    self.sys.rows.iter().map(|(a, h)| (&**a, &h.k)).collect();
                if utvpi::integer_empty(self.sys.vars.len(), &rows) {
                    return Leaf::Empty;
                }
                if !self.want {
                    return Leaf::Point(Vec::new());
                }
                self.fill_ok = true;
                continue;
            }
            if let Some(j) = self.sys.inexact_step() {
                // An empty real shadow, which keeps every integer point, shows the problem empty; from here
                // on the dark shadow is solved, whose points are points of the problem, and
                // the splinters of each dark elimination hold the points it misses.
                if !self.tested {
                    self.tested = true;
                    if relaxed_empty(&self.sys) {
                        return Leaf::Empty;
                    }
                }
                if self.may_splinter {
                    self.gray.push((self.steps.len(), self.sys.vars.len()));
                } else {
                    self.gap = true;
                }
                let rows = self.sys.eliminate(j, true);
                self.steps.push(Step::Chosen(j, rows));
                continue;
            }
            // Every elimination left adds terms. With three variables, one of which has a
            // unit coefficient in every row on one side (an exact elimination), that
            // variable's rows are replaced by the pairs of a lower and an upper bound that
            // `hull3::shadow` chooses: the edges where the top of the polyhedron meets its
            // bottom, O(m) rows found in O(m log m), which cut out the same real shadow as all
            // m² pairs. With the unit side the integer shadow is the real one, so the rows of
            // two variables left are decided exactly by `pair`, and `choose` lifts the
            // variable back. The dispatch on three live variables is a structural class, like
            // the dispatch on two or fewer to `twovar`: it switches on a count of dimensions,
            // not on a size of the input, so it is no threshold.
            if self.sys.live == 3
                && let Some(&(_, z)) = self.sys.exact.first()
            {
                let rows = self.sys.take(z);
                let mut others: Vec<usize> = Vec::with_capacity(2);
                for (i, _) in rows.iter().flat_map(|r| r.a.iter()) {
                    if *i != z && !others.contains(i) {
                        others.push(*i);
                    }
                }
                let at = |r: &Row, v: Option<&usize>| {
                    v.and_then(|v| r.a.binary_search_by_key(v, |t| t.0).ok())
                        .map_or(Int::ZERO, |i| r.a[i].1.clone())
                };
                let planes: Vec<hull3::Plane> = rows
                    .iter()
                    .map(|r| hull3::Plane {
                        z: r.at(z).clone(),
                        x: at(r, others.first()),
                        y: at(r, others.get(1)),
                        k: r.k.clone(),
                    })
                    .collect();
                for (lo, hi) in hull3::shadow(&planes) {
                    self.sys.add(combine(&rows[lo], &rows[hi], z, false));
                }
                self.steps.push(Step::Chosen(z, rows));
                continue;
            }
            // The rows are empty when the box of their bounds shows it, and have a point when
            // one of the five points of the box that `box_point` tries holds them; otherwise
            // the question is refused.
            //
            // Complexity tradeoff: a system that the box neither empties nor satisfies, once
            // no elimination is left that keeps the rows from growing, is given up: it gets
            // `Refusal::Growth` ("not decided", rejected at the function by `run.rs`
            // `linear_questions`), though it may have a point or none. Only five points of the
            // box are tried (nearest zero, lower corner, upper corner, the two midpoints), so a
            // system whose points all lie elsewhere in the box is refused. Why: an
            // elimination that adds terms multiplies lower by upper bounds, so the rows can grow
            // doubly exponentially in the variables eliminated (Fourier–Motzkin), and the dark
            // and gray shadows of the full Omega test add an exponential search on top; trying
            // every point of the box is exponential in the variables. Trigger: three live
            // variables with no unit side, or four or more, whose every elimination pairs more
            // bounds than it removes and whose rows are not all `±x ± y + k >= 0`; the size of
            // the system plays no part. (Three live variables with a unit side are decided by
            // the `hull3` stage above.) Tests: `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`,
            // `l01_38_presburger::checker::a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused`,
            // `l01_38_presburger::scaling::the_shifted_sparse_family_scales`. COMPLEXITY.md
            // rows S18 and Kept "Fourier–Motzkin pairs". A complete solution would run the
            // growing eliminations of the full Omega test (or another complete Presburger
            // procedure) and accept their exponential worst case, or find a structural class
            // of growing systems decidable in O(n log n); plan item HULL3-GEN (which needs the
            // cross-review XR3) is the general fix for three live variables with no unit side.
            let Some((lo, hi)) = bounds(&self.sys) else {
                return Leaf::Empty;
            };
            if box_empty_in(&self.sys, &lo, &hi) {
                return Leaf::Empty;
            }
            let Some(v) = box_point(&self.sys, &lo, &hi) else {
                return Leaf::Refused(Refusal::Growth);
            };
            start = v;
            break;
        }
        if !self.want {
            return Leaf::Point(Vec::new());
        }
        let mut vals = start;
        vals.resize(self.sys.vars.len(), Int::ZERO);
        for step in self.steps.iter().rev() {
            let (j, v) = match step {
                Step::Defined(j, def) => (*j, def.eval(&vals)),
                Step::Chosen(j, rows) => (*j, choose(rows, *j, &vals)),
            };
            vals[j] = v;
        }
        Leaf::Point(vals)
    }

    /// Decides the rows, which hold two variables or fewer: their variables and a point of
    /// them, or `None` when they have no integer point.
    fn pair(&self) -> Option<(Vec<usize>, Vec<Int>)> {
        let mut vs: Vec<usize> = Vec::new();
        for a in self.sys.rows.keys() {
            for (i, _) in a.iter() {
                if !vs.contains(i) {
                    vs.push(*i);
                }
            }
        }
        vs.sort_unstable();
        let rows: Vec<(&[Term], &Int)> = self.sys.rows.iter().map(|(a, h)| (&**a, &h.k)).collect();
        let (x, y) = twovar::point(&rows, vs[0], vs.get(1).copied(), self.want)?;
        Some((vs, vec![x, y]))
    }

    /// The splinter of the dark elimination whose step is at `at`, the system then having
    /// `vars` variables, for its bound `r >= 0` on `x = x[j]` with coefficient `±a` there, and
    /// `m` the largest coefficient of `x`, in magnitude, among the bounds of the other side:
    /// the problem with `r == k` for a fresh `0 <= k <= (a·m - a - m) / m` [Omega, sec. 2.3;
    /// for an upper bound, the same of `-x`], or `None` when that range is empty.
    /// It is built from the given rows and the definitions made before the step, so nothing of
    /// this run's state is copied: its points are points of the problem, and it holds the
    /// points of the splinter of the system at the step, each of which extends to one.
    fn splinter(
        &self,
        base: &[(Row, Rel)],
        at: usize,
        vars: usize,
        bound: &Row,
        j: usize,
        m: &Int,
    ) -> Option<Omega> {
        let a = &bound.at(j).abs();
        let top = (&(&(a * m) - a) - m).div_floor(m);
        if top.is_negative() {
            return None;
        }
        let k = vars;
        let mut rows: Vec<(Row, Rel)> = base.to_vec();
        for step in &self.steps[..at] {
            if let Step::Defined(v, def) = step {
                let a = merge(
                    &def.a,
                    &Int::ONE,
                    &[(*v, Int::ONE)],
                    &-&Int::ONE,
                    usize::MAX,
                );
                rows.push((
                    Row {
                        a,
                        k: def.k.clone(),
                    },
                    Rel::Eq,
                ));
            }
        }
        let a = merge(
            &bound.a,
            &Int::ONE,
            &[(k, Int::ONE)],
            &-&Int::ONE,
            usize::MAX,
        );
        rows.push((
            Row {
                a,
                k: bound.k.clone(),
            },
            Rel::Eq,
        ));
        rows.push((
            Row {
                a: vec![(k, Int::ONE)].into(),
                k: Int::ZERO,
            },
            Rel::Ge,
        ));
        rows.push((
            Row {
                a: vec![(k, -&Int::ONE)].into(),
                k: top,
            },
            Rel::Ge,
        ));
        Some(Omega::new(vars + 1, &rows, self.want, false))
    }

    /// Solves the equality in slot `s`: by a unit coefficient where it has one, or else by one
    /// unimodular step on the variable `y` of least coefficient `b`, the first on a tie: with
    /// `q[i]` the nearest integer to `a[i] / b` at each other `x[i]` and `q` that of `k / b`,
    /// `y = t - Σ q[i]·x[i] - q` for a fresh `t`. The map is onto the integers, and leaves the symmetric remainder of each
    /// `a[i]` by `b`, so the least coefficient at least halves and every other falls below it in
    /// one step, however large it was.
    fn equality(&mut self, s: usize) {
        let e = self.es.clear(s);
        if let Some((j, _)) = e.a.iter().find(|(_, c)| c.is_unit()) {
            self.define(*j, &e);
            return;
        }
        let (y, b) =
            e.a.iter()
                .map(|(i, c)| (*i, c))
                .min_by_key(|(i, c)| (c.abs(), *i))
                .expect("a row has a variable");
        let t = self.fresh();
        let mut a: Vec<Term> =
            e.a.iter()
                .filter(|(i, _)| *i != y)
                .map(|(i, c)| (*i, -&(c - &mod_hat(c, b)).div_floor(b)))
                .filter(|(_, q)| !q.is_zero())
                .collect();
        a.push((t, Int::ONE));
        // The constant is reduced with the rest, so that values do not grow past what the
        // solutions need.
        let def = Row {
            a: a.into(),
            k: -&(&e.k - &mod_hat(&e.k, b)).div_floor(b),
        };
        self.es.put(s, e, &mut self.sys);
        self.es.subst(y, &def, &mut self.sys);
        self.steps.push(Step::Defined(y, def.clone()));
        self.pending.push((y, def));
    }

    fn fresh(&mut self) -> usize {
        self.sys.vars.push(Var::default());
        self.es.of.push(BTreeSet::new());
        self.sys.vars.len() - 1
    }

    /// Replaces `x[j]` everywhere by what the equality `e`, whose coefficient there is a unit,
    /// makes it.
    fn define(&mut self, j: usize, e: &Row) {
        // `aj·x + rest == 0`, so `x = -aj·rest`.
        let f = -e.at(j);
        let def = Row {
            a: merge(&e.a, &f, &[], &Int::ZERO, j),
            k: &e.k * &f,
        };
        self.es.subst(j, &def, &mut self.sys);
        self.steps.push(Step::Defined(j, def.clone()));
        self.pending.push((j, def));
    }

    /// Fixes each variable every row but its bounds pulls to one bound, at that bound: a point
    /// with the variable elsewhere between its bounds stays a point when it moves there, so
    /// this keeps every answer, and it holds of several variables at once.
    fn fix(&mut self) {
        for j in std::mem::take(&mut self.sys.fixable) {
            let (lo, hi) = (self.sys.bound(j, false), self.sys.bound(j, true));
            let s = &self.sys.vars[j].sides;
            let v = match (s.lo == s.lo_unary, s.hi == s.hi_unary, lo, hi) {
                // Only bounds: the value nearest zero.
                (true, true, Some(l), Some(h)) => l.max(Int::ZERO).min(h),
                (true, _, Some(l), _) => l,
                (_, _, _, Some(h)) => h,
                _ => unreachable!("a fixable variable has the bound"),
            };
            let def = Row {
                a: Vec::new().into(),
                k: v,
            };
            self.steps.push(Step::Defined(j, def.clone()));
            self.pending.push((j, def));
        }
    }

    /// Writes the pending definitions into the inequalities, each row once. A definition holds
    /// only variables defined after it, or none, so each is resolved from the last back.
    fn flush(&mut self) {
        let defs = std::mem::take(&mut self.pending);
        let mut whole: BTreeMap<usize, Row> = BTreeMap::new();
        for (j, def) in defs.iter().rev() {
            let r = resolve(def, &whole);
            whole.insert(*j, r);
        }
        let mut rows = Vec::new();
        for (j, _) in &defs {
            rows.extend(self.sys.take(*j));
        }
        for r in rows {
            self.sys.add(resolve(&r, &whole));
        }
    }
}

/// `r` with each variable `whole` defines replaced by its definition.
fn resolve(r: &Row, whole: &BTreeMap<usize, Row>) -> Row {
    let mut sum: BTreeMap<usize, Int> = BTreeMap::new();
    let mut k = r.k.clone();
    for (v, c) in r.a.iter() {
        if let Some(d) = whole.get(v) {
            k = &k + &(c * &d.k);
            for (w, e) in d.a.iter() {
                let t = c * e;
                let at = sum.entry(*w).or_insert(Int::ZERO);
                *at = &*at + &t;
            }
        } else {
            let at = sum.entry(*v).or_insert(Int::ZERO);
            *at = &*at + c;
        }
    }
    Row {
        a: sum.into_iter().filter(|(_, c)| !c.is_zero()).collect(),
        k,
    }
}

/// The value nearest zero for `x[j]` that the rows allow at the values `m` of the variables
/// chosen after it, `m[j]` being zero still.
fn choose(rows: &[Row], j: usize, m: &[Int]) -> Int {
    let (mut lo, mut hi) = (None::<Int>, None::<Int>);
    for r in rows {
        let c = r.at(j);
        let rest = r.eval(m);
        // `c·x + rest >= 0`.
        if c.is_positive() {
            let b = -&rest.div_floor(c);
            lo = Some(lo.map_or(b.clone(), |l| l.max(b)));
        } else {
            let b = rest.div_floor(&-c);
            hi = Some(hi.map_or(b.clone(), |h| h.min(b)));
        }
    }
    match (lo, hi) {
        (Some(l), _) if l.is_positive() => l,
        (_, Some(h)) if h.is_negative() => h,
        _ => Int::ZERO,
    }
}

/// The values of a symbol over the formula's points, as a union of intervals (see the module
/// note): exact when one disjunction is left, a set holding them otherwise. A bound past `i64`
/// is read as no bound.
///
/// Complexity tradeoff: with two or more disjunctions the answer is the meet of each
/// disjunction's union of projections, with its two ends moved in by [`tighten`]; the gaps
/// that only a combination of disjuncts shows are given up, so the set can hold values no
/// point takes. Why: the exact projection is the union over every combination of one disjunct
/// per disjunction, which is exponential in the disjunctions. Trigger: more than one
/// disjunction left after propagation. Test:
/// `l01_38_presburger::random::random_tests_agree_with_the_interpreter` (every projection
/// holds every value; one of 60 is wider than the hull). COMPLEXITY.md rows S7 and S16. A
/// complete solution would project each combination of disjuncts, or a decision diagram over
/// the disjuncts, at a cost exponential in the worst case.
///
/// The `i64` bound (see [`hull_from`]) violates the no-thresholds rule; to be replaced.
pub fn project(f: &Formula, sym: &Atom) -> Result<IntervalSet, Refusal> {
    project_each(f, std::slice::from_ref(sym))?.0.remove(0)
}

/// The projections of [`project_each`], one for each symbol, and the causes for which a
/// disjunction was left out of them.
pub type Each = (Vec<Result<IntervalSet, Refusal>>, Vec<Refusal>);

/// [`project`] onto each of `syms`, removing disjuncts once: one result for each symbol, so
/// that a symbol whose hull is refused leaves the others projected. With them, the causes for
/// which a disjunction was left out, which leaves each hull wider but sound.
pub fn project_each(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    match propagate(f)? {
        Some(p) => project_parts(p, syms, Some(f)),
        None => Ok(no_points(syms)),
    }
}

/// [`project_each`]'s answer for a formula with no point.
fn no_points(syms: &[Atom]) -> Each {
    (
        syms.iter().map(|_| Ok(IntervalSet::empty())).collect(),
        Vec::new(),
    )
}

/// [`project_each`] of the settled parts `p` of a formula, which is `whole` when it is given.
/// A disjunct is projected from the parts of it, shared, not copied, and the base groups it
/// touches, found from its atoms, which are found once ([`Parts::atoms`]), or from the base's
/// atoms when they are fewer, so that a nest of disjunctions `d` deep costs each disjunct once,
/// not once for each level above it. A disjunct is asked only for the symbols that every
/// disjunct with a point beside it touches, and a hull is tightened at the top over the whole
/// formula and below it over the level with each disjunct's disjunctions cut to their
/// disjuncts' own constraints and its projections added ([`summarize`]), so that no level
/// reads the whole nest below it either.
fn project_parts(mut p: Parts, syms: &[Atom], whole: Option<&Formula>) -> Result<Each, Refusal> {
    let none = || no_points(syms);
    let mut skipped: Vec<Refusal> = Vec::new();
    if p.ors.len() > 1 && pick(&p, whole.is_some()).is_err() {
        let Some(q) = probe(p)? else {
            return Ok(none());
        };
        p = q;
    }
    let Some(model) = solve(&p.cons, true)? else {
        return Ok(none());
    };
    // The base's constraints in groups linked by shared atoms ([`Linked`]). The base has a
    // point, so its groups are independent: a symbol's hull over the base is its hull over its
    // own group, and a disjunct is projected with the groups its atoms touch, onto the symbols
    // in them, the others keeping the base's hull. A projection then costs the groups each
    // disjunct touches, not the whole base for each disjunct and each symbol.
    // With two disjunctions or more, a hull with two finite bounds, the only hull a tightening
    // moves, is tightened: at the top over the whole formula, below it over [`summarize`].
    let ors = std::mem::take(&mut p.ors);
    let n_ors = ors.len();
    let linked = Linked::of(std::mem::take(&mut p.cons));
    let bases: HashMap<usize, Formula> = (0..linked.held.len())
        .filter(|r| !linked.held[*r].is_empty())
        .map(|r| {
            let cs = linked.held[r]
                .iter()
                .map(|i| Formula::Con(linked.cons[*i].clone()));
            (r, Formula::and(cs.collect()))
        })
        .collect();
    // The group of an atom: a symbol no constraint mentions is a group of its own, numbered
    // past the linked atoms.
    let index: HashMap<&Atom, usize> = syms.iter().enumerate().map(|(k, s)| (s, k)).collect();
    let group = |a: &Atom| match linked.ids.get(a) {
        Some(i) => Some(linked.root(*i)),
        None => index.get(a).map(|k| linked.parent.len() + k),
    };
    let mut syms_of: HashMap<usize, Vec<usize>> = HashMap::new();
    for (k, s) in syms.iter().enumerate() {
        let g = group(s).expect("a symbol's group");
        syms_of.entry(g).or_default().push(k);
    }
    // The symbols no base constraint mentions.
    let free: Vec<&Atom> = index
        .keys()
        .copied()
        .filter(|s| !linked.ids.contains_key(*s))
        .collect();
    let top = Formula::top();
    let base_of = |r: usize| bases.get(&r).unwrap_or(&top);
    let mut out: Vec<Result<IntervalSet, Refusal>> = syms
        .iter()
        .map(|s| hull_from(base_of(group(s).expect("a symbol's group")), s, &model))
        .collect();
    // For each disjunction, its disjuncts with a point and their projections, each sorted by
    // symbol; read only to tighten a hull, so kept only with two disjunctions or more.
    let mut seen: Vec<Option<Vec<Projected>>> = Vec::new();
    for ds in &ors {
        // For each symbol, the join of its projections over the satisfiable disjuncts that
        // touch it (`None` once one is refused), and how many touch it; a satisfiable disjunct
        // that does not touch it gives the base's hull, which leaves it as it is.
        let mut acc: HashMap<usize, (Option<IntervalSet>, usize)> = HashMap::new();
        let (mut sat, mut refused) = (0usize, false);
        let mut found_here = Vec::new();
        // A symbol changes only when every disjunct with a point touches it, so the disjuncts
        // are read smallest first, and each is asked only for the symbols that every disjunct
        // with a point before it touched (`None`: all of them). A deep disjunct beside a small
        // one is then asked for the few symbols the small one names, not for every symbol of
        // the nest below it.
        let mut order: Vec<&Parts> = ds.iter().map(|d| &**d).collect();
        order.sort_by_key(|d| d.atoms().len());
        let mut wanted: Option<Vec<usize>> = None;
        for d in order {
            // The groups the disjunct touches, found from its atoms or from the base's,
            // whichever are fewer, so that a level does not read every atom below it.
            let atoms = d.atoms();
            let mut roots: Vec<usize> = if atoms.len() <= linked.ids.len() {
                (atoms.iter())
                    .filter_map(|a| linked.ids.get(a).map(|i| linked.root(*i)))
                    .collect()
            } else {
                (linked.ids.iter())
                    .filter(|(a, _)| atoms.contains(*a))
                    .map(|(_, i)| linked.root(*i))
                    .collect()
            };
            roots.sort_unstable();
            roots.dedup();
            let ks: Vec<usize> = match &wanted {
                Some(ws) => ws
                    .iter()
                    .copied()
                    .filter(|&k| match linked.ids.get(&syms[k]) {
                        Some(i) => roots.binary_search(&linked.root(*i)).is_ok(),
                        None => atoms.contains(&syms[k]),
                    })
                    .collect(),
                None => {
                    let named: Vec<&Atom> = if atoms.len() <= free.len() {
                        (atoms.iter())
                            .filter(|a| index.contains_key(a) && !linked.ids.contains_key(*a))
                            .collect()
                    } else {
                        free.iter()
                            .copied()
                            .filter(|s| atoms.contains(*s))
                            .collect()
                    };
                    let groups = roots
                        .iter()
                        .copied()
                        .chain(named.into_iter().filter_map(group));
                    let mut ks: Vec<usize> = groups
                        .flat_map(|r| syms_of.get(&r).into_iter().flatten().copied())
                        .collect();
                    ks.sort_unstable();
                    ks.dedup();
                    ks
                }
            };
            // The disjunct's parts with the base groups it touches, its constraints sorted as
            // [`nnf`] sorts them and its disjunctions shared.
            let mut fs: Vec<Formula> = roots.iter().map(|r| base_of(*r).clone()).collect();
            fs.extend(d.cons.iter().cloned().map(Formula::Con));
            let mut q = Parts::of(Formula::and(fs));
            q.cons.sort();
            q.ors.extend(d.ors.iter().cloned());
            let sub: Vec<Atom> = ks.iter().map(|&k| syms[k].clone()).collect();
            // A disjunct asked for no symbol is only asked whether it has a point, as
            // [`decide`] asks it.
            let found_rs = settle(q).and_then(|q| match q {
                None => Ok((no_points(&sub), false)),
                Some(q) if ks.is_empty() => {
                    // A point of the disjunct with each disjunct below cut to its own
                    // constraints keeps it, as a level below the top is tightened
                    // ([`summarize`]); the search below it runs only when there is none.
                    let point = q.ors.is_empty()
                        || pick(&q, false).is_ok()
                        || !matches!(probe(q), Ok(None));
                    Ok(((Vec::new(), Vec::new()), point))
                }
                Some(q) => project_parts(q, &sub, None).map(|e| {
                    let point = e.0.iter().any(|r| !matches!(r, Ok(s) if s.is_empty()));
                    (e, point)
                }),
            });
            let (rs, has_point) = match found_rs {
                Ok(((rs, more), point)) => {
                    skipped.extend(more);
                    (rs, point)
                }
                Err(r) => {
                    skipped.push(r);
                    refused = true;
                    break;
                }
            };
            if !has_point {
                continue;
            }
            sat += 1;
            let mut kept = Vec::new();
            for (j, &k) in ks.iter().enumerate() {
                if let Err(r) = &rs[j] {
                    skipped.push(*r);
                }
                let e = acc.entry(k).or_insert((Some(IntervalSet::empty()), 0));
                e.0 =
                    e.0.take()
                        .and_then(|u| rs[j].as_ref().ok().map(|h| u.join(h)));
                e.1 += 1;
                if n_ors > 1
                    && let Ok(h) = &rs[j]
                {
                    kept.push((k, h.clone()));
                }
            }
            if n_ors > 1 {
                found_here.push((d, kept));
            }
            wanted = Some(ks);
        }
        if n_ors > 1 {
            seen.push((!refused).then_some(found_here));
        }
        if refused {
            continue;
        }
        if sat == 0 {
            return Ok(none());
        }
        for (k, (u, touched)) in acc {
            if touched == sat
                && let Some(u) = u
                && let Ok(o) = &mut out[k]
            {
                *o = o.meet(&u);
            }
        }
    }
    let finite = |o: &Result<IntervalSet, Refusal>| matches!(o, Ok(s) if matches!(s.bounds(), Some((End::Fin(_), End::Fin(_)))));
    if n_ors > 1 && out.iter().any(finite) {
        let mut summary: Option<Formula> = None;
        for (o, sym) in out.iter_mut().zip(syms) {
            let Ok(s) = o else { continue };
            let Some((End::Fin(_), End::Fin(_))) = s.bounds() else {
                continue;
            };
            let f = match whole {
                Some(f) => f,
                None => summary.get_or_insert_with(|| summarize(&linked.cons, &seen, syms)),
            };
            *o = tighten(f, sym, s.clone());
        }
    }
    skipped.sort_unstable();
    skipped.dedup();
    Ok((out, skipped))
}

/// A disjunct with a point and its projections, each with the index of its symbol, sorted.
type Projected<'a> = (&'a Parts, Vec<(usize, IntervalSet)>);

/// A level of [`project_parts`] below the top, with more points than it has, for tightening
/// its hulls: the base `cons` and, for each disjunction (`None` where a disjunct was refused),
/// the disjunction of its disjuncts with a point, each a disjunct's own constraints and, when
/// it has disjunctions, its projections onto the symbols it was asked for and each of its
/// disjunctions with every disjunct cut to its own constraints. Each part's constraints are
/// read here at its own level and at the level above it, so the summaries of a nest cost its
/// size twice, however deep it is.
// Complexity tradeoff: below the top, a hull is tightened over this formula, not over the
// level's own, so a bound that only a choice two disjunctions or more inside a disjunct, jointly
// with the rest of the level, pushes inward is left where the projections put it: a sound
// hull, wider than the level's. Test
// `l01_39_reduced_product::deep_condition::a_choice_two_levels_inside_a_branch_is_read_by_its_projections_only`
// asserts the wider hull `[3..=4, 10..=10, 100..=200]` where the level's own is
// `[3..=4, 100..=200]`; a choice one disjunction inside is read exactly
// (`a_choice_one_level_inside_a_branch_is_read_with_the_rest_of_the_branch`). The level's own
// formula holds the whole nest below it, and tightening over it at each level costs the nest
// once for each level above: measured on this code, `arms_of_a_capped_test_take_time_near_linear_in_its_depth`
// then takes 51.1 times the work from d = 30 to 240 (limit 24), O(d²) (COMPLEXITY S31). It is
// triggered by two disjunctions or more at a level below the top, one of them with a disjunct
// whose disjunctions have disjunctions of their own. A complete answer would need each level's
// formula decided incrementally from the level below's; in general the exact bound decides
// whether a nest of disjunctions of linear constraints has a point, which is NP-complete.
fn summarize(cons: &[Con], seen: &[Option<Vec<Projected>>], syms: &[Atom]) -> Formula {
    let own = |p: &Parts| -> Vec<Formula> { p.cons.iter().cloned().map(Formula::Con).collect() };
    let mut fs: Vec<Formula> = cons.iter().cloned().map(Formula::Con).collect();
    for ds in seen.iter().flatten() {
        let each = ds.iter().map(|(d, rs)| {
            let mut gs = own(d);
            if !d.ors.is_empty() {
                gs.extend(rs.iter().map(|(k, h)| member(&syms[*k], h)));
                let cut = d
                    .ors
                    .iter()
                    .map(|es| Formula::or(es.iter().map(|e| Formula::and(own(e))).collect()));
                gs.extend(cut);
            }
            Formula::and(gs)
        });
        fs.push(Formula::or(each.collect()));
    }
    Formula::and(fs)
}

/// `set`, holding every value of `sym` over `f`'s points, with each finite bound raised or
/// lowered by bisection to the nearest value at which `f` with `sym` past it is shown to have
/// no point. A bound moves only on such a proof, so a refused question leaves it sound.
fn tighten(f: &Formula, sym: &Atom, set: IntervalSet) -> Result<IntervalSet, Refusal> {
    let Some((End::Fin(lo), End::Fin(hi))) = set.bounds() else {
        return Ok(set);
    };
    let x = Lin::atom(sym.clone());
    let none = |con: Con| {
        matches!(
            decide(&Formula::and(vec![f.clone(), Formula::Con(con)])),
            Ok(false)
        )
    };
    // The least `v` in `lo..=hi` with no proof that `f` has no point where `sym <= v`, and the
    // greatest with none where `sym >= v`.
    let (mut a, mut b) = (i128::from(lo), i128::from(hi));
    while a < b {
        let mid = a + (b - a).div_euclid(2);
        if none(Con::ge(&Lin::constant(mid), &x)) {
            a = mid + 1
        } else {
            b = mid
        }
    }
    let new_lo = a;
    if none(Con::ge(&Lin::constant(new_lo), &x)) {
        return Ok(IntervalSet::empty());
    }
    let (mut a, mut b) = (new_lo, i128::from(hi));
    while a < b {
        let mid = b - (b - a).div_euclid(2);
        if none(Con::ge(&x, &Lin::constant(mid))) {
            b = mid - 1
        } else {
            a = mid
        }
    }
    Ok(set.meet(&IntervalSet::range(
        End::from_i128(new_lo),
        End::from_i128(a),
    )))
}

/// The least and greatest values of a symbol over a conjunction.
fn hull(c: &Formula, sym: &Atom) -> Result<IntervalSet, Refusal> {
    match satisfiable(c)? {
        Some(m) => hull_from(c, sym, &m),
        None => Ok(IntervalSet::empty()),
    }
}

/// [`hull`] given a point `m` of the conjunction, found by the monotone questions "is there a
/// point with the symbol at most `v`" and "at least `v`". Each bound is searched outward
/// from the point's value with steps that double, then by bisection, so it takes O(log d)
/// questions for a bound at distance d, and one when the symbol is unbounded that way.
///
/// Complexity tradeoff: the search covers `i64` only, so a bound past it is answered as no
/// bound (the set is wider, never wrong). Why: interval ends are machine integers
/// (`interval::End::Fin(i64)`), whose arithmetic costs O(1) where unbounded integers cost
/// time in their length. Trigger: a bound whose magnitude exceeds `i64`. Tests:
/// `l01_38_presburger::omega::a_bound_past_i64_is_searched_within_i64`,
/// `l01_38_presburger::omega::a_model_may_hold_values_past_128_bits`. COMPLEXITY.md row C1.
/// This switches behavior at a magnitude, so it violates the no-thresholds rule; to be
/// replaced. A complete solution would keep interval ends as unbounded integers
/// (`store::int`), at a cost in their bits.
fn hull_from(c: &Formula, sym: &Atom, m: &Model) -> Result<IntervalSet, Refusal> {
    let x = Lin::atom(sym.clone());
    let (min, max) = (i128::from(i64::MIN), i128::from(i64::MAX));
    // The point's value, within the range the search covers.
    let at = m.get(sym).map_or(0, |v| {
        let past = if v.is_negative() { min } else { max };
        v.to_i128().unwrap_or(past).clamp(min, max)
    });
    let with = |con: Con| -> Result<bool, Refusal> {
        decide(&Formula::and(vec![c.clone(), Formula::Con(con)]))
    };
    let below = |v: i128| with(Con::ge(&Lin::constant(v), &x));
    let above = |v: i128| with(Con::ge(&x, &Lin::constant(v)));
    // The last value of the monotone `holds` that is true, moving from `start` (true) by
    // `dir` toward `end` (false).
    let edge = |holds: &dyn Fn(i128) -> Result<bool, Refusal>,
                start: i128,
                end: i128,
                dir: i128|
     -> Result<i128, Refusal> {
        let (mut good, mut step) = (start, 1i128);
        let bad = loop {
            let next = good + dir * step;
            if (next - end) * dir >= 0 {
                break end;
            }
            if !holds(next)? {
                break next;
            }
            good = next;
            step *= 2;
        };
        let (mut good, mut bad) = (good, bad);
        while (bad - good).abs() > 1 {
            let mid = good + (bad - good) / 2;
            if holds(mid)? { good = mid } else { bad = mid }
        }
        Ok(good)
    };
    let lo = if below(min)? {
        End::NegInf
    } else {
        End::from_i128(edge(&below, at, min, -1)?)
    };
    let hi = if above(max)? {
        End::PosInf
    } else {
        End::from_i128(edge(&above, at, max, 1)?)
    };
    Ok(IntervalSet::range(lo, hi))
}

/// The set `s` of a symbol as a formula: the disjunction of its pieces.
pub fn member(sym: &Atom, s: &IntervalSet) -> Formula {
    within(&Lin::atom(sym.clone()), s)
}

/// The values of the term `l` in the set `s`, as a formula.
pub fn within(l: &Lin, s: &IntervalSet) -> Formula {
    let mut pieces = Vec::new();
    for &(lo, hi) in s.pieces() {
        let mut both = Vec::new();
        if let End::Fin(v) = lo {
            both.push(Formula::Con(Con::ge(l, &Lin::constant(v))));
        }
        if let End::Fin(v) = hi {
            both.push(Formula::Con(Con::ge(&Lin::constant(v), l)));
        }
        pieces.push(Formula::and(both));
    }
    Formula::or(pieces)
}

/// What rung 2 concludes about an entailment.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Entailment {
    /// The premises entail the goal; the certificate is the premise set, the products of the
    /// factor premises included.
    Proved(Vec<Formula>),
    /// The goal fails at these values of the symbols, where the premises hold.
    Refuted(Model),
    /// The premises with the products, read linearly, hold at these values with the goal
    /// failing, but the values of the product atoms are not the products of the symbols'.
    NotProved(Model),
    /// The question lies outside the fragment decided in polynomial time.
    Refused(Refusal),
}

impl fmt::Display for Entailment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let model = |m: &Model, f: &mut fmt::Formatter<'_>| {
            let parts: Vec<String> = m.iter().map(|(a, v)| format!("{a} = {v}")).collect();
            write!(f, "{}", parts.join(", "))
        };
        match self {
            Entailment::Proved(ps) => {
                let parts: Vec<String> = ps.iter().map(|p| p.to_string()).collect();
                write!(f, "proved from {}", parts.join(" && "))
            }
            Entailment::Refuted(m) => {
                write!(f, "refuted: countermodel ")?;
                model(m, f)
            }
            Entailment::NotProved(m) => {
                write!(f, "not proved: the linear reading fails at ")?;
                model(m, f)
            }
            Entailment::Refused(r) => write!(f, "refused: {r}"),
        }
    }
}

/// Whether `premises` entail `goal` (rung 2).
pub fn entails(premises: &Relation, goal: &Relation) -> Entailment {
    entails_inner(premises, goal).unwrap_or_else(Entailment::Refused)
}

fn entails_inner(premises: &Relation, goal: &Relation) -> Result<Entailment, Refusal> {
    let defs = Formula::and(vec![premises.defined(), goal.defined()]);
    let mut ps = vec![premises.body.clone()];
    ps.extend(products(premises, goal)?);
    let premise = Formula::and(ps.clone());
    let f = Formula::and(vec![
        defs.clone(),
        premise,
        Formula::negate(goal.body.clone()),
    ]);
    let Some(m) = satisfiable(&f)? else {
        return Ok(Entailment::Proved(ps));
    };
    // A countermodel of the linear reading is a countermodel when the premises hold and the
    // goal fails with each product read as a product.
    let real = Formula::and(vec![
        defs,
        premises.body.clone(),
        Formula::negate(goal.body.clone()),
    ]);
    let syms: Model = m
        .iter()
        .filter(|(a, _)| !matches!(a, Atom::Product(..)))
        .map(|(a, v)| (a.clone(), v.clone()))
        .collect();
    if real.holds(&syms) {
        let shown = syms
            .into_iter()
            .filter(|(a, _)| matches!(a, Atom::Sym(_)))
            .collect();
        return Ok(Entailment::Refuted(shown));
    }
    Ok(Entailment::NotProved(m))
}

/// For each product the formulas mention, the products in pairs of the premises on its two
/// factors, each `>= 0`.
///
/// Complexity tradeoff: a product of two variables is an opaque atom, bounded only by these
/// products of pairs of linear premises; a goal that needs any other nonlinear reasoning is
/// `Entailment::NotProved`. Why: entailment over integer polynomials is undecidable
/// (Hilbert's tenth problem), and over the reals it costs time doubly exponential in the
/// variables (cylindrical algebraic decomposition). Trigger: a product atom in the premises
/// or the goal. Test:
/// `l01_38_presburger::entailment::a_product_is_bounded_only_through_the_premises_on_its_factors`.
/// COMPLEXITY.md row C2. No complete solution exists for integers; a stronger sound one would
/// add higher-degree products of premises (Positivstellensatz certificates), at a cost
/// polynomial of growing degree.
fn products(premises: &Relation, goal: &Relation) -> Result<Vec<Formula>, Refusal> {
    let mut wanted = BTreeSet::new();
    for f in [&premises.body, &goal.body] {
        for a in f.atoms() {
            if let Atom::Product(x, y) = a {
                wanted.insert((x, y));
            }
        }
    }
    if wanted.is_empty() {
        return Ok(Vec::new());
    }
    // The top-level linear inequalities, an equality read as two.
    let mut linear = Vec::new();
    for g in premises.body.conjuncts() {
        if let Formula::Con(c) = g
            && c.lin.is_linear()
        {
            linear.push(c.lin.clone());
            if c.rel == Rel::Eq {
                linear.push(c.lin.times(-1));
            }
        }
    }
    let base = Formula::and(vec![
        premises.defined(),
        Formula::and(
            linear
                .iter()
                .map(|l| {
                    Formula::Con(Con {
                        lin: l.clone(),
                        rel: Rel::Ge,
                    })
                })
                .collect(),
        ),
    ]);
    let mut on: BTreeMap<Arc<str>, Vec<Lin>> = BTreeMap::new();
    let syms: BTreeSet<Arc<str>> = wanted
        .iter()
        .flat_map(|(x, y)| [x.clone(), y.clone()])
        .collect();
    for s in syms {
        let atom = Atom::Sym(s.clone());
        let mut set: Vec<Lin> = linear
            .iter()
            .filter(|l| l.terms.contains_key(&atom))
            .cloned()
            .collect();
        let x = Lin::atom(atom.clone());
        if let Some((lo, hi)) = hull(&base, &atom)?.bounds() {
            if let End::Fin(l) = lo {
                set.push(x.minus(&Lin::constant(l)));
            }
            if let End::Fin(h) = hi {
                set.push(Lin::constant(h).minus(&x));
            }
        }
        set.sort();
        set.dedup();
        on.insert(s, set);
    }
    let mut out = BTreeSet::new();
    for (x, y) in &wanted {
        for a in &on[x] {
            for b in &on[y] {
                if let Some(p) = a.product(b) {
                    out.insert(Con {
                        lin: p,
                        rel: Rel::Ge,
                    });
                }
            }
        }
    }
    Ok(out.into_iter().map(Formula::Con).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(s: &str) -> Atom {
        Atom::Sym(s.into())
    }

    fn lin(terms: &[(&str, i128)], k: i128) -> Lin {
        let mut l = Lin::constant(k);
        for (s, c) in terms {
            l = l.plus(&Lin::atom(sym(s)).times(*c));
        }
        l
    }

    fn ge(terms: &[(&str, i128)], k: i128) -> Formula {
        Formula::Con(Con {
            lin: lin(terms, k),
            rel: Rel::Ge,
        })
    }

    #[test]
    fn a_relation_prints_with_the_first_atom_on_the_left() {
        assert_eq!(ge(&[("a", -1), ("b", -1)], 49).to_string(), "a + b <= 49");
        assert_eq!(ge(&[("i", -1), ("n", 1)], -2).to_string(), "i <= n - 2");
        assert_eq!(ge(&[("x", 2)], -3).to_string(), "2 * x >= 3");
    }

    #[test]
    fn integer_points_are_decided_where_the_real_shadow_has_points() {
        // 2x = 2y + 1 has real points and no integer point.
        let f = Formula::Con(Con {
            lin: lin(&[("x", 2), ("y", -2)], -1),
            rel: Rel::Eq,
        });
        assert_eq!(satisfiable(&f), Ok(None));
        // 3 <= 2x <= 3 has none either. 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has none
        // (Pugh's example): its dark shadow is empty and its real shadow is not, and the
        // splinters, or the exact test on two variables, settle it.
        assert_eq!(
            satisfiable(&Formula::and(vec![
                ge(&[("x", 2)], -3),
                ge(&[("x", -2)], 3)
            ])),
            Ok(None)
        );
        let pugh = Formula::and(vec![
            ge(&[("x", 11), ("y", 13)], -27),
            ge(&[("x", -11), ("y", -13)], 45),
            ge(&[("x", 7), ("y", -9)], 10),
            ge(&[("x", -7), ("y", 9)], 4),
        ]);
        assert_eq!(satisfiable(&pugh), Ok(None));
        // Shifted to hold the point (2, 1), the dark shadow finds a point.
        let shifted = Formula::and(vec![
            ge(&[("x", 11), ("y", 13)], -27),
            ge(&[("x", -11), ("y", -13)], 45),
            ge(&[("x", 7), ("y", -9)], -5),
            ge(&[("x", -7), ("y", 9)], 5),
        ]);
        let m = satisfiable(&shifted).unwrap().unwrap();
        assert!(shifted.holds(&m), "{m:?}");
    }

    fn row(a: &[(usize, i128)], k: i128) -> Row {
        Row {
            a: a.iter().map(|(j, c)| (*j, Int::from(*c))).collect(),
            k: Int::from(k),
        }
    }

    #[test]
    fn columns_of_opposite_signs_merge_and_lift_by_bezout() {
        // `2x - 3y == 1` sees `x` and `y` only through `2x - 3y`, which takes every integer:
        // one variable with column 1, and its point lifted to `x` and `y`.
        let r = row(&[(0, 2), (1, -3)], -1);
        let point = quotient(2, vec![(r.clone(), Rel::Eq)], true)
            .expect("decided")
            .expect("a point");
        assert_eq!(r.eval(&point), Int::ZERO);
    }

    #[test]
    fn merged_columns_take_only_the_multiples_of_their_divisor() {
        // `2x + 4y` is even, so `2x + 4y == 1` has no point, though it has rational ones.
        let r = row(&[(0, 2), (1, 4)], -1);
        assert_eq!(quotient(2, vec![(r, Rel::Eq)], true), Ok(None));
    }

    #[test]
    fn bezout_factors_give_the_divisor() {
        for (a, b) in [
            (0, 5),
            (0, -5),
            (12, 18),
            (12, -18),
            (7, 1),
            (1, -7),
            (6, 35),
        ] {
            let (g, s, t) = bezout(&Int::from(a), &Int::from(b));
            let want = Int::from(a).gcd(&Int::from(b));
            assert_eq!(g, want, "{a} {b}");
            assert_eq!(
                &(&s * &Int::from(a)) + &(&t * &Int::from(b)),
                want,
                "{a} {b}"
            );
        }
    }
}
