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
//! Satisfiability is decided by the Omega test \[Omega\] on the fragment it settles in a number
//! of steps polynomial in the rows, though not in the bit length of the coefficients, with no
//! budget (docs/thresholds.md, replacement 4), in one loop over a
//! system that holds each set of coefficients once and knows each variable's rows and bound
//! counts, so that a step touches only the rows of the variable it removes. Arithmetic is
//! exact, over unbounded integers. Equalities are solved, with Pugh's symmetric remainder
//! where no coefficient is a unit; two opposite rows that meet become an equality, and so,
//! once, do the rows of a cycle of differences (`Omega::cycles`); a variable
//! bounded on one side only is dropped with its rows. Otherwise the variable whose elimination
//! adds the fewest rows, of those the one that writes the fewest terms, is eliminated, exact
//! eliminations first, and only while the system holds no more terms than it was given: each
//! step removes a variable and the terms never pass the input's count. An elimination is
//! exact when every lower or every upper coefficient of the variable is a unit.
//!
//! Before the parts are split, variables whose columns are multiples of one column are merged
//! into one variable (`quotient`), a unimodular change of variables that keeps every
//! integer point. Two cases are then decided exactly whatever the eliminations would do. Rows
//! over two variables or fewer are decided by counting the integer points under each piece of
//! their upper and lower envelopes ([`super::twovar`]). Rows `±x ± y + k >= 0` are decided by
//! the parity test on the zero-weight cycles of their tight constraint graph
//! ([`super::utvpi`]); once they are shown to have a point, exact eliminations that add terms
//! are allowed, since each keeps that form, and they are taken only when a model is wanted.
//!
//! When every elimination left would add terms, the box test decides what it can, in one pass
//! over the terms and with no linear program: each variable's bounds are tightened once by
//! every row from the bounds its bound rows give (`bounds`); the rows are empty when one of
//! them is below zero at every point of that box, have a point when one of five points of the
//! box holds every row (the point nearest zero, the lower and upper corners, and the two
//! midpoints, `box_point`), are decided completely by [`super::live3`] when three variables are
//! live, and are refused otherwise. At the first inexact elimination
//! the real shadow is tested once (`relaxed_empty`): real-shadow eliminations are taken
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
use super::interval::{End, IntervalSet, Num};
use super::linear::{Q, Term};
use super::{live3, twovar, utvpi};

mod deep;
use deep::Id;

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
/// words (sec:diagnostics), and each is a property of the system's shape, never of its size
/// or of the names of its variables; narrowing keeps the written constraint, which is sound.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Refusal {
    /// Every elimination of a variable would enlarge the system, which has four variables or
    /// more and is not of the form `±x ± y + k >= 0`; no row is below zero over the box its
    /// bounds give its variables, and each of the five points of that box that `box_point`
    /// tries misses some row. A system with three variables left is decided by `live3`.
    Growth,
    /// The integer points could lie only in a splinter of a splinter: a gray shadow within a
    /// gray shadow over four variables or more, whose search is exponential in the variables.
    Shadows,
    /// The search through the disjunctions found no point and removed no disjunct.
    Disjuncts,
    /// The next step would choose among variables, or equalities, that no structure of the
    /// rows tells apart and that share a row, so the choice would fall to their names; the
    /// stages that need no choice decided nothing.
    Tie(Arc<Tie>),
    /// The formula has disjunctions left after every disjunct with no point is removed, and
    /// atoms that no structure tells apart, so the search through the disjunctions would go in
    /// an order chosen by name; the one choice of disjuncts that the structure fixes, when
    /// there is one, has no point with the rest. The rows of the [`Tie`] are the disjunctions left.
    Unordered(Arc<Tie>),
}

/// The variables of a [`Refusal::Tie`], and the rows they share, written over the variables
/// left at that step: a variable the solver made up for an equality or a splinter is `t1`,
/// `t2` and so on, and a variable standing for several whose columns are multiples of one
/// column is written as their sum.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Tie {
    /// The variables, as written.
    pub vars: Vec<String>,
    /// The rows they share, each `... >= 0` or `... == 0`.
    pub rows: Vec<String>,
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Refusal::Growth => {
                "the integer constraints have four variables or more, each of whose \
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
            Refusal::Tie(t) => {
                let quote = |xs: &[String]| {
                    xs.iter()
                        .map(|x| format!("`{x}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                return write!(
                    f,
                    "variables that no structure tells apart would be eliminated in an order \
                     chosen by name: {} occur alike in the integer constraints (the same \
                     coefficients, in rows that occur alike), so the next step has no first \
                     among them, and they share {}; so whether the constraints hold at an \
                     integer point is not decided",
                    quote(&t.vars),
                    if t.rows.len() == 1 {
                        format!("the row {}", quote(&t.rows))
                    } else {
                        format!("the rows {}", quote(&t.rows))
                    }
                );
            }
            Refusal::Unordered(t) => {
                let quote = |xs: &[String]| {
                    xs.iter()
                        .map(|x| format!("`{x}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                return write!(
                    f,
                    "the disjunctions of the integer constraints would be searched in an order \
                     chosen by name: {} occur alike in the constraints (the same coefficients, \
                     in rows that occur alike), so no order of the search is fixed by their \
                     structure, and {} {} left after every disjunct with no point is removed, \
                     with no choice of one disjunct in each, fixed by the structure, that has a \
                     point with the rest; so whether the constraints hold at an integer point is \
                     not decided",
                    quote(&t.vars),
                    if t.rows.len() == 1 {
                        format!("the disjunction {}", quote(&t.rows))
                    } else {
                        format!("the disjunctions {}", quote(&t.rows))
                    },
                    if t.rows.len() == 1 { "is" } else { "are" }
                );
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

impl Formula {
    /// `true`.
    pub fn top() -> Formula {
        Formula::And(Arc::new(Vec::new()))
    }

    /// `false`.
    pub fn bottom() -> Formula {
        Formula::Or(Arc::new(Vec::new()))
    }

    /// The conjunction, flattened, `true` dropped and `false` absorbing.
    pub fn and(fs: Vec<Formula>) -> Formula {
        Formula::and_keeping(fs, |_| false)
    }

    /// [`Formula::and`], with each conjunction at an index of `fs` where `keep` holds kept
    /// whole, as one conjunct, and not flattened into this one. The translator keeps the
    /// formula of a name used as an operand of `&&` (`preimage::Tx::chain`), and the
    /// maps of a formula keep a conjunction that was kept in the node they rebuild
    /// (`Formula::rebuild`), so whether a part is kept follows the program and never how
    /// many handles hold it. A kept conjunction is read as flattened by compare, hash
    /// and show (`deep::Flat`), and, each kept part at its first place alone, by
    /// `Formula::conjuncts`, by `Conjuncts::and` and by `Parts::of`.
    // Complexity tradeoff: a kept conjunction is not merged into this one, so the tightening
    // below (one constraint per left-hand side) does not reach the constraints inside it, and a
    // constraint written both inside it and beside it is kept twice. No point is given up and
    // no answer changes; the printed relation lists the named part's constraints as written.
    // Merging would copy the named part's k constraints into each of the d places that use it,
    // O(d k), quadratic in the size of the program when k is about d. Trigger: a name of a
    // conjunction used as an operand of `&&`. Test
    // `l01_39_reduced_product::named_test::arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // COMPLEXITY.md S31b. A complete merge needs the conjunction as a persistent map from each
    // left-hand side to its constraint, shared with the named part and extended at each place.
    pub fn and_keeping(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        #[cfg(test)]
        if TWO_AT_A_TIME.get() {
            return tests::and_keeping_before(fs, keep);
        }
        let mut j = Joining::new(true);
        for (i, f) in fs.into_iter().enumerate() {
            j.operand(f, keep(i));
        }
        j.finish()
    }

    /// The disjunction, flattened, `false` dropped and `true` absorbing, and `true` when two
    /// disjuncts are complements (`Formula::complementary`).
    pub fn or(fs: Vec<Formula>) -> Formula {
        Formula::or_keeping(fs, |_| false)
    }

    /// [`Formula::or`], with each disjunction at an index of `fs` where `keep` holds kept
    /// whole, as one disjunct, as [`Formula::and_keeping`] keeps a conjunction: the formula of
    /// a name used as an operand of `||`, and a disjunction kept in the node a map rebuilds.
    // Complexity tradeoff: a kept disjunction is not merged into this one, so `complementary`
    // does not find a constraint inside it beside its complement outside it, and the disjunction
    // stays one, which holds at the same points: no answer changes, but each later test splits
    // into its cases. Merging would copy the named part's k disjuncts into each of the d places
    // that use it, O(d k). Trigger: a name of a disjunction used as an operand of `||`. Test
    // `l01_39_reduced_product::named_test::arms_of_a_wide_named_disjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // COMPLEXITY.md S31b. A complete check needs each kept part's constraints indexed in its
    // node, so that the lookup across it costs O(1) per disjunct.
    pub fn or_keeping(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        #[cfg(test)]
        if TWO_AT_A_TIME.get() {
            return tests::or_keeping_before(fs, keep);
        }
        let mut j = Joining::new(false);
        for (i, f) in fs.into_iter().enumerate() {
            j.operand(f, keep(i));
        }
        j.finish()
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
    /// [`Formula::and_keeping`] or [`Formula::or_keeping`]; a constraint has no parts and is
    /// copied. A part in the place of a conjunction kept in a conjunction, or of a disjunction
    /// kept in a disjunction ([`Formula::kept`]), is kept whole.
    fn rebuild(&self, mut parts: Vec<Formula>) -> Formula {
        match self {
            Formula::Con(c) => Formula::Con(c.clone()),
            Formula::Not(_) => Formula::negate(parts.pop().expect("one part")),
            Formula::And(_) => Formula::and_keeping(parts, |i| self.kept(i)),
            Formula::Or(_) => Formula::or_keeping(parts, |i| self.kept(i)),
        }
    }

    /// Whether the part at `i` of `self` is a conjunction kept whole in a conjunction, or a
    /// disjunction kept whole in a disjunction.
    fn kept(&self, i: usize) -> bool {
        match self {
            Formula::And(gs) => matches!(gs[i], Formula::And(_)),
            Formula::Or(gs) => matches!(gs[i], Formula::Or(_)),
            Formula::Con(_) | Formula::Not(_) => false,
        }
    }

    /// The negation, with double negations and constants removed.
    pub fn negate(f: Formula) -> Formula {
        match f {
            Formula::Not(_) => f.into_negated().expect("a negation"),
            Formula::And(ref gs) if gs.is_empty() => Formula::bottom(),
            Formula::Or(ref gs) if gs.is_empty() => Formula::top(),
            g => Formula::Not(Arc::new(g)),
        }
    }

    /// Each constraint, in order, the constraints of a part held in more than one place listed
    /// at its first place alone (`Formula::walk`), so the list is at most the number of
    /// distinct parts and not the size of the formula written out. A caller that needs each
    /// place, for a count or a position, cannot use it. Its callers in the compiler read it as
    /// a set (`atoms`) or as a conjunction (`unbounded`), which a repeated constraint does not
    /// change; `conjuncts::Conjuncts::cons` passes it on, conjunct by conjunct.
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

    /// The top-level conjuncts, with a conjunction kept among them ([`Formula::and_keeping`])
    /// read as flattened into it; a conjunction kept at more than one place is read at its first.
    fn conjuncts(&self) -> Vec<&Formula> {
        let mut out = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![self];
        while let Some(g) = stack.pop() {
            match g {
                Formula::And(gs) => {
                    if seen.insert(Arc::as_ptr(gs)) {
                        stack.extend(gs.iter().rev());
                    }
                }
                g => out.push(g),
            }
        }
        out
    }
}

/// A conjunction or a disjunction made one operand at a time: [`Formula::and_keeping`] and
/// [`Formula::or_keeping`] give it their operands, and the translator gives it each operand of
/// a chain of `&&` or of `||` (`preimage::Tx::chain`), so that a chain of k operands costs
/// O(k log k), and not the O(k²) that making the conjunction of each prefix in turn costs,
/// which copied and tightened the prefix again at each operand (ST-formula-k2).
pub struct Joining {
    /// A conjunction, or a disjunction.
    and: bool,
    /// The parts so far.
    out: Vec<Formula>,
    /// Of a conjunction, the place in `out` of the constraint on each term and comparison.
    at: BTreeMap<(BTreeMap<Atom, Int>, Rel), usize>,
    /// Whether an operand decided the whole: `false` met in a conjunction, two constraints on
    /// one term that cannot both hold, or `true` met in a disjunction.
    decided: bool,
    /// How many parts were added, a constraint merged into an earlier one counted too.
    added: usize,
}

/// Where a [`Joining`] was, from [`Joining::mark`].
#[derive(Clone, Copy)]
pub struct Mark {
    /// The count of parts added, a constraint merged into an earlier one counted too.
    added: usize,
    /// The length of `out`.
    len: usize,
}

impl Joining {
    /// An empty conjunction when `and`, otherwise an empty disjunction.
    pub fn new(and: bool) -> Joining {
        Joining {
            and,
            out: Vec::new(),
            at: BTreeMap::new(),
            decided: false,
            added: 0,
        }
    }

    /// Adds the operand `f`. A part of the joining's own kind is kept whole where `kept`, and
    /// otherwise its parts are added; the empty one of that kind is dropped, and the empty
    /// one of the other kind decides the whole.
    pub fn operand(&mut self, f: Formula, kept: bool) {
        if self.decided {
            return;
        }
        let (own, empty) = match &f {
            Formula::And(gs) => (self.and, gs.is_empty()),
            Formula::Or(gs) => (!self.and, gs.is_empty()),
            Formula::Con(_) | Formula::Not(_) => (false, false),
        };
        match (own, empty) {
            (true, true) => {}
            (false, true) => self.decided = true,
            (true, false) if !kept => {
                for g in f.into_parts().expect("a conjunction or a disjunction") {
                    self.part(g);
                }
            }
            _ => self.part(f),
        }
    }

    /// Adds `g` as a part. Of two constraints in a conjunction on one term and comparison,
    /// the tighter alone, in the place of the first.
    fn part(&mut self, g: Formula) {
        if self.decided {
            return;
        }
        self.added += 1;
        let Formula::Con(c) = &g else {
            self.out.push(g);
            return;
        };
        if !self.and {
            self.out.push(g);
            return;
        }
        let key = (c.lin.terms.clone(), c.rel);
        match self.at.get(&key) {
            Some(&i) => {
                let Formula::Con(old) = &self.out[i] else {
                    unreachable!("a constraint")
                };
                if c.rel == Rel::Ge && c.lin.constant < old.lin.constant {
                    self.out[i] = g;
                } else if c.rel == Rel::Eq && c.lin.constant != old.lin.constant {
                    self.decided = true;
                }
            }
            None => {
                self.at.insert(key, self.out.len());
                self.out.push(g);
            }
        }
    }

    /// Where the joining is now, to pass to [`Joining::close`].
    pub fn mark(&self) -> Mark {
        Mark {
            added: self.added,
            len: self.out.len(),
        }
    }

    /// Ends an inner operand of the chain, one that is itself a `&&` in a chain of `&&` (or a
    /// `||` in one of `||`), whose operands are those added since `mark`. Made apart, such an
    /// operand is the formula `finish` gives, which is its one part where it has one, and
    /// the chain around it adds that part as an operand that is not kept: its parts when it
    /// is of the joining's kind, nothing when it is the empty one of that kind, and the whole
    /// decided when it is the empty one of the other. This does the same, so that the chain
    /// gives the formula of its operands joined two at a time as written.
    pub fn close(&mut self, mark: Mark) {
        // One part added since `mark` and one more in `out`: the operand made apart is that
        // part alone, the last of `out`. A constraint merged into an earlier one is counted in
        // `added` alone, and the operand made apart holds it as a part of its own.
        if self.decided || self.added - mark.added != 1 || self.out.len() - mark.len != 1 {
            return;
        }
        let unwraps = match self.out.last() {
            Some(Formula::And(gs)) => self.and || gs.is_empty(),
            Some(Formula::Or(gs)) => !self.and || gs.is_empty(),
            _ => false,
        };
        if !unwraps {
            return;
        }
        let last = self.out.pop().expect("the last part");
        self.added -= 1;
        self.operand(last, false);
    }

    /// The conjunction or disjunction: its one part where it has one, and `true` for a
    /// disjunction of two complementary parts (`Formula::complementary`).
    pub fn finish(mut self) -> Formula {
        if self.decided {
            return if self.and {
                Formula::bottom()
            } else {
                Formula::top()
            };
        }
        if !self.and && Formula::complementary(&self.out) {
            return Formula::top();
        }
        if self.out.len() == 1 {
            self.out.pop().expect("one")
        } else if self.and {
            Formula::And(Arc::new(self.out))
        } else {
            Formula::Or(Arc::new(self.out))
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
    match Renamed::of(f) {
        Naming::Kept => satisfiable_inner(f),
        Naming::Renamed(r) => {
            let found = satisfiable_inner(&r.f).map_err(|e| r.back_refusal(e))?;
            Ok(found.map(|m| m.into_iter().map(|(a, v)| (r.back(&a), v)).collect()))
        }
        Naming::Tied(vars, color) => match settle_tied(f, &color, true)? {
            Settled::Empty => Ok(None),
            Settled::Point(m) => Ok(Some(m)),
            Settled::Left(p) => Err(unordered(vars, &p)),
        },
    }
}

/// [`satisfiable`] of a formula whose names no longer matter ([`Renamed`]).
fn satisfiable_inner(f: &Formula) -> Result<Option<Model>, Refusal> {
    match propagate(f)? {
        None => Ok(None),
        Some(p) => found(p),
    }
}

/// Whether `f` holds somewhere. A conjunction is decided without building a point; a point is
/// built only to search the disjunctions that propagation leaves.
pub fn decide(f: &Formula) -> Result<bool, Refusal> {
    match Renamed::of(f) {
        Naming::Kept => decide_inner(f),
        Naming::Renamed(r) => decide_inner(&r.f).map_err(|e| r.back_refusal(e)),
        Naming::Tied(vars, color) => match settle_tied(f, &color, false)? {
            Settled::Empty => Ok(false),
            Settled::Point(_) => Ok(true),
            Settled::Left(p) => Err(unordered(vars, &p)),
        },
    }
}

/// [`decide`] of a formula whose names no longer matter ([`Renamed`]).
fn decide_inner(f: &Formula) -> Result<bool, Refusal> {
    match propagate(f)? {
        None => Ok(false),
        Some(p) if p.ors.is_empty() => Ok(true),
        Some(p) => Ok(found(p)?.is_some()),
    }
}

/// The new name of `a` under the renaming `to` of [`Renamed`]; an atom not in it keeps its own,
/// and a product its factors renamed.
fn rename(to: &HashMap<Atom, Arc<str>>, a: &Atom) -> Atom {
    let sym = |s: &Arc<str>| (to.get(&Atom::Sym(s.clone()))).map_or_else(|| s.clone(), Arc::clone);
    match a {
        Atom::Product(x, y) => Atom::product(&sym(x), &sym(y)),
        Atom::Sym(_) | Atom::Aux(_) => to
            .get(a)
            .map_or_else(|| a.clone(), |s| Atom::Sym(s.clone())),
    }
}

/// A formula with disjunctions, its atoms renamed by the structure of its constraints, so that
/// the search through its disjunctions ([`pick`], [`probe`], [`project_parts`]) reads one
/// formula under every naming of its variables. That search takes, in each disjunction, the
/// first disjunct that serves, in an order and at points that the names decide: [`nnf`] sorts
/// the disjuncts, comparing atoms by name, and the points come from [`solve`], whose model
/// breaks ties by place. The coloring of [`stable_colors`] over every constraint of the
/// formula, read as one system, depends on the structure alone; when it gives each atom its
/// own color, the atom of color rank `k` is renamed `#k`, which no written name is, with `k`
/// written with leading zeros to one width so that the names sort as the ranks do. A renaming
/// of the variables carries their colors with them, so every naming gives the one formula,
/// and every answer and refusal of it is renamed back. A product keeps its factors, renamed:
/// the coloring is given, for each product, a row joining it to its two factors, so that a factor
/// that occurs only in products has a color too.
///
/// Complexity tradeoff: when two atoms share a color ([`Naming::Tied`]), no renaming is
/// fixed by the structure, so the formula is not searched: [`decide`] and [`satisfiable`]
/// settle it by [`settle_as_sets`], whose result no order of its parts changes, answer it
/// when no two disjunctions left are linked ([`alone`]), test what is otherwise left with the
/// disjuncts their colors choose ([`settle_tied`], [`by_color`]), and refuse
/// with [`Refusal::Unordered`] when that finds no point; [`project_each`] projects it by
/// [`project_parts`] with `sets`, which asks only such questions and keeps every disjunction.
/// What is given up: a formula with such atoms whose point or whose emptiness only the search
/// shows (`true` or `false` becomes the refusal; [`settle_tied`]'s tradeoff), and in a
/// projection, the narrowing that showing a disjunct empty by a search would give. Why:
/// telling such atoms apart is canonical labeling
/// of the formula's graph, which individualization and refinement (McKay and Piperno's nauty
/// and Traces) do in time exponential in the worst case, while color refinement alone gives
/// one color to atoms that no automorphism exchanges (regular graphs, the Frucht graph);
/// searching as written made the answer depend on the names (5 of 1,000 systems of the test
/// below). Trigger: a formula with a disjunction, after negations are pushed in, two of whose
/// atoms the coloring does not tell apart. Tests:
/// `l01_38_presburger::names::disjunctions_whose_atoms_share_a_color` and
/// `l01_38_presburger::names::a_formula_whose_atoms_share_a_color_is_settled_or_refused`.
/// COMPLEXITY.md row NAME-ties-or. A complete solution would rename by a canonical labeling,
/// or search the disjunctions completely (DPLL(T)); each is exponential in the worst case.
struct Renamed {
    /// The formula renamed.
    f: Formula,
    /// The atom renamed `#k`, at `k`.
    from: Vec<Atom>,
    /// The new name of each atom renamed.
    to: HashMap<Atom, Arc<str>>,
}

/// How the names of a formula's atoms reach its answer ([`Renamed::of`]).
enum Naming {
    /// They do not: the formula has no disjunction, and [`solve`] decides it by structure
    /// alone.
    Kept,
    /// The formula renamed by the colors of its atoms.
    Renamed(Renamed),
    /// Two atoms or more share a color: the atoms of the least such color, by name, and the
    /// color of each atom, which no renaming changes.
    Tied(Vec<Atom>, HashMap<Atom, usize>),
}

impl Renamed {
    /// How the names of `f`'s atoms are kept from its answer: not at all when it has no
    /// disjunction, by renaming when each atom has its own color, and otherwise by settling
    /// it without a search ([`Naming::Tied`]).
    fn of(f: &Formula) -> Naming {
        if !f.chooses() {
            return Naming::Kept;
        }
        let mut cons = f.cons();
        let mut atoms: BTreeSet<Atom> = BTreeSet::new();
        for c in &cons {
            atoms.extend(c.lin.terms.keys().cloned());
        }
        let joins: Vec<Con> = (atoms.iter())
            .filter_map(|a| match a {
                Atom::Product(x, y) => {
                    let factors =
                        Lin::atom(Atom::Sym(x.clone())).plus(&Lin::atom(Atom::Sym(y.clone())));
                    Some(Con::eq(
                        &Lin::atom(a.clone()).plus(&factors),
                        &Lin::default(),
                    ))
                }
                Atom::Sym(_) | Atom::Aux(_) => None,
            })
            .collect();
        for c in &joins {
            atoms.extend(c.lin.terms.keys().cloned());
        }
        cons.extend(joins.iter());
        let atoms: Vec<Atom> = atoms.into_iter().collect();
        let color = stable_colors(&atoms, &cons);
        let mut plain: Vec<usize> = (0..atoms.len())
            .filter(|&i| !matches!(atoms[i], Atom::Product(..)))
            .collect();
        plain.sort_unstable_by_key(|&i| color[i]);
        if let Some(w) = plain.windows(2).find(|w| color[w[0]] == color[w[1]]) {
            let tied = color[w[0]];
            let mut vars: Vec<Atom> = (plain.iter())
                .filter(|&&i| color[i] == tied)
                .map(|&i| atoms[i].clone())
                .collect();
            vars.sort_unstable();
            return Naming::Tied(vars, atoms.into_iter().zip(color).collect());
        }
        let from: Vec<Atom> = plain.iter().map(|&i| atoms[i].clone()).collect();
        // The rank is written with leading zeros to one width, so that names compare as their
        // ranks do: unpadded, `#10` sorts before `#2`, and [`nnf`] would hand the disjuncts of
        // a chain to [`pick`] out of rank order, where its first choices can fail and [`probe`]
        // runs (`l01_25_preimage_catalog::s22::chain_cross_live_scales`: 34.9 times the bytes
        // from 32 to 256 unpadded, against a limit of 24).
        let width = from.len().saturating_sub(1).to_string().len();
        let to: HashMap<Atom, Arc<str>> = (from.iter().enumerate())
            .map(|(k, a)| (a.clone(), Arc::from(format!("#{k:0width$}"))))
            .collect();
        let f = f.map_cons(&|c| {
            let terms = c.lin.terms.iter().map(|(a, k)| (rename(&to, a), k.clone()));
            Formula::Con(Con {
                lin: Lin {
                    terms: terms.collect(),
                    constant: c.lin.constant.clone(),
                },
                rel: c.rel,
            })
        });
        Naming::Renamed(Renamed { f, from, to })
    }

    /// The new name of `a`; an atom not in the formula keeps its own.
    fn there(&self, a: &Atom) -> Atom {
        rename(&self.to, a)
    }

    /// The atom that `a`, a new name or one kept, stands for.
    fn back(&self, a: &Atom) -> Atom {
        let of = |s: &Arc<str>| {
            let k = s.strip_prefix('#').and_then(|k| k.parse::<usize>().ok());
            k.map(|k| &self.from[k])
        };
        match a {
            Atom::Sym(s) => of(s).map_or_else(|| a.clone(), Atom::clone),
            Atom::Product(x, y) => {
                let factor = |s: &Arc<str>| match of(s) {
                    Some(Atom::Sym(t)) => t.clone(),
                    _ => s.clone(),
                };
                Atom::product(&factor(x), &factor(y))
            }
            Atom::Aux(_) => a.clone(),
        }
    }

    /// `text`, written over the new names, with each written as the atom it stands for.
    fn back_text(&self, text: &str) -> String {
        let mut out = String::with_capacity(text.len());
        let mut rest = text;
        while let Some(at) = rest.find('#') {
            out.push_str(&rest[..at]);
            let digits = rest[at + 1..]
                .bytes()
                .take_while(u8::is_ascii_digit)
                .count();
            match rest[at + 1..at + 1 + digits].parse::<usize>() {
                Ok(k) if k < self.from.len() => out.push_str(&self.from[k].to_string()),
                _ => out.push_str(&rest[at..at + 1 + digits]),
            }
            rest = &rest[at + 1 + digits..];
        }
        out.push_str(rest);
        out
    }

    /// The refusal `e` of the renamed formula, written over the atoms as given.
    fn back_refusal(&self, e: Refusal) -> Refusal {
        match e {
            Refusal::Tie(t) => Refusal::Tie(Arc::new(Tie {
                vars: t.vars.iter().map(|v| self.back_text(v)).collect(),
                rows: t.rows.iter().map(|v| self.back_text(v)).collect(),
            })),
            Refusal::Unordered(t) => Refusal::Unordered(Arc::new(Tie {
                vars: t.vars.iter().map(|v| self.back_text(v)).collect(),
                rows: t.rows.iter().map(|v| self.back_text(v)).collect(),
            })),
            Refusal::Growth | Refusal::Shadows | Refusal::Disjuncts => e,
        }
    }
}

/// The refusal of a formula whose atoms `vars` share a color ([`Naming::Tied`]) and whose
/// settled parts `p` keep disjunctions: the atoms, and the disjunctions left that mention one
/// of them, or every disjunction left when none does. A disjunct is written as its own
/// constraints, with `&& ...` for the disjunctions within it.
fn unordered(vars: Vec<Atom>, p: &Parts) -> Refusal {
    let mentions = |ds: &[Rc<Parts>]| {
        ds.iter()
            .any(|d| vars.iter().any(|v| d.atoms().contains(v)))
    };
    let write = |ds: &[Rc<Parts>]| {
        let each = ds.iter().map(|d| {
            let mut cs: Vec<String> = d.cons.iter().map(Con::to_string).collect();
            if !d.ors.is_empty() {
                cs.push("...".to_owned());
            }
            match cs.len() {
                1 => cs.pop().expect("one"),
                _ => format!("({})", cs.join(" && ")),
            }
        });
        each.collect::<Vec<_>>().join(" || ")
    };
    let near: Vec<String> = (p.ors.iter())
        .filter(|ds| mentions(ds))
        .map(|ds| write(ds))
        .collect();
    let mut rows = if near.is_empty() {
        p.ors.iter().map(|ds| write(ds)).collect()
    } else {
        near
    };
    rows.sort_unstable();
    Refusal::Unordered(Arc::new(Tie {
        vars: vars.iter().map(Atom::to_string).collect(),
        rows,
    }))
}

/// The parts `p` settled as [`settle`] settles them, with each test of a disjunct made
/// against a base that no order of the parts can change, for a formula whose atoms share a
/// color ([`Naming::Tied`]), whose parts [`nnf`] sorts by name.
///
/// [`settle`] reads the disjunctions one at a time, and a disjunction left with one disjunct
/// joins the base at once, so a later disjunct is tested against more rows than an earlier
/// one; [`solve`] may refuse a system and decide a smaller one empty, so that order could
/// change which disjuncts are removed. Here the disjunctions are read in stages: each stage
/// tests every disjunction it holds against the base as the stage began, and only then adds
/// the disjuncts left alone to the base and makes their disjunctions the next stage, as
/// [`settle`] reads them in the same round. Each test then has the same rows whatever the
/// order, [`solve`] answers by the rows and not their order or names, and the base after each
/// stage is the same set of rows ([`Linked::meet`] keeps the least constant for a term and
/// comparison whatever the order), so by induction on the stages and rounds every naming
/// gives the same rounds, the same disjuncts removed and the same answer. A disjunct whose
/// constraints hold at the point found for the base is kept untested, as [`settle`] keeps it,
/// only while that point holds every row added to the base since: it is then a point of the
/// base and the disjunct, so the test would keep it too, and the point, which may depend on
/// the names, changes no result. The cost is that of [`settle`] with the points of later
/// stages unused, at most one test of each disjunct for each round.
///
/// A disjunct is kept when its test finds a point or is refused, so a disjunct kept is not
/// shown to have a point: [`AsSets::proven`] says which were. The last round adds nothing to
/// the base (a round that adds rows is not the last), so each disjunct left was tested in it
/// against the base as returned, and the marks of that round hold for the parts returned.
fn settle_as_sets(mut p: Parts) -> Result<Option<AsSets>, Refusal> {
    let mut base = Linked::reduced(std::mem::take(&mut p.cons));
    loop {
        let Some(model) = solve(&base.cons, !p.ors.is_empty())? else {
            return Ok(None);
        };
        let mut proven: Vec<Vec<bool>> = Vec::new();
        if p.ors.is_empty() {
            p.cons = base.cons;
            return Ok(Some(AsSets { p, proven }));
        }
        let mut changed = false;
        // Whether `model` is a point of the base as it now stands.
        let mut at_model = true;
        let mut stage = std::mem::take(&mut p.ors);
        while !stage.is_empty() {
            let mut alone: Vec<Rc<Parts>> = Vec::new();
            for ds in stage {
                let n = ds.len();
                // Each disjunct not shown empty, and whether it is shown to have a point.
                let (mut live, shown): (Vec<Rc<Parts>>, Vec<bool>) = (ds.into_iter())
                    .filter_map(|d| {
                        if at_model && d.cons.iter().all(|c| c.holds(&model)) {
                            return Some((d, true));
                        }
                        let mut cs = base.around(&d.cons);
                        cs.extend(d.cons.iter());
                        match solve(&cs, false) {
                            Ok(None) => None,
                            Ok(Some(_)) => Some((d, true)),
                            Err(_) => Some((d, false)),
                        }
                    })
                    .unzip();
                changed |= live.len() < n;
                match live.len() {
                    0 => return Ok(None),
                    // The others are shown empty, so the formula's points are those of the
                    // base with this one, which the next round solves.
                    1 => alone.push(live.pop().expect("one")),
                    _ => {
                        p.ors.push(live);
                        proven.push(shown);
                    }
                }
            }
            // Rows added to the base are solved again in the next round.
            changed |= !alone.is_empty();
            stage = Vec::new();
            for d in &alone {
                at_model &= d.cons.iter().all(|c| c.holds(&model));
                d.cons.iter().for_each(|c| {
                    base.meet(c.clone());
                });
                stage.extend(d.ors.iter().cloned());
            }
        }
        if !changed {
            p.cons = base.cons;
            return Ok(Some(AsSets { p, proven }));
        }
    }
}

/// The parts that [`settle_as_sets`] leaves, and for each disjunction left, in the order of
/// `p.ors`, whether each of its disjuncts is shown to have a point with the base: [`solve`]
/// found one with the base rows linked to it, or its constraints hold at a point of the base.
/// A disjunct kept because [`solve`] refused it is not.
struct AsSets {
    p: Parts,
    proven: Vec<Vec<bool>>,
}

/// What [`settle_tied`] leaves of a formula whose atoms share a color.
enum Settled {
    /// No point.
    Empty,
    /// A point, or an empty model when none was asked for.
    Point(Model),
    /// The parts, with disjunctions that settling leaves and no disjunct taken by color.
    Left(Parts),
}

/// `f`, whose atoms share a color ([`Naming::Tied`]) and have the colors `color`, settled
/// ([`settle_as_sets`]) and then, when disjunctions are left, answered when no two of them are
/// linked ([`alone`]), or else tested with the disjuncts that their colors choose
/// ([`by_color`]): a point of the base with those disjuncts is a point of `f`. With `want`,
/// the point is built.
///
/// Complexity tradeoff: a formula with linked disjunctions left after settling is answered
/// only when each disjunction has one least disjunct by [`by_color`]'s key and the base with
/// those disjuncts has a point; otherwise it is `Left`, which [`decide`] and [`satisfiable`]
/// refuse with [`Refusal::Unordered`]. What is given up: such a formula whose only points lie
/// under other choices, or two of whose disjuncts tie on the key, and every such formula with no
/// point (`false` becomes the refusal; [`settle_as_sets`] still shows no point when a
/// disjunction loses every disjunct against the base). Why: a search that tries the
/// disjuncts in turn needs an order among those of equal key, and that order would come from
/// the names; testing every disjunct with every other disjunction instead, as the probe that
/// this replaced did, cost the disjuncts times a settling for each round, cubic on a star of
/// tied leaves with a disjunction each (8 to 64 leaves: 22 ms to 10.8 s). Here the test is one
/// [`solve`] after the settling, and the links are read once. Trigger: a formula with two
/// linked disjunctions left after settling, two of whose atoms the coloring does not tell
/// apart. Tests:
/// `l01_38_presburger::names::a_formula_whose_atoms_share_a_color_is_settled_or_refused`,
/// `l01_38_presburger::names::decide_on_tied_disjunctions_scales` and
/// `l01_38_presburger::names::decide_on_separate_tied_disjunctions_scales`. COMPLEXITY.md row
/// NAME-ties-or. A complete solution would search the disjunctions completely (DPLL(T)),
/// exponential in the disjunctions in the worst case, or tell the atoms apart by a canonical
/// labeling, exponential in the worst case too.
fn settle_tied(f: &Formula, color: &HashMap<Atom, usize>, want: bool) -> Result<Settled, Refusal> {
    let Some(AsSets { p, proven }) = settle_as_sets(Parts::of(nnf(f, true)))? else {
        return Ok(Settled::Empty);
    };
    // Settling solved the base, and showed a point of the base with each disjunct that
    // `alone` takes (it takes only those [`AsSets::proven`] marks), so a point need not be
    // found again unless it is wanted.
    let lone = alone(&p, &proven);
    if !want && (p.ors.is_empty() || lone.is_some()) {
        return Ok(Settled::Point(Model::new()));
    }
    let Some(cons) = lone.or_else(|| by_color(&p, color)) else {
        return Ok(Settled::Left(p));
    };
    Ok(match solve(&cons, want)? {
        Some(m) => Settled::Point(m),
        None => Settled::Left(p),
    })
}

/// The constraints of the settled parts `p` with one disjunct of each disjunction, when no
/// two disjunctions are linked, through rows of the base or through each other's disjuncts,
/// and each has a disjunct with no disjunction of its own that `proven` marks; otherwise
/// `None`. Settling left disjuncts that it did not show empty, and `proven`
/// ([`AsSets::proven`]) marks those shown to have a point with the base: each was tested
/// against the rows linked to it, or holds at a point of the base as it now stands
/// ([`settle_as_sets`]). A disjunct that [`solve`] refused is not marked and never taken,
/// even when it comes first: taking it would read a refusal as a point. The rows a disjunct
/// is linked to are linked to no other disjunction, so the points of separate groups
/// combine into one point of the base with every disjunct taken. Whether `p` has such a
/// point is then fixed by the links, which no renaming changes; the disjunct taken in each
/// disjunction is the first marked one with no disjunction of its own, which the names
/// order, so only the point found by [`satisfiable`] may change with them. The groups are
/// found by union and find over the atoms with path halving, linking each row and each
/// disjunction's atoms.
fn alone<'a>(p: &'a Parts, proven: &[Vec<bool>]) -> Option<Vec<&'a Con>> {
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut ids: HashMap<&'a Atom, usize> = HashMap::new();
    let mut parent: Vec<usize> = Vec::new();
    // Links the atoms given into one group, and gives the group's root, or `None` when no
    // atom is given.
    let mut link = |atoms: &mut dyn Iterator<Item = &'a Atom>| -> Option<usize> {
        let mut root: Option<usize> = None;
        for a in atoms {
            let next = parent.len();
            let i = *ids.entry(a).or_insert(next);
            if i == next {
                parent.push(i);
            }
            let r = find(&mut parent, i);
            match root {
                None => root = Some(r),
                Some(q) if q != r => parent[r] = q,
                Some(_) => {}
            }
        }
        root
    };
    p.cons.iter().for_each(|c| {
        link(&mut c.lin.terms.keys());
    });
    let roots: Vec<Option<usize>> = (p.ors.iter())
        .map(|ds| link(&mut ds.iter().flat_map(|d| d.atoms().iter())))
        .collect();
    let mut seen = vec![false; parent.len()];
    for r in roots.into_iter().flatten() {
        let r = find(&mut parent, r);
        if std::mem::replace(&mut seen[r], true) {
            return None;
        }
    }
    let mut cons: Vec<&Con> = p.cons.iter().collect();
    for (ds, shown) in p.ors.iter().zip(proven) {
        let (d, _) = (ds.iter().zip(shown)).find(|&(d, &s)| s && d.ors.is_empty())?;
        cons.extend(d.cons.iter());
    }
    Some(cons)
}

/// The key of a constraint that no renaming of its atoms changes, given their colors: its
/// comparison, its constant, and the color and coefficient of each term, sorted. An atom with
/// no color, which the formula colored has not, reads as the greatest color.
fn color_key<'a>(
    c: &'a Con,
    color: &HashMap<Atom, usize>,
) -> (Rel, &'a Int, Vec<(usize, &'a Int)>) {
    let mut terms: Vec<(usize, &Int)> = (c.lin.terms.iter())
        .map(|(a, k)| (color.get(a).copied().unwrap_or(usize::MAX), k))
        .collect();
    terms.sort_unstable();
    (c.rel, &c.lin.constant, terms)
}

/// The constraints of the settled parts `p` with, in each disjunction, and in each disjunction
/// of a disjunct taken, the disjunct whose constraints have the least sorted list of
/// [`color_key`]s, or `None` when two disjuncts of a disjunction share the least list. Each
/// choice reads one disjunction and the colors, which a renaming carries with the atoms, so
/// every naming takes the same disjuncts, renamed; the constraints are a set to [`solve`],
/// which answers by the rows and not their order or names. The nest is read on an explicit
/// stack, and each disjunct's key costs its constraints' terms times their logarithm.
fn by_color<'a>(p: &'a Parts, color: &HashMap<Atom, usize>) -> Option<Vec<&'a Con>> {
    let mut cons: Vec<&Con> = p.cons.iter().collect();
    let mut stack: Vec<&[Rc<Parts>]> = p.ors.iter().map(Vec::as_slice).collect();
    while let Some(ds) = stack.pop() {
        let key = |d: &'a Parts| {
            let mut k: Vec<_> = d.cons.iter().map(|c| color_key(c, color)).collect();
            k.sort_unstable();
            k
        };
        let mut least: Option<(_, &Parts)> = None;
        let mut tied = false;
        for d in ds {
            let k = key(d);
            match &least {
                Some((l, _)) if k > *l => {}
                Some((l, _)) if k == *l => tied = true,
                _ => {
                    least = Some((k, d));
                    tied = false;
                }
            }
        }
        let (_, d) = least?;
        if tied {
            return None;
        }
        cons.extend(d.cons.iter());
        stack.extend(d.ors.iter().map(Vec::as_slice));
    }
    Some(cons)
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

/// Whether `extra` is shown to meet the constraints taken so far nowhere by a part of them:
/// `extra`, the bounds of its atoms, and the constraints taken so far whose atoms are all
/// atoms of `extra`. When these have no point, neither has the whole; `false` shows nothing.
/// The cost is that of [`local_repair`]'s constraints, not of the groups `extra` touches.
fn local_refute(acc: &[Con], near: &Near, extra: &[Con]) -> bool {
    let seed: BTreeSet<&Atom> = extra.iter().flat_map(|c| c.lin.terms.keys()).collect();
    let mut ids = BTreeSet::new();
    let mut bounds = Vec::new();
    for a in &seed {
        if let Some(v) = near.by_atom.get(*a) {
            let within = |i: &usize| acc[*i].lin.terms.keys().all(|b| seed.contains(b));
            ids.extend(v.iter().copied().filter(within));
        }
        near.bounds(a, &mut bounds);
    }
    let local: Vec<&Con> = (extra.iter())
        .chain(&bounds)
        .chain(ids.into_iter().map(|i| &acc[i]))
        .collect();
    matches!(solve(&local, false), Ok(None))
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

/// Adds the constraints of a disjunct taken, a bound taken again kept once ([`Linked::meet`]).
/// A bound on one atom that [`Linked::meet`] puts in the place of a weaker one still tightens
/// that atom's bounds in `near`; a constraint of more atoms put in place keeps its atoms, so
/// its entries in `near` stand.
fn take(cons: &[Con], acc: &mut Linked, near: &mut Near) {
    for c in cons {
        let i = acc.cons.len();
        if acc.meet(c.clone()) || c.lin.terms.len() == 1 {
            near.add(i, c);
        }
    }
}

/// The constraints taken so far by [`pick`] or [`settle`], indexed for [`local_repair`]: each constraint of
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
        let Some((a, lo, hi)) = one_bound(c) else {
            for a in c.lin.terms.keys() {
                self.by_atom.entry(a.clone()).or_default().push(i);
            }
            return;
        };
        self.tighten(a, lo, hi);
    }

    /// Moves the least value of `a` up to `lo` and its greatest down to `hi`, where they are
    /// given and tighter.
    fn tighten(&mut self, a: &Atom, lo: Option<Int>, hi: Option<Int>) {
        narrow_to(&mut self.one, a, lo, hi);
    }

    /// Whether some constraint of one atom in `cons` leaves that atom no value within its
    /// bounds here.
    fn refutes(&self, cons: &[Con]) -> bool {
        cons.iter().filter_map(one_bound).any(|(a, lo, hi)| {
            let (l, h) = self
                .one
                .get(a)
                .map_or((None, None), |(l, h)| (l.as_ref(), h.as_ref()));
            let lo = [l, lo.as_ref()].into_iter().flatten().max();
            let hi = [h, hi.as_ref()].into_iter().flatten().min();
            matches!((lo, hi), (Some(lo), Some(hi)) if lo > hi)
        })
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

/// The atom of a constraint of one atom, with the least and the greatest value it allows that
/// atom; a least above the greatest allows none.
fn one_bound(c: &Con) -> Option<(&Atom, Option<Int>, Option<Int>)> {
    let mut terms = c.lin.terms.iter();
    let (Some((a, coef)), None) = (terms.next(), terms.next()) else {
        return None;
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
    Some((a, lo, hi))
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
/// points are found by [`pick`] on the parts of a test,
/// trying first the disjuncts that no point found so far holds: on a chain of `k` guards
/// `i >= j` on one input, two points (at the least and the greatest `i` the chain allows)
/// keep every disjunct but the `O(1)` that propagation removes, where testing each of the
/// `2k` disjuncts by a propagation of all `2k` disjunctions cost `k^2` (ledger LIN-probe).
///
/// A disjunct that a propagation removes is also read for its bounds of one atom by
/// [`learn`], which finds the bounds the formula implies, and each later disjunct that breaks
/// one of them is removed without a test: on `k` guards beyond the inputs, where the formula
/// implies `i > c` and the `c` disjuncts `i <= j - 1` with `j <= c + 1` have no point, one
/// search over their bounds removes them all (ledger LIN-probe-refute). Such a disjunct has no
/// point, so the formula's points are as before; it may be one that propagation alone would
/// have kept, so the result can have fewer disjuncts than one propagation per disjunct
/// leaves.
fn probe(mut p: Parts) -> Result<Option<Parts>, Refusal> {
    let mut points: Vec<Model> = Vec::new();
    // The bounds on single atoms that the formula implies, found by [`learn`]. The formula
    // only gains constraints or stays equal from round to round, so they hold to the end.
    let mut implied = Near::default();
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
            for (at, (d, h)) in ds.iter().zip(flags).enumerate() {
                let d = d.clone();
                if h || points[since..].iter().any(|m| d.holds(m)) {
                    live.push(d);
                    live_held.push(true);
                    continue;
                }
                if implied.refutes(&d.cons) {
                    continue;
                }
                if let Some(m) = point_with(&p, &held, &d, &implied) {
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
                // Complexity tradeoff: a disjunct that no point holds and no implied bound
                // removes is still tested by one propagation of all the parts, so `r` such
                // disjuncts cost `r` propagations of the whole formula, and failed-literal
                // probing is polynomial, not `O(n log n)`, when `r` grows with `n` and the
                // disjuncts share no bound of one atom that [`learn`] finds. Why: `settle`
                // does not report which disjuncts its proof covers, and an undoable
                // (trail-based) propagation does not help, since on a chain each refutation's
                // own propagation runs through the whole chain. Each refuted disjunct also
                // costs [`learn`]: for each bound of one atom it writes, an exponential and a
                // binary search over the `m` bounds the other disjuncts write on that atom, up
                // to about `2 log2 m + 1` tests, each one [`bounds_refute`] (one propagation
                // of bounds, `O(n log n)`) and, when that does not refute, one `settle`. The
                // search usually ends on a bound that has a point, and that test always costs
                // a `settle`. So when no learned bound removes a later disjunct, `r` refuted
                // disjuncts cost up to `O(r log m)` settles, not `r` (verifier's counters:
                // `guards_beyond_the_inputs_scale` 5 calls of `learn` and 16 settles in them,
                // cross 2 and 2). Trigger: disjuncts without a point whose proofs
                // differ by more than a bound of one atom. Tests:
                // `l01_25_preimage_catalog::s22::chains_on_two_inputs_keep_their_boxes`
                // reaches it (cross at `k = 51`); `chain_cross_above_its_width_scales` (cross
                // at 12 and 96, COMPLEXITY.md S22: 40.0 times the bytes with one propagation
                // per disjunct, 10.1 times now) and
                // `l01_38_presburger::probe::guards_beyond_the_inputs_scale` measure it. A
                // complete solution is a `settle` that returns, with each refutation, the
                // constraints its proof used (a conflict explanation), so that one propagation
                // removes every disjunct those constraints exclude.
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
                    continue;
                }
                // The disjunction without `d`, which the formula is equal to without it.
                let rest: Vec<Rc<Parts>> = live.iter().chain(&ds[at + 1..]).cloned().collect();
                learn(&p, rest, &d, &mut implied);
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

/// After [`probe`] has found that the disjunct `d` of its parts `p` has no point, tests each
/// bound of one atom in `d` alone: when the formula with `x <= h` has no point, it implies
/// `x >= h + 1`, which removes without a propagation every disjunct that bounds `x` by `h` or
/// less. Of the upper bounds on `x` that the disjuncts write, sorted, the greatest for which
/// the formula has no point is found by an exponential and then a binary search, so that `r`
/// disjuncts removed this way cost `O(log r)` propagations, not `r`; lower bounds likewise.
/// The formula with a weaker bound has more points, so the bounds without a point are those
/// up to one. `rest` is `d`'s disjunction without `d`, whose place in `p` is empty while it
/// is tested. Each bound is first tested by [`bounds_refute`], which costs `O(n log n)`, and
/// then by [`settle`]; a bound is recorded in `implied` only when one of them has shown that
/// the formula has no point with its negation, so each removal it makes is proved.
fn learn(p: &Parts, rest: Vec<Rc<Parts>>, d: &Parts, implied: &mut Near) {
    if rest.is_empty() {
        return;
    }
    let mut ors: Vec<Vec<Rc<Parts>>> = (p.ors.iter()).filter(|o| !o.is_empty()).cloned().collect();
    ors.push(rest);
    let f = Parts {
        cons: p.cons.clone(),
        ors,
        atoms: OnceCell::new(),
        failed: Cell::new(0),
    };
    for (x, lo, hi) in d.cons.iter().filter_map(one_bound) {
        // `upper`: the bound is `x <= v`; otherwise `x >= v`. An equality is a bound both
        // ways, and its refutation implies neither.
        let (v, upper) = match (lo, hi) {
            (None, Some(h)) => (h, true),
            (Some(l), None) => (l, false),
            _ => continue,
        };
        let con = |v: &Int| {
            let (x, v) = (Lin::atom(x.clone()), Lin::constant(v.clone()));
            if upper {
                Con::ge(&v, &x)
            } else {
                Con::ge(&x, &v)
            }
        };
        if implied.refutes(&[con(&v)]) {
            continue;
        }
        // The bounds on `x` of the same side that are no stronger than `v`, weakest last.
        let weaker = |w: &Int| if upper { *w >= v } else { *w <= v };
        let mut ws: Vec<Int> = (f.ors.iter().flatten())
            .flat_map(|e| e.cons.iter().filter_map(one_bound))
            .filter_map(|(y, l, h)| (y == x).then_some(if upper { h } else { l }).flatten())
            .filter(weaker)
            .chain([v.clone()])
            .collect();
        ws.sort_unstable();
        ws.dedup();
        if !upper {
            ws.reverse();
        }
        let none = |w: &Int| {
            let c = con(w);
            if bounds_refute(&f, x, &c) {
                return true;
            }
            let mut q = f.clone();
            q.cons.push(c);
            matches!(settle(q), Ok(None))
        };
        if !none(&ws[0]) {
            continue;
        }
        // `ws[good]` has no point; `ws[bad]`, when `bad < ws.len()`, has one.
        let (mut good, mut step) = (0, 1);
        let mut bad = loop {
            let at = good + step;
            if at >= ws.len() {
                break ws.len();
            }
            if !none(&ws[at]) {
                break at;
            }
            good = at;
            step *= 2;
        };
        while bad - good > 1 {
            let mid = good + (bad - good) / 2;
            if none(&ws[mid]) {
                good = mid;
            } else {
                bad = mid;
            }
        }
        let w = &ws[good];
        if upper {
            implied.tighten(x, Some(w + &Int::ONE), None);
        } else {
            implied.tighten(x, None, Some(w - &Int::ONE));
        }
    }
}

/// The least and the greatest value of each atom, as [`Near::one`] keeps them; an atom absent
/// is unbounded.
type AtomBounds = BTreeMap<Atom, (Option<Int>, Option<Int>)>;

/// A part of a formula that [`bounds_refute`] reads: a constraint, or a disjunction.
enum Unit<'a> {
    Con(&'a Con),
    Or(&'a [Rc<Parts>]),
}

impl<'a> Unit<'a> {
    /// The atoms of the part but `x`, each once.
    fn atoms(&self, x: &Atom) -> Vec<&'a Atom> {
        let cons: Vec<&'a Con> = match self {
            Unit::Con(c) => vec![c],
            Unit::Or(ds) => ds.iter().flat_map(|d| &d.cons).collect(),
        };
        let mut atoms: Vec<&'a Atom> = (cons.into_iter())
            .flat_map(|c| c.lin.terms.keys())
            .filter(|a| *a != x)
            .collect();
        atoms.sort_unstable();
        atoms.dedup();
        atoms
    }
}

/// Whether the bounds of the atoms, propagated, show that the parts `f` with the bound `extra`
/// on the atom `x` have no point. A constraint moves the bounds of each of its atoms by the
/// bounds of the others. A disjunction moves each atom that all its disjuncts mention to the
/// join of the bounds each disjunct leaves it, a disjunct's own constraints being propagated
/// twice from the bounds so far, and a disjunct left with an atom that has no value being
/// dropped; the disjunctions below a disjunct are not read, which leaves it more points, so
/// every answer `true` is a proof. The parts are read once in breadth-first order from the
/// constraints, two parts being neighbors when they share an atom other than `x`, and once in
/// the reverse order: on a chain of definitions the first reading carries the bounds from
/// each end to the middle and the second carries them on to the other end. `x` is left out
/// of the neighbors because the guards on it reach every part of a chain of guards, so that
/// every part would be one step from the constraints. The order is that of the parts'
/// structure, not of the atoms' names. Each reading costs each constraint once, `O(n log n)`
/// for parts of `n` terms with the map from atoms to parts.
///
/// Complexity tradeoff: the propagation is not repeated until no bound moves, so a proof that
/// needs bounds carried along a chain more than twice is not found here; [`learn`] then asks
/// [`settle`], and a disjunct no bound refutes is tested by its own propagation in [`probe`],
/// as before. Why: propagating bounds until none moves can move a bound by one per round on a
/// cycle of constraints with no point (`x >= y + 1`, `y >= x`), so the rounds grow with the
/// bounds' magnitude, not with the parts. Trigger: a proof that needs a bound carried back
/// along a chain after it was carried there. Tests:
/// `l01_25_preimage_catalog::s22::chain_cross_above_its_width_scales` (cross at 12 and 96,
/// COMPLEXITY.md S22) and `l01_38_presburger::probe::guards_beyond_the_inputs_scale` (guards
/// on symbols whose names do not sort in the chain's order). A complete solution is the exact
/// projection of the formula onto `x`, which with disjunctions is exponential in them.
fn bounds_refute(f: &Parts, x: &Atom, extra: &Con) -> bool {
    let units: Vec<Unit<'_>> = (f.cons.iter().map(Unit::Con))
        .chain(f.ors.iter().map(|ds| Unit::Or(ds)))
        .collect();
    let atoms: Vec<Vec<&Atom>> = units.iter().map(|u| u.atoms(x)).collect();
    let mut by_atom: BTreeMap<&Atom, Vec<usize>> = BTreeMap::new();
    for (u, xs) in atoms.iter().enumerate() {
        for a in xs {
            by_atom.entry(a).or_default().push(u);
        }
    }
    // Breadth first from the first part of each set of connected parts.
    let mut seen = vec![false; units.len()];
    let mut order: Vec<usize> = Vec::with_capacity(units.len());
    let mut done: BTreeSet<&Atom> = BTreeSet::new();
    let mut head = 0;
    for start in 0..units.len() {
        if seen[start] {
            continue;
        }
        seen[start] = true;
        order.push(start);
        while head < order.len() {
            for a in &atoms[order[head]] {
                if done.insert(a) {
                    for &v in &by_atom[a] {
                        if !seen[v] {
                            seen[v] = true;
                            order.push(v);
                        }
                    }
                }
            }
            head += 1;
        }
    }
    let mut b = AtomBounds::new();
    let first = narrow(extra, &mut b);
    let mut read = |u: usize| match &units[u] {
        Unit::Con(c) => narrow(c, &mut b),
        Unit::Or(ds) => narrow_or(ds, &mut b),
    };
    !(first && order.iter().rev().all(|&u| read(u)) && order.iter().all(|&u| read(u)))
}

/// Moves the bounds in `b` of the atoms of the disjunction `ds` to the join of those its
/// disjuncts leave ([`bounds_refute`]); `false` when every disjunct is left without a point.
fn narrow_or(ds: &[Rc<Parts>], b: &mut AtomBounds) -> bool {
    let mut join: Option<AtomBounds> = None;
    for d in ds {
        let mut own: AtomBounds = (d.cons.iter().flat_map(|c| c.lin.terms.keys()))
            .map(|a| (a.clone(), b.get(a).cloned().unwrap_or_default()))
            .collect();
        let holds = (0..2).all(|_| d.cons.iter().all(|c| narrow(c, &mut own)));
        if !holds {
            continue;
        }
        join = Some(match join {
            None => own,
            // An atom one disjunct does not mention keeps its bounds there, so the join keeps
            // only the atoms both mention.
            Some(j) => (j.into_iter())
                .filter_map(|(a, (l, h))| {
                    let (ol, oh) = own.get(&a)?;
                    let lo = l.zip(ol.as_ref()).map(|(l, o)| l.min(o.clone()));
                    let hi = h.zip(oh.as_ref()).map(|(h, o)| h.max(o.clone()));
                    Some((a, (lo, hi)))
                })
                .collect(),
        });
    }
    let Some(join) = join else {
        return false;
    };
    join.into_iter()
        .all(|(a, (lo, hi))| narrow_to(b, &a, lo, hi))
}

/// Moves the bounds in `b` of the atoms of `c` by the bounds of its other atoms; `false` when
/// an atom is left with no value, or `c` has no atom and does not hold.
fn narrow(c: &Con, b: &mut AtomBounds) -> bool {
    match c.rel {
        Rel::Ge => narrow_ge(&c.lin, true, b),
        Rel::Eq => narrow_ge(&c.lin, true, b) && narrow_ge(&c.lin, false, b),
    }
}

/// [`narrow`] for `lin >= 0`, or for `-lin >= 0` unless `sign`.
fn narrow_ge(lin: &Lin, sign: bool, b: &mut AtomBounds) -> bool {
    let signed = |k: &Int| if sign { k.clone() } else { -k };
    // The greatest value of each term `coef·x`, `None` when `x` is unbounded that way.
    let most: Vec<Option<Int>> = (lin.terms.iter())
        .map(|(a, coef)| {
            let coef = signed(coef);
            let (lo, hi) = b.get(a)?;
            if coef.is_positive() {
                hi.as_ref().map(|h| &coef * h)
            } else {
                lo.as_ref().map(|l| &coef * l)
            }
        })
        .collect();
    let unbounded = most.iter().filter(|m| m.is_none()).count();
    let sum = (most.iter().flatten()).fold(signed(&lin.constant), |s, m| &s + m);
    if lin.terms.is_empty() {
        return !sum.is_negative();
    }
    for ((a, coef), m) in lin.terms.iter().zip(&most) {
        let coef = &signed(coef);
        // The greatest value of the other terms and the constant, when it is bounded.
        let rest = match (m, unbounded) {
            (Some(m), 0) => &sum - m,
            (None, 1) => sum.clone(),
            _ => continue,
        };
        // `coef·x >= -rest`.
        let r = -&rest;
        let ok = if coef.is_positive() {
            // `x >= ceil(r / coef)`.
            narrow_to(b, a, Some(-&(-&r).div_floor(coef)), None)
        } else {
            // `x <= floor(r / coef)`, `coef` below zero.
            narrow_to(b, a, None, Some((-&r).div_floor(&-coef)))
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Moves the bounds in `b` of `a` in to `lo` and `hi` where they are given and tighter;
/// `false` when `a` is left with no value.
fn narrow_to(b: &mut AtomBounds, a: &Atom, lo: Option<Int>, hi: Option<Int>) -> bool {
    let (l, h) = b.entry(a.clone()).or_default();
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
    !matches!((&*l, &*h), (Some(l), Some(h)) if l > h)
}

/// A point of the formula of [`probe`]'s parts `p` where the disjunct `d` holds, `d` being a
/// disjunct of the disjunction that `p` lacks while it is tested, or `None` when [`pick`]
/// finds none. In each other disjunction `pick` tries first the disjuncts that `held` marks as
/// held by no point, so that the point holds as many of them as its search reaches. The point
/// is checked against every part, so that a disjunct is kept by a point and not by trust in
/// the search.
/// The bounds in `implied`, which the formula implies, are added to the parts, so that the
/// search does not choose a value of an atom that no point has.
fn point_with(p: &Parts, held: &[Vec<bool>], d: &Parts, implied: &Near) -> Option<Model> {
    let others = || p.ors.iter().zip(held).filter(|(o, _)| !o.is_empty());
    let mut cons = p.cons.clone();
    implied
        .one
        .keys()
        .for_each(|a| implied.bounds(a, &mut cons));
    let mut q = Parts {
        cons,
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
    /// is read without recursion (COMPLEXITY.md S27). A disjunction that the formula holds as a
    /// conjunct in more than one place, and a disjunct held in more than one place, are made
    /// once and shared, as [`Rc`]s, at each place (COMPLEXITY.md S31).
    // Complexity tradeoff: a part reached twice in the formula is made once, but the skip of
    // one already conjoined above reaches only the places below the place that conjoined it.
    // A shared conjunction or disjunction used as a conjunct at places on separate branches
    // (disjuncts beside each other, not nested) is read at each: a conjunction's k constraints
    // are added to the base of each place, and a disjunction's list of k disjuncts is copied
    // into each (`ds.clone()`), where `settle`, `pick` and `witness` read it again. No answer is
    // given up. Trigger: a `let`-bound conjunction or disjunction of k parts used at each of d
    // disjuncts of one disjunction costs O(d k) here: with k = d named credit limits in each of
    // d tiers side by side, `product::arms` allocates 208.8 MB at d = 30 and 10.59 GB at 240,
    // 50.7 times (ST-formula-wide repair 4). Conjoining a part common to every disjunct once,
    // before the disjunction, changes answers, since `project_parts` hulls each disjunction of
    // a part apart from the rest: `rule && (x <= 0 || y <= 0)` projects `x` to `[..]` where
    // `(rule && x <= 0) || (rule && y <= 0)` gives `[..=0, 5..]`. The nested shapes are near linear (`Formula::and` and `Formula::or` keep a named part
    // whole): tests in `l01_39_reduced_product::named_test`
    // `arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // `..._wide_named_disjunction_at_each_tier_...`, `..._wide_named_disjunction_required_at_each_tier_...`
    // and `arms_of_a_chain_of_named_{conjunctions,disjunctions}_take_time_near_linear_in_its_length`,
    // COMPLEXITY.md S31b. A complete solution holds a shared conjunction as a shared chunk of
    // the base and a shared disjunction as one shared list (`Rc<[Rc<Parts>]>`), and lets
    // `settle`, `pick` and `witness` read a chunk or a disjunction they have already met once
    // per model; reading a repeated disjunction once can change which disjuncts `pick` takes,
    // so the models it returns must then be checked against the present ones.
    fn of(f: Formula) -> Parts {
        /// The shared parts known to hold (`yes`) and known not to hold (`no`) where a part is
        /// made: those conjoined on the way down, and the shared disjuncts beside a disjunct.
        #[derive(Clone, Default)]
        struct Assumed {
            yes: imbl::HashSet<Id>,
            no: imbl::HashSet<Id>,
        }
        /// A disjunction being entered: its key when shared, its disjuncts left and those
        /// made, and what is assumed where a disjunct held by it alone is made.
        type Entering = (
            Option<Id>,
            std::vec::IntoIter<Formula>,
            Vec<Rc<Parts>>,
            Assumed,
        );
        /// A part being made: its disjunctions not yet entered, last first, the disjunction
        /// being entered, the part's own key when shared, and what is assumed where it is.
        struct Frame {
            p: Parts,
            todo: Vec<Formula>,
            arms: Option<Entering>,
            id: Option<Id>,
            at: Assumed,
        }
        fn open(
            f: Formula,
            id: Option<Id>,
            mut at: Assumed,
            twice: &std::collections::HashSet<Id>,
        ) -> Frame {
            let mut p = Parts::default();
            let mut todo = Vec::new();
            let mut stack = vec![f];
            while let Some(mut g) = stack.pop() {
                // A shared part already conjoined above holds here; one known not to hold
                // makes the part false.
                if let Some(k) = Id::among(&g, twice) {
                    if at.yes.contains(&k) {
                        continue;
                    }
                    if at.no.contains(&k) {
                        let mut p = Parts::default();
                        p.ors.push(Vec::new());
                        return Frame {
                            p,
                            todo: Vec::new(),
                            arms: None,
                            id,
                            at,
                        };
                    }
                    at.yes.insert(k);
                }
                match &mut g {
                    Formula::Con(c) => p.cons.push(Con::take(c)),
                    // Reversed, so the conjuncts are added in order.
                    Formula::And(_) => {
                        stack.extend(g.into_parts().expect("a conjunction").into_iter().rev())
                    }
                    Formula::Or(_) => todo.push(g),
                    Formula::Not(_) => unreachable!("a formula in negation normal form"),
                }
            }
            todo.reverse();
            Frame {
                p,
                todo,
                arms: None,
                id,
                at,
            }
        }
        // The parts that the formula reaches through more than one parent: only these are made
        // once and assumed by key, so the parts made follow the formula's own sharing, never the
        // handles that hold its parts outside it.
        let twice = Id::reached_twice(&f);
        // The disjunctions and the disjuncts already made that are held in more than one place,
        // each made with nothing assumed, so that it serves at every place.
        let mut ors: HashMap<Id, Vec<Rc<Parts>>> = HashMap::new();
        let mut arms: HashMap<Id, Rc<Parts>> = HashMap::new();
        let mut stack = vec![open(f, None, Assumed::default(), &twice)];
        let mut made: Option<Rc<Parts>> = None;
        while let Some(top) = stack.last_mut() {
            if let (Some(q), Some((_, _, done, _))) = (made.take(), &mut top.arms) {
                // A false disjunct is left out.
                if !q.ors.iter().any(Vec::is_empty) {
                    done.push(q);
                }
            }
            if let Some((_, left, done, at)) = &mut top.arms {
                if let Some(g) = left.next() {
                    match Id::among(&g, &twice) {
                        Some(id) => match arms.get(&id) {
                            Some(q) => {
                                if !q.ors.iter().any(Vec::is_empty) {
                                    done.push(Rc::clone(q))
                                }
                            }
                            None => stack.push(open(g, Some(id), Assumed::default(), &twice)),
                        },
                        None => {
                            let at = at.clone();
                            stack.push(open(g, None, at, &twice))
                        }
                    }
                    continue;
                }
                let (id, _, done, _) = top.arms.take().expect("the disjunction entered");
                if let Some(id) = id {
                    ors.insert(id, done.clone());
                }
                top.p.ors.push(done);
            }
            if let Some(g) = top.todo.pop() {
                let id = Id::among(&g, &twice);
                if let Some(ds) = id.as_ref().and_then(|id| ors.get(id)) {
                    top.p.ors.push(ds.clone());
                    continue;
                }
                // A shared disjunction is made with nothing assumed. Each of its disjuncts
                // held by it alone is made with its shared disjuncts assumed not to hold, since
                // it serves only where they do not; a shared disjunct known to hold makes the
                // disjunction hold, and one known not to hold, or met twice, is left out.
                let mut at = match id {
                    Some(_) => Assumed::default(),
                    None => top.at.clone(),
                };
                let mut keep = Vec::new();
                let mut holds = false;
                for d in g.into_parts().expect("a disjunction") {
                    if let Some(k) = Id::among(&d, &twice) {
                        if at.yes.contains(&k) {
                            holds = true;
                            break;
                        }
                        if at.no.insert(k).is_some() {
                            continue;
                        }
                    }
                    keep.push(d);
                }
                if !holds {
                    top.arms = Some((id, keep.into_iter(), Vec::new(), at));
                }
                continue;
            }
            let Frame { p, id, .. } = stack.pop().expect("the top frame");
            if stack.is_empty() {
                return p;
            }
            let q = Rc::new(p);
            if let Some(id) = id {
                arms.insert(id, Rc::clone(&q));
            }
            made = Some(q);
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
/// does not depend on the order they are written in. The sort compares names, so its order
/// reaches an answer only through the names [`Renamed`] gives by color, or not at all: a
/// formula whose atoms share a color is settled, tested and projected by questions whose
/// answers no order of the parts changes ([`settle_as_sets`], [`alone`], [`by_color`],
/// [`project_parts`] with `sets`), and refused when a search would be needed.
fn nnf(f: &Formula, sign: bool) -> Formula {
    f.fold(
        sign,
        |g, s| s != matches!(g, Formula::Not(_)),
        |g, sign, mut parts| {
            let mut out = match (g, sign) {
                (Formula::Not(_), _) => parts.pop().expect("one part"),
                (Formula::And(_), true) | (Formula::Or(_), false) => {
                    Formula::and_keeping(parts, |i| g.kept(i))
                }
                (Formula::And(_), false) | (Formula::Or(_), true) => {
                    Formula::or_keeping(parts, |i| g.kept(i))
                }
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
            // A node held elsewhere is a part passed through whole, already sorted.
            if let Formula::And(gs) | Formula::Or(gs) = &mut out
                && let Some(gs) = Arc::get_mut(gs)
            {
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
///
/// A disjunct is kept when its constraints hold at a point of the base or when its own atoms
/// re-solved with the base's other atoms held at that point have a point ([`local_repair`]);
/// it is removed when its constraints with its atoms' bounds and the base's constraints over
/// its atoms alone have none ([`local_refute`]); only when all of these fail are the base
/// groups it touches solved with it. Each answer is exact. The base grows within a round as
/// disjunctions left with one disjunct join it, and on a nest those groups are one chain as
/// long as the nest: solving it for each disjunct cost the disjuncts times the chain (chain
/// family `cross_live` at `k = 256`: 1022 solves of 261 constraints in one call). The local
/// tests cost the constraints that link the disjunct's atoms to others and their bounds, so
/// the point is kept a point of the base as it grows, repaired the same way when a disjunct
/// that joins it does not hold there (COMPLEXITY S22, tests
/// `l01_25_preimage_catalog::s22::chain_cross_live_scales` and
/// `chain_cross_within_its_width_scales`).
fn settle(mut p: Parts) -> Result<Option<Parts>, Refusal> {
    // The base, with a bound written again (at each level of a nest, say) kept once
    // ([`Linked::meet`]), so that the groups a disjunct is tested with do not grow with the
    // depth, and indexed for [`local_repair`].
    let mut base = Linked::default();
    let mut near = Near::default();
    take(&std::mem::take(&mut p.cons), &mut base, &mut near);
    loop {
        // A point of the base serves only to keep, unasked, the disjuncts that meet the base,
        // so none is built when no disjunction is left.
        let Some(model) = solve(&base.cons, !p.ors.is_empty())? else {
            return Ok(None);
        };
        if p.ors.is_empty() {
            p.cons = base.cons;
            return Ok(Some(p));
        }
        // A point of the base as it is now, or `None` once the solver refuses to find one, after
        // which each disjunct is solved with its groups.
        let mut point = Some(model);
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
                    if let Some(pt) = &point
                        && (d.cons.iter().all(|c| c.holds(pt))
                            || local_repair(&base.cons, &near, pt, &d.cons).is_some())
                    {
                        return true;
                    }
                    if local_refute(&base.cons, &near, &d.cons) {
                        return false;
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
                    let repaired = match &point {
                        Some(pt) if d.cons.iter().all(|c| c.holds(pt)) => None,
                        Some(pt) => Some(local_repair(&base.cons, &near, pt, &d.cons)),
                        None => None,
                    };
                    take(&d.cons, &mut base, &mut near);
                    match (repaired, &mut point) {
                        (Some(Some(m)), Some(pt)) => pt.extend(m),
                        // No point of the base near the old one: one of the whole base, or
                        // none, in which case the formula has none either.
                        (Some(None), _) => match solve(&base.cons, true) {
                            Ok(Some(m)) => point = Some(m),
                            Ok(None) => return Ok(None),
                            Err(_) => point = None,
                        },
                        _ => {}
                    }
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
///
/// No step of the solver chooses by the names of the variables or by the order of the rows:
/// each choice goes by what the structure of the rows gives (the colors of [`canonical`], the
/// fill of an elimination, the coefficients), and where that leaves two candidates that share
/// a row, the solver refuses with [`Refusal::Tie`] instead of choosing; candidates that share
/// no row are taken together, which no order can change. So the answer, refusals included, is
/// the same under every naming of the variables and every order of the constraints.
fn solve<C: std::borrow::Borrow<Con>>(cons: &[C], want: bool) -> Result<Option<Model>, Refusal> {
    let cons: Vec<&Con> = cons.iter().map(|c| c.borrow()).collect();
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let Canonical {
        atoms,
        rows,
        keys,
        row_keys,
    } = canonical(atoms, &cons);
    let index: BTreeMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    // In the order of `canonical`, so that neither the order of the constraints nor the names of
    // the variables decide the order of the work, except among variables that refinement cannot
    // tell apart, where no choice is made by that order.
    let sorted: Vec<&Con> = rows.into_iter().map(|r| cons[r]).collect();
    // Each equality `x - y == d` ties `x` to `y`: every row is written over one variable of
    // each tied class, the others being offsets from it, so no row is rewritten for them.
    let mut ties = Ties::new(atoms.len());
    for c in &sorted {
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
    let at = ties.representatives(&keys);
    let mut base: Vec<(Row, Rel)> = Vec::with_capacity(sorted.len());
    for c in sorted {
        let mut sum: BTreeMap<usize, Int> = BTreeMap::new();
        let mut k = c.lin.constant.clone();
        for (a, coef) in &c.lin.terms {
            let (r, d) = &at[index[a]];
            k = &k + &(coef * d);
            let at = sum.entry(*r).or_insert(Int::ZERO);
            *at = &*at + coef;
        }
        let a = sum.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        base.push((Row { a, k }, c.rel));
    }
    let name = |i: usize| atoms[i].to_string();
    let Some(vals) = quotient(atoms.len(), base, &keys, &row_keys, want, &name)? else {
        return Ok(None);
    };
    if !want {
        return Ok(Some(Model::new()));
    }
    let mut model: Model = atoms.iter().cloned().zip(vals).collect();
    for (i, a) in atoms.iter().enumerate() {
        let (r, d) = &at[i];
        if *r != i {
            let v = &model[&atoms[*r]] + d;
            model.insert(a.clone(), v);
        }
    }
    Ok(Some(model))
}

/// A choice among candidates that share a row and that nothing but their names or places
/// tells apart, as variables by place and rows: the cause of a [`Refusal::Tie`] before its
/// variables are named.
struct Tied {
    vars: Vec<usize>,
    rows: Vec<(Row, Rel)>,
}

impl Tied {
    /// The refusal, with the variables by place below `vars` named by `name` and those made
    /// up after them `t1`, `t2` and so on.
    fn written(&self, vars: usize, name: &dyn Fn(usize) -> String) -> Refusal {
        let label = |j: usize| {
            if j < vars {
                name(j)
            } else {
                format!("t{}", j - vars + 1)
            }
        };
        Refusal::Tie(Arc::new(Tie {
            vars: self.vars.iter().map(|&j| label(j)).collect(),
            rows: self
                .rows
                .iter()
                .map(|(r, rel)| {
                    let rel = if *rel == Rel::Eq { "==" } else { ">=" };
                    format!(
                        "{} {rel} 0",
                        sum_of(r.a.iter().map(|(j, c)| (label(*j), c)), &r.k)
                    )
                })
                .collect(),
        }))
    }
}

/// `Σ c·x + k`, written as [`Lin`] writes a term.
fn sum_of<'a>(terms: impl Iterator<Item = (String, &'a Int)>, k: &Int) -> String {
    let mut out = String::new();
    for (x, c) in terms {
        let m = c.abs();
        match (out.is_empty(), c.is_negative()) {
            (true, true) => out.push('-'),
            (true, false) => {}
            (false, true) => out.push_str(" - "),
            (false, false) => out.push_str(" + "),
        }
        if m == Int::ONE {
            out.push_str(&x);
        } else {
            out.push_str(&format!("{m} * {x}"));
        }
    }
    if out.is_empty() {
        out = k.to_string();
    } else if k.is_positive() {
        out.push_str(&format!(" + {k}"));
    } else if k.is_negative() {
        out.push_str(&format!(" - {}", k.abs()));
    }
    out
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
///
/// The first entry of a column is first in the order of the rows, which names can decide, so
/// the sign of `y`, which the later steps can see, is set otherwise: `p` is turned so that the
/// members of least color (`keys`) enter with multiples above zero; where those members enter
/// with both signs, so that the sorted pairs of row color (`row_keys`) and entry are the
/// lesser of `p` and `-p`; and where `p` and `-p` give the same pairs, the group is not
/// merged. `y` takes the least color of its members.
fn quotient(
    vars: usize,
    base: Vec<(Row, Rel)>,
    keys: &[usize],
    row_keys: &[usize],
    want: bool,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
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
        return parts(vars, base, keys, want, name);
    }
    // The sign of each group's variable (true where it is `-p`), and its color. A group whose
    // sign nothing but names would choose is not merged: each member stays a variable of its
    // own, with its own column and color, which keeps the points as they are; whether a group
    // is merged depends on its columns and colors only, so no naming changes it.
    let content = |j: usize| &split[j].as_ref().expect("a column").0;
    let mut turned: Vec<(bool, usize)> = Vec::with_capacity(groups.len());
    let mut kept: Vec<(usize, Merged)> = Vec::with_capacity(groups.len());
    for (first, m) in groups {
        let (_, prim) = split[first].as_ref().expect("a group's first column");
        let least = m
            .links
            .iter()
            .map(|(j, _, _)| keys[*j])
            .min()
            .expect("a group has a member");
        let signs: BTreeSet<bool> = m
            .links
            .iter()
            .filter(|(j, _, _)| keys[*j] == least)
            .map(|(j, _, _)| content(*j).is_negative())
            .collect();
        let flip = match signs.len() {
            1 => Some(signs.contains(&true)),
            _ => {
                let pairs = |sign: &Int| {
                    let mut v: Vec<(usize, Int)> =
                        prim.iter().map(|(i, p)| (row_keys[*i], p * sign)).collect();
                    v.sort();
                    v
                };
                match pairs(&Int::ONE).cmp(&pairs(&-&Int::ONE)) {
                    Ordering::Less => Some(false),
                    Ordering::Greater => Some(true),
                    Ordering::Equal => None,
                }
            }
        };
        match flip {
            Some(flip) => {
                turned.push((flip, least));
                kept.push((first, m));
            }
            None => {
                for (j, _, _) in m.links {
                    turned.push((false, keys[j]));
                    let gcd = content(j).clone();
                    let links = vec![(j, Int::ZERO, Int::ONE)];
                    kept.push((j, Merged { gcd, links }));
                }
            }
        }
    }
    let groups = kept;
    let mut rows: Vec<Vec<Term>> = vec![Vec::new(); base.len()];
    for (id, (first, m)) in groups.iter().enumerate() {
        let (_, prim) = split[*first].as_ref().expect("a group's first column");
        let g = if turned[id].0 { -&m.gcd } else { m.gcd.clone() };
        for (i, p) in prim {
            rows[*i].push((id, p * &g));
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
    let group_keys: Vec<usize> = turned.iter().map(|t| t.1).collect();
    // A group's variable is the sum of its members, each times its multiple over the divisor.
    let group_name = |id: usize| {
        let (m, flip) = (&groups[id].1, turned[id].0);
        let terms: Vec<(String, Int)> = m
            .links
            .iter()
            .map(|(j, _, _)| {
                let c = content(*j).div_floor(&m.gcd);
                (name(*j), if flip { -&c } else { c })
            })
            .collect();
        sum_of(terms.iter().map(|(x, c)| (x.clone(), c)), &Int::ZERO)
    };
    let Some(y) = parts(groups.len(), reduced, &group_keys, want, &group_name)? else {
        return Ok(None);
    };
    if !want {
        return Ok(Some(Vec::new()));
    }
    let mut x = vec![Int::ZERO; vars];
    for (((_, m), value), (flip, _)) in groups.iter().zip(y).zip(&turned) {
        let mut carry = if *flip { -&value } else { value };
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
/// two variables is decided exactly, however many such parts there are. Each part's
/// variables keep their colors, `keys`.
fn parts(
    vars: usize,
    base: Vec<(Row, Rel)>,
    keys: &[usize],
    want: bool,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
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
        let part_keys: Vec<usize> = vs.iter().map(|&v| keys[v]).collect();
        let part_name = |i: usize| name(vs[i]);
        match search(vs.len(), &rows, &part_keys, want, &part_name) {
            Ok(None) => return Ok(None),
            Ok(Some(p)) => points.push((vs, p)),
            Err(r) => refused = Some(least(refused, r)),
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

/// The lesser of a refusal and the one held, if any.
fn least(held: Option<Refusal>, r: Refusal) -> Refusal {
    match held {
        Some(q) if q <= r => q,
        _ => r,
    }
}

/// The Omega test on `base` over `vars` variables of colors `keys`, with the splinters of its
/// dark eliminations: by Pugh's lemma [Omega, sec. 2.3] the problem has an integer point
/// exactly when its dark shadow has one or one of the splinters of a dark elimination has one.
/// The splinters are searched only when the dark shadows have no point, each once, without
/// splinters of their own. Pugh's lemma holds for either side of an elimination (for the
/// upper bounds, it is the lemma for `-x`), so the splinters taken are those of the side with
/// fewer bounds, and of both sides when they have as many, since which side is the lower one
/// can turn on the sign `quotient` gave a merged variable. The splinters are searched a batch
/// of dark eliminations at a time, in the order of the batches, and every splinter of a batch
/// is searched, so the answer does not depend on the order of the variables within a batch:
/// a point of a splinter is the answer; otherwise the first batch with a dark elimination
/// none of whose sides has only empty splinters gives the least refusal met in that batch;
/// otherwise the problem is empty. A refused dark
/// shadow is the answer likewise: the splinters hold only the points it misses, so they could
/// turn the refusal into a point but never into an empty answer.
fn search(
    vars: usize,
    base: &[(Row, Rel)],
    keys: &[usize],
    want: bool,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
    let mut top = Omega::new(keys, base, want, true);
    match top.run() {
        Leaf::Point(v) => return Ok(Some(v)),
        Leaf::Empty => {}
        Leaf::Refused(r) => return Err(r),
        Leaf::Tied(t) => return Err(t.written(vars, name)),
    }
    for batch in &top.gray {
        let mut refused: Option<Refusal> = None;
        for &(at, n) in batch {
            let Step::Chosen(j, rows) = &top.steps[at] else {
                unreachable!("a dark elimination is a chosen step")
            };
            let (lowers, uppers): (Vec<&Row>, Vec<&Row>) =
                rows.iter().partition(|r| r.at(*j).is_positive());
            // The splinters of the side with fewer rows, each bound measured against the
            // largest coefficient of the other side; both sides when they have as many rows.
            let sides: Vec<(&[&Row], &[&Row])> = match uppers.len().cmp(&lowers.len()) {
                Ordering::Less => vec![(&uppers, &lowers)],
                Ordering::Greater => vec![(&lowers, &uppers)],
                Ordering::Equal => vec![(&lowers, &uppers), (&uppers, &lowers)],
            };
            let mut covered = false;
            let mut why: Option<Refusal> = None;
            for (side, other) in sides {
                let m = other
                    .iter()
                    .map(|r| r.at(*j).abs())
                    .max()
                    .expect("an inexact elimination has both bounds");
                let mut open: Option<Refusal> = None;
                for bound in side {
                    let Some(mut child) = top.splinter(base, at, n, bound, *j, &m) else {
                        continue;
                    };
                    let mut leaf = child.run();
                    if matches!(leaf, Leaf::Empty) && child.gap {
                        // Run again with each gray shadow over three variables decided by
                        // `live3`, which leaves a gap only where four variables or more are left.
                        let Some(again) = top.splinter(base, at, n, bound, *j, &m) else {
                            unreachable!("a splinter built once is built again");
                        };
                        child = again;
                        child.exact3 = true;
                        leaf = child.run();
                    }
                    match leaf {
                        Leaf::Point(v) => return Ok(Some(v)),
                        Leaf::Empty if !child.gap => {}
                        // Complexity tradeoff: a splinter whose own elimination leaves a gray
                        // shadow (a splinter of a splinter) over four variables or more is not
                        // searched; the question gets `Refusal::Shadows` ("not decided") even
                        // when a point lies there. With three variables left, the run again
                        // above decides the gray shadow by `live3`. Why: each level of
                        // splinters multiplies the searches by the bounds of one side and their
                        // coefficients, so nested splinters cost time exponential in the
                        // variables. Trigger: an inexact elimination inside a splinter with four
                        // variables or more live, which needs coefficients other than ±1 on
                        // both sides of a variable at two levels. Tests:
                        // `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`,
                        // `l01_38_presburger::checker::a_question_whose_point_lies_past_one_splinter_is_rejected`,
                        // `l01_38_presburger::scaling::pughs_example_in_a_chain_scales`.
                        // COMPLEXITY.md row S18. A complete solution would recurse into nested
                        // splinters as Pugh's Omega test does, at a cost exponential in the
                        // depth of the nesting.
                        Leaf::Empty => open = Some(least(open, Refusal::Shadows)),
                        Leaf::Refused(r) => open = Some(least(open, r)),
                        Leaf::Tied(t) => open = Some(least(open, t.written(vars, name))),
                    }
                }
                match open {
                    None => covered = true,
                    Some(r) => why = Some(least(why, r)),
                }
            }
            if !covered && let Some(r) = why {
                refused = Some(least(refused, r));
            }
        }
        // Complexity tradeoff: the search ends at the first batch of dark eliminations with a
        // refusal, and the splinters of later batches, which could hold a point, are not
        // searched; the question gets the refusal. Why: searching every splinter costs a run of
        // the Omega test for each, which along a chain of dark eliminations is quadratic in the
        // variables; ending at the first refusal, as the search did before, keeps it linear
        // when that refusal comes early. The batches are given by the structure, and so is
        // their order, so ending after a whole batch keeps the answer the same under every
        // naming, which ending inside one would not. Trigger: a dark elimination whose
        // splinters are refused, before one whose splinters hold a point. Tests:
        // `l01_38_presburger::scaling::pughs_example_in_a_chain_scales`,
        // `l01_38_presburger::names::the_splinters_are_searched_a_batch_at_a_time`.
        // COMPLEXITY.md row NAME-ties.
        if let Some(r) = refused {
            return Err(r);
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

    /// Adds `x[x] - x[y] == d`; false when the ties already make it something else. Which of
    /// two roots of equal rank goes under the other follows the order of the arguments, so it
    /// is not used beyond this forest: [`Ties::representatives`] chooses the variable that
    /// stands for each class.
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

    /// For each variable, the member of its class that stands for the class, and `d` with the
    /// variable equal to that member plus `d`: the member of least color (`keys`), then of least
    /// offset, then of least place. Colors, and the differences between the offsets of a
    /// class, depend on the rows alone, not on the order in which [`Ties::equate`] joined the
    /// class; two members of one color and one offset are equal at every point and alike in
    /// the rows, so taking one or the other only renames the variable that stands for the
    /// class. O(n log n) for n variables.
    fn representatives(&self, keys: &[usize]) -> Vec<(usize, Int)> {
        let roots: Vec<(usize, Int)> = (0..self.parent.len()).map(|i| self.root(i)).collect();
        let mut best: Vec<Option<(usize, &Int, usize)>> = vec![None; roots.len()];
        for (i, (r, d)) in roots.iter().enumerate() {
            let candidate = (keys[i], d, i);
            if best[*r].is_none_or(|b| candidate < b) {
                best[*r] = Some(candidate);
            }
        }
        roots
            .iter()
            .map(|(r, d)| {
                let (_, e, rep) = best[*r].expect("each root has a member");
                (rep, d - e)
            })
            .collect()
    }
}

/// `atoms`, in name order, put in the order the solver takes them; the places in `cons` of the
/// rows in the order it takes them; and the color of each atom of that order in the coarsest
/// stable coloring of the system ([`stable_colors`]). Both orders are breadth first over the
/// rows, so that variables that share a row stand near each other, and so do rows that share a
/// variable:
/// from the variable of least color not yet placed, each placed variable's rows not yet taken
/// are taken in the order of their colors, and each row's variables not yet placed in the
/// order of theirs. Rows with no variable come last, by color. Names, and the order of
/// `cons`, break ties between equal colors only; when every variable's color is distinct, two
/// rows of one color are equal, so the orders depend on the structure alone. O(n + m + t log t)
/// for n variables, m rows and t terms, with the sorts of each row's terms and each variable's
/// rows. The colors of the rows, in the order taken, come with them.
fn canonical(atoms: Vec<Atom>, cons: &[&Con]) -> Canonical {
    let n = atoms.len();
    let color = stable_colors(&atoms, cons);
    let by_color = |v: &usize| (color[*v], *v);
    let mut rows_of: Vec<Vec<usize>> = vec![Vec::new(); n];
    let vars_of: Vec<Vec<usize>> = cons
        .iter()
        .enumerate()
        .map(|(r, c)| {
            let mut xs: Vec<usize> = c
                .lin
                .terms
                .keys()
                .map(|a| atoms.binary_search(a).expect("an atom of the system"))
                .collect();
            for &x in &xs {
                rows_of[x].push(n + r);
            }
            xs.sort_by_key(by_color);
            xs
        })
        .collect();
    for rs in &mut rows_of {
        rs.sort_by_key(by_color);
    }
    let mut seeds: Vec<usize> = (0..n).collect();
    seeds.sort_by_key(by_color);
    let mut placed = vec![false; n];
    let mut taken = vec![false; cons.len()];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    let mut rows: Vec<usize> = Vec::with_capacity(cons.len());
    for s in seeds {
        if placed[s] {
            continue;
        }
        placed[s] = true;
        order.push(s);
        let mut head = order.len() - 1;
        while head < order.len() {
            for &r in &rows_of[order[head]] {
                if taken[r - n] {
                    continue;
                }
                taken[r - n] = true;
                rows.push(r - n);
                for &x in &vars_of[r - n] {
                    if !placed[x] {
                        placed[x] = true;
                        order.push(x);
                    }
                }
            }
            head += 1;
        }
    }
    let mut bare: Vec<usize> = (0..cons.len()).filter(|&r| !taken[r]).collect();
    bare.sort_by_key(|&r| (color[n + r], r));
    rows.extend(bare);
    let keys = order.iter().map(|&x| color[x]).collect();
    let row_keys = rows.iter().map(|&r| color[n + r]).collect();
    let mut atoms: Vec<Option<Atom>> = atoms.into_iter().map(Some).collect();
    let order = order
        .into_iter()
        .map(|x| atoms[x].take().expect("each variable placed once"))
        .collect();
    Canonical {
        atoms: order,
        rows,
        keys,
        row_keys,
    }
}

/// What [`canonical`] gives: the atoms in the order taken, the places of the rows in the order
/// taken, and the color of each atom and of each row in those orders.
struct Canonical {
    atoms: Vec<Atom>,
    rows: Vec<usize>,
    keys: Vec<usize>,
    row_keys: Vec<usize>,
}

/// The variables of the conjunction `cons` in the order the solver takes them, and their
/// colors, by which it orders them: two variables have one color exactly when the structure
/// of the rows does not tell them apart, and the numbers depend on that structure only, not on
/// the names.
pub fn colors(cons: &[Con]) -> (Vec<Atom>, BTreeMap<Atom, u64>) {
    let cons: Vec<&Con> = cons.iter().collect();
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let Canonical {
        atoms: order,
        keys: colors,
        ..
    } = canonical(atoms, &cons);
    let colors = order
        .iter()
        .zip(colors)
        .map(|(a, k)| (a.clone(), k as u64))
        .collect();
    (order, colors)
}

/// The color of each of `atoms` (sorted, each in some row of `cons`), then of each row of
/// `cons`, in the coarsest stable coloring of the system's graph. The graph has a vertex for
/// each variable, each row and each term of a row, a term joined to its row and to its
/// variable. A row starts colored by its relation and constant, a term by its coefficient, and
/// every variable alike. A coloring is
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
/// new class is not pushed unless the old one was waiting (Hopcroft's rule, "process the smaller
/// half"), so a vertex is in O(log N) refining classes in all. The coarsest stable coloring is
/// Cardon and Crochemore's "coarsest regular congruence", an equivalence in which any two equal
/// vertices have the same number of successors by each type of arc in each class ("Partitioning
/// a graph in O(|A| log2 |V|)", Theoret. Comput. Sci. 19, 1982, 85-98), and Paige and Tarjan's
/// coarsest size-stable refinement, which they compute by queueing every new block but the
/// largest, in O(m log n) time because a vertex lies in at most log2 n + 1 of the blocks taken
/// from the queue ("Three partition refinement algorithms", SIAM J. Comput. 16(6), 1987,
/// 973-989, end of section 3). New colors are numbered in the increasing order of
/// (old color, number of neighbors), never by a hash, so equal colors mean equal structure and
/// the numbers depend on the structure alone, not on the names or the order of the rows.
/// O((n + m + t) log(n + m + t)) for n variables, m rows and t terms, with the sorts of the
/// starting colors.
fn stable_colors(atoms: &[Atom], cons: &[&Con]) -> Vec<usize> {
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
    refine.color.truncate(n + m);
    refine.color
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

/// The symmetric remainder of `a` by `m`, of either sign, odd in `a`: at exactly half of `m`
/// it takes the sign opposite to `a`, so that `mod_hat(-a, m) == -mod_hat(a, m)` and an
/// equality solved with its sign turned gives the same definition.
fn mod_hat(a: &Int, m: &Int) -> Int {
    let m = m.abs();
    let r = a.mod_floor(&m);
    match (&r + &r).cmp(&m) {
        Ordering::Less => r,
        Ordering::Greater => &r - &m,
        Ordering::Equal if a.is_negative() => r,
        Ordering::Equal => &r - &m,
    }
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

    /// Where the variable `x[j]`, of color `key`, stands among those to eliminate.
    fn rank(&self, key: usize, j: usize) -> Rank {
        (self.fill(), key, j)
    }
}

/// The fill of a variable's elimination, its color, and the variable. The step takes the
/// least fill and color; the place only orders variables that tie in both, among which no
/// choice is made by it (see [`System::least`]).
type Rank = (isize, usize, usize);

/// A row of a [`System`]: its constant, and its place in the system's list.
struct Held {
    k: Int,
    id: usize,
}

/// A variable of a [`System`]: its rows, by place, how it occurs in them, and its color.
#[derive(Default)]
struct Var {
    rows: BTreeSet<usize>,
    sides: Sides,
    key: usize,
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
    /// The lesser coefficients of the equalities kept as pairs of opposite rows, which are
    /// not met again.
    loose: BTreeSet<Coefs>,
    /// Whether a row is false, or two opposite rows meet nowhere.
    empty: bool,
    /// The variables some row holds.
    live: usize,
    /// The rows not of the form `±x ± y + k >= 0` or `±x + k >= 0`.
    wide_rows: usize,
}

impl System {
    /// An empty system over variables of the colors `keys`.
    fn new(keys: impl Iterator<Item = usize>) -> System {
        System {
            rows: BTreeMap::new(),
            ids: Vec::new(),
            vars: keys
                .map(|key| Var {
                    key,
                    ..Var::default()
                })
                .collect(),
            exact: BTreeSet::new(),
            inexact: BTreeSet::new(),
            one_sided: BTreeSet::new(),
            fixable: BTreeSet::new(),
            meets: BTreeSet::new(),
            loose: BTreeSet::new(),
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
                if !self.loose.contains(&lesser) {
                    self.meets.insert(lesser);
                }
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
            let key = v.key;
            set.remove(&v.sides.rank(key, *i));
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
            set.insert(s.rank(key, *i));
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

    /// The rows of opposite pairs that meet in an equality, one of each pair, all removed. Two
    /// pairs share no row, since a row has one opposite, so taking them all at once leaves the
    /// same system in whatever order they are taken.
    fn meetings(&mut self) -> Vec<Row> {
        let mut out = Vec::new();
        for a in std::mem::take(&mut self.meets) {
            let opp = opposite(&a);
            if let (Some(r), Some(o)) = (self.rows.get(&a), self.rows.get(opp.as_slice()))
                && (&r.k + &o.k).is_zero()
            {
                let (r, o) = (r.id, o.id);
                self.remove(o);
                out.push(self.remove(r));
            }
        }
        out
    }

    /// The variables of least fill and color among the ranks of `sets`, with that fill: all
    /// of them when no two share a row, and otherwise the tie, with the rows they share.
    ///
    /// Variables that share no row are eliminated together, and the order among them does
    /// not change the result: eliminating `x[i]` removes the rows of `x[i]` and adds rows over
    /// their other variables, none of which is `x[j]`, since no row holds both, so the rows of
    /// `x[j]`, and with them its elimination, are the same before and after; and adding a row
    /// keeps the least constant of each set of coefficients, which no order changes.
    fn least(&self, sets: &[&BTreeSet<Rank>]) -> Option<(isize, Result<Vec<usize>, Tied>)> {
        let &(fill, key, _) = sets.iter().filter_map(|s| s.first()).min()?;
        let js: Vec<usize> = sets
            .iter()
            .flat_map(|s| s.range((fill, key, 0)..=(fill, key, usize::MAX)))
            .map(|r| r.2)
            .collect();
        let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
        for j in &js {
            for id in &self.vars[*j].rows {
                *seen.entry(*id).or_insert(0) += 1;
            }
        }
        let shared: Vec<(Row, Rel)> = seen
            .into_iter()
            .filter(|(_, n)| *n > 1)
            .map(|(id, _)| {
                let a = self.ids[id].clone().expect("a row held");
                let k = self.rows[&a].k.clone();
                (Row { a, k }, Rel::Ge)
            })
            .collect();
        if shared.is_empty() {
            Some((fill, Ok(js)))
        } else {
            Some((
                fill,
                Err(Tied {
                    vars: js,
                    rows: shared,
                }),
            ))
        }
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
/// [`box_empty`] on what is left. The shadows are taken as [`System::least`] gives them: all
/// the variables of least fill and color together, and where two of those share a row, none,
/// the box test then deciding, so no step turns on the names of the variables.
fn relaxed_empty(gs: &System) -> bool {
    let mut sys = System::new(gs.vars.iter().map(|v| v.key));
    for (a, r) in &gs.rows {
        sys.add(Row {
            a: a.clone(),
            k: r.k.clone(),
        });
    }
    while !sys.empty {
        let Some((fill, js)) = sys.least(&[&sys.exact, &sys.inexact]) else {
            return false;
        };
        let (true, Ok(js)) = (fill <= 0, js) else {
            return box_empty(&sys);
        };
        for j in js {
            sys.eliminate(j, false);
        }
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

/// Whether the wide rows `Σ a[i]·x[i] + k >= 0` have no rational point in the box `lo`, `hi`,
/// by one of two tests on each row ([`row_box_empty`]): the row is below zero at every point of
/// the box, or it bounds a variable on one side by a rational past the bound another row gives
/// it on the other. Each variable keeps the greatest lower and the least upper bound the rows
/// have given it so far, so a pair of crossing bounds is found when the later of its two rows
/// is read, whatever the order of the rows. One pass over the terms. Every point of the rows
/// lies in the box, so either test shows them empty.
fn box_empty_in(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> bool {
    // The box's own bounds have no place here: a row that bounds a variable past one of them
    // is below zero at every point of the box, which the first test finds.
    let mut least: Vec<Option<Q>> = vec![None; lo.len()];
    let mut most: Vec<Option<Q>> = vec![None; hi.len()];
    sys.rows
        .iter()
        .filter(|(a, _)| a.len() > 1)
        .any(|(a, held)| row_box_empty(a, &held.k, lo, hi, &mut least, &mut most))
}

/// Whether the row `Σ a[i]·x[i] + k >= 0` shows the rows empty in the box `lo`, `hi`, given the
/// greatest lower bounds `least` and the least upper bounds `most` that the rows read before it
/// gave each variable, which it then updates with its own. Its largest value in the box, `k`
/// plus each `a[i]` times the upper bound of `x[i]` when `a[i]` is above zero and the lower one
/// when below, is negative; or, with each other term at its largest value `rest`, the row
/// leaves `a[i]·x[i] >= -rest`, a rational bound on `x[i]` that crosses the other side's bound.
/// `rest` is known when at most `x[i]` itself lacks the bound the row needs. No bound is
/// rounded, so what is shown empty has no rational point in the box. Two passes over the
/// row's terms.
fn row_box_empty(
    a: &[Term],
    k: &Int,
    lo: &[Option<Int>],
    hi: &[Option<Int>],
    least: &mut [Option<Q>],
    most: &mut [Option<Q>],
) -> bool {
    // The largest value of `c·x[i]` in the box.
    let top = |i: usize, c: &Int| {
        if c.is_positive() { &hi[i] } else { &lo[i] }
            .as_ref()
            .map(|b| c * b)
    };
    let mut sum = k.clone();
    let mut open: Option<usize> = None;
    for (i, c) in a {
        match top(*i, c) {
            Some(m) => sum = &sum + &m,
            None if open.is_none() => open = Some(*i),
            // Two variables lack the bound the row needs: it bounds none of them.
            None => return false,
        }
    }
    if open.is_none() && sum.is_negative() {
        return true;
    }
    for (i, c) in a {
        let rest = match (open, top(*i, c)) {
            (None, Some(m)) => &sum - &m,
            (Some(o), None) if o == *i => sum.clone(),
            _ => continue,
        };
        if c.is_positive() {
            // `c·x[i] >= -rest`: a lower bound.
            let b = Q::new(-&rest, c.clone());
            if most[*i].as_ref().is_some_and(|h| *h < b) {
                return true;
            }
            if least[*i].as_ref().is_none_or(|l| *l < b) {
                least[*i] = Some(b);
            }
        } else {
            // `-c·x[i] <= rest`: an upper bound.
            let b = Q::new(rest, -c);
            if least[*i].as_ref().is_some_and(|l| b < *l) {
                return true;
            }
            if most[*i].as_ref().is_none_or(|h| b < *h) {
                most[*i] = Some(b);
            }
        }
    }
    false
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
/// An equality as its structure gives it: the colors of its variables with their
/// coefficients, sorted, and its constant, taken for the row or its negation, whichever is
/// less, so that neither the names of the variables nor the sign the row was written with
/// changes it.
type Shape = (Vec<(usize, Int)>, Int);

/// The order in which equalities are solved: first those written by the latest batch of steps,
/// so that the work stays with the equalities the last step changed, as a stack of equalities
/// does; then the fewest variables; then the number of equalities that hold the variable the
/// step would define (its degree, the least over a tie), so that a step writes its definition
/// into as few other equalities as it can; then the [`Shape`]. Each part is given by the
/// structure and by the steps before, none by a name. Along a chain of equalities this goes
/// from one equality to the next and keeps each as short as it was; an order that jumps
/// fills the rows in, and their coefficients grow.
type EqKey = (std::cmp::Reverse<u64>, usize, usize, Shape);

/// The [`Shape`] of the row `r` over the variables of `sys`.
fn shape(r: &Row, sys: &System) -> Shape {
    let side = |f: &Int| -> Shape {
        let mut a: Vec<(usize, Int)> = r.a.iter().map(|(i, c)| (sys.vars[*i].key, c * f)).collect();
        a.sort_unstable();
        (a, &r.k * f)
    };
    side(&Int::ONE).min(side(&-&Int::ONE))
}

/// The variables a step on the equality `e` would choose to define, as `Omega::equality`
/// chooses: those with a unit coefficient when there are any, otherwise those of least
/// coefficient, and of these those of least color. More than one is a tie.
fn pivots(e: &Row, sys: &System) -> Vec<usize> {
    let key = |i: usize| sys.vars[i].key;
    let units = e.a.iter().any(|(_, c)| c.is_unit());
    let pool: Vec<(Int, usize, usize)> =
        e.a.iter()
            .filter(|(_, c)| !units || c.is_unit())
            .map(|(i, c)| (c.abs(), key(*i), *i))
            .collect();
    let (m, k, _) = pool.iter().min().expect("a row has a variable").clone();
    pool.into_iter()
        .filter(|(c, kk, _)| *c == m && *kk == k)
        .map(|p| p.2)
        .collect()
}

/// The row or its negation, whichever is less, as its coefficients and its constant: two
/// equalities with the same one are the same equality.
fn unsigned(r: &Row) -> (Vec<Term>, Int) {
    let neg = opposite(&r.a);
    if *r.a <= *neg {
        (r.a.to_vec(), r.k.clone())
    } else {
        (neg, -&r.k)
    }
}

/// An equality held: its row, its key, and the variables a step on it would define.
struct Kept {
    row: Row,
    key: EqKey,
    pivots: Vec<usize>,
}

/// The equalities, by slot, a slot emptied when its row holds everywhere or another slot
/// holds the same equality, with the slots of each variable, the slots whose step would define
/// each variable, and the slots in use in the order of their [`EqKey`]s.
struct Equalities {
    rows: Vec<Option<Kept>>,
    of: Vec<BTreeSet<usize>>,
    pivot_of: Vec<BTreeSet<usize>>,
    order: BTreeSet<(EqKey, usize)>,
    /// The slot of each equality held, by [`unsigned`].
    held: BTreeMap<(Vec<Term>, Int), usize>,
    /// The number of batches of steps begun so far: an equality written by a later one is solved
    /// first.
    now: u64,
}

/// The equalities to solve next, by slot: those of least [`EqKey`] when no two share a variable,
/// otherwise the same slots with the tie.
type EqStep = Result<Vec<usize>, (Vec<usize>, Tied)>;

impl Equalities {
    fn new(vars: usize) -> Equalities {
        Equalities {
            rows: Vec::new(),
            of: vec![BTreeSet::new(); vars],
            pivot_of: vec![BTreeSet::new(); vars],
            order: BTreeSet::new(),
            held: BTreeMap::new(),
            now: 0,
        }
    }

    /// Room for a fresh variable.
    fn grow(&mut self) {
        self.of.push(BTreeSet::new());
        self.pivot_of.push(BTreeSet::new());
    }

    /// The row in slot `s`, which is in use.
    fn row(&self, s: usize) -> &Row {
        &self.rows[s].as_ref().expect("a slot in use").row
    }

    /// The slots of the equalities of least key, all of them when no two share a variable or
    /// when each has one variable to define, with a unit coefficient, that no other of them
    /// holds; otherwise the tie, with the variables they share and the equalities. Equalities
    /// taken so are solved together, and the order among them does not change the result:
    /// solving one defines one of its variables (its pivot) by the others, or by the others
    /// and a fresh one, and writes the definition only into the rows that hold the pivot. In
    /// the first case no other of them holds any of its variables. In the second, no other of
    /// them holds its pivot, so each other is solved the same before and after, and no
    /// definition holds another's pivot, since a definition holds only variables of its own
    /// equality, so each row ends with every pivot replaced by its definition, whatever the
    /// order. Every substitution of one batch is stamped alike (`Equalities::step`), so the
    /// order does not reach the [`EqKey`]s either.
    fn least(&self) -> Option<EqStep> {
        let (key, _) = self.order.first()?;
        let slots: Vec<usize> = self
            .order
            .range((key.clone(), 0)..=(key.clone(), usize::MAX))
            .map(|(_, s)| *s)
            .collect();
        let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
        for s in &slots {
            for (i, _) in self.row(*s).a.iter() {
                *seen.entry(*i).or_insert(0) += 1;
            }
        }
        let vars: Vec<usize> = seen
            .into_iter()
            .filter(|(_, n)| *n > 1)
            .map(|(i, _)| i)
            .collect();
        let apart = |s: &usize| {
            let held = self.rows[*s].as_ref().expect("a slot in use");
            let [p] = held.pivots[..] else {
                return false;
            };
            held.row.at(p).is_unit() && vars.binary_search(&p).is_err()
        };
        if vars.is_empty() || slots.iter().all(apart) {
            return Some(Ok(slots));
        }
        let rows = slots
            .iter()
            .map(|s| (self.row(*s).clone(), Rel::Eq))
            .collect();
        Some(Err((slots, Tied { vars, rows })))
    }

    fn push(&mut self, r: Row, sys: &mut System) {
        self.rows.push(None);
        self.put(self.rows.len() - 1, r, sys);
    }

    /// The degree of a step that would define one of `pivots`.
    fn degree(&self, pivots: &[usize]) -> usize {
        pivots
            .iter()
            .map(|p| self.of[*p].len())
            .min()
            .expect("a pivot")
    }

    fn put(&mut self, s: usize, r: Row, sys: &mut System) {
        match r.normal(true) {
            Norm::False => sys.empty = true,
            Norm::True => {}
            Norm::Row(r) => {
                let same = unsigned(&r);
                if self.held.contains_key(&same) {
                    return;
                }
                self.held.insert(same, s);
                for (i, _) in r.a.iter() {
                    self.of[*i].insert(s);
                }
                let pivots = pivots(&r, sys);
                for p in &pivots {
                    self.pivot_of[*p].insert(s);
                }
                let key = (
                    std::cmp::Reverse(self.now),
                    r.a.len(),
                    self.degree(&pivots),
                    shape(&r, sys),
                );
                self.order.insert((key.clone(), s));
                let vars: Vec<usize> = r.a.iter().map(|(i, _)| *i).collect();
                self.rows[s] = Some(Kept {
                    row: r,
                    key,
                    pivots,
                });
                self.rekey(&vars, s);
            }
        }
    }

    /// Empties the slot `s`, and returns its row.
    fn clear(&mut self, s: usize) -> Row {
        let Kept { row, key, pivots } = self.rows[s].take().expect("a slot in use");
        self.order.remove(&(key, s));
        self.held.remove(&unsigned(&row));
        for p in &pivots {
            self.pivot_of[*p].remove(&s);
        }
        let vars: Vec<usize> = row.a.iter().map(|(i, _)| *i).collect();
        for i in &vars {
            self.of[*i].remove(&s);
        }
        self.rekey(&vars, s);
        row
    }

    /// Renews the degree in the key of each slot but `s` whose step would define one of
    /// `vars`, whose counts of equalities have changed. Each slot has its own pivots, so a
    /// change to the equalities of a variable renews only the slots that would define it.
    fn rekey(&mut self, vars: &[usize], s: usize) {
        let slots: BTreeSet<usize> = vars
            .iter()
            .flat_map(|v| self.pivot_of[*v].iter().copied())
            .filter(|t| *t != s)
            .collect();
        for t in slots {
            let degree = self.degree(&self.rows[t].as_ref().expect("a slot in use").pivots);
            let held = self.rows[t].as_mut().expect("a slot in use");
            if held.key.2 != degree {
                self.order.remove(&(held.key.clone(), t));
                held.key.2 = degree;
                self.order.insert((held.key.clone(), t));
            }
        }
    }

    /// Starts a batch of steps: the equalities their substitutions write are stamped after
    /// those of every batch before, and alike within the batch.
    fn step(&mut self) {
        self.now += 1;
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
    /// The next step would choose among candidates that only their names tell apart.
    Tied(Tied),
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
    /// The dark eliminations kept, by batch, the batches in the order taken: the place of each
    /// one's step, and the number of variables then. A batch is the variables
    /// [`System::least`] gave together, which share no row and which nothing but their names
    /// tells apart.
    gray: Vec<Vec<(usize, usize)>>,
    /// Whether a dark shadow was taken whose splinters are not searched.
    gap: bool,
    /// Whether a gray shadow with three variables left is decided by `live3` in place of a
    /// dark shadow with a gap: set when a splinter is run again after its first run left one.
    exact3: bool,
    /// Whether an exact elimination may add terms: set once a system of rows `±x ± y + k >= 0`
    /// is shown to have a point, since its eliminations are all exact and keep that form.
    fill_ok: bool,
    /// The first tie among equalities, which were then kept as pairs of opposite rows.
    loose_tie: Option<Tied>,
    /// The equalities whose coefficients a step has reduced but not yet to a unit: each is
    /// taken again until it is solved, as the Omega test does, since taking another between
    /// its steps can undo their reduction. They share no variable, as the batch they came
    /// from shares none and a step brings in only its own variables and a fresh one.
    working: Vec<usize>,
    /// Whether the cycles of the rows have been searched for the equalities they imply
    /// ([`Omega::cycles`]).
    cycled: bool,
}

impl Omega {
    /// The test on the rows `base`, each `>= 0` or `== 0`, over variables of the colors `keys`.
    fn new(keys: &[usize], base: &[(Row, Rel)], want: bool, may_splinter: bool) -> Omega {
        let mut sys = System::new(keys.iter().copied());
        let mut es = Equalities::new(keys.len());
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
            exact3: false,
            fill_ok: false,
            loose_tie: None,
            working: Vec::new(),
            cycled: false,
        }
    }

    fn run(&mut self) -> Leaf {
        // The values of the variables left when the loop ends, zero where none is given.
        let mut start: Vec<Int> = Vec::new();
        loop {
            if self.sys.empty {
                return Leaf::Empty;
            }
            // No step below chooses by the names of the variables: each takes what the
            // structure gives first (by color, through `System::least` and
            // `Equalities::least`), all such candidates together when no two share a row, and
            // none when two do, which ends the eliminations at `tie`. Equalities tied so are
            // kept as pairs of opposite rows, which the stages below decide by the same rule.
            let working = std::mem::take(&mut self.working);
            let slots: Vec<usize> = working
                .into_iter()
                .filter(|s| self.es.rows[*s].is_some())
                .collect();
            let next = if slots.is_empty() {
                self.es.least()
            } else {
                Some(Ok(slots))
            };
            self.es.step();
            match next {
                Some(Ok(slots)) => {
                    for s in slots {
                        if let Err(t) = self.equality(s) {
                            self.loosen(&[s], t);
                        }
                    }
                    continue;
                }
                Some(Err((slots, t))) => {
                    if !self.differences(&slots) {
                        self.loosen(&slots, t);
                    }
                    continue;
                }
                None => {}
            }
            if !self.pending.is_empty() {
                self.flush();
                continue;
            }
            let meets = self.sys.meetings();
            if !meets.is_empty() {
                for r in meets {
                    self.es.push(r, &mut self.sys);
                }
                continue;
            }
            // Before the first step that is not an equality, the equalities that cycles of the
            // rows imply are solved like those of the input.
            if !self.cycled {
                self.cycled = true;
                if self.cycles() {
                    continue;
                }
            }
            if self.sys.rows.is_empty() {
                break;
            }
            // Dropping a variable bounded on one side only removes its rows, which leaves every
            // other such variable bounded on one side or not at all, so the variables dropped
            // in the end, and the rows left, are the same in whatever order they are taken.
            if let Some(&j) = self.sys.one_sided.first() {
                let rows = self.sys.take(j);
                self.steps.push(Step::Chosen(j, rows));
                continue;
            }
            if !self.sys.fixable.is_empty() {
                self.fix();
                continue;
            }
            let mut tie: Option<Tied> = None;
            match self.sys.least(&[&self.sys.exact]) {
                Some((fill, _)) if fill > 0 && !self.fill_ok => {}
                Some((_, Ok(js))) => {
                    for j in js {
                        let rows = self.sys.eliminate(j, false);
                        self.steps.push(Step::Chosen(j, rows));
                    }
                    continue;
                }
                // Once `fill_ok` is set the rows are `±x ± y + k >= 0` and have a point, and
                // their eliminations are exact and keep that form, so the answer is known and
                // the order of the rest only places the point found.
                Some((_, Err(_))) if self.fill_ok => {
                    let &(_, _, j) = self.sys.exact.first().expect("a variable");
                    let rows = self.sys.eliminate(j, false);
                    self.steps.push(Step::Chosen(j, rows));
                    continue;
                }
                Some((_, Err(t))) => tie = Some(t),
                None => {}
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
                // Every elimination is exact, and each adds terms or is tied.
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
            if tie.is_none() {
                match self.sys.least(&[&self.sys.inexact]) {
                    Some((fill, Ok(js))) if fill <= 0 => {
                        // An empty real shadow, which keeps every integer point, shows the
                        // problem empty; from here on the dark shadow is solved, whose points
                        // are points of the problem, and the splinters of each dark elimination
                        // hold the points it misses.
                        if !self.tested {
                            self.tested = true;
                            if relaxed_empty(&self.sys) {
                                return Leaf::Empty;
                            }
                        }
                        if self.exact3 && self.sys.live == 3 {
                            // A gray shadow inside a splinter, which would leave the question
                            // refused, is decided completely when three variables are left.
                            match self.three() {
                                Some(leaf) => return leaf,
                                None => continue,
                            }
                        }
                        if self.may_splinter {
                            self.gray.push(Vec::with_capacity(js.len()));
                        } else {
                            self.gap = true;
                        }
                        for j in js {
                            if self.may_splinter {
                                let at = (self.steps.len(), self.sys.vars.len());
                                self.gray.last_mut().expect("a batch").push(at);
                            }
                            let rows = self.sys.eliminate(j, true);
                            self.steps.push(Step::Chosen(j, rows));
                        }
                        continue;
                    }
                    Some((fill, Err(t))) if fill <= 0 => tie = Some(t),
                    _ => {}
                }
            }
            // Every elimination left adds terms. Three live variables, with a unit side or
            // not, are decided by `live3` below, after the box. Until HULL3-subsumed a
            // variable with a unit coefficient in every row on one side was first projected
            // out here by the pairs of bounds `hull3::shadow` chose (XT3 B4). That stage was
            // removed on these measurements of `decide` (instructions; load 47 to 57,
            // 2026-11-05). Rows of `stages::three_rows` with
            // coefficients up to a million, summed over 3 seeds, at 64 / 512 / 4,096 rows:
            // 261M / 3,705M / 38,929M with the stage, 203M / 501M / 1,369M without it. The
            // lens of `live3::tangents` over (5000, 5000), at 64 / 256 / 1,024 pairs of
            // planes: 355M / 2,198M / 11,712M with the stage, 941M / 4,092M / 7,163M without
            // it, and in time 66 ms / 1.61 s against about 210 ms / 2.4 s. The stage was at
            // worst 28 times the work of `live3` alone and grew 13 to 14 times per factor 8,
            // while `live3` alone was at worst 2.7 times the work (3.5 times the time) of the
            // stage. With coefficients up to 5, or a pair of rows with no point, the stage
            // never ran.
            //
            // An empty real shadow shows the problem empty whatever was tied.
            if tie.is_some() && !self.tested {
                self.tested = true;
                if relaxed_empty(&self.sys) {
                    return Leaf::Empty;
                }
            }
            // The rows are empty when the box of their bounds shows it, and have a point when
            // one of the five points of the box that `box_point` tries holds them; otherwise
            // three variables left are decided by `live3`, and four or
            // more are refused.
            //
            // Complexity tradeoff: a system over four variables or more that the box neither
            // empties nor satisfies, once
            // no elimination is left that keeps the rows from growing, is given up: it gets
            // `Refusal::Growth` ("not decided", rejected at the function by `run.rs`
            // `linear_questions`), though it may have a point or none. Only five points of the
            // box are tried (nearest zero, lower corner, upper corner, the two midpoints), so a
            // system whose points all lie elsewhere in the box is refused. The box is shown empty
            // only by one pass over the rows (`row_box_empty`): a row below zero over the box, or
            // two rows that bound a variable past each other with the other terms at their
            // largest; a system with no rational point that no such pair shows (the rows of
            // `stages::CROSSING` raised by 1 to 7) is refused, since the resolvents that would
            // find more (cross-review XR3 Q1) were not adopted. Why: an
            // elimination that adds terms multiplies lower by upper bounds, so the rows can grow
            // doubly exponentially in the variables eliminated (Fourier–Motzkin), and the dark
            // and gray shadows of the full Omega test add an exponential search on top; trying
            // every point of the box is exponential in the variables. Trigger: four or more
            // live variables whose every elimination pairs more bounds than it removes and
            // whose rows are not all `±x ± y + k >= 0`; the size of the system plays no part.
            // (Three live variables are decided completely, by `live3` below.) Tests: `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`,
            // `l01_38_presburger::checker::a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused`,
            // `l01_38_presburger::scaling::the_shifted_sparse_family_scales`,
            // `l01_38_presburger::stages::rows_the_one_pass_test_does_not_show_empty_stay_refused`,
            // `l01_38_presburger::scaling::the_box_stage_with_a_hub_in_one_row_per_block_scales`.
            // COMPLEXITY.md rows S18, Q1-ROWBOX and Kept "Fourier–Motzkin pairs". A complete
            // solution would run the growing eliminations of the full Omega test (or another
            // complete Presburger procedure) and accept their exponential worst case, or find a
            // structural class of growing systems over four variables or more decidable in
            // O(n log n).
            let Some((lo, hi)) = bounds(&self.sys) else {
                return Leaf::Empty;
            };
            if box_empty_in(&self.sys, &lo, &hi) {
                return Leaf::Empty;
            }
            if let Some(v) = box_point(&self.sys, &lo, &hi) {
                start = v;
                break;
            }
            if self.sys.live <= 3 {
                // `live3` decides three variables completely, so the order of tied ones
                // cannot change its answer.
                match self.three() {
                    Some(leaf) => return leaf,
                    None => continue,
                }
            }
            // Complexity tradeoff: when the next elimination would choose among variables
            // (or equalities, or the variables of an equality) that share a row and that
            // refinement of the rows cannot tell apart, and neither the stages above nor the
            // box decide the rows, the question gets `Refusal::Tie` ("not decided"), though
            // it may have a point or none. Why: which of them goes first changes the rows
            // that follow and so whether a later stage decides them, and nothing but their
            // names would choose; refusing keeps every answer, refusals included, the same
            // under every naming of the variables, while trying every order is exponential
            // in the tied variables and telling them apart for good (canonical labeling of
            // the rows) has no known polynomial algorithm. Trigger: two variables of one
            // color, both of least fill, sharing a row, in a system no other stage decides;
            // the size of the system plays no part. Tests:
            // `l01_38_presburger::names::a_tie_that_shares_a_row_is_refused`,
            // `l01_38_presburger::names::every_naming_gives_one_answer_on_the_regular_family_of_five_103`.
            // COMPLEXITY.md row NAME-ties. A complete solution would search every order of
            // the tied candidates, or decide the rows by a complete method (plan item
            // HULL3-GEN; three live variables are decided by `live3` above).
            return match tie.or_else(|| self.loose_tie.take()) {
                Some(t) => Leaf::Tied(t),
                None => Leaf::Refused(Refusal::Growth),
            };
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

    /// Decides the rows, which hold three variables, by Lenstra's method in dimension three
    /// (`live3`), with no refusal: the answer when it is settled here (empty, or a point
    /// that is not wanted), or `None` once the three variables are defined by a point.
    fn three(&mut self) -> Option<Leaf> {
        let Some((x, v)) = self.triple() else {
            return Some(Leaf::Empty);
        };
        if !self.want {
            return Some(Leaf::Point(Vec::new()));
        }
        for (j, v) in x.into_iter().zip(v) {
            self.sys.take(j);
            let a = Vec::new().into();
            self.steps.push(Step::Defined(j, Row { a, k: v }));
        }
        None
    }

    /// The three live variables and an integer point of the rows over them, or `None` when
    /// the rows have none.
    fn triple(&self) -> Option<([usize; 3], [Int; 3])> {
        let vs: BTreeSet<usize> = self
            .sys
            .rows
            .keys()
            .flat_map(|a| a.iter().map(|(i, _)| *i))
            .collect();
        let vs: [usize; 3] = Vec::from_iter(vs)
            .try_into()
            .unwrap_or_else(|_| unreachable!("three live variables"));
        let rows: Vec<(&[Term], &Int)> = self.sys.rows.iter().map(|(a, h)| (&**a, &h.k)).collect();
        let x = live3::decide(&rows, &vs)?;
        Some((vs, x))
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
        // The fresh `k` has a color of its own, above every color of the rows.
        let keys: Vec<usize> = self.sys.vars[..vars]
            .iter()
            .map(|v| v.key)
            .chain([usize::MAX])
            .collect();
        Some(Omega::new(&keys, &rows, self.want, false))
    }

    /// Solves the equality in slot `s`: by the unit coefficient of least color where it has
    /// one, or else by one unimodular step on the variable `y` of least coefficient `b` and of
    /// least color among those: with `q[i]` the nearest integer to `a[i] / b` at each other
    /// `x[i]` and `q` that of `k / b`, `y = t - Σ q[i]·x[i] - q` for a fresh `t` of the color of
    /// `y`. The map is onto the integers, and leaves the symmetric remainder of each `a[i]` by
    /// `b`, so the least coefficient at least halves and every other falls below it in one
    /// step, however large it was. When two variables tie for the choice, the tie, with the
    /// equality, and the equality is left in its slot.
    fn equality(&mut self, s: usize) -> Result<(), Tied> {
        let e = self.es.clear(s);
        let key = |i: usize| self.sys.vars[i].key;
        let units: Vec<usize> =
            e.a.iter()
                .filter(|(_, c)| c.is_unit())
                .map(|(i, _)| *i)
                .collect();
        let pool: Vec<(Int, usize, usize)> = if units.is_empty() {
            e.a.iter().map(|(i, c)| (c.abs(), key(*i), *i)).collect()
        } else {
            units.iter().map(|&i| (Int::ONE, key(i), i)).collect()
        };
        let (m, k, _) = pool.iter().min().expect("a row has a variable").clone();
        let tied: Vec<usize> = pool
            .iter()
            .filter(|(c, kk, _)| *c == m && *kk == k)
            .map(|p| p.2)
            .collect();
        // `x - y == d` between two variables of one color, as `Ties` does in `solve`: the
        // greater is defined by the lesser, which is a choice by the values, not the names; when
        // `d` is zero the two are equal at every point, so defining either leaves the same rows
        // with one name for the other.
        let difference = tied.len() == 2 && e.a.len() == 2 && e.a[0].1 == -&e.a[1].1;
        if difference {
            // `c·x0 - c·x1 + k == 0`, so `x0 - x1 == -k·c`.
            let d = -&(&e.k * &e.a[0].1);
            let y = if d.is_negative() { e.a[1].0 } else { e.a[0].0 };
            self.define(y, &e);
            return Ok(());
        }
        if tied.len() > 1 {
            let rows = vec![(e.clone(), Rel::Eq)];
            self.es.put(s, e, &mut self.sys);
            return Err(Tied { vars: tied, rows });
        }
        let y = tied[0];
        if !units.is_empty() {
            self.define(y, &e);
            return Ok(());
        }
        let b = &e.at(y).clone();
        let t = self.fresh(key(y));
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
        self.working.push(s);
        self.steps.push(Step::Defined(y, def.clone()));
        self.pending.push((y, def));
        Ok(())
    }

    /// Solves the equalities in `slots` together when each is `x - y == d`, and says whether
    /// it did. Each class of variables they join is written over one member, the member of least
    /// color, then of least value, then of least place, as [`Ties::representatives`] chooses,
    /// so the order of the equalities plays no part; two members of one color and one value
    /// are equal at every point, so taking either leaves the same rows with one name for the
    /// other. O(e log e) for e equalities.
    fn differences(&mut self, slots: &[usize]) -> bool {
        let is_difference =
            |r: &Row| r.a.len() == 2 && r.a[0].1.is_unit() && r.a[0].1 == -&r.a[1].1;
        if !slots.iter().all(|s| {
            self.es.rows[*s]
                .as_ref()
                .is_some_and(|h| is_difference(&h.row))
        }) {
            return false;
        }
        let rows: Vec<Row> = slots.iter().map(|s| self.es.clear(*s)).collect();
        let vars: Vec<usize> = rows
            .iter()
            .flat_map(|r| r.a.iter().map(|(i, _)| *i))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let local = |i: usize| vars.binary_search(&i).expect("a variable of the rows");
        let mut ties = Ties::new(vars.len());
        for r in &rows {
            // `c·x - c·y + k == 0`, so `x - y == -k·c`.
            let d = -&(&r.k * &r.a[0].1);
            if !ties.equate(local(r.a[0].0), local(r.a[1].0), d) {
                self.sys.empty = true;
                return true;
            }
        }
        let keys: Vec<usize> = vars.iter().map(|&i| self.sys.vars[i].key).collect();
        for (l, (rep, d)) in ties.representatives(&keys).into_iter().enumerate() {
            if rep != l {
                // `x - rep - d == 0`.
                let e = Row {
                    a: merge(
                        &[(vars[l], Int::ONE)],
                        &Int::ONE,
                        &[(vars[rep], -&Int::ONE)],
                        &Int::ONE,
                        usize::MAX,
                    ),
                    k: -&d,
                };
                self.define(vars[l], &e);
            }
        }
        true
    }

    /// Turns into equalities the rows that a cycle of rows forces to hold with `==`, and says
    /// whether it found any, or found the rows empty. A row `x - y + k >= 0` with `k <= 0`
    /// says `x >= y + w` with `w = -k >= 0`: an edge `y → x` of weight `w` in a graph over
    /// the variables and a node for zero, which the rows `x + k >= 0` (`x >= w`, an edge from
    /// zero) and `-x + k >= 0` (`0 >= x + w`, an edge to zero) join. Every edge within a
    /// strongly connected component lies on a cycle, along which the variables only rise,
    /// each by at least its edge's weight, and come back to where they began; so an edge
    /// of weight above zero there leaves no point, and every other holds with `==`. The
    /// variables of a cycle of rows `x - y >= 0` are thus all equal, and so are two rows
    /// `x - y >= 0` and `y - x >= 0`. The edges are chosen by the rows alone, so no name plays
    /// a part. O(m log m + n) for m rows over n variables, by Tarjan's algorithm
    /// ([`utvpi::components`]).
    ///
    /// Complexity tradeoff: two kinds of implied equality are not found here. A cycle whose
    /// weights have both signs and sum to zero (`x - y + 1 >= 0`, `y - z - 1 >= 0`,
    /// `z - x >= 0`) needs a potential of the whole graph, a shortest-path search with
    /// negative weights; and a cycle that only forms after the definitions this search starts,
    /// or after an elimination, would need the search again after every step, O(m) each, so
    /// O(m·n) over a run. The search runs once, before the first step that is not an
    /// equality. A system that has only such cycles goes on to the stages below as before, and
    /// may be refused with `Refusal::Growth` though its cycles decide it. Trigger: a zero-sum
    /// cycle of difference rows with a weight below zero on it, or one closed by a step; the
    /// size of the system plays no part. Tests:
    /// `l01_38_presburger::omega::a_cycle_of_rows_makes_its_variables_equal` and
    /// `l01_38_presburger::scaling::a_cycle_of_rows_scales`. COMPLEXITY.md row
    /// OMEGA-cycle-growth. A complete solution would find a potential with
    /// [`utvpi::integer_empty`]'s search, take the zero-weight cycles among its tight edges,
    /// and keep the components up to date as steps add rows (incremental strongly connected
    /// components).
    fn cycles(&mut self) -> bool {
        // The node of `x[j]` is `j + 1`, and zero is node 0.
        let mut out: Vec<Vec<usize>> = vec![Vec::new(); self.sys.vars.len() + 1];
        let mut edges: Vec<(usize, usize, usize, bool)> = Vec::new();
        for (a, held) in &self.sys.rows {
            if held.k.is_positive() || a.iter().any(|(_, c)| !c.is_unit()) {
                continue;
            }
            let node = |(i, _): &Term| i + 1;
            let (from, to) = match &a[..] {
                [t] if t.1.is_positive() => (0, node(t)),
                [t] => (node(t), 0),
                [s, t] if s.1 == -&t.1 && s.1.is_positive() => (node(t), node(s)),
                [s, t] if s.1 == -&t.1 => (node(s), node(t)),
                _ => continue,
            };
            out[from].push(to);
            edges.push((from, to, held.id, held.k.is_zero()));
        }
        let comp = utvpi::components(&out, |v| *v);
        let mut tight: Vec<usize> = Vec::new();
        for (from, to, id, zero) in edges {
            if comp[from] != comp[to] {
                continue;
            }
            if !zero {
                self.sys.empty = true;
                return true;
            }
            tight.push(id);
        }
        let found = !tight.is_empty();
        for id in tight {
            let r = self.sys.remove(id);
            self.es.push(r, &mut self.sys);
        }
        found
    }

    /// Keeps the equalities in `slots`, which tie as `t` says, as pairs of opposite rows. Each
    /// slot is cleared, and no equality takes its place: equalities are formed only from the
    /// input and from rows that meet ([`System::meetings`]), and rows whose coefficients are
    /// kept in `loose` are not formed again, so the loop ends. An equality whose rows were
    /// kept before adds them again, which changes nothing, and the loop goes on to the stages
    /// below as after any tie kept so; the stages after the eliminations decide what they can
    /// and the first tie is kept for the refusal. Each pair holds the points of its equality,
    /// so the rows mean what they did, and the set of slots is chosen by structure, so no
    /// order among them plays a part. O(e log m) for e equalities over m rows.
    fn loosen(&mut self, slots: &[usize], t: Tied) {
        self.loose_tie.get_or_insert(t);
        for &s in slots {
            if self.es.rows[s].is_none() {
                continue;
            }
            let r = self.es.clear(s);
            let opp: Coefs = opposite(&r.a).into();
            let lesser = if r.a < opp { r.a.clone() } else { opp.clone() };
            self.sys.loose.insert(lesser);
            let k = -&r.k;
            self.sys.add(r);
            self.sys.add(Row { a: opp, k });
        }
    }

    /// A fresh variable of the color `key`.
    fn fresh(&mut self, key: usize) -> usize {
        self.sys.vars.push(Var {
            key,
            ..Var::default()
        });
        self.es.grow();
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
/// disjunction's union of projections, with its two ends moved in by `tighten`; the gaps
/// that only a combination of disjuncts shows are given up, so the set can hold values no
/// point takes. Why: the exact projection is the union over every combination of one disjunct
/// per disjunction, which is exponential in the disjunctions. Trigger: more than one
/// disjunction left after propagation. Test:
/// `l01_38_presburger::random::random_tests_agree_with_the_interpreter` (every projection
/// holds every value; one of 60 is wider than the hull). COMPLEXITY.md rows S7 and S16. A
/// complete solution would project each combination of disjuncts, or a decision diagram over
/// the disjuncts, at a cost exponential in the worst case.
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
    let r = match Renamed::of(f) {
        Naming::Kept => return project_each_inner(f, syms),
        Naming::Renamed(r) => r,
        // Projected with each disjunction kept, by questions that no order of the parts
        // changes ([`project_parts`] with `sets`).
        Naming::Tied(..) => {
            return match settle_as_sets(Parts::of(nnf(f, true)))? {
                None => Ok(no_points(syms)),
                // A projection may keep a disjunct not shown to have a point.
                Some(AsSets { p, .. }) => {
                    project_parts(p, syms, Some(f), true, &mut HashMap::new())
                }
            };
        }
    };
    let there: Vec<Atom> = syms.iter().map(|s| r.there(s)).collect();
    let (each, skipped) = project_each_inner(&r.f, &there).map_err(|e| r.back_refusal(e))?;
    Ok((
        each.into_iter()
            .map(|s| s.map_err(|e| r.back_refusal(e)))
            .collect(),
        skipped.into_iter().map(|e| r.back_refusal(e)).collect(),
    ))
}

/// [`project_each`] of a formula whose names no longer matter ([`Renamed`]).
fn project_each_inner(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    match propagate(f)? {
        Some(p) => project_parts(p, syms, Some(f), false, &mut HashMap::new()),
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
///
/// With `sets`, for parts whose atoms share a color ([`Naming::Tied`]), each question is one
/// whose answer no order of the parts changes: no search ([`pick`], [`probe`]) removes
/// disjuncts first; each disjunct of a disjunction is settled by [`settle_as_sets`] before any
/// is asked for a symbol; those shown to have no point are not asked, and each of the others
/// is asked for the symbols that all of them touch, even after one is refused; and a hull is
/// tightened by [`decide`], which renames or settles the formula as its colors allow. The
/// projection is then a function of the parts as sets: for each disjunction, the union of its
/// disjuncts' projections, met over the disjunctions. The settling of each disjunct is the
/// cost added to that of the projection, one test of each disjunct below it for each round of
/// the settling.
fn project_parts(
    mut p: Parts,
    syms: &[Atom],
    whole: Option<&Formula>,
    sets: bool,
    memo: &mut Below,
) -> Result<Each, Refusal> {
    let none = || no_points(syms);
    let mut skipped: Vec<Refusal> = Vec::new();
    if !sets && p.ors.len() > 1 && pick(&p, whole.is_some()).is_err() {
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
    // The groups a disjunct touches, found from its atoms or from the base's, whichever are
    // fewer, so that a level does not read every atom below it.
    let roots_of = |atoms: &OrdSet<Atom>| -> Vec<usize> {
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
        roots
    };
    // The symbols a disjunct with `atoms` and base groups `roots` touches, in order.
    let touched = |atoms: &OrdSet<Atom>, roots: &[usize]| -> Vec<usize> {
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
    };
    // The disjunct's parts with the base groups it touches, its constraints sorted as
    // [`nnf`] sorts them and its disjunctions shared.
    let parts_of = |d: &Parts, roots: &[usize]| -> Parts {
        let mut fs: Vec<Formula> = roots.iter().map(|r| base_of(*r).clone()).collect();
        fs.extend(d.cons.iter().cloned().map(Formula::Con));
        let mut q = Parts::of(Formula::and(fs));
        q.cons.sort();
        q.ors.extend(d.ors.iter().cloned());
        q
    };
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
        // the nest below it. With `sets`, each disjunct is settled first, and each
        // that may have a point is asked for the symbols that all such disjuncts touch, which
        // no order changes; the others are not asked.
        let mut order: Vec<&Rc<Parts>> = ds.iter().collect();
        order.sort_by_key(|d| d.atoms().len());
        let mut wanted: Option<Vec<usize>> = None;
        let mut pre: Vec<Option<Result<Option<Parts>, Refusal>>> = Vec::new();
        if sets {
            for d in &order {
                let roots = roots_of(d.atoms());
                // A projection may keep a disjunct not shown to have a point.
                let s = settle_as_sets(parts_of(d, &roots)).map(|s| s.map(|s| s.p));
                // Only a settling that leaves no point shows that a disjunct has none; a
                // search for one would choose by name.
                let maybe = !matches!(s, Ok(None));
                if maybe {
                    let ks = touched(d.atoms(), &roots);
                    wanted = Some(match wanted {
                        None => ks,
                        Some(ws) => ws
                            .into_iter()
                            .filter(|k| ks.binary_search(k).is_ok())
                            .collect(),
                    });
                }
                pre.push(maybe.then_some(s));
            }
        }
        for (at, d) in order.into_iter().enumerate() {
            let pre_d = match pre.get_mut(at) {
                Some(s) => match s.take() {
                    Some(s) => Some(s),
                    None => continue,
                },
                None => None,
            };
            let atoms = d.atoms();
            let roots = roots_of(atoms);
            let ks: Vec<usize> = match &wanted {
                Some(ws) => ws
                    .iter()
                    .copied()
                    .filter(|&k| match linked.ids.get(&syms[k]) {
                        Some(i) => roots.binary_search(&linked.root(*i)).is_ok(),
                        None => atoms.contains(&syms[k]),
                    })
                    .collect(),
                None => touched(atoms, &roots),
            };
            let sub: Vec<Atom> = ks.iter().map(|&k| syms[k].clone()).collect();
            // A disjunct asked for no symbol is only asked whether it has a point, as
            // [`decide`] asks it; with `sets` it was asked above.
            // A disjunct met before, at the same base groups and asked for the same symbols,
            // is read once: its answer depends on these alone.
            let key: BelowKey = (
                Rc::as_ptr(d),
                (roots.iter())
                    .flat_map(|r| linked.held[*r].iter().map(|i| linked.cons[*i].clone()))
                    .collect(),
                sub.clone(),
            );
            let found_rs = if let Some((_, r)) = memo.get(&key) {
                r.clone()
            } else {
                let settled = match pre_d {
                    Some(s) => s,
                    None => settle(parts_of(d, &roots)),
                };
                let r = settled.and_then(|q| match q {
                    None => Ok((no_points(&sub), false)),
                    Some(q) if ks.is_empty() => {
                        // A point of the disjunct with each disjunct below cut to its own
                        // constraints keeps it, as a level below the top is tightened
                        // ([`summarize`]); the search below it runs only when there is none.
                        let point = sets
                            || q.ors.is_empty()
                            || pick(&q, false).is_ok()
                            || !matches!(probe(q), Ok(None));
                        Ok(((Vec::new(), Vec::new()), point))
                    }
                    Some(q) => project_parts(q, &sub, None, sets, memo).map(|e| {
                        let point = e.0.iter().any(|r| !matches!(r, Ok(s) if s.is_empty()));
                        (e, point)
                    }),
                });
                memo.insert(key, (Rc::clone(d), r.clone()));
                r
            };
            let (rs, has_point) = match found_rs {
                Ok(((rs, more), point)) => {
                    skipped.extend(more);
                    (rs, point)
                }
                Err(r) => {
                    skipped.push(r);
                    refused = true;
                    // With `sets` every disjunct is asked, so the causes reported are those
                    // of all of them, not of those before the first refused.
                    if sets {
                        continue;
                    }
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
                    skipped.push(r.clone());
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
                found_here.push((&**d, kept));
            }
            if !sets {
                wanted = Some(ks);
            }
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
            *o = tighten(f, sym, s.clone(), if sets { decide } else { decide_inner });
        }
    }
    skipped.sort_unstable();
    skipped.dedup();
    Ok((out, skipped))
}

/// A disjunct of [`project_parts`] below the top, by address, with the constraints of the base
/// groups it is read with and the symbols it is asked for.
type BelowKey = (*const Parts, Vec<Con>, Vec<Atom>);

/// The answers of [`project_parts`] for the disjuncts below the top already read, each with
/// the disjunct it is keyed by, held so that its address is not reused. A disjunct shared by
/// several disjunctions (a named disjunction used as a disjunct at each of several places,
/// COMPLEXITY.md S31b) is then projected once for each base and set of symbols, not once for
/// each path to it, which is exponential in the depth when the shared disjunctions nest.
type Below = HashMap<BelowKey, (Rc<Parts>, Result<(Each, bool), Refusal>)>;

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
/// no point. A bound moves only on such a proof, so a refused question leaves it sound. Each
/// question is asked of `ask`, [`decide_inner`] for a formula renamed or [`decide`] when its
/// atoms may share a color.
fn tighten(
    f: &Formula,
    sym: &Atom,
    set: IntervalSet,
    ask: fn(&Formula) -> Result<bool, Refusal>,
) -> Result<IntervalSet, Refusal> {
    let Some((End::Fin(lo), End::Fin(hi))) = set.bounds() else {
        return Ok(set);
    };
    let x = Lin::atom(sym.clone());
    let none = |con: Con| {
        matches!(
            ask(&Formula::and(vec![f.clone(), Formula::Con(con)])),
            Ok(false)
        )
    };
    let (one, two) = (Int::ONE, Int::from(2));
    // The least `v` in `lo..=hi` with no proof that `f` has no point where `sym <= v`, and the
    // greatest with none where `sym >= v`.
    let (mut a, mut b) = (Int::from(lo), Int::from(hi));
    while a < b {
        let mid = &a + &(&b - &a).div_floor(&two);
        if none(Con::ge(&Lin::constant(mid.clone()), &x)) {
            a = &mid + &one
        } else {
            b = mid
        }
    }
    let new_lo = a;
    if none(Con::ge(&Lin::constant(new_lo.clone()), &x)) {
        return Ok(IntervalSet::empty());
    }
    let (mut a, mut b) = (new_lo.clone(), Int::from(hi));
    while a < b {
        let mid = &b - &(&b - &a).div_floor(&two);
        if none(Con::ge(&x, &Lin::constant(mid.clone()))) {
            b = &mid - &one
        } else {
            a = mid
        }
    }
    Ok(set.meet(&IntervalSet::range(
        End::Fin(Num::from(&new_lo)),
        End::Fin(Num::from(&a)),
    )))
}

/// The least and greatest values of a symbol over a formula.
fn hull(c: &Formula, sym: &Atom) -> Result<IntervalSet, Refusal> {
    match satisfiable_inner(c)? {
        Some(m) => hull_from(c, sym, &m),
        None => Ok(IntervalSet::empty()),
    }
}

/// [`hull`] given a point `m` of the formula. A side with no bound is found by one question,
/// [`unbounded`]. A bound is then found by the monotone questions "is there a point with the
/// symbol at most `v`" and "at least `v`", searched outward from the point's value with steps
/// that double, then by bisection, so it takes O(log d) questions for a bound at distance d,
/// each on integers of O(log d) bits. Every bound is exact at any magnitude.
fn hull_from(c: &Formula, sym: &Atom, m: &Model) -> Result<IntervalSet, Refusal> {
    let x = Lin::atom(sym.clone());
    let at = m.get(sym).cloned().unwrap_or(Int::ZERO);
    let with = |con: Con| -> Result<bool, Refusal> {
        decide_inner(&Formula::and(vec![c.clone(), Formula::Con(con)]))
    };
    let below = |v: &Int| with(Con::ge(&Lin::constant(v.clone()), &x));
    let above = |v: &Int| with(Con::ge(&x, &Lin::constant(v.clone())));
    // The last value of the monotone `holds` that is true, moving from `start` (true) by
    // `dir`; `holds` is false far enough that way, since the side is bounded.
    let edge = |holds: &dyn Fn(&Int) -> Result<bool, Refusal>,
                start: &Int,
                dir: &Int|
     -> Result<Int, Refusal> {
        let (mut good, mut step) = (start.clone(), Int::ONE);
        let bad = loop {
            let next = &good + &(dir * &step);
            if !holds(&next)? {
                break next;
            }
            good = next;
            step = &step + &step;
        };
        let (mut good, mut bad) = (good, bad);
        let two = Int::from(2);
        while (&bad - &good).abs() > Int::ONE {
            let mid = &good + &(&bad - &good).div_floor(&two);
            if holds(&mid)? { good = mid } else { bad = mid }
        }
        Ok(good)
    };
    let lo = if unbounded(c, sym, -1)? {
        End::NegInf
    } else {
        End::Fin(Num::from(&edge(&below, &at, &Int::from(-1))?))
    };
    let hi = if unbounded(c, sym, 1)? {
        End::PosInf
    } else {
        End::Fin(Num::from(&edge(&above, &at, &Int::ONE)?))
    };
    Ok(IntervalSet::range(lo, hi))
}

/// Whether `sym` takes arbitrarily large values (`dir` 1) or arbitrarily small ones (`dir`
/// -1) over the integer points of `c`, which has one. In negation normal form `c` is an
/// and-or tree of constraints, so its integer points are the union, over its terms in
/// disjunctive form, of the integer points of each term's polyhedron `P`. When `P` has an
/// integer point, the hull of its integer points has the recession cone of `P` (Meyer 1974),
/// so `sym` is unbounded over them exactly when some ray `r` with `A·r >= 0` and `E·r == 0`
/// for `P`'s rows `A·z + a >= 0` and `E·z + e == 0` has `dir · r_sym > 0`, and then one with
/// `dir · r_sym >= 1` in integers, the cone being rational. The question is one formula: each
/// constraint is replaced by itself and its row without the constant over a copy of the atoms
/// (fresh auxiliary variables), which keeps the tree, so its terms are the pairs of a term's
/// polyhedron and its cone. With no disjunction the point is known, and the cone alone is
/// asked. Its size is twice that of `c`.
fn unbounded(c: &Formula, sym: &Atom, dir: i64) -> Result<bool, Refusal> {
    let f = nnf(c, true);
    let atoms = f.atoms();
    let first = atoms
        .iter()
        .filter_map(|a| match a {
            Atom::Aux(n) => Some(n + 1),
            _ => None,
        })
        .max()
        .unwrap_or(0);
    let ray: BTreeMap<&Atom, Atom> = atoms
        .iter()
        .zip(first..)
        .map(|(a, n)| (a, Atom::Aux(n)))
        .collect();
    let cone = |con: &Con| Con {
        lin: Lin {
            terms: con
                .lin
                .terms
                .iter()
                .map(|(a, k)| (ray[a].clone(), k.clone()))
                .collect(),
            constant: Int::ZERO,
        },
        rel: con.rel,
    };
    // A shared conjunction is entered once.
    let has_or = |g: &Formula| -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![g];
        while let Some(g) = stack.pop() {
            match g {
                Formula::Or(_) => return true,
                Formula::And(gs) if Id::of(g).is_none_or(|id| seen.insert(id)) => {
                    stack.extend(gs.iter())
                }
                _ => {}
            }
        }
        false
    };
    // A symbol no constraint mentions takes every value.
    let Some(r) = ray.get(sym) else {
        return Ok(true);
    };
    let r = Lin::atom(r.clone());
    let away = Formula::Con(Con::ge(&r.times(dir), &Lin::constant(1)));
    let body = if has_or(&f) {
        // Each constraint `k` replaced by `k && cone(k)`.
        f.map_cons(&|k| Formula::and(vec![Formula::Con(k.clone()), Formula::Con(cone(k))]))
    } else {
        Formula::and(f.cons().iter().map(|con| Formula::Con(cone(con))).collect())
    };
    decide(&Formula::and(vec![body, away]))
}

/// The set `s` of a symbol as a formula: the disjunction of its pieces.
pub fn member(sym: &Atom, s: &IntervalSet) -> Formula {
    within(&Lin::atom(sym.clone()), s)
}

/// The values of the term `l` in the set `s`, as a formula.
pub fn within(l: &Lin, s: &IntervalSet) -> Formula {
    let mut pieces = Vec::new();
    for (lo, hi) in s.pieces() {
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
thread_local! {
    /// Whether [`Formula::and_keeping`] and [`Formula::or_keeping`] join as they did before
    /// [`Joining`], and the translator joins a chain of `&&` or `||` two at a time
    /// (`preimage::Tx::two_at_a_time`): for the tests that compare the two (ST-formula-k2).
    pub(super) static TWO_AT_A_TIME: Cell<bool> = const { Cell::new(false) };
}

#[cfg(test)]
pub(super) mod tests {
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
        let point = quotient(2, vec![(r.clone(), Rel::Eq)], &[0, 1], &[0], true, &|i| {
            format!("x{i}")
        })
        .expect("decided")
        .expect("a point");
        assert_eq!(r.eval(&point), Int::ZERO);
    }

    #[test]
    fn merged_columns_take_only_the_multiples_of_their_divisor() {
        // `2x + 4y` is even, so `2x + 4y == 1` has no point, though it has rational ones.
        let r = row(&[(0, 2), (1, 4)], -1);
        assert_eq!(
            quotient(2, vec![(r, Rel::Eq)], &[0, 1], &[0], true, &|i| format!(
                "x{i}"
            )),
            Ok(None)
        );
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

    /// Whether the rows `Σ a[i]·x[i] + k >= 0` over `n` variables, with the box `lo`, `hi` as
    /// rows, have no rational point: Fourier–Motzkin over every variable, exact over `Int`.
    fn rationally_empty(
        n: usize,
        rows: &[(Vec<Int>, Int)],
        lo: &[Option<Int>],
        hi: &[Option<Int>],
    ) -> bool {
        let unit = |j: usize, c: i128| -> Vec<Int> {
            (0..n)
                .map(|i| Int::from(if i == j { c } else { 0 }))
                .collect()
        };
        let mut cur: Vec<(Vec<Int>, Int)> = rows.to_vec();
        for j in 0..n {
            if let Some(l) = &lo[j] {
                cur.push((unit(j, 1), -l));
            }
            if let Some(h) = &hi[j] {
                cur.push((unit(j, -1), h.clone()));
            }
        }
        for j in 0..n {
            let (mut pos, mut neg, mut rest) = (Vec::new(), Vec::new(), Vec::new());
            for r in cur {
                if r.0[j].is_positive() {
                    pos.push(r);
                } else if r.0[j].is_negative() {
                    neg.push(r);
                } else {
                    rest.push(r);
                }
            }
            for (pa, pk) in &pos {
                for (qa, qk) in &neg {
                    let (a, b) = (&pa[j], &-&qa[j]);
                    let c: Vec<Int> = (0..n).map(|i| &(b * &pa[i]) + &(a * &qa[i])).collect();
                    let k = &(b * pk) + &(a * qk);
                    let g = c.iter().fold(k.abs(), |g, x| g.gcd(x));
                    if g.is_zero() {
                        rest.push((c, k));
                    } else {
                        rest.push((c.iter().map(|x| x.div_floor(&g)).collect(), k.div_floor(&g)));
                    }
                }
            }
            rest.sort();
            rest.dedup();
            cur = rest;
        }
        cur.iter().any(|(_, k)| k.is_negative())
    }

    /// The rows of `sys` over `n` variables, each as its coefficients by place and its constant.
    fn dense(sys: &System, n: usize) -> Vec<(Vec<Int>, Int)> {
        sys.rows
            .iter()
            .map(|(a, held)| {
                let mut c = vec![Int::ZERO; n];
                for (i, x) in a.iter() {
                    c[*i] = x.clone();
                }
                (c, held.k.clone())
            })
            .collect()
    }

    /// The old box test: some wide row below zero at every point of the box.
    fn a_row_below_zero(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> bool {
        sys.rows
            .iter()
            .filter(|(a, _)| a.len() > 1)
            .any(|(a, held)| {
                let mut s = held.k.clone();
                for (i, c) in a.iter() {
                    match if c.is_positive() { &hi[*i] } else { &lo[*i] } {
                        Some(b) => s = &s + &(c * b),
                        None => return false,
                    }
                }
                s.is_negative()
            })
    }

    /// A system of the rows `Σ c·x + k >= 0` over variables by place, renamed by `perm`, with
    /// each variable in `[-half, half]`.
    fn boxed_system(rows: &[(Vec<i128>, i128)], perm: &[usize], half: i128) -> System {
        let n = perm.len();
        let mut sys = System::new(0..n);
        for (c, k) in rows {
            let t: Vec<(usize, i128)> = (0..n)
                .filter(|&i| c[i] != 0)
                .map(|i| (perm[i], c[i]))
                .collect();
            let mut t = t;
            t.sort();
            sys.add(row(&t, *k));
        }
        for j in 0..n {
            sys.add(row(&[(j, 1)], half));
            sys.add(row(&[(j, -1)], half));
        }
        sys
    }

    /// A small random generator for the tests below (xorshift).
    struct Draw(u64);

    impl Draw {
        fn int(&mut self, lo: i128, hi: i128) -> i128 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            lo + (self.0 % (hi - lo + 1) as u64) as i128
        }
    }

    /// Every permutation of `0..4`.
    fn perms4() -> Vec<Vec<usize>> {
        let mut out = Vec::new();
        for a in 0..4 {
            for b in 0..4 {
                for c in 0..4 {
                    for d in 0..4 {
                        let p = vec![a, b, c, d];
                        let mut s = p.clone();
                        s.sort();
                        s.dedup();
                        if s.len() == 4 {
                            out.push(p);
                        }
                    }
                }
            }
        }
        out
    }

    #[test]
    fn the_row_test_of_the_box_shows_empty_only_what_has_no_rational_point() {
        // 3000 systems of 2 to 5 rows over four variables in [-4, 4], coefficients up to 7
        // and constants up to 20 (the oracle's 0x38_0a family). Wherever the box test says
        // empty, Fourier–Motzkin finds no rational point in the box it was given; the answer
        // is the same under all 24 namings of the variables, which reorder the rows; and some
        // systems are shown empty only by two rows whose bounds on a variable cross.
        let mut g = Draw(0x38_0a_0b);
        let all = perms4();
        let (mut empty, mut crossed) = (0, 0);
        for _ in 0..3000 {
            let rows: Vec<(Vec<i128>, i128)> = (0..g.int(2, 5))
                .map(|_| ((0..4).map(|_| g.int(-7, 7)).collect(), g.int(-20, 20)))
                .collect();
            let mut answers = Vec::new();
            for p in &all {
                let sys = boxed_system(&rows, p, 4);
                if sys.empty {
                    answers.push(None);
                    continue;
                }
                let Some((lo, hi)) = bounds(&sys) else {
                    answers.push(None);
                    continue;
                };
                let e = box_empty_in(&sys, &lo, &hi);
                if p == &all[0] {
                    if e {
                        assert!(rationally_empty(4, &dense(&sys, 4), &lo, &hi), "{rows:?}");
                    }
                    empty += usize::from(e);
                    crossed += usize::from(e && !a_row_below_zero(&sys, &lo, &hi));
                }
                answers.push(Some(e));
            }
            assert!(answers.windows(2).all(|w| w[0] == w[1]), "{rows:?}");
        }
        assert!(empty > crossed && crossed > 0, "{empty} {crossed}");
    }

    #[test]
    fn the_row_test_of_the_box_keeps_every_system_with_an_integer_point() {
        // 3000 systems of 2 to 6 rows over four variables in [-4, 4], each row holding at a
        // random point of the box with slack 0 to 2: the box test never says empty.
        let mut g = Draw(0x38_0c_0d);
        for _ in 0..3000 {
            let p: Vec<i128> = (0..4).map(|_| g.int(-4, 4)).collect();
            let rows: Vec<(Vec<i128>, i128)> = (0..g.int(2, 6))
                .map(|_| {
                    let c: Vec<i128> = (0..4).map(|_| g.int(-7, 7)).collect();
                    let at: i128 = c.iter().zip(&p).map(|(c, x)| c * x).sum();
                    (c, g.int(0, 2) - at)
                })
                .collect();
            let sys = boxed_system(&rows, &[0, 1, 2, 3], 4);
            let (lo, hi) = bounds(&sys).expect("a box holding the point");
            assert!(!box_empty_in(&sys, &lo, &hi), "{rows:?} at {p:?}");
        }
    }

    /// The box test on the rows `Σ a·x + k >= 0` over `n` variables and the box `lo`, `hi`.
    fn box_test(
        n: usize,
        rows: &[(&[(usize, i128)], Int)],
        lo: &[Option<i128>],
        hi: &[Option<i128>],
    ) -> bool {
        let mut sys = System::new(0..n);
        for (a, k) in rows {
            sys.add(Row {
                a: a.iter().map(|(j, c)| (*j, Int::from(*c))).collect(),
                k: k.clone(),
            });
        }
        let lo: Vec<Option<Int>> = lo.iter().map(|b| b.map(Int::from)).collect();
        let hi: Vec<Option<Int>> = hi.iter().map(|b| b.map(Int::from)).collect();
        box_empty_in(&sys, &lo, &hi)
    }

    #[test]
    fn a_row_with_no_variables_is_below_zero_when_its_constant_is() {
        let (lo, hi) = ([Some(0)], [Some(1)]);
        let (mut least, mut most) = (vec![None], vec![None]);
        let to = |b: &[Option<i128>]| -> Vec<Option<Int>> {
            b.iter().map(|b| b.map(Int::from)).collect()
        };
        let (lo, hi) = (to(&lo), to(&hi));
        assert!(row_box_empty(
            &[],
            &Int::from(-1),
            &lo,
            &hi,
            &mut least,
            &mut most
        ));
        assert!(!row_box_empty(
            &[],
            &Int::ZERO,
            &lo,
            &hi,
            &mut least,
            &mut most
        ));
    }

    #[test]
    fn a_variable_with_no_bound_on_the_side_a_row_needs_is_bounded_by_that_row() {
        // x0 has no bound and x1 is in [0, 1]. `2·x0 - x1 - 3 >= 0` needs the upper bound of
        // x0, so it bounds x0 alone: x0 >= 3/2. `-2·x0 - x1 + k >= 0` gives x0 <= k/2, below
        // 3/2 for k = 2 (empty) and not for k = 4 (the point (2, 0)).
        let (lo, hi) = ([None, Some(0)], [None, Some(1)]);
        let a: &[(usize, i128)] = &[(0, 2), (1, -1)];
        let b: &[(usize, i128)] = &[(0, -2), (1, -1)];
        for (k, empty) in [(2, true), (3, false), (4, false)] {
            let rows = [(a, Int::from(-3)), (b, Int::from(k))];
            assert_eq!(box_test(2, &rows, &lo, &hi), empty, "k = {k}");
        }
        // With x2 unbounded too, `x0 + x2 - 100 >= 0` lacks two bounds and bounds neither.
        let c: &[(usize, i128)] = &[(0, 1), (2, 1)];
        let rows = [(a, Int::from(-3)), (c, Int::from(-100))];
        assert!(!box_test(
            3,
            &rows,
            &[None, Some(0), None],
            &[None, Some(1), None]
        ));
    }

    #[test]
    fn bounds_at_the_edge_of_i128_cross_exactly() {
        // `P·x0 + x1 - (P - 1) >= 0` and `-P·x0 + x1 + R >= 0` with P = i128::MAX, x0 in
        // [-1, 1] and x1 in [0, 1]: x0 >= (P - 2)/P and x0 <= (R + 1)/P. Each row's largest
        // value in the box passes i128 and is positive; the bounds cross for R = P - 10 and
        // meet at one point for R = P - 3.
        let p = i128::MAX;
        let (lo, hi) = ([Some(-1), Some(0)], [Some(1), Some(1)]);
        let a: &[(usize, i128)] = &[(0, p), (1, 1)];
        let b: &[(usize, i128)] = &[(0, -p), (1, 1)];
        for (r, empty) in [(p - 10, true), (p - 3, false), (p, false)] {
            let rows = [(a, -&Int::from(p - 1)), (b, Int::from(r))];
            assert_eq!(box_test(2, &rows, &lo, &hi), empty, "R = P - {}", p - r);
        }
    }

    /// A chain of `&&` or `||` as the translator reads it: a leaf is an operand's formula
    /// and whether it is a name's (kept whole), and an inner node joins two chains.
    enum Chain {
        Leaf(Formula, bool),
        Join(Box<Chain>, Box<Chain>),
    }

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    /// A small random formula over `x` and `y`: a constraint `>= 0` or `== 0` on a term
    /// with a small constant, `true`, `false`, a negation, or a conjunction or disjunction
    /// of one to three of these built directly, so one with a single part occurs too.
    fn small(rng: &mut Rng, depth: u32) -> Formula {
        let con = |rng: &mut Rng| {
            let terms: &[(&str, i128)] = match rng.below(3) {
                0 => &[("x", 1)],
                1 => &[("y", -1)],
                _ => &[("x", 1), ("y", 1)],
            };
            let rel = if rng.below(4) == 0 { Rel::Eq } else { Rel::Ge };
            Formula::Con(Con {
                lin: lin(terms, rng.below(3) as i128 - 1),
                rel,
            })
        };
        match rng.below(if depth == 0 { 4 } else { 8 }) {
            0 | 1 => con(rng),
            2 => Formula::top(),
            3 => Formula::bottom(),
            4 => Formula::negate(con(rng)),
            k => {
                let parts = (0..=rng.below(3)).map(|_| small(rng, depth - 1)).collect();
                if k % 2 == 0 {
                    Formula::And(Arc::new(parts))
                } else {
                    Formula::Or(Arc::new(parts))
                }
            }
        }
    }

    fn chain(rng: &mut Rng, depth: u32) -> Chain {
        if depth == 0 || rng.below(3) == 0 {
            Chain::Leaf(small(rng, 2), rng.below(2) == 0)
        } else {
            Chain::Join(
                Box::new(chain(rng, depth - 1)),
                Box::new(chain(rng, depth - 1)),
            )
        }
    }

    /// `Formula::and_keeping` as it was before `Joining`, to compare against.
    pub(super) fn and_keeping_before(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        let mut flat = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            match f {
                Formula::And(ref gs) if gs.is_empty() => {}
                Formula::And(_) if keep(i) => flat.push(f),
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
            Formula::And(Arc::new(out))
        }
    }

    /// `Formula::or_keeping` as it was before `Joining`, to compare against.
    pub(super) fn or_keeping_before(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        let mut out = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            match f {
                Formula::Or(ref gs) if gs.is_empty() => {}
                Formula::Or(_) if keep(i) => out.push(f),
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
            Formula::Or(Arc::new(out))
        }
    }

    /// The chain joined two at a time, as the translator joined it before `Joining`: an
    /// inner node is no name, so its formula is not kept.
    fn two_at_a_time(c: &Chain, and: bool) -> (Formula, bool) {
        match c {
            Chain::Leaf(f, kept) => (f.clone(), *kept),
            Chain::Join(a, b) => {
                let ((fa, ka), (fb, kb)) = (two_at_a_time(a, and), two_at_a_time(b, and));
                let keep = |i: usize| [ka, kb][i];
                let f = if and {
                    and_keeping_before(vec![fa, fb], keep)
                } else {
                    or_keeping_before(vec![fa, fb], keep)
                };
                (f, false)
            }
        }
    }

    /// The chain in one `Joining`, read as `preimage::Tx::chain` reads it.
    fn in_one(c: &Chain, and: bool) -> Formula {
        fn add(c: &Chain, j: &mut Joining) {
            match c {
                Chain::Leaf(f, kept) => j.operand(f.clone(), *kept),
                Chain::Join(a, b) => {
                    let mark = j.mark();
                    add(a, j);
                    add(b, j);
                    j.close(mark);
                }
            }
        }
        let Chain::Join(a, b) = c else {
            unreachable!("a chain of two operands")
        };
        let mut j = Joining::new(and);
        add(a, &mut j);
        add(b, &mut j);
        j.finish()
    }

    /// The formula's tree as built, each node and its parts, with kept parts shown as such:
    /// compare, hash and show read a kept part as flattened, and this must not.
    fn built(f: &Formula) -> String {
        match f {
            Formula::Con(c) => format!("({c})"),
            Formula::Not(g) => format!("!{}", built(g)),
            Formula::And(gs) => format!(
                "and[{}]",
                gs.iter().map(built).collect::<Vec<_>>().join(", ")
            ),
            Formula::Or(gs) => format!(
                "or[{}]",
                gs.iter().map(built).collect::<Vec<_>>().join(", ")
            ),
        }
    }

    #[test]
    fn a_chain_joined_in_one_pass_is_built_as_joined_two_at_a_time() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let mut kinds = std::collections::BTreeSet::new();
        for round in 0..20_000 {
            // A chain is a `&&` or `||` of two operands, never one operand alone.
            let c = Chain::Join(Box::new(chain(&mut rng, 4)), Box::new(chain(&mut rng, 4)));
            for and in [true, false] {
                let (old, _) = two_at_a_time(&c, and);
                let new = in_one(&c, and);
                assert_eq!(built(&new), built(&old), "round {round}, and = {and}");
                kinds.insert(built(&old).chars().take(3).collect::<String>());
            }
        }
        // `true`, `false`, constraints, negations, conjunctions and disjunctions all occur.
        assert!(kinds.len() >= 5, "{kinds:?}");
    }
}
