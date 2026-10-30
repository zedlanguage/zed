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
//! Satisfiability is decided by the Omega test [Omega]: equalities are solved, with Pugh's
//! symmetric remainder where no coefficient is a unit; an inequality-only problem eliminates
//! one variable at a time, exactly when every lower or every upper coefficient of the variable
//! is a unit, and otherwise by the real shadow, the dark shadow and the splinters. A
//! satisfiable problem yields a model: each eliminated variable takes the value nearest zero
//! that its bounds allow under the values of the variables eliminated after it. Disjunctions
//! are split into conjunctions, depth first, in the formula's order.
//!
//! Entailment from premises to a goal is the unsatisfiability of the premises with the negated
//! goal. A product of two symbols is an atom of its own, so the test still decides linear
//! facts; before it, for each product the formulas mention, the premises on its factors are
//! multiplied in pairs, once: a premise on a symbol is a top-level linear inequality of the
//! premises that mentions it, or a bound on the symbol that the linear premises imply.
//!
//! The budgets of step M0.5: a relation takes at most [`VARIABLES`] atoms and [`ATOMS`]
//! constraints, and every intermediate problem at most [`INTERMEDIATE`] constraints; the same
//! bound caps the conjunctions a formula splits into and the splinters one elimination tries.
//! A coefficient past `i128` is past the budget too. Past a budget the relation is dropped and
//! the answer is unknown, which is sound: the written constraint is kept.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use super::interval::{End, IntervalSet};

/// The most atoms a relation takes (step M0.5).
pub const VARIABLES: usize = 16;

/// The most constraints a relation takes (step M0.5).
pub const ATOMS: usize = 64;

/// The most constraints an intermediate problem of an elimination takes (step M0.5).
pub const INTERMEDIATE: usize = 4_096;

/// The most conjunctions a relation a scope keeps splits into (step L1.39): each projection
/// of the relation tests each of them.
pub const KEPT_CONJUNCTIONS: u64 = 64;

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

/// Past a budget: the relation is dropped.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Over;

fn add(a: i128, b: i128) -> Result<i128, Over> {
    a.checked_add(b).ok_or(Over)
}

fn mul(a: i128, b: i128) -> Result<i128, Over> {
    a.checked_mul(b).ok_or(Over)
}

/// A linear term: each atom times its coefficient, plus a constant. No coefficient is zero.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Lin {
    /// The coefficients.
    pub terms: BTreeMap<Atom, i128>,
    /// The constant.
    pub constant: i128,
}

impl Lin {
    /// The constant `k`.
    pub fn constant(k: i128) -> Lin {
        Lin {
            terms: BTreeMap::new(),
            constant: k,
        }
    }

    /// The atom `a`.
    pub fn atom(a: Atom) -> Lin {
        Lin {
            terms: BTreeMap::from([(a, 1)]),
            constant: 0,
        }
    }

    /// `self + other`.
    pub fn plus(&self, other: &Lin) -> Result<Lin, Over> {
        let mut out = self.clone();
        for (a, c) in &other.terms {
            let v = add(*out.terms.get(a).unwrap_or(&0), *c)?;
            if v == 0 {
                out.terms.remove(a);
            } else {
                out.terms.insert(a.clone(), v);
            }
        }
        out.constant = add(out.constant, other.constant)?;
        Ok(out)
    }

    /// `self * k`.
    pub fn times(&self, k: i128) -> Result<Lin, Over> {
        if k == 0 {
            return Ok(Lin::default());
        }
        Ok(Lin {
            terms: self
                .terms
                .iter()
                .map(|(a, c)| Ok((a.clone(), mul(*c, k)?)))
                .collect::<Result<_, _>>()?,
            constant: mul(self.constant, k)?,
        })
    }

    /// `self - other`.
    pub fn minus(&self, other: &Lin) -> Result<Lin, Over> {
        self.plus(&other.times(-1)?)
    }

    /// Whether every atom is a symbol or an auxiliary variable.
    pub fn is_linear(&self) -> bool {
        !self.terms.keys().any(|a| matches!(a, Atom::Product(..)))
    }

    /// The product of two terms, its products of two symbols as atoms; `None` when neither
    /// is a constant and either holds an atom that is not a symbol.
    pub fn product(&self, other: &Lin) -> Option<Result<Lin, Over>> {
        if self.terms.is_empty() {
            return Some(other.times(self.constant));
        }
        if other.terms.is_empty() {
            return Some(self.times(other.constant));
        }
        let syms = |l: &Lin| l.terms.keys().all(|a| matches!(a, Atom::Sym(_)));
        if !syms(self) || !syms(other) {
            return None;
        }
        let go = || -> Result<Lin, Over> {
            let mut out = self.times(other.constant)?;
            for (a, c) in &other.terms {
                let Atom::Sym(x) = a else {
                    unreachable!("checked above")
                };
                out = out.plus(&Lin::atom(a.clone()).times(mul(*c, self.constant)?)?)?;
                for (b, d) in &self.terms {
                    let Atom::Sym(y) = b else {
                        unreachable!("checked above")
                    };
                    out = out.plus(&Lin::atom(Atom::product(x, y)).times(mul(*c, *d)?)?)?;
                }
            }
            Ok(out)
        };
        Some(go())
    }

    /// The value at `values`, each atom absent from it zero.
    fn eval(&self, values: &BTreeMap<Atom, i128>) -> Result<i128, Over> {
        let mut v = self.constant;
        for (a, c) in &self.terms {
            v = add(v, mul(*c, *values.get(a).unwrap_or(&0))?)?;
        }
        Ok(v)
    }
}

impl fmt::Display for Lin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (a, c) in &self.terms {
            let (sign, m) = if *c < 0 { ("-", -c) } else { ("+", *c) };
            match (first, sign) {
                (true, "-") => write!(f, "-")?,
                (true, _) => {}
                (false, s) => write!(f, " {s} ")?,
            }
            if m == 1 {
                write!(f, "{a}")?;
            } else {
                write!(f, "{m} * {a}")?;
            }
            first = false;
        }
        if first {
            write!(f, "{}", self.constant)
        } else if self.constant > 0 {
            write!(f, " + {}", self.constant)
        } else if self.constant < 0 {
            write!(f, " - {}", -self.constant)
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
    pub fn ge(a: &Lin, b: &Lin) -> Result<Con, Over> {
        Ok(Con {
            lin: a.minus(b)?,
            rel: Rel::Ge,
        })
    }

    /// `a == b`.
    pub fn eq(a: &Lin, b: &Lin) -> Result<Con, Over> {
        Ok(Con {
            lin: a.minus(b)?,
            rel: Rel::Eq,
        })
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
        let neg = *first < 0;
        let (mut left, mut right) = (Lin::default(), Lin::default());
        for (a, c) in &self.lin.terms {
            if (*c < 0) == neg {
                left.terms.insert(a.clone(), c.abs());
            } else {
                right.terms.insert(a.clone(), c.abs());
            }
        }
        // left_sign * left - right_sign * right + k (rel) 0, with left positive.
        right.constant = if neg {
            self.lin.constant
        } else {
            -self.lin.constant
        };
        let op = match (self.rel, neg) {
            (Rel::Eq, _) => "==",
            (Rel::Ge, false) => ">=",
            (Rel::Ge, true) => "<=",
        };
        write!(f, "{left} {op} {right}")
    }
}

/// A quantifier-free formula over linear constraints.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
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
        let mut out = Vec::new();
        for f in fs {
            match f {
                Formula::And(gs) => out.extend(gs),
                Formula::Or(ref gs) if gs.is_empty() => return Formula::bottom(),
                g => out.push(g),
            }
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::And(out)
        }
    }

    /// The disjunction, flattened, `false` dropped and `true` absorbing.
    pub fn or(fs: Vec<Formula>) -> Formula {
        let mut out = Vec::new();
        for f in fs {
            match f {
                Formula::Or(gs) => out.extend(gs),
                Formula::And(ref gs) if gs.is_empty() => return Formula::top(),
                g => out.push(g),
            }
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::Or(out)
        }
    }

    /// The disjunction of `a` and `b` with the conjuncts they share taken out of it, so that
    /// joining two narrowings of one relation does not copy the relation into each disjunct.
    pub fn either(a: &Formula, b: &Formula) -> Formula {
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
        let rest = |p: &[Formula]| {
            Formula::and(p.iter().filter(|g| !shared.contains(g)).cloned().collect())
        };
        let mut out: Vec<Formula> = pa.iter().filter(|g| shared.contains(g)).cloned().collect();
        out.push(Formula::or(vec![rest(pa), rest(pb)]));
        Formula::and(out)
    }

    /// The conjuncts of `self`, in order, while they hold at most [`ATOMS`] constraints and
    /// split into at most [`KEPT_CONJUNCTIONS`] conjunctions in all. Past the constraints a
    /// relation is over the budget of step M0.5 for every use, and past the conjunctions each
    /// projection of it costs a test of each; a conjunction implies each part of it.
    pub fn bounded(self) -> Formula {
        if self.cons().len() <= ATOMS && self.split_count(false) <= KEPT_CONJUNCTIONS {
            return self;
        }
        let Formula::And(gs) = self else {
            return Formula::top();
        };
        let (mut cons, mut split) = (0, 1u64);
        let kept = gs
            .into_iter()
            .filter(|g| {
                let (n, k) = (
                    cons + g.cons().len(),
                    split.saturating_mul(g.split_count(false)),
                );
                let fits = n <= ATOMS && k <= KEPT_CONJUNCTIONS;
                if fits {
                    (cons, split) = (n, k);
                }
                fits
            })
            .collect();
        Formula::and(kept)
    }

    /// How many conjunctions the formula, negated when `neg`, splits into before any is
    /// found unsatisfiable, saturating.
    fn split_count(&self, neg: bool) -> u64 {
        match (self, neg) {
            (Formula::Con(c), true) if c.rel == Rel::Eq => 2,
            (Formula::Con(_), _) => 1,
            (Formula::Not(g), _) => g.split_count(!neg),
            (Formula::And(gs), false) | (Formula::Or(gs), true) => gs
                .iter()
                .fold(1u64, |a, g| a.saturating_mul(g.split_count(neg))),
            (Formula::And(gs), true) | (Formula::Or(gs), false) => gs
                .iter()
                .fold(0u64, |a, g| a.saturating_add(g.split_count(neg))),
        }
    }

    /// The negation, with double negations and constants removed.
    pub fn negate(f: Formula) -> Formula {
        match f {
            Formula::Not(g) => *g,
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

    fn walk<'a>(&'a self, f: &mut dyn FnMut(&'a Con)) {
        match self {
            Formula::Con(c) => f(c),
            Formula::Not(g) => g.walk(f),
            Formula::And(gs) | Formula::Or(gs) => gs.iter().for_each(|g| g.walk(f)),
        }
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
    pub fn holds(&self, values: &BTreeMap<Atom, i128>) -> Result<bool, Over> {
        let mut vs = values.clone();
        for a in self.atoms() {
            if let Atom::Product(x, y) = &a {
                let v = |s: &Arc<str>| *values.get(&Atom::Sym(s.clone())).unwrap_or(&0);
                vs.insert(a.clone(), mul(v(x), v(y))?);
            }
        }
        self.holds_as(&vs)
    }

    /// Whether the formula holds at `values`, each atom read as its value there.
    fn holds_as(&self, vs: &BTreeMap<Atom, i128>) -> Result<bool, Over> {
        Ok(match self {
            Formula::Con(c) => {
                let v = c.lin.eval(vs)?;
                if c.rel == Rel::Eq { v == 0 } else { v >= 0 }
            }
            Formula::Not(g) => !g.holds_as(vs)?,
            Formula::And(gs) => {
                for g in gs {
                    if !g.holds_as(vs)? {
                        return Ok(false);
                    }
                }
                true
            }
            Formula::Or(gs) => {
                for g in gs {
                    if g.holds_as(vs)? {
                        return Ok(true);
                    }
                }
                false
            }
        })
    }

    /// The top-level conjuncts.
    fn conjuncts(&self) -> Vec<&Formula> {
        match self {
            Formula::And(gs) => gs.iter().collect(),
            g => vec![g],
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let part = |g: &Formula, f: &mut fmt::Formatter<'_>| match g {
            Formula::And(gs) | Formula::Or(gs) if gs.len() > 1 => write!(f, "({g})"),
            _ => write!(f, "{g}"),
        };
        match self {
            Formula::Con(c) => write!(f, "{c}"),
            Formula::Not(g) => {
                write!(f, "!")?;
                match &**g {
                    Formula::Con(_) | Formula::And(_) | Formula::Or(_) => write!(f, "({g})"),
                    _ => write!(f, "{g}"),
                }
            }
            Formula::And(gs) | Formula::Or(gs) if gs.is_empty() => {
                write!(f, "{}", matches!(self, Formula::And(_)))
            }
            Formula::And(gs) | Formula::Or(gs) => {
                let sep = if matches!(self, Formula::And(_)) {
                    " && "
                } else {
                    " || "
                };
                for (i, g) in gs.iter().enumerate() {
                    if i > 0 {
                        write!(f, "{sep}")?;
                    }
                    part(g, f)?;
                }
                Ok(())
            }
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
pub type Model = BTreeMap<Atom, i128>;

/// Whether `f` holds somewhere, and where.
pub fn satisfiable(f: &Formula) -> Result<Option<Model>, Over> {
    let atoms: Vec<Atom> = f.atoms().into_iter().collect();
    if atoms.len() > VARIABLES || f.cons().len() > ATOMS {
        return Err(Over);
    }
    let index: BTreeMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    let mut split = Split {
        index: &index,
        leaves: 0,
        solver: Omega {
            next: atoms.len(),
            splinters: 0,
        },
    };
    let found = split.go(vec![(f.clone(), true)], Vec::new())?;
    Ok(found.map(|m| {
        atoms
            .iter()
            .enumerate()
            .filter_map(|(i, a)| m.get(&i).map(|v| (a.clone(), *v)))
            .collect()
    }))
}

/// The disjunctions of a formula split into conjunctions, depth first.
struct Split<'a> {
    index: &'a BTreeMap<&'a Atom, usize>,
    leaves: usize,
    solver: Omega,
}

impl Split<'_> {
    /// Whether the pending formulas, each with the sign it is taken with, hold together with
    /// the rows gathered so far.
    fn go(
        &mut self,
        mut pending: Vec<(Formula, bool)>,
        rows: Vec<Row>,
    ) -> Result<Option<Vals>, Over> {
        let Some((f, sign)) = pending.pop() else {
            self.leaves += 1;
            if self.leaves > INTERMEDIATE {
                return Err(Over);
            }
            let (eqs, ges): (Vec<Row>, Vec<Row>) = rows.into_iter().partition(|r| r.eq);
            return self.solver.solve(eqs, ges);
        };
        match (f, sign) {
            (Formula::Not(g), s) => {
                pending.push((*g, !s));
                self.go(pending, rows)
            }
            (Formula::And(gs), true) | (Formula::Or(gs), false) => {
                pending.extend(gs.into_iter().rev().map(|g| (g, sign)));
                self.go(pending, rows)
            }
            (Formula::And(gs), false) | (Formula::Or(gs), true) => {
                for g in gs {
                    let mut p = pending.clone();
                    p.push((g, sign));
                    if let Some(m) = self.go(p, rows.clone())? {
                        return Ok(Some(m));
                    }
                }
                Ok(None)
            }
            (Formula::Con(c), true) => {
                let mut rows = rows;
                rows.push(self.row(&c.lin, c.rel == Rel::Eq));
                self.go(pending, rows)
            }
            (Formula::Con(c), false) => {
                // Not `t >= 0` is `-t - 1 >= 0`; not `t == 0` is `t >= 1` or `-t >= 1`.
                let neg = self.row(&c.lin, false).neg_minus_one()?;
                if c.rel == Rel::Ge {
                    let mut rows = rows;
                    rows.push(neg);
                    return self.go(pending, rows);
                }
                let pos = {
                    let mut r = self.row(&c.lin, false);
                    r.k = add(r.k, -1)?;
                    r
                };
                for r in [pos, neg] {
                    let mut rs = rows.clone();
                    rs.push(r);
                    if let Some(m) = self.go(pending.clone(), rs)? {
                        return Ok(Some(m));
                    }
                }
                Ok(None)
            }
        }
    }

    fn row(&self, l: &Lin, eq: bool) -> Row {
        Row {
            a: l.terms.iter().map(|(a, c)| (self.index[a], *c)).collect(),
            k: l.constant,
            eq,
        }
    }
}

/// The values of the solver's variables, each absent one zero.
type Vals = BTreeMap<usize, i128>;

/// `Σ a[i]·x[i] + k`, compared with zero by `==` or `>=`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Row {
    a: BTreeMap<usize, i128>,
    k: i128,
    eq: bool,
}

/// What normalizing a row gives.
enum Norm {
    True,
    False,
    Row(Row),
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Row {
    fn neg_minus_one(&self) -> Result<Row, Over> {
        Ok(Row {
            a: self.a.iter().map(|(i, c)| (*i, -c)).collect(),
            k: add(-self.k, -1)?,
            eq: false,
        })
    }

    fn eval(&self, m: &Vals) -> Result<i128, Over> {
        let mut v = self.k;
        for (i, c) in &self.a {
            v = add(v, mul(*c, *m.get(i).unwrap_or(&0))?)?;
        }
        Ok(v)
    }

    /// The row divided by the gcd of its coefficients, an inequality's constant rounded down.
    fn normal(mut self) -> Norm {
        let g = self.a.values().fold(0, |g, c| gcd(g, *c));
        if g == 0 {
            return match (self.eq, self.k) {
                (true, 0) => Norm::True,
                (false, k) if k >= 0 => Norm::True,
                _ => Norm::False,
            };
        }
        if self.eq && self.k % g != 0 {
            return Norm::False;
        }
        for c in self.a.values_mut() {
            *c /= g;
        }
        self.k = self.k.div_euclid(g);
        Norm::Row(self)
    }

    /// The row with `x[j]` replaced by `def`.
    fn subst(&self, j: usize, def: &Row) -> Result<Row, Over> {
        let Some(&c) = self.a.get(&j) else {
            return Ok(self.clone());
        };
        let mut out = self.clone();
        out.a.remove(&j);
        for (i, d) in &def.a {
            let v = add(*out.a.get(i).unwrap_or(&0), mul(c, *d)?)?;
            if v == 0 {
                out.a.remove(i);
            } else {
                out.a.insert(*i, v);
            }
        }
        out.k = add(out.k, mul(c, def.k)?)?;
        Ok(out)
    }

    /// The row without `x[j]`.
    fn rest(&self, j: usize) -> Row {
        let mut r = self.clone();
        r.a.remove(&j);
        r
    }
}

/// Pugh's symmetric remainder: `a - m·floor(a/m + 1/2)`.
fn mod_hat(a: i128, m: i128) -> i128 {
    let r = a.rem_euclid(m);
    if 2 * r >= m { r - m } else { r }
}

/// The Omega test.
struct Omega {
    /// The next fresh variable.
    next: usize,
    /// The splinters tried so far.
    splinters: usize,
}

impl Omega {
    fn solve(&mut self, eqs: Vec<Row>, ges: Vec<Row>) -> Result<Option<Vals>, Over> {
        if eqs.len() + ges.len() > INTERMEDIATE {
            return Err(Over);
        }
        let mut es = Vec::new();
        for r in eqs {
            match r.normal() {
                Norm::False => return Ok(None),
                Norm::True => {}
                Norm::Row(r) => es.push(r),
            }
        }
        let mut gs = Vec::new();
        for r in ges {
            match r.normal() {
                Norm::False => return Ok(None),
                Norm::True => {}
                Norm::Row(r) => gs.push(r),
            }
        }
        if let Some(e) = es.pop() {
            return self.equality(e, es, gs);
        }
        self.inequalities(gs)
    }

    fn equality(&mut self, e: Row, es: Vec<Row>, gs: Vec<Row>) -> Result<Option<Vals>, Over> {
        if let Some((&j, &aj)) = e.a.iter().find(|(_, c)| c.abs() == 1) {
            // `aj·x + rest == 0`, so `x = -aj·rest`.
            let rest = e.rest(j);
            let def = Row {
                a: rest.a.iter().map(|(i, c)| (*i, -aj * c)).collect(),
                k: -aj * rest.k,
                eq: true,
            };
            let es = es
                .iter()
                .map(|r| r.subst(j, &def))
                .collect::<Result<_, _>>()?;
            let gs = gs
                .iter()
                .map(|r| r.subst(j, &def))
                .collect::<Result<_, _>>()?;
            let Some(mut m) = self.solve(es, gs)? else {
                return Ok(None);
            };
            let v = def.eval(&m)?;
            m.insert(j, v);
            return Ok(Some(m));
        }
        // No unit coefficient: Pugh's step with a fresh variable `s`, whose new equality has
        // a unit coefficient at the variable with the least coefficient.
        let (_, &least) = e.a.iter().min_by_key(|(_, c)| c.abs()).expect("a variable");
        let m = add(least.abs(), 1)?;
        let s = self.next;
        self.next += 1;
        let mut a: BTreeMap<usize, i128> =
            e.a.iter()
                .map(|(i, c)| (*i, mod_hat(*c, m)))
                .filter(|(_, c)| *c != 0)
                .collect();
        a.insert(s, -m);
        let hat = Row {
            a,
            k: mod_hat(e.k, m),
            eq: true,
        };
        let mut es = es;
        es.push(e);
        es.push(hat);
        self.solve(es, gs)
    }

    fn inequalities(&mut self, gs: Vec<Row>) -> Result<Option<Vals>, Over> {
        // Of two rows with one set of coefficients, the tighter; a row and its opposite
        // meet in an equality, or nowhere.
        let mut tight: BTreeMap<BTreeMap<usize, i128>, i128> = BTreeMap::new();
        for r in gs {
            let k = tight.entry(r.a).or_insert(r.k);
            *k = (*k).min(r.k);
        }
        for (a, k) in &tight {
            let opp: BTreeMap<usize, i128> = a.iter().map(|(i, c)| (*i, -c)).collect();
            if let Some(k2) = tight.get(&opp) {
                let s = add(*k, *k2)?;
                if s < 0 {
                    return Ok(None);
                }
                if s == 0 {
                    let eq = Row {
                        a: a.clone(),
                        k: *k,
                        eq: true,
                    };
                    let rest: Vec<Row> = tight
                        .iter()
                        .filter(|(b, _)| *b != a && **b != opp)
                        .map(|(b, k)| Row {
                            a: b.clone(),
                            k: *k,
                            eq: false,
                        })
                        .collect();
                    return self.solve(vec![eq], rest);
                }
            }
        }
        let gs: Vec<Row> = tight
            .into_iter()
            .map(|(a, k)| Row { a, k, eq: false })
            .collect();
        if gs.is_empty() {
            return Ok(Some(Vals::new()));
        }
        let vars: BTreeSet<usize> = gs.iter().flat_map(|r| r.a.keys().copied()).collect();
        // A variable bounded on one side only: its rows can always be met.
        for &j in &vars {
            let signs: BTreeSet<bool> = gs
                .iter()
                .filter_map(|r| r.a.get(&j).map(|c| *c > 0))
                .collect();
            if signs.len() == 1 {
                let (with, without): (Vec<Row>, Vec<Row>) =
                    gs.into_iter().partition(|r| r.a.contains_key(&j));
                let Some(mut m) = self.solve(Vec::new(), without)? else {
                    return Ok(None);
                };
                let v = choose(&with, j, &m)?;
                m.insert(j, v);
                return Ok(Some(m));
            }
        }
        // Eliminate the variable that is exact with the fewest pairs, or else the one with
        // the fewest pairs.
        let cost = |j: usize| {
            let lo: Vec<i128> = gs
                .iter()
                .filter_map(|r| r.a.get(&j).filter(|c| **c > 0).copied())
                .collect();
            let hi: Vec<i128> = gs
                .iter()
                .filter_map(|r| r.a.get(&j).filter(|c| **c < 0).map(|c| -c))
                .collect();
            let exact = lo.iter().all(|c| *c == 1) || hi.iter().all(|c| *c == 1);
            (!exact, lo.len() * hi.len(), j)
        };
        let j = vars
            .iter()
            .copied()
            .min_by_key(|j| cost(*j))
            .expect("a variable");
        let (inexact, pairs, _) = cost(j);
        let (with, others): (Vec<Row>, Vec<Row>) =
            gs.iter().cloned().partition(|r| r.a.contains_key(&j));
        if others.len() + pairs > INTERMEDIATE {
            return Err(Over);
        }
        let lowers: Vec<&Row> = with.iter().filter(|r| r.a[&j] > 0).collect();
        let uppers: Vec<&Row> = with.iter().filter(|r| r.a[&j] < 0).collect();
        // Lower `a·x + l >= 0` and upper `-b·x + u >= 0` give `a·u + b·l >= 0`, and the dark
        // shadow `a·u + b·l >= (a - 1)(b - 1)`.
        let shadow = |dark: bool| -> Result<Vec<Row>, Over> {
            let mut out = others.clone();
            for lo in &lowers {
                for hi in &uppers {
                    let (a, b) = (lo.a[&j], -hi.a[&j]);
                    let mut r = Row {
                        a: BTreeMap::new(),
                        k: 0,
                        eq: false,
                    };
                    for (src, f) in [(hi.rest(j), a), (lo.rest(j), b)] {
                        for (i, c) in &src.a {
                            let v = add(*r.a.get(i).unwrap_or(&0), mul(*c, f)?)?;
                            if v == 0 {
                                r.a.remove(i);
                            } else {
                                r.a.insert(*i, v);
                            }
                        }
                        r.k = add(r.k, mul(src.k, f)?)?;
                    }
                    if dark {
                        r.k = add(r.k, -mul(a - 1, b - 1)?)?;
                    }
                    out.push(r);
                }
            }
            Ok(out)
        };
        let pick = |m: Option<Vals>| -> Result<Option<Vals>, Over> {
            let Some(mut m) = m else { return Ok(None) };
            let v = choose(&with, j, &m)?;
            m.insert(j, v);
            Ok(Some(m))
        };
        if !inexact {
            let r = self.solve(Vec::new(), shadow(false)?)?;
            return pick(r);
        }
        if self.solve(Vec::new(), shadow(false)?)?.is_none() {
            return Ok(None);
        }
        if let Some(m) = self.solve(Vec::new(), shadow(true)?)? {
            return pick(Some(m));
        }
        // The splinters: `a·x + l == i` for `0 <= i <= (m·a - m - a) / m`, `m` the largest
        // upper coefficient.
        let big = uppers
            .iter()
            .map(|r| -r.a[&j])
            .max()
            .expect("an upper bound");
        for lo in &lowers {
            let a = lo.a[&j];
            let top = (mul(big, a)? - big - a).div_euclid(big);
            for i in 0..=top {
                self.splinters += 1;
                if self.splinters > INTERMEDIATE {
                    return Err(Over);
                }
                let mut e = (*lo).clone();
                e.k = add(e.k, -i)?;
                e.eq = true;
                if let Some(m) = self.solve(vec![e], gs.clone())? {
                    return Ok(Some(m));
                }
            }
        }
        Ok(None)
    }
}

/// The value nearest zero for `x[j]` that the rows allow at the values `m` of the others.
fn choose(rows: &[Row], j: usize, m: &Vals) -> Result<i128, Over> {
    let (mut lo, mut hi) = (None::<i128>, None::<i128>);
    for r in rows {
        let c = r.a[&j];
        let rest = r.rest(j).eval(m)?;
        // `c·x + rest >= 0`.
        if c > 0 {
            let b = (-rest).div_euclid(c) + i128::from((-rest).rem_euclid(c) != 0);
            lo = Some(lo.map_or(b, |l| l.max(b)));
        } else {
            let b = rest.div_euclid(-c);
            hi = Some(hi.map_or(b, |h| h.min(b)));
        }
    }
    Ok(match (lo, hi) {
        (Some(l), _) if l > 0 => l,
        (_, Some(h)) if h < 0 => h,
        _ => 0,
    })
}

/// The values of a symbol over the formula's points, as a union of intervals: the hull of
/// the symbol's values over each conjunction the formula splits into. A bound past `i64` is
/// read as no bound.
pub fn project(f: &Formula, sym: &Atom) -> Result<IntervalSet, Over> {
    project_each(f, std::slice::from_ref(sym))?.remove(0)
}

/// [`project`] onto each of `syms`, splitting the formula into conjunctions once: one result
/// for each symbol, so that a symbol past a budget leaves the others projected.
pub fn project_each(f: &Formula, syms: &[Atom]) -> Result<Vec<Result<IntervalSet, Over>>, Over> {
    let mut out: Vec<Result<IntervalSet, Over>> =
        syms.iter().map(|_| Ok(IntervalSet::empty())).collect();
    for (conj, model) in conjunctions(f)? {
        let c = Formula::and(conj.into_iter().map(Formula::Con).collect());
        for (o, sym) in out.iter_mut().zip(syms) {
            if let Ok(acc) = o {
                *o = hull_from(&c, sym, &model).map(|h| acc.join(&h));
            }
        }
    }
    Ok(out)
}

/// The conjunctions a formula splits into, each a list of constraints with a point that
/// meets it, those found unsatisfiable dropped.
fn conjunctions(f: &Formula) -> Result<Vec<(Vec<Con>, Model)>, Over> {
    fn go(
        pending: &mut Vec<(Formula, bool)>,
        cons: Vec<Con>,
        out: &mut Vec<Vec<Con>>,
    ) -> Result<(), Over> {
        let Some((f, sign)) = pending.pop() else {
            if out.len() >= INTERMEDIATE {
                return Err(Over);
            }
            out.push(cons);
            return Ok(());
        };
        let both = |pending: &mut Vec<(Formula, bool)>,
                    out: &mut Vec<Vec<Con>>,
                    gs: Vec<(Formula, bool)>,
                    cons: Vec<Con>|
         -> Result<(), Over> {
            for g in gs {
                let mut p = pending.clone();
                p.push(g);
                go(&mut p, cons.clone(), out)?;
            }
            Ok(())
        };
        match (f, sign) {
            (Formula::Not(g), s) => {
                pending.push((*g, !s));
                go(pending, cons, out)
            }
            (Formula::And(gs), true) | (Formula::Or(gs), false) => {
                pending.extend(gs.into_iter().rev().map(|g| (g, sign)));
                go(pending, cons, out)
            }
            (Formula::And(gs), false) | (Formula::Or(gs), true) => both(
                pending,
                out,
                gs.into_iter().map(|g| (g, sign)).collect(),
                cons,
            ),
            (Formula::Con(c), true) => {
                let mut cons = cons;
                cons.push(c);
                go(pending, cons, out)
            }
            (Formula::Con(c), false) => {
                let one = Lin::constant(1);
                let neg = Con::ge(&Lin::default(), &c.lin.plus(&one)?)?;
                if c.rel == Rel::Ge {
                    let mut cons = cons;
                    cons.push(neg);
                    return go(pending, cons, out);
                }
                let pos = Con::ge(&c.lin, &one)?;
                for d in [pos, neg] {
                    let mut cs = cons.clone();
                    cs.push(d);
                    go(&mut pending.clone(), cs, out)?;
                }
                Ok(())
            }
        }
    }
    let mut out = Vec::new();
    go(&mut vec![(f.clone(), true)], Vec::new(), &mut out)?;
    let mut live = Vec::new();
    for c in out {
        let f = Formula::and(c.iter().cloned().map(Formula::Con).collect());
        if let Some(m) = satisfiable(&f)? {
            live.push((c, m));
        }
    }
    Ok(live)
}

/// The least and greatest values of a symbol over a conjunction.
fn hull(c: &Formula, sym: &Atom) -> Result<IntervalSet, Over> {
    match satisfiable(c)? {
        Some(m) => hull_from(c, sym, &m),
        None => Ok(IntervalSet::empty()),
    }
}

/// [`hull`] given a point `m` of the conjunction, found by the monotone questions "is there a
/// point with the symbol at most `v`" and "at least `v`". Each bound is searched outward
/// from the point's value with steps that double, then by bisection, so it takes O(log d)
/// questions for a bound at distance d, and one when the symbol is unbounded that way.
fn hull_from(c: &Formula, sym: &Atom, m: &Model) -> Result<IntervalSet, Over> {
    let x = Lin::atom(sym.clone());
    let at = *m.get(sym).unwrap_or(&0);
    let with = |con: Con| -> Result<bool, Over> {
        Ok(satisfiable(&Formula::and(vec![c.clone(), Formula::Con(con)]))?.is_some())
    };
    let below = |v: i128| with(Con::ge(&Lin::constant(v), &x)?);
    let above = |v: i128| with(Con::ge(&x, &Lin::constant(v))?);
    let (min, max) = (i128::from(i64::MIN), i128::from(i64::MAX));
    // The last value of the monotone `holds` that is true, moving from `start` (true) by
    // `dir` toward `end` (false).
    let edge = |holds: &dyn Fn(i128) -> Result<bool, Over>,
                start: i128,
                end: i128,
                dir: i128|
     -> Result<i128, Over> {
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
pub fn member(sym: &Atom, s: &IntervalSet) -> Result<Formula, Over> {
    within(&Lin::atom(sym.clone()), s)
}

/// The values of the term `l` in the set `s`, as a formula.
pub fn within(l: &Lin, s: &IntervalSet) -> Result<Formula, Over> {
    let mut pieces = Vec::new();
    for &(lo, hi) in s.pieces() {
        let mut both = Vec::new();
        if let End::Fin(v) = lo {
            both.push(Formula::Con(Con::ge(l, &Lin::constant(v.into()))?));
        }
        if let End::Fin(v) = hi {
            both.push(Formula::Con(Con::ge(&Lin::constant(v.into()), l)?));
        }
        pieces.push(Formula::and(both));
    }
    Ok(Formula::or(pieces))
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
    /// A budget was passed, and the relation dropped.
    Dropped,
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
            Entailment::Dropped => write!(f, "dropped: past the budget of step M0.5"),
        }
    }
}

/// Whether `premises` entail `goal` (rung 2).
pub fn entails(premises: &Relation, goal: &Relation) -> Entailment {
    entails_inner(premises, goal).unwrap_or(Entailment::Dropped)
}

fn entails_inner(premises: &Relation, goal: &Relation) -> Result<Entailment, Over> {
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
        .map(|(a, v)| (a.clone(), *v))
        .collect();
    if real.holds(&syms)? {
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
fn products(premises: &Relation, goal: &Relation) -> Result<Vec<Formula>, Over> {
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
                linear.push(c.lin.times(-1)?);
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
                set.push(x.minus(&Lin::constant(l.into()))?);
            }
            if let End::Fin(h) = hi {
                set.push(Lin::constant(h.into()).minus(&x)?);
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
                        lin: p?,
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
            l = l.plus(&Lin::atom(sym(s)).times(*c).unwrap()).unwrap();
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
    fn the_dark_shadow_and_the_splinters_decide_integer_points() {
        // 2x = 2y + 1 has real points and no integer point.
        let f = Formula::Con(Con {
            lin: lin(&[("x", 2), ("y", -2)], -1),
            rel: Rel::Eq,
        });
        assert_eq!(satisfiable(&f), Ok(None));
        // 3 <= 2x <= 3 has none either; 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has none
        // (Pugh's example).
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
    }
}
