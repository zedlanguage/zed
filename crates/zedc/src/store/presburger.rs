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
//! Satisfiability is decided by the Omega test [Omega] on the fragment it settles in
//! polynomial time, with no budget (docs/thresholds.md, replacement 4). Equalities are
//! solved, with Pugh's symmetric remainder where no coefficient is a unit. An
//! inequality-only problem eliminates one variable at a time, and only while the system
//! holds no more rows than it was given: each step removes a variable and the rows never
//! pass the input's count. An elimination is exact when every lower or every upper
//! coefficient of the variable is a unit; otherwise a point of the dark shadow is a point of
//! the problem and an empty real shadow, read over the rationals, shows the problem empty, and
//! between the two the question is undecided. A satisfiable problem yields a model: each
//! eliminated variable takes the value nearest zero that its bounds allow under the values of
//! the variables eliminated after it.
//!
//! A formula with disjunctions is not split into all its conjunctions. Its top-level
//! constraints are the base; a disjunct whose own top-level constraints meet the base nowhere
//! is removed, and a disjunction with one disjunct left adds it to the base, until nothing is
//! removed: each round removes a disjunct, so the rounds are at most the disjuncts. No
//! disjunct left is no point. A point is then sought by taking, for each disjunction in turn,
//! the first disjunct that meets the base with the disjuncts already taken. Where none does,
//! each disjunct whose addition to the base empties it by the rule above is removed, until
//! none is, and the search runs again; where it fails again, the question is undecided. A
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
//! An undecided question, or a coefficient past `i128`, leaves the relation unused, which is
//! sound: the written constraint is kept.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use super::interval::{End, IntervalSet};

/// The projection onto each symbol, in order; `Err(Over)` where it is undecided.
type Projections = Vec<Result<IntervalSet, Over>>;

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
        let mut flat = Vec::new();
        for f in fs {
            match f {
                Formula::And(gs) => flat.extend(gs),
                Formula::Or(ref gs) if gs.is_empty() => return Formula::bottom(),
                g => flat.push(g),
            }
        }
        // Of two constraints on one term, the tighter alone, in the place of the first.
        let mut out: Vec<Formula> = Vec::new();
        let mut at: BTreeMap<(BTreeMap<Atom, i128>, Rel), usize> = BTreeMap::new();
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

    /// The formula with every constraint that mentions `sym`, alone or in a product,
    /// replaced by `true` where it occurs under an even number of negations and by `false`
    /// where under an odd number: a formula implied by `self` that says nothing of `sym`.
    pub fn forget(&self, sym: &Arc<str>) -> Formula {
        fn go(f: &Formula, sym: &Arc<str>, pos: bool) -> Formula {
            match f {
                Formula::Con(c) => {
                    let mentions = c.lin.terms.keys().any(|a| match a {
                        Atom::Sym(n) => n == sym,
                        Atom::Product(x, y) => x == sym || y == sym,
                        Atom::Aux(_) => false,
                    });
                    match (mentions, pos) {
                        (false, _) => f.clone(),
                        (true, true) => Formula::top(),
                        (true, false) => Formula::bottom(),
                    }
                }
                Formula::Not(g) => Formula::negate(go(g, sym, !pos)),
                Formula::And(gs) => Formula::and(gs.iter().map(|g| go(g, sym, pos)).collect()),
                Formula::Or(gs) => Formula::or(gs.iter().map(|g| go(g, sym, pos)).collect()),
            }
        }
        go(self, sym, true)
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
    let Some(p) = propagate(f)? else {
        return Ok(None);
    };
    if let Ok(m) = pick(&p) {
        return Ok(Some(m));
    }
    match probe(p)? {
        None => Ok(None),
        Some(p) => pick(&p).map(Some),
    }
}

/// A point of `p`, taking for each disjunction in turn the first disjunct that meets the
/// constraints taken so far, or `Over` when none does.
fn pick(p: &Parts) -> Result<Model, Over> {
    let mut model = solve(&p.cons)?.ok_or(Over)?;
    let (mut acc, mut queue) = (p.cons.clone(), p.ors.clone());
    while let Some(ds) = queue.pop() {
        let mut taken = None;
        for d in ds {
            let mut cs = acc.clone();
            cs.extend(lits(&d));
            if let Ok(Some(m)) = solve(&cs) {
                taken = Some((d, m));
                break;
            }
        }
        let Some((d, m)) = taken else {
            return Err(Over);
        };
        model = m;
        let mut q = Parts::default();
        q.add(d);
        acc.extend(q.cons);
        queue.extend(q.ors);
    }
    Ok(model)
}

/// `p` with each disjunct removed whose addition, propagated, leaves no point, until none is
/// removed, or `None` when `p` has no point. Each round but the last removes a disjunct, and
/// each tests every disjunct by one propagation, so the work is polynomial in the disjuncts.
fn probe(mut p: Parts) -> Result<Option<Parts>, Over> {
    loop {
        let mut changed = false;
        for i in 0..p.ors.len() {
            let ds = std::mem::take(&mut p.ors[i]);
            let n = ds.len();
            let live: Vec<Formula> = ds
                .into_iter()
                .filter(|d| {
                    let mut q = Parts {
                        cons: p.cons.clone(),
                        ors: p.ors.iter().filter(|o| !o.is_empty()).cloned().collect(),
                    };
                    q.add(d.clone());
                    !matches!(settle(q), Ok(None))
                })
                .collect();
            changed |= live.len() < n;
            if live.is_empty() {
                return Ok(None);
            }
            p.ors[i] = live;
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

/// A formula in negation normal form as its top-level constraints and its top-level
/// disjunctions, each a list of disjuncts.
#[derive(Clone, Default)]
struct Parts {
    cons: Vec<Con>,
    ors: Vec<Vec<Formula>>,
}

impl Parts {
    /// Adds a formula in negation normal form.
    fn add(&mut self, f: Formula) {
        match f {
            Formula::Con(c) => self.cons.push(c),
            Formula::And(gs) => gs.into_iter().for_each(|g| self.add(g)),
            Formula::Or(gs) => self.ors.push(gs),
            Formula::Not(_) => unreachable!("a formula in negation normal form"),
        }
    }
}

/// `f`, negated when `!sign`, with each negation pushed to the constraints: not `t >= 0` is
/// `-t - 1 >= 0`, and not `t == 0` is `t >= 1 || -t >= 1`.
fn nnf(f: &Formula, sign: bool) -> Result<Formula, Over> {
    Ok(match (f, sign) {
        (Formula::Not(g), s) => nnf(g, !s)?,
        (Formula::And(gs), true) | (Formula::Or(gs), false) => {
            Formula::and(gs.iter().map(|g| nnf(g, sign)).collect::<Result<_, _>>()?)
        }
        (Formula::And(gs), false) | (Formula::Or(gs), true) => {
            Formula::or(gs.iter().map(|g| nnf(g, sign)).collect::<Result<_, _>>()?)
        }
        (Formula::Con(c), true) => Formula::Con(c.clone()),
        (Formula::Con(c), false) => {
            let one = Lin::constant(1);
            let neg = Formula::Con(Con::ge(&Lin::default(), &c.lin.plus(&one)?)?);
            if c.rel == Rel::Ge {
                neg
            } else {
                Formula::or(vec![Formula::Con(Con::ge(&c.lin, &one)?), neg])
            }
        }
    })
}

/// The top-level constraints of a formula in negation normal form.
fn lits(f: &Formula) -> Vec<Con> {
    match f {
        Formula::Con(c) => vec![c.clone()],
        Formula::And(gs) => gs.iter().flat_map(lits).collect(),
        _ => Vec::new(),
    }
}

/// The formula's base and disjunctions once no disjunct can be removed, or `None` when it has
/// no point. A disjunct is removed when its top-level constraints meet the base nowhere; a
/// disjunction left with one disjunct adds it to the base. Each round but the last removes a
/// disjunct, so there are at most as many rounds as disjuncts, each a test of every disjunct.
fn propagate(f: &Formula) -> Result<Option<Parts>, Over> {
    let mut p = Parts::default();
    p.add(nnf(f, true)?);
    settle(p)
}

/// [`propagate`] from parts.
fn settle(mut p: Parts) -> Result<Option<Parts>, Over> {
    loop {
        if solve(&p.cons)?.is_none() {
            return Ok(None);
        }
        let mut changed = false;
        let mut kept = Vec::new();
        for ds in std::mem::take(&mut p.ors) {
            let n = ds.len();
            let mut live: Vec<Formula> = ds
                .into_iter()
                .filter(|d| {
                    let mut cs = p.cons.clone();
                    cs.extend(lits(d));
                    !matches!(solve(&cs), Ok(None))
                })
                .collect();
            changed |= live.len() < n;
            match live.len() {
                0 => return Ok(None),
                1 => {
                    let mut q = Parts::default();
                    q.add(live.pop().expect("one"));
                    p.cons.extend(q.cons);
                    kept.extend(q.ors);
                }
                _ => kept.push(live),
            }
        }
        p.ors = kept;
        if !changed {
            return Ok(Some(p));
        }
    }
}

/// Whether a conjunction of constraints holds somewhere, and where.
fn solve(cons: &[Con]) -> Result<Option<Model>, Over> {
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let index: BTreeMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    let (eqs, ges): (Vec<Row>, Vec<Row>) = cons
        .iter()
        .map(|c| Row {
            a: c.lin.terms.iter().map(|(a, k)| (index[a], *k)).collect(),
            k: c.lin.constant,
            eq: c.rel == Rel::Eq,
        })
        .partition(|r| r.eq);
    let mut omega = Omega {
        next: atoms.len(),
        room: cons.len(),
    };
    let found = omega.solve(eqs, ges)?;
    Ok(found.map(|m| {
        atoms
            .iter()
            .enumerate()
            .filter_map(|(i, a)| m.get(&i).map(|v| (a.clone(), *v)))
            .collect()
    }))
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
    /// The most rows an elimination may leave: the rows of the problem as given.
    room: usize,
}

impl Omega {
    fn solve(&mut self, eqs: Vec<Row>, ges: Vec<Row>) -> Result<Option<Vals>, Over> {
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
        // Eliminate the variable that leaves the fewest rows, exact before inexact, among those
        // that leave no more rows than the problem was given.
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
            let rows = gs.len() - lo.len() - hi.len() + lo.len() * hi.len();
            (!exact, rows, j)
        };
        let Some((inexact, _, j)) = vars
            .iter()
            .map(|j| cost(*j))
            .filter(|(_, rows, _)| *rows <= self.room)
            .min()
        else {
            return Err(Over);
        };
        let (with, others): (Vec<Row>, Vec<Row>) =
            gs.iter().cloned().partition(|r| r.a.contains_key(&j));
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
        // An empty real shadow, over the rationals, shows the problem empty; a point of the dark
        // shadow, which lies within the real one, is a point of it. Between them the question
        // is undecided: the splinters that would settle it recurse once per value of a
        // coefficient at each variable, which is exponential in the variables.
        if relaxed_empty(&gs) {
            return Ok(None);
        }
        match self.solve(Vec::new(), shadow(true)?) {
            Ok(Some(m)) => pick(Some(m)),
            _ => Err(Over),
        }
    }
}

/// Whether the inequalities have no rational point, by Fourier–Motzkin elimination with the
/// real shadow alone, each row normalized (which keeps every integer point). A `false` is
/// "not shown": a variable whose elimination would leave more rows than `gs` holds, or an
/// overflow, stops it. One pass eliminates each variable once.
fn relaxed_empty(gs: &[Row]) -> bool {
    let mut rows: Vec<Row> = gs.to_vec();
    let room = gs.len();
    loop {
        let mut tight: BTreeMap<BTreeMap<usize, i128>, i128> = BTreeMap::new();
        for r in rows {
            match r.normal() {
                Norm::False => return true,
                Norm::True => {}
                Norm::Row(r) => {
                    let k = tight.entry(r.a).or_insert(r.k);
                    *k = (*k).min(r.k);
                }
            }
        }
        for (a, k) in &tight {
            let opp: BTreeMap<usize, i128> = a.iter().map(|(i, c)| (*i, -c)).collect();
            if tight
                .get(&opp)
                .is_some_and(|k2| k.checked_add(*k2).is_some_and(|s| s < 0))
            {
                return true;
            }
        }
        let gs: Vec<Row> = tight
            .into_iter()
            .map(|(a, k)| Row { a, k, eq: false })
            .collect();
        let mut sides: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
        for r in &gs {
            for (i, c) in &r.a {
                let e = sides.entry(*i).or_default();
                if *c > 0 { e.0 += 1 } else { e.1 += 1 }
            }
        }
        let n = gs.len();
        let Some((_, j)) = sides
            .iter()
            .map(|(j, (lo, hi))| (n - lo - hi + lo * hi, *j))
            .min()
        else {
            return false;
        };
        if n - sides[&j].0 - sides[&j].1 + sides[&j].0 * sides[&j].1 > room {
            return false;
        }
        let (with, mut out): (Vec<Row>, Vec<Row>) =
            gs.into_iter().partition(|r| r.a.contains_key(&j));
        for l in with.iter().filter(|r| r.a[&j] > 0) {
            for u in with.iter().filter(|r| r.a[&j] < 0) {
                let (a, b) = (l.a[&j], -u.a[&j]);
                let mut r = Row {
                    a: BTreeMap::new(),
                    k: 0,
                    eq: false,
                };
                for (src, f) in [(u, a), (l, b)] {
                    for (i, c) in src.a.iter().filter(|(i, _)| **i != j) {
                        let Some(v) = c
                            .checked_mul(f)
                            .and_then(|v| v.checked_add(*r.a.get(i).unwrap_or(&0)))
                        else {
                            return false;
                        };
                        if v == 0 {
                            r.a.remove(i);
                        } else {
                            r.a.insert(*i, v);
                        }
                    }
                    let Some(k) = src.k.checked_mul(f).and_then(|v| v.checked_add(r.k)) else {
                        return false;
                    };
                    r.k = k;
                }
                out.push(r);
            }
        }
        rows = out;
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

/// The values of a symbol over the formula's points, as a union of intervals (see the module
/// note): exact when one disjunction is left, a set holding them otherwise. A bound past `i64`
/// is read as no bound.
pub fn project(f: &Formula, sym: &Atom) -> Result<IntervalSet, Over> {
    project_each(f, std::slice::from_ref(sym))?.remove(0)
}

/// [`project`] onto each of `syms`, removing disjuncts once: one result for each symbol, so
/// that a symbol whose hull is undecided leaves the others projected.
pub fn project_each(f: &Formula, syms: &[Atom]) -> Result<Vec<Result<IntervalSet, Over>>, Over> {
    let none = || syms.iter().map(|_| Ok(IntervalSet::empty())).collect();
    let Some(mut p) = propagate(f)? else {
        return Ok(none());
    };
    if p.ors.len() > 1 && pick(&p).is_err() {
        let Some(q) = probe(p)? else {
            return Ok(none());
        };
        p = q;
    }
    let Some(model) = solve(&p.cons)? else {
        return Ok(none());
    };
    let base = Formula::and(p.cons.iter().cloned().map(Formula::Con).collect());
    // Each disjunct's projections with the base, a level of disjunctions fewer than `f`; an
    // undecided one is `None`.
    let mut parts: Vec<Vec<Option<Projections>>> = Vec::new();
    for ds in &p.ors {
        let mut each = Vec::new();
        for d in ds {
            each.push(project_each(&Formula::and(vec![base.clone(), d.clone()]), syms).ok());
        }
        parts.push(each);
    }
    Ok(syms
        .iter()
        .enumerate()
        .map(|(k, sym)| {
            let mut out = hull_from(&base, sym, &model)?;
            for ds in &parts {
                let mut u = Some(IntervalSet::empty());
                for d in ds {
                    u = match (u, d) {
                        (Some(u), Some(r)) => r[k].as_ref().ok().map(|h| u.join(h)),
                        _ => None,
                    };
                }
                if let Some(u) = u {
                    out = out.meet(&u);
                }
            }
            if p.ors.len() > 1 {
                out = tighten(f, sym, out)?;
            }
            Ok(out)
        })
        .collect())
}

/// `set`, holding every value of `sym` over `f`'s points, with each finite bound raised or
/// lowered by bisection to the nearest value at which `f` with `sym` past it is shown to have
/// no point. A bound moves only on such a proof, so an undecided question leaves it sound.
fn tighten(f: &Formula, sym: &Atom, set: IntervalSet) -> Result<IntervalSet, Over> {
    let Some((End::Fin(lo), End::Fin(hi))) = set.bounds() else {
        return Ok(set);
    };
    let x = Lin::atom(sym.clone());
    let none = |con: Con| {
        matches!(
            satisfiable(&Formula::and(vec![f.clone(), Formula::Con(con)])),
            Ok(None)
        )
    };
    // The least `v` in `lo..=hi` with no proof that `f` has no point where `sym <= v`, and the
    // greatest with none where `sym >= v`.
    let (mut a, mut b) = (i128::from(lo), i128::from(hi));
    while a < b {
        let mid = a + (b - a).div_euclid(2);
        if none(Con::ge(&Lin::constant(mid), &x)?) {
            a = mid + 1
        } else {
            b = mid
        }
    }
    let new_lo = a;
    if none(Con::ge(&Lin::constant(new_lo), &x)?) {
        return Ok(IntervalSet::empty());
    }
    let (mut a, mut b) = (new_lo, i128::from(hi));
    while a < b {
        let mid = b - (b - a).div_euclid(2);
        if none(Con::ge(&x, &Lin::constant(mid))?) {
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
    /// The question lies outside the fragment the test decides (see the module note).
    Undecided,
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
            Entailment::Undecided => {
                write!(f, "undecided: outside the fragment the Omega test decides")
            }
        }
    }
}

/// Whether `premises` entail `goal` (rung 2).
pub fn entails(premises: &Relation, goal: &Relation) -> Entailment {
    entails_inner(premises, goal).unwrap_or(Entailment::Undecided)
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
    fn the_dark_shadow_decides_integer_points_and_the_gap_is_undecided() {
        // 2x = 2y + 1 has real points and no integer point.
        let f = Formula::Con(Con {
            lin: lin(&[("x", 2), ("y", -2)], -1),
            rel: Rel::Eq,
        });
        assert_eq!(satisfiable(&f), Ok(None));
        // 3 <= 2x <= 3 has none either. 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has none
        // (Pugh's example), but its dark shadow is empty and its real shadow is not: only the
        // splinters, not taken, would settle it.
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
        assert_eq!(satisfiable(&pugh), Err(Over));
        // Shifted to hold the point (2, 1), the dark shadow finds a point.
        let shifted = Formula::and(vec![
            ge(&[("x", 11), ("y", 13)], -27),
            ge(&[("x", -11), ("y", -13)], 45),
            ge(&[("x", 7), ("y", -9)], -5),
            ge(&[("x", -7), ("y", 9)], 5),
        ]);
        let m = satisfiable(&shifted).unwrap().unwrap();
        assert!(shifted.holds(&m).unwrap(), "{m:?}");
    }
}
