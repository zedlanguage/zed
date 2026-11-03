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
//! eliminations first, and only while the system
//! holds no more rows than it was given: each step removes a variable and the rows never pass
//! the input's count. An elimination is exact when every lower or every upper coefficient of
//! the variable is a unit. At the first inexact elimination the real shadow is tested once:
//! empty over the rationals, it shows the problem empty. From there on the dark shadow is
//! solved, whose points are points of the problem, and an empty dark shadow is a refusal, as
//! is a system every elimination of which would grow it ([`Refusal`]). A satisfiable problem
//! yields a model: each eliminated variable takes the value nearest zero that its bounds allow
//! under the values of the variables eliminated after it.
//!
//! A formula with disjunctions is not split into all its conjunctions. Its top-level
//! constraints are the base; a disjunct whose own top-level constraints meet the base nowhere
//! is removed, and a disjunction with one disjunct left adds it to the base, until nothing is
//! removed: each round removes a disjunct, so the rounds are at most the disjuncts. No
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
//! and narrowing drops the refusal, so that nothing reports it to the author so far. A term written with a coefficient past `i128` is
//! refused; the solver's own rows and models are unbounded.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use super::int::Int;
use super::interval::{End, IntervalSet};

/// The projection onto each symbol, in order; an error where it is refused.
type Projections = Vec<Result<IntervalSet, Refusal>>;

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

/// Why a question lies outside the fragment decided in polynomial time. Each is reported in
/// its own words (sec:diagnostics); narrowing keeps the written constraint, which is sound.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refusal {
    /// A coefficient or constant of a written term does not fit in `i128`.
    Coefficient,
    /// The real shadow holds a point and the dark shadow holds none, so that only the
    /// splinters, which are exponential in the variables, would settle the question.
    Shadows,
    /// The elimination of every variable left would leave more rows than the question has.
    Growth,
    /// The search through the disjunctions found no point and removed no disjunct.
    Disjuncts,
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Refusal::Coefficient => "a coefficient of the relation does not fit in 128 bits",
            Refusal::Shadows => {
                "the relation has rational points but no integer point was found or ruled out"
            }
            Refusal::Growth => "eliminating any variable left would grow the relation",
            Refusal::Disjuncts => "no choice among the relation's disjunctions was settled",
        })
    }
}

fn add(a: i128, b: i128) -> Result<i128, Refusal> {
    a.checked_add(b).ok_or(Refusal::Coefficient)
}

fn mul(a: i128, b: i128) -> Result<i128, Refusal> {
    a.checked_mul(b).ok_or(Refusal::Coefficient)
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
    pub fn plus(&self, other: &Lin) -> Result<Lin, Refusal> {
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
    pub fn times(&self, k: i128) -> Result<Lin, Refusal> {
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
    pub fn minus(&self, other: &Lin) -> Result<Lin, Refusal> {
        self.plus(&other.times(-1)?)
    }

    /// Whether every atom is a symbol or an auxiliary variable.
    pub fn is_linear(&self) -> bool {
        !self.terms.keys().any(|a| matches!(a, Atom::Product(..)))
    }

    /// The product of two terms, its products of two symbols as atoms; `None` when neither
    /// is a constant and either holds an atom that is not a symbol.
    pub fn product(&self, other: &Lin) -> Option<Result<Lin, Refusal>> {
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
        let go = || -> Result<Lin, Refusal> {
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
    fn eval(&self, values: &Model) -> Int {
        let mut v = Int::from(self.constant);
        for (a, c) in &self.terms {
            if let Some(x) = values.get(a) {
                v = &v + &(&Int::from(*c) * x);
            }
        }
        v
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
    pub fn ge(a: &Lin, b: &Lin) -> Result<Con, Refusal> {
        Ok(Con {
            lin: a.minus(b)?,
            rel: Rel::Ge,
        })
    }

    /// `a == b`.
    pub fn eq(a: &Lin, b: &Lin) -> Result<Con, Refusal> {
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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

    /// The formula with each constraint `c` replaced by `f(c)`.
    pub fn map_cons(&self, f: &dyn Fn(&Con) -> Formula) -> Formula {
        match self {
            Formula::Con(c) => f(c),
            Formula::Not(g) => Formula::negate(g.map_cons(f)),
            Formula::And(gs) => Formula::and(gs.iter().map(|g| g.map_cons(f)).collect()),
            Formula::Or(gs) => Formula::or(gs.iter().map(|g| g.map_cons(f)).collect()),
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
    pub fn holds(&self, values: &Model) -> bool {
        let mut vs = values.clone();
        for a in self.atoms() {
            if let Atom::Product(x, y) = &a {
                let v = |s: &Arc<str>| values.get(&Atom::Sym(s.clone())).unwrap_or(&Int::ZERO);
                vs.insert(a.clone(), v(x) * v(y));
            }
        }
        self.holds_as(&vs)
    }

    /// Whether the formula holds at `values`, each atom read as its value there.
    fn holds_as(&self, vs: &Model) -> bool {
        match self {
            Formula::Con(c) => {
                let v = c.lin.eval(vs);
                if c.rel == Rel::Eq {
                    v.is_zero()
                } else {
                    !v.is_negative()
                }
            }
            Formula::Not(g) => !g.holds_as(vs),
            Formula::And(gs) => gs.iter().all(|g| g.holds_as(vs)),
            Formula::Or(gs) => gs.iter().any(|g| g.holds_as(vs)),
        }
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
pub type Model = BTreeMap<Atom, Int>;

/// Whether `f` holds somewhere, and where.
pub fn satisfiable(f: &Formula) -> Result<Option<Model>, Refusal> {
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
/// constraints taken so far, or a refusal when none does.
fn pick(p: &Parts) -> Result<Model, Refusal> {
    let mut model = solve(&p.cons)?.ok_or(Refusal::Disjuncts)?;
    let (mut acc, mut queue) = (p.cons.clone(), p.ors.clone());
    while let Some(ds) = queue.pop() {
        let mut taken = None;
        let mut why = Refusal::Disjuncts;
        for d in ds {
            let mut cs = acc.clone();
            cs.extend(lits(&d));
            match solve(&cs) {
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
fn probe(mut p: Parts) -> Result<Option<Parts>, Refusal> {
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
/// `-t - 1 >= 0`, and not `t == 0` is `t >= 1 || -t >= 1`. The parts of each conjunction and
/// disjunction are sorted, so that the search through them, which takes the first that serves,
/// does not depend on the order they are written in.
fn nnf(f: &Formula, sign: bool) -> Result<Formula, Refusal> {
    let mut out = match (f, sign) {
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
    };
    if let Formula::And(gs) | Formula::Or(gs) = &mut out {
        gs.sort();
    }
    Ok(out)
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
fn propagate(f: &Formula) -> Result<Option<Parts>, Refusal> {
    let mut p = Parts::default();
    p.add(nnf(f, true)?);
    settle(p)
}

/// [`propagate`] from parts.
fn settle(mut p: Parts) -> Result<Option<Parts>, Refusal> {
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
fn solve(cons: &[Con]) -> Result<Option<Model>, Refusal> {
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let index: BTreeMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    // Sorted, so that the answer does not depend on the order the constraints are given in.
    let mut sorted: Vec<&Con> = cons.iter().collect();
    sorted.sort();
    let mut sys = System::new(atoms.len());
    let mut es = Equalities::new(atoms.len());
    for c in sorted {
        let r = Row {
            a: c.lin
                .terms
                .iter()
                .map(|(a, k)| (index[a], Int::from(*k)))
                .collect(),
            k: Int::from(c.lin.constant),
        };
        match c.rel {
            Rel::Eq => es.push(r, &mut sys),
            Rel::Ge => sys.add(r),
        }
    }
    let omega = Omega {
        sys,
        es,
        steps: Vec::new(),
        room: cons.len(),
    };
    omega.run(&atoms)
}

/// A coefficient at a variable.
type Term = (usize, Int);

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

/// Pugh's symmetric remainder: `a - m·floor(a/m + 1/2)`.
fn mod_hat(a: &Int, m: &Int) -> Int {
    let r = a.mod_floor(m);
    if &(&r + &r) >= m { &r - m } else { r }
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
}

impl Sides {
    /// Whether no elimination of the variable is exact.
    fn inexact(&self) -> bool {
        self.lo_wide > 0 && self.hi_wide > 0
    }

    /// The rows its elimination adds less the rows it removes.
    fn growth(&self) -> isize {
        (self.lo * self.hi) as isize - (self.lo + self.hi) as isize
    }

    /// The terms its elimination writes.
    fn written(&self) -> usize {
        self.lo * self.hi_terms + self.hi * self.lo_terms
    }

    /// Where the variable stands among those to eliminate: by rows added, then terms written.
    fn rank(&self, j: usize) -> Rank {
        (self.growth(), self.written(), j)
    }
}

/// The growth of a variable's elimination, the terms it writes, and the variable.
type Rank = (isize, usize, usize);

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
    /// The lesser coefficients of two opposite rows whose constants sum to zero; a pair may
    /// since have changed, and is checked when taken.
    meets: BTreeSet<Coefs>,
    /// Whether a row is false, or two opposite rows meet nowhere.
    empty: bool,
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
            meets: BTreeSet::new(),
            empty: false,
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
        for (i, c) in a.iter() {
            let v = &mut self.vars[*i];
            let set = if v.sides.inexact() {
                &mut self.inexact
            } else {
                &mut self.exact
            };
            set.remove(&v.sides.rank(*i));
            self.one_sided.remove(i);
            let s = &mut v.sides;
            let (side, wide, terms) = if c.is_positive() {
                (&mut s.lo, &mut s.lo_wide, &mut s.lo_terms)
            } else {
                (&mut s.hi, &mut s.hi_wide, &mut s.hi_terms)
            };
            if add {
                *side += 1;
                *wide += usize::from(!c.is_unit());
                *terms += a.len();
                v.rows.insert(id);
            } else {
                *side -= 1;
                *wide -= usize::from(!c.is_unit());
                *terms -= a.len();
                v.rows.remove(&id);
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

    /// Whether the elimination is inexact and the variable of least growth among the exact
    /// eliminations, or failing that the inexact ones, the first on a tie, whose elimination
    /// leaves no more than `room` rows.
    fn best(&self, room: usize) -> Option<(bool, usize)> {
        let fits = |&&(g, _, _): &&Rank| self.rows.len() as isize + g <= room as isize;
        let exact = self.exact.first().filter(fits).map(|r| (false, r.2));
        exact.or_else(|| self.inexact.first().filter(fits).map(|r| (true, r.2)))
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

/// The Omega test. Each step solves an equality, turns two opposite rows that meet into one,
/// drops a variable bounded on one side only, or eliminates a variable, until no row is left;
/// the model is then built back through the steps.
struct Omega {
    sys: System,
    es: Equalities,
    steps: Vec<Step>,
    /// The most rows an elimination may leave: the rows of the problem as given.
    room: usize,
}

impl Omega {
    fn run(mut self, atoms: &[Atom]) -> Result<Option<Model>, Refusal> {
        // Below an inexact elimination only the dark shadow is solved, so an empty problem
        // there is not shown empty, and the real shadow is tried once, at the first.
        let mut dark = false;
        loop {
            if self.sys.empty {
                return if dark {
                    Err(Refusal::Shadows)
                } else {
                    Ok(None)
                };
            }
            if let Some(s) = self.es.last() {
                self.equality(s);
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
            let (inexact, j) = self.sys.best(self.room).ok_or(Refusal::Growth)?;
            if inexact && !dark {
                // An empty real shadow, over the rationals, shows the problem empty; a point of
                // the dark shadow, which lies within the real one, is a point of it. Between
                // them the question is refused: the splinters that would settle it recurse once
                // per value of a coefficient at each variable, which is exponential in the
                // variables.
                if relaxed_empty(&self.sys) {
                    return Ok(None);
                }
                dark = true;
            }
            let rows = self.sys.eliminate(j, inexact);
            self.steps.push(Step::Chosen(j, rows));
        }
        let mut vals = vec![Int::ZERO; self.sys.vars.len()];
        let mut model = Model::new();
        for step in self.steps.iter().rev() {
            let (j, v) = match step {
                Step::Defined(j, def) => (*j, def.eval(&vals)),
                Step::Chosen(j, rows) => (*j, choose(rows, *j, &vals)),
            };
            if let Some(a) = atoms.get(j) {
                model.insert(a.clone(), v.clone());
            }
            vals[j] = v;
        }
        Ok(Some(model))
    }

    /// Solves the equality in slot `s`: by a unit coefficient where it has one, or else by Pugh's
    /// step. That step takes the variable `x[j]` with the least coefficient, the first on a tie,
    /// and `m`, one above it; with a fresh `t`, the equality of the coefficients `mod_hat(a, m)`
    /// and `-m` at `t` has a unit at `x[j]`, and defines `x[j]`. By Pugh's argument this shrinks
    /// the coefficients of the equality in the slot, by about 5/6 each time, so the steps end.
    fn equality(&mut self, s: usize) {
        let e = self.es.clear(s);
        if let Some((j, _)) = e.a.iter().find(|(_, c)| c.is_unit()) {
            self.define(*j, &e);
            return;
        }
        let (j, least) =
            e.a.iter()
                .map(|(i, c)| (*i, c.abs()))
                .min_by(|p, q| p.1.cmp(&q.1))
                .expect("a row has a variable");
        let m = &least + &Int::ONE;
        let t = self.sys.vars.len();
        self.sys.vars.push(Var::default());
        self.es.of.push(BTreeSet::new());
        let mut a: Vec<Term> =
            e.a.iter()
                .map(|(i, c)| (*i, mod_hat(c, &m)))
                .filter(|(_, c)| !c.is_zero())
                .collect();
        a.push((t, -&m));
        let hat = Row {
            a: a.into(),
            k: mod_hat(&e.k, &m),
        };
        self.es.put(s, e, &mut self.sys);
        self.define(j, &hat);
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
        for r in self.sys.take(j) {
            self.sys.add(r.subst(j, &def));
        }
        self.es.subst(j, &def, &mut self.sys);
        self.steps.push(Step::Defined(j, def));
    }
}

/// Whether the inequalities have no rational point, by Fourier–Motzkin elimination with the
/// real shadow alone, each row normalized (which keeps every integer point). A `false` is
/// "not shown": a variable whose elimination would leave more rows than `gs` holds stops it.
/// Each step eliminates the variable of least rank.
fn relaxed_empty(gs: &System) -> bool {
    let mut sys = System::new(gs.vars.len());
    for (a, r) in &gs.rows {
        sys.add(Row {
            a: a.clone(),
            k: r.k.clone(),
        });
    }
    let room = sys.rows.len() as isize;
    while !sys.empty {
        let least = sys.exact.first().into_iter().chain(sys.inexact.first());
        let Some(&(growth, _, j)) = least.min() else {
            return false;
        };
        if sys.rows.len() as isize + growth > room {
            return false;
        }
        sys.eliminate(j, false);
    }
    true
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
pub fn project(f: &Formula, sym: &Atom) -> Result<IntervalSet, Refusal> {
    project_each(f, std::slice::from_ref(sym))?.remove(0)
}

/// [`project`] onto each of `syms`, removing disjuncts once: one result for each symbol, so
/// that a symbol whose hull is refused leaves the others projected.
pub fn project_each(
    f: &Formula,
    syms: &[Atom],
) -> Result<Vec<Result<IntervalSet, Refusal>>, Refusal> {
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
    // refused one is `None`.
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
/// no point. A bound moves only on such a proof, so a refused question leaves it sound.
fn tighten(f: &Formula, sym: &Atom, set: IntervalSet) -> Result<IntervalSet, Refusal> {
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
fn hull_from(c: &Formula, sym: &Atom, m: &Model) -> Result<IntervalSet, Refusal> {
    let x = Lin::atom(sym.clone());
    let (min, max) = (i128::from(i64::MIN), i128::from(i64::MAX));
    // The point's value, within the range the search covers.
    let at = m.get(sym).map_or(0, |v| {
        let past = if v.is_negative() { min } else { max };
        v.to_i128().unwrap_or(past).clamp(min, max)
    });
    let with = |con: Con| -> Result<bool, Refusal> {
        Ok(satisfiable(&Formula::and(vec![c.clone(), Formula::Con(con)]))?.is_some())
    };
    let below = |v: i128| with(Con::ge(&Lin::constant(v), &x)?);
    let above = |v: i128| with(Con::ge(&x, &Lin::constant(v))?);
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
pub fn member(sym: &Atom, s: &IntervalSet) -> Result<Formula, Refusal> {
    within(&Lin::atom(sym.clone()), s)
}

/// The values of the term `l` in the set `s`, as a formula.
pub fn within(l: &Lin, s: &IntervalSet) -> Result<Formula, Refusal> {
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
    fn the_dark_shadow_decides_integer_points_and_the_gap_is_refused() {
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
        assert_eq!(satisfiable(&pugh), Err(Refusal::Shadows));
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
}
