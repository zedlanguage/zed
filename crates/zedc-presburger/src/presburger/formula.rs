//! The formulas of the solver (`super`): atoms, linear terms, constraints and formulas over
//! them, and the key of a compound part held by more than one parent ([`Id`]), with the
//! arithmetic of terms, the value of a constraint at a model, the rank of a formula's
//! variant and how each is written. The solver and the operations that follow a formula's
//! nesting (`super::deep`) both read these, so they are kept in a file below both
//! (ZED_PORT_GAPS.md gap 10).

use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::slice;
use std::sync::Arc;

use zedc_int::int::Int;

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
pub struct Id(Formula);

impl Clone for Id {
    fn clone(&self) -> Id {
        Id(self.0.clone())
    }
}

impl Id {
    /// The key of `f`, a compound part.
    pub fn any(f: &Formula) -> Id {
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

    /// The rank of the variant, in the order in which [`Ord`] puts them.
    pub(super) fn rank(&self) -> u8 {
        match self {
            Formula::Con(_) => 0,
            Formula::Not(_) => 1,
            Formula::And(_) => 2,
            Formula::Or(_) => 3,
        }
    }

    /// Whether `self` is a conjunction or disjunction of the variant `kind`, so that it is read
    /// as flattened into a parent of that variant (`deep::Flat`).
    pub(super) fn flattens_into(&self, kind: u8) -> bool {
        matches!(self, Formula::And(_) | Formula::Or(_)) && self.rank() == kind
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
        let mut out = self.times(other.constant.clone());
        for (x, c) in &xs {
            out = out.plus(&Lin::atom(x.atom()).times(*c * &self.constant));
            for (y, d) in &ys {
                out = out.plus(&Lin::atom(Atom::product_of(x.clone(), y.clone())).times(*c * *d));
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
}

impl Lin {
    /// Writes the term, each symbol through `name`.
    fn show(&self, f: &mut fmt::Formatter<'_>, name: Names) -> fmt::Result {
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
                a.show(f, name)?;
            } else {
                write!(f, "{m} * ")?;
                a.show(f, name)?;
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

    /// Whether the constraint holds at `values` ([`Formula::holds`]).
    pub(super) fn holds(&self, values: &Model) -> bool {
        let v = self.lin.eval(values);
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
