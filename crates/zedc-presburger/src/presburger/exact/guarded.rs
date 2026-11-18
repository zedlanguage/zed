//! The forward certificate of the cover (route F of PRES-cover-bench-guards-beyond and
//! PRES-cover-bench-chains-abs, chosen by their cross-review, seat Opus round 3): a proof, with
//! no question of the solver, that every value of `s` in the solver's set `h` has a point of
//! `f`, so that `h` is the exact projection.
//!
//! The conjuncts of `f` are read as definitions and residuals. A definition gives one atom, its
//! head, as a function of atoms known before it:
//! - an equation whose head has coefficient 1 or -1;
//! - a choice, a disjunction of two disjuncts `g >= 0 && e1 == 0` and `-g - 1 >= 0 && e2 == 0`
//!   (the two guards exact complements over the integers once each is divided by the gcd of
//!   its coefficients, the constant rounded down), the head with coefficient 1 or -1 in both
//!   equations and in neither guard.
//!
//! Starting from `s`, a definition is taken once its head is its only unknown atom (Kahn's
//! order). Where none can be taken and atoms are unknown, one atom read by no guard becomes the
//! pin `p`, free; a second such stop declines. Every conjunct not taken as a definition is a
//! residual. Then, for each piece `[lo, hi]` of `h`, each atom's value is held as
//! `slope * p + c`, with `c` in an interval: `s` is `0 * p + [lo, hi]` and the pin `1 * p + 0`.
//! A choice whose guard reads `p` declines; one whose guard is at least 0 (at most -1) over the
//! whole interval takes the first (second) disjunct; otherwise both, joined when their slopes
//! are equal, and declined when not. A residual gives the set of pins at which it holds for
//! every `c` in its interval; the piece is certified when the meet of those sets is not empty.
//!
//! Soundness (each value `v` in a certified piece has a point): take a pin `p` in the meet and
//! set `s = v`, the pin to `p`, and each head, in Kahn's order, to the value its definition
//! gives from the atoms set before it. By induction on that order each atom's value lies in
//! `slope * p + [lo, hi]`: true of `s` and the pin; an equation's head is a sum of known values
//! times their coefficients, and interval sums hold every such sum; a choice's guard value lies
//! in the guard's interval, so where the interval is at least 0 the first guard holds, at most
//! -1 the second, and otherwise exactly one of the two complementary guards holds and its
//! equation's value lies in the join. Each definition then holds at the point: an equation by
//! the choice of its head, a choice by the disjunct whose guard holds. Each residual holds for
//! every value in its intervals at `p`, so at the point's own values. So every conjunct holds,
//! and `v` has a point. Since every value with a point lies in `h` (the solver's set), the
//! projection is `h`. A wrong pin, or intervals too wide, can only make a residual's set empty,
//! a decline, never a wrong answer.
//!
//! Prior work: the definitions are Gaussian elimination of unit-coefficient equations (Pugh's
//! exact elimination, "A practical algorithm for exact array dependence analysis", CACM 35(8),
//! 1992, p. 106) extended to guarded definitions; the interval reading of the values given a
//! pin is interval constraint propagation over the definition order.

use std::collections::{HashMap, HashSet};

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet};

use super::super::formula::Id;
use super::super::meter::{PIECE, Work};
use super::super::{Atom, Con, Formula, Lin, Refusal, Rel};
use super::projection::{each_constraint, fin};

/// A definition of one atom from others ([module note](self)).
enum Def<'a> {
    /// `lin == 0`, with the head's coefficient 1 or -1.
    Eq(&'a Lin),
    /// The first equation where `guard >= 0`, the second where `guard <= -1`.
    Choice { guard: Lin, arms: [&'a Lin; 2] },
}

impl Def<'_> {
    fn atoms(&self) -> impl Iterator<Item = &Atom> {
        let (a, b, c): (&Lin, Option<&Lin>, Option<&Lin>) = match self {
            Def::Eq(e) => (e, None, None),
            Def::Choice { guard, arms } => (guard, Some(arms[0]), Some(arms[1])),
        };
        (a.terms.keys())
            .chain(b.into_iter().flat_map(|l| l.terms.keys()))
            .chain(c.into_iter().flat_map(|l| l.terms.keys()))
    }

    /// Whether `x` may be this definition's head: coefficient 1 or -1 in each equation, and
    /// absent from the guard.
    fn may_define(&self, x: &Atom) -> bool {
        let unit = |l: &Lin| l.terms.get(x).is_some_and(|c| c.abs() == Int::ONE);
        match self {
            Def::Eq(e) => unit(e),
            Def::Choice { guard, arms } => {
                !guard.terms.contains_key(x) && unit(arms[0]) && unit(arms[1])
            }
        }
    }
}

/// An atom's value at a point: `slope * p + c`, `c` from `lo` to `hi` (`None` without end).
#[derive(Clone)]
struct Val {
    slope: Int,
    lo: Option<Int>,
    hi: Option<Int>,
}

impl Val {
    fn join(&self, o: &Val) -> Option<Val> {
        (self.slope == o.slope).then(|| Val {
            slope: self.slope.clone(),
            lo: self
                .lo
                .as_ref()
                .zip(o.lo.as_ref())
                .map(|(a, b)| a.min(b).clone()),
            hi: self
                .hi
                .as_ref()
                .zip(o.hi.as_ref())
                .map(|(a, b)| a.max(b).clone()),
        })
    }
}

/// The compiled reading of `f`: the definitions taken, in Kahn's order with their heads, the
/// residuals, and the pin.
struct Reading<'a> {
    order: Vec<(Def<'a>, Atom)>,
    residuals: Vec<&'a Formula>,
    pin: Option<Atom>,
}

/// `lin` divided by the gcd of its coefficients, the constant rounded down: the same integer
/// points of `lin >= 0`.
fn normal(lin: &Lin) -> Lin {
    let d = (lin.terms.values()).fold(Int::ZERO, |d, c| d.gcd(c));
    if d.is_zero() || d == Int::ONE {
        return lin.clone();
    }
    Lin {
        terms: (lin.terms.iter())
            .map(|(a, c)| (a.clone(), c.div_floor(&d)))
            .collect(),
        constant: lin.constant.div_floor(&d),
    }
}

/// The row `>= 0` of a guard written `t >= 0` or `!(t >= 0)` (`-t - 1 >= 0`).
fn guard_row(f: &Formula) -> Option<Lin> {
    match f {
        Formula::Con(Con { lin, rel: Rel::Ge }) => Some(normal(lin)),
        Formula::Not(g) => match &**g {
            Formula::Con(Con { lin, rel: Rel::Ge }) => {
                Some(normal(&lin.times(-1).plus(&Lin::constant(-1))))
            }
            _ => None,
        },
        _ => None,
    }
}

/// `f` read as a choice ([`Def::Choice`]), or `None`.
fn choice(f: &Formula) -> Option<Def<'_>> {
    let Formula::Or(arms) = f else { return None };
    let [a, b] = &arms[..] else { return None };
    fn arm(x: &Formula) -> Option<(Lin, &Lin)> {
        let parts = x.conjuncts();
        let [p, q] = &parts[..] else { return None };
        fn eq(g: &Formula) -> Option<&Lin> {
            match g {
                Formula::Con(Con { lin, rel: Rel::Eq }) => Some(lin),
                _ => None,
            }
        }
        match (eq(p), eq(q)) {
            (Some(e), None) => Some((guard_row(q)?, e)),
            (None, Some(e)) => Some((guard_row(p)?, e)),
            _ => None,
        }
    }
    let ((g, e), (h, d)) = (arm(a)?, arm(b)?);
    // Exact complements: `g + h == -1` with no atom, so `h >= 0` is `g <= -1`.
    let sum = g.plus(&h);
    (sum.terms.is_empty() && sum.constant == Int::from(-1)).then_some(Def::Choice {
        guard: g,
        arms: [e, d],
    })
}

/// The definitions and residuals of `f` from `s` ([module note](self)); `None` where a second
/// atom must be left free, or a product is read.
// Complexity tradeoff: Kahn's order over the atom incidence of the definitions, O(r·t) for r
// conjuncts of t terms, plus O(a log a) to number the a atoms in their order (so the pin does
// not depend on the order of the parts); the naive repeated pass over all definitions until
// none is taken is O(r²·t).
fn read<'a>(f: &'a Formula, s: &Atom, work: &mut Work) -> Result<Option<Reading<'a>>, Refusal> {
    let parts = f.conjuncts();
    let mut defs: Vec<Option<Def<'a>>> = Vec::with_capacity(parts.len());
    let mut all: HashSet<&Atom> = HashSet::new();
    let mut found = false;
    for g in &parts {
        work.charge(PIECE)?;
        each_constraint(g, |c| {
            for a in c.lin.terms.keys() {
                found |= matches!(a, Atom::Product(..));
                all.insert(a);
            }
        });
        defs.push(match g {
            Formula::Con(Con { lin, rel: Rel::Eq }) => Some(Def::Eq(lin)),
            _ => choice(g),
        });
    }
    if found {
        return Ok(None);
    }
    // The atoms numbered, in the order of `Atom` (so that the pin chosen below, the least, does
    // not depend on the order of the parts), and each definition's distinct atoms by number.
    let mut atoms: Vec<&Atom> = all.into_iter().collect();
    atoms.sort();
    let index: HashMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (*a, i)).collect();
    let mut guarded = vec![false; atoms.len()];
    let mut by_atom: Vec<Vec<usize>> = vec![Vec::new(); atoms.len()];
    let mut reads: Vec<Vec<usize>> = vec![Vec::new(); defs.len()];
    for (i, d) in defs.iter().enumerate() {
        let Some(d) = d else { continue };
        if let Def::Choice { guard, .. } = d {
            for a in guard.terms.keys() {
                guarded[index[a]] = true;
            }
        }
        for a in d.atoms() {
            let j = index[a];
            if !reads[i].contains(&j) {
                reads[i].push(j);
                by_atom[j].push(i);
            }
        }
    }
    let mut known = vec![false; atoms.len()];
    let mut unknown: Vec<usize> = reads.iter().map(Vec::len).collect();
    let mut left = atoms.len();
    let mut queue: Vec<usize> = Vec::new();
    let mut taken = vec![false; defs.len()];
    let mut order: Vec<(usize, Atom)> = Vec::new();
    let mut pin = None;
    // Marks atom `x` known and queues the definitions left with one unknown atom.
    let learn = |x: usize,
                 known: &mut [bool],
                 unknown: &mut [usize],
                 queue: &mut Vec<usize>,
                 left: &mut usize| {
        if !known[x] {
            known[x] = true;
            *left -= 1;
            for &i in &by_atom[x] {
                unknown[i] -= 1;
                if unknown[i] == 1 {
                    queue.push(i);
                }
            }
        }
    };
    if let Some(&x) = index.get(s) {
        learn(x, &mut known, &mut unknown, &mut queue, &mut left);
    }
    queue.extend((0..defs.len()).filter(|&i| unknown[i] == 1));
    loop {
        while let Some(i) = queue.pop() {
            work.charge(PIECE)?;
            let Some(d) = &defs[i] else { continue };
            if taken[i] || unknown[i] != 1 {
                continue;
            }
            let Some(&x) = reads[i].iter().find(|&&j| !known[j]) else {
                continue;
            };
            if !d.may_define(atoms[x]) {
                continue;
            }
            taken[i] = true;
            order.push((i, atoms[x].clone()));
            learn(x, &mut known, &mut unknown, &mut queue, &mut left);
        }
        if left == 0 {
            break;
        }
        if pin.is_some() {
            return Ok(None);
        }
        // The least unknown atom read by no guard: a guard reading the pin would decline.
        let Some(x) = (0..atoms.len()).find(|&j| !known[j] && !guarded[j]) else {
            return Ok(None);
        };
        pin = Some(atoms[x].clone());
        learn(x, &mut known, &mut unknown, &mut queue, &mut left);
    }
    let mut residuals = Vec::new();
    for (i, g) in parts.iter().enumerate() {
        if !taken[i] {
            residuals.push(*g);
        }
    }
    let order = (order.into_iter())
        .map(|(i, x)| (defs[i].take().expect("a taken definition"), x))
        .collect();
    Ok(Some(Reading {
        order,
        residuals,
        pin,
    }))
}

/// The value of `lin` given the atoms' values; every atom of `lin` has one (Kahn's order).
fn value(lin: &Lin, vals: &HashMap<&Atom, Val>) -> Val {
    let mut out = Val {
        slope: Int::ZERO,
        lo: Some(lin.constant.clone()),
        hi: Some(lin.constant.clone()),
    };
    for (a, c) in &lin.terms {
        let v = &vals[a];
        out.slope = &out.slope + &(c * &v.slope);
        let (l, h) = if c.is_negative() {
            (&v.hi, &v.lo)
        } else {
            (&v.lo, &v.hi)
        };
        out.lo = out.lo.zip(l.as_ref()).map(|(o, l)| &o + &(c * l));
        out.hi = out.hi.zip(h.as_ref()).map(|(o, h)| &o + &(c * h));
    }
    out
}

/// The head `x` of `lin == 0`, its coefficient 1 or -1: `x = -c * (lin - c * x)`.
fn solved(lin: &Lin, x: &Atom, vals: &HashMap<&Atom, Val>) -> Val {
    let c = &lin.terms[x];
    let mut rest = lin.clone();
    rest.terms.remove(x);
    let v = value(&rest, vals);
    if c.is_negative() {
        return v;
    }
    Val {
        slope: -&v.slope,
        lo: v.hi.map(|h| -&h),
        hi: v.lo.map(|l| -&l),
    }
}

/// The pins `p` with `a * p + lo >= k` (`lo` without end: none).
fn at_least(a: &Int, lo: Option<&Int>, k: &Int) -> IntervalSet {
    let Some(lo) = lo else {
        return IntervalSet::empty();
    };
    let r = lo - k;
    if a.is_zero() {
        return if r.is_negative() {
            IntervalSet::empty()
        } else {
            IntervalSet::top()
        };
    }
    // `a * p >= -r`: `p >= ceil(-r / a)` for `a > 0`, `p <= floor(r / -a)` for `a < 0`.
    if a.is_positive() {
        IntervalSet::range(fin(&-&r.div_floor(a)), End::PosInf)
    } else {
        IntervalSet::range(End::NegInf, fin(&r.div_floor(&-a)))
    }
}

/// The pins `p` with `a * p + hi <= k`.
fn at_most(a: &Int, hi: Option<&Int>, k: &Int) -> IntervalSet {
    at_least(&-a, hi.map(|h| -h).as_ref(), &-k)
}

/// The pins at which `f` (negated where `neg`) holds for every value in its atoms' intervals.
// Complexity tradeoff: one visit of each shared part per sign (memo by `Id`), O(size of f); the tree
// walk without the memo is exponential in the sharing depth (DAG visited set, P207).
fn pins(
    f: &Formula,
    neg: bool,
    vals: &HashMap<&Atom, Val>,
    memo: &mut HashMap<(Id, bool), IntervalSet>,
    work: &mut Work,
) -> Result<IntervalSet, Refusal> {
    let key = Id::of(f).map(|k| (k, neg));
    if let Some(k) = &key
        && let Some(set) = memo.get(k)
    {
        return Ok(set.clone());
    }
    let set = match f {
        Formula::Con(c) => {
            work.charge(PIECE)?;
            let v = value(&c.lin, vals);
            let (lo, hi) = (v.lo.as_ref(), v.hi.as_ref());
            let (zero, one) = (Int::ZERO, Int::ONE);
            match (c.rel, neg) {
                (Rel::Ge, false) => at_least(&v.slope, lo, &zero),
                (Rel::Ge, true) => at_most(&v.slope, hi, &-&one),
                (Rel::Eq, false) => {
                    at_least(&v.slope, lo, &zero).meet(&at_most(&v.slope, hi, &zero))
                }
                (Rel::Eq, true) => {
                    at_least(&v.slope, lo, &one).join(&at_most(&v.slope, hi, &-&one))
                }
            }
        }
        Formula::Not(g) => pins(g, !neg, vals, memo, work)?,
        Formula::And(gs) | Formula::Or(gs) => {
            let meet = matches!(f, Formula::And(_)) != neg;
            let mut out = if meet {
                IntervalSet::top()
            } else {
                IntervalSet::empty()
            };
            for g in gs.iter() {
                let x = pins(g, neg, vals, memo, work)?;
                out = if meet { out.meet(&x) } else { out.join(&x) };
                if meet && out.is_empty() {
                    break;
                }
            }
            out
        }
    };
    if let Some(k) = key {
        memo.insert(k, set.clone());
    }
    Ok(set)
}

/// Whether the reading certifies each value of `s` from `lo` to `hi` ([module note](self)).
fn certified(r: &Reading, s: &Atom, lo: &End, hi: &End, work: &mut Work) -> Result<bool, Refusal> {
    let end = |e: &End| match e {
        End::Fin(n) => Some(Int::from(n)),
        _ => None,
    };
    let mut vals: HashMap<&Atom, Val> = HashMap::new();
    vals.insert(
        s,
        Val {
            slope: Int::ZERO,
            lo: end(lo),
            hi: end(hi),
        },
    );
    if let Some(p) = &r.pin {
        let zero = Some(Int::ZERO);
        vals.insert(
            p,
            Val {
                slope: Int::ONE,
                lo: zero.clone(),
                hi: zero,
            },
        );
    }
    for (d, x) in &r.order {
        work.charge(PIECE)?;
        let v = match d {
            Def::Eq(e) => solved(e, x, &vals),
            Def::Choice { guard, arms } => {
                let g = value(guard, &vals);
                if !g.slope.is_zero() {
                    return Ok(false);
                }
                let yes = g.lo.as_ref().is_some_and(|l| !l.is_negative());
                let no = g.hi.as_ref().is_some_and(|h| h.is_negative());
                match (yes, no) {
                    (true, _) => solved(arms[0], x, &vals),
                    (_, true) => solved(arms[1], x, &vals),
                    _ => match solved(arms[0], x, &vals).join(&solved(arms[1], x, &vals)) {
                        Some(v) => v,
                        None => return Ok(false),
                    },
                }
            }
        };
        vals.insert(x, v);
    }
    let mut memo = HashMap::new();
    let mut at = IntervalSet::top();
    for g in &r.residuals {
        at = at.meet(&pins(g, false, &vals, &mut memo, work)?);
        if at.is_empty() {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `h`, where every value of it is shown to have a point of `f` ([module note](self)); `None`
/// where the reading or a piece declines.
pub(super) fn forward(
    f: &Formula,
    s: &Atom,
    h: &IntervalSet,
    work: &mut Work,
) -> Result<Option<IntervalSet>, Refusal> {
    let Some(r) = read(f, s, work)? else {
        return Ok(None);
    };
    for (lo, hi) in h.pieces() {
        if !certified(&r, s, lo, hi, work)? {
            return Ok(None);
        }
    }
    Ok(Some(h.clone()))
}
