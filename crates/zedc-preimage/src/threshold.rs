//! The exact bounds of a threshold-implication component (DESIGN.md sec:domains, item (2) of
//! the tests that hold disjunctions): every part is `x + k*w <= a || y - m*w >= b`, an upper
//! bound on one name or a lower bound on another, `w` one name for the whole component (the
//! *hub*), and every base atom on a name other than the hub has one of the same two shapes.
//!
//! Fix the hub at `c`. A part then reads "if `x >= a - k*c + 1` then `y >= b + m*c`", and two
//! values of the names that both pass give two more that pass when each name takes the smaller
//! of its two values, or each the larger. So the values that pass have a least member, found by
//! raising lower bounds along the parts, and a greatest, found by lowering upper bounds along
//! the parts read backward, and these are the exact bounds of every name. With every `k` and
//! `m` at least 0, raising `c` only raises the least member and lowers the greatest, so the
//! hub's values that pass are its least value `p` up to some `c*`, found by a binary search,
//! and every other name's bounds are those at `p`; with every `k` and `m` at most 0 the same
//! holds with the ends swapped, and with both signs a hub of two values is solved at each value.
//!
//! A hub value that is unbounded is handled as a value past every constant: the propagation
//! then compares terms `s*T + k` with `T` above every integer, so the bounds at an unbounded
//! end are the limits of the bounds there.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zedc_int::int::{Int, Num};
use zedc_lattice::interval::{End, IntervalSet};
use zedc_presburger::presburger::{Atom, Formula, Lin, Rel};

/// `x + k*w <= a`: an upper bound on name `x` that the hub moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Upper {
    /// The name, an index into [`System::names`].
    pub x: usize,
    /// The hub's coefficient.
    pub k: Int,
    /// The constant.
    pub a: Int,
}

/// `y - m*w >= b`: a lower bound on name `y` that the hub moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lower {
    /// The name, an index into [`System::names`].
    pub y: usize,
    /// The hub's coefficient, negated.
    pub m: Int,
    /// The constant.
    pub b: Int,
}

/// A component: each name's values, the hub's, and the atoms.
#[derive(Clone, Debug)]
pub struct System {
    /// The values of each name other than the hub.
    pub names: Vec<IntervalSet>,
    /// The values of the hub.
    pub hub: IntervalSet,
    /// The parts, each `upper || lower` with the two on different names.
    pub parts: Vec<(Upper, Lower)>,
    /// The base atoms that are upper bounds.
    pub uppers: Vec<Upper>,
    /// The base atoms that are lower bounds.
    pub lowers: Vec<Lower>,
}

/// What [`solve`] finds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// No values pass.
    Empty,
    /// The least and greatest value of each name that pass, and the hub's values that pass.
    Bounds {
        /// Each name's least and greatest value.
        names: Vec<(End, End)>,
        /// The hub's values.
        hub: IntervalSet,
    },
    /// The hub has three or more values and the coefficients have both signs: each value is
    /// solved exactly, but the values can be many (plan row S4-hub-mixed).
    MixedHub,
}

/// A value of the propagation: `s*T + k`, `T` above every integer, or an infinity. `s` is 0
/// when the hub has a value; it is not 0 only at an unbounded end of the hub. The derived order
/// is the order of the values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Val {
    NegInf,
    Fin(Int, Int),
    PosInf,
}

/// Where the hub is: at a value, or past every integer below or above.
#[derive(Clone, Copy, Debug)]
enum At<'a> {
    Value(&'a Int),
    Below,
    Above,
}

impl At<'_> {
    /// `a + k*c` at this hub value.
    fn plus(&self, a: &Int, k: &Int) -> Val {
        match self {
            At::Value(c) => Val::Fin(Int::ZERO, a + &(k * *c)),
            At::Above => Val::Fin(k.clone(), a.clone()),
            At::Below => Val::Fin(-k, a.clone()),
        }
    }
}

fn int(n: &Num) -> Int {
    Int::from(n)
}

/// The least member of `d` at or above `v`; `None` when there is none.
fn ceil(d: &IntervalSet, v: &Val) -> Option<Val> {
    match v {
        Val::NegInf => Some(match d.first()? {
            (End::Fin(lo), _) => Val::Fin(Int::ZERO, int(lo)),
            _ => Val::NegInf,
        }),
        Val::PosInf => None,
        Val::Fin(s, k) => match s.cmp(&Int::ZERO) {
            Ordering::Greater => match d.last()? {
                (_, End::PosInf) => Some(v.clone()),
                _ => None,
            },
            Ordering::Less => match d.first()? {
                (End::Fin(lo), _) => Some(Val::Fin(Int::ZERO, int(lo))),
                _ => Some(v.clone()),
            },
            Ordering::Equal => {
                let x = End::Fin(Num::from(k));
                // The first piece whose upper end is at or above `x`.
                let (lo, _) = d.piece_at_or_above(&x)?;
                Some(if *lo <= x {
                    v.clone()
                } else {
                    match lo {
                        End::Fin(lo) => Val::Fin(Int::ZERO, int(lo)),
                        _ => unreachable!("a piece after a finite end starts finite"),
                    }
                })
            }
        },
    }
}

/// The greatest member of `d` at or below `v`; `None` when there is none.
fn floor(d: &IntervalSet, v: &Val) -> Option<Val> {
    let neg = |v: &Val| match v {
        Val::NegInf => Val::PosInf,
        Val::PosInf => Val::NegInf,
        Val::Fin(s, k) => Val::Fin(-s, -k),
    };
    ceil(&d.neg(), &neg(v)).map(|v| neg(&v))
}

/// The least or greatest end of `d` as a value; `None` when `d` is empty.
fn end_of(d: &IntervalSet, least: bool) -> Option<Val> {
    let (lo, hi) = d.bounds()?;
    Some(match if least { lo } else { hi } {
        End::NegInf => Val::NegInf,
        End::PosInf => Val::PosInf,
        End::Fin(n) => Val::Fin(Int::ZERO, int(n)),
    })
}

/// The least and the greatest member of the values that pass with the hub at `at`, or `None`
/// when no value passes there. In time O(N log N) for N atoms: each name's parts are sorted by
/// threshold, and each part fires once in each direction.
fn members(sys: &System, at: At<'_>) -> Option<(Vec<Val>, Vec<Val>)> {
    let n = sys.names.len();
    // The least member: raise lower bounds.
    let mut lo: Vec<Val> = Vec::with_capacity(n);
    for d in &sys.names {
        lo.push(end_of(d, true)?);
    }
    for l in &sys.lowers {
        let v = ceil(&sys.names[l.y], &lo[l.y].clone().max(at.plus(&l.b, &l.m)))?;
        lo[l.y] = v;
    }
    // Each part as "if x reaches t then y >= r": by x, sorted by t.
    let mut fire: Vec<Vec<(Val, usize, Val)>> = vec![Vec::new(); n];
    for (up, low) in &sys.parts {
        let t = at.plus(&(&up.a + &Int::ONE), &-&up.k);
        fire[up.x].push((t, low.y, at.plus(&low.b, &low.m)));
    }
    for f in &mut fire {
        f.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    }
    let mut next = vec![0usize; n];
    let mut work: Vec<usize> = (0..n).collect();
    while let Some(x) = work.pop() {
        while let Some((t, y, r)) = fire[x].get(next[x]) {
            if *t > lo[x] {
                break;
            }
            next[x] += 1;
            if *r > lo[*y] {
                lo[*y] = ceil(&sys.names[*y], r)?;
                work.push(*y);
            }
        }
    }
    // The greatest member: lower upper bounds.
    let mut hi: Vec<Val> = Vec::with_capacity(n);
    for d in &sys.names {
        hi.push(end_of(d, false)?);
    }
    for u in &sys.uppers {
        let v = floor(&sys.names[u.x], &hi[u.x].clone().min(at.plus(&u.a, &-&u.k)))?;
        hi[u.x] = v;
    }
    if lo.iter().zip(&hi).any(|(l, h)| l > h) {
        return None;
    }
    // Each part read backward as "if y falls below r then x <= s": by y, sorted by r, the
    // greatest first.
    let mut back: Vec<Vec<(Val, usize, Val)>> = vec![Vec::new(); n];
    for (up, low) in &sys.parts {
        back[low.y].push((at.plus(&low.b, &low.m), up.x, at.plus(&up.a, &-&up.k)));
    }
    for f in &mut back {
        f.sort_unstable_by(|a, b| b.0.cmp(&a.0));
    }
    let mut next = vec![0usize; n];
    let mut work: Vec<usize> = (0..n).collect();
    while let Some(y) = work.pop() {
        while let Some((r, x, s)) = back[y].get(next[y]) {
            if hi[y] >= *r {
                break;
            }
            next[y] += 1;
            if *s < hi[*x] {
                hi[*x] = floor(&sys.names[*x], s)?;
                work.push(*x);
            }
        }
    }
    // The least member passes every atom when it is below every upper bound, so values pass;
    // the greatest is then a member too, and at or above the least.
    debug_assert!(lo.iter().zip(&hi).all(|(l, h)| l <= h));
    Some((lo, hi))
}

/// A value of the propagation as an end: a value past every integer is an infinity.
fn end(v: &Val) -> End {
    match v {
        Val::NegInf => End::NegInf,
        Val::PosInf => End::PosInf,
        Val::Fin(s, k) => match s.cmp(&Int::ZERO) {
            Ordering::Less => End::NegInf,
            Ordering::Greater => End::PosInf,
            Ordering::Equal => End::Fin(Num::from(k)),
        },
    }
}

/// The signs of the hub's coefficients: whether any is above 0, and whether any is below.
fn signs(sys: &System) -> (bool, bool) {
    let ks = sys
        .parts
        .iter()
        .flat_map(|(u, l)| [&u.k, &l.m])
        .chain(sys.uppers.iter().map(|u| &u.k))
        .chain(sys.lowers.iter().map(|l| &l.m));
    let mut out = (false, false);
    for k in ks {
        match k.cmp(&Int::ZERO) {
            Ordering::Greater => out.0 = true,
            Ordering::Less => out.1 = true,
            Ordering::Equal => {}
        }
    }
    out
}

/// `sys` with the hub negated: every `k` and `m` negated and the hub's values too.
fn mirrored(sys: &System) -> System {
    System {
        names: sys.names.clone(),
        hub: sys.hub.neg(),
        parts: sys
            .parts
            .iter()
            .map(|(u, l)| {
                (
                    Upper {
                        k: -&u.k,
                        ..u.clone()
                    },
                    Lower {
                        m: -&l.m,
                        ..l.clone()
                    },
                )
            })
            .collect(),
        uppers: sys
            .uppers
            .iter()
            .map(|u| Upper {
                k: -&u.k,
                ..u.clone()
            })
            .collect(),
        lowers: sys
            .lowers
            .iter()
            .map(|l| Lower {
                m: -&l.m,
                ..l.clone()
            })
            .collect(),
    }
}

/// The exact bounds of every name of `sys`, and the hub's values, that pass every atom.
///
/// In time O(N log N log W) for N atoms, W the width of the hub's values: each propagation is
/// O(N log N), and the binary search for the hub's greatest value that passes makes O(log W)
/// of them.
pub fn solve(sys: &System) -> Answer {
    if sys.hub.is_empty() || sys.names.iter().any(IntervalSet::is_empty) {
        return Answer::Empty;
    }
    match signs(sys) {
        (true, true) => mixed(sys),
        (false, true) => match rising(&mirrored(sys)) {
            Answer::Bounds { names, hub } => Answer::Bounds {
                names,
                hub: hub.neg(),
            },
            a => a,
        },
        _ => rising(sys),
    }
}

/// A hub with coefficients of both signs: solved at each value when it has two or fewer.
fn mixed(sys: &System) -> Answer {
    let mut values: Vec<Int> = Vec::new();
    for (lo, hi) in sys.hub.pieces() {
        let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
            return Answer::MixedHub;
        };
        let (lo, hi) = (int(lo), int(hi));
        let mut c = lo;
        while c <= hi {
            if values.len() == 2 {
                return Answer::MixedHub;
            }
            values.push(c.clone());
            c = &c + &Int::ONE;
        }
    }
    let mut names: Option<Vec<(End, End)>> = None;
    let mut hub = IntervalSet::empty();
    for c in &values {
        let Some((lo, hi)) = members(sys, At::Value(c)) else {
            continue;
        };
        let these: Vec<(End, End)> = lo.iter().zip(&hi).map(|(l, h)| (end(l), end(h))).collect();
        names = Some(match names {
            None => these,
            Some(was) => was
                .into_iter()
                .zip(these)
                .map(|((l0, h0), (l1, h1))| (l0.min(l1), h0.max(h1)))
                .collect(),
        });
        hub = hub.join(&IntervalSet::point(Num::from(c)));
    }
    match names {
        Some(names) => Answer::Bounds { names, hub },
        None => Answer::Empty,
    }
}

/// Every coefficient at least 0: raising the hub only raises the least member and lowers the
/// greatest, so the hub's values that pass are its least value `p` up to some `c*`.
fn rising(sys: &System) -> Answer {
    let (p, q) = sys
        .hub
        .bounds()
        .map(|(p, q)| (p.clone(), q.clone()))
        .expect("the hub has values");
    let least: Option<Int> = match &p {
        End::Fin(p) => Some(int(p)),
        _ => None,
    };
    let at_p = least.as_ref().map_or(At::Below, At::Value);
    let Some((lo, hi)) = members(sys, at_p) else {
        return Answer::Empty;
    };
    let names: Vec<(End, End)> = lo.iter().zip(&hi).map(|(l, h)| (end(l), end(h))).collect();
    let passes = |c: &Int| members(sys, At::Value(c)).is_some();
    // A value that passes, to search from: `p`, or below the least constant when the hub has
    // no least value, found by doubling downward (each value below one that passes passes).
    // Complexity tradeoff: the search for the hub's greatest value that passes makes O(log W)
    // propagations, W the width of the hub's values (or the distance to the value where the
    // answer stops changing when the hub is unbounded), so the cost is O(N log N log W) and
    // not O(N log N). Why: whether a hub value passes depends on the whole component, and the
    // least member is not a function of the hub that one propagation could carry along.
    // Trigger: a hub whose values that pass end inside a wide interval. Test:
    // `l01_39_scope_relations::xst::threshold::the_hub_search_scales_with_the_digits_of_its_width`.
    // COMPLEXITY.md row S4-ti. A complete solution carries the least member as a piecewise
    // linear function of the hub through one propagation.
    let start: Int = match &p {
        End::Fin(p) => int(p),
        _ => {
            let mut c = match &q {
                End::Fin(q) => int(q).min(Int::ZERO),
                _ => Int::ZERO,
            };
            let mut step = Int::ONE;
            while !passes(&c) {
                c = &c - &step;
                step = &step + &step;
            }
            c
        }
    };
    // The greatest value that passes, by doubling upward when the hub has no greatest value
    // and the values past every integer do not pass, then halving.
    let top: Option<Int> = match &q {
        End::Fin(q) => {
            let q = int(q);
            if passes(&q) {
                Some(q)
            } else {
                Some(search(start, q, passes))
            }
        }
        _ if members(sys, At::Above).is_some() => None,
        _ => {
            let mut step = Int::ONE;
            let mut fail = &start + &step;
            while passes(&fail) {
                step = &step + &step;
                fail = &start + &step;
            }
            Some(search(start, fail, passes))
        }
    };
    let cut = match top {
        Some(t) => IntervalSet::range(End::NegInf, End::Fin(Num::from(&t))),
        None => IntervalSet::top(),
    };
    Answer::Bounds {
        names,
        hub: sys.hub.meet(&cut),
    }
}

/// The greatest value in `pass..fail` that passes, when `pass` passes and `fail` does not.
fn search(mut pass: Int, mut fail: Int, passes: impl Fn(&Int) -> bool) -> Int {
    let two = Int::from(2);
    while &pass + &Int::ONE < fail {
        let mid = (&pass + &fail).div_floor(&two);
        if passes(&mid) {
            pass = mid;
        } else {
            fail = mid;
        }
    }
    pass
}

/// A bound that one atom of a component puts on a name: an upper bound `x + k*w <= a` or a
/// lower bound `y - m*w >= b`, with `k` or `m` 0 when the atom does not mention the hub.
enum Bound {
    Upper(Arc<str>, Int, Int),
    Lower(Arc<str>, Int, Int),
}

/// The term of a constraint `t >= 0` that `f` is, when `f` is one: `t >= 0` itself, or
/// `-t - 1 >= 0` for `!(t >= 0)`.
fn at_least_zero(f: &Formula) -> Option<Lin> {
    let (t, negated) = ge_term(f)?;
    Some(if negated {
        Lin {
            terms: t.terms.iter().map(|(a, k)| (a.clone(), -k)).collect(),
            constant: &-&t.constant - &Int::ONE,
        }
    } else {
        t.clone()
    })
}

/// The term of an inequality, with whether the formula negates it.
fn ge_term(f: &Formula) -> Option<(&Lin, bool)> {
    match f {
        Formula::Con(c) if c.rel == Rel::Ge => Some((&c.lin, false)),
        Formula::Not(n) => match &**n {
            Formula::Con(c) if c.rel == Rel::Ge => Some((&c.lin, true)),
            _ => None,
        },
        _ => None,
    }
}

/// The bound that `t >= 0` puts on a name other than `hub`, its other name being `hub`; `None`
/// when `t` has another shape. A bound on the hub alone is `Err` with the hub's values it keeps.
fn bound(t: &Lin, hub: Option<&Arc<str>>) -> Option<Result<Bound, IntervalSet>> {
    let mut on: Option<(&Arc<str>, &Int)> = None;
    let mut h = Int::ZERO;
    for (a, k) in &t.terms {
        let Atom::Sym(n) = a else {
            return None;
        };
        if Some(n) == hub {
            h = k.clone();
        } else if on.replace((n, k)).is_some() {
            return None;
        }
    }
    let Some((x, kx)) = on else {
        // On the hub alone: `h*w + c >= 0`, `h` 1 or -1.
        let c = Num::from(&t.constant);
        return match h {
            h if h == Int::ONE => Some(Err(IntervalSet::range(
                End::Fin(Num::from(&-&t.constant)),
                End::PosInf,
            ))),
            h if h == -&Int::ONE => Some(Err(IntervalSet::range(End::NegInf, End::Fin(c)))),
            _ => None,
        };
    };
    // `x + h*w + c >= 0` is `x - (-h)*w >= -c`; `-x + h*w + c >= 0` is `x + (-h)*w <= c`.
    if *kx == Int::ONE {
        Some(Ok(Bound::Lower(x.clone(), -&h, -&t.constant)))
    } else if *kx == -&Int::ONE {
        Some(Ok(Bound::Upper(x.clone(), -&h, t.constant.clone())))
    } else {
        None
    }
}

/// A component read from its conjuncts, before the names' values are known.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The names other than the hub, in the order [`Upper::x`] and [`Lower::y`] index.
    pub names: Vec<Arc<str>>,
    /// The hub, when an atom mentions one.
    pub hub: Option<Arc<str>>,
    /// The hub's values that its own atoms keep.
    hub_values: IntervalSet,
    parts: Vec<(Upper, Lower)>,
    uppers: Vec<Upper>,
    lowers: Vec<Lower>,
}

impl Shape {
    /// The component with each name's values as `values` gives them.
    pub fn system(&self, values: impl Fn(&Arc<str>) -> IntervalSet) -> System {
        System {
            names: self.names.iter().map(&values).collect(),
            hub: match &self.hub {
                Some(w) => values(w).meet(&self.hub_values),
                None => IntervalSet::single(0),
            },
            parts: self.parts.clone(),
            uppers: self.uppers.clone(),
            lowers: self.lowers.clone(),
        }
    }
}

/// The conjuncts `gs` as a threshold-implication component, when they are one: each a
/// constraint (an equality being two) or a disjunction of two, of the shapes `x + k*w <= a` and
/// `y - m*w >= b` with one hub `w`, each disjunction an upper bound on one name and a lower
/// bound on another. In time O(N log N) for N atoms.
pub fn shape(gs: &[Arc<Formula>]) -> Option<Shape> {
    // The hub: the name every atom of two names shares.
    let mut hubs: Option<BTreeSet<Arc<str>>> = None;
    let mut atoms: Vec<(usize, Lin)> = Vec::new();
    let mut ors: Vec<bool> = Vec::new();
    for (i, g) in gs.iter().enumerate() {
        let lins: Vec<Lin> = match &**g {
            Formula::Con(c) if c.rel == Rel::Eq => {
                let neg = Lin {
                    terms: c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect(),
                    constant: -&c.lin.constant,
                };
                vec![c.lin.clone(), neg]
            }
            Formula::Or(cases) if cases.len() == 2 => {
                vec![at_least_zero(&cases[0])?, at_least_zero(&cases[1])?]
            }
            f => vec![at_least_zero(f)?],
        };
        ors.push(matches!(&**g, Formula::Or(_)));
        for t in lins {
            let names: BTreeSet<Arc<str>> = t
                .terms
                .keys()
                .map(|a| match a {
                    Atom::Sym(n) => Some(n.clone()),
                    _ => None,
                })
                .collect::<Option<_>>()?;
            if names.len() > 2 {
                return None;
            }
            if names.len() == 2 {
                hubs = Some(match hubs {
                    None => names,
                    Some(h) => h.intersection(&names).cloned().collect(),
                });
            }
            atoms.push((i, t));
        }
    }
    let candidates: Vec<Option<Arc<str>>> = match hubs {
        None => vec![None],
        Some(h) => h.into_iter().map(Some).collect(),
    };
    candidates
        .into_iter()
        .find_map(|hub| read(&atoms, &ors, hub))
}

/// [`shape`] with the hub `hub`.
fn read(atoms: &[(usize, Lin)], ors: &[bool], hub: Option<Arc<str>>) -> Option<Shape> {
    let mut index: BTreeMap<Arc<str>, usize> = BTreeMap::new();
    let mut names: Vec<Arc<str>> = Vec::new();
    let mut at = |x: &Arc<str>| {
        *index.entry(x.clone()).or_insert_with(|| {
            names.push(x.clone());
            names.len() - 1
        })
    };
    let mut out = Shape {
        names: Vec::new(),
        hub: hub.clone(),
        hub_values: IntervalSet::top(),
        parts: Vec::new(),
        uppers: Vec::new(),
        lowers: Vec::new(),
    };
    let mut i = 0;
    while i < atoms.len() {
        let (g, t) = &atoms[i];
        if ors[*g] {
            let (_, s) = &atoms[i + 1];
            let (Ok(one), Ok(two)) = (bound(t, hub.as_ref())?, bound(s, hub.as_ref())?) else {
                return None;
            };
            let (up, low) = match (one, two) {
                (Bound::Upper(x, k, a), Bound::Lower(y, m, b))
                | (Bound::Lower(y, m, b), Bound::Upper(x, k, a)) => ((x, k, a), (y, m, b)),
                _ => return None,
            };
            if up.0 == low.0 {
                return None;
            }
            out.parts.push((
                Upper {
                    x: at(&up.0),
                    k: up.1,
                    a: up.2,
                },
                Lower {
                    y: at(&low.0),
                    m: low.1,
                    b: low.2,
                },
            ));
            i += 2;
        } else {
            match bound(t, hub.as_ref())? {
                Err(w) => out.hub_values = out.hub_values.meet(&w),
                Ok(Bound::Upper(x, k, a)) => out.uppers.push(Upper { x: at(&x), k, a }),
                Ok(Bound::Lower(y, m, b)) => out.lowers.push(Lower { y: at(&y), m, b }),
            }
            i += 1;
        }
    }
    out.names = names;
    Some(out)
}

/// A unit-slope threshold row, read without building a component or copying its domains.
pub struct LeafRow {
    /// The name of the arm `x + w <= a`.
    pub x: Arc<str>,
    /// The name of the arm `y - w >= b`.
    pub y: Arc<str>,
    /// The name `w` both arms share.
    pub hub: Arc<str>,
    /// The bound `a` of `x + w <= a`.
    pub upper: Int,
    /// The bound `b` of `y - w >= b`.
    pub lower: Int,
}

/// Reads `x + w <= a || y - w >= b`, with three distinct names.
pub fn leaf_row(g: &Formula) -> Option<LeafRow> {
    let Formula::Or(arms) = g else { return None };
    let [a, b] = arms.as_slice() else { return None };
    let ((a, _), (b, _)) = (ge_term(a)?, ge_term(b)?);
    if a.terms.len() != 2 || b.terms.len() != 2 {
        return None;
    }
    let mut common = a.terms.keys().filter(|n| b.terms.contains_key(*n));
    let Atom::Sym(hub) = common.next()? else {
        return None;
    };
    if common.next().is_some() {
        return None;
    }
    let (Ok(a), Ok(b)) = (
        bound(&at_least_zero(&arms[0])?, Some(hub))?,
        bound(&at_least_zero(&arms[1])?, Some(hub))?,
    ) else {
        return None;
    };
    let (x, k, upper, y, m, lower) = match (a, b) {
        (Bound::Upper(x, k, a), Bound::Lower(y, m, b))
        | (Bound::Lower(y, m, b), Bound::Upper(x, k, a)) => (x, k, a, y, m, b),
        _ => return None,
    };
    (k == Int::ONE && m == Int::ONE).then(|| LeafRow {
        x,
        y,
        hub: hub.clone(),
        upper,
        lower,
    })
}
