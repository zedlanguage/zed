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
//! 1992, sec. 2.2 of the expanded text: an equality with a unit coefficient is solved for that
//! variable and substituted; the crate root's References) extended to guarded definitions; the
//! interval reading of the values given a pin is interval constraint propagation over the
//! definition order.
//!
//! Published work used in this file. Each site names the author; the full citation is in the
//! crate's `lib.rs`, "References". Kahn 1962, doi:10.1145/368996.369025; Tarjan 1975,
//! doi:10.1145/321879.321884 (union by size with path compression); Pugh 1991,
//! doi:10.1145/125826.125848; Pugh 1992 (the CACM text cited above),
//! doi:10.1145/135226.135233.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use zedc_int::int::{Int, row_range};
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

/// The compiled reading of `f` from one atom: the definitions taken, in Kahn's order with their
/// heads, the residuals, and the pin.
struct Reading<'p, 'a> {
    order: Vec<(&'p Def<'a>, Atom)>,
    residuals: Vec<&'a Formula>,
    pin: Option<Atom>,
}

/// What [`Prep::read`] needs of `f` that does not depend on the atom read from, built once for
/// all the names of a part ([`prepare`]): the conjuncts and those read as definitions, the
/// atoms numbered in the order of `Atom`, which of them a guard reads, and the incidence of
/// atoms and definitions.
pub(super) struct Prep<'a> {
    parts: Vec<&'a Formula>,
    defs: Vec<Option<Def<'a>>>,
    atoms: Vec<&'a Atom>,
    index: HashMap<&'a Atom, usize>,
    by_atom: Vec<Vec<usize>>,
    reads: Vec<Vec<usize>>,
    /// Each atom `x` as `sign * r + shift` for the atom `r` (by number) of its class: the atoms
    /// tied through equations of two atoms with coefficients 1 or -1 ([`Prep::class`]).
    tie: Vec<(usize, Int, Int)>,
    /// The definitions that read one atom, and the atoms no guard reads, in order.
    single: Vec<usize>,
    unguarded: Vec<usize>,
    /// The marks of [`Prep::read`], kept between readings and set back after each.
    scratch: RefCell<Scratch>,
}

/// The marks of one reading: the atoms known, the unknown atoms of each definition, the
/// definitions taken, and where they were changed, so that they are set back in that time.
struct Scratch {
    known: Vec<bool>,
    unknown: Vec<usize>,
    taken: Vec<bool>,
    atoms_set: Vec<usize>,
    defs_set: Vec<usize>,
}

/// The classes of the atoms `atoms` tied through the equations among `defs` of exactly two
/// atoms, each with coefficient 1 or -1: `a * y + b * x + c == 0` is `y = -a·b * x - a·c`, a
/// bijection between the values of `y` and of `x` at the points of `f`, so the projection of
/// `y` is that of `x` moved by it ([`Prep::carried`]). Each atom as `sign * r + shift` for its
/// class's atom `r`. An equation that closes a cycle adds nothing to the classes; it is a
/// conjunct of `f` like any other, and the ties used are all equations of `f`.
// Complexity tradeoff: union by size with path compression (Tarjan, "Efficiency of a good but
// not linear set union algorithm", JACM 22(2), 1975), each node holding its relation to its
// parent (the weighted union-find of the relation `x = ±y + c`), O(r·α(a)) for r equations
// over a atoms; the naive search of each pair of atoms for a path of equations is O(a·r).
fn ties(defs: &[Option<Def>], index: &HashMap<&Atom, usize>) -> Vec<(usize, Int, Int)> {
    let n = index.len();
    let mut up: Vec<(usize, Int, Int)> = (0..n).map(|j| (j, Int::ONE, Int::ZERO)).collect();
    let mut size = vec![1usize; n];
    // `j` as `sign * root + shift`, every node on its path pointed at the root.
    fn find(up: &mut [(usize, Int, Int)], j: usize) -> (usize, Int, Int) {
        let mut path = Vec::new();
        let mut r = j;
        while up[r].0 != r {
            path.push(r);
            r = up[r].0;
        }
        // Nearest the root first: each node's parent already points at the root, so
        // `x = s * p + c` and `p = ps * root + pc` give `x = s·ps * root + s·pc + c`.
        for &x in path.iter().rev() {
            let (p, s, c) = up[x].clone();
            if p != r {
                let (_, ps, pc) = up[p].clone();
                up[x] = (r, &s * &ps, &(&s * &pc) + &c);
            }
        }
        if j == r {
            (r, Int::ONE, Int::ZERO)
        } else {
            up[j].clone()
        }
    }
    for d in defs.iter().flatten() {
        let Def::Eq(e) = d else { continue };
        let mut terms = e.terms.iter();
        let (Some((y, a)), Some((x, b)), None) = (terms.next(), terms.next(), terms.next()) else {
            continue;
        };
        if a.abs() != Int::ONE || b.abs() != Int::ONE {
            continue;
        }
        // `y = sigma * x + delta`, with `a` its own inverse.
        let sigma = -&(a * b);
        let mut delta = -&(a * &e.constant);
        let (ry, sy, cy) = find(&mut up, index[y]);
        let (rx, sx, cx) = find(&mut up, index[x]);
        if ry == rx {
            continue;
        }
        // The smaller class goes under the larger: `x = sigma * y - sigma * delta` as well.
        let ((ry, sy, cy), (rx, sx, cx)) = if size[ry] > size[rx] {
            delta = -&(&sigma * &delta);
            ((rx, sx, cx), (ry, sy, cy))
        } else {
            ((ry, sy, cy), (rx, sx, cx))
        };
        // `sy * ry + cy = sigma * (sx * rx + cx) + delta`, `sy` its own inverse.
        up[ry] = (
            rx,
            &sy * &(&sigma * &sx),
            &sy * &(&(&(&sigma * &cx) + &delta) - &cy),
        );
        size[rx] += size[ry];
    }
    (0..n).map(|j| find(&mut up, j)).collect()
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

/// The part of the reading of `f` that does not depend on the atom read from ([`Prep`]), once
/// for all the names of a part; `None` where a product is read, or where no atom could be read
/// from: a reading learns the atom it starts from, at most one pin, and one head for each
/// definition it takes, so with more atoms than the definitions plus 2 it declines from every
/// atom, and so does each certificate of the part.
// Complexity tradeoff: one pass over the constraints, O(r·t) for r constraints of t terms, a
// piece charged for each constraint read (not one for each conjunct, which left the meter
// blind to a disjunction's constraints), plus O(a log a) to number the a atoms in their order
// (so that the pin does not depend on the order of the parts). Built once a part, not once a
// name: built for each name, it was O(k·r·t) for the k names of a part whatever the readings
// did, 32.7 times the instructions at 8n on `wide_pairs_scale` (k = r = n, so O(n²)), and its
// time ran out on the disjoint groups (PRES-groupA-forward-per-part). The count of atoms
// against definitions rejects such a part with no reading at all.
pub(super) fn prepare<'a>(f: &'a Formula, work: &mut Work) -> Result<Option<Prep<'a>>, Refusal> {
    let parts = f.conjuncts();
    let mut defs: Vec<Option<Def<'a>>> = Vec::with_capacity(parts.len());
    let mut all: HashSet<&Atom> = HashSet::new();
    let mut found = false;
    for g in &parts {
        let mut read = 0;
        each_constraint(g, |c| {
            read += 1;
            for a in c.lin.terms.keys() {
                found |= matches!(a, Atom::Product(..));
                all.insert(a);
            }
        });
        work.charge(PIECE.saturating_mul(read))?;
        defs.push(match g {
            Formula::Con(Con { lin, rel: Rel::Eq }) => Some(Def::Eq(lin)),
            _ => choice(g),
        });
    }
    if found || all.len() > defs.iter().flatten().count() + 2 {
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
    let tie = ties(&defs, &index);
    let single = (0..defs.len()).filter(|&i| reads[i].len() == 1).collect();
    let unguarded = (0..atoms.len()).filter(|&j| !guarded[j]).collect();
    let scratch = RefCell::new(Scratch {
        known: vec![false; atoms.len()],
        unknown: reads.iter().map(Vec::len).collect(),
        taken: vec![false; defs.len()],
        atoms_set: Vec::new(),
        defs_set: Vec::new(),
    });
    Ok(Some(Prep {
        parts,
        defs,
        atoms,
        index,
        by_atom,
        reads,
        tie,
        single,
        unguarded,
        scratch,
    }))
}

impl<'a> Prep<'a> {
    /// The class of `s` among the atoms tied through equations of two atoms ([`ties`]).
    pub(super) fn class(&self, s: &Atom) -> Option<usize> {
        self.index.get(s).map(|&j| self.tie[j].0)
    }

    /// The projection of `s` from `set`, that of `from`, an atom of the same class: `s` is
    /// `sign * from + shift` at every point of the part, a bijection, so its projection is
    /// `set` moved by it. `None` where the two are not of one class.
    pub(super) fn carried(&self, s: &Atom, from: &Atom, set: &IntervalSet) -> Option<IntervalSet> {
        let (r, ss, cs) = &self.tie[*self.index.get(s)?];
        let (q, sf, cf) = &self.tie[*self.index.get(from)?];
        if r != q {
            return None;
        }
        // `from = sf * r + cf`, so `r = sf * (from - cf)` and `s = ss·sf * from + cs - ss·sf·cf`.
        let sign = ss * sf;
        let shift = cs - &(&sign * cf);
        let moved = |e: &End| match e {
            End::Fin(n) => fin(&(&(&sign * &Int::from(n)) + &shift)),
            End::NegInf | End::PosInf if sign.is_negative() => -e,
            e => e.clone(),
        };
        let mut pieces: Vec<(End, End)> = set
            .pieces()
            .map(|(lo, hi)| (moved(lo), moved(hi)))
            .collect();
        if sign.is_negative() {
            pieces = pieces.into_iter().rev().map(|(lo, hi)| (hi, lo)).collect();
        }
        Some(IntervalSet::from_pieces(pieces))
    }

    /// The definitions and residuals from `s` ([module note](self)); `None` where a second
    /// atom must be left free.
    // Complexity tradeoff: Kahn's order over the atom incidence of the definitions, O(r·t) for
    // r conjuncts of t terms; the naive repeated pass over all definitions until none is taken
    // is O(r²·t). The marks are the part's own (`Prep::scratch`), set back after each reading
    // where it set them, and the definitions with one atom and the atoms no guard reads are
    // listed once a part: a reading costs the atoms it learns and the definitions that read
    // them, each charged a piece, not O(a + r) for every name whatever it reads. Before, each
    // name built its marks anew, scanned every definition and every atom, and charged neither,
    // so a part whose readings stop early cost O(k·(a + r)) unseen by the meter: 23.9 and 35.9
    // times the time at 8 times k on `tests::names_tied_through_three_atoms_are_read_once_for_
    // the_part` and `..._with_coefficients_past_one_...`, within 10.5 in the units charged. A
    // reading that learns every atom is still O(r·t), so for the k names of such a part
    // O(k·r·t) in all (PRES-groupA-forward-per-name-order, part 2, open).
    fn read<'p>(&'p self, s: &Atom, work: &mut Work) -> Result<Option<Reading<'p, 'a>>, Refusal> {
        let Prep {
            parts,
            defs,
            atoms,
            index,
            by_atom,
            reads,
            single,
            unguarded,
            scratch,
            ..
        } = self;
        let mut marks = scratch.borrow_mut();
        let marks = &mut *marks;
        let got = (|| {
            let mut left = atoms.len();
            let mut queue: Vec<usize> = single.clone();
            let mut order: Vec<(usize, Atom)> = Vec::new();
            let mut pin = None;
            // Marks atom `x` known and queues the definitions left with one unknown atom; a
            // piece for each definition that reads it.
            let learn = |x: usize,
                         marks: &mut Scratch,
                         queue: &mut Vec<usize>,
                         left: &mut usize,
                         work: &mut Work|
             -> Result<(), Refusal> {
                if !marks.known[x] {
                    work.charge(PIECE.saturating_mul(by_atom[x].len() as u64))?;
                    marks.known[x] = true;
                    marks.atoms_set.push(x);
                    *left -= 1;
                    for &i in &by_atom[x] {
                        if marks.unknown[i] == reads[i].len() {
                            marks.defs_set.push(i);
                        }
                        marks.unknown[i] -= 1;
                        if marks.unknown[i] == 1 {
                            queue.push(i);
                        }
                    }
                }
                Ok(())
            };
            if let Some(&x) = index.get(s) {
                learn(x, marks, &mut queue, &mut left, work)?;
            }
            // The least atom no guard reads not yet known: those before it are known for
            // the rest of the reading, so the walk is at most the atoms learned.
            let mut next_free = 0;
            loop {
                while let Some(i) = queue.pop() {
                    work.charge(PIECE)?;
                    let Some(d) = &defs[i] else { continue };
                    if marks.taken[i] || marks.unknown[i] != 1 {
                        continue;
                    }
                    let Some(&x) = reads[i].iter().find(|&&j| !marks.known[j]) else {
                        continue;
                    };
                    if !d.may_define(atoms[x]) {
                        continue;
                    }
                    marks.taken[i] = true;
                    marks.defs_set.push(i);
                    order.push((i, atoms[x].clone()));
                    learn(x, marks, &mut queue, &mut left, work)?;
                }
                if left == 0 {
                    break;
                }
                if pin.is_some() {
                    return Ok(None);
                }
                // The least unknown atom read by no guard: a guard reading the pin would
                // decline.
                while next_free < unguarded.len() && marks.known[unguarded[next_free]] {
                    next_free += 1;
                }
                let Some(&x) = unguarded.get(next_free) else {
                    return Ok(None);
                };
                pin = Some(atoms[x].clone());
                learn(x, marks, &mut queue, &mut left, work)?;
            }
            Ok(Some((order, pin)))
        })();
        // The marks set back where this reading set them.
        for x in marks.atoms_set.drain(..) {
            marks.known[x] = false;
        }
        for i in marks.defs_set.drain(..) {
            marks.unknown[i] = reads[i].len();
            marks.taken[i] = false;
        }
        let Some((order, pin)) = got? else {
            return Ok(None);
        };
        let taken: HashSet<usize> = order.iter().map(|(i, _)| *i).collect();
        let mut residuals = Vec::new();
        for (i, g) in parts.iter().enumerate() {
            if !taken.contains(&i) {
                residuals.push(*g);
            }
        }
        let order = (order.into_iter())
            .map(|(i, x)| (defs[i].as_ref().expect("a taken definition"), x))
            .collect();
        Ok(Some(Reading {
            order,
            residuals,
            pin,
        }))
    }
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
    // `a * p + r >= 0`.
    let (lo, hi) = row_range(a, &r, false).0;
    IntervalSet::range(
        lo.as_ref().map_or(End::NegInf, fin),
        hi.as_ref().map_or(End::PosInf, fin),
    )
}

/// The pins `p` with `a * p + hi <= k`.
fn at_most(a: &Int, hi: Option<&Int>, k: &Int) -> IntervalSet {
    at_least(&-a, hi.map(|h| -h).as_ref(), &-k)
}

/// The pins at which `f` (negated where `neg`) holds for every value in its atoms' intervals.
// Complexity tradeoff: one visit of each shared part per sign (memo by `Id`), O(size of f); the
// tree walk without the memo is exponential in the sharing depth (DAG visited set, P207). The parts
// waiting for their children are on an explicit stack, not the call stack: a recursive walk
// overflowed the stack on a chain 24,000 rules deep (FAIL-ids-shared-parts-stack-overflow,
// `bench::ids::passes_over_shared_parts_take_time_linear_in_the_distinct_parts`).
fn pins(
    f: &Formula,
    neg: bool,
    vals: &HashMap<&Atom, Val>,
    memo: &mut HashMap<(Id, bool), IntervalSet>,
    work: &mut Work,
) -> Result<IntervalSet, Refusal> {
    /// A negation, conjunction or disjunction whose children are being read: `next` is the
    /// index of the next child, and `out` the set of those read.
    struct Part<'f> {
        f: &'f Formula,
        neg: bool,
        key: Option<(Id, bool)>,
        next: usize,
        out: IntervalSet,
    }
    // Whether the children of `f` (negated where `neg`) are met (else joined).
    let meets = |f: &Formula, neg: bool| matches!(f, Formula::And(_)) != neg;
    let mut stack: Vec<Part> = Vec::new();
    // The part to read next, or the set of the one just read.
    let mut down = Some((f, neg));
    let mut up: Option<IntervalSet> = None;
    loop {
        if let Some((g, neg)) = down.take() {
            let key = Id::of(g).map(|k| (k, neg));
            if let Some(set) = key.as_ref().and_then(|k| memo.get(k)) {
                up = Some(set.clone());
            } else if let Formula::Con(c) = g {
                work.charge(PIECE)?;
                let set = con_pins(c, neg, vals);
                if let Some(k) = key {
                    memo.insert(k, set.clone());
                }
                up = Some(set);
            } else {
                let out = if !matches!(g, Formula::Not(_)) && meets(g, neg) {
                    IntervalSet::top()
                } else {
                    IntervalSet::empty()
                };
                stack.push(Part {
                    f: g,
                    neg,
                    key,
                    next: 0,
                    out,
                });
            }
        }
        let Some(top) = stack.last_mut() else {
            return Ok(up.expect("the set of `f`"));
        };
        let children: &[Formula] = match top.f {
            Formula::Not(g) => std::slice::from_ref(&**g),
            Formula::And(gs) | Formula::Or(gs) => gs,
            Formula::Con(_) => unreachable!("a constraint is read where it is met"),
        };
        if let Some(x) = up.take() {
            if matches!(top.f, Formula::Not(_)) {
                top.out = x;
            } else if meets(top.f, top.neg) {
                top.out = top.out.meet(&x);
                if top.out.is_empty() {
                    top.next = children.len();
                }
            } else {
                top.out = top.out.join(&x);
            }
        }
        if let Some(g) = children.get(top.next) {
            top.next += 1;
            let flip = matches!(top.f, Formula::Not(_));
            down = Some((g, top.neg != flip));
            continue;
        }
        let done = stack.pop().expect("the part on top");
        if let Some(k) = done.key {
            memo.insert(k, done.out.clone());
        }
        up = Some(done.out);
    }
}

/// The pins at which the constraint `c` (negated where `neg`) holds for every value in its
/// atoms' intervals.
fn con_pins(c: &Con, neg: bool, vals: &HashMap<&Atom, Val>) -> IntervalSet {
    let v = value(&c.lin, vals);
    let (lo, hi) = (v.lo.as_ref(), v.hi.as_ref());
    let (zero, one) = (Int::ZERO, Int::ONE);
    match (c.rel, neg) {
        (Rel::Ge, false) => at_least(&v.slope, lo, &zero),
        (Rel::Ge, true) => at_most(&v.slope, hi, &-&one),
        (Rel::Eq, false) => at_least(&v.slope, lo, &zero).meet(&at_most(&v.slope, hi, &zero)),
        (Rel::Eq, true) => at_least(&v.slope, lo, &one).join(&at_most(&v.slope, hi, &-&one)),
    }
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
/// where the reading or a piece declines. For one name; the names of a part share one
/// [`prepare`] through [`forward_in`].
#[cfg(test)]
pub(super) fn forward(
    f: &Formula,
    s: &Atom,
    h: &IntervalSet,
    work: &mut Work,
) -> Result<Option<IntervalSet>, Refusal> {
    let Some(prep) = prepare(f, work)? else {
        return Ok(None);
    };
    forward_in(&prep, s, h, work)
}

/// `forward` on the part `prep` was prepared from.
pub(super) fn forward_in(
    prep: &Prep,
    s: &Atom,
    h: &IntervalSet,
    work: &mut Work,
) -> Result<Option<IntervalSet>, Refusal> {
    let Some(r) = prep.read(s, work)? else {
        return Ok(None);
    };
    for (lo, hi) in h.pieces() {
        if !certified(&r, s, lo, hi, work)? {
            return Ok(None);
        }
    }
    Ok(Some(h.clone()))
}

#[cfg(test)]
mod tests;
mod two_pins;
