//! The reading of a whole part with two pins (PRES-groupA-forward-per-name-order, part 2b): the
//! part is read once, every atom a form `α·p + β·q + γ` in two free atoms `p` and `q`, and each
//! name's projection is read off the integer points of the polygon its residuals cut out.
//!
//! The reading. From no atom known, a definition (an equation whose head has coefficient 1 or
//! -1, [`Def::Eq`]) is taken once its head is its only unknown atom (Kahn's order, as
//! [`Prep::read`]); where none can be taken and atoms are unknown, one becomes a pin: first an
//! atom that no definition may have as its head (it is free in every reading), else the least
//! unknown one. A third pin declines, and so does a part with a choice (its guard would split
//! the plane; choices are open). Each head is an integer form in the pins, since its
//! coefficient is 1 or -1. Every conjunct not taken is a residual, which must be a row
//! (`t >= 0`, `t == 0`, or `!(t >= 0)`): over the pins, a half-plane `A·p + B·q + C >= 0` (an
//! equation two of them).
//!
//! Exactness. Each integer `(p, q)` gives exactly one value of every atom, and every taken
//! definition holds there by the choice of its head; so the points of the part are exactly the
//! integer `(p, q)` of the polygon, each atom at its form. The values of a name `α·p + β·q + γ`
//! are `γ + g·u` for `g = gcd(α, β)` and `u = a·p + b·q`, `a = α/g`, `b = β/g` coprime: every
//! `g`-th value, a class modulo `g`, where `g > 1`. With `s·a + t·b == 1` (Bezout), the change
//! of coordinates `p = s·u - b·w`, `q = t·u + a·w` is unimodular (determinant `s·a + t·b`), so
//! the integer `(p, q)` are the integer `(u, w)`, and each half-plane reads
//! `E·u + D·w + C >= 0` with `E = A·s + B·t`, `D = B·a - A·b`. A value `u` has a point exactly
//! when the rows with `D == 0` hold and some integer `w` lies between the lower bounds
//! (`D > 0`) and the upper ones (`D < 0`). Fourier-Motzkin over `w` gives the real shadow, a
//! range holding every such `u`; Pugh's dark shadow, each pair's condition raised by
//! `(D_l - 1)·(-D_u - 1)`, a range of `u` each of which has an integer `w` (W. Pugh, "The Omega
//! test", CACM 35(8), 1992, sec. 3: where the greatest lower and least upper bound are at least
//! that far apart, an integer lies between them). The values of the real shadow outside the dark
//! one are tried one by one, each with the integer bounds of `w` (the splinters, decided here
//! value by value rather than by Pugh's equalities). So the set is exact; where it is unbounded,
//! empty, or a number passes `i128`, the reading declines and the per-name certificate or the
//! cover answers.
//!
//! Prior work in this crate: `row_sums::plane` projects the same polygons by the real shadow
//! where it is exact (a pair with a side of coefficient 1) and leaves forms with a common
//! factor to the join; here the dark shadow and the splinters make every pair exact, and a
//! common factor gives a class.

use std::collections::HashMap;

use zedc_int::int::{Int, Num};
use zedc_lattice::interval::{End, IntervalSet};
use zedc_lattice::lattice::Congruence;

use super::super::super::meter::{PIECE, Work};
use super::super::super::row_sums::plane::{bezout, div_ceil, div_floor};
use super::super::super::{Atom, Classed, Con, Formula, Lin, Refusal, Rel};
use super::{Def, Prep};

/// `α·p + β·q + γ`.
type Form = (i128, i128, i128);

/// The part read with two pins ([module note](self)): each atom's form and the half-planes of
/// the residuals.
pub(in super::super) struct TwoPins<'p, 'a> {
    prep: &'p Prep<'a>,
    forms: Vec<Form>,
    halves: Vec<Form>,
    /// The polygon's edges, where it is bounded with interior ([`edges`]).
    poly: Option<Polygon>,
}

/// `c·f`, or `None` past `i128`.
fn times(c: i128, f: Form) -> Option<Form> {
    Some((
        c.checked_mul(f.0)?,
        c.checked_mul(f.1)?,
        c.checked_mul(f.2)?,
    ))
}

/// `f + g`, or `None` past `i128`.
fn plus(f: Form, g: Form) -> Option<Form> {
    Some((
        f.0.checked_add(g.0)?,
        f.1.checked_add(g.1)?,
        f.2.checked_add(g.2)?,
    ))
}

/// The form of `lin` given each atom's form.
fn form_of(lin: &Lin, index: &HashMap<&Atom, usize>, forms: &[Form]) -> Option<Form> {
    let mut out = (0, 0, lin.constant.to_i128()?);
    for (a, c) in &lin.terms {
        out = plus(out, times(c.to_i128()?, forms[index[a]])?)?;
    }
    Some(out)
}

impl<'a> Prep<'a> {
    /// The part read with at most two pins ([module note](self)); `None` where it declines.
    // Complexity tradeoff: one Kahn's order over the whole part, O(r·t) for r conjuncts of t
    // terms, a piece charged for each definition visited and each incidence of an atom learned,
    // once a part; then O(r·t) for the forms and the half-planes. Naive version (each name's own
    // reading, `Prep::read`): O(r·t) a name, O(k·r·t) for the k names of a part, where the reading
    // from each name learns the whole part (`y(j) == 2·p + 3·q + j`: 17.5 times the work at 8
    // times k, `tests::names_with_coefficients_past_one_are_read_once_for_the_part`).
    pub(in super::super) fn two_pins<'p>(
        &'p self,
        work: &mut Work,
    ) -> Result<Option<TwoPins<'p, 'a>>, Refusal> {
        let Prep {
            parts,
            defs,
            atoms,
            index,
            by_atom,
            reads,
            ..
        } = self;
        if defs
            .iter()
            .flatten()
            .any(|d| matches!(d, Def::Choice { .. }))
        {
            return Ok(None);
        }
        // The atoms some definition may have as head; the others can only be pins.
        let mut headed = vec![false; atoms.len()];
        for (i, d) in defs.iter().enumerate() {
            let Some(d) = d else { continue };
            work.charge(PIECE.saturating_mul(reads[i].len() as u64))?;
            for &j in &reads[i] {
                headed[j] |= d.may_define(atoms[j]);
            }
        }
        let mut known = vec![false; atoms.len()];
        let mut unknown: Vec<usize> = reads.iter().map(Vec::len).collect();
        let mut taken = vec![false; defs.len()];
        let mut forms: Vec<Form> = vec![(0, 0, 0); atoms.len()];
        let mut queue: Vec<usize> = (0..defs.len()).filter(|&i| unknown[i] == 1).collect();
        let mut left = atoms.len();
        let mut pins = 0;
        // The next atom to try as a pin, in each of the two orders: atoms before it are known.
        let (mut next_free, mut next_any) = (0, 0);
        let free: Vec<usize> = (0..atoms.len()).filter(|&j| !headed[j]).collect();
        loop {
            while let Some(i) = queue.pop() {
                work.charge(PIECE)?;
                let Some(Def::Eq(e)) = &defs[i] else { continue };
                if taken[i] || unknown[i] != 1 {
                    continue;
                }
                let Some(&x) = reads[i].iter().find(|&&j| !known[j]) else {
                    continue;
                };
                if !defs[i].as_ref().is_some_and(|d| d.may_define(atoms[x])) {
                    continue;
                }
                // `c·x + rest == 0` with `c` 1 or -1: `x = -c·rest`.
                let c = e.terms[atoms[x]]
                    .to_i128()
                    .expect("a coefficient of 1 or -1");
                let Some(f) = (|| {
                    let mut out = (0, 0, e.constant.to_i128()?);
                    for (a, k) in &e.terms {
                        let j = index[a];
                        if j != x {
                            out = plus(out, times(k.to_i128()?, forms[j])?)?;
                        }
                    }
                    times(-c, out)
                })() else {
                    return Ok(None);
                };
                taken[i] = true;
                forms[x] = f;
                learn(
                    x,
                    &mut known,
                    &mut unknown,
                    &mut queue,
                    &mut left,
                    by_atom,
                    work,
                )?;
            }
            if left == 0 {
                break;
            }
            if pins == 2 {
                return Ok(None);
            }
            while next_free < free.len() && known[free[next_free]] {
                next_free += 1;
            }
            while next_any < atoms.len() && known[next_any] {
                next_any += 1;
            }
            let x = free.get(next_free).copied().unwrap_or(next_any);
            forms[x] = if pins == 0 { (1, 0, 0) } else { (0, 1, 0) };
            pins += 1;
            learn(
                x,
                &mut known,
                &mut unknown,
                &mut queue,
                &mut left,
                by_atom,
                work,
            )?;
        }
        // The residuals as half-planes over the pins.
        let mut halves = Vec::new();
        for (i, g) in parts.iter().enumerate() {
            if taken[i] {
                continue;
            }
            work.charge(PIECE)?;
            let (lin, both) = match g {
                Formula::Con(Con { lin, rel }) => (lin.clone(), *rel == Rel::Eq),
                Formula::Not(n) => match &**n {
                    Formula::Con(Con { lin, rel: Rel::Ge }) => {
                        (lin.times(-1).plus(&Lin::constant(-1)), false)
                    }
                    _ => return Ok(None),
                },
                _ => return Ok(None),
            };
            let Some(f) = form_of(&lin, index, &forms) else {
                return Ok(None);
            };
            let mut add = |f: Form| -> bool {
                if f.0 == 0 && f.1 == 0 {
                    // No pin: true, or the part has no point (left to the cover).
                    return f.2 >= 0;
                }
                halves.push(f);
                true
            };
            if !add(f) {
                return Ok(None);
            }
            if both {
                let Some(n) = times(-1, f) else {
                    return Ok(None);
                };
                if !add(n) {
                    return Ok(None);
                }
            }
        }
        let h = halves.len() as u64;
        work.charge(
            PIECE.saturating_mul(h.saturating_mul(u64::from(u64::BITS - h.leading_zeros() + 1))),
        )?;
        let poly = edges(&halves);
        Ok(Some(TwoPins {
            prep: self,
            forms,
            halves,
            poly,
        }))
    }
}

/// Marks `x` known and queues the definitions left with one unknown atom; a piece for each
/// definition that reads it.
fn learn(
    x: usize,
    known: &mut [bool],
    unknown: &mut [usize],
    queue: &mut Vec<usize>,
    left: &mut usize,
    by_atom: &[Vec<usize>],
    work: &mut Work,
) -> Result<(), Refusal> {
    if !known[x] {
        work.charge(PIECE.saturating_mul(by_atom[x].len() as u64))?;
        known[x] = true;
        *left -= 1;
        for &i in &by_atom[x] {
            unknown[i] -= 1;
            if unknown[i] == 1 {
                queue.push(i);
            }
        }
    }
    Ok(())
}

impl TwoPins<'_, '_> {
    /// The exact projection of the part onto `s` ([module note](self)); `None` where it
    /// declines.
    // Complexity tradeoff: where the polygon is bounded with interior, its V edges are found
    // once a part in O(h log h) ([`edges`]) and each name costs O((log d + S)·log V) for the
    // distance d from an end of its range to the values with a stretch of `w` at least 1 long
    // and the S values tried one by one ([`poly_values`]): O(h log h + k·log h) a part where d
    // and S do not grow. Otherwise (open, flat, or past `i128`) O(h²) a name for the pairs of
    // the shadows plus O(h) a value tried ([`u_values`]), O(k·h²) a part; an open polygon's
    // half-planes are not pruned, so many residuals there still cost that (PRES-two-pin-edges
    // leaves it; the unbounded test has h = 2).
    pub(in super::super) fn values(
        &self,
        s: &Atom,
        work: &mut Work,
    ) -> Result<Option<Classed>, Refusal> {
        let Some(&j) = self.prep.index.get(s) else {
            return Ok(None);
        };
        let (al, be, ga) = self.forms[j];
        // A name fixed by the part: its one value, where the part has a point.
        let (g, a, b) = if al == 0 && be == 0 {
            (0, 1, 0)
        } else {
            let g = Int::from(al).gcd(&Int::from(be)).to_i128();
            let Some(g) = g.filter(|g| *g > 0) else {
                return Ok(None);
            };
            (g, al / g, be / g)
        };
        let us = match &self.poly {
            Some(poly) => poly_values(poly, (a, b), work)?,
            None => u_values(a, b, &self.halves, work)?,
        };
        let Some(us) = us else {
            return Ok(None);
        };
        if us.is_empty() {
            return Ok(None);
        }
        if g == 0 {
            return Ok(Some(Classed::plain(IntervalSet::point(Num::from(ga)))));
        }
        // A class other than every integer takes finite ranges (`Classed::new`); an open end
        // there declines to the per-name path.
        if g > 1 && us.iter().any(|(lo, hi)| lo.is_none() || hi.is_none()) {
            return Ok(None);
        }
        let mut pieces = Vec::with_capacity(us.len());
        for (lo, hi) in us {
            // `g > 0`, so an open end stays on its side.
            let at = |u: Option<i128>, open: End| match u {
                None => Some(open),
                Some(u) => Some(End::Fin(Num::from(g.checked_mul(u)?.checked_add(ga)?))),
            };
            let (Some(lo), Some(hi)) = (at(lo, End::NegInf), at(hi, End::PosInf)) else {
                return Ok(None);
            };
            pieces.push((lo, hi));
        }
        let ranges = IntervalSet::from_pieces(pieces);
        Ok(Some(if g == 1 {
            Classed::plain(ranges)
        } else {
            Classed::new(
                ranges,
                Congruence::new(Num::from(g), Num::from(ga.rem_euclid(g))),
            )
        }))
    }
}

/// The values of `u = a·p + b·q` (`a`, `b` coprime) over the integer points of `halves`, as
/// sorted runs; `Ok(None)` where it declines (an open end the dark shadow does not share, or
/// past `i128`) ([module note](self)).
fn u_values(
    a: i128,
    b: i128,
    halves: &[Form],
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    let Some((s, t)) = bezout(a, b) else {
        return Ok(None);
    };
    // Each half-plane as `E·u + D·w + C >= 0`, and the same with the two coordinates swapped.
    let mut uw: Vec<Row> = Vec::with_capacity(halves.len());
    for &(ha, hb, hc) in halves {
        let row = (|| {
            let e = ha.checked_mul(s)?.checked_add(hb.checked_mul(t)?)?;
            let d = hb.checked_mul(a)?.checked_sub(ha.checked_mul(b)?)?;
            Some((e, d, hc))
        })();
        let Some(row) = row else {
            return Ok(None);
        };
        uw.push(row);
    }
    let wu: Vec<Row> = uw.iter().map(|&(e, d, c)| (d, e, c)).collect();
    let h = halves.len() as u64;
    work.charge(PIECE.saturating_mul(3 * h * h + h))?;
    let (Some(real), Some(dark), Some(across)) =
        (shadow(&uw, false), shadow(&uw, true), shadow(&wu, false))
    else {
        return Ok(None);
    };
    let (Some(real), Some((wl, wh))) = (real, across) else {
        // No integer point: the real shadow of one coordinate or the other is empty.
        return Ok(Some(Vec::new()));
    };
    // An end of the real shadow that is open: every value past it has a point exactly where the
    // dark shadow is open at the same end (each of its values has an integer `w`), and then
    // only the finite stretch outside the dark shadow is tried. Where the real shadow is open
    // and the dark one is not (a strip whose fiber stays shorter than Pugh's bound, the values
    // with a point periodic rather than all), the reading declines. Each open end is cut at a
    // value inside the dark shadow, and the run reaching the cut is opened again at the end.
    let (open_lo, open_hi) = (real.0.is_none(), real.1.is_none());
    let Some((dl, dh)) = dark else {
        if open_lo || open_hi {
            return Ok(None);
        }
        return u_runs(real, None, (wl, wh), &uw, &wu, h, work);
    };
    if (open_lo && dl.is_some()) || (open_hi && dh.is_some()) {
        return Ok(None);
    }
    // A finite value of the dark shadow, within the real one.
    let inside = dl.or(dh).or(real.0).or(real.1).unwrap_or(0);
    let rl = real.0.unwrap_or(inside);
    let rh = real.1.unwrap_or(inside).max(rl);
    let Some(mut runs) = u_runs(
        (Some(rl), Some(rh)),
        Some((dl, dh)),
        (wl, wh),
        &uw,
        &wu,
        h,
        work,
    )?
    else {
        return Ok(None);
    };
    if open_lo && let Some(first) = runs.first_mut() {
        first.0 = None;
    }
    if open_hi && let Some(last) = runs.last_mut() {
        last.1 = None;
    }
    Ok(Some(runs))
}

/// The runs of [`u_values`] within the finite real shadow `real`, with the dark shadow `dark`
/// (`None` where empty) and the real shadow `(wl, wh)` of the other coordinate.
#[allow(clippy::too_many_arguments)]
fn u_runs(
    real: (Option<i128>, Option<i128>),
    dark: Option<(Option<i128>, Option<i128>)>,
    (wl, wh): (Option<i128>, Option<i128>),
    uw: &[Row],
    wu: &[Row],
    h: u64,
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    let (Some(rl), Some(rh)) = real else {
        return Ok(None);
    };
    // The dark shadow within the real one.
    let dark = dark
        .map(|(l, h)| (l.map_or(rl, |l| l.max(rl)), h.map_or(rh, |h| h.min(rh))))
        .filter(|(l, h)| l <= h);
    let dark_size = dark.map_or(0, |(l, h)| h - l + 1);
    let Some(splinters) = rh
        .checked_sub(rl)
        .and_then(|n| n.checked_add(1 - dark_size))
    else {
        return Ok(None);
    };
    let width = match (wl, wh) {
        (Some(l), Some(h)) => h.checked_sub(l).and_then(|n| n.checked_add(1)),
        _ => None,
    };
    let mut runs: Vec<(i128, i128)> = Vec::new();
    if let (Some(width), Some(wl), Some(wh)) = (width, wl, wh)
        && width < splinters
    {
        // The narrower way: each integer `w` of the polygon gives one interval of `u`.
        for w in wl..=wh {
            work.charge(PIECE.saturating_mul(h))?;
            match fiber(wu, w) {
                None => return Ok(None),
                Some(None) => {}
                Some(Some((l, h))) => {
                    let (l, h) = (l.map_or(rl, |l| l.max(rl)), h.map_or(rh, |h| h.min(rh)));
                    if l <= h {
                        runs.push((l, h));
                    }
                }
            }
        }
        runs.sort_unstable();
        let mut merged: Vec<(i128, i128)> = Vec::with_capacity(runs.len());
        for (l, h) in runs {
            match merged.last_mut() {
                Some((_, e)) if *e >= l - 1 => *e = (*e).max(h),
                _ => merged.push((l, h)),
            }
        }
        return Ok(Some(finite(merged)));
    }
    // The values of the real shadow outside the dark one, each tried for an integer `w`.
    let mut add = |l: i128, h: i128| match runs.last_mut() {
        Some((_, e)) if *e + 1 == l => *e = h,
        _ => runs.push((l, h)),
    };
    // Below the dark shadow, the dark shadow whole, above it.
    let segments = match dark {
        Some((l, h)) => [(rl, l - 1, false), (l, h, true), (h + 1, rh, false)],
        None => [(rl, rh, false), (1, 0, false), (1, 0, false)],
    };
    for (lo, hi, whole) in segments {
        if whole {
            add(lo, hi);
            continue;
        }
        let mut u = lo;
        while u <= hi {
            work.charge(PIECE.saturating_mul(h))?;
            match fiber(uw, u) {
                None => return Ok(None),
                Some(None) => {}
                Some(Some(_)) => add(u, u),
            }
            u += 1;
        }
    }
    Ok(Some(finite(runs)))
}

/// The polygon of `halves` as its edges ([`Polygon`]); `None` where it is not bounded, has no
/// interior, or a number passes `i128`, and then each name reads all the half-planes
/// ([`u_values`]).
// Complexity tradeoff: the half-plane intersection by sorting on the angle of the normal and
// a double-ended queue, O(h log h) once a part (the O(h log h) bound for half-plane
// intersection is Shamos and Hoey, "Geometric intersection problems", FOCS 1976), then a check
// of every half-plane at its least corner, O(h log V). Naive: every name's shadows over all h
// half-planes, O(h²) a name and O(k·h²) a part (`tests::names_over_a_polygon_of_many_sides_
// read_its_edges_once`, 190.77 times at 8 times k; `names_over_a_polygon_of_many_true_edges_
// cost_log_of_them`, 195.19); now O(log V) a step a name ([`poly_values`]). Exact: a
// half-plane dropped holds at every corner of the kept ones, so on their whole polygon, and
// the integer points are the same. Four sides of a box of half-width 2^60 are added so that the
// queue meets a closed region; where one of them is left among the edges the polygon may be
// open, and the old path answers (unbounded parts, `u_values`).
fn edges(halves: &[Form]) -> Option<Polygon> {
    const M: i128 = 1 << 60;
    let boxed = [(1, 0, M), (-1, 0, M), (0, 1, M), (0, -1, M)];
    let mut all: Vec<(Form, bool)> = halves.iter().map(|&f| (f, false)).collect();
    all.extend(boxed.iter().map(|&f| (f, true)));
    // The angle of the normal `(A, B)`: upper half first, then by the cross product.
    let upper = |f: &Form| f.1 > 0 || (f.1 == 0 && f.0 > 0);
    let cross = |f: &Form, g: &Form| f.0.checked_mul(g.1)?.checked_sub(f.1.checked_mul(g.0)?);
    let mut bad = false;
    all.sort_by(|(f, _), (g, _)| {
        upper(g).cmp(&upper(f)).then_with(|| match cross(f, g) {
            Some(c) => 0.cmp(&c),
            None => {
                bad = true;
                std::cmp::Ordering::Equal
            }
        })
    });
    if bad {
        return None;
    }
    // Of half-planes with the same normal direction, the tightest: `C/|n|` least.
    let mut kept: Vec<(Form, bool)> = Vec::with_capacity(all.len());
    for (f, b) in all {
        if let Some((g, gb)) = kept.last_mut()
            && upper(g) == upper(&f)
            && cross(g, &f)? == 0
        {
            // `f = λ·g` on the normal, `λ > 0`: `f` is tighter where `C_f < λ·C_g`.
            let (kf, kg) = if g.0 != 0 { (f.0, g.0) } else { (f.1, g.1) };
            let lhs = f.2.checked_mul(kg)?;
            let rhs = g.2.checked_mul(kf)?;
            if (kg > 0 && lhs < rhs) || (kg < 0 && lhs > rhs) {
                *g = f;
                *gb = b;
            }
            continue;
        }
        kept.push((f, b));
    }
    // The corner of two lines, `(p·d, q·d, d)` with `d > 0`; `None` where parallel.
    let corner = |f: &Form, g: &Form| -> Option<(i128, i128, i128)> {
        let det = cross(f, g)?;
        if det == 0 {
            return None;
        }
        let p = g.2.checked_mul(f.1)?.checked_sub(f.2.checked_mul(g.1)?)?;
        let q = f.2.checked_mul(g.0)?.checked_sub(g.2.checked_mul(f.0)?)?;
        Some(if det > 0 { (p, q, det) } else { (-p, -q, -det) })
    };
    // `A·p + B·q + C` at a corner, times its `d > 0`.
    let at = |f: &Form, c: (i128, i128, i128)| -> Option<i128> {
        f.0.checked_mul(c.0)?
            .checked_add(f.1.checked_mul(c.1)?)?
            .checked_add(f.2.checked_mul(c.2)?)
    };
    // The queue drops a neighbor whose corner is not strictly inside the new half-plane, so of
    // many lines through one corner only two stay; the check below, which counts the line
    // itself as inside, makes every drop exact whatever the queue did.
    let inside = |f: &Form, c: (i128, i128, i128)| -> Option<bool> { Some(at(f, c)? > 0) };
    let mut q: std::collections::VecDeque<(Form, bool)> = std::collections::VecDeque::new();
    for (f, b) in kept {
        while q.len() >= 2 && !inside(&f, corner(&q[q.len() - 1].0, &q[q.len() - 2].0)?)? {
            q.pop_back();
        }
        while q.len() >= 2 && !inside(&f, corner(&q[0].0, &q[1].0)?)? {
            q.pop_front();
        }
        q.push_back((f, b));
    }
    loop {
        let n = q.len();
        if n >= 3 && !inside(&q[0].0, corner(&q[n - 1].0, &q[n - 2].0)?)? {
            q.pop_back();
        } else if n >= 3 && !inside(&q[n - 1].0, corner(&q[0].0, &q[1].0)?)? {
            q.pop_front();
        } else {
            break;
        }
    }
    if q.len() < 3 || q.iter().any(|(_, b)| *b) {
        return None;
    }
    // The check: the kept normals turn by less than half a turn from each to the next, so the
    // kept half-planes cut a bounded convex polygon whose corners are those of neighbors; and
    // every half-plane of the part holds at the corner least along its normal (found by binary
    // search, [`Polygon::ends`]), so it holds on the whole polygon and the part's polygon is
    // that one. O(h log V) for the V kept.
    let mut rows: Vec<Form> = q.into_iter().map(|(f, _)| f).collect();
    let mut first = 0;
    for i in 1..rows.len() {
        if angle_cmp((rows[i].0, rows[i].1), (rows[first].0, rows[first].1))?.is_lt() {
            first = i;
        }
    }
    rows.rotate_left(first);
    let n = rows.len();
    let mut corners = Vec::with_capacity(n);
    for i in 0..n {
        let (f, g) = (&rows[i], &rows[(i + 1) % n]);
        if cross(f, g)? <= 0 {
            return None;
        }
        corners.push(corner(f, g)?);
    }
    let poly = Polygon { rows, corners };
    for f in halves {
        let [x, y] = poly.ends((f.0, f.1))?;
        if at(f, poly.corners[x])? < 0 || at(f, poly.corners[y])? < 0 {
            return None;
        }
    }
    Some(poly)
}

/// A bounded convex polygon with interior: the half-planes of its edges in the order of the
/// angles of their normals from 0, and `corners[j]`, the corner of edges `j` and `j + 1`
/// (cyclic), as `(p·d, q·d, d)` with `d > 0`.
struct Polygon {
    rows: Vec<Form>,
    corners: Vec<(i128, i128, i128)>,
}

/// The order of the angles of two directions, counterclockwise from the first axis; `None`
/// past `i128`.
fn angle_cmp(f: (i128, i128), g: (i128, i128)) -> Option<std::cmp::Ordering> {
    let upper = |v: (i128, i128)| v.1 > 0 || (v.1 == 0 && v.0 > 0);
    let cross = f.0.checked_mul(g.1)?.checked_sub(f.1.checked_mul(g.0)?)?;
    Some(upper(g).cmp(&upper(f)).then(0.cmp(&cross)))
}

/// The least `i` in `[lo, hi)` where `pred` fails, `pred` holding on a prefix (`hi` where it
/// never fails); `None` where `pred` is `None`.
fn first_false(
    mut lo: i128,
    mut hi: i128,
    mut pred: impl FnMut(i128) -> Option<bool>,
) -> Option<i128> {
    while lo < hi {
        let m = lo + (hi - lo) / 2;
        if pred(m)? {
            lo = m + 1;
        } else {
            hi = m;
        }
    }
    Some(lo)
}

impl Polygon {
    /// `(v·x - c)·d` at corner `j` (cyclic), `x = (p, q)`: its sign is that of `v·x - c`.
    fn off(&self, j: usize, v: (i128, i128), c: i128) -> Option<i128> {
        let (p, q, d) = self.corners[j % self.corners.len()];
        v.0.checked_mul(p)?
            .checked_add(v.1.checked_mul(q)?)?
            .checked_sub(c.checked_mul(d)?)
    }

    /// The number of edges whose normal's angle is below that of `v` (`or_equal`: not above).
    fn below(&self, v: (i128, i128), or_equal: bool) -> Option<usize> {
        let k = first_false(0, self.rows.len() as i128, |i| {
            let r = self.rows[i as usize];
            let o = angle_cmp((r.0, r.1), v)?;
            Some(o.is_lt() || (or_equal && o.is_eq()))
        })?;
        Some(k as usize)
    }

    /// The two chains of edges along `v·x`: the edges whose normals lie strictly between `v`
    /// and `-v` counterclockwise, and between `-v` and `v`; each `[j0, j1)`, indices cyclic.
    /// Along each chain `v·x` runs from one end of the polygon to the other, and at a value
    /// between the ends one edge of each chain bounds the polygon's line there. Each chain has
    /// an edge, the normals of a bounded polygon lying in no closed half-plane.
    fn chains(&self, v: (i128, i128)) -> Option<[(usize, usize); 2]> {
        let n = self.rows.len();
        let o = (v.0.checked_neg()?, v.1.checked_neg()?);
        let mut out = [(0, 0); 2];
        for (i, (from, to)) in [(v, o), (o, v)].into_iter().enumerate() {
            let j0 = self.below(from, true)?;
            let mut j1 = self.below(to, false)?;
            if j1 <= j0 {
                j1 += n;
            }
            if j1 - j0 >= n {
                return None;
            }
            out[i] = (j0, j1);
        }
        Some(out)
    }

    /// The corners where `v·x` is least and greatest, in either order: the two ends of a chain.
    fn ends(&self, v: (i128, i128)) -> Option<[usize; 2]> {
        let n = self.rows.len();
        let [(j0, j1), _] = self.chains(v)?;
        Some([(j0 + n - 1) % n, (j1 - 1) % n])
    }

    /// The integer values of `v·x` over the polygon, `[ceil(least), floor(greatest)]`.
    fn range(&self, v: (i128, i128)) -> Option<(i128, i128)> {
        let [x, y] = self.ends(v)?;
        let (mut lo, mut hi) = (i128::MAX, i128::MIN);
        for j in [x, y] {
            let (_, _, d) = self.corners[j];
            let num = self.off(j, v, 0)?;
            lo = lo.min(div_ceil(num, d)?);
            hi = hi.max(div_floor(num, d)?);
        }
        Some((lo, hi))
    }

    /// The edge of `chain` that bounds the line `v·x == c`, for `c` between the ends.
    fn across(&self, (j0, j1): (usize, usize), v: (i128, i128), c: i128) -> Option<Form> {
        let n = self.rows.len();
        // The corner where edge `j` starts; along the chain `v·x` there is monotone.
        let start = |j: usize| self.off(j + n - 1, v, c);
        // `c` lies between the chain's ends, so it rises where its start is below `c` or its
        // end above (at `c` equal to one end, the other end decides).
        let rising = start(j0)? < 0 || self.off(j1 - 1, v, c)? > 0;
        let k = first_false(j0 as i128, j1 as i128, |j| {
            let o = start(j as usize)?;
            Some(if rising { o <= 0 } else { o >= 0 })
        })?;
        Some(self.rows[(k as usize).saturating_sub(1).max(j0) % n])
    }
}

/// `|y_a - y_b|` for the bounds `y = -(E·c + C)/D` of two rows at `x == c`, as `(num, den)`.
fn gap(ra: Row, rb: Row, c: i128) -> Option<(i128, i128)> {
    let ya = ra.0.checked_mul(c)?.checked_add(ra.2)?;
    let yb = rb.0.checked_mul(c)?.checked_add(rb.2)?;
    let num = yb.checked_mul(ra.1)?.checked_sub(ya.checked_mul(rb.1)?)?;
    Some((num.checked_abs()?, ra.1.checked_mul(rb.1)?.checked_abs()?))
}

/// The stretch of `[rl, rh]` where `len` is at least 1, the length concave: its greatest
/// value by binary search on the sign of its step, then halving on either side. `Ok(None)`
/// past `i128`, `Ok(Some(None))` where nowhere.
type Len<'f> = dyn Fn(i128, &mut Work) -> Result<Option<(i128, i128)>, Refusal> + 'f;
type Long<'f> = dyn Fn(i128, &mut Work) -> Result<Option<bool>, Refusal> + 'f;
fn full_dark(
    rl: i128,
    rh: i128,
    len: &Len<'_>,
    long: &Long<'_>,
    work: &mut Work,
) -> Result<Option<Option<(i128, i128)>>, Refusal> {
    let mut peak = (rl, rh);
    while peak.0 < peak.1 {
        let m = peak.0 + (peak.1 - peak.0) / 2;
        let (Some(x), Some(y)) = (len(m, work)?, len(m + 1, work)?) else {
            return Ok(None);
        };
        let (Some(l), Some(r)) = (y.0.checked_mul(x.1), x.0.checked_mul(y.1)) else {
            return Ok(None);
        };
        if l > r {
            peak.0 = m + 1;
        } else {
            peak.1 = m;
        }
    }
    let top = peak.0;
    let Some(at_top) = long(top, work)? else {
        return Ok(None);
    };
    if !at_top {
        return Ok(Some(None));
    }
    // The first value of `[rl, top]` with length at least 1, and the last of `[top, rh]`.
    let (mut lo, mut hi) = (rl, top);
    while lo < hi {
        let m = lo + (hi - lo) / 2;
        let Some(ok) = long(m, work)? else {
            return Ok(None);
        };
        if ok { hi = m } else { lo = m + 1 }
    }
    let d1 = lo;
    let (mut lo, mut hi) = (top, rh);
    while lo < hi {
        let m = hi - (hi - lo) / 2;
        let Some(ok) = long(m, work)? else {
            return Ok(None);
        };
        if ok { lo = m } else { hi = m - 1 }
    }
    Ok(Some(Some((d1, lo))))
}

/// [`u_values`] over a [`Polygon`]: each end, each line's bounds and each gap found by binary
/// search over the edges, O(log V) each.
// Complexity tradeoff: naive, the shadows over all V edges, O(V²) a name (Fourier-Motzkin and
// Pugh's dark shadow, [`u_values`]); here the real shadow is the values at the two corners
// where `u` is least and greatest, and in place of Pugh's dark shadow the values where the
// line `u == c` meets the polygon in a stretch of `w` at least 1 long (each holds an integer
// `w`). That length is concave in `c` (the polygon is convex), so its greatest value is found
// by binary search on the sign of its step, and the two ends where it reaches 1 by binary
// search on either side: O(log(R)·log V) for the range R of `u`. The values outside are tried
// one by one as before, or each `w` of the polygon where that is fewer, O(log V) each. So a
// name costs O((log R + S)·log V) for S values tried, against O(V² + S·V) before.
fn poly_values(
    poly: &Polygon,
    (a, b): (i128, i128),
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    let Some((s, t)) = bezout(a, b) else {
        return Ok(None);
    };
    let n = poly.rows.len() as u64;
    let log = u64::from(u64::BITS - n.leading_zeros() + 1);
    let step = PIECE.saturating_mul(log);
    work.charge(step.saturating_mul(8))?;
    let to_uw = |(ha, hb, hc): Form| -> Option<Row> {
        let e = ha.checked_mul(s)?.checked_add(hb.checked_mul(t)?)?;
        let d = hb.checked_mul(a)?.checked_sub(ha.checked_mul(b)?)?;
        Some((e, d, hc))
    };
    let to_wu = |f: Form| -> Option<Row> {
        let (e, d, c) = to_uw(f)?;
        Some((d, e, c))
    };
    // `u = a·p + b·q` and `w = -t·p + s·q`.
    let (vu, vw) = ((a, b), (t.checked_neg(), s));
    let Some(vw) = vw.0.map(|x| (x, vw.1)) else {
        return Ok(None);
    };
    let (Some(cu), Some(cw), Some((rl, rh)), Some((wl, wh))) = (
        poly.chains(vu),
        poly.chains(vw),
        poly.range(vu),
        poly.range(vw),
    ) else {
        return Ok(None);
    };
    if rl > rh || wl > wh {
        return Ok(Some(Vec::new()));
    }
    // The two rows bounding `w` on the line `u == c`.
    let rows_at = |c: i128| -> Option<[Row; 2]> {
        Some([
            to_uw(poly.across(cu[0], vu, c)?)?,
            to_uw(poly.across(cu[1], vu, c)?)?,
        ])
    };
    let len = |c: i128, work: &mut Work| -> Result<Option<(i128, i128)>, Refusal> {
        work.charge(step)?;
        Ok(rows_at(c).and_then(|[x, y]| gap(x, y, c)))
    };
    let long = |c: i128, work: &mut Work| -> Result<Option<bool>, Refusal> {
        Ok(len(c, work)?.map(|(x, y)| x >= y))
    };
    // The end of the stretch where the length is at least 1 nearest `from`, sought toward `to`
    // by doubling steps and then halving between the last two (O(log d) for the distance d
    // to it); `Some(None)` where no step lands in it (the stretch is missed or empty). Where
    // a step `x` is long and the one before, `y`, is not, `y` lies outside the stretch on the
    // side of `from`, and between them the test is monotone.
    let gallop = |from: i128, to: i128, work: &mut Work| -> Result<Option<Option<i128>>, Refusal> {
        let dir: i128 = if to >= from { 1 } else { -1 };
        let mut out = from - dir;
        let mut size: i128 = 1;
        loop {
            let probe = from + dir * (size - 1);
            let probe = if dir > 0 {
                probe.min(to)
            } else {
                probe.max(to)
            };
            let Some(ok) = long(probe, work)? else {
                return Ok(None);
            };
            if ok {
                // The first long value after `out`, going from `from`.
                let (mut lo, mut hi) = (out + dir, probe);
                while lo != hi {
                    let m = lo + dir * ((hi - lo) * dir / 2);
                    let Some(ok) = long(m, work)? else {
                        return Ok(None);
                    };
                    if ok { hi = m } else { lo = m + dir }
                }
                return Ok(Some(Some(lo)));
            }
            if probe == to {
                return Ok(Some(None));
            }
            out = probe;
            let Some(next) = size.checked_mul(2) else {
                return Ok(None);
            };
            size = next;
        }
    };
    let quick = match gallop(rl, rh, work)? {
        None => return Ok(None),
        Some(Some(d1)) => match gallop(rh, d1, work)? {
            Some(Some(d2)) => Some(Some((d1, d2))),
            _ => return Ok(None),
        },
        Some(None) => None,
    };
    // The stretch of `c` where the length is at least 1, `None` where nowhere; where the steps
    // above missed it, by the greatest length (binary search on the sign of its step) and
    // halving on either side, O(log R) steps.
    let dark = match quick {
        Some(dark) => dark,
        None => match full_dark(rl, rh, &len, &long, work)? {
            Some(dark) => dark,
            None => return Ok(None),
        },
    };
    let dark_size = dark.map_or(0, |(l, h)| h - l + 1);
    let (Some(splinters), Some(width)) = (
        rh.checked_sub(rl)
            .and_then(|x| x.checked_add(1 - dark_size)),
        wh.checked_sub(wl).and_then(|x| x.checked_add(1)),
    ) else {
        return Ok(None);
    };
    let mut runs: Vec<(i128, i128)> = Vec::new();
    if width < splinters {
        // The narrower way: each integer `w` of the polygon gives one interval of `u`.
        for w in wl..=wh {
            work.charge(step)?;
            let rows = (|| {
                Some([
                    to_wu(poly.across(cw[0], vw, w)?)?,
                    to_wu(poly.across(cw[1], vw, w)?)?,
                ])
            })();
            let Some(rows) = rows else { return Ok(None) };
            match fiber(&rows, w) {
                None => return Ok(None),
                Some(None) => {}
                Some(Some((l, h))) => {
                    let (l, h) = (l.map_or(rl, |l| l.max(rl)), h.map_or(rh, |h| h.min(rh)));
                    if l <= h {
                        runs.push((l, h));
                    }
                }
            }
        }
        runs.sort_unstable();
        let mut merged: Vec<(i128, i128)> = Vec::with_capacity(runs.len());
        for (l, h) in runs {
            match merged.last_mut() {
                Some((_, e)) if *e >= l - 1 => *e = (*e).max(h),
                _ => merged.push((l, h)),
            }
        }
        return Ok(Some(finite(merged)));
    }
    let mut add = |l: i128, h: i128| match runs.last_mut() {
        Some((_, e)) if *e + 1 == l => *e = h,
        _ => runs.push((l, h)),
    };
    let segments = match dark {
        Some((l, h)) => [(rl, l - 1, false), (l, h, true), (h + 1, rh, false)],
        None => [(rl, rh, false), (1, 0, false), (1, 0, false)],
    };
    for (lo, hi, whole) in segments {
        if whole {
            add(lo, hi);
            continue;
        }
        for u in lo..=hi {
            work.charge(step)?;
            let Some(rows) = rows_at(u) else {
                return Ok(None);
            };
            match fiber(&rows, u) {
                None => return Ok(None),
                Some(None) => {}
                Some(Some(_)) => add(u, u),
            }
        }
    }
    Ok(Some(finite(runs)))
}

/// A run of values, `None` an open end.
type Run = (Option<i128>, Option<i128>);

/// Finite runs as [`Run`]s.
fn finite(runs: Vec<(i128, i128)>) -> Vec<Run> {
    runs.into_iter().map(|(l, h)| (Some(l), Some(h))).collect()
}

/// A row `x·X + y·Y + c >= 0` over two integer unknowns.
type Row = (i128, i128, i128);

/// Bounds on integer `X` from `p·X + q >= 0`, met into `(lo, hi)`; `Some(false)` where it never
/// holds, `None` past `i128`.
fn meet(p: i128, q: i128, lo: &mut Option<i128>, hi: &mut Option<i128>) -> Option<bool> {
    match p.signum() {
        0 => Some(q >= 0),
        1 => {
            let l = div_ceil(q.checked_neg()?, p)?;
            *lo = Some(lo.map_or(l, |v| v.max(l)));
            Some(true)
        }
        _ => {
            let h = div_floor(q, p.checked_neg()?)?;
            *hi = Some(hi.map_or(h, |v| v.min(h)));
            Some(true)
        }
    }
}

/// The bounds on `X` once `Y` is eliminated from `rows` (Fourier-Motzkin, each pair of a lower
/// and an upper bound on `Y`): the real shadow, or with `dark` Pugh's dark shadow, whose every
/// integer `X` has an integer `Y` ([module note](self)). `Some(None)` where empty, `None` past
/// `i128`. O(h²) for h rows.
fn shadow(rows: &[Row], dark: bool) -> Option<Option<(Option<i128>, Option<i128>)>> {
    let (mut lo, mut hi) = (None, None);
    let mut holds = true;
    for &(x, y, c) in rows {
        if y == 0 {
            holds &= meet(x, c, &mut lo, &mut hi)?;
        }
    }
    for &(xl, yl, cl) in rows.iter().filter(|r| r.1 > 0) {
        for &(xu, yu, cu) in rows.iter().filter(|r| r.1 < 0) {
            let p = yl.checked_mul(xu)?.checked_sub(yu.checked_mul(xl)?)?;
            let mut q = yl.checked_mul(cu)?.checked_sub(yu.checked_mul(cl)?)?;
            if dark {
                q = q.checked_sub((yl - 1).checked_mul(yu.checked_neg()? - 1)?)?;
            }
            holds &= meet(p, q, &mut lo, &mut hi)?;
        }
    }
    let empty = !holds || matches!((lo, hi), (Some(l), Some(h)) if l > h);
    Some((!empty).then_some((lo, hi)))
}

/// The integer `Y` of `rows` at `X == x`, as bounds; `Some(None)` where there is none, `None`
/// past `i128`. O(h).
fn fiber(rows: &[Row], x: i128) -> Option<Option<(Option<i128>, Option<i128>)>> {
    let (mut lo, mut hi) = (None, None);
    let mut holds = true;
    for &(xr, y, c) in rows {
        holds &= meet(y, xr.checked_mul(x)?.checked_add(c)?, &mut lo, &mut hi)?;
    }
    let empty = !holds || matches!((lo, hi), (Some(l), Some(h)) if l > h);
    Some((!empty).then_some((lo, hi)))
}
