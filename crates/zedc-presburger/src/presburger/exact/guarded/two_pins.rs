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
        Ok(Some(TwoPins {
            prep: self,
            forms,
            halves,
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
    // Complexity tradeoff: O(h²) for the h half-planes, the pairs of the shadows, plus O(h) for
    // each value of the real shadow outside the dark one, each charged; for the k names of a
    // part O(k·h²) in all, with no reading of the part a name. A part with many residuals (h of
    // the order of k) would still cost O(k·h²); sorting the half-planes into the polygon's edges
    // once a part and finding each shadow's ends by binary search over them would make it
    // O(h log h + k·log h) (PRES-groupA-two-pin-edges, open).
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
        let Some(us) = u_values(a, b, &self.halves, work)? else {
            return Ok(None);
        };
        if us.is_empty() {
            return Ok(None);
        }
        if g == 0 {
            return Ok(Some(Classed::plain(IntervalSet::point(Num::from(ga)))));
        }
        let mut pieces = Vec::with_capacity(us.len());
        for (lo, hi) in us {
            let at = |u: i128| Some(End::Fin(Num::from(g.checked_mul(u)?.checked_add(ga)?)));
            let (Some(lo), Some(hi)) = (at(lo), at(hi)) else {
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
/// sorted runs; `Ok(None)` where unbounded or past `i128` ([module note](self)).
fn u_values(
    a: i128,
    b: i128,
    halves: &[Form],
    work: &mut Work,
) -> Result<Option<Vec<(i128, i128)>>, Refusal> {
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
            match fiber(&wu, w) {
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
        return Ok(Some(merged));
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
            match fiber(&uw, u) {
                None => return Ok(None),
                Some(None) => {}
                Some(Some(_)) => add(u, u),
            }
            u += 1;
        }
    }
    Ok(Some(runs))
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
