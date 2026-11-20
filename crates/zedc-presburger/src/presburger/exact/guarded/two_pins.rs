//! The reading of a whole part with two pins (PRES-groupA-forward-per-name-order, part 2b): the
//! part is read once, every atom a form `α·p + β·q + γ` in two free atoms `p` and `q`, and each
//! name's projection is read off the integer points of the polygon its residuals cut out.
//!
//! The reading. From no atom known, a definition (an equation whose head has coefficient 1 or
//! -1, [`Def::Eq`]) is taken once its head is its only unknown atom (Kahn's order, as
//! [`Prep::read`]); where none can be taken and atoms are unknown, one becomes a pin: first an
//! atom that no definition may have as its head (it is free in every reading), else the least
//! unknown one. A third pin declines. A choice shared with other conjuncts splits the part into
//! cells, one arm and its guard in each, an arm whose guards cut out no real `p` pruned; a
//! choice read by nothing else (a leaf) is two queries over the region cut by its guard
//! ([`Prep::cell`], [`cut_values`]). Each head is an integer form in the pins, since its
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
//! test", 1991, and its CACM 1992 version, sec. 2.3.2, `b·α - a·β >= (a - 1)·(b - 1)`: where
//! the greatest lower and least upper bound are at least that far apart, an integer lies between
//! them; full citations in the crate root's References. The comment had "CACM, sec. 3", which
//! is the section on nonlinear subscripts). The values of the real shadow outside the dark
//! one are tried one by one, each with the integer bounds of `w` (the splinters, decided here
//! value by value rather than by Pugh's equalities). So the set is exact; where it is unbounded
//! and its values may be periodic (the stretch of `w` stays below 1 long toward an open end, as
//! on a flat ray), or a number passes `i128`, the reading declines and the per-name certificate
//! or the cover answers.
//!
//! Prior work in this crate: `row_sums::plane` projects the same polygons by the real shadow
//! where it is exact (a pair with a side of coefficient 1) and leaves forms with a common
//! factor to the join; here the dark shadow and the splinters make every pair exact, and a
//! common factor gives a class.

use std::collections::HashMap;

use zed_collections::search::{try_first_true, try_last_true};
use zed_kernel::bits::BitLen;
use zedc_int::int::{Int, Num, i128_div_ceil, i128_div_floor};
use zedc_lattice::interval::{End, IntervalSet};
use zedc_lattice::lattice::Congruence;

use super::super::super::meter::{PIECE, TWO_PIN_READINGS, Work};
use super::super::super::row_sums::plane::bezout;
use super::super::super::{Atom, Classed, Con, Formula, Lin, Refusal, Rel};
use super::super::projection::each_constraint;
use super::{Def, Prep};

/// `α·p + β·q + γ`.
type Form = (i128, i128, i128);

/// The part read with two pins ([module note](self)): each atom's form and the half-planes of
/// the residuals.
pub(in super::super) struct TwoPins<'p, 'a> {
    prep: &'p Prep<'a>,
    /// One for each arm taken at each shared choice ([`Prep::two_pins`]).
    cells: Vec<Cell>,
}

/// The part with one arm taken at each shared choice: each atom's form, the half-planes (the
/// residuals and the guards of the arms taken), and the choices read by nothing else.
struct Cell {
    forms: Vec<Form>,
    /// The region the half-planes cut out ([`shape_of`]).
    shape: Shape,
    /// The head of each leaf choice (read by no other conjunct): its guard's form and the
    /// head's form on each arm.
    leaves: HashMap<usize, (Form, [Form; 2])>,
}

/// The region of a cell's half-planes, as read ([`shape_of`]).
enum Shape {
    /// Bounded with interior: its edges.
    Bounded(Polygon),
    /// Unbounded with a corner: its edges up to a lid, and the two rays past it.
    Open(Box<Open>),
    /// Otherwise (flat, empty, a half-plane or a strip, or past `i128`): half-planes that cut
    /// it out, each name read from them all ([`u_values`]).
    Rows(Vec<Form>),
}

/// One reading of the part with some choices' arms fixed ([`Prep::cell`]).
enum Read {
    /// The part declines.
    Decline,
    /// A guard or residual with no pin is false, or both arms of a choice cut out no integer
    /// point: no point here.
    Empty,
    /// The shared choice of this conjunct is next, with both arms possible; the arms fixed so
    /// far, including those this reading took because the other arm had no point.
    Branch(usize, Vec<Option<usize>>),
    Done(Cell),
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
    //
    // Choices (PRES-two-pin-choices). A choice whose head no other conjunct reads (a leaf) is
    // taken with both arms: its head's values are those of the first arm over the polygon cut
    // by `guard >= 0` and of the second over the polygon cut by `guard <= -1`, two queries for
    // that name alone ([`TwoPins::values`]), and the polygon of the others is not split. A
    // shared choice (its head read by a residual or another definition) splits the part: each
    // arm is a cell, read again with that arm's equation and its guard as a half-plane, and a
    // name's set is the union over the cells, which partition the integer `(p, q)`. Cost: O(r·t)
    // a reading, at most `2·C - 1` readings for C cells (a binary tree, each inner node a
    // reading stopped at its choice), so O(C·(r·t + h log h)) a part and O(C·log h) a name:
    // with c shared choices fixed, linear in the names as before. Where c grows, C can be 2^c
    // (nested guards: the composed choices of Montúfar, Pascanu, Cho and Bengio, "On the number
    // of linear regions of deep neural networks", NIPS 2014, have exponentially many pieces);
    // no exact method here avoids reading each. Flat guards cut at most `1 + c + c(c-1)/2`
    // real cells (the line arrangement of Zaslavsky, "Facing up to arrangements", Mem. AMS
    // 154, 1975). An arm whose guards cut out no integer `p` is pruned where the choice is
    // met, before any reading of it (PRES-two-pin-prune, part b; [`Prep::cell`]), so C counts
    // the cells that test keeps: those of the arrangement with a point, and some with none
    // (it reads the guards alone, by their real shadow on `p`); before, every one of the 2^c
    // cells was read (`tests::empty_cells_are_pruned_before_they_are_read`: 7 readings for
    // 4 cells, 15 before). The per-name path the part declines to costs one reading a name, so
    // the cells pay only while C ≤ n, the n `names` asked: the part declines where they would
    // pass n, with no charge where the choices read by another definition alone already give
    // 2^c > n (as when any choice declined it, before), after one pass over the residuals,
    // O(r·t), where those they read do, and otherwise (a choice that splits the part only by
    // the head the reading gives it) after at most `2·n - 1` readings, no more than the
    // per-name path's n up to a factor 2. A chain of k choices (the
    // counter of `tests::guards_named`, read by the forward certificate) thus costs nothing here.
    pub(in super::super) fn two_pins<'p>(
        &'p self,
        names: usize,
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
        // Whether the choices whose every possible head is read by another conjunct (each
        // splits the part) give more than `names` cells: by `by_atom`, read by another
        // definition, and by `loose`, read by a conjunct that is no definition. A pass over
        // what `Prep` built and charged, so not charged again.
        let too_many = |loose: &[bool]| {
            let shared = defs
                .iter()
                .zip(reads)
                .filter(|(d, r)| match d {
                    Some(d @ Def::Choice { .. }) => r
                        .iter()
                        .all(|&x| !d.may_define(atoms[x]) || by_atom[x].len() > 1 || loose[x]),
                    _ => false,
                })
                .count();
            shared > 0 && (shared >= 64 || 1u64 << shared > names as u64)
        };
        let mut loose = vec![false; self.atoms.len()];
        if too_many(&loose) {
            return Ok(None);
        }
        if defs
            .iter()
            .flatten()
            .any(|d| matches!(d, Def::Choice { .. }))
        {
            for (g, d) in parts.iter().zip(defs) {
                if d.is_some() {
                    continue;
                }
                let mut read = 0u64;
                each_constraint(g, |c| {
                    read += 1;
                    for a in c.lin.terms.keys() {
                        loose[index[a]] = true;
                    }
                });
                work.charge(PIECE.saturating_mul(read))?;
            }
            if too_many(&loose) {
                return Ok(None);
            }
        }
        let mut cells = Vec::new();
        let mut stack: Vec<Vec<Option<usize>>> = vec![vec![None; defs.len()]];
        while let Some(fix) = stack.pop() {
            TWO_PIN_READINGS.set(TWO_PIN_READINGS.get() + 1);
            match self.cell(fix, &loose, work)? {
                Read::Decline => return Ok(None),
                Read::Empty => {}
                Read::Branch(i, fix) => {
                    // This cell becomes two: more than n cells cost more than the per-name path.
                    if cells.len() + stack.len() + 2 > names {
                        return Ok(None);
                    }
                    work.charge(PIECE.saturating_mul(fix.len() as u64))?;
                    for arm in [1, 0] {
                        let mut f = fix.clone();
                        f[i] = Some(arm);
                        stack.push(f);
                    }
                }
                Read::Done(cell) => cells.push(cell),
            }
        }
        Ok(Some(TwoPins { prep: self, cells }))
    }

    /// One reading of the part with the arm `fix[i]` taken at each choice `i` that has one
    /// ([`Prep::two_pins`]).
    fn cell(
        &self,
        mut fix: Vec<Option<usize>>,
        loose: &[bool],
        work: &mut Work,
    ) -> Result<Read, Refusal> {
        let Prep {
            parts,
            defs,
            atoms,
            index,
            by_atom,
            reads,
            ..
        } = self;
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
        // The guards of the arms taken, as half-planes.
        let mut guards: Vec<Form> = Vec::new();
        let mut leaves: HashMap<usize, (Form, [Form; 2])> = HashMap::new();
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
                // `c·x + rest == 0` with `c` 1 or -1: `x = -c·rest`.
                let head = |e: &Lin| -> Option<Form> {
                    let c = e.terms[atoms[x]].to_i128()?;
                    let mut out = (0, 0, e.constant.to_i128()?);
                    for (a, k) in &e.terms {
                        let j = index[a];
                        if j != x {
                            out = plus(out, times(k.to_i128()?, forms[j])?)?;
                        }
                    }
                    times(-c, out)
                };
                let f = match d {
                    Def::Eq(e) => head(e),
                    Def::Choice { guard, arms } => {
                        // The guard reads no `x` (`may_define`), so its atoms are known.
                        let Some(g) = form_of(guard, index, &forms) else {
                            return Ok(Read::Decline);
                        };
                        // `guard >= 0` on the first arm, `-guard - 1 >= 0` on the second.
                        let cut = |arm: usize| {
                            if arm == 0 {
                                Some(g)
                            } else {
                                times(-1, g).and_then(|n| plus(n, (0, 0, -1)))
                            }
                        };
                        let arm = match fix[i] {
                            Some(arm) => Some(arm),
                            None if by_atom[x].len() == 1 && !loose[x] => None,
                            None => {
                                // A shared choice with no arm fixed (PRES-two-pin-prune, part
                                // b): an arm whose guard and the guards taken so far cut out no
                                // integer point is pruned before any cell reads it. Where one
                                // arm is pruned this reading takes the other and goes on, so
                                // every reading that stops here has two arms with points and
                                // the readings are at most `2·C - 1` for the C cells with a
                                // point. The test is the real shadow on `p` (Fourier-Motzkin,
                                // [`shadow`]), empty only where no real point has an integer
                                // `p`: sound, not complete (a cell it keeps may still have no
                                // integer point, and is read). O(g²) for g guards, once a
                                // reading; the residuals are not in it, so the cost does not
                                // grow with the part.
                                let mut empty = [false; 2];
                                for (arm, e) in empty.iter_mut().enumerate() {
                                    let Some(c) = cut(arm) else {
                                        return Ok(Read::Decline);
                                    };
                                    let rows: Vec<Row> =
                                        guards.iter().copied().chain([c]).collect();
                                    let r = rows.len() as u64;
                                    work.charge(PIECE.saturating_mul(r.saturating_mul(r)))?;
                                    *e = shadow(&rows, false) == Some(None);
                                }
                                match empty {
                                    [true, true] => return Ok(Read::Empty),
                                    [true, false] => Some(1),
                                    [false, true] => Some(0),
                                    [false, false] => return Ok(Read::Branch(i, fix)),
                                }
                            }
                        };
                        match arm {
                            Some(arm) => {
                                let Some(c) = cut(arm) else {
                                    return Ok(Read::Decline);
                                };
                                fix[i] = Some(arm);
                                guards.push(c);
                                head(arms[arm])
                            }
                            None => {
                                let (Some(f0), Some(f1)) = (head(arms[0]), head(arms[1])) else {
                                    return Ok(Read::Decline);
                                };
                                leaves.insert(x, (g, [f0, f1]));
                                // Read by no other conjunct: this form is never used.
                                Some(f0)
                            }
                        }
                    }
                };
                let Some(f) = f else {
                    return Ok(Read::Decline);
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
                return Ok(Read::Decline);
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
        // The residuals and the guards taken as half-planes over the pins.
        let mut halves = Vec::new();
        // No pin: true, or this cell has no point (where every cell has none, each name
        // declines and the cover answers).
        let mut add = |f: Form| -> bool {
            if f.0 == 0 && f.1 == 0 {
                return f.2 >= 0;
            }
            halves.push(f);
            true
        };
        for g in guards {
            if !add(g) {
                return Ok(Read::Empty);
            }
        }
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
                    _ => return Ok(Read::Decline),
                },
                _ => return Ok(Read::Decline),
            };
            let Some(f) = form_of(&lin, index, &forms) else {
                return Ok(Read::Decline);
            };
            if !add(f) {
                return Ok(Read::Empty);
            }
            if both {
                let Some(n) = times(-1, f) else {
                    return Ok(Read::Decline);
                };
                if !add(n) {
                    return Ok(Read::Empty);
                }
            }
        }
        // The cuts of the leaf choices' arms, so that an open region's lid is placed past where
        // they cross its rays ([`open`]).
        let mut cuts = Vec::with_capacity(2 * leaves.len());
        for &(g, _) in leaves.values() {
            cuts.push(g);
            if let Some(n) = times(-1, g).and_then(|n| plus(n, (0, 0, -1))) {
                cuts.push(n);
            }
        }
        let h = (halves.len() + cuts.len()) as u64;
        work.charge(PIECE.saturating_mul(h.saturating_mul(u64::from(h.bit_len() + 1))))?;
        let shape = shape_of(&halves, &cuts);
        Ok(Read::Done(Cell {
            forms,
            shape,
            leaves,
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
    // and S do not grow. An open region with a corner is the same, its edges cut by a lid
    // ([`open`], [`open_values`]; PRES-two-pin-prune, part a). Otherwise (a half-plane or a
    // strip, read from its one or two edges; flat, or past `i128`, from all h) O(h²) a name
    // for the pairs of the shadows plus O(h) a value tried ([`u_values`]). With choices, that
    // for each cell, and for a leaf choice's head two queries a cell, each over the region cut
    // by its guard, read in place in O(log V) ([`cut_values`]); the per-name path it replaces
    // reads the whole part, O(r·t) ≥ O(V).
    pub(in super::super) fn values(
        &self,
        s: &Atom,
        work: &mut Work,
    ) -> Result<Option<Classed>, Refusal> {
        let Some(&j) = self.prep.index.get(s) else {
            return Ok(None);
        };
        // `(g, γ, runs of u)` for each query with a point: the values `γ + g·u`.
        let mut found: Vec<(i128, i128, Vec<Run>)> = Vec::new();
        for cell in &self.cells {
            let queries = match cell.leaves.get(&j) {
                None => vec![(cell.forms[j], None)],
                Some(&(guard, [f0, f1])) => {
                    let Some(other) = times(-1, guard).and_then(|n| plus(n, (0, 0, -1))) else {
                        return Ok(None);
                    };
                    vec![(f0, Some(guard)), (f1, Some(other))]
                }
            };
            for (f, cut) in queries {
                let Some((g, us)) = form_values(f, cell, cut, work)? else {
                    return Ok(None);
                };
                if !us.is_empty() {
                    found.push((g, f.2, us));
                }
            }
        }
        // The union is one class only where every query with a step has the same step `m`
        // and every query the same residue modulo `m`; otherwise the per-name path answers.
        let Some(m) = found.iter().map(|q| q.0).max() else {
            return Ok(None);
        };
        if found.iter().any(|q| q.0 > 0 && q.0 != m)
            || (m > 1 && found.iter().any(|q| (q.1 - found[0].1).rem_euclid(m) != 0))
        {
            return Ok(None);
        }
        let residue = found[0].1.rem_euclid(m.max(1));
        let mut pieces = Vec::new();
        for (g, ga, us) in found {
            if g == 0 {
                // A name fixed in this query: its one value.
                pieces.push((End::Fin(Num::from(ga)), End::Fin(Num::from(ga))));
                continue;
            }
            // A class other than every integer takes finite ranges (`Classed::new`); an open
            // end there declines to the per-name path.
            if g > 1 && us.iter().any(|(lo, hi)| lo.is_none() || hi.is_none()) {
                return Ok(None);
            }
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
        }
        let ranges = IntervalSet::from_pieces(pieces);
        Ok(Some(if m <= 1 {
            Classed::plain(ranges)
        } else {
            Classed::new(ranges, Congruence::new(Num::from(m), Num::from(residue)))
        }))
    }
}

/// The values of the form `f` over the integer points of `cell`, cut by `cut` where given: its
/// step `g` (`gcd(α, β)`, 0 for a form with no pin) and the runs of `u` with `f = γ + g·u`;
/// `None` where it declines ([module note](self)).
fn form_values(
    f: Form,
    cell: &Cell,
    cut: Option<Form>,
    work: &mut Work,
) -> Result<Option<(i128, Vec<Run>)>, Refusal> {
    let (al, be, _) = f;
    let (g, a, b) = if al == 0 && be == 0 {
        (0, 1, 0)
    } else {
        let g = Int::from(al).gcd(&Int::from(be)).to_i128();
        let Some(g) = g.filter(|g| *g > 0) else {
            return Ok(None);
        };
        (g, al / g, be / g)
    };
    let cut = match cut {
        // A guard with no pin: true on the whole cell, or false on it.
        Some(c) if c.0 == 0 && c.1 == 0 => {
            if c.2 < 0 {
                return Ok(Some((g, Vec::new())));
            }
            None
        }
        c => c,
    };
    let us = match cut {
        None => shape_values(&cell.shape, (a, b), work)?,
        Some(c) => cut_values(&cell.shape, c, (a, b), work)?,
    };
    Ok(us.map(|us| (g, us)))
}

/// The runs of `u = a·p + b·q` over the integer points of `shape`.
fn shape_values(
    shape: &Shape,
    (a, b): (i128, i128),
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    match shape {
        Shape::Bounded(poly) => poly_values(poly, (a, b), work),
        Shape::Open(o) => open_values(&o.k, &o.rays, (a, b), work),
        Shape::Rows(halves) => u_values(a, b, halves, work),
    }
}

/// `2·(⌊log2 n⌋ + 2)` pieces, for one search over n edges.
fn log_pieces(n: usize) -> u64 {
    let n = n as u64;
    PIECE.saturating_mul(2 * u64::from(n.bit_len() + 1))
}

/// The runs of `u = a·p + b·q` over the integer points of `shape` where `c >= 0` (the arm of a
/// leaf choice, [`TwoPins::values`]).
// Complexity tradeoff: naive, the region's edges again with `c` among them, O(V log V) a
// query ([`shape_of`]), so O(k·V log V) for k leaf choices over one region of V edges
// (`tests::leaf_choices_over_a_polygon_of_many_true_edges_cost_log_of_them`: 67.38 times the
// work at 8 times k before). Here the cut region is read in place, O(log V) ([`clip`]): the
// line `c == 0` meets a convex polygon in at most two edges, each found by binary search
// from the corner where `c` is greatest (Chazelle and Dobkin, "Intersection of convex
// objects in two and three dimensions", JACM 34(1), 1987, Theorem 3: the intersection of a
// line and a convex p-gon in O(log p)). An open region is cut in place where `c` holds on
// both its rays past the lid, so the cut region is again open with the same rays; or fails
// past the lid, so the cut region lies within it ([`open`], [`fails_past_lid`]); or holds on
// one ray and fails on the other (parallel to either allowed), so the cut region's rays are
// the one kept and `c`'s line from where it crosses the lid ([`split`],
// PRES-two-pin-split-rays: `tests::leaf_choices_whose_guards_split_the_rays_cost_log_of_them`,
// 72.19 times the work at 8 times k with the edges found again, 9.58 now). The edges are
// found again, O(V log V), only where none of those applies (`c == 0` through an end of the
// lid, a cut region with no interior, or past `i128`).
fn cut_values(
    shape: &Shape,
    c: Form,
    (a, b): (i128, i128),
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    let rebuild = |work: &mut Work| -> Result<Option<Vec<Run>>, Refusal> {
        let mut halves: Vec<Form> = match shape {
            Shape::Bounded(p) => (0..p.n()).map(|i| p.row(i)).collect(),
            Shape::Open(o) => (0..o.k.n())
                .map(|i| o.k.row(i))
                .filter(|&f| f != o.rays.lid)
                .collect(),
            Shape::Rows(h) => h.clone(),
        };
        halves.push(c);
        let h = halves.len() as u64;
        work.charge(PIECE.saturating_mul(h.saturating_mul(u64::from(h.bit_len() + 1))))?;
        shape_values(&shape_of(&halves, &[]), (a, b), work)
    };
    match shape {
        Shape::Bounded(p) => {
            work.charge(log_pieces(p.n()))?;
            match clip(p, c) {
                Some(cut) => cut_poly_values(p, cut, (a, b), work),
                None => rebuild(work),
            }
        }
        Shape::Open(o) => {
            work.charge(log_pieces(o.k.n()))?;
            let r = &o.rays;
            let n = (c.0, c.1);
            let signs = (|| Some([dot(n, r.ds)?, dot(n, r.de)?, at(&c, r.l0)?, at(&c, r.l1)?]))();
            let Some(signs) = signs else {
                return rebuild(work);
            };
            match clip(&o.k, c) {
                // `c` holds on both rays from the ends of the lid, so on all past the lid: the
                // cut region is the polygon cut with the same rays past the lid, which `c`
                // keeps (it holds at both its ends).
                Some(cut) if signs.iter().all(|&x| x >= 0) => match cut {
                    Cut::Whole => open_values(&o.k, r, (a, b), work),
                    Cut::Part(k) => open_values(&k, r, (a, b), work),
                    Cut::Empty | Cut::Face(_) => rebuild(work),
                },
                // `c` is at most 0 on the lid and does not rise along either ray, falling along
                // each or below 0 on the whole lid: past the lid it is below 0 except on the
                // lid itself, so the cut region is the polygon's, cut.
                Some(cut) if fails_past_lid(signs) => cut_poly_values(&o.k, cut, (a, b), work),
                // `c` holds on one ray and fails on the other: the polygon cut, with rays the
                // one kept and `c`'s line from where it crosses the lid ([`split`]).
                Some(Cut::Part(k)) => match split(r, c, signs) {
                    Some(rays) => open_values(&k, &rays, (a, b), work),
                    None => rebuild(work),
                },
                _ => rebuild(work),
            }
        }
        Shape::Rows(_) => rebuild(work),
    }
}

/// Whether `c` is below 0 everywhere past the lid of an open region, from
/// `[c·ds, c·de, c(l0), c(l1)]` ([`cut_values`]): a point there is `l + α·ds + β·de` for `l` on
/// the lid and `α, β >= 0` not both 0, where `c` is `c(l) + α·(c·ds) + β·(c·de)`, `c(l)` at most
/// 0 between the ends; it is below 0 where each ray's term is below 0 or `c(l)` is.
fn fails_past_lid([s0, s1, c0, c1]: [i128; 4]) -> bool {
    let lid_below = c0 < 0 && c1 < 0;
    c0 <= 0 && c1 <= 0 && (s0 < 0 || (s0 == 0 && lid_below)) && (s1 < 0 || (s1 == 0 && lid_below))
}

/// The rays past the lid of the open region `r` cut by `c >= 0` where `c` holds on one ray and
/// fails on the other, from `[c·ds, c·de, c(l0), c(l1)]` ([`cut_values`]); `None` otherwise or
/// past `i128`.
// Exact: say `c` holds along `ra` (`c·ds >= 0`, `c(l0) > 0`) and fails along `rb` (`c·de <= 0`,
// `c(l1) < 0`; parallel to either ray is allowed). Past the lid the region is
// `conv(l0, l1) + cone(ds, de)` ([`Rays`]); its part where `c >= 0` is convex, with the corners
// `l0` and `z`, where `c == 0` crosses the lid (`c` is above 0 at `l0` and below at `l1`), and
// the directions `cone(ds, de)` where `c` does not fall, which is `cone(ds, de')` for `de'` the
// direction of `c`'s line within `cone(ds, de)`. That is `{ra >= 0, c >= 0, lid <= 0}`: the rays
// `ra` and `c`, `ds` and `de'`, the lid's ends `l0` and `z`, so long as the lid falls along
// both directions and the corner of `ra` and `c` lies before it ([`open`] places the lid past
// where each leaf choice's cut crosses the lines of `ra` and `rb`, so it does), or `ra` and `c`
// are parallel with opposite normals, a half-strip. Each of those is checked here, with `de'`
// in `cone(ds, de)` (`ra·de' >= 0`, `rb·de' >= 0`), so a failed check declines to the edges
// found again, never a wrong answer. Within the lid the cut region is the polygon cut by `c`,
// whose lid edge runs from `l0` to `z`. The other way round, `rb` is kept and `c` takes the
// place of `ra`. O(1).
fn split(r: &Rays, c: Form, [s0, s1, c0, c1]: [i128; 4]) -> Option<Rays> {
    let rays = if s0 >= 0 && c0 > 0 && s1 <= 0 && c1 < 0 {
        Rays {
            rb: c,
            de: (c.1, c.0.checked_neg()?),
            l1: point(&r.lid, &c)?,
            ..*r
        }
    } else if s1 >= 0 && c1 > 0 && s0 <= 0 && c0 < 0 {
        Rays {
            ra: c,
            ds: (c.1.checked_neg()?, c.0),
            l0: point(&c, &r.lid)?,
            ..*r
        }
    } else {
        return None;
    };
    let cr = cross(&rays.ra, &rays.rb)?;
    let corner = if cr > 0 {
        at(&rays.lid, point(&rays.ra, &rays.rb)?)? > 0
    } else {
        cr == 0 && dot((rays.ra.0, rays.ra.1), (rays.rb.0, rays.rb.1))? < 0
    };
    let lid = (rays.lid.0, rays.lid.1);
    let within = |d: (i128, i128)| -> Option<bool> {
        Some(dot((r.ra.0, r.ra.1), d)? >= 0 && dot((r.rb.0, r.rb.1), d)? >= 0)
    };
    let ok = corner
        && dot(lid, rays.ds)? < 0
        && dot(lid, rays.de)? < 0
        && within(rays.ds)?
        && within(rays.de)?;
    ok.then_some(rays)
}

/// [`poly_values`] over the polygon `p` cut as `cut`.
fn cut_poly_values<P: Convex>(
    p: &P,
    cut: Cut<'_, P>,
    (a, b): (i128, i128),
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    match cut {
        Cut::Empty => Ok(Some(Vec::new())),
        Cut::Whole => poly_values(p, (a, b), work),
        Cut::Face(rows) => u_values(a, b, &rows, work),
        Cut::Part(k) => poly_values(&k, (a, b), work),
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
        return Ok(Some(finite(merge_runs(runs))));
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
/// interior, or a number passes `i128` ([`shape_of`] then tries an open region).
// Complexity tradeoff: the half-plane intersection by sorting on the angle of the normal and
// a double-ended queue, O(h log h) once a part (the O(h log h) bound for half-plane
// intersection is Shamos and Hoey, "Geometric intersection problems", FOCS 1976), then a check
// of every half-plane at its least corner, O(h log V). Naive: every name's shadows over all h
// half-planes, O(h²) a name and O(k·h²) a part (`tests::names_over_a_polygon_of_many_sides_
// read_its_edges_once`, 190.77 times at 8 times k; `names_over_a_polygon_of_many_true_edges_
// cost_log_of_them`, 195.19); now O(log V) a step a name ([`poly_values`]). Exact: a
// half-plane dropped holds at every corner of the kept ones, so on their whole polygon, and
// the integer points are the same. Four sides of a box of half-width 2^60 are added so that the
// queue meets a closed region; where one of them is left among the edges the region may be
// open, and [`open`] reads it.
fn edges(halves: &[Form]) -> Option<Polygon> {
    let q = hull(halves)?;
    if q.len() < 3 || q.iter().any(|(_, b)| *b) {
        return None;
    }
    bounded(halves, q.into_iter().map(|(f, _)| f).collect())
}

/// The region of `halves` ([`Shape`]): bounded ([`edges`]), open with a corner ([`open`], its
/// lid past where each of `cuts` crosses its rays), else the half-planes themselves.
fn shape_of(halves: &[Form], cuts: &[Form]) -> Shape {
    hull(halves)
        .and_then(|q| {
            if q.len() >= 3 && !q.iter().any(|(_, b)| *b) {
                bounded(halves, q.into_iter().map(|(f, _)| f).collect()).map(Shape::Bounded)
            } else {
                open(halves, &q, cuts)
            }
        })
        .unwrap_or_else(|| Shape::Rows(halves.to_vec()))
}

/// `f × g` of two normals; `None` past `i128`.
fn cross(f: &Form, g: &Form) -> Option<i128> {
    f.0.checked_mul(g.1)?.checked_sub(f.1.checked_mul(g.0)?)
}

/// `n · d`; `None` past `i128`.
fn dot(n: (i128, i128), d: (i128, i128)) -> Option<i128> {
    n.0.checked_mul(d.0)?.checked_add(n.1.checked_mul(d.1)?)
}

/// A point `(p·d, q·d, d)` with `d > 0`.
type Pt = (i128, i128, i128);

/// The point where the lines of two half-planes meet; `None` where parallel or past `i128`.
fn point(f: &Form, g: &Form) -> Option<Pt> {
    let det = cross(f, g)?;
    if det == 0 {
        return None;
    }
    let p = g.2.checked_mul(f.1)?.checked_sub(f.2.checked_mul(g.1)?)?;
    let q = f.2.checked_mul(g.0)?.checked_sub(g.2.checked_mul(f.0)?)?;
    Some(if det > 0 { (p, q, det) } else { (-p, -q, -det) })
}

/// `A·p + B·q + C` at a point, times its `d > 0`.
fn at(f: &Form, c: Pt) -> Option<i128> {
    f.0.checked_mul(c.0)?
        .checked_add(f.1.checked_mul(c.1)?)?
        .checked_add(f.2.checked_mul(c.2)?)
}

/// The half-planes of `halves` left by the double-ended queue inside a box of half-width
/// 2^60, in the cyclic order of the angles of their normals, each marked where it is a side
/// of the box ([`edges`]); `None` past `i128`.
fn hull(halves: &[Form]) -> Option<Vec<(Form, bool)>> {
    const M: i128 = 1 << 60;
    let boxed = [(1, 0, M), (-1, 0, M), (0, 1, M), (0, -1, M)];
    let mut all: Vec<(Form, bool)> = halves.iter().map(|&f| (f, false)).collect();
    all.extend(boxed.iter().map(|&f| (f, true)));
    // The angle of the normal `(A, B)`: upper half first, then by the cross product.
    let upper = |f: &Form| f.1 > 0 || (f.1 == 0 && f.0 > 0);
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
    let corner = point;
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
    Some(q.into_iter().collect())
}

/// The bounded polygon of the rows `rows` left by [`hull`], checked against all of `halves`.
fn bounded(halves: &[Form], mut rows: Vec<Form>) -> Option<Polygon> {
    // The check: the kept normals turn by less than half a turn from each to the next, so the
    // kept half-planes cut a bounded convex polygon whose corners are those of neighbors; and
    // every half-plane of the part holds at the corner least along its normal (found by binary
    // search, [`Polygon::ends`]), so it holds on the whole polygon and the part's polygon is
    // that one. O(h log V) for the V kept.
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
        corners.push(point(f, g)?);
    }
    let poly = Polygon { rows, corners };
    for f in halves {
        let [x, y] = poly.ends((f.0, f.1))?;
        if at(f, poly.corner(x))? < 0 || at(f, poly.corner(y))? < 0 {
            return None;
        }
    }
    Some(poly)
}

/// An unbounded region with a corner, cut at a lid: the bounded polygon `k` of its edges and
/// the lid, and past the lid what lies between two rays ([`open`]).
struct Open {
    k: Polygon,
    rays: Rays,
}

/// Past the lid of an [`Open`] region: `W ∩ {lid <= 0}` for `W = {ra >= 0, rb >= 0}`, the
/// points `conv(l0, l1) + cone(ds, de)`, where `ra`, `rb` are the edges of least and greatest
/// angle, `ds`, `de` the directions of their unbounded sides, and `l0`, `l1` the ends of the
/// lid on them.
#[derive(Clone, Copy)]
struct Rays {
    lid: Form,
    ra: Form,
    rb: Form,
    ds: (i128, i128),
    de: (i128, i128),
    l0: Pt,
    l1: Pt,
}

/// The region of `halves` where [`hull`] left a side of the box among `q`: a half-plane or a
/// strip as its one or two half-planes, else an [`Open`] region; `None` where none fits (flat,
/// empty, no corner but not one of those, or past `i128`).
// Complexity tradeoff (PRES-two-pin-prune, part a): naive, an unbounded region's names read
// all h half-planes by their shadows, O(h²) a name and O(k·h²) a part (`tests::names_over_an_
// open_polygon_of_many_true_edges_cost_log_of_them`: 205.66 times the work at 8 times k
// before). Here the m edges left by the queue are cut by a lid, a half-plane whose normal
// points between the two unbounded sides, placed past every corner of the edges and past
// where each leaf choice's cut crosses the two rays: the lid and the edges are a bounded
// polygon, found once in O(m log m) ([`edges`]), and each name reads it in O(log V) a step
// ([`open_values`]). Exact: the m edges are the region R of `halves` within the box, so R lies
// in `W = {ra >= 0, rb >= 0}`; every half-plane is checked to hold on the polygon (at its two
// extreme corners), at both ends of the lid, and along both rays (`h·ds >= 0`, `h·de >= 0`),
// so it holds on the polygon and on `conv(l0, l1) + cone(ds, de)`, which is `W` past the lid
// (the lid meets both rays, past the corner of `ra` and `rb` where they meet); so the region
// of `halves` is the polygon and that, and no point is lost to the box. O(h log m) for the
// check, so O(h log h) once a part as before.
fn open(halves: &[Form], q: &[(Form, bool)], cuts: &[Form]) -> Option<Shape> {
    let n = q.len();
    // The edges that are not sides of the box, one run in the cyclic order.
    let starts: Vec<usize> = (0..n)
        .filter(|&i| !q[i].1 && q[(i + n - 1) % n].1)
        .collect();
    let [i0] = starts[..] else {
        return None;
    };
    let r: Vec<Form> = (0..n)
        .map(|i| q[(i0 + i) % n])
        .take_while(|x| !x.1)
        .map(|x| x.0)
        .collect();
    let m = r.len();
    let (ra, rb) = (r[0], r[m - 1]);
    // A point on the line of `f`: `-C·(A, B) / (A² + B²)`.
    let on = |f: &Form| -> Option<Pt> {
        let c = f.2.checked_neg()?;
        Some((
            c.checked_mul(f.0)?,
            c.checked_mul(f.1)?,
            dot((f.0, f.1), (f.0, f.1))?,
        ))
    };
    if m == 1 {
        // A half-plane: every half-plane has its normal's direction and holds on its line.
        let p0 = on(&ra)?;
        for h in halves {
            if cross(h, &ra)? != 0 || dot((h.0, h.1), (ra.0, ra.1))? <= 0 || at(h, p0)? < 0 {
                return None;
            }
        }
        return Some(Shape::Rows(vec![ra]));
    }
    for w in r.windows(2) {
        if cross(&w[0], &w[1])? <= 0 {
            return None;
        }
    }
    let cr = cross(&ra, &rb)?;
    if cr < 0 || (cr == 0 && dot((ra.0, ra.1), (rb.0, rb.1))? >= 0) {
        return None;
    }
    if cr == 0 && m == 2 {
        // A strip: every half-plane is parallel to it and holds on both its lines.
        let (p0, p1) = (on(&ra)?, on(&rb)?);
        for h in halves {
            if cross(h, &ra)? != 0 || at(h, p0)? < 0 || at(h, p1)? < 0 {
                return None;
            }
        }
        return Some(Shape::Rows(vec![ra, rb]));
    }
    // Along `ra` toward where `rb` holds, and along `rb` toward where `ra` holds:
    // `rb·ds = ra·de = cr` where `cr > 0`.
    let ds = (ra.1.checked_neg()?, ra.0);
    let de = (rb.1, rb.0.checked_neg()?);
    // The lid's normal falls along both rays: `-(n_a + n_b)·ds = -cr`; for a half-strip
    // (`cr == 0`, the normals opposite) `-ds`.
    let ell = if cr > 0 {
        (
            ra.0.checked_add(rb.0)?.checked_neg()?,
            ra.1.checked_add(rb.1)?.checked_neg()?,
        )
    } else {
        (ds.0.checked_neg()?, ds.1.checked_neg()?)
    };
    // The lid `ell·x + c >= 0` with `c` the least integer that leaves it at least 1 at every
    // corner of the edges and where each cut crosses the lines of `ra` and `rb`.
    let mut pts: Vec<Pt> = Vec::with_capacity(m + 2 * cuts.len());
    for w in r.windows(2) {
        pts.push(point(&w[0], &w[1])?);
    }
    for c in cuts {
        pts.extend([point(&ra, c), point(c, &rb)].into_iter().flatten());
    }
    let mut cl = i128::MIN;
    for (x, y, d) in pts {
        cl = cl.max(1i128.checked_sub(i128_div_floor(dot(ell, (x, y))?, d)?)?);
    }
    let lid = (ell.0, ell.1, cl);
    if cr > 0 && at(&lid, point(&ra, &rb)?)? <= 0 {
        return None;
    }
    let mut rows = r.clone();
    rows.push(lid);
    let k = edges(&rows)?;
    if !(0..k.n()).any(|i| k.row(i) == lid) {
        return None;
    }
    let (l0, l1) = (point(&ra, &lid)?, point(&lid, &rb)?);
    for h in halves {
        let [x, y] = k.ends((h.0, h.1))?;
        let n = (h.0, h.1);
        if at(h, k.corner(x))? < 0
            || at(h, k.corner(y))? < 0
            || dot(n, ds)? < 0
            || dot(n, de)? < 0
            || at(h, l0)? < 0
            || at(h, l1)? < 0
        {
            return None;
        }
    }
    Some(Shape::Open(Box::new(Open {
        k,
        rays: Rays {
            lid,
            ra,
            rb,
            ds,
            de,
            l0,
            l1,
        },
    })))
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
/// never fails); `None` where `pred` is `None`: the shared search, `try_first_true`, on the
/// predicate negated.
fn first_false(lo: i128, hi: i128, mut pred: impl FnMut(i128) -> Option<bool>) -> Option<i128> {
    try_first_true(lo, hi, |&i| pred(i).map(|b| !b).ok_or(())).ok()
}

/// A question of [`full_dark`]'s searches as the shared search takes it: `Err(None)` past
/// `i128`, `Err(Some(_))` a refusal.
fn asked(r: Result<Option<bool>, Refusal>) -> Result<bool, Option<Refusal>> {
    match r {
        Ok(Some(b)) => Ok(b),
        Ok(None) => Err(None),
        Err(e) => Err(Some(e)),
    }
}

/// The answer of one of [`full_dark`]'s searches back in its own form: `Ok(None)` past `i128`.
fn found<T>(r: Result<T, Option<Refusal>>) -> Result<Option<T>, Refusal> {
    match r {
        Ok(t) => Ok(Some(t)),
        Err(None) => Ok(None),
        Err(Some(e)) => Err(e),
    }
}

/// A bounded convex polygon with interior and no three corners on a line, read edge by edge:
/// `row(i)` for `i < n()`, the half-planes of its edges in the order of the angles of their
/// normals from 0, and `corner(j)`, the corner of edges `j` and `j + 1` (cyclic), as
/// `(p·d, q·d, d)` with `d > 0`. [`Polygon`] holds them; a [`Clip`] reads them from the polygon
/// it cuts, so a cut costs no copy.
trait Convex {
    fn n(&self) -> usize;
    /// Edge `i`, `i < n()`.
    fn row(&self, i: usize) -> Form;
    /// Corner `j`, `j < n()`.
    fn corner(&self, j: usize) -> Pt;

    /// `(v·x - c)·d` at corner `j` (cyclic), `x = (p, q)`: its sign is that of `v·x - c`.
    fn off(&self, j: usize, v: (i128, i128), c: i128) -> Option<i128> {
        let (p, q, d) = self.corner(j % self.n());
        v.0.checked_mul(p)?
            .checked_add(v.1.checked_mul(q)?)?
            .checked_sub(c.checked_mul(d)?)
    }

    /// The number of edges whose normal's angle is below that of `v` (`or_equal`: not above).
    fn below(&self, v: (i128, i128), or_equal: bool) -> Option<usize> {
        let k = first_false(0, self.n() as i128, |i| {
            let r = self.row(i as usize);
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
        let n = self.n();
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
        let n = self.n();
        let [(j0, j1), _] = self.chains(v)?;
        Some([(j0 + n - 1) % n, (j1 - 1) % n])
    }

    /// The integer values of `v·x` over the polygon, `[ceil(least), floor(greatest)]`.
    fn range(&self, v: (i128, i128)) -> Option<(i128, i128)> {
        let [x, y] = self.ends(v)?;
        let (mut lo, mut hi) = (i128::MAX, i128::MIN);
        for j in [x, y] {
            let (_, _, d) = self.corner(j);
            let num = self.off(j, v, 0)?;
            lo = lo.min(i128_div_ceil(num, d)?);
            hi = hi.max(i128_div_floor(num, d)?);
        }
        Some((lo, hi))
    }

    /// The edge of `chain` that bounds the line `v·x == c`, for `c` between the ends.
    fn across(&self, (j0, j1): (usize, usize), v: (i128, i128), c: i128) -> Option<Form> {
        let n = self.n();
        // The corner where edge `j` starts; along the chain `v·x` there is monotone.
        let start = |j: usize| self.off(j + n - 1, v, c);
        // `c` lies between the chain's ends, so it rises where its start is below `c` or its
        // end above (at `c` equal to one end, the other end decides).
        let rising = start(j0)? < 0 || self.off(j1 - 1, v, c)? > 0;
        let k = first_false(j0 as i128, j1 as i128, |j| {
            let o = start(j as usize)?;
            Some(if rising { o <= 0 } else { o >= 0 })
        })?;
        Some(self.row((k as usize).saturating_sub(1).max(j0) % n))
    }
}

impl Convex for Polygon {
    fn n(&self) -> usize {
        self.rows.len()
    }
    fn row(&self, i: usize) -> Form {
        self.rows[i]
    }
    fn corner(&self, j: usize) -> Pt {
        self.corners[j]
    }
}

/// A [`Convex`] polygon cut by `g >= 0` where the line `g == 0` crosses its interior: the
/// edges `b`, `b + 1`, …, `b + cnt - 1` of `base` (cyclic) then `g`, its corners those of the
/// base between them, `a` (of the last edge kept and `g`) and `z` (of `g` and edge `b`), all
/// read from `rot` on so that edge 0 has the least angle ([`clip`]).
struct Clip<'b, P> {
    base: &'b P,
    g: Form,
    b: usize,
    cnt: usize,
    a: Pt,
    z: Pt,
    rot: usize,
}

impl<P: Convex> Convex for Clip<'_, P> {
    fn n(&self) -> usize {
        self.cnt + 1
    }
    fn row(&self, i: usize) -> Form {
        let i = (self.rot + i) % (self.cnt + 1);
        if i < self.cnt {
            self.base.row((self.b + i) % self.base.n())
        } else {
            self.g
        }
    }
    fn corner(&self, j: usize) -> Pt {
        let j = (self.rot + j) % (self.cnt + 1);
        if j + 1 < self.cnt {
            self.base.corner((self.b + j) % self.base.n())
        } else if j + 1 == self.cnt {
            self.a
        } else {
            self.z
        }
    }
}

/// A [`Convex`] polygon cut by `g >= 0`.
enum Cut<'b, P> {
    /// No point.
    Empty,
    /// `g` holds on the whole polygon.
    Whole,
    /// `g == 0` only touches it, at a corner or along an edge: the edges there and `g == 0`.
    Face(Vec<Form>),
    Part(Clip<'b, P>),
}

/// `base` cut by `g >= 0`; `None` past `i128`.
// Complexity tradeoff: naive, the edges of the cut polygon found again, O(V log V), or copied
// and cut, O(V). Here O(log V), with no copy: the corners where `g` is greatest and least by
// the binary search of [`Convex::ends`], then along each chain between them, where `g` falls,
// the last corner with `g > 0` by binary search; the cut polygon is the edges between them
// and `g`, read through [`Clip`]. The method is Chazelle and Dobkin's for the intersection of
// a line and a convex polygon ("Intersection of convex objects in two and three dimensions",
// JACM 34(1), 1987, Theorem 3, O(log p) for a p-gon, by the vertices extreme along the line's
// normal and a binary search on each chain between them); reading the cut polygon in place,
// O(1) more a step, is ours.
fn clip<P: Convex>(base: &P, g: Form) -> Option<Cut<'_, P>> {
    let n = base.n();
    let v = (g.0, g.1);
    let c = g.2.checked_neg()?;
    // `g` at corner `j`, times its `d > 0`.
    let val = |j: usize| base.off(j, v, c);
    let [x, y] = base.ends(v)?;
    let (vx, vy) = (val(x)?, val(y)?);
    let (top, low, hi, lo) = if vx >= vy {
        (x, y, vx, vy)
    } else {
        (y, x, vy, vx)
    };
    if hi < 0 {
        return Some(Cut::Empty);
    }
    if lo >= 0 {
        return Some(Cut::Whole);
    }
    if hi == 0 {
        // The face is corner `top` or an edge through it, which the edges `top - 1` to
        // `top + 2` bound on the line `g == 0`.
        let mut rows: Vec<Form> = (0..4).map(|i| base.row((top + n - 1 + i) % n)).collect();
        rows.push(g);
        rows.push(times(-1, g)?);
        return Some(Cut::Face(rows));
    }
    // From `top` to `low` either way round, `g` does not rise.
    let fwd = ((low + n - top) % n) as i128;
    let back = ((top + n - low) % n) as i128;
    let e = first_false(1, fwd + 1, |i| Some(val(top + i as usize)? > 0))? as usize - 1;
    let s = first_false(1, back + 1, |i| Some(val(top + n - i as usize)? > 0))? as usize - 1;
    // Corners `b` to `e` have `g > 0`; the edges `b` to `e + 1` are kept.
    let (b, e) = ((top + n - s) % n, (top + e) % n);
    let cnt = (e + n - b) % n + 2;
    let (last, first) = (base.row((e + 1) % n), base.row(b));
    if cross(&last, &g)? <= 0 || cross(&g, &first)? <= 0 {
        return None;
    }
    let (a, z) = (point(&last, &g)?, point(&g, &first)?);
    // The kept edge of least angle: the base's edge 0 where kept, else edge `b`; or `g`.
    let p0 = (n - b) % n;
    let least = if p0 < cnt { p0 } else { 0 };
    let r = base.row((b + least) % n);
    let rot = if angle_cmp(v, (r.0, r.1))?.is_lt() {
        cnt
    } else {
        least
    };
    Some(Cut::Part(Clip {
        base,
        g,
        b,
        cnt,
        a,
        z,
        rot,
    }))
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
    // The least `m` in `[rl, rh)` where the length stops rising, `rh` where it rises
    // throughout: concave, it rises and then does not. (`m + 1` is at most `rh`.)
    let peak = try_first_true(rl, rh, |&m| {
        let (Some(x), Some(y)) = (len(m, work).map_err(Some)?, len(m + 1, work).map_err(Some)?)
        else {
            return Err(None);
        };
        let (Some(l), Some(r)) = (y.0.checked_mul(x.1), x.0.checked_mul(y.1)) else {
            return Err(None);
        };
        Ok(l <= r)
    });
    let Some(top) = found(peak)? else {
        return Ok(None);
    };
    let Some(at_top) = long(top, work)? else {
        return Ok(None);
    };
    if !at_top {
        return Ok(Some(None));
    }
    // The first value of `[rl, top]` with length at least 1, and the last of `[top, rh]`.
    let Some(d1) = found(try_first_true(rl, top, |&m| asked(long(m, work))))? else {
        return Ok(None);
    };
    let Some(d2) = found(try_last_true(top, rh, |&m| asked(long(m, work))))? else {
        return Ok(None);
    };
    Ok(Some(Some((d1, d2))))
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
    poly: &impl Convex,
    (a, b): (i128, i128),
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    let Some((s, t)) = bezout(a, b) else {
        return Ok(None);
    };
    let n = poly.n() as u64;
    let log = u64::from(n.bit_len() + 1);
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
        return Ok(Some(finite(merge_runs(runs))));
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

/// The real length of the stretch of `w` that `rows` leave on the line `u == c`
/// ([`length`]).
enum Stretch {
    Empty,
    Infinite,
    /// `num / den`, `den > 0`.
    Finite(i128, i128),
}

impl Stretch {
    /// At least 1 long, so holding an integer `w`.
    fn long(&self) -> bool {
        match self {
            Stretch::Empty => false,
            Stretch::Infinite => true,
            Stretch::Finite(num, den) => num >= den,
        }
    }
}

/// `x > y` for fractions `(num, den)` with `den > 0`; `None` past `i128`.
fn greater(x: (i128, i128), y: (i128, i128)) -> Option<bool> {
    Some(x.0.checked_mul(y.1)? > y.0.checked_mul(x.1)?)
}

/// The length of the stretch of real `w` where every row `E·u + D·w + C >= 0` holds at
/// `u == c`; `None` past `i128`. O(rows).
fn length(rows: &[Row], c: i128) -> Option<Stretch> {
    // The greatest lower bound and least upper bound of `w`, as fractions.
    let mut lo: Option<(i128, i128)> = None;
    let mut hi: Option<(i128, i128)> = None;
    for &(e, d, k) in rows {
        let y = e.checked_mul(c)?.checked_add(k)?;
        match d.signum() {
            0 if y < 0 => return Some(Stretch::Empty),
            0 => {}
            1 => {
                // `w >= -y / d`.
                let x = (y.checked_neg()?, d);
                if lo.map_or(Some(true), |l| greater(x, l))? {
                    lo = Some(x);
                }
            }
            _ => {
                // `w <= y / -d`.
                let x = (y, d.checked_neg()?);
                if hi.map_or(Some(true), |h| greater(h, x))? {
                    hi = Some(x);
                }
            }
        }
    }
    let (Some((ln, ld)), Some((hn, hd))) = (lo, hi) else {
        return Some(Stretch::Infinite);
    };
    let num = hn.checked_mul(ld)?.checked_sub(ln.checked_mul(hd)?)?;
    let den = hd.checked_mul(ld)?;
    Some(if num < 0 {
        Stretch::Empty
    } else {
        Stretch::Finite(num, den)
    })
}

/// [`poly_values`] over an [`Open`] region: the polygon `k` up to the lid and past it what
/// lies between the rays `rays` ([`open`]).
// Complexity tradeoff: naive, the shadows of all h half-planes, O(h²) a name ([`u_values`]).
// Here O((log d + S)·log V) a name, as [`poly_values`]: the line `u == c` within the
// polygon's range of `u` is bounded by the edges of `k` found by binary search, the lid
// standing for `ra` and `rb`; past that range it meets only the region past the lid (the
// corner `X` of `ra` and `rb` lies before the lid on each ray, so where the region runs on
// toward greater `u`, `u(X)` is below the greater of `u(l0)`, `u(l1)`, which `k` reaches),
// bounded by `ra` and `rb` alone. Where the region runs on toward greater `u` and not lesser,
// its least `u` is that of `k`, and the length of the stretch of `w`, concave and at least 0
// on the region's whole range, does not fall: the values from the first at least 1 long, d
// from the least, on are one open run, found by doubling steps and halving, and the S before
// it are tried one by one. Past `k` the length is linear; where it does not rise there and is
// below 1, the values with a point may be periodic, and the name declines. Open both ways, the
// length is the same everywhere, so every value or decline; open neither way (a half-strip
// along `w`), the stretch is infinite on the range of `k`.
fn open_values<K: Convex>(
    k: &K,
    rays: &Rays,
    (a, b): (i128, i128),
    work: &mut Work,
) -> Result<Option<Vec<Run>>, Refusal> {
    let (Some(vs), Some(ve)) = (dot((a, b), rays.ds), dot((a, b), rays.de)) else {
        return Ok(None);
    };
    if vs <= 0 && ve <= 0 && (vs < 0 || ve < 0) {
        // Open toward lesser `u` only: the values of `-u`, negated.
        let (Some(na), Some(nb)) = (a.checked_neg(), b.checked_neg()) else {
            return Ok(None);
        };
        let Some(runs) = open_values(k, rays, (na, nb), work)? else {
            return Ok(None);
        };
        let flip = |x: Option<i128>| match x {
            None => Some(None),
            Some(x) => x.checked_neg().map(Some),
        };
        let mut out = Vec::with_capacity(runs.len());
        for (l, h) in runs.into_iter().rev() {
            let (Some(l), Some(h)) = (flip(h), flip(l)) else {
                return Ok(None);
            };
            out.push((l, h));
        }
        return Ok(Some(out));
    }
    let Some((s, t)) = bezout(a, b) else {
        return Ok(None);
    };
    let step = log_pieces(k.n());
    work.charge(step.saturating_mul(4))?;
    let to_uw = |(ha, hb, hc): Form| -> Option<Row> {
        let e = ha.checked_mul(s)?.checked_add(hb.checked_mul(t)?)?;
        let d = hb.checked_mul(a)?.checked_sub(ha.checked_mul(b)?)?;
        Some((e, d, hc))
    };
    let v = (a, b);
    let (Some(cu), Some((rl, rh))) = (k.chains(v), k.range(v)) else {
        return Ok(None);
    };
    // The rows bounding `w` on the line `u == c`.
    let rows_at = |c: i128| -> Option<Vec<Row>> {
        let mut out = Vec::with_capacity(4);
        if rl <= c && c <= rh {
            for chain in cu {
                let f = k.across(chain, v, c)?;
                if f == rays.lid {
                    out.extend([to_uw(rays.ra)?, to_uw(rays.rb)?]);
                } else {
                    out.push(to_uw(f)?);
                }
            }
        } else {
            out.extend([to_uw(rays.ra)?, to_uw(rays.rb)?]);
        }
        Some(out)
    };
    let len = |c: i128, work: &mut Work| -> Result<Option<Stretch>, Refusal> {
        work.charge(step)?;
        Ok(rows_at(c).and_then(|rows| length(&rows, c)))
    };
    let long = |c: i128, work: &mut Work| -> Result<Option<bool>, Refusal> {
        Ok(len(c, work)?.map(|l| l.long()))
    };
    if vs <= 0 && ve <= 0 {
        // Open neither way: both rays run along `w`, a half-strip; its stretch is infinite on
        // the range of `k`, checked at both ends (the length is concave between them).
        if rl > rh {
            return Ok(Some(Vec::new()));
        }
        return Ok(match (long(rl, work)?, long(rh, work)?) {
            (Some(true), Some(true)) => Some(vec![(Some(rl), Some(rh))]),
            _ => None,
        });
    }
    if vs < 0 || ve < 0 {
        // Open both ways.
        return Ok(match long(rl, work)? {
            Some(true) => Some(vec![(None, None)]),
            _ => None,
        });
    }
    // Open toward greater `u` only. Past `k` the length is linear: it must reach 1.
    let Some(c1) = rh.checked_add(1).map(|x| x.max(rl)) else {
        return Ok(None);
    };
    let Some(c2) = c1.checked_add(1) else {
        return Ok(None);
    };
    let (Some(l1), Some(l2)) = (len(c1, work)?, len(c2, work)?) else {
        return Ok(None);
    };
    let rises = match (&l1, &l2) {
        _ if l1.long() || l2.long() => true,
        (Stretch::Finite(n1, d1), Stretch::Finite(n2, d2)) => {
            greater((*n2, *d2), (*n1, *d1)) == Some(true)
        }
        _ => false,
    };
    if !rises {
        return Ok(None);
    }
    // The first long value from `rl`, by doubling steps and then halving.
    let Some(mut out) = rl.checked_sub(1) else {
        return Ok(None);
    };
    let mut size: i128 = 1;
    let d1 = loop {
        let Some(probe) = rl.checked_add(size - 1) else {
            return Ok(None);
        };
        match long(probe, work)? {
            None => return Ok(None),
            Some(true) => match found(try_first_true(out + 1, probe, |&m| asked(long(m, work))))? {
                Some(d1) => break d1,
                None => return Ok(None),
            },
            Some(false) => {
                out = probe;
                let Some(next) = size.checked_mul(2) else {
                    return Ok(None);
                };
                size = next;
            }
        }
    };
    let mut runs: Vec<Run> = Vec::new();
    for c in rl..d1 {
        work.charge(step)?;
        let Some(rows) = rows_at(c) else {
            return Ok(None);
        };
        match fiber(&rows, c) {
            None => return Ok(None),
            Some(None) => {}
            Some(Some(_)) => match runs.last_mut() {
                Some((_, Some(e))) if *e + 1 == c => *e = c,
                _ => runs.push((Some(c), Some(c))),
            },
        }
    }
    match runs.last_mut() {
        Some((_, h)) if *h == Some(d1 - 1) => *h = None,
        _ => runs.push((Some(d1), None)),
    }
    Ok(Some(runs))
}

/// A run of values, `None` an open end.
type Run = (Option<i128>, Option<i128>);

/// Finite runs as [`Run`]s.
fn finite(runs: Vec<(i128, i128)>) -> Vec<Run> {
    runs.into_iter().map(|(l, h)| (Some(l), Some(h))).collect()
}

/// The union of the closed runs `runs`, each `l <= h`, in any order, as sorted disjoint runs
/// with no two adjacent: sorted, then each run joined to the last kept one where it overlaps or
/// touches it. O(r log r) for r runs; the sort is needed, as the runs come one per `w` in the
/// order of `w`, not of `u`. The one copy of the narrower way of [`u_runs`] and of
/// [`poly_values`] (dryA5 row 22).
///
/// The shared [`zed_collections::intervals::coalesce`] (DRY-sorted-structures-2) tests
/// `l <= e + 1` without forming `e + 1` at `i128::MAX`, so it is exact over all of `i128`. The
/// copies tested `e >= l - 1`, which overflowed at `l == i128::MIN` (a panic in a debug build).
fn merge_runs(runs: Vec<(i128, i128)>) -> Vec<(i128, i128)> {
    zed_collections::intervals::coalesce(runs)
}

/// A row `x·X + y·Y + c >= 0` over two integer unknowns.
type Row = (i128, i128, i128);

/// Bounds on integer `X` from `p·X + q >= 0`, met into `(lo, hi)`; `Some(false)` where it never
/// holds, `None` past `i128`.
fn meet(p: i128, q: i128, lo: &mut Option<i128>, hi: &mut Option<i128>) -> Option<bool> {
    match p.signum() {
        0 => Some(q >= 0),
        1 => {
            let l = i128_div_ceil(q.checked_neg()?, p)?;
            *lo = Some(lo.map_or(l, |v| v.max(l)));
            Some(true)
        }
        _ => {
            let h = i128_div_floor(q, p.checked_neg()?)?;
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

#[cfg(test)]
mod merge_runs_tests {
    use super::merge_runs;

    /// Overlapping, nested, touching and apart runs, and the ends of `i128`, where the copies'
    /// `l - 1` overflowed.
    #[test]
    fn runs_are_joined_where_they_overlap_or_touch() {
        assert_eq!(
            merge_runs(vec![(7, 9), (0, 5), (2, 3), (6, 6), (11, 12)]),
            [(0, 9), (11, 12)]
        );
        assert_eq!(merge_runs(vec![]), []);
        let (min, max) = (i128::MIN, i128::MAX);
        assert_eq!(
            merge_runs(vec![(min, min), (min, 0), (2, max), (max, max)]),
            [(min, 0), (2, max)]
        );
        assert_eq!(merge_runs(vec![(min + 1, 0), (min, min)]), [(min, 0)]);
    }
}
