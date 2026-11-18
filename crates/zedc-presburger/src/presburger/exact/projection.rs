//! Two ways to give a cell of the cover (`super::cover`) the values of an implicant that run
//! without end, which the elimination of `super::cell` leaves out (PRES-pugh-exact-projection-
//! research; the stuck case is `an_unbounded_conjunction_needs_one_cell`, whose cells each held
//! eight values of a ray, so the cover never ended):
//! - [`pugh`]: the exact projection of the implicant onto the symbol, by the Omega test's
//!   projection (Pugh, "A practical algorithm for exact array dependence analysis", CACM 35(8),
//!   1992, sections "Eliminating equality constraints", "Dark shadow" and "Projection"):
//!   equalities removed with Pugh's `mod^` step, the symbol kept as a protected variable
//!   whose residue is fixed when every other coefficient shares a factor, then each other
//!   variable removed by an exact Fourier-Motzkin step where every lower or every upper
//!   coefficient is 1, else by the dark shadow and every splinter next to a lower bound.
//!   The answer is a union of stride sets `{lo <= v <= hi, v == res mod step}`.
//! - [`rays`]: the recession directions of the implicant: a direction `d` with `A·d >= 0`
//!   over its inequalities, `E·d == 0` over its equalities and the symbol's step `d_s` below
//!   (or above) zero; with `g = |d_s|`, one point of the implicant in each residue of the
//!   symbol modulo `g` gives a ray of values from that point on. About `g + 1` questions.
//!
//! Both are measured against each other and against the old cell in
//! docs/handoff/PRES-pugh-findings.md; they are switched by [`METHOD`] for that comparison.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::super::meter::{EXACT_QUESTIONS, LISTED, Work};
use super::super::{Atom, Con, Formula, Lin, Model, Refusal, Rel};

/// The in-cell step for the values an implicant has without end.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Method {
    /// The cell as before this research: elimination where it is exact, else runs or a fixed
    /// stride atom.
    Old,
    /// Pugh's exact projection of the implicant (`pugh`).
    Pugh,
    /// The old cell and the recession rays of the implicant (`rays`).
    Rays,
}

thread_local! {
    /// Test control: the in-cell method, in place of [`Method::Pugh`]. Set by the tests that
    /// compare the methods; read from no environment variable (PRES-pugh-xr round 3: the rules
    /// allow no debug switch read from the environment in delivered code).
    pub static METHOD: Cell<Option<Method>> = const { Cell::new(None) };
}

/// The method in force: [`METHOD`] where set, else Pugh's.
pub fn method() -> Method {
    METHOD.get().unwrap_or(Method::Pugh)
}

/// `{v : lo <= v <= hi, v == res mod step}`, an absent end infinite, `step >= 1`,
/// `0 <= res < step`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Strided {
    pub(super) lo: Option<Int>,
    pub(super) hi: Option<Int>,
    pub(super) step: Int,
    pub(super) res: Int,
}

/// The exact projection of the conjunction `rows` onto `s`, as a union of stride sets; each
/// row made is charged its terms and one more to `work`. `rows` hold no product atom.
pub(super) fn pugh(rows: &[Con], s: &Atom, work: &mut Work) -> Result<Vec<Strided>, Refusal> {
    let mut out = Vec::new();
    let mut fresh = 0u32;
    let mut at = Int::from(1);
    let mut from = Int::from(0);
    project(
        rows.to_vec(),
        s,
        &mut at,
        &mut from,
        work,
        &mut fresh,
        &mut out,
    )?;
    Ok(out)
}

/// `a mod^ b` of Pugh's equality step: `a - b·floor(a/b + 1/2)`, in `(-b/2, b/2]`.
fn mod_hat(a: &Int, b: &Int) -> Int {
    let two = Int::from(2);
    let q = (&(&two * a) + b).div_floor(&(&two * b));
    a - &(b * &q)
}

/// `rows` with `x` replaced by `e`.
fn substituted(rows: Vec<Con>, x: &Atom, e: &Lin) -> Vec<Con> {
    rows.into_iter()
        .map(|mut k| {
            if let Some(c) = k.lin.terms.remove(x) {
                k.lin.plus_assign(&e.times(c));
            }
            k
        })
        .collect()
}

/// `rows` divided by the gcd of each row's coefficients (an inequality's constant rounded
/// down, an equality whose constant the gcd does not divide has no point), rows with no
/// atom checked and dropped, and inequalities over the same terms kept once at their
/// tightest; a pair `t + c >= 0`, `-t + d >= 0` with `c + d < 0` has no point and with
/// `c + d == 0` is the equality `t + c == 0`. `None` where the rows have no point.
fn tidied(rows: Vec<Con>) -> Option<Vec<Con>> {
    let mut eqs: BTreeMap<BTreeMap<Atom, Int>, Int> = BTreeMap::new();
    let mut ges: BTreeMap<BTreeMap<Atom, Int>, Int> = BTreeMap::new();
    for k in rows {
        let Lin { terms, constant } = k.lin;
        if terms.is_empty() {
            let ok = match k.rel {
                Rel::Ge => !constant.is_negative(),
                Rel::Eq => constant.is_zero(),
            };
            if !ok {
                return None;
            }
            continue;
        }
        let g = terms.values().fold(Int::from(0), |g, c| g.gcd(c));
        let (terms, constant) = if g == Int::from(1) {
            (terms, constant)
        } else {
            if k.rel == Rel::Eq && !constant.mod_floor(&g).is_zero() {
                return None;
            }
            let terms = terms
                .into_iter()
                .map(|(a, c)| (a, c.div_floor(&g)))
                .collect();
            (terms, constant.div_floor(&g))
        };
        match k.rel {
            Rel::Eq => {
                // `t + c == 0` and `-t - c == 0` are one row: keep the one whose first
                // coefficient is above zero.
                let flip = terms.values().next().is_some_and(Int::is_negative);
                let (terms, constant) = if flip {
                    (
                        terms.into_iter().map(|(a, c)| (a, -&c)).collect(),
                        -&constant,
                    )
                } else {
                    (terms, constant)
                };
                match eqs.get(&terms) {
                    Some(c) if c != &constant => return None,
                    _ => {
                        eqs.insert(terms, constant);
                    }
                }
            }
            Rel::Ge => {
                let e = ges.entry(terms).or_insert_with(|| constant.clone());
                if constant < *e {
                    *e = constant;
                }
            }
        }
    }
    let mut out: Vec<Con> = Vec::with_capacity(eqs.len() + ges.len());
    let mut paired: BTreeSet<BTreeMap<Atom, Int>> = BTreeSet::new();
    for (terms, c) in &ges {
        if paired.contains(terms) {
            continue;
        }
        let neg: BTreeMap<Atom, Int> = terms.iter().map(|(a, k)| (a.clone(), -k)).collect();
        if let Some(d) = ges.get(&neg) {
            let sum = c + d;
            if sum.is_negative() {
                return None;
            }
            if sum.is_zero() {
                paired.insert(terms.clone());
                paired.insert(neg);
                out.push(Con {
                    lin: Lin {
                        terms: terms.clone(),
                        constant: c.clone(),
                    },
                    rel: Rel::Eq,
                });
                continue;
            }
        }
        out.push(Con {
            lin: Lin {
                terms: terms.clone(),
                constant: c.clone(),
            },
            rel: Rel::Ge,
        });
    }
    for (terms, c) in eqs {
        out.push(Con {
            lin: Lin { terms, constant: c },
            rel: Rel::Eq,
        });
    }
    Some(out)
}

/// The values `at·t + from` of `s` at the points of `rows`, `t` standing for `s` (`at` zero
/// once `t` is fixed), added to `out`.
fn project(
    rows: Vec<Con>,
    t: &Atom,
    at: &mut Int,
    from: &mut Int,
    work: &mut Work,
    fresh: &mut u32,
    out: &mut Vec<Strided>,
) -> Result<(), Refusal> {
    let size: u64 = rows.iter().map(|k| k.lin.terms.len() as u64 + 1).sum();
    work.read(size)?;
    let Some(mut rows) = tidied(rows) else {
        return Ok(());
    };
    // An equality with an atom other than `t`.
    if let Some(i) = (0..rows.len())
        .find(|&i| rows[i].rel == Rel::Eq && rows[i].lin.terms.keys().any(|a| a != t))
    {
        let e = rows[i].lin.clone();
        let unit = (e.terms.iter()).find(|(a, c)| *a != t && c.abs() == Int::from(1));
        if let Some((x, c)) = unit {
            // `c·x + r == 0`, `c = ±1`: `x = -c·r`.
            let (x, c) = (x.clone(), c.clone());
            let mut r = e.clone();
            r.terms.remove(&x);
            rows.swap_remove(i);
            let rows = substituted(rows, &x, &r.times(-&c));
            return project(rows, t, at, from, work, fresh, out);
        }
        let g = (e.terms.iter())
            .filter(|(a, _)| *a != t)
            .fold(Int::from(0), |g, (_, c)| g.gcd(c));
        if g > Int::from(1) {
            // `a·t + c == 0 mod g`: with `d = gcd(a, g)`, `t == r mod g/d` (the protected
            // variable's step of Pugh's projection, "Projection", which adds `g·σ == ...`).
            let a = e.terms.get(t).cloned().unwrap_or_else(|| Int::from(0));
            let c = e.constant.clone();
            let d = a.gcd(&g);
            if !c.mod_floor(&d).is_zero() {
                return Ok(());
            }
            let m = g.div_floor(&d);
            let (a1, c1) = (a.div_floor(&d), c.div_floor(&d));
            // `a1·r == -c1 mod m`, `a1` and `m` coprime.
            let r = if m == Int::from(1) {
                Int::from(0)
            } else {
                let (_, inv, _) = a1.mod_floor(&m).extended_gcd(&m).expect("gcd");
                (&(-&c1) * &inv).mod_floor(&m)
            };
            // `t := m·t + r`.
            let e_t = Lin {
                terms: [(t.clone(), m.clone())].into_iter().collect(),
                constant: r.clone(),
            };
            let rows = substituted(rows, t, &e_t);
            let (at0, from0) = (at.clone(), from.clone());
            *from = &(&*at * &r) + &*from;
            *at = &*at * &m;
            let done = project(rows, t, at, from, work, fresh, out);
            (*at, *from) = (at0, from0);
            return done;
        }
        // Pugh's `mod^` step on the atom with the least coefficient other than `t`.
        let (k, ak) = (e.terms.iter())
            .filter(|(a, _)| *a != t)
            .min_by(|x, y| x.1.abs().cmp(&y.1.abs()).then_with(|| x.0.cmp(y.0)))
            .map(|(a, c)| (a.clone(), c.clone()))
            .expect("an atom other than t");
        let m = &ak.abs() + &Int::from(1);
        *fresh += 1;
        let sigma = Atom::Sym(format!("#pugh{fresh}").into());
        let sign = if ak.is_negative() {
            Int::from(-1)
        } else {
            Int::from(1)
        };
        // `x_k = -sign(a_k)·m·σ + Σ_{i != k} sign(a_k)·(a_i mod^ m)·x_i + sign(a_k)·(c mod^ m)`.
        let mut ek = Lin {
            terms: [(sigma, &(-&sign) * &m)].into_iter().collect(),
            constant: &sign * &mod_hat(&e.constant, &m),
        };
        for (a, c) in &e.terms {
            if *a != k {
                let v = &sign * &mod_hat(c, &m);
                if !v.is_zero() {
                    ek.terms.insert(a.clone(), v);
                }
            }
        }
        let rows = substituted(rows, &k, &ek);
        return project(rows, t, at, from, work, fresh, out);
    }
    // An equality over `t` alone: `t` fixed, kept where the rest has a point.
    if let Some(i) = (0..rows.len()).find(|&i| rows[i].rel == Rel::Eq) {
        let e = rows[i].lin.clone();
        let a = e.terms.get(t).cloned().expect("t");
        if !e.constant.mod_floor(&a).is_zero() {
            return Ok(());
        }
        let v = -&e.constant.div_floor(&a);
        rows.swap_remove(i);
        let rows = substituted(rows, t, &Lin::constant(v.clone()));
        let (at0, from0) = (at.clone(), from.clone());
        *from = &(&*at * &v) + &*from;
        *at = Int::from(0);
        let done = project(rows, t, at, from, work, fresh, out);
        (*at, *from) = (at0, from0);
        return done;
    }
    // Inequalities only. The atoms other than `t`, each with its lower and upper rows.
    let mut sides: BTreeMap<Atom, (Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for (i, k) in rows.iter().enumerate() {
        for (a, c) in &k.lin.terms {
            if a == t {
                continue;
            }
            let e = sides.entry(a.clone()).or_default();
            if c.is_positive() {
                e.0.push(i)
            } else {
                e.1.push(i)
            }
        }
    }
    if sides.is_empty() {
        let set = bounded(&rows, t);
        let Some((lo, hi)) = set.bounds() else {
            return Ok(());
        };
        if at.is_zero() {
            out.push(Strided {
                lo: Some(from.clone()),
                hi: Some(from.clone()),
                step: Int::from(1),
                res: Int::from(0),
            });
            return Ok(());
        }
        let map = |e: &End| match e {
            End::Fin(n) => Some(&(&*at * &Int::from(n)) + &*from),
            _ => None,
        };
        out.push(Strided {
            lo: map(lo),
            hi: map(hi),
            step: at.clone(),
            res: from.mod_floor(at),
        });
        return Ok(());
    }
    // An atom bounded on one side only: its rows dropped, exactly.
    if let Some((x, _)) = sides
        .iter()
        .find(|(_, (l, u))| l.is_empty() || u.is_empty())
    {
        let x = x.clone();
        let rows = rows
            .into_iter()
            .filter(|k| !k.lin.terms.contains_key(&x))
            .collect();
        return project(rows, t, at, from, work, fresh, out);
    }
    // The atom to remove: one whose elimination is exact, with the fewest new rows; else the
    // one with the fewest splinters, then the fewest new rows.
    let coef = |i: usize, x: &Atom| rows[i].lin.terms[x].abs();
    let splinters = |x: &Atom, l: &[usize], u: &[usize]| -> Int {
        let amax = u.iter().map(|&i| coef(i, x)).max().expect("upper");
        let mut n = Int::from(0);
        for &i in l {
            let b = coef(i, x);
            let top = (&(&(&amax * &b) - &amax) - &b).div_floor(&amax);
            if !top.is_negative() {
                n = &n + &(&top + &Int::from(1));
            }
        }
        n
    };
    let exact = |x: &Atom, l: &[usize], u: &[usize]| {
        l.iter().all(|&i| coef(i, x) == Int::from(1))
            || u.iter().all(|&i| coef(i, x) == Int::from(1))
    };
    let (x, (lower, upper)) = sides
        .iter()
        .min_by(|(x, (l, u)), (y, (m, v))| {
            let (ex, ey) = (exact(x, l, u), exact(y, m, v));
            ey.cmp(&ex)
                .then_with(|| {
                    if ex {
                        Int::from(0).cmp(&Int::from(0))
                    } else {
                        splinters(x, l, u).cmp(&splinters(y, m, v))
                    }
                })
                .then_with(|| (l.len() * u.len()).cmp(&(m.len() * v.len())))
                .then_with(|| x.cmp(y))
        })
        .map(|(x, lu)| (x.clone(), lu.clone()))
        .expect("an atom");
    let is_exact = exact(&x, &lower, &upper);
    let others: Vec<Con> = (rows.iter())
        .filter(|k| !k.lin.terms.contains_key(&x))
        .cloned()
        .collect();
    // For each lower `b·x + l >= 0` and upper `-a·x + u >= 0`: `a·(b·x + l) + b·(-a·x + u) =
    // a·l + b·u >= 0`, the real shadow, and `>= (a-1)(b-1)`, the dark one.
    let mut shadow = others.clone();
    for &i in &lower {
        for &j in &upper {
            let (b, a) = (coef(i, &x), coef(j, &x));
            let mut lin = rows[i].lin.times(a.clone());
            lin.plus_assign(&rows[j].lin.times(b.clone()));
            debug_assert!(!lin.terms.contains_key(&x));
            if !is_exact {
                lin.constant = &lin.constant - &(&(&a - &Int::from(1)) * &(&b - &Int::from(1)));
            }
            shadow.push(Con { lin, rel: Rel::Ge });
        }
    }
    project(shadow, t, at, from, work, fresh, out)?;
    if is_exact {
        return Ok(());
    }
    // The splinters: for each lower `b·x >= β` and `a` the largest upper coefficient, the
    // rows with `b·x == β + i` for `0 <= i <= (a·b - a - b)/a`.
    let amax = upper.iter().map(|&i| coef(i, &x)).max().expect("upper");
    for &i in &lower {
        let b = coef(i, &x);
        let top = (&(&(&amax * &b) - &amax) - &b).div_floor(&amax);
        let mut k = Int::from(0);
        while k <= top {
            let mut one = rows.clone();
            let mut lin = rows[i].lin.clone();
            lin.constant = &lin.constant - &k;
            one.push(Con { lin, rel: Rel::Eq });
            project(one, t, at, from, work, fresh, out)?;
            k = &k + &Int::from(1);
        }
    }
    Ok(())
}

/// A piece of values with no end, with holes: the values of `piece` whose residue modulo
/// `step` is marked in `have`.
pub(super) struct Tail {
    pub(super) piece: IntervalSet,
    pub(super) step: Int,
    pub(super) have: Vec<bool>,
}

/// The union of `parts` as a set of ranges, the values of each finite piece with holes
/// listed one by one, each charged to `work`, and each residue table of the lcm of the
/// steps charged its size; with it, each piece with holes and no end that the parts with
/// no holes do not fill, which ranges cannot hold ([`Tail`]).
pub(super) fn ranges(
    parts: &[Strided],
    work: &mut Work,
) -> Result<(IntervalSet, Vec<Tail>), Refusal> {
    let end_lo = |p: &Strided| p.lo.as_ref().map_or(End::NegInf, fin);
    let end_hi = |p: &Strided| p.hi.as_ref().map_or(End::PosInf, fin);
    let plain = IntervalSet::from_pieces(
        (parts.iter())
            .filter(|p| p.step == Int::from(1))
            .map(|p| (end_lo(p), end_hi(p)))
            .collect(),
    );
    let holed: Vec<&Strided> = parts.iter().filter(|p| p.step > Int::from(1)).collect();
    if holed.is_empty() {
        return Ok((plain, Vec::new()));
    }
    // The line cut at every finite end of a holed part: in each segment the same parts hold.
    let mut cuts: BTreeSet<Int> = BTreeSet::new();
    for p in &holed {
        if let Some(l) = &p.lo {
            cuts.insert(l.clone());
        }
        if let Some(h) = &p.hi {
            cuts.insert(h + &Int::from(1));
        }
    }
    let cuts: Vec<Int> = cuts.into_iter().collect();
    let mut segments: Vec<(Option<Int>, Option<Int>)> = Vec::with_capacity(cuts.len() + 1);
    if let (Some(first), Some(last)) = (cuts.first(), cuts.last()) {
        segments.push((None, Some(first - &Int::from(1))));
        for w in cuts.windows(2) {
            segments.push((Some(w[0].clone()), Some(&w[1] - &Int::from(1))));
        }
        segments.push((Some(last.clone()), None));
    } else {
        segments.push((None, None));
    }
    let mut pieces: Vec<(End, End)> = plain.pieces().cloned().collect();
    let mut tails = Vec::new();
    for (lo, hi) in segments {
        work.charge(holed.len() as u64)?;
        let seg = IntervalSet::range(
            lo.as_ref().map_or(End::NegInf, fin),
            hi.as_ref().map_or(End::PosInf, fin),
        );
        let inside = |p: &&&Strided| {
            p.lo.as_ref()
                .is_none_or(|l| lo.as_ref().is_some_and(|v| v >= l))
                && p.hi
                    .as_ref()
                    .is_none_or(|h| hi.as_ref().is_some_and(|v| v <= h))
        };
        let active: Vec<&&Strided> = holed.iter().filter(inside).collect();
        if active.is_empty() {
            continue;
        }
        let rest = seg.minus(&plain);
        if rest.is_empty() {
            continue;
        }
        let lcm = active.iter().fold(Int::from(1), |l, p| {
            let g = l.gcd(&p.step);
            &l.div_floor(&g) * &p.step
        });
        let n = lcm
            .to_i128()
            .and_then(|n| u64::try_from(n).ok())
            .unwrap_or(u64::MAX);
        // The table is filled and read a byte at a time, about a hundredth of a unit each
        // (a unit is about 100 ns, `EXACT_LIMIT`): one unit for each 64 residues.
        work.charge(n / 64 + 1)?;
        let mut have = vec![false; n as usize];
        for p in &active {
            let step = p.step.to_i128().expect("charged") as usize;
            let mut r = p.res.to_i128().expect("charged") as usize;
            while r < n as usize {
                have[r] = true;
                r += step;
            }
        }
        if have.iter().all(|&b| b) {
            pieces.extend(rest.pieces().cloned());
            continue;
        }
        for (l, u) in rest.pieces() {
            let (End::Fin(l), End::Fin(u)) = (l, u) else {
                tails.push(Tail {
                    piece: IntervalSet::range(l.clone(), u.clone()),
                    step: lcm.clone(),
                    have: have.clone(),
                });
                continue;
            };
            listed(&Int::from(l), &Int::from(u), &lcm, &have, work, &mut pieces)?;
        }
    }
    Ok((IntervalSet::from_pieces(pieces), tails))
}

/// The values from `l` to `u` whose residue modulo `step` is marked in `have`, added to
/// `pieces`, each charged [`LISTED`] units of `work`, and the table one unit for each 64 residues.
pub(super) fn listed(
    l: &Int,
    u: &Int,
    step: &Int,
    have: &[bool],
    work: &mut Work,
    pieces: &mut Vec<(End, End)>,
) -> Result<(), Refusal> {
    // The table read once, one unit for each 64 residues, as where it is made.
    work.charge(have.len() as u64 / 64 + 1)?;
    for (r, _) in have.iter().enumerate().filter(|(_, b)| **b) {
        let r = Int::from(r as i64);
        // The first value at or above `l` with residue `r`.
        let mut v = l + &(&r - l).mod_floor(step);
        while &v <= u {
            work.charge(LISTED)?;
            pieces.push((fin(&v), fin(&v)));
            v = &v + step;
        }
    }
    Ok(())
}

/// The recession rays of the implicant `rows` at `s`, for each sign: a direction `d` of the
/// rows (`A·d >= 0`, `E·d == 0`) with `d_s <= -1` (or `>= 1`), asked of the solver; with
/// `g = |d_s|`, for each residue of `s` modulo `g` a point of the rows, from which `d` runs
/// without end. Each question is charged `size` and the rows' own terms, and the solver's
/// work on it ([`asked`]). A refusal of a question gives no ray for that sign (or residue);
/// past the work limit, `rays` is refused.
pub(super) fn rays(
    rows: &[Con],
    s: &Atom,
    size: u64,
    work: &mut Work,
) -> Result<Vec<Strided>, Refusal> {
    let mut out = Vec::new();
    let homogeneous: Vec<Formula> = (rows.iter())
        .map(|k| {
            Formula::Con(Con {
                lin: Lin {
                    terms: k.lin.terms.clone(),
                    constant: Int::from(0),
                },
                rel: k.rel,
            })
        })
        .collect();
    let rows_f: Vec<Formula> = rows.iter().map(|k| Formula::Con(k.clone())).collect();
    let row_terms: u64 = rows.iter().map(|k| k.lin.terms.len() as u64 + 1).sum();
    for down in [true, false] {
        // `d_s <= -1` or `-d_s <= -1`.
        let sign = if down { Int::from(1) } else { Int::from(-1) };
        let mut ask = homogeneous.clone();
        ask.push(Formula::Con(Con {
            lin: Lin {
                terms: [(s.clone(), -&sign)].into_iter().collect(),
                constant: Int::from(-1),
            },
            rel: Rel::Ge,
        }));
        work.read(size + row_terms)?;
        EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
        let Some(d) = asked(work, &Formula::and(ask))? else {
            continue;
        };
        let g = d.get(s).cloned().unwrap_or_else(|| Int::from(0)).abs();
        if g.is_zero() {
            continue;
        }
        // One point of the rows in each residue of `s` modulo `g`.
        let mut r = Int::from(0);
        while r < g {
            work.read(size + row_terms + 2)?;
            EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
            let k = Atom::Sym("#ray".into());
            let mut ask = rows_f.clone();
            ask.push(Formula::Con(Con {
                lin: Lin {
                    terms: [(s.clone(), Int::from(1)), (k, -&g)].into_iter().collect(),
                    constant: -&r,
                },
                rel: Rel::Eq,
            }));
            if let Some(p) = asked(work, &Formula::and(ask))? {
                let v = p.get(s).cloned().unwrap_or_else(|| Int::from(0));
                let (lo, hi) = if down {
                    (None, Some(v))
                } else {
                    (Some(v), None)
                };
                out.push(Strided {
                    lo,
                    hi,
                    step: g.clone(),
                    res: r.clone(),
                });
            }
            r = &r + &Int::from(1);
        }
    }
    Ok(out)
}

/// A question of [`rays`], asked as the cover asks its own (`Work::ask`): the solver's work
/// on it charged to `work`. `None` where it has no point or the solver refuses it for another
/// cause, as the residue questions of the cover read such a refusal; past the work limit,
/// refused with [`Refusal::Questions`] (PRES-rays-unmetered: the solver's work here was not
/// charged, only the fixed reads above).
fn asked(work: &mut Work, q: &Formula) -> Result<Option<Model>, Refusal> {
    match work.ask(q) {
        Ok(m) => Ok(m),
        Err(e) if work.used > work.limit => Err(e),
        Err(_) => Ok(None),
    }
}

// The four helpers below are used by the cover (`exact.rs`) as well as here. They are written
// in this module, which `exact.rs` imports, so that this module imports nothing of `exact.rs`
// (row MAIN-red-pugh-land: the two files were an import cycle).

/// The value of `l` at `m`, each atom absent from `m` zero and each product read as an atom of
/// its own, as the solver reads its points.
pub(super) fn value(l: &Lin, m: &Model) -> Int {
    let mut v = l.constant.clone();
    for (a, k) in &l.terms {
        if let Some(x) = m.get(a) {
            v = &v + &(k * x);
        }
    }
    v
}

pub(super) fn fin(v: &Int) -> End {
    End::Fin(Num::from(v))
}

/// The values of `s` that rows over `s` alone allow (each row with no atom holding or not).
pub(super) fn bounded(rows: &[Con], s: &Atom) -> IntervalSet {
    let mut lo: Option<Int> = None;
    let mut hi: Option<Int> = None;
    for k in rows {
        let Some(a) = k.lin.terms.get(s) else {
            if !holds_at(k, &k.lin.constant) {
                return IntervalSet::empty();
            }
            continue;
        };
        let c = &k.lin.constant;
        let (l, u) = match k.rel {
            // `a·s + c >= 0`: `s >= ceil(-c / a)` with `a` above zero, else `s <= floor(c / -a)`.
            Rel::Ge if a.is_positive() => (Some(-&c.div_floor(a)), None),
            Rel::Ge => (None, Some(c.div_floor(&-a))),
            Rel::Eq => {
                if !c.mod_floor(a).is_zero() {
                    return IntervalSet::empty();
                }
                let v = -&c.div_floor(a);
                (Some(v.clone()), Some(v))
            }
        };
        if let Some(l) = l
            && lo.as_ref().is_none_or(|x| &l > x)
        {
            lo = Some(l);
        }
        if let Some(u) = u
            && hi.as_ref().is_none_or(|x| &u < x)
        {
            hi = Some(u);
        }
    }
    if let (Some(l), Some(u)) = (&lo, &hi)
        && l > u
    {
        return IntervalSet::empty();
    }
    IntervalSet::range(
        lo.as_ref().map_or(End::NegInf, fin),
        hi.as_ref().map_or(End::PosInf, fin),
    )
}

/// Whether the constraint `c` holds where its form is `v`.
pub(super) fn holds_at(c: &Con, v: &Int) -> bool {
    match c.rel {
        Rel::Ge => !v.is_negative(),
        Rel::Eq => v.is_zero(),
    }
}

// The tests are files of their own: they name the solver (`presburger.rs`, the steps of
// [`Work`]), which calls this module through `exact.rs`, and test modules kept here would
// make the two import each other (`s_01f_import_graph`, row PRES-cover-wire).
#[cfg(test)]
mod pendants_rows;
#[cfg(test)]
mod tests;
