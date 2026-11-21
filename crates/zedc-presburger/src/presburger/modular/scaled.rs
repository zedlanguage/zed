//! Remainders of a multiple of the variable in a one-variable formula
//! (PRES-one-variable-scaled-and-nested-residues): `(a * x + b) mod m` with `a` not `1` or `-1`.
//! [`solve_modular_whole`] reads a remainder only of `x + c` or `-x + c`; [`solve`] rewrites
//! each literal on such a remainder to a literal on a remainder of `x` itself, which it reads,
//! and hands it the rewritten formula. A remainder of a quotient of `x`, such as
//! `(x div 3) mod 10`, is declined and stays refused: rewritten into residues of `x`, a chain of
//! `n` quotients writes about `n^2` bits (measured ratio 35.1 at 8n), so it needs a method of
//! its own (row PRES-nested-quotient-residues).
//!
//! No source is used: the identity below is elementary and is proved here.
//!
//! Lemma A (a scaled remainder is a remainder of `x`). Let `m >= 1`, `g = gcd(a, m)`,
//! `n = m / g`, `a' = a / g`, and `k = g * c1 + c0` with `0 <= c0 < g`. Then for every integer
//! `t`, `(a t + k) mod m = g * ((a' t + c1) mod n) + c0`.
//! Proof. `a t + k = g (a' t + c1) + c0`. Write `a' t + c1 = n Q + u` with `0 <= u < n`. Then
//! `a t + k = m Q + (g u + c0)` and `0 <= g u + c0 <= g (n - 1) + g - 1 = m - 1`, so by the
//! uniqueness of the Euclidean remainder, `(a t + k) mod m = g u + c0`. QED.
//! So `(a t + k) mod m` lies in `[l, h]` exactly when `u = (a' t + c1) mod n` lies in
//! `[ceil((l - c0) / g), floor((h - c0) / g)]` (as `g > 0`), and since `gcd(a', n) = 1`, the map
//! `t mod n -> (a' t + c1) mod n` is a bijection of `0..n`; the set of `t mod n` it sends into a
//! set `U` is the preimage [`affine_preimage`] computes.
//!
//! Tests: `tests::scaled_remainders_match_enumeration` (random formulas against
//! enumeration over a period or the bounds), `tests::an_affine_preimage_matches_enumeration`,
//! `tests::the_rows_scaled_example_is_decided`,
//! `tests::a_remainder_of_a_quotient_is_still_declined`,
//! and end to end
//! `l01_38_presburger::checker::a_question_over_one_scaled_variable_is_decided`.

use super::*;

#[cfg(test)]
mod tests;

/// A top-level equation read as the definition of a remainder and a quotient:
/// `r = (a * t + k) mod m` and `q = sigma * floor((a * t + k) / m)`, where `t` is the variable or
/// the quotient of another row. A row with no remainder atom (`r` is `None`) says the remainder
/// is zero.
struct DefRow<'f> {
    con: &'f Con,
    a: Int,
    k: Int,
    m: Int,
    q: Atom,
    sigma: i8,
    r: Option<Atom>,
    /// The row whose quotient is `t`, or `None` when `t` is the variable; [`solve`] declines a
    /// formula with any row that has one.
    parent: Option<usize>,
}

/// The bounds `(lo, hi)` the top-level one-term constraints put on each atom; an equation that
/// no integer meets gives an empty range.
fn one_term_bounds(top: &[&Con]) -> HashMap<Atom, (Option<Int>, Option<Int>)> {
    let mut bounds: HashMap<Atom, (Option<Int>, Option<Int>)> = HashMap::new();
    for c in top {
        if c.lin.terms.len() != 1 {
            continue;
        }
        let (a, k) = c.lin.terms.iter().next().expect("one term");
        let e = bounds.entry(a.clone()).or_insert((None, None));
        let c0 = &c.lin.constant;
        match c.rel {
            // `k a + c0 >= 0`: `a >= ceil(-c0 / k)` for `k > 0`, `a <= floor(c0 / -k)` for `k < 0`.
            Rel::Ge if k.is_positive() => e.0 = max_lo(e.0.take(), Some((-c0).div_ceil(k))),
            Rel::Ge => e.1 = min_hi(e.1.take(), Some(c0.div_floor(&-k))),
            Rel::Eq => {
                let (lo, hi) = if c0.mod_floor(&k.abs()).is_zero() {
                    let v = (-c0).div_floor(k);
                    (v.clone(), v)
                } else {
                    (Int::ONE, Int::ZERO)
                };
                e.0 = max_lo(e.0.take(), Some(lo));
                e.1 = min_hi(e.1.take(), Some(hi));
            }
        }
    }
    bounds
}

/// A top-level equation `c_u u + c_v v + c_r r + k0 == 0`, or `c_u u + c_v v + k0 == 0`, that
/// reads as a definition row with `u` or `v` as its quotient; which one is fixed by [`orient`].
struct Shape<'f> {
    con: &'f Con,
    r: Option<Atom>,
    /// `-c_r`, or `1` with no remainder.
    s: Int,
    ends: [(Atom, Int); 2],
    /// Whether `ends[i]` can be the quotient: its coefficient is at least 2 in size and exceeds
    /// the upper bound of the remainder.
    can_q: [bool; 2],
}

/// Reads `c` as a [`Shape`], or `None` when neither end can be a quotient. With three atoms the
/// remainder is the one atom of coefficient `1` or `-1` that the top-level bounds hold in
/// `[0, hi]` with `hi` below the size of another coefficient, or, when several are, the one
/// such `Aux` atom; there must be exactly one. Any such atom gives a true reading (see
/// [`def_row`]); the choice only decides which formulas are read.
fn read_shape<'f>(
    c: &'f Con,
    bounds: &HashMap<Atom, (Option<Int>, Option<Int>)>,
) -> Option<Shape<'f>> {
    if c.rel != Rel::Eq || !(2..=3).contains(&c.lin.terms.len()) {
        return None;
    }
    let terms: Vec<(&Atom, &Int)> = c.lin.terms.iter().collect();
    let upper = |i: usize| -> Option<Int> {
        let (a, k) = terms[i];
        match bounds.get(a) {
            Some((Some(lo), Some(hi)))
                if k.is_unit()
                    && !lo.is_negative()
                    && lo <= hi
                    && (0..terms.len()).any(|j| j != i && terms[j].1.abs() > *hi) =>
            {
                Some(hi.clone())
            }
            _ => None,
        }
    };
    let (r, s, hi) = if terms.len() == 3 {
        let mut found: Vec<(usize, Int)> =
            (0..3).filter_map(|i| upper(i).map(|h| (i, h))).collect();
        if found.len() > 1 {
            // A variable held in a short range (`x == 4` beside `x == 30 q + r + 4`) also reads
            // as a remainder. The checker writes remainders as `Aux` atoms (see [`orient`]),
            // so those are kept.
            found.retain(|(i, _)| matches!(terms[*i].0, Atom::Aux(_)));
        }
        let [(i, hi)] = &found[..] else {
            return None;
        };
        (Some(*i), -terms[*i].1, hi.clone())
    } else {
        (None, Int::ONE, Int::ZERO)
    };
    let mut rest = (0..terms.len()).filter(|&j| Some(j) != r);
    let (u, v) = (
        rest.next().expect("two ends"),
        rest.next().expect("two ends"),
    );
    let end = |j: usize| (terms[j].0.clone(), terms[j].1.clone());
    let fits = |j: usize| {
        let size = terms[j].1.abs();
        size >= Int::from(2) && size > hi
    };
    let can_q = [fits(u), fits(v)];
    if !can_q[0] && !can_q[1] {
        return None;
    }
    Some(Shape {
        con: c,
        r: r.map(|i| terms[i].0.clone()),
        s,
        ends: [end(u), end(v)],
        can_q,
    })
}

/// The definition row of `shape` with `ends[q_end]` as its quotient, which `can_q` allows.
///
/// Proof of the reading. Write the row `c_q q + c_t t + c_r r + k0 == 0` with `c_r = ±1`, and
/// multiply it by `s = -c_r`: `r = A t + C q + K` with `A = s c_t`, `C = s c_q`, `K = s k0`, and
/// `m = |C|`. Every point has `0 <= r <= hi <= m - 1` (the bounds are top-level conjuncts, and
/// `can_q` gives `m > hi`), and `A t + K = r - C q = m (-sgn(C) q) + r`, so by the uniqueness of
/// the Euclidean remainder, `r = (A t + K) mod m` and `-sgn(C) q = floor((A t + K) / m)`, that
/// is, `q = sigma * floor(...)` with `sigma = -sgn(C)`. With two atoms (`c_q q + c_t t + k0 ==
/// 0`), the same reading with `r = 0` gives `A t + K = m (-sgn(C) q)` for `A = c_t`, `K = k0`,
/// `C = c_q`: the remainder is zero and `q = sigma * floor((A t + K) / m)`; conversely, at a
/// point where `(A t + K) mod m = 0`, that `q` meets the row. Nothing here uses which of the two
/// coefficients is larger, so either end that `can_q` allows gives a true reading.
fn def_row<'f>(shape: &Shape<'f>, q_end: usize) -> DefRow<'f> {
    let (q, c_q) = &shape.ends[q_end];
    let (_, c_t) = &shape.ends[1 - q_end];
    let cq = &shape.s * c_q;
    DefRow {
        con: shape.con,
        a: &shape.s * c_t,
        k: &shape.s * &shape.con.lin.constant,
        m: c_q.abs(),
        q: q.clone(),
        sigma: if cq.is_positive() { -1 } else { 1 },
        r: shape.r.clone(),
        parent: None,
    }
}

/// Picks the variable `x`, each row's quotient and each row's parent; `None`
/// when no choice fits.
///
/// The rows are the edges of a graph on the atoms of their ends. Each atom other than `x` must
/// be the quotient of exactly one row and `x` of none, and the parents must have no cycle, so
/// the graph is a tree with one more atom than rows, and once `x` (the root) is chosen, the
/// quotient of each row is its end farther from `x`. The choice is open only in `x`. A root
/// fits when every row's far end can be its quotient (`can_q`); the count of rows that do not
/// fit is found for every root at once, as moving the root from `p` to its child `c` across row
/// `e` changes only `e`'s far end from `c` to `p`. When a constraint other than the rows names
/// an atom of the tree (`named`), that atom must be `x`, as every quotient may occur only in its
/// rows. O(rows) steps.
fn orient<'f>(shapes: &[Shape<'f>], named: Option<&Atom>) -> Option<(Atom, Vec<DefRow<'f>>)> {
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut atoms: Vec<&Atom> = Vec::new();
    let mut adj: Vec<Vec<(usize, usize)>> = Vec::new();
    let mut ends_at = Vec::with_capacity(shapes.len());
    for (e, shape) in shapes.iter().enumerate() {
        let mut at = [0usize; 2];
        for (side, (a, _)) in shape.ends.iter().enumerate() {
            at[side] = *index.entry(a).or_insert_with(|| {
                atoms.push(a);
                adj.push(Vec::new());
                atoms.len() - 1
            });
        }
        adj[at[0]].push((e, at[1]));
        adj[at[1]].push((e, at[0]));
        ends_at.push(at);
    }
    if atoms.len() != shapes.len() + 1 {
        return None;
    }
    // Breadth first from `root`: the row to each atom's parent, and the atoms in the order met.
    let walk = |root: usize| -> Option<(Vec<Option<usize>>, Vec<usize>)> {
        let mut up: Vec<Option<usize>> = vec![None; atoms.len()];
        let mut seen = vec![false; atoms.len()];
        let mut met = vec![root];
        seen[root] = true;
        let mut next = 0;
        while next < met.len() {
            let p = met[next];
            next += 1;
            for &(e, c) in &adj[p] {
                if !seen[c] {
                    seen[c] = true;
                    up[c] = Some(e);
                    met.push(c);
                }
            }
        }
        (met.len() == atoms.len()).then_some((up, met))
    };
    // With `atoms = rows + 1`, connected means a tree.
    let (up, met) = walk(0)?;
    let misfit = |e: usize, far: usize| {
        let side = if ends_at[e][0] == far { 0 } else { 1 };
        u32::from(!shapes[e].can_q[side])
    };
    let mut bad = vec![0u32; atoms.len()];
    bad[0] = (0..atoms.len())
        .filter_map(|c| up[c].map(|e| misfit(e, c)))
        .sum();
    for &c in &met[1..] {
        let e = up[c].expect("every atom but the root has a parent row");
        let p = if ends_at[e][0] == c {
            ends_at[e][1]
        } else {
            ends_at[e][0]
        };
        bad[c] = bad[p] - misfit(e, c) + misfit(e, p);
    }
    let fits = |i: usize| bad[i] == 0 && !matches!(atoms[i], Atom::Product(..));
    // Any root that fits gives true readings, but [`solve_modular_whole`] declines some
    // rewrites on a root that is a quotient (seed 3840964118206103216 case 255 of
    // `scaled_and_nested_remainders_match_enumeration`). The checker writes every quotient and
    // remainder as an `Aux` atom (zedc-preimage `Normal::parts`: the remainder `Aux(n)` of a
    // `mod` has its quotient at `Aux(n - 1)`), so a root that fits and is not `Aux` is the
    // checker's variable and is taken first.
    let root = match named {
        Some(a) => index.get(a).copied().filter(|&i| fits(i))?,
        None => (0..atoms.len())
            .filter(|&i| fits(i))
            .min_by_key(|&i| matches!(atoms[i], Atom::Aux(_)))?,
    };
    // Row `e` of the result is the reading of `shapes[e]`, so the indices of `shapes` stay valid;
    let (up, met) = walk(root).expect("connected");
    let mut rows: Vec<Option<DefRow<'f>>> = (0..shapes.len()).map(|_| None).collect();
    for &c in &met[1..] {
        let e = up[c].expect("every atom but the root has a parent row");
        let q_end = if ends_at[e][0] == c { 0 } else { 1 };
        let mut row = def_row(&shapes[e], q_end);
        row.parent = up[ends_at[e][1 - q_end]];
        rows[e] = Some(row);
    }
    let rows = rows
        .into_iter()
        .map(|row| row.expect("a tree reaches every row"))
        .collect();
    Some((atoms[root].clone(), rows))
}

/// The residues `t mod n`, with `n = m / gcd(a, m)`, at which `(a t + k) mod m` lies in `v`
/// (a residue set modulo `m`), by Lemma A; `None` when that set would take more than
/// [`SWEEP_SWITCHOVER`] steps to write.
///
/// After Lemma A the task is the preimage of a set `U` modulo `n` under `t -> (a' t + c1) mod n`
/// with `gcd(a', n) = 1`. For `a' = 1` or `-1` an interval maps to an interval, shifted or
/// reflected ([`shift_residue_interval`]). Otherwise let `b` be `a' mod n` or `n - (a' mod n)`,
/// whichever is at most `n / 2`; for the second, `(a' t + c1) mod n = (b t' + c1) mod n` with
/// `t' = (-t) mod n`, so the preimage in `t'` is computed and reflected. Each interval `[l, h]`
/// of `U` is written in the cheaper of two ways:
/// - points: `t' = b^-1 (u - c1) mod n` for each `u` in `[l, h]`, `h - l + 1` steps;
/// - windows: `t'` in `0..n` gives `b t' + c1` in `[0, (b + 1) n)` (as `c1 < n`), so
///   `(b t' + c1) mod n` lies in `[l, h]` exactly when, for some `j` in `0..=b`,
///   `j n + l <= b t' + c1 <= j n + h`, that is,
///   `t'` in `[ceil((j n + l - c1) / b), floor((j n + h - c1) / b)]`, clipped to `0..n`;
///   `b + 1` steps.
///
/// As the map is a bijection modulo `n`, the preimage of the complement of `U` is the
/// complement of the preimage of `U`, so the side of fewer steps is computed.
// Complexity tradeoff: the preimage of one interval under multiplication by `b` modulo `n`
// has up to `min(b, h - l + 1)` runs, which no form of intervals avoids; with both `b` and the
// interval near `sqrt(n)`, that is about `sqrt(n)` runs. Naive, enumerate all `n` residues:
// O(n) for every literal. Used: O(min(b + 1, h - l + 1)) per interval, on the side (the set or
// its complement) of fewer steps, so O(1) per interval for `a' = ±1` and a small `b`, constant
// in `m` for a fixed coefficient, and O(m) in the costly case `b` near `m / 3`, where the runs
// themselves number about `m / 3` (bench `scaled_remainders_scale_in_the_modulus`). What
// is given up: a literal that needs more than SWEEP_SWITCHOVER (400,000, the measured point at
// which this module stops writing residue lists, at its definition) steps is not rewritten and
// is refused as before. Such a set has that many runs, so any interval form of it is that large.
fn affine_preimage(a: &Int, k: &Int, m: &Int, v: &[(Int, Int)]) -> Option<(Int, ResidueSet)> {
    let g = a.gcd(m);
    let n = m.div_floor(&g);
    let c1 = k.div_floor(&g);
    let c0 = k - &(&g * &c1);
    let u: Vec<(Int, Int)> = v
        .iter()
        .map(|(l, h)| ((l - &c0).div_ceil(&g), (h - &c0).div_floor(&g)))
        .collect();
    let u = res_normalize(u, &n);
    if n == Int::ONE {
        return Some((n, u));
    }
    let a1 = a.div_floor(&g).mod_floor(&n);
    let c1 = c1.mod_floor(&n);
    let n_less = &n - &Int::ONE;
    if a1 == Int::ONE || a1 == n_less {
        let s_x: i8 = if a1 == Int::ONE { 1 } else { -1 };
        let parts = (u.iter())
            .flat_map(|(l, h)| shift_residue_interval(l, h, s_x, &c1, &n))
            .collect();
        return Some((n.clone(), res_normalize(parts, &n)));
    }
    let (b, reflect) = if &a1 + &a1 <= n {
        (a1, false)
    } else {
        (&n - &a1, true)
    };
    let windows = &b + &Int::ONE;
    let steps = |s: &[(Int, Int)]| -> Int {
        let mut total = Int::ZERO;
        for (l, h) in s {
            let points = &(h - l) + &Int::ONE;
            total = &total + &points.min(windows.clone());
        }
        total
    };
    let complement = res_complement(&u, &n);
    let (src, flip) = if steps(&complement) < steps(&u) {
        (complement, true)
    } else {
        (u, false)
    };
    if steps(&src) > Int::from(SWEEP_SWITCHOVER as usize) {
        return None;
    }
    let inv = inverse_mod(&b, &n)?;
    let mut parts = Vec::new();
    for (l, h) in &src {
        if &(h - l) + &Int::ONE <= windows {
            let mut w = l.clone();
            while w <= *h {
                let t = (&inv * &(&w - &c1)).mod_floor(&n);
                parts.push((t.clone(), t));
                w = &w + &Int::ONE;
            }
        } else {
            let mut j = Int::ZERO;
            while j <= b {
                let base = &(&j * &n) - &c1;
                let lo = (&base + l).div_ceil(&b);
                let hi = (&base + h).div_floor(&b);
                if lo <= hi {
                    parts.push((lo, hi));
                }
                j = &j + &Int::ONE;
            }
        }
    }
    let mut t = res_normalize(parts, &n);
    if reflect {
        t = reflect_residues(&t, &n);
    }
    if flip {
        t = res_complement(&t, &n);
    }
    Some((n, t))
}

/// `{(n - v) mod n : v in s}`: an interval `[l, h]` with `l >= 1` goes to `[n - h, n - l]`, and
/// `0` to itself.
fn reflect_residues(s: &[(Int, Int)], n: &Int) -> ResidueSet {
    let mut out = Vec::with_capacity(s.len() + 1);
    for (l, h) in s {
        if l.is_zero() {
            out.push((Int::ZERO, Int::ZERO));
            if h.is_positive() {
                out.push((n - h, n - &Int::ONE));
            }
        } else {
            out.push((n - h, n - l));
        }
    }
    res_normalize(out, n)
}

/// The residues of the variable, `(n, T)` meaning `x mod n` in `T`, at which the remainder of
/// row `i` (a row on `x`) lies in `v`, a residue set modulo the row's `m`: Lemma A.
fn pull_back(rows: &[DefRow<'_>], i: usize, v: ResidueSet) -> Option<(Int, ResidueSet)> {
    affine_preimage(&rows[i].a, &rows[i].k, &rows[i].m, &v)
}

/// The interval of values in `0..m` at which the one-term constraint `c` on a remainder holds.
fn remainder_values(c: &Con, m: &Int) -> ResidueSet {
    let (_, k) = c.lin.terms.iter().next().expect("one term");
    let c0 = &c.lin.constant;
    let (lo, hi) = match c.rel {
        Rel::Ge if k.is_positive() => ((-c0).div_ceil(k), m - &Int::ONE),
        Rel::Ge => (Int::ZERO, c0.div_floor(&-k)),
        Rel::Eq if c0.mod_floor(&k.abs()).is_zero() => {
            let v = (-c0).div_floor(k);
            (v.clone(), v)
        }
        Rel::Eq => return Vec::new(),
    };
    res_normalize(vec![(lo, hi)], m)
}

/// [`solve_modular`]'s answer to `f`, or, when it declines, [`solve`]'s. [`solve`] runs only
/// when [`solve_modular`] declines, so every formula that one accepts is answered as before.
/// The fallback is written here, not in [`solve_modular`], so that `modular.rs` names nothing
/// of this file and the two files form no import cycle (test `s_01f_import_graph`).
pub(crate) fn solve_modular_or_scaled(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    solve_modular(f, want_model).or_else(|| solve(f, want_model))
}

/// A point of `f` found by [`solve_modular_or_scaled`], or `None` when `f` has no point or lies
/// outside its scope. Because [`solve_modular`] chooses `x_root` from the name- and
/// order-independent candidate intersection (size at most 2) and tries every candidate, whether
/// it finds a point does not depend on atom names or row order. Not proved for [`solve`], which
/// runs only where [`solve_modular`] declines: where several atoms fit as its root it takes the
/// first by kind and then by index, and [`solve_modular_whole`] may decline the rewrite on one
/// root and accept it on another, so there whether a point is found may depend on the order of
/// the atoms.
pub(crate) fn point_by_structure(f: &Formula) -> Option<Model> {
    solve_modular_or_scaled(f, true).flatten()
}

/// Decides `f` as [`solve_modular_whole`] does, after rewriting each literal on a remainder of
/// a multiple of the variable to a literal on a remainder of the variable; `None` when `f` does
/// not have that shape.
///
/// Shape. The top-level conjuncts hold definition rows ([`read_shape`], [`orient`],
/// [`def_row`]); each quotient and remainder is defined by one row; the dividend `t` of every
/// row is one variable `x` (defined by no row); a quotient occurs in no other constraint; a
/// remainder occurs only in one-term constraints; every other constraint names at most `x`.
///
/// Rewrite. Each definition row becomes `true`; each one-term constraint on a remainder becomes
/// the residues of `x` [`pull_back`] gives, written on a new remainder `s_n` of `x` for each
/// modulus `n` (`x == n p_n + s_n`, `0 <= s_n <= n - 1`, top level); a row with no remainder adds
/// the literal that its remainder is zero; constraints on `x` alone stay.
///
/// Proof that `f` has a point exactly when the rewritten formula has one, with the same `x`.
/// (1) Given a point of `f`: by [`def_row`] each remainder and quotient is the value its row
/// defines from `x`, so by Lemmas A and B each rewritten literal has the truth value of the
/// literal it replaces, with `p_n = floor(x / n)`, `s_n = x mod n`; a definition row is
/// `true` in both, and a zero remainder holds. (2) Given a point of the rewritten formula: its
/// rows force `s_n = x mod n`. Set each quotient and remainder to the value its row defines from
/// `x`: each row then holds (a three-term row by construction, a two-term row as
/// its remainder is zero), and again each literal has the truth value of the literal it replaces,
/// so `f` holds. The Boolean structure is unchanged (`Formula::map_cons`), so the equivalence of
/// each replaced constraint at the points of (1) and (2) carries to `f`. QED.
/// A point found is rebuilt from `x` as in (2) and checked with [`Formula::holds`].
// Complexity tradeoff: each literal on a remainder is one [`affine_preimage`], whose cost is
// given there; O(1) further steps per constraint. Declined, and refused as before: any row whose
// dividend is the quotient of another row. Rewritten into residues of `x` by
// `floor(floor(y / d) / m) = floor(y / (d m))` and `floor(W / d) mod m = floor((W mod (d m)) /
// d)`, a literal on level `i` of a chain of quotients by `d` becomes a residue set of `x` modulo
// `d^(i+1)`, about `i log2(d)` bits, so `n` levels with a literal each write about
// `n^2 log2(d) / 2` bits from an input of about `n`. Measured on branch wt/presres1 (commit
// 5634afcbb, 2026-11-21, load 88): ratio 35.1 at 8n, over the limit of 10.5; the printed
// rewrite grew 48.6 times (35,215 to 1,712,893 characters at depth 200 and 1,600). Chains need
// a method that does not go through residues of `x` (row PRES-nested-quotient-residues).
pub(super) fn solve(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    let mut top: Vec<&Con> = Vec::new();
    let mut clauses: Vec<&Formula> = Vec::new();
    for g in f.conjunct_list().iter() {
        match g {
            Formula::Con(c) => top.push(c),
            _ => clauses.push(g),
        }
    }
    let bounds = one_term_bounds(&top);
    let shapes: Vec<Shape<'_>> = top.iter().filter_map(|c| read_shape(c, &bounds)).collect();
    if shapes.is_empty() {
        return None;
    }
    let mut r_of: HashMap<Atom, usize> = HashMap::new();
    for (i, shape) in shapes.iter().enumerate() {
        if let Some(r) = &shape.r
            && r_of.insert(r.clone(), i).is_some()
        {
            return None;
        }
    }
    let ends: HashSet<&Atom> = shapes
        .iter()
        .flat_map(|s| s.ends.iter().map(|(a, _)| a))
        .collect();
    if ends.iter().any(|a| r_of.contains_key(*a)) {
        return None;
    }
    // The atoms of the tree that a constraint other than a row names; at most one may be `x`.
    let shape_cons: HashSet<&Con> = shapes.iter().map(|s| s.con).collect();
    let mut named: Option<&Atom> = None;
    let mut two_named = false;
    f.walk(&mut |c| {
        if shape_cons.contains(c) {
            return;
        }
        for a in c.lin.terms.keys() {
            if let Some(&e) = ends.get(a) {
                match named {
                    None => named = Some(e),
                    Some(n) => two_named |= n != e,
                }
            }
        }
    });
    if two_named {
        return None;
    }
    let (x, rows) = orient(&shapes, named)?;
    // A row on the quotient of another row: a chain, declined (see the tradeoff above).
    if rows.iter().any(|row| row.parent.is_some()) {
        return None;
    }

    // Every constraint: a definition row (top level only), a one-term constraint on a remainder,
    // or one on `x` alone.
    let def_cons: HashSet<&Con> = rows.iter().map(|row| row.con).collect();
    let allowed = |c: &Con, at_top: bool| -> bool {
        if at_top && def_cons.contains(c) {
            return true;
        }
        if c.lin.terms.len() == 1 {
            let a = c.lin.terms.keys().next().expect("one term");
            return *a == x || r_of.contains_key(a);
        }
        c.lin.terms.keys().all(|a| *a == x)
    };
    if !top.iter().all(|c| allowed(c, true)) {
        return None;
    }
    let mut nested_ok = true;
    for g in &clauses {
        g.walk(&mut |c| nested_ok &= allowed(c, false));
    }
    if !nested_ok {
        return None;
    }
    // A top-level bound that fixes `x` to `v`: every point of `f` has `x = v`, and its rows then
    // fix every quotient and remainder ([`def_row`]), so `f` has a point exactly when
    // [`point_at`] `v` is one. One evaluation of `f`; [`solve_modular_whole`] declines the
    // rewritten formula here, as its step 1 takes `x` out of the rows of the new remainders.
    if let Some((Some(lo), Some(hi))) = bounds.get(&x)
        && lo == hi
    {
        let model = point_at(&rows, &x, lo);
        return Some(
            f.holds(&model)
                .then(|| if want_model { model } else { Model::new() }),
        );
    }

    // The new remainders of `x`, one per modulus, numbered past every auxiliary atom of `f`.
    let mut next_aux = 0u32;
    f.walk(&mut |c| next_aux = next_aux.max(c.lin.aux_end()));
    let mut fresh: BTreeMap<Int, (Atom, Atom)> = BTreeMap::new();
    let mut residue_literal = |n: Int, t: ResidueSet| -> Formula {
        if t.is_empty() {
            return Formula::bottom();
        }
        if res_is_full(&t, &n) {
            return Formula::top();
        }
        let len = fresh.len() as u32;
        let (_, s) = fresh.entry(n.clone()).or_insert_with(|| {
            (
                Atom::Aux(next_aux + 2 * len),
                Atom::Aux(next_aux + 2 * len + 1),
            )
        });
        let s = Lin::atom(s.clone());
        let top_res = &n - &Int::ONE;
        let pieces = (t.into_iter())
            .map(|(l, h)| {
                let mut both = Vec::new();
                if l.is_positive() {
                    both.push(Formula::Con(Con::ge(&s, &Lin::constant(l))));
                }
                if h < top_res {
                    both.push(Formula::Con(Con::ge(&Lin::constant(h), &s)));
                }
                Formula::and(both)
            })
            .collect();
        Formula::or(pieces)
    };
    let mut replaced: HashMap<Con, Formula> = HashMap::new();
    let mut failed = false;
    let mut replace = |c: &Con| {
        if failed || replaced.contains_key(c) || def_cons.contains(c) || c.lin.terms.len() != 1 {
            return;
        }
        let a = c.lin.terms.keys().next().expect("one term");
        let Some(&i) = r_of.get(a) else {
            return;
        };
        match pull_back(&rows, i, remainder_values(c, &rows[i].m)) {
            Some((n, t)) => {
                replaced.insert(c.clone(), residue_literal(n, t));
            }
            None => failed = true,
        }
    };
    f.walk(&mut replace);
    let mut zero_remainders = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        if row.r.is_none() {
            let (n, t) = pull_back(&rows, i, vec![(Int::ZERO, Int::ZERO)])?;
            zero_remainders.push(residue_literal(n, t));
        }
    }
    if failed {
        return None;
    }
    let body = f.map_cons(&|c| {
        if def_cons.contains(c) {
            Formula::top()
        } else if let Some(g) = replaced.get(c) {
            g.clone()
        } else {
            Formula::Con(c.clone())
        }
    });
    let xl = Lin::atom(x.clone());
    let mut parts = vec![body];
    parts.extend(zero_remainders);
    if fresh.is_empty() {
        // Every literal on a remainder was always or never true, so what is left reads `x`
        // alone, which [`solve_modular_whole`] declines (it needs a coefficient other than
        // `1` or `-1`). The remainder of `x` by 2, with no literal on it, is such a row: every
        // `x` meets it with one `p` and one `s`, so for each `x` the formula has a point
        // exactly when it had one before.
        fresh.insert(Int::from(2), (Atom::Aux(next_aux), Atom::Aux(next_aux + 1)));
    }
    for (n, (p, s)) in &fresh {
        let s = Lin::atom(s.clone());
        parts.push(Formula::Con(Con::eq(
            &xl,
            &Lin::atom(p.clone()).times(n.clone()).plus(&s),
        )));
        parts.push(Formula::Con(Con::ge(&s, &Lin::constant(0))));
        parts.push(Formula::Con(Con::ge(&Lin::constant(n - &Int::ONE), &s)));
    }
    let rewritten = Formula::and(parts);
    let found = solve_modular_whole(&rewritten, want_model)?;
    let Some(point) = found else {
        return Some(None);
    };
    if !want_model {
        return Some(Some(Model::new()));
    }
    let x_value = point.get(&x).cloned().unwrap_or(Int::ZERO);
    let model = point_at(&rows, &x, &x_value);
    // By (2) of the proof this is a point of `f`; a failure here is a defect of this module,
    // and declining leaves `f` to the general path.
    let holds = f.holds(&model);
    debug_assert!(
        holds,
        "the point rebuilt from x = {x_value} is not one of\n{f}"
    );
    holds.then_some(Some(model))
}

/// The values at `x = v` of `x` and of each quotient and remainder its row (a row on `x`)
/// defines, as in (2) of the proof of [`solve`]: `E = a x + k`, `r = E mod m`,
/// `q = sigma * floor(E / m)`. O(rows) arithmetic operations.
fn point_at(rows: &[DefRow<'_>], x: &Atom, v: &Int) -> Model {
    let mut model = Model::new();
    model.insert(x.clone(), v.clone());
    for row in rows {
        let e = &(&row.a * v) + &row.k;
        let fl = e.div_floor(&row.m);
        if let Some(r) = &row.r {
            model.insert(r.clone(), &e - &(&row.m * &fl));
        }
        let q = if row.sigma > 0 { fl } else { -&fl };
        model.insert(row.q.clone(), q);
    }
    model
}
