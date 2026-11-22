//! Remainders of a multiple of the variable in a one-variable formula
//! (PRES-one-variable-scaled-and-nested-residues): `(a * x + b) mod m` with `a` not `1` or `-1`.
//! [`solve_modular_whole`] reads a remainder only of `x + c` or `-x + c`; [`solve`] rewrites
//! each literal on such a remainder to a literal on a remainder of `x` itself, which it reads,
//! and hands it the rewritten formula. A remainder of a quotient of `x`, such as
//! `(x div 3) mod 10`, is declined and stays refused: rewritten into residues of `x`, a chain of
//! `n` quotients writes about `n^2` bits (measured ratio 35.1 at 8n), so it needs a method of
//! its own (row PRES-nested-quotient-residues). A remainder of a sum of rows' parts, such as
//! `(x div 3 + x div 5) mod 7`, is read as a [`SumRow`] and rewritten into residues of `x`
//! modulo its period (row PRES-one-variable-sum-of-quotients, [`sum_residues`]).
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
//! `tests::sums_of_quotients_match_enumeration`, `tests::the_rows_sum_example_is_decided`,
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

/// A part of a [`SumRow`]: the variable, or the quotient or the remainder of row `i`.
#[derive(Clone, Copy)]
enum Part {
    X,
    Q(usize),
    R(usize),
}

/// A top-level equation `sum_j c_j p_j + c_q q + c_r r + k0 == 0` (or with no `r`) whose parts
/// `p_j` are the variable and quotients and remainders of rows on it, read as
/// `r = E mod m` and `q = sigma * floor(E / m)` with `E = s (sum_j c_j p_j + k0)`, `s = -c_r`
/// (`1` with no remainder, which then says `E mod m = 0`), `m = |c_q|` and
/// `sigma = -sgn(s c_q)`. The proof is that of [`def_row`] with `A t` replaced by
/// `s sum_j c_j p_j`, which nothing in it reads beyond being an integer at each point.
/// `parts` holds `s c_j`, `k` holds `s k0`.
struct SumRow {
    parts: Vec<(Part, Int)>,
    k: Int,
    m: Int,
    q: Atom,
    sigma: i8,
    r: Option<Atom>,
}

/// Reads `c` as a [`SumRow`] over the rows `rows` on `x`, or `None`. Every atom of `c` other than
/// one quotient atom and at most one remainder atom must be `x`, a row's quotient (`q_row`) or a
/// row's remainder (`r_of`), and at least one must be; the remainder is the one other atom of
/// coefficient `1` or `-1` that the top-level bounds hold in `[0, hi]` with `hi` below the size
/// of the quotient's coefficient, and the quotient's coefficient is at least 2 in size.
fn read_sum(
    c: &Con,
    x: &Atom,
    q_row: &HashMap<&Atom, usize>,
    r_of: &HashMap<Atom, usize>,
    bounds: &HashMap<Atom, (Option<Int>, Option<Int>)>,
) -> Option<SumRow> {
    if c.rel != Rel::Eq {
        return None;
    }
    let mut parts: Vec<(Part, Int)> = Vec::new();
    let mut rest: Vec<(&Atom, &Int)> = Vec::new();
    for (a, k) in &c.lin.terms {
        let part = if a == x {
            Some(Part::X)
        } else if let Some(&i) = q_row.get(a) {
            Some(Part::Q(i))
        } else {
            r_of.get(a).map(|&i| Part::R(i))
        };
        match part {
            Some(p) => parts.push((p, k.clone())),
            None => rest.push((a, k)),
        }
    }
    if parts.is_empty() {
        return None;
    }
    let below = |r: usize, q: usize| -> bool {
        let (a, k) = rest[r];
        matches!(bounds.get(a), Some((Some(lo), Some(hi)))
            if k.is_unit() && !lo.is_negative() && lo <= hi && *hi < rest[q].1.abs())
    };
    let (q, r) = match rest.len() {
        1 => (0, None),
        2 => match (below(0, 1), below(1, 0)) {
            (true, false) => (1, Some(0)),
            (false, true) => (0, Some(1)),
            _ => return None,
        },
        _ => return None,
    };
    let (q_atom, c_q) = rest[q];
    let m = c_q.abs();
    // With no remainder a quotient of coefficient 1 in size is read too, as in [`read_shape`]:
    // the row is then of modulus 1 (`E mod 1 = 0` at every point, `q = sigma E`), which is how a
    // sum whose remainder is always zero is written once divided by its gcd: `3 q0 + 3 q4 ==
    // 3 q2 + 3 q3 - 6` is `q0 + q4 - q2 - q3 == -2` (PRES-sum-of-quotients-shadows-random, seed
    // 3700079103403926633 case 92). Without it `q4` was no row's quotient, `solve` declined, and
    // the general path refused with `Shadows`.
    if m < Int::from(2) && r.is_some() {
        return None;
    }
    let s = r.map_or(Int::ONE, |i| -rest[i].1);
    let cq = &s * c_q;
    Some(SumRow {
        parts: parts.into_iter().map(|(p, k)| (p, &s * &k)).collect(),
        k: &s * &c.lin.constant,
        m,
        q: q_atom.clone(),
        sigma: if cq.is_positive() { -1 } else { 1 },
        r: r.map(|i| rest[i].0.clone()),
    })
}

/// `E` of `sum` at the values `model` of the rows' parts (from [`point_at`]); `x` is the
/// variable's value. O(parts) arithmetic operations.
fn sum_value(sum: &SumRow, rows: &[DefRow<'_>], model: &Model, x: &Int) -> Int {
    let mut e = sum.k.clone();
    for (p, k) in &sum.parts {
        let v = match p {
            Part::X => x,
            Part::Q(i) => &model[&rows[*i].q],
            Part::R(i) => &model[rows[*i].r.as_ref().expect("a remainder part has its atom")],
        };
        e = &e + &(k * v);
    }
    e
}

/// The residues of `x` at which the remainder `E mod m` of `sum` lies in `u` (a residue set
/// modulo `m`), as `(n, T)`: `x mod n` in `T`.
///
/// Proof. Let `L` be the least common multiple of the moduli `m_i` of the rows `sum` reads, and
/// `alpha = sum_j c_j d_j` with `d_j = L` for `x`, `sigma_i a_i L / m_i` for the quotient of row
/// `i` and `0` for its remainder. For every `x` and integer `j`, `E(x + j L) = E(x) + j alpha`:
/// `x` grows by `j L`; the dividend `a_i x + k_i` of row `i` grows by `a_i j L`, a multiple of
/// `m_i`, so its floor quotient grows by exactly `a_i j L / m_i` and its remainder is unchanged.
/// So `E mod m` has period `n = m L` (`E(x + m L) = E(x) + m alpha`), and for `x = c + j L` with
/// `0 <= c < L`, `0 <= j < m`, `E(x) mod m = (E(c) + j alpha) mod m`. QED.
// Complexity tradeoff: naive version, none (the general path refused these formulas with the
// shadows reason). Used: `E(c)` for each `c < L` (O(L * parts) operations), then one addition
// and one reduction modulo `m` for each of the `n = m L` residues, O(n + L * parts) in all, and
// the residue set written has at most `n / 2 + 1` runs, so the work is within a constant of the
// largest output. `n` is the product of the moduli the sum reads (for coprime moduli), so a sum
// over `k` coprime moduli costs their product, exponential in `k`: such a set of residues can
// need that many runs, and a method that does not write residues of `x` is row
// PRES-sum-of-quotients-period-product. Tests: `tests::sums_of_quotients_match_enumeration`;
// benchmark `bench::sums_of_quotients_scale` (`x div 3 + x div 5` modulo `m`, ratio 7.66 at
// 8m when written). COMPLEXITY.md row
// PRES-one-variable-sum-of-quotients.
/// `None` when `L` or `m` does not fit a machine word: the loop below runs `m L` steps, which
/// cannot finish at such sizes, so this is the limit of what can be written, not a threshold.
fn sum_residues(
    sum: &SumRow,
    rows: &[DefRow<'_>],
    x: &Atom,
    u: &ResidueSet,
) -> Option<(Int, ResidueSet)> {
    let mut l = Int::ONE;
    let mut alpha = Int::ZERO;
    for (p, _) in &sum.parts {
        if let Part::Q(i) | Part::R(i) = p {
            l = l.lcm(&rows[*i].m);
        }
    }
    for (p, k) in &sum.parts {
        let d = match p {
            Part::X => l.clone(),
            Part::Q(i) => {
                let row = &rows[*i];
                // Exact: `m_i` divides `L`.
                let step = (&row.a * &l).div_floor(&row.m);
                if row.sigma > 0 { step } else { -&step }
            }
            Part::R(_) => Int::ZERO,
        };
        alpha = &alpha + &(k * &d);
    }
    let m = &sum.m;
    let n = m * &l;
    let alpha = alpha.mod_floor(m);
    let (l_n, m_n) = (
        u64::try_from(l.to_i128()?).ok()?,
        u64::try_from(m.to_i128()?).ok()?,
    );
    let mut start: Vec<Int> = Vec::new();
    let mut c = Int::ZERO;
    for _ in 0..l_n {
        start.push(sum_value(sum, rows, &point_at(rows, x, &c), &c).mod_floor(m));
        c = &c + &Int::ONE;
    }
    let inside = |v: &Int| u.iter().any(|(lo, hi)| lo <= v && v <= hi);
    let mut out: ResidueSet = Vec::new();
    let mut run: Option<Int> = None;
    let mut t = Int::ZERO;
    let mut shift = Int::ZERO;
    for _ in 0..m_n {
        for e in &start {
            let mut v = e + &shift;
            if &v >= m {
                v = &v - m;
            }
            match (inside(&v), &run) {
                (true, None) => run = Some(t.clone()),
                (false, Some(lo)) => {
                    out.push((lo.clone(), &t - &Int::ONE));
                    run = None;
                }
                _ => {}
            }
            t = &t + &Int::ONE;
        }
        shift = &shift + &alpha;
        if &shift >= m {
            shift = &shift - m;
        }
    }
    if let Some(lo) = run {
        out.push((lo, &n - &Int::ONE));
    }
    let set = res_normalize(out, &n);
    Some((n, set))
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
    // With no remainder an end of coefficient 1 in size fits too: the row is then of modulus 1,
    // its quotient linear in the other end (`q = sigma (A t + K)`, [`def_row`] with `m = 1`).
    // That is how a remainder that is always zero is written once the row is divided by its
    // gcd: `(-5 x - 5) mod 5 == 0` is `x + q == -1` (PRES-sum-of-quotients-period-product,
    // part 2). Without it the quotient was no row's, so `solve` declined the formula and the
    // general path refused a sum beside it with `Shadows`.
    let fits = |j: usize| {
        let size = terms[j].1.abs();
        (size >= Int::from(2) || r.is_none()) && size > hi
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
    // Before that, a root on every row is taken: with it no row has a parent, and [`solve`]
    // declines every reading in which one does (a chain), so a root that leaves a chain is
    // never better. The general path renames atoms to `Sym`s before it asks again, and then the
    // `Aux` test cannot tell the variable from a quotient: in seed 12744803785466090665 case 189
    // of `sums_of_quotients_match_enumeration` (PRES-sum-of-quotients-shadows-random), `4 y + r
    // == 5 x + 11` with `r` in `[0, 3]` reads either way, the root `y` left the other row (on
    // `x`) a chain, and the formula was refused with `Shadows`. O(1) a candidate (the degree).
    let root = match named {
        Some(a) => index.get(a).copied().filter(|&i| fits(i))?,
        None => (0..atoms.len())
            .filter(|&i| fits(i))
            .min_by_key(|&i| {
                (
                    adj[i].len() != shapes.len(),
                    matches!(atoms[i], Atom::Aux(_)),
                )
            })?,
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
    // The top-level equations of three or more terms over the rows' parts: each must read as a
    // [`SumRow`] once `x` is known, or the formula is declined (as it was before
    // PRES-one-variable-sum-of-quotients, so no earlier answer changes).
    // In the order of `top`, so the fresh atoms are numbered the same on every run.
    let sum_list: Vec<&Con> = top
        .iter()
        .copied()
        .filter(|c| {
            c.rel == Rel::Eq
                && c.lin.terms.len() >= 3
                && !shape_cons.contains(c)
                && c.lin
                    .terms
                    .keys()
                    .any(|a| ends.contains(a) || r_of.contains_key(a))
        })
        .collect();
    let sum_cons: HashSet<&Con> = sum_list.iter().copied().collect();
    let mut named: Option<&Atom> = None;
    let mut two_named = false;
    f.walk(&mut |c| {
        if shape_cons.contains(c) || sum_cons.contains(c) {
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
    let q_row: HashMap<&Atom, usize> = rows
        .iter()
        .enumerate()
        .map(|(i, row)| (&row.q, i))
        .collect();
    let mut sums: Vec<SumRow> = Vec::new();
    for c in &sum_list {
        sums.push(read_sum(c, &x, &q_row, &r_of, &bounds)?);
    }
    // Each sum's quotient and remainder are its own: no other sum names them.
    let mut sum_r: HashMap<Atom, usize> = HashMap::new();
    let mut sum_atoms: HashSet<&Atom> = HashSet::new();
    for (j, sum) in sums.iter().enumerate() {
        if !sum_atoms.insert(&sum.q) {
            return None;
        }
        if let Some(r) = &sum.r {
            if !sum_atoms.insert(r) {
                return None;
            }
            sum_r.insert(r.clone(), j);
        }
    }
    let def_cons: HashSet<&Con> = rows.iter().map(|row| row.con).collect();
    let allowed = |c: &Con, at_top: bool| -> bool {
        if at_top && (def_cons.contains(c) || sum_cons.contains(c)) {
            return true;
        }
        if c.lin.terms.len() == 1 {
            let a = c.lin.terms.keys().next().expect("one term");
            return *a == x || r_of.contains_key(a) || sum_r.contains_key(a);
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
        let model = point_with_sums(&rows, &sums, &x, lo);
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
        let found = if let Some(&i) = r_of.get(a) {
            pull_back(&rows, i, remainder_values(c, &rows[i].m))
        } else if let Some(&j) = sum_r.get(a) {
            sum_residues(&sums[j], &rows, &x, &remainder_values(c, &sums[j].m))
        } else {
            return;
        };
        match found {
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
    // A sum with no remainder says `E mod m = 0` ([`SumRow`]).
    for sum in sums.iter().filter(|sum| sum.r.is_none()) {
        let (n, t) = sum_residues(sum, &rows, &x, &vec![(Int::ZERO, Int::ZERO)])?;
        zero_remainders.push(residue_literal(n, t));
    }
    if failed {
        return None;
    }
    let body = f.map_cons(&|c| {
        if def_cons.contains(c) || sum_cons.contains(c) {
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
    let model = point_with_sums(&rows, &sums, &x, &x_value);
    // By (2) of the proof this is a point of `f`; a failure here is a defect of this module,
    // and declining leaves `f` to the general path.
    let holds = f.holds(&model);
    debug_assert!(
        holds,
        "the point rebuilt from x = {x_value} is not one of\n{f}"
    );
    holds.then_some(Some(model))
}

/// [`point_at`], and the quotient and remainder of each sum at `x = v` as [`SumRow`] reads them.
fn point_with_sums(rows: &[DefRow<'_>], sums: &[SumRow], x: &Atom, v: &Int) -> Model {
    let mut model = point_at(rows, x, v);
    for sum in sums {
        let e = sum_value(sum, rows, &model, v);
        let fl = e.div_floor(&sum.m);
        if let Some(r) = &sum.r {
            model.insert(r.clone(), &e - &(&sum.m * &fl));
        }
        model.insert(sum.q.clone(), if sum.sigma > 0 { fl } else { -&fl });
    }
    model
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
