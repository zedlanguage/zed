//! Sums of quotients over pairwise coprime moduli, decided over the values of the sums instead
//! of the residues of `x` (row PRES-sum-of-quotients-period-product, part (1)).
//!
//! [`sum_residues`] writes the residues of `x` modulo `m L`, `L` the lcm of the moduli a sum
//! reads, so a sum over `k` coprime moduli costs their product, exponential in `k`. Here the
//! formula is decided over the tuples of the sums' remainders that some `x` reaches, whose number
//! does not grow with `k` when the sums are fixed.
//!
//! Lemma C (a sum splits by the Chinese remainder theorem). Let a sum ([`SumRow`]) of modulus
//! `M_j` read rows ([`DefRow`]) `i` on `x`: `rho_i = (a_i x + k_i) mod m_i` and
//! `q_i = sigma_i floor((a_i x + k_i) / m_i)`, with `gcd(m_i, M_j) = 1`. Let `c_X`, `c_Qi`,
//! `c_Ri` be its coefficients on `x`, `q_i`, `rho_i`, and `k` its constant, so that
//! `E = c_X x + sum_i (c_Qi q_i + c_Ri rho_i) + k`. Let `w_i` be the inverse of `m_i` modulo
//! `M_j`. Then
//! `E = A_j x + B_j + sum_i u_ji rho_i (mod M_j)`, with
//! `A_j = c_X + sum_i c_Qi sigma_i w_i a_i`, `B_j = k + sum_i c_Qi sigma_i w_i k_i` and
//! `u_ji = c_Ri - c_Qi sigma_i w_i`.
//! Proof. `a_i x + k_i - rho_i = m_i floor((a_i x + k_i) / m_i)` exactly, so
//! `q_i = sigma_i (a_i x + k_i - rho_i) / m_i`, and multiplying by `m_i w_i = 1 (mod M_j)` gives
//! `q_i = sigma_i w_i (a_i x + k_i - rho_i) (mod M_j)`. Substituting into `E` and collecting the
//! terms in `x`, the constants and each `rho_i` gives the three sums. QED.
//!
//! So `E_j mod M_j` is a function of `x mod M` (`M` the lcm of the sums' moduli, which `M_j`
//! divides) and of the remainders `rho_i`, and `rho_i` is a function of `x mod m_i`. Group the
//! rows by modulus into blocks; when the blocks' moduli `m_b` are pairwise coprime and coprime
//! to `M`, the map `x mod (M prod_b m_b) -> (x mod M, x mod m_1, ...)` is a bijection (the
//! Chinese remainder theorem), so the coordinates take every tuple of values together.
//!
//! Theorem (for the class below: no product atom, coprime moduli, every literal on `x` a row or
//! a sum, every literal on a row's remainder at the top level). Let `f` have [`super::solve`]'s
//! shape and lie in that class. Then `f` has a point exactly when some tuple `s` in the set `R`
//! built below satisfies the literals on the sums' remainders (with `E_j mod M_j = s_j`, and
//! `s_j = 0` for a sum with no remainder).
//! `R` starts as `{(A_j t_0 + B_j mod M_j)_j : 0 <= t_0 < M}`; each block `b` replaces it by the
//! sums `R + W_b` (coordinatewise, modulo each `M_j`), where `W_b` is the set of
//! `(sum_{i in b} u_ji rho_i(t) mod M_j)_j` over the `t` in `0..m_b` at which every row of `b`
//! meets its top-level literals.
//! Proof. By Lemma C, at any `x` the tuple of `E_j mod M_j` is the start value at
//! `t_0 = x mod M` plus the block values at `t_b = x mod m_b`, and every row's literal holds
//! exactly when its row's `t_b` is allowed. (1) A point of `f` therefore has its tuple in `R` and
//! satisfies the sums' literals there (its rows and sums define their parts from `x`
//! ([`def_row`], [`SumRow`]), so each sum's remainder is `E_j mod M_j`). (2) Conversely, a tuple
//! in `R` comes from some `t_0` and allowed `t_b`; by the bijection some `x` has exactly these
//! coordinates, and at that `x` with every part defined from it ([`point_with_sums`]) each row,
//! each sum and each row's literal holds, and the sums' literals hold as they do at the tuple:
//! they name only the sums' remainders, which are atoms here (no product atom, whose value
//! [`Formula::holds`] reads through its factors), so reading them at the tuple's values is
//! reading them at the point. The Boolean structure over the sums' literals is evaluated as it
//! stands. QED.
//! A point is rebuilt by keeping, for each tuple, the step that first reached it, and the
//! Chinese remainder theorem ([`combine_crt_tree`]) on the `t`s; it is checked with
//! [`Formula::holds`].
//!
//! What the path declines (`None`, the other paths then decide `f`): every formula when no
//! question's meter runs ([`solve_by_sums`] gives the reason); a formula naming a product
//! atom, declined before this path by [`super::solve`] (META1 A1 of XR-presburger4, whose
//! comment gives the reason); a literal that names `x` and is not a row or a sum (every
//! literal on `x`'s value or residue); a literal on a row's remainder under a disjunction or a
//! negation, or with a second term, unless it is the same literal as one at the top level
//! (then it holds wherever the top-level one does, and is read as true); moduli (of the blocks
//! and of `M`) that share a prime; a modulus of a sum, the lcm `M`, or the modulus of a block of
//! several rows that does not fit a machine word; and every formula whose bound on this path's
//! steps (below) is above the steps of [`sum_residues`].
//!
//! Literature. The searches recorded for this row (allpapers: paperclip semantic search over
//! arXiv with 183 results, Gemini grounded search; 2026-11-22) found no method for residues of a
//! sum of floor quotients of one variable over many moduli; this says only that those searches
//! found none. The step `R + W_b` is the sumset of two sets in the group
//! `Z_{M_1} x ... x Z_{M_J}`. For one sum (`J = 1`, the cyclic group `Z_m`), and for several
//! sums whose moduli are pairwise coprime (the product group is then cyclic), the n-fold sumset
//! `A_1 + ... + A_n` of arbitrary sets is the problem of Bringmann and Nakos, "Fast n-fold
//! Boolean Convolution via Additive Combinatorics" (ICALP 2021, arXiv:2105.03968), solved in
//! almost linear time in the input plus output size; it generalizes modular subset sum
//! (Axiotis et al., arXiv:2008.10577; Cardinal and Iacono, arXiv:2008.08417; Le and Le,
//! arXiv:2609.30992), where each set is `{0, a_i}`. Neither gives the reduction of the sums of
//! quotients to that sumset (Lemma C and the theorem above), and neither covers the product of
//! several cyclic groups with arbitrary blocks. Simultaneous incongruences (Garey and Johnson,
//! problem AN2, NP-complete) is a reason the guard declines a literal on `x`'s residues: such a
//! literal can couple blocks, and then the tuples of coordinates do not separate; the guard
//! declines every such literal, coupling or not.
//!
//! Tests: `tests::sumset_decisions_match_enumeration`,
//! `tests::the_sumset_path_takes_the_coprime_sums`,
//! `tests::sumset_leaves_a_product_remainder_to_the_fallback`,
//! `tests::sumset_holds_only_the_tuples_reached`, `tests::sumset_shapes_match_enumeration`, and
//! the benchmarks `bench::sums_over_many_coprime_moduli_scale` and
//! `bench::sums_over_many_moduli_two_scale`.

use super::*;

#[cfg(test)]
thread_local! {
    /// Tests only: take this path whatever the costs, so the random tests reach it on every
    /// formula in its scope.
    pub(super) static ALWAYS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Tests only: the number of formulas this path was selected for on this thread (it passed
    /// the scope checks and the cost comparison); a selected formula may still be declined.
    pub(super) static SELECTED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Tests only: the number of formulas this path answered exactly on this thread ([`answered`]).
    pub(super) static ANSWERED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Tests only: the most entries one set of tuples (`R` or `W_b`) held at once on this thread,
    /// each entry a tuple over the coordinates some `x` moves.
    pub(super) static MOST_HELD: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The rows of one modulus `m`, as indices into the rows; their remainders are functions of
/// `x mod m`.
struct Block {
    m: Int,
    rows: Vec<usize>,
}

/// A tuple of remainders, one per sum.
type Tuple = Vec<usize>;

/// A block's way back, kept only for a model: the step that first reached each tuple of the
/// block's `R`, as (index of the tuple before, index into `W_b`), and each tuple's `t` of `W_b`.
type Back = (Vec<(usize, usize)>, Vec<Int>);

/// The primes of `n`, or `None` when `n` does not fit a machine word. `n >= 1`.
fn primes_of(n: &Int) -> Option<Vec<u64>> {
    let n = u64::try_from(n.to_i128()?).ok()?;
    Some(
        zed_numtheory::factor(n)
            .into_iter()
            .map(|(p, _)| p)
            .collect(),
    )
}

/// `v` as a machine word, or `None`.
fn word(v: &Int) -> Option<usize> {
    usize::try_from(v.to_i128()?).ok()
}

/// `(a + b) mod r` for `a, b < r`, without overflow at any word `r`.
fn add_mod(a: usize, b: usize, r: usize) -> usize {
    ((a as u128 + b as u128) % r as u128) as usize
}

/// Charges `steps` steps of this path to the meter of the cover's question running, if any
/// (`meter::charge_pieces`, one piece a step), and returns whether the meter has room left.
/// A step is one value of `t_0`, one value of a block's `t` or of its row's remainder, one pair
/// of a reached tuple and a block's tuple, or one reached tuple read against the literals.
/// Not measured at this site: a step adds `J` words and looks a tuple up in an ordered map, about
/// the work of a piece of `exact::residues` (made, compared, joined) for the small `J` of the
/// inputs measured, so it is charged one piece; unproved that it bounds the step's CPU time for
/// large `J`.
fn charge(steps: &Int) -> bool {
    let steps = steps.to_i128().and_then(|s| u64::try_from(s).ok());
    crate::presburger::meter::charge_pieces(steps.unwrap_or(u64::MAX)).is_ok()
}

/// [`super::solve`]'s answer by the theorem above, or `None` when `f` lies outside its scope
/// (see the list above) or when the residues of `x` cost less ([`sum_residues`]), so that path
/// keeps those formulas. On a meter spent by its charges it answers "no point" at once, as the
/// solver's searches do; the question is then refused (`meter::Work::metered`).
// Complexity tradeoff: naive version, [`sum_residues`]: O(M_j L_j) residues of `x` per sum, the
// product of the moduli for coprime moduli, exponential in their number `k`. Used: the tuples
// reached, held sparsely in ordered maps. With `J` sums that some `x` moves (the others are
// constant and read once), `n_i` intervals of allowed remainders for row `i` and `R_b` the
// tuples reached before block `b`: O(M J log(2 + R_0)) for the start (`R_0 <= min(M, S)`,
// `S = prod_j M_j`); for a block of one row, O(J min(m_b, n_b M) log(2 + |W_b|) + n_b) (each run
// of allowed remainders is walked until `M` steps, since the tuple depends on the remainder
// modulo `M`); for a block of several rows, O(m_b (sum_{i in b} (n_i + J + 1)) + m_b J
// log(2 + |W_b|)); O(R_b |W_b| J log(2 + R_{b+1})) for each step `R + W_b`, or
// O((R_b + R_{b+1}) J log(2 + R_{b+1})) when `W_b` is the whole group on the coordinates it
// moves; and O(R_last (J + |f|) + |f|) to read the literals at the tuples. The step counts
// charged to the meter are these without the log factors. Bit costs: `S` is built in
// O(M(B) log J) for its `B = log S` bits ([`product_of`]); a model keeps one step per tuple and
// block, O(sum_b R_b) words, and pays the Chinese remainder theorem on the blocks' `t`s
// ([`combine_crt_tree`], O(M(B') log k) for the `B'` bits of `M prod_b m_b`). Linear in
// `k` for fixed sums, measured by `bench::sums_over_many_coprime_moduli_scale`, and the tuples
// held follow the tuples reached, not `S` (`bench::sums_over_many_moduli_two_scale`). Each set
// `R_b + W_b` is the naive pairwise sumset; Bringmann and Nakos (above) compute an n-fold sumset
// in a cyclic group in almost linear time in input plus output, a gain only when `R_b |W_b|` is
// far above `R_{b+1}`, which the measured inputs do not reach. The choice between the two paths
// compares a bound on this path's steps (the loops above, `R_b` bounded by `min(S, R_{b-1} W)`)
// with [`sum_residues`]'s residue count, both exact answers, so no answer depends on it; it keeps
// [`sum_residues`] where the sums' moduli are large and the rows few. The coprimality check
// factors each modulus (`zed_numtheory::factor`, a bounded cost per word) and keeps a set of the
// primes seen, O(k) where checking every pair would be O(k^2).
#[allow(clippy::too_many_arguments)]
pub(super) fn solve_by_sums(
    f: &Formula,
    x: &Atom,
    top: &[&Con],
    rows: &[DefRow<'_>],
    sums: &[SumRow],
    r_of: &HashMap<Atom, usize>,
    sum_r: &HashMap<Atom, usize>,
    skip: &HashSet<&Con>,
    want_model: bool,
) -> Option<Option<Model>> {
    // Only under a question's meter (XR-presburger4 round 2 F1, Claude): the tuples reached can
    // number `2^J` for `J` sums (J rows over odd primes, J sums modulo 2 of the form
    // `sum_i q_i + q_j`: 1,048,576 tuples at J = 20, 0.79 s), and with no meter running
    // [`charge`] counts nothing, so nothing would stop the path where [`sum_residues`] declines
    // at once (its period does not fit a word). Under a meter the charges below count the
    // path's steps and the question is refused at its limit (`meter::Work::metered`). With no
    // meter every formula gets the answer of the paths after this one, as before this path; a
    // structural class on which the tuples reached are provably few would let the path run
    // with no meter too (row PRES-sumset-structural-class).
    if sums.is_empty() || !crate::presburger::meter::running() {
        return None;
    }
    // Every constraint naming `x` is a row or a sum; literals on rows' remainders are at the
    // top level and give the allowed remainders of each row.
    let mut allowed: Vec<ResidueSet> = rows
        .iter()
        .map(|row| match row.r {
            Some(_) => vec![(Int::ZERO, &row.m - &Int::ONE)],
            None => vec![(Int::ZERO, Int::ZERO)],
        })
        .collect();
    let mut at_top: HashSet<&Con> = HashSet::new();
    for c in top {
        if skip.contains(c) || c.lin.terms.len() != 1 {
            continue;
        }
        let a = c.lin.terms.keys().next().expect("one term");
        if let Some(&i) = r_of.get(a) {
            let mine = remainder_values(c, &rows[i].m);
            allowed[i] = res_intersect(&allowed[i], &mine);
            at_top.insert(c);
        }
    }
    let mut ok = true;
    let mut n_lits = 0usize;
    f.walk(&mut |c| {
        if skip.contains(c) || at_top.contains(c) {
            return;
        }
        n_lits += 1;
        ok &= c.lin.terms.len() == 1 && c.lin.terms.keys().all(|a| sum_r.contains_key(a));
    });
    if !ok {
        return None;
    }

    // The sums' moduli, the blocks, and their coprimality.
    let mut lcm_m = Int::ONE;
    let mut seen: HashSet<u64> = HashSet::new();
    for sum in sums {
        lcm_m = lcm_m.lcm(&sum.m);
    }
    let big_m = word(&lcm_m)?;
    let m_primes = primes_of(&lcm_m)?;
    seen.extend(m_primes);
    let mut by_m: BTreeMap<Int, Vec<usize>> = BTreeMap::new();
    for (i, row) in rows.iter().enumerate() {
        by_m.entry(row.m.clone()).or_default().push(i);
    }
    let blocks: Vec<Block> = by_m
        .into_iter()
        .map(|(m, rows)| Block { m, rows })
        .collect();
    for b in &blocks {
        // A block of several rows is walked over `0..m_b`, so `m_b` must fit a word. Every row
        // reads `x`: a term is stored only with a nonzero coefficient, and `def_row` reads `a`
        // as `x`'s coefficient.
        if b.rows.len() > 1 {
            word(&b.m)?;
        }
        debug_assert!(b.rows.iter().all(|&i| !rows[i].a.is_zero()));
        for p in primes_of(&b.m)? {
            if !seen.insert(p) {
                return None;
            }
        }
    }

    // Every sum's modulus fits a word (each coordinate is a word below it).
    let radix_all: Vec<usize> = sums.iter().map(|s| word(&s.m)).collect::<Option<_>>()?;

    // Lemma C's coefficients, per sum, reduced modulo its modulus; a `u_ji` that is 0 there is
    // left out, as it adds nothing to a tuple.
    let mut a_j: Vec<Int> = Vec::new();
    let mut b_j: Vec<Int> = Vec::new();
    let mut u: Vec<HashMap<usize, Int>> = Vec::new();
    for sum in sums {
        let mj = &sum.m;
        let (mut a, mut b) = (Int::ZERO, sum.k.clone());
        let mut ui: HashMap<usize, Int> = HashMap::new();
        for (p, c) in &sum.parts {
            match p {
                Part::X => a = &a + c,
                Part::Q(i) => {
                    let row = &rows[*i];
                    let w = inverse_mod(&row.m, mj).expect("coprime to the sum's modulus");
                    let cw = if row.sigma > 0 { c * &w } else { -&(c * &w) };
                    a = &a + &(&cw * &row.a);
                    b = &b + &(&cw * &row.k);
                    let e = ui.entry(*i).or_insert(Int::ZERO);
                    *e = &*e - &cw;
                }
                Part::R(i) => {
                    let e = ui.entry(*i).or_insert(Int::ZERO);
                    *e = &*e + c;
                }
            }
        }
        a_j.push(a.mod_floor(mj));
        b_j.push(b.mod_floor(mj));
        u.push(
            (ui.into_iter())
                .map(|(i, v)| (i, v.mod_floor(mj)))
                .filter(|(_, v)| !v.is_zero())
                .collect(),
        );
    }
    // The coordinates no `x` moves (XR-presburger4 round 2 P2, Codex): a sum whose `A_j` and
    // every `u_ji` are 0 modulo `M_j` has `E_j mod M_j = B_j` at every `x` (Lemma C), the same
    // in every tuple. Each is read once here and left out of the tuples and of the costs: a sum
    // with no remainder needs `E_j mod M_j = 0` (as at the literals below), so `B_j != 0` leaves
    // no point, and a sum's remainder takes the value `B_j` at every tuple. Kept in the tuples,
    // such a coordinate cost `J` word additions a pair of tuples for nothing: k sparse sums
    // `2 r_i + 2 r_{i+1}` modulo 2 beside one dense sum took Θ(k²) additions on Codex's port.
    let mut fixed = Model::new();
    let mut live: Vec<usize> = Vec::new();
    for (j, sum) in sums.iter().enumerate() {
        if !a_j[j].is_zero() || !u[j].is_empty() {
            live.push(j);
        } else if let Some(r) = &sum.r {
            fixed.insert(r.clone(), b_j[j].clone());
        } else if !b_j[j].is_zero() {
            answered();
            return Some(None);
        }
    }
    let radix: Vec<usize> = live.iter().map(|&j| radix_all[j]).collect();
    let u_live: Vec<&HashMap<usize, Int>> = live.iter().map(|&j| &u[j]).collect();

    // The cost of each path (see the tradeoff above): a bound on the steps of the loops below,
    // each step a coordinate or more; `per_step` is the coordinates of a tuple, at least 1.
    let per_step = Int::from(live.len().max(1));
    let s_int = product_of(&radix);
    let mut reached = least(&lcm_m, &s_int).clone();
    let mut new_cost = &lcm_m * &per_step;
    for b in &blocks {
        // The values the loops below walk for `W_b`, and their cost.
        let (values, walk) = walk_of(b, &allowed, &lcm_m, &per_step, live.len());
        let pairs = &reached * least(&values, &s_int);
        new_cost = &new_cost + &(&walk + &(&pairs * &per_step));
        reached = least(&pairs, &s_int).clone();
    }
    new_cost = &new_cost + &literal_cost(reached.clone(), live.len(), n_lits);
    // The lcm only grows, so the sum is read only until it passes `new_cost`: the lcm of all the
    // rows' moduli, a number of about `k` words built one gcd at a time, would cost O(k^2) word
    // steps (measured: 10.17 times the instructions at 8k in the benchmark below with it).
    let mut old_cost = Int::ZERO;
    'sums: for sum in sums {
        let mut l = Int::ONE;
        for (p, _) in &sum.parts {
            if let Part::Q(i) | Part::R(i) = p {
                l = l.lcm(&rows[*i].m);
                if &old_cost + &(&sum.m * &l) > new_cost {
                    old_cost = &old_cost + &(&sum.m * &l);
                    break 'sums;
                }
            }
        }
        old_cost = &old_cost + &(&sum.m * &l);
    }
    #[cfg(test)]
    let always = ALWAYS.with(std::cell::Cell::get);
    #[cfg(not(test))]
    let always = false;
    if new_cost > old_cost && !always {
        return None;
    }
    #[cfg(test)]
    SELECTED.with(|t| t.set(t.get() + 1));
    #[cfg(test)]
    let held = |n: usize| MOST_HELD.with(|h| h.set(h.get().max(n)));

    // The contribution of row `i` at remainder `rho` to each coordinate, added to a tuple.
    let delta = |i: usize, rho: &Int, out: &mut [usize]| {
        for (jj, o) in out.iter_mut().enumerate() {
            if let Some(c) = u_live[jj].get(&i) {
                let v = (c * rho).mod_floor(&sums[live[jj]].m);
                *o = add_mod(*o, word(&v).expect("below a word modulus"), radix[jj]);
            }
        }
    };

    // The start set: `t_0` over `0..M`, keeping the first `t_0` of each tuple.
    if !charge(&(&lcm_m * &per_step)) {
        return Some(None);
    }
    let mut first: BTreeMap<Tuple, usize> = BTreeMap::new();
    for t0 in 0..big_m {
        let tuple: Tuple = (live.iter())
            .map(|&j| {
                let v = (&(&a_j[j] * &Int::from(t0)) + &b_j[j]).mod_floor(&sums[j].m);
                word(&v).expect("below a word modulus")
            })
            .collect();
        first.entry(tuple).or_insert(t0);
    }
    let (mut reach, t0s): (Vec<Tuple>, Vec<usize>) = first.into_iter().unzip();
    #[cfg(test)]
    held(reach.len());
    // For each block, its way back ([`Back`]).
    let mut back: Vec<Back> = Vec::new();
    for b in &blocks {
        // `W_b`: each tuple once, with its first `t`.
        let mut w: BTreeMap<Tuple, Int> = BTreeMap::new();
        let (_, walk) = walk_of(b, &allowed, &lcm_m, &per_step, live.len());
        if !charge(&walk) {
            return Some(None);
        }
        if let [i] = b.rows[..] {
            // `rho = (a t + k) mod m` takes exactly the values `= k (mod g)`, `g = gcd(a, m)`,
            // each at the `t` with `(a / g) t = (rho - k) / g (mod m / g)`; the tuple depends on
            // `rho mod M`, and `g` divides `m`, coprime to `M`, so `M` steps of `g` from any
            // `rho` pass every residue modulo `M`. With `m / g = 1` every `t` gives
            // `rho = k mod m` (the inverse modulo 1 is 0, so `t = 0` is taken).
            let row = &rows[i];
            let g = row.a.gcd(&b.m);
            let n = b.m.div_floor(&g);
            let inv = inverse_mod(&row.a.div_floor(&g), &n).expect("coprime after the gcd");
            let k0 = row.k.mod_floor(&g);
            for (lo, hi) in &allowed[i] {
                let mut rho = lo + &(&k0 - lo).mod_floor(&g);
                let mut steps = 0usize;
                while &rho <= hi && steps < big_m {
                    let mut d = vec![0usize; live.len()];
                    delta(i, &rho, &mut d);
                    let t = (&(&rho - &row.k).div_floor(&g) * &inv).mod_floor(&n);
                    w.entry(d).or_insert(t);
                    rho = &rho + &g;
                    steps += 1;
                }
            }
        } else {
            for t in 0..word(&b.m).expect("checked to fit a word above") {
                let t = Int::from(t);
                let mut d = vec![0usize; live.len()];
                let mut fits = true;
                for &i in &b.rows {
                    let row = &rows[i];
                    let rho = (&(&row.a * &t) + &row.k).mod_floor(&b.m);
                    fits &= allowed[i].iter().any(|(lo, hi)| lo <= &rho && &rho <= hi);
                    delta(i, &rho, &mut d);
                }
                if fits {
                    w.entry(d).or_insert(t);
                }
            }
        }
        // No allowed `t` in this block: `R + W_b` is empty, and so is every later one.
        if w.is_empty() {
            answered();
            return Some(None);
        }
        let (w, w_t): (Vec<Tuple>, Vec<Int>) = w.into_iter().unzip();
        #[cfg(test)]
        held(w.len());
        // The coordinates this block moves: those of a sum with a `u_ji != 0` for a row `i` of
        // the block. A tuple of `W_b` is 0 on every other coordinate.
        let moved: Vec<bool> = (u_live.iter())
            .map(|ui| b.rows.iter().any(|i| ui.contains_key(i)))
            .collect();
        let whole = (radix.iter().zip(&moved))
            .filter(|(_, m)| **m)
            .try_fold(1usize, |p, (&r, _)| p.checked_mul(r));
        let mut next: BTreeMap<Tuple, (usize, usize)> = BTreeMap::new();
        if whole == Some(w.len()) {
            // `W_b` is the whole group on the coordinates it moves (XR-presburger4 round 2 P1,
            // Codex): it lies in {0 elsewhere} x (that group) and has the group's size, so it is
            // that set, and `R + W_b` is the set of tuples whose other coordinates are those of
            // a tuple of `R`, the moved ones anything. Written directly, one tuple of `R` for
            // each value of the other coordinates: O(|R| J log |R| + |R + W_b| J log |R + W_b|),
            // where the pairs of `R` and `W_b` were |R| |W_b|, Θ(M²) for one sum modulo `M` over
            // singleton rows whose remainders pass every residue modulo `M` (63.72 times at 8M
            // on Codex's port). Each tuple's step back is that tuple of `R` and the tuple of
            // `W_b` that is their difference on the moved coordinates, found by modular
            // subtraction and a binary search of the sorted `W_b`.
            if !charge(&(&Int::from(reach.len()) * &per_step)) {
                return Some(None);
            }
            let mut by_rest: BTreeMap<Tuple, usize> = BTreeMap::new();
            for (pi, cur) in reach.iter().enumerate() {
                let rest: Tuple = (cur.iter().zip(&moved))
                    .map(|(&v, &m)| if m { 0 } else { v })
                    .collect();
                by_rest.entry(rest).or_insert(pi);
            }
            let made = &Int::from(by_rest.len()) * &Int::from(w.len());
            if !charge(&(&made * &per_step)) {
                return Some(None);
            }
            for (mut t, pi) in by_rest {
                loop {
                    let wi = if want_model {
                        let d: Tuple = (t.iter().zip(&reach[pi]).zip(&radix).zip(&moved))
                            .map(|(((&v, &p), &r), &m)| if m { add_mod(v, r - p, r) } else { 0 })
                            .collect();
                        w.binary_search(&d)
                            .expect("W_b is the whole group it moves")
                    } else {
                        0
                    };
                    next.insert(t.clone(), (pi, wi));
                    // The next value of the moved coordinates, counted in their radices.
                    let mut wrapped = true;
                    for jj in (0..t.len()).filter(|&jj| moved[jj]) {
                        t[jj] += 1;
                        if t[jj] < radix[jj] {
                            wrapped = false;
                            break;
                        }
                        t[jj] = 0;
                    }
                    if wrapped {
                        break;
                    }
                }
            }
        } else {
            let pairs = &Int::from(reach.len()) * &Int::from(w.len());
            if !charge(&(&pairs * &per_step)) {
                return Some(None);
            }
            let mut sum_t = vec![0usize; live.len()];
            for (pi, cur) in reach.iter().enumerate() {
                for (wi, d) in w.iter().enumerate() {
                    for (((s, c), d), r) in sum_t.iter_mut().zip(cur).zip(d).zip(&radix) {
                        *s = add_mod(*c, *d, *r);
                    }
                    if !next.contains_key(&sum_t) {
                        next.insert(sum_t.clone(), (pi, wi));
                    }
                }
            }
        }
        let (r, steps): (Vec<Tuple>, Vec<(usize, usize)>) = next.into_iter().unzip();
        reach = r;
        #[cfg(test)]
        held(reach.len());
        if want_model {
            back.push((steps, w_t));
        }
    }

    // The literals on the sums' remainders, read at each reached tuple.
    if !charge(&literal_cost(Int::from(reach.len()), live.len(), n_lits)) {
        return Some(None);
    }
    let lits = f.map_cons(&|c| {
        if skip.contains(c) || at_top.contains(c) {
            Formula::top()
        } else {
            Formula::Con(c.clone())
        }
    });
    let mut values = fixed;
    let found = reach.iter().position(|tuple| {
        if (live.iter().zip(tuple)).any(|(&j, v)| sums[j].r.is_none() && *v != 0) {
            return false;
        }
        for (&j, v) in live.iter().zip(tuple) {
            if let Some(r) = &sums[j].r {
                values.insert(r.clone(), Int::from(*v));
            }
        }
        lits.holds(&values)
    });
    let Some(mut at) = found else {
        answered();
        return Some(None);
    };
    if !want_model {
        answered();
        return Some(Some(Model::new()));
    }
    let mut pairs: Vec<(Int, Int)> = Vec::new();
    for (b, (steps, w_t)) in blocks.iter().zip(&back).rev() {
        let (prev, wi) = steps[at];
        pairs.push((w_t[wi].clone(), b.m.clone()));
        at = prev;
    }
    pairs.push((Int::from(t0s[at]), lcm_m.clone()));
    let (x_value, _) = combine_crt_tree(pairs)?;
    let model = point_with_sums(rows, sums, x, &x_value);
    // By (2) of the theorem this is a point of `f`; a failure here is a defect of this module,
    // and declining leaves `f` to the other paths.
    let holds = f.holds(&model);
    debug_assert!(
        holds,
        "the point rebuilt from x = {x_value} is not one of\n{f}"
    );
    if holds {
        answered();
    }
    holds.then_some(Some(model))
}

/// Counts an exact answer of [`solve_by_sums`] ([`ANSWERED`], tests only): a return of "no
/// point" from the tuples, or of a point checked with [`Formula::holds`]; not a return on a
/// spent meter, nor a decline.
fn answered() {
    #[cfg(test)]
    ANSWERED.with(|t| t.set(t.get() + 1));
}

/// The lesser of `a` and `b`, by reference.
fn least<'a>(a: &'a Int, b: &'a Int) -> &'a Int {
    if a <= b { a } else { b }
}

/// The values [`solve_by_sums`] walks for block `b`'s `W_b`, and their cost in steps: for a
/// block of one row `i`, `min(m_b, n_i M)` values of its remainder, `J` coordinates each, and
/// one step for each of its `n_i` intervals; for a block of several rows, every `t` in
/// `0..m_b`, each row's remainder tested against its `n_i` intervals and added to the `J`
/// coordinates, and the row itself. `j` is the coordinates of a tuple; `per_step` is `j`, at
/// least 1.
fn walk_of(b: &Block, allowed: &[ResidueSet], lcm_m: &Int, per_step: &Int, j: usize) -> (Int, Int) {
    if let [i] = b.rows[..] {
        let n_i = Int::from(allowed[i].len());
        let v = least(&b.m, &(&n_i * lcm_m)).clone();
        let walk = &(&v * per_step) + &n_i;
        (v, walk)
    } else {
        let per: usize = b.rows.iter().map(|&i| allowed[i].len() + j + 1).sum();
        (b.m.clone(), &b.m * &Int::from(per))
    }
}

/// The steps of reading the literals at `reached` tuples: each tuple's `j` coordinates and
/// its `n_lits` literals, and the formula of the literals built once, `n_lits` more.
fn literal_cost(reached: Int, j: usize, n_lits: usize) -> Int {
    &(&reached * &Int::from(j + n_lits)) + &Int::from(n_lits)
}

/// The product of `radix`, the size of the group of the tuples (XR-presburger4 round 2 P3,
/// Codex and Gemini): each radix repeated `c` times is raised to the power `c` by squaring
/// ([`zed_kernel::num::pow_uint`]), and the powers of the distinct radices are multiplied in a
/// product tree ([`zed_kernel::num::trees::product_tree`]). Multiplied one radix at a time,
/// the `i`-th product has about `i` words, Θ(J²) word steps for `J` radices (62.25 times the
/// work at J = 2,000 against 16,000 on Gemini's port); here O(M(B) log J) for the `B` bits of
/// the product, `M(B)` the cost of one product of `B` bits.
fn product_of(radix: &[usize]) -> Int {
    use num_bigint::{BigInt, BigUint};
    let mut count: BTreeMap<usize, u64> = BTreeMap::new();
    for &r in radix {
        *count.entry(r).or_insert(0) += 1;
    }
    let leaves: Vec<BigUint> = (count.into_iter())
        .map(|(r, c)| zed_kernel::num::pow_uint(&BigUint::from(r), c))
        .collect();
    let root = match zed_kernel::num::trees::product_tree(&leaves).pop() {
        Some(mut top) => top.pop().expect("the root of the tree"),
        None => leaves
            .into_iter()
            .next()
            .unwrap_or_else(|| BigUint::from(1u32)),
    };
    Int::from(BigInt::from(root))
}
