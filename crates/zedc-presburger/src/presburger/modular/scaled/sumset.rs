//! Sums of quotients over pairwise coprime moduli, decided over the values of the sums instead
//! of the residues of `x` (row PRES-sum-of-quotients-period-product, part (1)).
//!
//! [`sum_residues`] writes the residues of `x` modulo `m L`, `L` the lcm of the moduli a sum
//! reads, so a sum over `k` coprime moduli costs their product, exponential in `k`. Here the
//! formula is decided over the tuples of the sums' remainders, whose number does not grow with
//! `k`.
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
//! Theorem. Let `f` have [`super::solve`]'s shape, with these coprime moduli, every constraint
//! naming `x` a row or a sum, and every literal on a row's remainder at the top level. Then `f`
//! has a point exactly when some tuple `s` in the set `R` built below satisfies the literals on
//! the sums' remainders (with `E_j mod M_j = s_j`, and `s_j = 0` for a sum with no remainder).
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
//! each sum and each row's literal holds, and the sums' literals hold as they do at the tuple.
//! The Boolean structure over the sums' literals is evaluated as it stands. QED.
//! A point is rebuilt by keeping, for each tuple, the `t` that first reached it, and the
//! Chinese remainder theorem ([`combine_crt_tree`]) on the `t`s; it is checked with
//! [`Formula::holds`].
//!
//! Literature. The search for this row (allpapers: paperclip semantic search over arXiv with
//! 183 results, Gemini grounded search; 2026-11-22) found no method for residues of a sum of
//! floor quotients of one variable over many moduli. The nearest work is modular subset sum
//! (Axiotis et al.; Cardinal and Iacono; Le and Le, arXiv:2609.30992, "Deterministic
//! Linear-Time Modular Subset Sum"), whose state is also a residue modulo the target's modulus;
//! here each block offers a set of residues rather than one item, which the step `R + W_b`
//! handles. Simultaneous incongruences (Garey and Johnson, problem AN2, NP-complete) is why the
//! formula is declined when a literal on `x`'s residues couples blocks: then the tuples of
//! coordinates do not separate.
//!
//! Tests: `tests::sumset_decisions_match_enumeration`,
//! `tests::the_sumset_path_takes_the_coprime_sums`, and the benchmark
//! `bench::sums_over_many_coprime_moduli_scale`.

use super::*;

#[cfg(test)]
thread_local! {
    /// Tests only: take this path whatever the costs, so the random tests reach it on every
    /// formula in its scope.
    pub(super) static ALWAYS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Tests only: the number of formulas this path answered on this thread.
    pub(super) static TAKEN: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The rows of one modulus `m`, as indices into the rows; their remainders are functions of
/// `x mod m`.
struct Block {
    m: Int,
    rows: Vec<usize>,
}

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

/// `n` copies of `v`, or `None` when the allocator refuses the room (the formula is then
/// declined, as [`sum_residues`] declines one whose residues cannot be counted in a word).
fn filled<T: Clone>(n: usize, v: T) -> Option<Vec<T>> {
    let mut out = Vec::new();
    out.try_reserve_exact(n).ok()?;
    out.resize(n, v);
    Some(out)
}

/// The tuple `s` (one remainder per sum) written as one number in the mixed radix `radix`.
fn encode(s: &[usize], radix: &[usize]) -> usize {
    s.iter().zip(radix).fold(0, |acc, (v, r)| acc * r + v)
}

fn decode(mut code: usize, radix: &[usize], out: &mut [usize]) {
    for (o, r) in out.iter_mut().zip(radix).rev() {
        *o = code % r;
        code /= r;
    }
}

/// [`super::solve`]'s answer by the theorem above, or `None` when `f` lies outside its scope or
/// when the residues of `x` cost less ([`sum_residues`]), so that path keeps those formulas.
// Complexity tradeoff: naive version, [`sum_residues`]: O(M_j L_j) residues of `x` per sum, the
// product of the moduli for coprime moduli, exponential in their number `k`. Used: with
// `S = prod_j M_j` tuples and `J` sums, O(M J) for the start, O(min(m_b, (n_b + 1) M)) values
// for a block of one row with `n_b` runs of allowed remainders (the values of `rho` modulo `M`
// repeat after `M` steps of the coset) or O(m_b) for a block of several rows, O(S |W_b| J) for
// each step `R + W_b`, and O(S |f|) to read the literals at the tuples: linear in `k` for fixed
// sums, measured by `bench::sums_over_many_coprime_moduli_scale`. The coprimality check factors
// each modulus (`zed_numtheory::factor`, a bounded cost per word) and keeps a set of the primes
// seen, O(k) where checking every pair would be O(k^2). The choice between the two paths
// compares their step counts as written above, both exact, so no answer depends on it; it keeps
// [`sum_residues`] where the sums' moduli are large and the rows few.
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
    if sums.is_empty() {
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
    f.walk(&mut |c| {
        if skip.contains(c) || at_top.contains(c) {
            return;
        }
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
        // A block of several rows is walked over `0..m_b`, so `m_b` must fit a word; a row with
        // `a = 0` reads no `x` and has no `t` to solve for.
        if b.rows.len() > 1 {
            word(&b.m)?;
        }
        if b.rows.iter().any(|&i| rows[i].a.is_zero()) {
            return None;
        }
        for p in primes_of(&b.m)? {
            if !seen.insert(p) {
                return None;
            }
        }
    }

    // The cost of each path (see the tradeoff above).
    let radix: Vec<usize> = sums.iter().map(|s| word(&s.m)).collect::<Option<_>>()?;
    let mut s_int = Int::ONE;
    for sum in sums {
        s_int = &s_int * &sum.m;
    }
    let states = word(&s_int)?;
    let n_sums = Int::from(sums.len());
    let mut new_cost = &lcm_m * &n_sums;
    for b in &blocks {
        let c = if let [i] = b.rows[..] {
            let runs = Int::from(allowed[i].len() + 1);
            b.m.clone().min(&runs * &lcm_m)
        } else {
            &b.m * &Int::from(b.rows.len())
        };
        new_cost = &new_cost + &(&c + &(&(&s_int * &c.clone().min(s_int.clone())) * &n_sums));
    }
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
    TAKEN.with(|t| t.set(t.get() + 1));

    // Lemma C's coefficients, per sum.
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
        u.push(ui.into_iter().map(|(i, v)| (i, v.mod_floor(mj))).collect());
    }
    // The contribution of row `i` at remainder `rho` to each sum, as a tuple.
    let delta = |i: usize, rho: &Int, out: &mut [usize]| {
        for (j, o) in out.iter_mut().enumerate() {
            if let Some(c) = u[j].get(&i) {
                let v = (c * rho).mod_floor(&sums[j].m);
                *o = (*o + word(&v).expect("below a word modulus")) % radix[j];
            }
        }
    };

    // The start set: `t_0` over `0..M`, keeping the first `t_0` of each tuple.
    let mut first: Vec<Option<usize>> = filled(states, None)?;
    let mut tuple = vec![0usize; sums.len()];
    for t0 in 0..big_m {
        for (j, o) in tuple.iter_mut().enumerate() {
            let v = (&(&a_j[j] * &Int::from(t0)) + &b_j[j]).mod_floor(&sums[j].m);
            *o = word(&v).expect("below a word modulus");
        }
        let code = encode(&tuple, &radix);
        if first[code].is_none() {
            first[code] = Some(t0);
        }
    }
    let mut reach: Vec<bool> = first.iter().map(Option::is_some).collect();
    // For each block, the tuple each new tuple came from and the `t` it took there.
    let mut back: Vec<Vec<Option<(usize, Int)>>> = Vec::new();
    for b in &blocks {
        // `W_b`: each tuple once, with its first `t`.
        let mut w_seen: HashSet<usize> = HashSet::new();
        let mut w: Vec<(Vec<usize>, Int)> = Vec::new();
        let mut add = |t: Int, d: Vec<usize>| {
            if w_seen.insert(encode(&d, &radix)) {
                w.push((d, t));
            }
        };
        if let [i] = b.rows[..] {
            // `rho = (a t + k) mod m` takes exactly the values `= k (mod g)`, `g = gcd(a, m)`,
            // each at the `t` with `(a / g) t = (rho - k) / g (mod m / g)`; the tuple depends on
            // `rho mod M`, and `g` divides `m`, coprime to `M`, so `M` steps of `g` from any
            // `rho` pass every residue modulo `M`.
            let row = &rows[i];
            let g = row.a.gcd(&b.m);
            let n = b.m.div_floor(&g);
            let inv = inverse_mod(&row.a.div_floor(&g), &n).expect("coprime after the gcd");
            let k0 = row.k.mod_floor(&g);
            for (lo, hi) in &allowed[i] {
                let mut rho = lo + &(&k0 - lo).mod_floor(&g);
                let mut steps = 0usize;
                while &rho <= hi && steps < big_m {
                    let mut d = vec![0usize; sums.len()];
                    delta(i, &rho, &mut d);
                    let t = (&(&rho - &row.k).div_floor(&g) * &inv).mod_floor(&n);
                    add(t, d);
                    rho = &rho + &g;
                    steps += 1;
                }
            }
        } else {
            for t in 0..word(&b.m).expect("checked to fit a word above") {
                let t = Int::from(t);
                let mut d = vec![0usize; sums.len()];
                let mut fits = true;
                for &i in &b.rows {
                    let row = &rows[i];
                    let rho = (&(&row.a * &t) + &row.k).mod_floor(&b.m);
                    fits &= allowed[i].iter().any(|(lo, hi)| lo <= &rho && &rho <= hi);
                    delta(i, &rho, &mut d);
                }
                if fits {
                    add(t, d);
                }
            }
        }
        let mut next = filled(states, false)?;
        let mut from: Vec<Option<(usize, Int)>> =
            filled(if want_model { states } else { 0 }, None)?;
        let mut cur = vec![0usize; sums.len()];
        let mut sum_t = vec![0usize; sums.len()];
        for (code, _) in reach.iter().enumerate().filter(|(_, r)| **r) {
            decode(code, &radix, &mut cur);
            for (d, t) in &w {
                for (((s, c), d), r) in sum_t.iter_mut().zip(&cur).zip(d).zip(&radix) {
                    *s = (c + d) % r;
                }
                let to = encode(&sum_t, &radix);
                if !next[to] {
                    next[to] = true;
                    if want_model {
                        from[to] = Some((code, t.clone()));
                    }
                }
            }
        }
        reach = next;
        back.push(from);
    }

    // The literals on the sums' remainders, read at each reached tuple.
    let lits = f.map_cons(&|c| {
        if skip.contains(c) || at_top.contains(c) {
            Formula::top()
        } else {
            Formula::Con(c.clone())
        }
    });
    let mut values = Model::new();
    let mut found: Option<usize> = None;
    for (code, _) in reach.iter().enumerate().filter(|(_, r)| **r) {
        decode(code, &radix, &mut tuple);
        if sums
            .iter()
            .zip(&tuple)
            .any(|(sum, v)| sum.r.is_none() && *v != 0)
        {
            continue;
        }
        for (sum, v) in sums.iter().zip(&tuple) {
            if let Some(r) = &sum.r {
                values.insert(r.clone(), Int::from(*v));
            }
        }
        if lits.holds(&values) {
            found = Some(code);
            break;
        }
    }
    let Some(mut code) = found else {
        return Some(None);
    };
    if !want_model {
        return Some(Some(Model::new()));
    }
    let mut pairs: Vec<(Int, Int)> = Vec::new();
    for (b, from) in blocks.iter().zip(&back).rev() {
        let (prev, t) = from[code].clone().expect("a reached tuple has its step");
        pairs.push((t, b.m.clone()));
        code = prev;
    }
    let t0 = first[code].expect("a start tuple has its t_0");
    pairs.push((Int::from(t0), lcm_m.clone()));
    let (x_value, _) = combine_crt_tree(pairs)?;
    let model = point_with_sums(rows, sums, x, &x_value);
    // By (2) of the theorem this is a point of `f`; a failure here is a defect of this module,
    // and declining leaves `f` to the other paths.
    let holds = f.holds(&model);
    debug_assert!(
        holds,
        "the point rebuilt from x = {x_value} is not one of\n{f}"
    );
    holds.then_some(Some(model))
}
