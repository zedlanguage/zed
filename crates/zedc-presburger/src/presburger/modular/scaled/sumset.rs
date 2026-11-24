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
//! `q_i = sigma_i floor((a_i x + k_i) / m_i)`, with `gcd(m_i, M_j) = 1` for each `q_i` it reads.
//! Let `c_X`, `c_Qi`, `c_Ri` be its coefficients on `x`, `q_i`, `rho_i`, and `k` its constant, so
//! that `E = c_X x + sum_i (c_Qi q_i + c_Ri rho_i) + k`. Let `w_i` be the inverse of `m_i` modulo
//! `M_j`. Then
//! `E = A_j x + B_j + sum_i u_ji rho_i (mod M_j)`, with
//! `A_j = c_X + sum_i c_Qi sigma_i w_i a_i`, `B_j = k + sum_i c_Qi sigma_i w_i k_i` and
//! `u_ji = c_Ri - c_Qi sigma_i w_i`.
//! Proof. `a_i x + k_i - rho_i = m_i floor((a_i x + k_i) / m_i)` exactly, so
//! `q_i = sigma_i (a_i x + k_i - rho_i) / m_i`, and multiplying by `m_i w_i = 1 (mod M_j)` gives
//! `q_i = sigma_i w_i (a_i x + k_i - rho_i) (mod M_j)`. Substituting into `E` and collecting the
//! terms in `x`, the constants and each `rho_i` gives the three sums. QED.
//!
//! A sum whose `A_j` and every `u_ji` are 0 modulo `M_j` is fixed: `E_j mod M_j = B_j` at every
//! `x`. The others are live, and `M` is the lcm of the live sums' moduli. So a live `E_j mod M_j`
//! is a function of `x mod M` (`M_j` divides `M`) and of the remainders `rho_i`, and `rho_i` is a
//! function of `x mod m_i`. Group the rows by modulus into blocks; when the blocks' moduli `m_b`
//! are pairwise coprime and coprime to `M`, the map
//! `x mod (M prod_b m_b) -> (x mod M, x mod m_1, ...)` is a bijection (the Chinese remainder
//! theorem), so the coordinates take every tuple of values together.
//!
//! Theorem (for the class below: no product atom, coprime moduli, every literal on `x` a row or
//! a sum, every literal on a row's remainder at the top level). Let `f` have [`super::solve`]'s
//! shape and lie in that class. Then `f` has a point exactly when some tuple `s` in the set `R`
//! built below satisfies the literals on the sums' remainders (with `E_j mod M_j = s_j`, and
//! `s_j = 0` for a sum with no remainder).
//! `R` starts as `{(A_j t_0 + B_j mod M_j)_j : 0 <= t_0 < M}` over the live sums; each block `b`
//! replaces it by the sums `R + W_b` (coordinatewise, modulo each `M_j`), where `W_b` is the set
//! of `(sum_{i in b} u_ji rho_i(t) mod M_j)_j` over the `t` in `0..m_b` at which every row of `b`
//! meets its top-level literals; a fixed sum takes `B_j` throughout.
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
//!
//! The tuples are held over coordinates, fewer than the live sums (XR-presburger4 round 3,
//! Gemini). Live sums `j`, `j'` of one modulus whose vectors `(A_j, u_j1, u_j2, ...)` are
//! `lambda_j v` and `lambda_j' v` for one vector `v` share the coordinate
//! `v_c = (v_0 t_0 + sum_i v_i rho_i) mod M_j`: `E_j mod M_j = lambda_j v_c + B_j`. Here `v` is
//! the vector divided by its first entry invertible modulo `M_j` (`lambda_j` that entry), or the
//! vector itself (`lambda_j = 1`) when no entry is invertible. The live sums with no `u_ji` (moved
//! by `t_0` alone) share one class coordinate: the index of their joint value at `t_0` among the
//! joint values of `0..M`. Both are functions of the same `t_0` and `rho_i`, so `R` over the
//! coordinates and `R` over the sums are in bijection, and every step above reads the same.
//! Each tuple is one id of a hash-consed tree over the coordinates ([`tuples`]), equal ids
//! exactly for equal tuples, so a set of tuples is a set of ids, and a block reads and rebuilds
//! only the paths to the coordinates it moves (PERIOD-B-P1-intern-rest).
//!
//! A point is rebuilt from the last tuple backward: each block's `t` is that of a tuple `w` of
//! `W_b` with `s - w` in the set before the block, and `t_0` that of the start tuple reached;
//! the Chinese remainder theorem ([`combine_crt_tree`]) on the `t`s gives `x`, checked with
//! [`Formula::holds`].
//!
//! What the path declines (`None`, the other paths then decide `f`), in the order checked:
//! a formula with no sum, and every formula when no question's meter runs ([`solve_by_sums`]
//! gives the reason); a formula naming a product atom, declined before this path by
//! [`super::solve`] (META1 A1 of XR-presburger4, whose comment gives the reason); a constraint
//! not at the top level, or at the top level and not a literal on a row's remainder, that is not
//! a literal of one term on a sum's remainder (every literal on `x`'s value or residue, a literal
//! on a row's remainder under a disjunction or a negation or with a second term, unless it is the
//! same literal as one at the top level, then read as true); a row whose modulus has no inverse
//! modulo the modulus of a sum that reads its quotient; a live sum's modulus or `M` that does not
//! fit a machine word; a block's modulus that does not fit a machine word (its primes are
//! found by factoring a word); moduli (of the blocks and of `M`) that share a prime; and every
//! formula whose bound on this path's steps (below) is above the steps of [`sum_residues`].
//!
//! Literature. The searches recorded for this row (allpapers: paperclip semantic search over
//! arXiv with 183 results, Gemini grounded search; 2026-11-22) found no method for residues of a
//! sum of floor quotients of one variable over many moduli; this says only that those searches
//! found none. The step `R + W_b` is the sumset of two sets in the group
//! `Z_{M_1} x ... x Z_{M_J}`. For one sum (`J = 1`, the cyclic group `Z_m`), and for several
//! sums whose moduli are pairwise coprime (the product group is then cyclic), the n-fold sumset
//! `A_1 + ... + A_n` of arbitrary sets is the problem of Bringmann and Nakos, "Fast n-fold
//! Boolean Convolution via Additive Combinatorics" (ICALP 2021, arXiv:2105.03968), solved for
//! input plus output size `k` "by a randomized Las Vegas algorithm in O(k · polylog(mk))
//! expected time, or by a deterministic algorithm in k · 2^{O(sqrt(log k · log log m))} time"
//! (`introduction.tex` lines 97-98; line 84 states the same bounds in words: "a randomized Las
//! Vegas algorithm running in expected time O(k · polylog m), and a deterministic algorithm
//! running in time k · m^{o(1)}"), so neither bound is linear (META4 LIT4-B, Codex); it
//! generalizes modular subset sum
//! (Axiotis et al., arXiv:2008.10577; Cardinal and Iacono, arXiv:2008.08417; Le and Le,
//! arXiv:2609.30992), where each set is `{0, a_i}`. Neither gives the reduction of the sums of
//! quotients to that sumset (Lemma C and the theorem above), and neither covers the product of
//! several cyclic groups with arbitrary blocks. One step `R + W_b` is computed here by the
//! reduction of a sumset to a product of polynomials with 0/1 coefficients, where that costs
//! less than the pairs. Source: Bringmann and Nakos (above), Section 1, "Boolean Convolution
//! and Sumset Computation": sumset computation of `A, B ⊆ Z_m` "corresponds to Boolean
//! convolution with wraparound" (line 14), and the next paragraph's heading is "Standard
//! Convolution and Polynomial Multiplication" (line 17), whose `C[k] = sum_i A[i] · B[k-i]` is
//! the coefficient of `z^k` in the product of the polynomials `sum A[i] z^i` and `sum B[i] z^i`
//! (arXiv source `introduction.tex`, read 2026-11-23 in the copy fetched for XR-presburger4
//! round 4, `r4/codex/sources/fetched/verification/source/Bringmann2021fast`; an earlier
//! version of this comment quoted "This problem is equivalent to polynomial multiplication",
//! which that source does not hold). The packing of several coordinates into one
//! integer exponent is proved at [`poly_cost`] and its callers; it is not taken from a paper.
//! (Until XR-presburger4 META4 order 6, this sentence credited the reduction to Cardinal and
//! Iacono, Section 2, which describes a dynamic string algorithm, not this reduction: Codex,
//! round 4, LIT4-B.) Tests: `tests::sumset_decisions_match_enumeration`.
//! Simultaneous incongruences (Garey and Johnson, problem AN2, NP-complete) is a reason the guard
//! declines a literal on `x`'s residues: such a literal can couple blocks, and then the tuples of
//! coordinates do not separate; the guard declines every such literal, coupling or not.
//!
//! Tests: `tests::sumset_decisions_match_enumeration`,
//! `tests::the_sumset_path_takes_the_coprime_sums`,
//! `tests::sumset_leaves_a_product_remainder_to_the_fallback`,
//! `tests::sumset_holds_only_the_tuples_reached`, `tests::sumset_shapes_match_enumeration`,
//! `tests::the_sumset_path_runs_only_under_a_meter`,
//! `tests::an_answer_on_a_spent_meter_is_not_checked`, `tests::sumset_charges_each_step`,
//! `tests::a_sum_with_a_whole_group_costs_its_tuples`,
//! `tests::a_sum_missing_one_residue_costs_its_tuples`,
//! `tests::a_whole_group_reached_before_a_block_costs_its_tuples`,
//! `tests::two_sums_of_one_direction_cost_one_coordinate`,
//! `tests::sums_moved_by_x_alone_cost_one_coordinate`, `tests::fixed_literals_are_read_once`,
//! `tests::a_fixed_sum_leaves_the_period`, `tests::constant_sums_are_read_once`,
//! `tests::coordinates_moved_by_the_end_blocks_are_not_copied`, and the
//! benchmarks `bench::coordinates_moved_by_the_end_blocks_scale`,
//! `bench::sums_over_many_coprime_moduli_scale`,
//! `bench::sums_over_many_moduli_two_scale`, `bench::constant_sums_beside_a_dense_sum_scale`,
//! `bench::many_sums_over_few_rows_scale`, `bench::a_sum_missing_one_residue_scale`,
//! `bench::two_sums_of_one_direction_scale`, `bench::sums_moved_by_x_alone_scale` and
//! `bench::fixed_literals_beside_a_live_sum_scale`. The bound on the estimate of the costs
//! (XR-presburger4 round 3 P3) is proved at its site, not measured: the formulas whose estimate
//! is large are declined to [`sum_residues`], whose work on them no benchmark can run.

use super::*;

mod tuples;
use tuples::Tuples;

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
    /// Tests only: the words written to build the tuples reached on this thread (PRES-B-P1-
    /// copied-words), so that a test sees copies the units hide beside the walks of the blocks.
    pub(super) static COPIED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Counts `n` words written to build tuples ([`COPIED`], tests only).
fn copied(n: u64) {
    #[cfg(test)]
    COPIED.with(|c| c.set(c.get().saturating_add(n)));
    #[cfg(not(test))]
    let _ = n;
}

/// The rows of one modulus `m`, as indices into the rows; their remainders are functions of
/// `x mod m`.
struct Block {
    m: Int,
    rows: Vec<usize>,
}

/// A tuple of values, one per coordinate.
type Tuple = Vec<usize>;

/// Where a live sum's remainder is read in a tuple (the coordinates in the module comment).
enum Place {
    /// `(lam v_c + b) mod m`, from coordinate `c`.
    Moved {
        c: usize,
        lam: usize,
        b: usize,
        m: usize,
    },
    /// Entry `pos` of the joint value of the sums moved by `t_0` alone, whose index is the class
    /// coordinate.
    Class { pos: usize },
}

/// A block's step, kept only for a model: a step by one tuple `w` of `W_b` (over the coordinates
/// `mv` the block moves) at its `t`, or a sum, with the ids of the tuples before it.
enum Level {
    Shift {
        mv: Vec<usize>,
        w: Tuple,
        t: Int,
    },
    Sum {
        before: HashSet<usize>,
        mv: Vec<usize>,
        w: Vec<Tuple>,
        w_t: Vec<Int>,
    },
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

/// `v >= 0` as a word, or the largest word when it does not fit one.
fn word_or_max(v: &Int) -> u64 {
    (v.to_i128())
        .and_then(|v| u64::try_from(v).ok())
        .unwrap_or(u64::MAX)
}

/// `(a + b) mod r` for `a, b <= r`, without overflow at any word `r`: the way back passes
/// `b = r - v`, which is `r` when `v = 0` (XR-presburger4 round 4 P4-D, Codex).
fn add_mod(a: usize, b: usize, r: usize) -> usize {
    ((a as u128 + b as u128) % r as u128) as usize
}

/// `(a b + c) mod r` for words, without overflow.
fn mul_add_mod(a: usize, b: usize, c: usize, r: usize) -> usize {
    ((a as u128 * b as u128 + c as u128) % r as u128) as usize
}

/// Charges `steps` steps of this path to the meter of the cover's question running, if any
/// (`meter::charge_pieces`, one piece a step), and returns whether the meter has room left.
/// A step is one word of a tuple written or read (one coordinate), one value of `t_0` or of a
/// block's `t` for each coordinate it moves, one test of a row's remainder against one interval,
/// one coefficient of a product of polynomials, or one literal read at a tuple; each call site
/// names what it charges. Not measured at this site: a step is a few word operations and, for a
/// tuple, a share of a lookup in an ordered map; the map's log factor is not charged.
fn charge(steps: u64) -> bool {
    crate::presburger::meter::charge_pieces(steps).is_ok()
}

/// [`super::solve`]'s answer by the theorem above, or `None` when `f` lies outside its scope
/// (see the list above) or when the residues of `x` cost less ([`sum_residues`]), so that path
/// keeps those formulas. On a meter spent by its charges it answers "no point" at once, as the
/// solver's searches do; the question is then refused (`meter::Work::metered`).
// Complexity tradeoff: naive version, [`sum_residues`]: O(M_j L_j) residues of `x` per sum, the
// product of the moduli for coprime moduli, exponential in their number `k`. Used: the tuples
// reached, held sparsely, over `C` coordinates (at most the live sums, see the module comment).
// With `n_i` intervals of allowed remainders for row `i`, `deg(i)` the coordinates row `i` moves
// (the sum of all `deg(i)` is at most the size of the sums), `d_b` those block `b` moves, and
// `R_b` the tuples reached before block `b`:
// - the start, O(M (C + J_0) log(2 + R_0)) (`J_0` the sums moved by `t_0` alone);
// - `W_b` of one row, O(min(m_b, n_b M) deg(i) log(2 + |W_b|) + n_b) (each run of allowed
//   remainders is walked until `M` steps, since the tuple depends on the remainder modulo `M`);
//   of several rows, O(m_b sum_{i in b} (n_i + deg(i) + 1) + m_b d_b log(2 + |W_b|));
// - `R + W_b`: with one tuple in `W_b`, a translation, O(R_b U_b); else the tuples of `R` are
//   grouped by their other coordinates (O(R_b U_b), the rest an id), and each group `R_c` gives
//   `R_c + W_b` over the `G = prod r` values of the moved coordinates as the cheapest of: all of
//   them when `R_c` or `W_b` is all of them (O(G C)); the pairs (O(|R_c| |W_b| d_b log)); or the
//   product of the two polynomials with 0/1 coefficients by Kronecker substitution (below),
//   O(L log L + L d_b) for `L = prod (2 r - 1) <= 2^d_b G` words, by
//   [`zed_kernel::num::mul_uint`] (O(n log n) by transforms above `MUL_LEAF = 400` words);
//   each tuple of `R_{b+1}` is then built, O(U_b);
// - the literals, O(R_last (J + |lits| + U_lit) + |f|), with the literals on fixed sums read
//   once.
// Here a tuple is one id of a hash-consed tree over the coordinates ([`tuples`]), and `U_b` is
// the number of its nodes on the paths to the coordinates block `b` moves, `U_lit` to those the
// literals read: at most `sum_{c in mv_b} (depth(c) + 1)`, the tree weighted so that a
// coordinate moved often sits near the root, and never more in all than a balanced tree's
// `O(d_b log C)` (the bound proved at [`tuples`]). Until PERIOD-B-P1-intern-rest each tuple was a
// vector of `C` words read and written whole at each block: with `k` blocks each moving one
// coordinate beside `k` coordinates moved elsewhere that was Θ(k²) words for one tuple reached
// (`tests::coordinates_moved_by_the_end_blocks_are_not_copied`, which counts them).
// The step counts charged to the meter are these without the log factors. A model keeps the ids
// before each block, O(sum_b R_b) words, and pays O(|W_b| U_b) a block to find the way back
// and the Chinese remainder theorem on the blocks' `t`s ([`combine_crt_tree`], O(M(B') log k)
// for the `B'` bits of `M prod_b m_b`). The cost of the two paths is compared in saturating word
// arithmetic, O(C + k) (XR-presburger4 round 3 P3: built in big integers it was Θ(k²) bit work
// before the first charge). Where a block's `W_b` misses one value of its group, the pairs were
// Θ(M²) for one sum modulo `M` (59.3 times at 8M, XR-presburger4 round 3 P1, Claude); the
// polynomial product makes it O(M log M), `tests::a_sum_missing_one_residue_costs_its_tuples`.
// Bringmann and Nakos (above) compute an n-fold sumset in a cyclic group in
// O(k polylog(mk)) expected time (Las Vegas) or k 2^{O(sqrt(log k log log m))} deterministic
// time, `k` the input plus output size; the product of polynomials here is the step of one
// pair of sets. The choice between the two paths compares a bound on this path's steps (the
// loops above, `R_b` bounded by `min(S, R_{b-1} |W|)` for `S` the product of the radices) with
// [`sum_residues`]'s residue count, both exact answers, so no answer depends on it; it keeps
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
            // O(1) a literal (XR-presburger4 round 4 P4-D, Codex's MISSED-ERROR: excluded
            // residues one at a time on one row would make each meet copy the runs left, Θ(L²)
            // for L literals). Proof that it cannot happen: `allowed[i]` starts as one interval;
            // `remainder_values` gives at most one, as a literal is `Rel::Ge` (a half-line) or
            // `Rel::Eq` (a point), and `Rel` has no `!=`; the meet of two intervals is at most
            // one interval. So `allowed[i]` holds at most one interval after every literal, by
            // induction, and each meet reads at most two. A residue excluded is an `Or` of two
            // literals, not at the top level, and a literal on a row's remainder below the top
            // level makes the path decline (`ok` below).
            let mine = remainder_values(c, &rows[i].m);
            allowed[i] = res_intersect(&allowed[i], &mine);
            debug_assert!(allowed[i].len() <= 1);
            at_top.insert(c);
        }
    }
    let mut ok = true;
    let mut n_all = 0u64;
    f.walk(&mut |c| {
        n_all += 1;
        if skip.contains(c) || at_top.contains(c) {
            return;
        }
        ok &= c.lin.terms.len() == 1 && c.lin.terms.keys().all(|a| sum_r.contains_key(a));
    });
    if !ok {
        return None;
    }
    // The walk of `f` just made, `n_all` constraints, charged before any answer below
    // (XR-presburger4 round 4 P4-C, Codex: it and the copy by `map_cons` were charged only with
    // the literals at the end, which the early answers skipped). Test
    // `an_early_answer_charges_the_walk_of_the_formula`.
    if !charge(n_all) {
        return Some(None);
    }

    // Lemma C's coefficients, per sum, reduced modulo its modulus; a `u_ji` that is 0 there is
    // left out, as it adds nothing to a tuple. A row's modulus with no inverse modulo a sum's
    // modulus that reads its quotient is declined.
    let mut a_j: Vec<Int> = Vec::new();
    let mut b_j: Vec<Int> = Vec::new();
    let mut u: Vec<Vec<(usize, Int)>> = Vec::new();
    for sum in sums {
        let mj = &sum.m;
        let (mut a, mut b) = (Int::ZERO, sum.k.clone());
        let mut ui: HashMap<usize, Int> = HashMap::new();
        for (p, c) in &sum.parts {
            match p {
                Part::X => a = &a + c,
                Part::Q(i) => {
                    let row = &rows[*i];
                    let w = inverse_mod(&row.m, mj)?;
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
        // A row whose remainder has one allowed value `c` (a top-level literal `r_i == c`, or no
        // remainder, `c = 0`) adds `u_ji c` to `E_j` at every point, so it goes into `B_j` and
        // leaves `u_j` (XR-presburger4 round 4 B-P1, Gemini's P-A; META4 order 8). The row stays
        // in its block, whose walk still requires `r_i = c`, and moves no coordinate of this
        // sum: a sum left with no `u_ji` is moved by `t_0` alone or fixed, not a coordinate of
        // its own. Before, P-A's `k` sums `2 q_0 + q_{k+j}` modulo 2, with `r_{k+j} == 0`, were
        // `k` coordinates, and each of the `k` blocks of the other rows copied all of them,
        // Θ(k²). Test `rows_of_one_remainder_leave_the_coordinates`.
        ui.retain(|&i, v| match &allowed[i][..] {
            [(lo, hi)] if lo == hi => {
                b = &b + &(&*v * lo);
                false
            }
            _ => true,
        });
        a_j.push(a.mod_floor(mj));
        b_j.push(b.mod_floor(mj));
        let mut ui: Vec<(usize, Int)> = (ui.into_iter())
            .map(|(i, v)| (i, v.mod_floor(mj)))
            .filter(|(_, v)| !v.is_zero())
            .collect();
        ui.sort_unstable_by_key(|(i, _)| *i);
        u.push(ui);
    }
    // The fixed sums (XR-presburger4 round 2 P2, Codex): a sum whose `A_j` and every `u_ji` are 0
    // modulo `M_j` has `E_j mod M_j = B_j` at every `x` (Lemma C). Each is read once here and
    // left out of the tuples, of `M` and of the costs: a sum with no remainder needs
    // `E_j mod M_j = 0` (as at the literals below), so `B_j != 0` leaves no point, and a sum's
    // remainder takes the value `B_j` at every tuple.
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
    // The literals on the sums' remainders, with each literal on a fixed sum's remainder read
    // once here, as true or false (XR-presburger4 round 3 P2, Codex: it was read again at every
    // tuple); [`Formula::and`] and [`Formula::or`] drop or absorb the constants. The literals on
    // rows' remainders at the top level hold wherever the tuple's `t`s are allowed.
    // A literal on one sum's remainder that every value `0..M_j` meets (the bounds
    // `0 <= r_j <= M_j - 1` written with each sum) or none meets is read once here, as true or
    // false: the remainder at a tuple is always in `0..M_j` (a value modulo `M_j`, and
    // [`read_sum`] admits a sum only with those bounds at the top level). Kept, the bounds read
    // every sum's remainder, so the filter of the places below kept all `k` sums and the
    // literals at each of the `M` tuples were Θ(k M) (XR-presburger4 round 4 NB-P2, META4
    // order 9: 15,456 -> 726,096 units at k = m = 15 -> 120 with only the filter). O(1) words a
    // literal ([`remainder_values`] meets one interval with `0..M_j`).
    let constant = |c: &Con| -> Option<bool> {
        let [a] = &c.lin.terms.keys().collect::<Vec<_>>()[..] else {
            return None;
        };
        let m = &sums[*sum_r.get(*a)?].m;
        let vals = remainder_values(c, m);
        if vals.is_empty() {
            Some(false)
        } else {
            (vals[..] == [(Int::ZERO, m - &Int::ONE)]).then_some(true)
        }
    };
    let lits = f.map_cons(&|c| {
        if skip.contains(c) || at_top.contains(c) {
            Formula::top()
        } else if let Some(holds) = constant(c) {
            if holds {
                Formula::top()
            } else {
                Formula::bottom()
            }
        } else if (c.lin.terms.keys()).all(|a| fixed.contains_key(a)) {
            if Formula::Con(c.clone()).holds(&fixed) {
                Formula::top()
            } else {
                Formula::bottom()
            }
        } else {
            Formula::Con(c.clone())
        }
    });
    // The copy of `f` by `map_cons`, `n_all` constraints, charged before any answer below, as
    // the walk of `f` is above (P4-C).
    if !charge(n_all) {
        return Some(None);
    }
    if matches!(&lits, Formula::Or(gs) if gs.is_empty()) {
        answered();
        return Some(None);
    }
    let mut n_lits = 0u64;
    lits.walk(&mut |_| n_lits += 1);

    // `M`, the lcm of the live sums' moduli (XR-presburger4 round 3 P2, Codex: the fixed sums'
    // moduli entered it), built one word at a time and declined as soon as it passes a word
    // (round 3 P3, Gemini: built over every sum first, Θ(k²) bit work).
    let mut lcm_m = Int::ONE;
    for &j in &live {
        lcm_m = lcm_m.lcm(&sums[j].m);
        word(&lcm_m)?;
    }
    let big_m = word(&lcm_m)?;
    let mut seen: HashSet<u64> = primes_of(&lcm_m)?.into_iter().collect();
    let mut by_m: BTreeMap<Int, Vec<usize>> = BTreeMap::new();
    for (i, row) in rows.iter().enumerate() {
        by_m.entry(row.m.clone()).or_default().push(i);
    }
    let blocks: Vec<Block> = by_m
        .into_iter()
        .map(|(m, rows)| Block { m, rows })
        .collect();
    for b in &blocks {
        // A block of several rows is walked over `0..m_b`, so `m_b` must fit a word; every
        // block's primes are found by factoring a word. Every row reads `x`: a term is stored
        // only with a nonzero coefficient, and `def_row` reads `a` as `x`'s coefficient.
        debug_assert!(b.rows.iter().all(|&i| !rows[i].a.is_zero()));
        for p in primes_of(&b.m)? {
            if !seen.insert(p) {
                return None;
            }
        }
    }

    // The coordinates (module comment): the moved ones, sums merged by their vector, then the
    // class coordinate of the sums moved by `t_0` alone, if any.
    let mut radix: Vec<usize> = Vec::new();
    let mut start_a: Vec<usize> = Vec::new();
    let mut by_row: Vec<Vec<(usize, usize)>> = vec![Vec::new(); rows.len()];
    type Key = (usize, usize, Vec<(usize, usize)>);
    let mut coord_of: HashMap<Key, usize> = HashMap::new();
    let mut places: Vec<(usize, Place)> = Vec::new();
    // The sums moved by `t_0` alone, as `(A_j, B_j, M_j)` words.
    let mut by_t0: Vec<(usize, usize, usize)> = Vec::new();
    for &j in &live {
        let mj_int = &sums[j].m;
        let mj = word(mj_int).expect("divides M, a word");
        let b = word(&b_j[j]).expect("below a word modulus");
        if u[j].is_empty() {
            let a = word(&a_j[j]).expect("below a word modulus");
            places.push((j, Place::Class { pos: by_t0.len() }));
            by_t0.push((a, b, mj));
            continue;
        }
        let entries = std::iter::once(&a_j[j]).chain(u[j].iter().map(|(_, v)| v));
        let (lam, inv) = (entries.clone())
            .find_map(|e| inverse_mod(e, mj_int).map(|inv| (e.clone(), inv)))
            .unwrap_or((Int::ONE, Int::ONE));
        let norm = |e: &Int| word(&(e * &inv).mod_floor(mj_int)).expect("below a word modulus");
        let key: Key = (
            mj,
            norm(&a_j[j]),
            u[j].iter().map(|(i, v)| (*i, norm(v))).collect(),
        );
        let c = match coord_of.get(&key) {
            Some(&c) => c,
            None => {
                let c = radix.len();
                radix.push(mj);
                start_a.push(key.1);
                for &(i, e) in &key.2 {
                    by_row[i].push((c, e));
                }
                coord_of.insert(key, c);
                c
            }
        };
        let lam = word(&lam).expect("below a word modulus");
        places.push((j, Place::Moved { c, lam, b, m: mj }));
    }
    // The places read at each tuple: a sum with no remainder (its value must be 0) and a sum
    // whose remainder a literal reads. A remainder no literal reads is never looked at, so
    // filling it at every tuple was `|R| k` steps for `k` such sums beside `M` tuples, Θ(k M)
    // (XR-presburger4 round 4 NB-P2; META4 order 9). One walk of the literals, O(n_lits)
    // hashes. Test `remainders_no_literal_reads_are_not_filled`.
    let mut read: HashSet<&Atom> = HashSet::new();
    lits.walk(&mut |c| read.extend(c.lin.terms.keys()));
    places.retain(|(j, _)| sums[*j].r.as_ref().is_none_or(|r| read.contains(r)));
    let n_moved = radix.len();
    // The class coordinate's radix is the number of joint values, at most `M`, known after the
    // start below; `M` bounds it in the cost.
    let class_c = (!by_t0.is_empty()).then(|| {
        radix.push(big_m);
        n_moved
    });
    let n_coord = radix.len() as u64;
    // The coordinates each block moves, sorted.
    let mvs: Vec<Vec<usize>> = (blocks.iter())
        .map(|b| {
            let mut mv: Vec<usize> = (b.rows.iter())
                .flat_map(|&i| by_row[i].iter().map(|&(c, _)| c))
                .collect();
            mv.sort_unstable();
            mv.dedup();
            mv
        })
        .collect();

    // The cost of each path (see the tradeoff above), in saturating words: a bound on the steps
    // of the loops below.
    let m64 = big_m as u64;
    let s_all = (radix.iter()).fold(1u64, |p, &r| p.saturating_mul(r as u64));
    let start_cost = m64.saturating_mul((n_moved + by_t0.len()).max(1) as u64);
    // The tuples reached before each block, a bound (`R_b <= min(S, R_{b-1} |W_b|)`), and after
    // the last.
    let mut reached_at: Vec<u64> = Vec::with_capacity(blocks.len() + 1);
    let mut walks: Vec<(u64, u64)> = Vec::with_capacity(blocks.len());
    let mut reached = m64.min(s_all);
    for (b, mv) in blocks.iter().zip(&mvs) {
        let (values, walk) = walk_of(b, &allowed, &by_row, m64);
        let g = (mv.iter()).fold(1u64, |p, &c| p.saturating_mul(radix[c] as u64));
        reached_at.push(reached);
        walks.push((values.min(g), walk));
        reached = s_all.min(reached.saturating_mul(values.min(g)));
    }
    reached_at.push(reached);
    // The coordinates the literals read.
    let mut read_cs: Vec<usize> = (places.iter())
        .map(|(_, p)| match *p {
            Place::Moved { c, .. } => c,
            Place::Class { .. } => class_c.expect("a class"),
        })
        .collect();
    read_cs.sort_unstable();
    read_cs.dedup();
    // The tuples, held in a tree weighted by the tuples expected to visit each coordinate
    // ([`tuples`]): each coordinate weighs one, plus `R_b` for each block `b` moving it, plus the
    // tuples read at the literals when one reads it. Summed in `u128`, exact: each term is below
    // 2^64, one per entry of `mvs` and `read_cs` or per coordinate, fewer than 2^60 in all, so
    // the total is below 2^124, as the depth bound at [`tuples`] takes it. Summed in saturating
    // `u64`, the bounds `R_b` that reach `2^64` (the product of the radices past a word) made every
    // coordinate weigh `2^64 - 1`, the tree balanced whatever the blocks moved, and the words
    // copied on `tests::spanning_rows` grew 15.4 times from `k = 15` to 120 (job g1 of
    // b22-period1). O(C log C + size of the `mv`s), charged with the start below as a word per
    // coordinate (the log not charged).
    let mut weight: Vec<u128> = vec![1; radix.len()];
    for (mv, &r) in mvs.iter().zip(&reached_at) {
        for &c in mv {
            weight[c] = weight[c].saturating_add(u128::from(r));
        }
    }
    for &c in &read_cs {
        weight[c] = weight[c].saturating_add(u128::from(reached));
    }
    let mut tuples = Tuples::new(&weight);
    let moved: Vec<tuples::Moved> = mvs.iter().map(|mv| tuples.moved(mv)).collect();
    // The nodes a tuple visits at each block and at the literals ([`Tuples::visits`]), at least
    // one; they replace the `C` words a tuple was read and written whole (PERIOD-B-P1).
    let visits: Vec<u64> = moved.iter().map(|m| tuples.visits(m).max(1)).collect();
    let lit_moved = tuples.moved(&read_cs);
    let lit_visits = tuples.visits(&lit_moved);
    let start_cost = start_cost.saturating_add(n_coord);
    let mut new_cost = start_cost;
    for (b, mv) in mvs.iter().enumerate() {
        let (reached, next) = (reached_at[b], reached_at[b + 1]);
        let ((values, walk), per) = (walks[b], visits[b]);
        let step = if values <= 1 {
            reached.saturating_mul(per)
        } else {
            let g = (mv.iter()).fold(1u64, |p, &c| p.saturating_mul(radix[c] as u64));
            let pairs = (reached.saturating_mul(values)).saturating_mul(mv.len() as u64);
            let classes = reached.min(s_all / g.max(1)).max(1);
            let poly = poly_cost(&radix, mv).unwrap_or(u64::MAX);
            (reached.saturating_mul(per))
                .saturating_add(pairs.min(poly.saturating_mul(classes)))
                .saturating_add(next.saturating_mul(per))
        };
        new_cost = (new_cost.saturating_add(walk)).saturating_add(step);
    }
    new_cost = (new_cost.saturating_add(literal_cost(reached, places.len(), n_lits, n_all)))
        .saturating_add(reached.saturating_mul(lit_visits));
    // The lcm only grows, so the sum is read only until it passes `new_cost`: the lcm of all the
    // rows' moduli, a number of about `k` words built one gcd at a time, would cost O(k^2) word
    // steps (measured: 10.17 times the instructions at 8k in the benchmark below with it).
    // Bound (XR-presburger4 round 3 P3, Codex and Gemini: the estimate was Θ(k²) bit work before
    // the first charge). Everything above is word arithmetic, saturating, O(1) a block, a row of
    // a block and a coordinate moved, so O(C + k + B) in all, beside the shape of the tuples'
    // tree, O(C log C), and its visits, O(sum_b d_b) nodes of depth below 180 ([`tuples`]).
    // Below, until the break,
    // `old_cost <= new_int < 2^64`, so the `l` of the sum at hand satisfies `M_j l <= 2^64` before
    // its last lcm, and after it `l <= 2^64 m_i` with `m_i` one row's modulus: each lcm and each
    // product reads O(1 + words(m_i)) words, and each part is read once, so the loop is O(size
    // of the sums) word steps. No step here is charged: each is bounded by the input read.
    let new_int = Int::from(usize::try_from(new_cost).unwrap_or(usize::MAX));
    let mut old_cost = Int::ZERO;
    'sums: for sum in sums {
        let mut l = Int::ONE;
        for (p, _) in &sum.parts {
            if let Part::Q(i) | Part::R(i) = p {
                l = l.lcm(&rows[*i].m);
                if &old_cost + &(&sum.m * &l) > new_int {
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
    if new_int > old_cost && !always {
        return None;
    }
    #[cfg(test)]
    SELECTED.with(|t| t.set(t.get() + 1));
    #[cfg(test)]
    let held = |n: usize| MOST_HELD.with(|h| h.set(h.get().max(n)));

    // The start set: `t_0` over `0..M`, keeping the first `t_0` of each tuple; the joint values
    // of the sums moved by `t_0` alone are numbered as they are met. Charged a word per moved
    // coordinate and per such sum, for each `t_0`.
    if !charge(start_cost) {
        return Some(None);
    }
    let mut class_of: HashMap<Tuple, usize> = HashMap::new();
    let mut class_vals: Vec<Tuple> = Vec::new();
    let mut first: BTreeMap<Tuple, usize> = BTreeMap::new();
    for t0 in 0..big_m {
        let mut tuple: Tuple = (0..n_moved)
            .map(|c| mul_add_mod(start_a[c], t0, 0, radix[c]))
            .collect();
        if class_c.is_some() {
            let joint: Tuple = (by_t0.iter())
                .map(|&(a, b, m)| mul_add_mod(a, t0, b, m))
                .collect();
            let idx = match class_of.get(&joint) {
                Some(&idx) => idx,
                None => {
                    class_of.insert(joint.clone(), class_vals.len());
                    class_vals.push(joint);
                    class_vals.len() - 1
                }
            };
            tuple.push(idx);
        }
        first.entry(tuple).or_insert(t0);
    }
    if let Some(c) = class_c {
        radix[c] = class_vals.len();
    }
    // Each start tuple made once, O(C) ([`Tuples::make`]), within the steps charged above.
    let mut reach: Vec<usize> = Vec::with_capacity(first.len());
    let mut t0_of: HashMap<usize, usize> = HashMap::new();
    for (tuple, t0) in first {
        let id = tuples.make(&tuple);
        reach.push(id);
        if want_model {
            t0_of.insert(id, t0);
        }
    }
    #[cfg(test)]
    held(reach.len());
    let radix_int: Vec<Int> = radix.iter().map(|&r| Int::from(r)).collect();
    // The position of each coordinate in the moved coordinates of the block at hand.
    let mut pos_of = vec![usize::MAX; radix.len()];
    // For each block, its step ([`Level`]), for a model.
    let mut levels: Vec<Level> = Vec::new();
    for (bi, (b, mv)) in blocks.iter().zip(&mvs).enumerate() {
        for (p, &c) in mv.iter().enumerate() {
            pos_of[c] = p;
        }
        let (moved, per) = (&moved[bi], visits[bi]);
        // The contribution of row `i` at remainder `rho` to each coordinate it moves.
        let delta = |i: usize, rho: &Int, out: &mut [usize]| {
            for &(c, e) in &by_row[i] {
                let rr = word(&rho.mod_floor(&radix_int[c])).expect("below a word modulus");
                let o = &mut out[pos_of[c]];
                *o = mul_add_mod(e, rr, *o, radix[c]);
            }
        };
        // `W_b` over the coordinates the block moves: each tuple once, with its first `t`.
        let mut w: BTreeMap<Tuple, Int> = BTreeMap::new();
        let (_, walk) = walk_of(b, &allowed, &by_row, m64);
        if !charge(walk) {
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
                    let mut d = vec![0usize; mv.len()];
                    delta(i, &rho, &mut d);
                    let t = (&(&rho - &row.k).div_floor(&g) * &inv).mod_floor(&n);
                    w.entry(d).or_insert(t);
                    rho = &rho + &g;
                    steps += 1;
                }
            }
        } else {
            for t in 0..word(&b.m)? {
                let t = Int::from(t);
                let mut d = vec![0usize; mv.len()];
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
        for &c in mv {
            pos_of[c] = usize::MAX;
        }
        // No allowed `t` in this block: `R + W_b` is empty, and so is every later one.
        if w.is_empty() {
            answered();
            return Some(None);
        }
        let (w, w_t): (Vec<Tuple>, Vec<Int>) = w.into_iter().unzip();
        #[cfg(test)]
        held(w.len());
        let d = mv.len();
        if let [w0] = &w[..] {
            // One tuple: `R + W_b` is `R` moved by it, a bijection, so the tuples stay distinct;
            // each is read and rebuilt along the paths of the moved coordinates.
            if !charge((reach.len() as u64).saturating_mul(per)) {
                return Some(None);
            }
            if d > 0 {
                for t in &mut reach {
                    let mut vals = tuples.read(*t, moved);
                    for ((v, &c), &s) in vals.iter_mut().zip(mv).zip(w0) {
                        *v = add_mod(*v, s, radix[c]);
                    }
                    *t = tuples.set(*t, moved, &vals);
                }
            }
            if want_model {
                levels.push(Level::Shift {
                    mv: mv.clone(),
                    w: w0.clone(),
                    t: w_t[0].clone(),
                });
            }
            continue;
        }
        // The tuples of `R` grouped by their other coordinates, `R_c` the moved part of each
        // group: `R + W_b` is the union over the groups of their other coordinates with
        // `R_c + W_b`. Each tuple's moved part read and its rest (the part set to 0) built along
        // the paths of the moved coordinates ([`Tuples::visits`]); the groups in the order first
        // met, so the answer does not depend on a hash.
        if !charge((reach.len() as u64).saturating_mul(per)) {
            return Some(None);
        }
        let radii: Vec<usize> = mv.iter().map(|&c| radix[c]).collect();
        let g = radii.iter().try_fold(1usize, |p, &r| p.checked_mul(r));
        let before: HashSet<usize> = if want_model {
            reach.iter().copied().collect()
        } else {
            HashSet::new()
        };
        let zeros = vec![0usize; d];
        let mut group_of: HashMap<usize, usize> = HashMap::new();
        let mut classes: Vec<(usize, Vec<Tuple>)> = Vec::new();
        for t in std::mem::take(&mut reach) {
            let part = tuples.read(t, moved);
            let rest = tuples.set(t, moved, &zeros);
            let at = *group_of.entry(rest).or_insert_with(|| {
                classes.push((rest, Vec::new()));
                classes.len() - 1
            });
            classes[at].1.push(part);
        }
        for (rest, parts) in classes {
            // The cheapest of the three ways (the tradeoff above), each charged before it runs.
            let outs: Vec<Tuple> = if g == Some(parts.len()) || g == Some(w.len()) {
                // All of the group: `R_c` already is (XR-presburger4 round 3, Gemini), so
                // `R_c + W_b` is too, `W_b` being nonempty; or `W_b` is (round 2 P1, Codex),
                // and `R_c` is nonempty.
                let g = g.expect("equal to a length") as u64;
                if !charge(g.saturating_mul(d as u64)) {
                    return Some(None);
                }
                every_value(&radii)
            } else {
                let pairs =
                    ((parts.len() as u64).saturating_mul(w.len() as u64)).saturating_mul(d as u64);
                match poly_cost(&radix, mv) {
                    Some(poly) if poly < pairs => {
                        if !charge(poly) {
                            return Some(None);
                        }
                        sumset_by_product(&parts, &w, &radii)
                    }
                    _ => {
                        if !charge(pairs) {
                            return Some(None);
                        }
                        sumset_by_pairs(&parts, &w, &radii)
                    }
                }
            };
            // Each tuple of `R_{b+1}` built from the rest along the moved coordinates' paths.
            if !charge((outs.len() as u64).saturating_mul(per)) {
                return Some(None);
            }
            for o in outs {
                reach.push(tuples.set(rest, moved, &o));
            }
        }
        #[cfg(test)]
        held(reach.len());
        if want_model {
            levels.push(Level::Sum {
                before,
                mv: mv.clone(),
                w,
                w_t,
            });
        }
    }

    // The literals on the sums' remainders, read at each reached tuple: a word per live sum and
    // each literal at each tuple, the literals once, and the walk of `f` that built them.
    // The walk of `f` and its copy were charged where they ran (P4-C), so `n_all` is 0 here.
    // The coordinates read are read together along their paths, `lit_visits` nodes a tuple.
    let lit_reads = (reach.len() as u64).saturating_mul(lit_visits);
    if !charge(literal_cost(reach.len() as u64, places.len(), n_lits, 0).saturating_add(lit_reads))
    {
        return Some(None);
    }
    // The index of each coordinate read in `read_cs`.
    let mut slot = vec![usize::MAX; radix.len()];
    for (i, &c) in read_cs.iter().enumerate() {
        slot[c] = i;
    }
    let mut values = Model::new();
    let found = reach.iter().position(|&id| {
        let tuple = tuples.read(id, &lit_moved);
        for (j, place) in &places {
            let v = match *place {
                Place::Moved { c, lam, b, m } => mul_add_mod(lam, tuple[slot[c]], b, m),
                Place::Class { pos } => class_vals[tuple[slot[class_c.expect("a class")]]][pos],
            };
            match &sums[*j].r {
                None if v != 0 => return false,
                None => {}
                Some(r) => {
                    values.insert(r.clone(), Int::from(v));
                }
            }
        }
        lits.holds(&values)
    });
    let Some(at) = found else {
        answered();
        return Some(None);
    };
    if !want_model {
        answered();
        return Some(Some(Model::new()));
    }
    // The way back (module comment): each candidate read and rebuilt along the paths of the
    // block's moved coordinates, `visits[b]` nodes.
    let back: u64 = (levels.iter().zip(&visits))
        .map(|(l, &per)| match l {
            Level::Shift { .. } => per,
            Level::Sum { w, .. } => (w.len() as u64).saturating_mul(per),
        })
        .fold(0u64, u64::saturating_add);
    if !charge(back) {
        return Some(None);
    }
    let mut s = reach.swap_remove(at);
    let mut pairs: Vec<(Int, Int)> = Vec::new();
    for ((b, level), moved) in blocks.iter().zip(&levels).zip(&moved).rev() {
        let mut minus = |s: usize, mv: &[usize], w: &Tuple| -> usize {
            let mut vals = tuples.read(s, moved);
            for ((v, &c), &u) in vals.iter_mut().zip(mv).zip(w) {
                *v = add_mod(*v, radix[c] - u, radix[c]);
            }
            tuples.set(s, moved, &vals)
        };
        let t = match level {
            Level::Shift { mv, w, t } => {
                s = minus(s, mv, w);
                t
            }
            Level::Sum { before, mv, w, w_t } => {
                let (wi, prev) = (w.iter().enumerate())
                    .map(|(wi, wv)| (wi, minus(s, mv, wv)))
                    .find(|(_, prev)| before.contains(prev))
                    .expect("a tuple of R + W_b is a tuple of R plus one of W_b");
                s = prev;
                &w_t[wi]
            }
        };
        pairs.push((t.clone(), b.m.clone()));
    }
    let t0 = *t0_of.get(&s).expect("a start tuple");
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

/// Every tuple of values below `radii`, the first coordinate counted fastest.
fn every_value(radii: &[usize]) -> Vec<Tuple> {
    let mut out = Vec::new();
    let mut t = vec![0usize; radii.len()];
    loop {
        out.push(t.clone());
        let mut wrapped = true;
        for (v, &r) in t.iter_mut().zip(radii) {
            *v += 1;
            if *v < r {
                wrapped = false;
                break;
            }
            *v = 0;
        }
        if wrapped {
            return out;
        }
    }
}

/// `a + b` coordinatewise modulo `radii`, each sum once, by the pairs.
fn sumset_by_pairs(a: &[Tuple], b: &[Tuple], radii: &[usize]) -> Vec<Tuple> {
    let mut out: BTreeSet<Tuple> = BTreeSet::new();
    let mut s = vec![0usize; radii.len()];
    for x in a {
        for y in b {
            for (((s, &x), &y), &r) in s.iter_mut().zip(x).zip(y).zip(radii) {
                *s = add_mod(x, y, r);
            }
            if !out.contains(&s) {
                out.insert(s.clone());
            }
        }
    }
    out.into_iter().collect()
}

/// The steps of [`sumset_by_product`] over the coordinates `mv`, without the log factor of the
/// product, as the other charges leave out the log factors of the maps (see [`charge`]): the two
/// polynomials of `L = prod (2 r - 1)` words written, the `2 L` words of the product read, each
/// decoded in `d` digits, and the `G` values of the group, `d` words each; `None` when `2 L` does
/// not fit a word. Every multiply that can pass a word is checked: `2 r - 1` itself passes one
/// for `r >= 2^63` (XR-presburger4 round 4, P4-A, Codex and Gemini), and then `None`, as the
/// product it would size cannot be held. Test `tests::poly_cost_of_a_radix_past_half_a_word`.
pub(super) fn poly_cost(radix: &[usize], mv: &[usize]) -> Option<u64> {
    let mut l = 1u64;
    let mut g = 1u64;
    for &c in mv {
        let digits = (radix[c] as u64).checked_mul(2)?.checked_sub(1)?;
        l = l.checked_mul(digits)?;
        g = g.saturating_mul(radix[c] as u64);
    }
    usize::try_from(l.checked_mul(2)?).ok()?;
    let d = mv.len() as u64;
    Some(((2 * l).saturating_mul(1 + d)).saturating_add(g.saturating_mul(d)))
}

/// `a + b` coordinatewise modulo `radii` by one product of polynomials (Kronecker
/// substitution): a tuple `v` is the power `sum_p v_p s_p` with `s_0 = 1` and
/// `s_{p+1} = s_p (2 r_p - 1)`, and a set is the polynomial with coefficient 1 at each of its
/// tuples' powers, held as a number with one 64-bit word a coefficient.
/// Proof. In the product, the coefficient at the power `e` counts the pairs `(x, y)` with
/// `sum_p (x_p + y_p) s_p = e`; it is at most `min(|a|, |b|) < 2^64`, so no word carries into
/// the next and each word of the product is one coefficient. Each `x_p + y_p` lies in
/// `0..2 r_p - 1`, so `e` has the digits `x_p + y_p` in the mixed radix `2 r_p - 1`, and distinct
/// digit tuples give distinct powers. So a coefficient is nonzero exactly when its digits are
/// `x + y` for some pair, and `x + y` modulo `radii` is each digit folded modulo `r_p`. QED.
/// [`zed_kernel::num::mul_uint`] multiplies by transforms in O(n log n) above `MUL_LEAF = 400`
/// words (zed-kernel `num/fast.rs`, the build that is not a test).
fn sumset_by_product(a: &[Tuple], b: &[Tuple], radii: &[usize]) -> Vec<Tuple> {
    let mut strides = Vec::with_capacity(radii.len());
    let mut l = 1usize;
    for &r in radii {
        strides.push(l);
        l *= 2 * r - 1;
    }
    let poly = |set: &[Tuple]| {
        let mut limbs = vec![0u32; 2 * l];
        for v in set {
            let e: usize = v.iter().zip(&strides).map(|(x, s)| x * s).sum();
            limbs[2 * e] = 1;
        }
        num_bigint::BigUint::new(limbs)
    };
    let product = zed_kernel::num::mul_uint(&poly(a), &poly(b));
    let g: usize = radii.iter().product();
    let mut hit = vec![false; g];
    for (e, coef) in product.iter_u64_digits().enumerate() {
        if coef == 0 {
            continue;
        }
        let (mut rest, mut idx, mut scale) = (e, 0usize, 1usize);
        for &r in radii {
            idx += (rest % (2 * r - 1)) % r * scale;
            rest /= 2 * r - 1;
            scale *= r;
        }
        hit[idx] = true;
    }
    (hit.into_iter().enumerate())
        .filter(|&(_, h)| h)
        .map(|(mut idx, _)| {
            (radii.iter())
                .map(|&r| {
                    let v = idx % r;
                    idx /= r;
                    v
                })
                .collect()
        })
        .collect()
}

/// The values [`solve_by_sums`] walks for block `b`'s `W_b`, and their cost in steps, in
/// saturating words: for a block of one row `i`, `min(m_b, sum over its intervals of
/// min(hi - lo + 1, M))` values of its remainder, a
/// word for each coordinate the row moves (at least 1), and one step for each of its `n_i`
/// intervals; for a block of several rows, every `t` in `0..m_b`, each row's remainder tested
/// against its `n_i` intervals and added to the coordinates it moves, and the row itself.
fn walk_of(
    b: &Block,
    allowed: &[ResidueSet],
    by_row: &[Vec<(usize, usize)>],
    m: u64,
) -> (u64, u64) {
    let m_b = word_or_max(&b.m);
    if let [i] = b.rows[..] {
        let n_i = allowed[i].len() as u64;
        // The walk steps at most `min(hi - lo + 1, M)` times in each interval (XR-presburger4
        // round 4 TASTE, Claude P-6: `n_i M` overcharged short intervals).
        let v = (allowed[i].iter())
            .map(|(lo, hi)| word_or_max(&(&(hi - lo) + &Int::ONE)).min(m))
            .fold(0u64, u64::saturating_add)
            .min(m_b);
        let walk = (v.saturating_mul(by_row[i].len().max(1) as u64)).saturating_add(n_i);
        (v, walk)
    } else {
        let per: u64 = (b.rows.iter())
            .map(|&i| (allowed[i].len() + by_row[i].len() + 1) as u64)
            .fold(0u64, u64::saturating_add);
        (m_b, m_b.saturating_mul(per))
    }
}

/// The steps of reading the literals at `reached` tuples, in saturating words: each tuple's `j`
/// live sums and its `n_lits` literals, the literals once, `n_lits` more, and the walk of `f`
/// that built them, `n_all` constraints.
fn literal_cost(reached: u64, j: usize, n_lits: u64, n_all: u64) -> u64 {
    (reached.saturating_mul((j as u64).saturating_add(n_lits)))
        .saturating_add(n_lits)
        .saturating_add(n_all)
}
