//! A one-variable formula whose constraints read the quotients of its rows beside the variable
//! and the remainders (FAIL-omega-pairs-4972743790605253739): [`solve`] in `scaled.rs` declines
//! a constraint of two or more terms that names a quotient or a remainder, and the general path
//! then refuses some such formulas for `Growth`, as the quotients have no bound. Here the
//! variable is swept over one period of the rows' moduli, and at each residue every constraint
//! is a constraint on one integer `t`.
//!
//! No source is used: the identity below is elementary and is proved here.
//!
//! Lemma C (a period of the moduli makes every part linear). Let each row read
//! `q = sigma * floor((a x + k) / m)` and `r = (a x + k) mod m` ([`def_row`]), let `L` be the lcm
//! of the rows' moduli, and write `x = L t + s` with `0 <= s < L` (one `s` and one `t` for each
//! integer `x`, by Euclidean division). Then `a x + k = (a L / m) m t + (a s + k)`, and `a L / m`
//! is an integer as `m` divides `L`, so `floor((a x + k) / m) = (a L / m) t + floor((a s + k) / m)`
//! and `(a x + k) mod m = (a s + k) mod m`.
//! Proof. For an integer `j`, `floor((j m + e) / m) = j + floor(e / m)` and
//! `(j m + e) mod m = e mod m`; take `j = (a L / m) t` and `e = a s + k`. QED.
//! So at a fixed `s`, `x`, each quotient and each remainder is `alpha t + beta` with integers
//! `alpha`, `beta`, each constraint `sum c_i (alpha_i t + beta_i) + k0` is `A t + B` compared
//! with zero, and the integers `t` at which it holds are an interval (all of them, or none, when
//! `A = 0`; for an equation with `A != 0`, the one point `-B / A` when `A` divides `B`).
//!
//! Proof that `f` has a point exactly when some `s` gives a `t` in the set [`t_set`] computes
//! for `f`. (1) A point of `f` has some `x = L t + s`; by [`def_row`] (the definition rows are
//! top-level conjuncts and the remainders' bounds keep each in `[0, m - 1]`) every quotient and
//! remainder there is the value Lemma C gives, so each constraint has the truth value of its
//! interval at `t`, and the set of `f` holds `t` (the set of a conjunction is the meet of its
//! parts' sets, of a disjunction the union, of a negation the complement). (2) Given `s` and a
//! `t` in the set: [`point_at`] at `x = L t + s` sets every quotient and remainder to the values
//! Lemma C gives, every definition row then holds (a three-term row by construction; a two-term
//! row is a constraint of the formula, so its interval holds `t`, which says its remainder is
//! zero), and every constraint has the truth value of its interval at `t`, so `f` holds. QED.
//! A point found is rebuilt so and checked with [`Formula::holds`].
//!
//! The residue sweep above tests every `s < L`, and `L` grows as the product of the coprime
//! moduli. A second exact method (PRES-period-sweep-no-budget) tests far fewer points where the
//! constraints read the quotients mostly through `x`'s size:
//!
//! Lemma D (a constraint on `x` and the remainders alone). Let `M` be the lcm of the moduli of
//! the rows whose quotients a constraint `c` names. Substituting
//! `q_i = sigma_i (a_i x + k_i - r_i) / m_i` (exact, as `m_i` divides `a_i x + k_i - r_i`) and
//! multiplying by `M > 0` turns `c` into `G x + E + h`, compared with zero as `c` is, where
//! `h = sum R_i r_i`, `G = M c_x + sum c_qi sigma_i a_i (M / m_i)`,
//! `E = M k0 + sum c_qi sigma_i k_i (M / m_i)` and `R_i = M c_ri - c_qi sigma_i (M / m_i)`, and
//! `r_i = (a_i x + k_i) mod m_i` lies in `[0, m_i - 1]` for every row, whether or not the formula
//! names it ([`x_form`]). Multiplying by `M > 0` keeps the sign and zero-ness. QED.
//! So `h` lies in `[lo, hi]`, `lo = sum_{R_i < 0} R_i (m_i - 1)`,
//! `hi = sum_{R_i > 0} R_i (m_i - 1)`, and with `A = -E - hi` and `B = -E - lo - [c is >=]`:
//! - `G x < A` makes `c` false (`G x + E + h <= G x + E + hi < 0`);
//! - `G x > B` makes it true (`>= 0`: `G x + E + h >= G x + E + lo > -1`), or false for `==`
//!   (`> 0`, as `B = -E - lo` there);
//! - and `c`'s truth is open only for `G x` in `[A, B]`.
//!
//! Lemma E (the runs). For `G = 0`, `c` is constant when `A > 0` or `B < 0`, and otherwise
//! depends on `x` only through the remainders with `R_i != 0`, each periodic with period `m_i`;
//! let `L_P` be the lcm of those `m_i` over every such open constraint. For `G != 0`, `c` is
//! constant on each side of its window, the `x` with `G x` in `[A, B]` (`[ceil(A/G), floor(B/G)]`
//! for `G > 0`, the ends swapped for `G < 0`, widened to one point when it holds none). Then `f`
//! has a point iff one lies in the runs [`runs`] lists: every window, and in each gap between
//! the merged windows, and on each ray past them, the `L_P` points nearest the bounded end (all
//! of a shorter gap); with no window, `[0, L_P - 1]`.
//! Proof. A point inside a window is listed. On a gap or a ray every windowed constraint is
//! constant, every `G = 0` constraint is constant or a function of `x mod L_P` (each `r_i` is a
//! function of `x mod m_i`, and `m_i` divides `L_P`), so `f`'s truth at the point of `x`
//! ([`point_at`], whose rows hold by the proof of Lemma C above) is a function of `x mod L_P` on
//! that gap or ray; `L_P` consecutive integers meet every class, and a shorter gap is listed
//! whole. QED.
//! The runs hold at most `2 W + (W + 1) L_P` points for `W` the windows' total width, against
//! `L` for the residue sweep; `L_P` divides `L` and leaves out every modulus read only through
//! `x`'s size (a sum of quotients compared with a bound, as in
//! `tests::a_sum_of_quotients_past_the_old_bound_is_decided`).
//!
//! What neither method decides cheaply, and why no `O(n log n)` method is expected. The formulas
//! here hold, as the remainders of rows `x = p_i q_i + r_i` under `r_i != c_i`, every instance of
//! SIMULTANEOUS INCONGRUENCES: given pairs `(c_i, p_i)`, is there an `x` with `x !== c_i (mod
//! p_i)` for every `i`. That problem is NP-complete (M. R. Garey and D. S. Johnson, "Computers
//! and Intractability", W. H. Freeman, 1979, problem \[AN2\], credited there to L. J. Stockmeyer
//! and A. R. Meyer, "Word problems requiring exponential time", STOC 1973,
//! doi:10.1145/800125.804029). Cited from memory, 2026-11-23: the book and the paper were not
//! read here; the allpapers searches "incongruences", "congruences", "existential Presburger
//! one variable", "Presburger complexity" and two semantic queries returned nothing on
//! 2026-11-23, and the hits of "Presburger arithmetic" (250 papers) hold no one-variable
//! result; C. Haase, arXiv:1401.5266, Proposition 1 (LaTeX read, pa-wexp.tex:155), cites
//! Gr\"adel 1988 and Sch\"oning 1997 for `PA(i + 1, j)` with `j > 2` variables at the innermost
//! quantifier, which does not cover one variable. So, unless P = NP, no polynomial method
//! decides the class, and the two methods are exponential exactly where `L_P` (the incongruence
//! core) is: every modulus counted in `L_P` is read by an open constraint with `G = 0`, a
//! condition on remainders alone. The windows' width is the other cost: `W` grows as
//! `(hi - lo) / |G|`, pseudo-polynomial in the coefficients of the remainders against those of
//! `x` (unproved whether a method polynomial in their bits decides wide windows; the windows of
//! the tests are narrow). Past [`PERIOD_SWEEP_SWITCHOVER`] the formula goes to the general path
//! first, and to the sweep up to [`PERIOD_SWEEP_AFTER_REFUSAL_UNITS`] where that refuses.
//!
//! Tests: `tests::quotients_beside_the_variable_match_enumeration` (random formulas against
//! enumeration over the bounds), `tests::four_pairs_with_a_sum_of_their_quotients_are_decided`,
//! and end to end, in `l01_38_omega_test::one_scope`,
//! `four_pairs_of_one_symbol_and_a_sum_of_their_quotients_have_a_point` and
//! `the_unit_of_seed_4972743790605253739_is_answered_as_its_bodies_read`.

use super::*;
use zed_collections::intervals;

/// The count of units (the cheaper of the two methods' counts, [`solve_by`]) up to which [`solve`]
/// decides a formula before the general path is asked; past it the general path is asked first,
/// and the sweep only after it refuses ([`solve_after_refusal`]). Measured, not assumed
/// (PRES-period-sweep-no-budget, b22-presburger8, 2026-11-23, release build, one thread, Colab
/// VM hm4): 7,312 random formulas of `scaled::tests::random_part_literals` over one to four rows
/// (half the moduli primes from 11 to 113, half with a sum of the quotients equal to or at least
/// 1,000 to 1,000,000), each one `solve_modular_or_scaled` declines and whose count `U` is from
/// 500 to 5,000,000 (seed 4115099595012585212), each timed by the sweep alone and by the general
/// path without it. The two agree on every formula both decide; the general path refuses 345 of
/// them, at every size (31 with `U` under 1,000, 121 under 10^4, 111 under 10^5, 65 under 10^6,
/// 17 above), so with a refusal counted as infinite cost no switchover in the range sends the
/// formulas past it to the general path alone. With the sweep after a refusal, the total time by
/// switchover `T` (the sweep where `U <= T`, else the general path, and the sweep too where that
/// refuses) is: 512: 12.15 s; 4,096: 10.82 s; 16,384: 10.10 s; 32,768: 9.99 s; 65,536: 10.50
/// s; 262,144: 13.69 s; 1,048,576: 25.12 s; 4,194,304: 40.64 s; the sweep on every formula,
/// 42.96 s; 400,000 (`SWEEP_SWITCHOVER` of `modular.rs`, measured for another procedure, which
/// this module used before): 15.72 s, and with no sweep after a refusal, as before, 11.20 s with
/// 27 formulas refused. The minimum is flat from 16,384 to 65,536, and
/// 32,768 lies in it. The times were taken apart and summed (the general path's time to its
/// refusal plus the sweep's), not run in this order.
pub(crate) const PERIOD_SWEEP_SWITCHOVER: u128 = 32_768;

/// The count of units past which [`solve_after_refusal`] declines too, so the formula keeps the
/// general path's refusal. This is an allowance of work, not a switchover between methods of
/// equal output, so the standing rule (no limit but a measured switchover) does not allow it: it
/// stands in for the old `SWEEP_SWITCHOVER` (400,000) of `modular.rs`, past which this sweep
/// declined before, and is tracked under LIMITS-remove-all with row PRES-period-sweep-np-subclass,
/// which replaces it by a refusal of a class recognized from the formula. It makes no refusal of
/// its own: it is reached only after the general path refused, and every formula the sweep
/// answered before (at most 400,000 units) is within it. The count grows with `L_P` and the
/// windows' width (module note); past it the formula is in the class the module note shows
/// NP-hard (unless the windows are wide: unproved), but the count does not decide membership in
/// that class. 5,000,000 is the largest count measured with [`PERIOD_SWEEP_SWITCHOVER`]: no sweep
/// up to it took more than 946 ms (at `U` = 4,260,240), about 190 ns a unit.
pub(crate) const PERIOD_SWEEP_AFTER_REFUSAL_UNITS: u128 = 5_000_000;

/// A set of integers `t`: a normal list of closed intervals, `None` an unbounded end.
type TSet = Vec<(Option<Int>, Option<Int>)>;

/// [`solve_modular_or_scaled`]'s answer to `f`, or, when it declines, the period sweep's
/// ([`solve`]). The sweep runs only where both earlier solvers decline, so every formula they
/// accept is answered as before. This fallback is written here, not in `scaled.rs`, so that
/// `scaled.rs` names nothing of this file and the two files form no import cycle (test
/// `s_01f_import_graph`).
pub(crate) fn solve_modular_scaled_or_swept(
    f: &Formula,
    want_model: bool,
) -> Option<Option<Model>> {
    solve_modular_or_scaled(f, want_model).or_else(|| solve(f, want_model))
}

/// [`solve_by`] up to [`PERIOD_SWEEP_AFTER_REFUSAL_UNITS`] units, for a formula the general path
/// has refused (the checker's `decide_named` and `satisfiable_named` in `presburger.rs`): past
/// [`PERIOD_SWEEP_SWITCHOVER`] the general path is asked first, as it is the faster on most such
/// formulas (measured at [`PERIOD_SWEEP_SWITCHOVER`]), and this sweep answers what it refuses.
/// Test: `tests::a_formula_the_general_path_refuses_is_swept_past_the_switchover`.
pub(crate) fn solve_after_refusal(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    solve_by(
        f,
        want_model,
        Method::Cheaper,
        PERIOD_SWEEP_AFTER_REFUSAL_UNITS,
    )
}

/// Decides `f` by Lemma C (the residue sweep) or Lemma E (the runs), whichever counts fewer
/// units, or `None` when `f` is outside their shape or the cheaper costs more than
/// [`PERIOD_SWEEP_SWITCHOVER`] units. Shape: the top-level definition rows ([`read_shape`],
/// [`orient`]) are all on one variable `x` (no row on another row's quotient), and every
/// constraint names only `x` and the rows' quotients and remainders. It runs where
/// [`solve_modular`] and [`super::solve`] decline ([`solve_modular_scaled_or_swept`]).
// Complexity tradeoff: the residue sweep costs O(L * W) for `L` the lcm of the moduli and `W`
// the sizes of the sets folded at one residue (at most the constraints times the nodes of the
// formula, on a formula whose disjunctions keep many intervals); the runs cost O(P * N) for `P`
// their points (Lemma E, at most `2 W' + (W' + 1) L_P` for `W'` the windows' width) and `N` the
// formula's distinct nodes, after O(c log c) to sort the `c` windows. `L` and `L_P` may be
// exponential in the number of coprime moduli, and the class is NP-hard (module note), so no
// method is O(n log n) on all of it. Naive: none decides these formulas; before the sweep they
// went to the general path, which refused some (`Growth` on the row's four pairs at 7b58d316e;
// `Shadows` on 7 of 3000 random formulas of `tests::unbounded_quotient_formulas_agree_with_decide`
// at seed 16937151135935670534 on 2cf833851, none of them with the sweep). Used: the cheaper of
// the two counts, run when it stays within [`PERIOD_SWEEP_SWITCHOVER`] (measured for this
// module against the general path, at its definition); past it the formula goes to the general
// path, and where that refuses, to the sweep again up to [`PERIOD_SWEEP_AFTER_REFUSAL_UNITS`]
// ([`solve_after_refusal`]). Each unit is also charged to the question's meter
// (`meter::charge_pieces`). Under a meter (a question of the exact cover) the sweep runs first
// up to `SWEEP_SWITCHOVER` (400,000), as before this module had its own switchover: there a
// general path that spends the meter leaves the question refused, so the sweep after its
// refusal could not answer what the sweep first answered before (orchestrator, 2026-11-23: no
// formula answered before is refused now). Argument that the cover answers what it answered at
// 60267344b: there the residue sweep ran first where its count was at most 400,000; here the
// cheaper of two counts, no larger, so the same formulas are swept first, by a method whose
// whole count is no larger, and the rest go to the general path as there; the sweep after a
// refusal only adds answers. Unproved: that where the runs are the cheaper by count, they never
// spend the meter before a point that the residue sweep met early in its loop.
pub(super) fn solve(f: &Formula, want_model: bool) -> Option<Option<Model>> {
    let first = if super::super::super::meter::running() {
        super::super::SWEEP_SWITCHOVER
    } else {
        PERIOD_SWEEP_SWITCHOVER
    };
    solve_by(f, want_model, Method::Cheaper, first)
}

/// Which of the two exact methods [`solve_by`] runs: the cheaper by its count of units (as
/// [`solve`] does), or one of them whatever its cost (for the tests that check each against
/// the other).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Method {
    Cheaper,
    #[cfg(test)]
    Runs,
    #[cfg(test)]
    Residues,
}

/// [`solve`] by `method`, declining past `limit` units.
pub(super) fn solve_by(
    f: &Formula,
    want_model: bool,
    method: Method,
    limit: u128,
) -> Option<Option<Model>> {
    let conjuncts = f.conjunct_list();
    let top: Vec<&Con> = conjuncts
        .iter()
        .filter_map(|g| match g {
            Formula::Con(c) => Some(c),
            _ => None,
        })
        .collect();
    let bounds = one_term_bounds(&top);
    let shapes: Vec<Shape<'_>> = top.iter().filter_map(|c| read_shape(c, &bounds)).collect();
    if shapes.is_empty() {
        return None;
    }
    let (x, rows) = orient(&shapes, None)?;
    if rows.iter().any(|row| row.parent.is_some()) {
        return None;
    }
    // Each part's place: `x`, or the quotient or remainder of row `i`.
    let mut part: HashMap<&Atom, Part> = HashMap::with_capacity(2 * rows.len() + 1);
    part.insert(&x, Part::X);
    for (i, row) in rows.iter().enumerate() {
        part.insert(&row.q, Part::Q(i));
        if let Some(r) = &row.r {
            part.insert(r, Part::R(i));
        }
    }
    // A product atom declines, as in `scaled::solve` (META1 A1 of XR-presburger4): [`orient`]
    // never roots on a product, but a product can be a row's quotient or remainder, and the
    // sweep would give it a value of its own where [`Formula::holds`] reads it through its
    // factors (the test `the_sweep_leaves_a_product_quotient_to_the_general_path`).
    let mut cons = 0u64;
    let mut inside = true;
    f.walk(&mut |c| {
        cons += 1;
        inside &= c
            .lin
            .terms
            .keys()
            .all(|a| part.contains_key(a) && !matches!(a, Atom::Product(..)));
    });
    if !inside {
        return None;
    }
    let period = rows.iter().fold(Int::ONE, |p, row| p.lcm(&row.m));
    // The two exact methods, each at its cost in units: the points of the runs ([`runs`]), each
    // folding the formula's `nodes` distinct parts once, and the residue sweep, each residue
    // reading every constraint at least once (`period * cons`). The cheaper one runs; past
    // the switchover neither does.
    let (runs, points) = runs(f, &part, &rows);
    let mut nodes = 0u64;
    f.fold((), |_, ()| (), |_, (), _: Vec<()>| nodes += 1);
    let tested = &points * &Int::from(nodes as i64);
    let swept = &period * &Int::from(cons as i64);
    // Both limits are far below `i128::MAX`.
    let switchover = Int::from(limit as i128);
    let by_runs = match method {
        Method::Cheaper => tested < swept,
        #[cfg(test)]
        Method::Runs => true,
        #[cfg(test)]
        Method::Residues => false,
    };
    if by_runs {
        if tested > switchover {
            return None;
        }
        return search_runs(f, &part, &rows, &x, &runs, nodes, want_model);
    }
    if swept > switchover {
        return None;
    }
    let mut spent: u128 = 0;
    let mut s = Int::ZERO;
    while s < period {
        let at = parts_at(&rows, &period, &s);
        let mut made: u128 = 0;
        let set = t_set(f, &part, &at, &mut made);
        spent += made;
        if spent > limit {
            return None;
        }
        if super::super::super::meter::charge_pieces(u64::try_from(made).unwrap_or(u64::MAX))
            .is_err()
        {
            return None;
        }
        if let Some(t) = set
            .first()
            .map(|(lo, hi)| lo.clone().or_else(|| hi.clone()).unwrap_or(Int::ZERO))
        {
            if !want_model {
                return Some(Some(Model::new()));
            }
            let v = &(&period * &t) + &s;
            let model = point_at(&rows, &x, &v);
            // By (2) of the proof this is a point of `f`; a failure here is a defect of this
            // module, and declining leaves `f` to the general path.
            let holds = f.holds(&model);
            debug_assert!(holds, "the point at x = {v} is not one of\n{f}");
            return holds.then_some(Some(model));
        }
        s = &s + &Int::ONE;
    }
    Some(None)
}

/// `(alpha, beta)` of `x` and of each row's quotient and remainder at residue `s`, by Lemma C:
/// `x = L t + s`, `q = sigma ((a L / m) t + floor((a s + k) / m))`, `r = (a s + k) mod m`.
/// Entry `0` is `x`; entries `1 + 2 i` and `2 + 2 i` are row `i`'s quotient and remainder.
fn parts_at(rows: &[DefRow<'_>], period: &Int, s: &Int) -> Vec<(Int, Int)> {
    let mut at = Vec::with_capacity(1 + 2 * rows.len());
    at.push((period.clone(), s.clone()));
    for row in rows {
        let e = &(&row.a * s) + &row.k;
        let fl = e.div_floor(&row.m);
        let slope = (&row.a * period).div_floor(&row.m);
        let rem = &e - &(&row.m * &fl);
        at.push(if row.sigma > 0 {
            (slope, fl)
        } else {
            (-&slope, -&fl)
        });
        at.push((Int::ZERO, rem));
    }
    at
}

/// The integers `t` at which `f` holds at the residue `at` was made for, folded from the
/// constraints up ([`Formula::fold`], a shared part once); `made` counts the constraints read
/// and the intervals made.
fn t_set(f: &Formula, part: &HashMap<&Atom, Part>, at: &[(Int, Int)], made: &mut u128) -> TSet {
    f.fold(
        (),
        |_, ()| (),
        |g, (), parts: Vec<TSet>| {
            let out = match g {
                Formula::Con(c) => con_set(c, part, at),
                Formula::Not(_) => intervals::complement_spans(&parts[0]),
                Formula::And(_) => {
                    let mut it = parts.into_iter();
                    let first = it.next().unwrap_or_else(|| vec![(None, None)]);
                    it.fold(first, |acc, p| intervals::intersect(&acc, &p))
                }
                Formula::Or(_) => parts
                    .into_iter()
                    .fold(Vec::new(), |acc, p| intervals::union(&acc, &p)),
                Formula::Holes(_) => unreachable!("`fold` reads a call node as its clauses"),
            };
            *made += 1 + out.len() as u128;
            out
        },
    )
}

/// The integers `t` at which the constraint `c` holds: `A t + B >= 0` or `== 0`.
fn con_set(c: &Con, part: &HashMap<&Atom, Part>, at: &[(Int, Int)]) -> TSet {
    let (mut a, mut b) = (Int::ZERO, c.lin.constant.clone());
    for (atom, k) in &c.lin.terms {
        let (alpha, beta) = match part[atom] {
            Part::X => &at[0],
            Part::Q(i) => &at[1 + 2 * i],
            Part::R(i) => &at[2 + 2 * i],
        };
        a = &a + &(k * alpha);
        b = &b + &(k * beta);
    }
    let all = || vec![(None, None)];
    match c.rel {
        Rel::Ge if a.is_zero() => {
            if b.is_negative() {
                Vec::new()
            } else {
                all()
            }
        }
        // `A t >= -B`.
        Rel::Ge if a.is_positive() => vec![(Some((-&b).div_ceil(&a)), None)],
        Rel::Ge => vec![(None, Some(b.div_floor(&-&a)))],
        Rel::Eq if a.is_zero() => {
            if b.is_zero() {
                all()
            } else {
                Vec::new()
            }
        }
        Rel::Eq => {
            if b.mod_floor(&a.abs()).is_zero() {
                let t = (-&b).div_floor(&a);
                vec![(Some(t.clone()), Some(t))]
            } else {
                Vec::new()
            }
        }
    }
}

/// The constraint `c` read on `x` and the remainders alone, Lemma D at the module note:
/// `(G, E, R)` such that, at the point of every `x` ([`point_at`]), `M` times the value of
/// `c`'s term is `G x + E + sum R_i r_i` for one integer `M >= 1`, with `r_i = (a_i x + k_i)
/// mod m_i` the remainder of row `i` (whether or not the row names it). `R` lists each row
/// once, by index, with a nonzero coefficient. O(terms) arithmetic operations.
fn x_form(
    c: &Con,
    part: &HashMap<&Atom, Part>,
    rows: &[DefRow<'_>],
) -> (Int, Int, Vec<(usize, Int)>) {
    let mut m = Int::ONE;
    for a in c.lin.terms.keys() {
        if let Part::Q(i) = part[a] {
            m = m.lcm(&rows[i].m);
        }
    }
    let (mut g, mut e) = (Int::ZERO, &m * &c.lin.constant);
    let mut r: HashMap<usize, Int> = HashMap::new();
    for (a, k) in &c.lin.terms {
        match part[a] {
            Part::X => g = &g + &(&m * k),
            Part::R(i) => {
                let ri = r.entry(i).or_insert(Int::ZERO);
                *ri = &*ri + &(&m * k);
            }
            // `M k q = (sigma k M / m_i) (a_i x + k_i - r_i)`.
            Part::Q(i) => {
                let row = &rows[i];
                let s = &(k * &m.div_floor(&row.m)) * &Int::from(i64::from(row.sigma));
                g = &g + &(&s * &row.a);
                e = &e + &(&s * &row.k);
                let ri = r.entry(i).or_insert(Int::ZERO);
                *ri = &*ri - &s;
            }
        }
    }
    let mut r: Vec<(usize, Int)> = r.into_iter().filter(|(_, v)| !v.is_zero()).collect();
    r.sort_unstable_by_key(|(i, _)| *i);
    (g, e, r)
}

/// The runs of `x` that [`search_runs`] tests, ascending and disjoint, and their count of
/// points: every window of a constraint whose `G` is not zero, and in each gap between the
/// windows (and past the first and the last) the first `L_P` points from the gap's bounded end
/// (or all of the gap when it is shorter), with `L_P` the lcm of the moduli of the rows that the
/// constraints with `G = 0` read and whose truth the remainders' ranges do not fix; with no
/// window, `[0, L_P - 1]`. Exactness is Lemma E at the module note. O(c log c) for `c`
/// constraints, the sort of the windows, and O(terms) for the forms.
fn runs(f: &Formula, part: &HashMap<&Atom, Part>, rows: &[DefRow<'_>]) -> (Vec<(Int, Int)>, Int) {
    let mut windows: Vec<(Int, Int)> = Vec::new();
    let mut lp = Int::ONE;
    f.walk(&mut |c| {
        let (g, e, r) = x_form(c, part, rows);
        // `h = sum R_i r_i` lies in `[lo, hi]`, as each `r_i` lies in `[0, m_i - 1]`.
        let (mut lo, mut hi) = (Int::ZERO, Int::ZERO);
        for (i, ri) in &r {
            let span = ri * &(&rows[*i].m - &Int::ONE);
            if ri.is_negative() {
                lo = &lo + &span;
            } else {
                hi = &hi + &span;
            }
        }
        // The truth of `G x + E + h >= 0` (or `== 0`) is not fixed by the range of `h` only
        // where `G x` lies in `[a, b]`.
        let a = &(-&e) - &hi;
        let b = &(&(-&e) - &lo) - &Int::from(i64::from(c.rel == Rel::Ge));
        if g.is_zero() {
            if !a.is_positive() && !b.is_negative() {
                for (i, _) in &r {
                    lp = lp.lcm(&rows[*i].m);
                }
            }
            return;
        }
        let (w1, w2) = if g.is_positive() {
            (a.div_ceil(&g), b.div_floor(&g))
        } else {
            (b.div_ceil(&g), a.div_floor(&g))
        };
        let w2 = w2.max(w1.clone());
        windows.push((w1, w2));
    });
    let windows = intervals::coalesce(windows);
    let one = Int::ONE;
    let mut out: Vec<(Int, Int)> = Vec::with_capacity(2 * windows.len() + 1);
    match (windows.first(), windows.last()) {
        (Some(first), Some(last)) => {
            out.push((&first.0 - &lp, &first.0 - &one));
            for (j, w) in windows.iter().enumerate() {
                out.push(w.clone());
                if let Some(next) = windows.get(j + 1) {
                    // `coalesce` joins touching windows, so this gap holds a point.
                    let a = &w.1 + &one;
                    let b = (&next.0 - &one).min(&(&a + &lp) - &one);
                    out.push((a, b));
                }
            }
            out.push((&last.1 + &one, &last.1 + &lp));
        }
        _ => out.push((Int::ZERO, &lp - &one)),
    }
    let points = out
        .iter()
        .fold(Int::ZERO, |n, (a, b)| &(&n + b) - &(a - &one));
    (out, points)
}

/// Tests each point of `runs` in order ([`runs`], Lemma E); the first point of `f` found, or
/// `Some(None)` when none is one. Each point costs `nodes` units, charged to the question's
/// meter; `None` when the meter is spent, or (a defect of this module) when the point rebuilt
/// is not one of `f`.
fn search_runs(
    f: &Formula,
    part: &HashMap<&Atom, Part>,
    rows: &[DefRow<'_>],
    x: &Atom,
    runs: &[(Int, Int)],
    nodes: u64,
    want_model: bool,
) -> Option<Option<Model>> {
    for (a, b) in runs {
        let mut v = a.clone();
        while &v <= b {
            if super::super::super::meter::charge_pieces(nodes).is_err() {
                return None;
            }
            let at = parts_at(rows, &Int::ZERO, &v);
            if holds_at(f, part, &at) {
                if !want_model {
                    return Some(Some(Model::new()));
                }
                let model = point_at(rows, x, &v);
                let holds = f.holds(&model);
                debug_assert!(holds, "the point at x = {v} is not one of\n{f}");
                return holds.then_some(Some(model));
            }
            v = &v + &Int::ONE;
        }
    }
    Some(None)
}

/// Whether `f` holds where `x` and each quotient and remainder take the second values of `at`
/// ([`parts_at`] at `t = 0`): one fold, a shared part once.
fn holds_at(f: &Formula, part: &HashMap<&Atom, Part>, at: &[(Int, Int)]) -> bool {
    f.fold(
        (),
        |_, ()| (),
        |g, (), parts: Vec<bool>| match g {
            Formula::Con(c) => {
                let mut v = c.lin.constant.clone();
                for (atom, k) in &c.lin.terms {
                    let i = match part[atom] {
                        Part::X => 0,
                        Part::Q(i) => 1 + 2 * i,
                        Part::R(i) => 2 + 2 * i,
                    };
                    v = &v + &(k * &at[i].1);
                }
                if c.rel == Rel::Eq {
                    v.is_zero()
                } else {
                    !v.is_negative()
                }
            }
            Formula::Not(_) => !parts[0],
            Formula::And(_) => parts.iter().all(|&p| p),
            Formula::Or(_) => parts.iter().any(|&p| p),
            Formula::Holes(_) => unreachable!("`fold` reads a call node as its clauses"),
        },
    )
}
