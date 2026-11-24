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
//! Tests: `tests::quotients_beside_the_variable_match_enumeration` (random formulas against
//! enumeration over the bounds), `tests::four_pairs_with_a_sum_of_their_quotients_are_decided`,
//! and end to end `l01_38_omega_test::one_scope::four_pairs_of_one_symbol_and_a_sum_of_their_quotients_have_a_point`
//! and `one_scope::the_unit_of_seed_4972743790605253739_is_answered_as_its_bodies_read`.

use super::*;
use zed_collections::intervals;

/// A set of integers `t`: a normal list of closed intervals, `None` an unbounded end.
type TSet = Vec<(Option<Int>, Option<Int>)>;

/// Decides `f` by Lemma C, or `None` when `f` is outside its shape or the sweep would cost more
/// than [`SWEEP_SWITCHOVER`] units. Shape: the top-level definition rows ([`read_shape`],
/// [`orient`]) are all on one variable `x` (no row on another row's quotient), and every
/// constraint names only `x` and the rows' quotients and remainders. It runs where
/// [`solve_modular`] and [`super::solve`] decline ([`solve_modular_or_scaled`]).
// Complexity tradeoff: the sweep costs O(L * W) for `L` the lcm of the moduli and `W` the sizes
// of the sets folded at one residue (at most the constraints times the nodes of the formula, on
// a formula whose disjunctions keep many intervals), and `L` may be exponential in the number of
// coprime moduli. Naive: none decides these formulas; before, they went to the general path,
// which refused some (`Growth` on the row's four pairs at 7b58d316e; `Shadows` on 7 of 3000
// random formulas of `tests::unbounded_quotient_formulas_agree_with_decide` at seed
// 16937151135935670534 on 2cf833851, none of them with the sweep). Used: the sweep where its count of units (constraints read and
// intervals made, over every residue) stays within [`SWEEP_SWITCHOVER`], the switchover this
// module measured for its residue sweep (at its definition); past it the formula goes to the
// general path as before, so no answer given before changes. Not measured for this sweep: the
// cost of one unit here (one interval made or one constraint read, each a few `Int` operations)
// is taken to be near that of a residue piece there, by the kind of work, not by a measurement.
// Each unit is also charged to the question's meter (`meter::charge_pieces`).
pub(super) fn solve(f: &Formula, want_model: bool) -> Option<Option<Model>> {
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
    let mut cons = 0u64;
    let mut inside = true;
    f.walk(&mut |c| {
        cons += 1;
        inside &= c.lin.terms.keys().all(|a| part.contains_key(a));
    });
    if !inside {
        return None;
    }
    let period = rows.iter().fold(Int::ONE, |p, row| p.lcm(&row.m));
    // Each residue reads every constraint at least once, so `period * cons` units are spent
    // before any set is made; past the switchover the sweep is not started.
    let budget = Int::from(SWEEP_SWITCHOVER as i64);
    if &period * &Int::from(cons as i64) > budget {
        return None;
    }
    let mut spent: u128 = 0;
    let mut s = Int::ZERO;
    while s < period {
        let at = parts_at(&rows, &period, &s);
        let mut made: u128 = 0;
        let set = t_set(f, &part, &at, &mut made);
        spent += made;
        if spent > SWEEP_SWITCHOVER {
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
