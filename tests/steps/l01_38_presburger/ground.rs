//! Constraints with no atom, such as `0 == 0` and its negation `-1 >= 0`, inside a disjunct
//! nested below another (PRESBURGER-or-if-disjuncts-refusal).

use super::nest_empty::v;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide};

/// `Σ c·a + k`, with `q<n>` the auxiliary atom `n`, as the preimage stage names them.
fn lin(t: &[(&str, i64)], k: i64) -> Lin {
    (t.iter()).fold(Lin::constant(k), |l, (a, c)| {
        let atom = match a.strip_prefix('q') {
            Some(n) => Atom::Aux(n.parse().expect("a number")),
            None => v(a),
        };
        l.plus(&Lin::atom(atom).times(*c))
    })
}

/// `l >= 0`.
fn ge(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::ge(&lin(t, k), &Lin::constant(0)))
}

/// `l == 0`.
fn eq(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::eq(&lin(t, k), &Lin::constant(0)))
}

fn and(fs: Vec<Formula>) -> Formula {
    Formula::and(fs)
}

fn or(fs: Vec<Formula>) -> Formula {
    Formula::or(fs)
}

fn not(f: Formula) -> Formula {
    Formula::negate(f)
}

/// The exactness question of round 0 of seed 10347845748276606162 of
/// `zedc_preimage`'s `or_ifs_hold_where_they_held_as_ifs`, for the demand `false` with
/// `if g { true } else { b }` read as `g || b`, made smaller with no point and the refusal kept.
/// `0 == 0` is the comparison `v + 2 != 2 + v` of two equal sums, and `0 >= 0` one like it.
/// The first two disjuncts are kept whole as one disjunction, and `0 >= 0 && x >= 0` as one
/// conjunction, as the translator keeps the formula of a name (`Formula::and_keeping`); written
/// flat, the question was decided before the fix too. `with_ground` false writes each
/// constraint with no atom as `true` or `false` instead.
fn seed_question(with_ground: bool) -> Formula {
    let zero = |holds: bool| match (with_ground, holds) {
        (true, true) => eq(&[], 0),
        (true, false) => not(eq(&[], 0)),
        (false, true) => Formula::top(),
        (false, false) => Formula::bottom(),
    };
    let guard = or(vec![
        ge(&[("x", 1), ("y", -1)], -1),
        ge(&[("x", -1)], -6),
        ge(&[("x", 1)], -3),
    ]);
    let at_least_zero = if with_ground {
        ge(&[], 0)
    } else {
        Formula::top()
    };
    let ground = and(vec![at_least_zero, ge(&[("x", 1)], 0)]);
    let q3 = || eq(&[("q3", 1)], 0);
    let x_q0 = || eq(&[("x", -1), ("q0", -1)], 0);
    let y_zero = || eq(&[("y", 1)], 0);
    let first_two = or(vec![
        and(vec![y_zero(), zero(false), x_q0()]),
        and(vec![not(y_zero()), not(and(vec![zero(false), x_q0()]))]),
    ]);
    let both = Formula::and_keeping(vec![guard.clone(), ground.clone(), q3()], |i| i == 1);
    let neither = and(vec![
        not(guard),
        not(Formula::and_keeping(vec![ground, q3()], |i| i == 0)),
    ]);
    and(vec![
        eq(&[("y", -2), ("q1", 1)], 0),
        eq(&[("q2", 1)], 1),
        eq(&[("x", -1), ("q3", 1)], 0),
        ge(&[("x", 1)], 0),
        ge(&[("y", 1)], 0),
        ge(&[("y", -1)], 0),
        Formula::or_keeping(
            vec![
                first_two,
                ge(&[("y", 1)], -1),
                eq(&[("q2", 1)], -2),
                and(vec![
                    not(or(vec![ge(&[("y", 1)], -1), eq(&[("q2", 1)], -2)])),
                    eq(&[("x", -2), ("q3", 1)], -4),
                ]),
                and(vec![or(vec![both, neither]), ge(&[("x", -2)], 2)]),
            ],
            |i| i == 0,
        ),
    ])
}

#[test]
fn a_disjunct_false_by_a_constraint_with_no_atom_two_levels_down_is_left_out() {
    // Before the fix `-1 >= 0` (the negation of `0 == 0`) was kept as a constraint of its
    // disjunct, read by no bound of the disjunction above it, and the search was refused.
    assert_eq!(decide(&seed_question(true)), Ok(false));
}

#[test]
fn the_seed_question_with_its_ground_constraints_written_as_constants_is_decided_alike() {
    // Control: decided before the fix too.
    assert_eq!(decide(&seed_question(false)), Ok(false));
}

/// `x == 0 && y == 0 && (y >= 1 || (x >= 0 && ((g && x == 0) || y >= 1)))`: a point exactly
/// when `g` holds, `g` two levels down. `kept`: `x == 0 && y == 0 && ((g && x == 0 || y >= 1)
/// || y >= 1)` instead, the inner disjunction kept whole as one disjunct of the outer one
/// (`Formula::or_keeping`), as in the seed's question.
fn nested(g: Formula, kept: bool) -> Formula {
    let inner = or(vec![and(vec![g, eq(&[("x", 1)], 0)]), ge(&[("y", 1)], -1)]);
    let outer = if kept {
        Formula::or_keeping(vec![inner, ge(&[("y", 1)], -1)], |i| i == 0)
    } else {
        or(vec![
            ge(&[("y", 1)], -1),
            and(vec![ge(&[("x", 1)], 0), inner]),
        ])
    };
    and(vec![eq(&[("x", 1)], 0), eq(&[("y", 1)], 0), outer])
}

#[test]
fn constraints_with_no_atom_decide_their_disjunct_on_both_sides_of_zero() {
    // `k >= 0` holds from 0 up, `k == 0` at 0 alone; each beside its `true` or `false`.
    for k in -2..=2 {
        let cases = [(ge(&[], k), k >= 0), (eq(&[], k), k == 0)];
        for ((g, holds), kept) in cases
            .into_iter()
            .flat_map(|c| [(c.clone(), false), (c, true)])
        {
            let shown = format!("{g}, kept {kept}");
            assert_eq!(decide(&nested(g, kept)), Ok(holds), "{shown}");
            let constant = if holds {
                Formula::top()
            } else {
                Formula::bottom()
            };
            let as_constant = decide(&nested(constant, kept));
            assert_eq!(as_constant, Ok(holds), "{shown} as a constant");
        }
    }
}

#[test]
fn a_constraint_with_no_atom_at_the_top_or_in_every_disjunct_decides_the_formula() {
    let x = || ge(&[("x", 1)], 0);
    assert_eq!(decide(&and(vec![ge(&[], -1), x()])), Ok(false));
    assert_eq!(decide(&and(vec![eq(&[], 0), x()])), Ok(true));
    let all_false = or(vec![
        and(vec![ge(&[], -1), x()]),
        and(vec![eq(&[], 3), ge(&[("x", -1)], 0)]),
    ]);
    assert_eq!(decide(&and(vec![all_false, x()])), Ok(false));
    // A disjunct true by `0 == 0` alone makes its disjunction hold.
    let one_true = or(vec![eq(&[], 0), eq(&[], 1)]);
    let f = and(vec![one_true, x(), ge(&[("x", -1)], 0)]);
    assert_ne!(decide(&f), Err(Refusal::Disjuncts));
    assert_eq!(decide(&f), Ok(true));
}
