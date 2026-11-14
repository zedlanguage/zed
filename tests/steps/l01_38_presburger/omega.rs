//! The Omega test's corner cases: each cause of a refusal with its own message, values past
//! `i128`, equalities with no unit coefficient, opposite rows that meet, and an answer that does
//! not depend on the order of the constraints.

use std::sync::Arc;

use zed_tests::{instances::Rng, scaling};
use zedc::store::int::Int;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{
    Atom, Con, Entailment, Formula, Lin, Refusal, Relation, Shared, decide, entails, project,
    project_each, row_box, satisfiable,
};

fn sym(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

/// `Σ c·s + k`.
fn lin(terms: &[(&str, i128)], k: i128) -> Lin {
    terms.iter().fold(Lin::constant(k), |l, (s, c)| {
        l.plus(&Lin::atom(sym(s)).times(*c))
    })
}

fn ge(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::ge(&lin(terms, k), &Lin::constant(0)))
}

fn eq(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::eq(&lin(terms, k), &Lin::constant(0)))
}

#[test]
fn a_ledger_equation_with_no_unit_coefficient_is_solved() {
    // Pugh's example: 7a + 12b + 31c == 17 and 3a + 5b + 14c == 7, with a in 1..=40 and b in
    // -50..=50, has integer points, reached through his symmetric remainder.
    let f = Formula::and(vec![
        eq(&[("a", 7), ("b", 12), ("c", 31)], -17),
        eq(&[("a", 3), ("b", 5), ("c", 14)], -7),
        ge(&[("a", 1)], -1),
        ge(&[("a", -1)], 40),
        ge(&[("b", 1)], 50),
        ge(&[("b", -1)], 50),
    ]);
    let m = satisfiable(&f).unwrap().expect("a point");
    assert!(f.holds(&m), "{m:?}");
    // 6 boxes and 10 crates hold an even count; 6a + 10b == 7 has no point at all.
    assert_eq!(satisfiable(&eq(&[("a", 6), ("b", 10)], -7)), Ok(None));
    // With a third size of 15 every count can be reached, again without a unit coefficient.
    let g = eq(&[("a", 6), ("b", 10), ("c", 15)], -7);
    let m = satisfiable(&g).unwrap().expect("a point");
    assert!(g.holds(&m), "{m:?}");
}

#[test]
fn opposite_rows_meet_in_an_equality_or_nowhere() {
    // Rent split so that 3 shares and 5 extras are at least and at most 7: exactly 7.
    let f = Formula::and(vec![
        ge(&[("s", 3), ("e", 5)], -7),
        ge(&[("s", -3), ("e", -5)], 7),
        ge(&[("e", 1)], 0),
    ]);
    let m = satisfiable(&f).unwrap().expect("a point");
    assert!(f.holds(&m), "{m:?}");
    // Meeting at a value the coefficients cannot reach: 2x == 1.
    let f = Formula::and(vec![ge(&[("x", 2)], -1), ge(&[("x", -2)], 1)]);
    assert_eq!(satisfiable(&f), Ok(None));
    // Crossing: x >= 3 and x <= 2.
    let f = Formula::and(vec![ge(&[("x", 1)], -3), ge(&[("x", -1)], 2)]);
    assert_eq!(satisfiable(&f), Ok(None));
}

/// `3·x[i+1] >= 2·x[i] + 1` and `2·x[i] + 3 >= 3·x[i+1]`, with `x[v] >= 4`, which holds only
/// with values growing by half at each step back from the last. (Without `x[v] >= 4` every
/// `x[i]` may be 1, 2 or 3; only the order of the eliminations gave large values.)
fn growing(v: usize) -> Formula {
    let name = |i: usize| format!("x{i}");
    let last = name(v);
    let floor = ge(&[(last.as_str(), 1)], -4);
    let rows = (0..v).flat_map(|i| {
        let (a, b) = (name(i), name(i + 1));
        [
            ge(&[(b.as_str(), 3), (a.as_str(), -2)], -1),
            ge(&[(a.as_str(), 2), (b.as_str(), -3)], 3),
        ]
    });
    Formula::and(rows.chain([floor]).collect())
}

#[test]
fn a_model_may_hold_values_past_128_bits() {
    let f = growing(1024);
    let m = satisfiable(&f).unwrap().expect("a point");
    assert!(f.holds(&m));
    assert!(m.values().any(|v| v.to_i128().is_none()));
    // The projection is read through such a point; its bounds lie past `i64`, as no bound.
    let hull = project(&f, &sym("x0")).unwrap();
    assert!(hull.bounds().is_some(), "{hull:?}");
}

#[test]
fn a_bound_past_i64_is_exact() {
    // `2^70 <= x <= 2^70 + 5`: both ends lie past the 64-bit range, and the hull is exact.
    let v = 1i128 << 70;
    let f = Formula::and(vec![ge(&[("x", 1)], -v), ge(&[("x", -1)], v + 5)]);
    let hull = project(&f, &sym("x")).unwrap();
    assert_eq!(
        hull,
        IntervalSet::range(End::Fin(Num::from(v)), End::Fin(Num::from(v + 5)))
    );
    assert_eq!(
        hull.to_string(),
        "[1180591620717411303424..=1180591620717411303429]"
    );
}

/// `a != b`, as a disjunction.
fn differ(a: &str, b: &str) -> Formula {
    Formula::or(vec![ge(&[(a, 1), (b, -1)], -1), ge(&[(b, 1), (a, -1)], -1)])
}

#[test]
fn each_cause_of_a_refusal_has_its_own_message() {
    let refused = |f: Formula, why: Refusal, text: &str| {
        assert_eq!(satisfiable(&f), Err(why.clone()));
        let e = entails(&Relation::of(f), &Relation::of(Formula::bottom()));
        assert_eq!(e, Entailment::Refused(why));
        assert_eq!(e.to_string(), format!("refused: {text}"));
    };
    // Every elimination of each variable adds terms, no row is below zero over the box of the
    // bounds, and each of the five points of that box that the box stage tries misses a row.
    refused(
        Formula::and(vec![
            ge(&[("x", 4), ("w", -12), ("y", -10), ("z", -12)], 11),
            ge(&[("w", 4), ("x", 10), ("y", -10), ("z", -11)], -28),
            ge(&[("w", 11), ("x", 4), ("y", -1), ("z", 12)], -28),
            ge(&[("w", -8), ("x", -5), ("y", 12), ("z", -1)], 31),
        ]),
        Refusal::Growth,
        "to find whole numbers that meet these conditions, the checker removes one variable \
         at a time, putting in place of the conditions on it conditions on the variables left. \
         Here four variables or more are left, and removing any one of them would leave more \
         conditions than there are now, so the work could grow without end. The checker \
         stopped there, with no values found and none ruled out",
    );
    // A splinter of the dark elimination takes a dark shadow of its own that has no point,
    // over four live variables, as many as the elimination it came from: splitting it again
    // adds a variable for each it removes and need not end (it ran 41 levels deep, the rows
    // growing from 8 to 992). With three, `live3` decides the splinter's gray shadow.
    refused(
        Formula::and(vec![
            ge(&[("x", 9), ("y", -4), ("w", -8)], -3),
            ge(&[("x", 5), ("y", 11), ("w", 9)], -9),
            ge(&[("x", -7), ("y", -12), ("z", -2), ("w", 8)], -1),
            ge(&[("x", -9), ("y", 8), ("z", 7)], 0),
            ge(&[("x", -10), ("y", 4), ("z", -6), ("w", -4)], 22),
        ]),
        Refusal::Shadows,
        "to find whole numbers that meet these conditions, the checker removes one variable \
         at a time, putting in place of the conditions on it conditions on the variables left. \
         Where the values a variable can take have gaps, it splits the conditions into cases, \
         one for each gap. Here the only values could lie in a case that would have to be \
         split again with as many variables left as before, so the splitting need not end. The \
         checker stopped there, with no values found and none ruled out",
    );
    // Four tasks, three slots, each pair in different slots: no slot assignment, which the
    // search through the disjunctions does not show by propagation. Each task has a row of
    // its own, with a coefficient of its own, that `t >= 0` implies, so that the structure
    // tells the tasks apart.
    let tasks = ["a", "b", "c", "d"];
    let pigeons = |apart: bool| {
        let mut rows = Vec::new();
        for (i, t) in tasks.iter().enumerate() {
            rows.push(ge(&[(t, 1)], 0));
            rows.push(ge(&[(t, -1)], 2));
            if apart {
                rows.push(ge(&[(t, 2 + i as i128)], 1));
            }
            rows.extend(tasks[..i].iter().map(|s| differ(s, t)));
        }
        Formula::and(rows)
    };
    refused(
        pigeons(true),
        Refusal::Disjuncts,
        "the conditions hold alternatives, where one of several cases is enough (from `||`, \
         from `!=`, which holds when either side is the larger, or from a negated `&&`), and \
         the checker looks for a choice of one case from each alternative that can hold with \
         the rest; no choice it tried has values that meet every condition, and it could rule \
         out none of the cases. The checker stopped there, with no values found and none ruled \
         out",
    );
    // With no such rows the tasks occur alike, so the search would take them in an order
    // chosen by name, and the disjunctions left are named.
    let Err(why @ Refusal::Unordered(_)) = satisfiable(&pigeons(false)) else {
        panic!("the tied tasks are refused for their order");
    };
    let e = entails(
        &Relation::of(pigeons(false)),
        &Relation::of(Formula::bottom()),
    );
    assert_eq!(e, Entailment::Refused(why));
    let text = e.to_string();
    assert!(
        text.starts_with(
            "refused: the conditions hold alternatives, where one of several cases is enough"
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "and the variables `a`, `b`, `c`, `d` occur alike in them (with the same \
             coefficients, in conditions that are alike), so only their names could order the \
             search"
        ),
        "{text}"
    );
}

#[test]
fn a_box_every_elimination_of_which_would_add_terms_is_answered() {
    // x has 2 lower and 3 upper bounds and y 2 and 3, around the origin.
    let f = Formula::and(vec![
        ge(&[("x", 1), ("y", -1)], 100),
        ge(&[("x", 1), ("y", -2)], 100),
        ge(&[("x", -1), ("y", 2)], 100),
        ge(&[("x", -2), ("y", 1)], 100),
        ge(&[("x", -1), ("y", -1)], 100),
    ]);
    let m = satisfiable(&f).unwrap().expect("a point");
    assert!(f.holds(&m), "{m:?}");
}

#[test]
fn a_rational_point_with_no_integer_value_of_a_variable_is_empty() {
    // 2x + 2y == 1 written as rows of three terms that no elimination can take without fill.
    let f = Formula::and(vec![
        ge(&[("x", 2), ("y", 4), ("z", 2)], -1),
        ge(&[("x", -2), ("y", -4), ("z", -2)], 1),
    ]);
    assert_eq!(satisfiable(&f), Ok(None));
    // A cycle of differences that sums below zero, with every variable on both sides.
    let f = Formula::and(vec![
        ge(&[("a", 1), ("b", -1)], -1),
        ge(&[("b", 1), ("c", -1)], -1),
        ge(&[("c", 1), ("a", -1)], 1),
    ]);
    assert_eq!(satisfiable(&f), Ok(None));
}

/// A ring of `k` partners, each paying at least what the next pays and the last at least what
/// the first pays, each payment in `[-half, half]`, and the total in `[lo, hi]`. The ring makes
/// every payment equal, so the total is `k` times one payment; each elimination of a payment
/// would add terms to the total's rows.
fn ring(k: usize, half: i128, lo: i128, hi: i128) -> Formula {
    let names: Vec<String> = (0..k).map(|i| format!("p{i}")).collect();
    let mut fs = Vec::new();
    for i in 0..k {
        let (p, q) = (names[i].as_str(), names[(i + 1) % k].as_str());
        fs.push(ge(&[(p, 1), (q, -1)], 0));
        fs.push(ge(&[(p, 1)], half));
        fs.push(ge(&[(p, -1)], half));
    }
    let total: Vec<(&str, i128)> = names.iter().map(|s| (s.as_str(), 1)).collect();
    let less: Vec<(&str, i128)> = names.iter().map(|s| (s.as_str(), -1)).collect();
    fs.push(ge(&total, -lo));
    fs.push(ge(&less, hi));
    Formula::and(fs)
}

#[test]
fn a_cycle_of_rows_makes_its_variables_equal() {
    // Four partners, each in [-1, 1], with a total in [1, 3]: the total is -4, 0 or 4, so
    // there is no integer point, though there are rational ones (OMEGA-cycle-growth; this was
    // refused `Growth`).
    assert_eq!(satisfiable(&ring(4, 1, 1, 3)), Ok(None));
    assert_eq!(decide(&ring(4, 1, 1, 3)), Ok(false));
    // Seven partners in [-3, 3] with a total in [8, 13] have none either; with [8, 14] each pays 2.
    assert_eq!(satisfiable(&ring(7, 3, 8, 13)), Ok(None));
    let f = ring(7, 3, 8, 14);
    let m = satisfiable(&f).unwrap().expect("a point");
    assert!(f.holds(&m), "{m:?}");
    for i in 0..7 {
        assert_eq!(m[&sym(&format!("p{i}"))], Int::from(2i64), "{m:?}");
    }
    // Two opposite rows are a cycle of two: `a >= b` and `b >= a`, with `a + b` odd.
    let f = Formula::and(vec![
        ge(&[("a", 1), ("b", -1)], 0),
        ge(&[("b", 1), ("a", -1)], 0),
        ge(&[("a", 1), ("b", 1), ("c", 2)], -1),
        ge(&[("a", -1), ("b", -1), ("c", -2)], 1),
    ]);
    assert_eq!(satisfiable(&f), Ok(None));
    // A cycle through zero: `x >= y >= 0 >= x`, so both are zero and `x + y + 2z == 1` is odd.
    let f = Formula::and(vec![
        ge(&[("x", 1), ("y", -1)], 0),
        ge(&[("y", 1)], 0),
        ge(&[("x", -1)], 0),
        ge(&[("x", 1), ("y", 1), ("z", 2)], -1),
        ge(&[("x", -1), ("y", -1), ("z", -2)], 1),
    ]);
    assert_eq!(satisfiable(&f), Ok(None));
    // A cycle with a step of one on it, `a >= b + 1 >= c + 1 >= a + 1`, has no point at all.
    let f = Formula::and(vec![
        ge(&[("a", 1), ("b", -1)], -1),
        ge(&[("b", 1), ("c", -1)], 0),
        ge(&[("c", 1), ("a", -1)], 0),
        ge(&[("a", 1), ("b", 1), ("c", 1)], 0),
        ge(&[("a", -1), ("b", -1), ("c", -1)], 9),
    ]);
    assert_eq!(satisfiable(&f), Ok(None));
}

#[test]
fn the_answer_is_the_answer_of_every_point_of_a_small_box() {
    // Every system has at most 3 variables in -6..=6; a refusal is allowed, a wrong answer not.
    let mut rng = Rng::new(0x1381);
    let (mut answered, mut refused) = (0, 0);
    for t in 0..1500 {
        let v = 2 + t % 2;
        let names = ["a", "b", "c"];
        let mut rows: Vec<Vec<(usize, i128)>> = Vec::new();
        let mut ks = Vec::new();
        let mut fs: Vec<Formula> = names[..v]
            .iter()
            .flat_map(|s| [ge(&[(s, 1)], 6), ge(&[(s, -1)], 6)])
            .collect();
        for _ in 0..v + rng.below(3 * v) {
            let mut row: Vec<(usize, i128)> = Vec::new();
            for _ in 0..2 {
                let i = rng.below(v);
                if !row.iter().any(|p| p.0 == i) {
                    row.push((i, [-5, -3, -2, -1, 1, 2, 3, 5][rng.below(8)]));
                }
            }
            let k = rng.int(-14, 14) as i128;
            let l: Vec<(&str, i128)> = row.iter().map(|(i, c)| (names[*i], *c)).collect();
            fs.push(ge(&l, k));
            rows.push(row);
            ks.push(k);
        }
        let holds = |p: &[i128]| {
            rows.iter()
                .zip(&ks)
                .all(|(r, k)| r.iter().map(|(i, c)| c * p[*i]).sum::<i128>() + k >= 0)
        };
        let box_ = -6..=6i128;
        let truth = box_.clone().any(|a| {
            box_.clone().any(|b| {
                if v == 2 {
                    holds(&[a, b, 0])
                } else {
                    box_.clone().any(|c| holds(&[a, b, c]))
                }
            })
        });
        let f = Formula::and(fs);
        match satisfiable(&f) {
            Ok(Some(m)) => {
                assert!(truth && f.holds(&m), "{f}: {m:?}");
                answered += 1;
            }
            Ok(None) => {
                assert!(!truth, "{f}: empty, but it has a point");
                answered += 1;
            }
            Err(_) => refused += 1,
        }
    }
    assert!(
        refused * 50 < answered,
        "{refused} refused, {answered} answered"
    );
}

/// `3·x[i] + 5·x[i+1] == 7`: one solution line, whose values need about n digits.
fn euclid_chain(n: usize) -> Formula {
    let names: Vec<String> = (0..=n).map(|i| format!("x{i:06}")).collect();
    Formula::and(
        names
            .windows(2)
            .map(|p| eq(&[(p[0].as_str(), 3), (p[1].as_str(), 5)], -7))
            .collect(),
    )
}

/// `6·x[i] + 10·x[i+1] + 15·x[i+2] == 7`, with no two coefficients coprime but the three.
fn euclid_chain3(n: usize) -> Formula {
    let names: Vec<String> = (0..=n + 1).map(|i| format!("x{i:06}")).collect();
    Formula::and(
        names
            .windows(3)
            .map(|p| {
                eq(
                    &[(p[0].as_str(), 6), (p[1].as_str(), 10), (p[2].as_str(), 15)],
                    -7,
                )
            })
            .collect(),
    )
}

#[test]
fn chains_of_equalities_cost_the_digits_of_their_values() {
    // n values of n digits each: the output itself is quadratic in bits, and the work is too.
    // Control: T4 took 297 times as long from 64 to 512 and over 30 s at 1024.
    for (name, build) in [
        ("3x + 5y == 7", euclid_chain as fn(usize) -> Formula),
        ("6x + 10y + 15z == 7", euclid_chain3),
    ] {
        let n = 64;
        let (small, large) = (build(n), build(scaling::FACTOR * n));
        for f in [&small, &large] {
            let m = satisfiable(f).unwrap().expect("a point");
            assert!(f.holds(&m));
            let digits = m.values().map(|v| v.to_string().len()).max().unwrap();
            assert!(digits <= n * scaling::FACTOR, "{digits} digits");
        }
        scaling::check_order(name, n, 2, |m| {
            drop(satisfiable(if m == n { &small } else { &large }));
        });
    }
}

#[test]
fn a_disjunct_refused_by_the_solver_is_reported_by_its_own_cause() {
    let pugh = Formula::and(vec![
        ge(&[("x", 11), ("y", 13)], -27),
        ge(&[("x", -11), ("y", -13)], 45),
        ge(&[("x", 7), ("y", -9)], 10),
        ge(&[("x", -7), ("y", 9)], 4),
    ]);
    let f = Formula::or(vec![pugh.clone(), pugh]);
    assert_eq!(satisfiable(&f), Ok(None));
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_constraints() {
    let rows = vec![
        eq(&[("a", 7), ("b", 12), ("c", 31)], -17),
        eq(&[("a", 3), ("b", 5), ("c", 14)], -7),
        ge(&[("a", 1)], -1),
        ge(&[("a", -1)], 40),
        ge(&[("b", 1)], 50),
        ge(&[("b", -1)], 50),
        ge(&[("a", 3), ("d", -2)], 4),
        ge(&[("d", 3), ("a", -2)], 9),
    ];
    let first = satisfiable(&Formula::and(rows.clone())).unwrap();
    assert!(first.is_some());
    // Every rotation, and every rotation reversed.
    for i in 0..rows.len() {
        let mut turned = rows.clone();
        turned.rotate_left(i);
        assert_eq!(satisfiable(&Formula::and(turned.clone())).unwrap(), first);
        turned.reverse();
        assert_eq!(satisfiable(&Formula::and(turned)).unwrap(), first);
    }
}

/// A random constraint on `a`, `b` and `c`, with a small box's worth of coefficients.
fn random_con(rng: &mut Rng) -> Formula {
    let c = |rng: &mut Rng| rng.int(-3, 3) as i128;
    let terms = [("a", c(rng)), ("b", c(rng)), ("c", c(rng))];
    let terms: Vec<_> = terms.into_iter().filter(|t| t.1 != 0).collect();
    if rng.below(4) == 0 {
        eq(&terms, c(rng))
    } else {
        ge(&terms, 2 * c(rng))
    }
}

/// A random formula with disjunctions and negations, of depth at most `d`.
fn random_formula(rng: &mut Rng, d: u32) -> Formula {
    if d == 0 || rng.below(3) == 0 {
        return random_con(rng);
    }
    let parts: Vec<Formula> = (0..2 + rng.below(3))
        .map(|_| random_formula(rng, d - 1))
        .collect();
    match rng.below(5) {
        0 => Formula::negate(Formula::and(parts)),
        1 | 2 => Formula::and(parts),
        _ => Formula::or(parts),
    }
}

/// `f` with the parts of every conjunction and disjunction in a random order.
fn shuffled(f: &Formula, rng: &mut Rng) -> Formula {
    let mut turned = |gs: &[Formula]| {
        let mut gs: Vec<Formula> = gs.iter().map(|g| shuffled(g, rng)).collect();
        for i in (1..gs.len()).rev() {
            gs.swap(i, rng.below(i + 1));
        }
        gs
    };
    match f {
        Formula::Con(_) => f.clone(),
        Formula::Not(g) => Formula::Not(Shared::new(turned(std::slice::from_ref(&**g)).remove(0))),
        Formula::And(gs) => Formula::And(Shared::new(turned(gs))),
        Formula::Or(gs) => Formula::Or(Shared::new(turned(gs))),
    }
}

/// Formulas `from..to` of one random sequence of 2000, each solved and solved reordered, and how
/// many of them the reordering changed. The formulas before `from` are drawn and not solved,
/// so that the two halves together are the one sequence.
fn reordered_formulas_agree(from: usize, to: usize) -> usize {
    let mut rng = Rng::new(0x1380);
    let mut disjunctive = 0;
    for i in 0..to {
        let f = random_formula(&mut rng, 3);
        let g = shuffled(&f, &mut rng);
        if i < from {
            continue;
        }
        disjunctive += usize::from(f != g);
        assert_eq!(satisfiable(&f), satisfiable(&g), "{f} and {g}");
        for s in ["a", "b", "c"] {
            assert_eq!(project(&f, &sym(s)), project(&g, &sym(s)), "{f} and {g}");
        }
    }
    disjunctive
}

// A proof rule that held on one spelling of `a < 0 || b < 0` and not on `b < 0 || a < 0` would
// change with a reformatting of the source. The 2000 formulas are checked in four quarters, each
// well under the 60-second limit of one test.

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts() {
    let disjunctive = reordered_formulas_agree(0, 500);
    assert!(disjunctive > 250, "{disjunctive} of 500 reordered");
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_second_quarter() {
    let disjunctive = reordered_formulas_agree(500, 1000);
    assert!(disjunctive > 250, "{disjunctive} of 500 reordered");
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_third_quarter() {
    let disjunctive = reordered_formulas_agree(1000, 1500);
    assert!(disjunctive > 250, "{disjunctive} of 500 reordered");
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_fourth_quarter() {
    let disjunctive = reordered_formulas_agree(1500, 2000);
    assert!(disjunctive > 250, "{disjunctive} of 500 reordered");
}

/// `Σ x[i] >= 0` with `x[i] == x[i+1] + 1`: one long row, each equality substituted into it.
fn tied_sum(n: usize) -> Formula {
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let sum: Vec<(&str, i128)> = names.iter().map(|s| (s.as_str(), 1)).collect();
    let mut rows = vec![ge(&sum, 0)];
    for p in names.windows(2) {
        rows.push(eq(&[(p[0].as_str(), 1), (p[1].as_str(), -1)], -1));
    }
    Formula::and(rows)
}

#[test]
fn equalities_substituted_into_a_long_row_cost_the_row_each_time() {
    // The equalities are solved among themselves, and the row is rewritten once for all of them.
    // Control: T4 took 121 times as long.
    let n = 256;
    let (small, large) = (tied_sum(n), tied_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert!(satisfiable(f).unwrap().is_some());
    }
    scaling::check_order("a long row with equalities", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

/// `Σ x[i] <= 49` with `x[i] >= 0`: a budget shared among n counts.
fn bounded_sum(n: usize) -> Formula {
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let sum: Vec<(&str, i128)> = names.iter().map(|s| (s.as_str(), -1)).collect();
    let mut rows = vec![ge(&sum, 49)];
    rows.extend(names.iter().map(|s| ge(&[(s.as_str(), 1)], 0)));
    Formula::and(rows)
}

#[test]
fn eliminating_the_terms_of_a_long_row_costs_the_row_each_time() {
    // Every x[i] is pulled to its lower bound by the one long row, and all are fixed there at
    // once, the row written once. Control: T4 took 38 times as long.
    let n = 128;
    let (small, large) = (bounded_sum(n), bounded_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
    scaling::check_order("a sum of bounded terms", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

/// The bounds the box stage gives the rows of a refused projection cost O(T log T) in the T
/// terms: each row tightens each of its terms from one sum of the bounds of the others, not from
/// a new sum for each term. `bounded_sum` gives each `x[i]` in [0, 49].
#[test]
fn the_box_of_refused_rows_scales() {
    let n = 2048;
    let (small, large) = (bounded_sum(n), bounded_sum(scaling::FACTOR * n));
    let syms = |m: usize| -> Vec<Atom> { (0..m).map(|i| sym(&format!("x{i}"))).collect() };
    let (s_small, s_large) = (syms(n), syms(scaling::FACTOR * n));
    let want = IntervalSet::range(End::Fin(Num::from(0)), End::Fin(Num::from(49)));
    for (f, s) in [(&small, &s_small), (&large, &s_large)] {
        assert!(row_box(f, s).iter().all(|b| *b == want));
    }
    scaling::check_order("the box of one long row", n, 1, |m| {
        drop(if m == n {
            row_box(&small, &s_small)
        } else {
            row_box(&large, &s_large)
        });
    });
}

/// The names of `fed_sum`: `a` sorts first, so that it is the first variable on a tie.
fn fed_names(n: usize) -> (Vec<String>, Vec<String>) {
    let names = |p: &str| (0..n).map(|i| format!("{p}{i:06}")).collect();
    (names("b"), names("c"))
}

/// `a <= Σ b[j]`, `a >= -c[i]`, `b[j] <= 5` and `c[i] <= 7`: one value between a long sum and n
/// lower bounds, size O(n). Eliminating `a` first gives n rows of n terms.
fn fed_sum(n: usize) -> Formula {
    let (bs, cs) = fed_names(n);
    let mut sum: Vec<(&str, i128)> = bs.iter().map(|s| (s.as_str(), 1)).collect();
    sum.push(("a", -1));
    let mut rows = vec![ge(&sum, 0)];
    for (b, c) in bs.iter().zip(&cs) {
        rows.push(ge(&[("a", 1), (c.as_str(), 1)], 0));
        rows.push(ge(&[(b.as_str(), -1)], 5));
        rows.push(ge(&[(c.as_str(), -1)], 7));
    }
    Formula::and(rows)
}

#[test]
fn a_value_between_a_long_sum_and_many_bounds_is_not_eliminated_first() {
    // Every b[j] and c[i] is pulled to its bound; `a` then has two bounds of its own, and its
    // elimination, n rows of n terms, is never taken.
    let n = 16;
    let (small, large) = (fed_sum(n), fed_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
    scaling::check_order("a value below a sum", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

/// `fed_sum` with each `b[j]` and `c[i]` tied to others so that each has two lower and two upper
/// bounds, and every other variable too, and with boxes that give the rows room: `a` is now the
/// one variable whose elimination removes a row, and goes first.
fn tied_fed_sum(n: usize) -> Formula {
    let (bs, cs) = fed_names(n);
    let mut rows = vec![fed_sum(n)];
    for (i, (b, c)) in bs.iter().zip(&cs).enumerate() {
        let (p, q, r) = (format!("d{i:06}"), format!("e{i:06}"), format!("f{i:06}"));
        let (b, c, p, q, r) = (b.as_str(), c.as_str(), p.as_str(), q.as_str(), r.as_str());
        rows.push(ge(&[(c, 1), (p, 1)], 3));
        rows.push(ge(&[(c, -1), (p, 1)], 9));
        rows.push(ge(&[(b, 1), (q, 1)], 3));
        rows.push(ge(&[(b, -1), (q, 1)], 9));
        rows.push(ge(&[(p, -1), (r, 1)], 3));
        rows.push(ge(&[(p, -1), (r, -1)], 9));
        rows.push(ge(&[(q, -1), (r, 1)], 2));
        rows.push(ge(&[(q, -1), (r, -1)], 8));
        for k in 0..12 {
            let y = format!("g{i:06}{k:02}");
            rows.push(ge(&[(y.as_str(), 1)], 9));
            rows.push(ge(&[(y.as_str(), -1)], 9));
        }
    }
    Formula::and(rows)
}

#[test]
fn a_value_that_alone_removes_a_row_is_eliminated_first_at_cubic_cost() {
    // Eliminating `a` first would write n rows of n terms, which is fill, and the variables with
    // no fill go first. Control: T4 took 90 times as long, and was held at cubic.
    let n = 16;
    let (small, large) = (tied_fed_sum(n), tied_fed_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
    scaling::check_order("a value below a tied sum", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

#[test]
fn a_box_around_the_origin_has_a_checked_point_or_a_stated_refusal() {
    // Five rows `a·x + b·y + k >= 0` with `a`, `b` in -3..=3 and `k` in 1..=20 hold at the
    // origin, so "no point" is wrong. Each answer is a point that the rows are checked to hold
    // at, or a refusal with its own message (cross-review XR3, R3_CODEX.md Q9).
    let mut rng = Rng::new(17);
    let (mut points, mut refused) = (0, 0);
    for _ in 0..1000 {
        let f = Formula::and(
            (0..5)
                .map(|_| {
                    let (a, b) = (rng.int(-3, 3) as i128, rng.int(-3, 3) as i128);
                    ge(&[("x", a), ("y", b)], rng.int(1, 20) as i128)
                })
                .collect(),
        );
        assert!(f.holds(&Default::default()), "{f}");
        match satisfiable(&f) {
            Ok(Some(m)) => {
                assert!(f.holds(&m), "{f} at {m:?}");
                points += 1;
            }
            Ok(None) => panic!("{f} holds at the origin"),
            Err(e) => {
                assert!(!e.to_string().is_empty(), "{f}");
                refused += 1;
            }
        }
        match decide(&f) {
            Ok(held) => assert!(held, "{f} holds at the origin"),
            Err(e) => assert!(!e.to_string().is_empty(), "{f}"),
        }
    }
    println!("boxes around the origin: {points} points, {refused} refused");
    assert_eq!(points + refused, 1000);
}

/// The rows of `l01_25_preimage_catalog::s22` case 236 of row 1000 (`if (i == -3) { .. }`
/// over `i mod 3`), with the names `name` gives and the equations `flip` picks negated: `i` is
/// `-4`, `0` or `4`. A remainder `q1`, `q2` to `q6` the arms' values, and a disjunction for
/// each `if`.
fn arms_of_case_236(name: &dyn Fn(&str) -> String, flip: &dyn Fn(usize) -> bool) -> Formula {
    let mut k = 0;
    let mut e = |terms: &[(&str, i128)], c: i128| {
        k += 1;
        let s = if flip(k) { -1 } else { 1 };
        let t: Vec<(String, i128)> = terms.iter().map(|(n, x)| (name(n), x * s)).collect();
        let t: Vec<(&str, i128)> = t.iter().map(|(n, x)| (n.as_str(), *x)).collect();
        eq(&t, c * s)
    };
    let g = |terms: &[(&str, i128)], c: i128| {
        let t: Vec<(String, i128)> = terms.iter().map(|(n, x)| (name(n), *x)).collect();
        let t: Vec<(&str, i128)> = t.iter().map(|(n, x)| (n.as_str(), *x)).collect();
        ge(&t, c)
    };
    let not = |f: Formula| Formula::Not(Shared::new(f));
    let both = |a: Formula, b: Formula| Formula::and(vec![a, b]);
    let def = e(&[("i", 1), ("q0", -3), ("q1", -1)], 0);
    let mut arms = Vec::new();
    for q in ["q2", "q3"] {
        let (a, b) = (e(&[("i", 1)], -8), e(&[("i", 1)], -8));
        let (yes, no) = (e(&[("i", 1), (q, 1)], 0), e(&[("i", 5), (q, 1)], 0));
        arms.push(Formula::or(vec![both(not(a), no), both(b, yes)]));
    }
    for q in ["q4", "q5"] {
        let (a, b) = (e(&[("q1", 1)], -1), e(&[("q1", 1)], -1));
        let (yes, no) = (e(&[("q2", 1), (q, -1)], 0), e(&[("q3", 1), (q, 1)], 0));
        arms.push(Formula::or(vec![both(a, yes), both(not(b), no)]));
    }
    let (a, b) = (e(&[("i", 1)], 3), e(&[("i", 1)], 3));
    let (yes, no) = (
        e(&[("q4", 1), ("q6", 1)], 6),
        e(&[("q5", 1), ("q6", -1)], 0),
    );
    arms.push(Formula::or(vec![both(a, yes), both(not(b), no)]));
    let i0 = e(&[("i", 1)], 0);
    Formula::and(
        [
            vec![def, g(&[("q1", 1)], 0), g(&[("q1", -1)], 2)],
            arms,
            vec![
                Formula::or(vec![
                    both(g(&[("i", 1)], 5), g(&[("i", -1)], -3)),
                    i0,
                    both(g(&[("i", 1)], -4), g(&[("i", -1)], 5)),
                ]),
                Formula::or(vec![
                    both(g(&[("q6", 1)], 26), g(&[("q6", -1)], -17)),
                    both(g(&[("q6", 1)], 4), g(&[("q6", -1)], 1)),
                ]),
            ],
        ]
        .concat(),
    )
}

/// [`arms_of_case_236`] written 60 ways, its names permuted and its equations negated at
/// random: `project_each` gives `i` the same set in every writing, its points `{-4, 0, 4}`
/// exactly (found by asking each `i` in `[-6, 6]`). Before item PROJECT-canon-precision the
/// set was `[-4, -3]`, `0`, `4`: the greedy search found a point, so the search over
/// disjuncts (`probe`) did not run and a disjunct with no point was kept; it now runs always,
/// its searches batched (COMPLEXITY.md row PROJECT-canon-precision).
#[test]
fn a_disjunct_with_no_point_beside_a_point_gives_one_answer_in_every_writing() {
    let mut rng = Rng::new(0x236);
    let plain = arms_of_case_236(&|n| n.to_string(), &|_| false);
    let mut points = IntervalSet::empty();
    for v in -6..=6i64 {
        let one = Formula::and(vec![plain.clone(), eq(&[("i", 1)], -(v as i128))]);
        if satisfiable(&one).expect("decided").is_some() {
            points = points.join(&IntervalSet::single(v));
        }
    }
    assert_eq!(points.to_string(), "[-4..=-4, 0..=0, 4..=4]");
    for w in 0..60 {
        let mut perm: Vec<usize> = (0..7).collect();
        for k in (1..7).rev() {
            perm.swap(k, rng.below(k + 1));
        }
        let flips: Vec<bool> = (0..32).map(|_| rng.below(2) == 0).collect();
        let i = if w % 2 == 0 { "i" } else { "m" };
        let name = |n: &str| match n {
            "i" => i.to_string(),
            q => format!("q{}", perm[q[1..].parse::<usize>().expect("a number")]),
        };
        let f = arms_of_case_236(&name, &|k| flips[k]);
        let (each, skipped) = project_each(&f, &[sym(i)]).expect("projected");
        assert!(skipped.is_empty(), "writing {w}: {f}");
        let got = each[0].as_ref().expect("a set");
        assert_eq!(*got, points, "writing {w}: {f}");
    }
}

/// A pipeline of `n` stages, each with a state `y[k]` that is 0 (idle) or 2 (drained), a
/// state of 1 (stalled) or a credit `z[k] >= 0`, and a credit of at most 5; with `chain`,
/// each stage's state at most 2 above the next one's. No stage can stall, but that shows only
/// beside the stage's other choice, so each test of a choice reads the stage's rows (item
/// PROJECT-dead2-quadratic). `zn` names the credits, so that two namings can be compared.
fn dead2(n: usize, chain: bool, zn: &str) -> Formula {
    let y = |k: usize| format!("y{k}");
    let z = |k: usize| format!("{zn}{k}");
    let mut fs = Vec::new();
    for k in 0..n {
        if chain && k + 1 < n {
            fs.push(ge(&[(&y(k + 1), 1), (&y(k), -1)], 2));
        }
        fs.push(Formula::or(vec![
            eq(&[(&y(k), 1)], 0),
            eq(&[(&y(k), 1)], -2),
        ]));
        fs.push(Formula::or(vec![
            eq(&[(&y(k), 1)], -1),
            ge(&[(&z(k), 1)], 0),
        ]));
        fs.push(ge(&[(&z(k), -1)], 5));
    }
    Formula::and(fs)
}

/// Every stage's credit is exactly `[0..=5]` and its state `{0, 2}`, under either naming of
/// the credits, chained or not: no stage can stall, since its state is 0 or 2, so its credit
/// is at least 0 (item PROJECT-hull-credit-lower). Before it the credit's hull had no lower
/// bound: the rows the state's disjunction implies, `0 <= y <= 2`, allow a stall.
#[test]
fn pipeline_stage_hulls_are_exact() {
    for chain in [false, true] {
        for zn in ["z", "a"] {
            for n in [1, 2, 3, 4, 16, 128] {
                let f = dead2(n, chain, zn);
                let syms: Vec<Atom> = (0..n)
                    .flat_map(|k| [sym(&format!("{zn}{k}")), sym(&format!("y{k}"))])
                    .collect();
                let (each, skipped) =
                    zedc::store::presburger::project_each(&f, &syms).expect("answered");
                let hulls: Vec<String> = (each.iter())
                    .map(|h| h.as_ref().expect("not refused").to_string())
                    .collect();
                let exact: Vec<&str> = (0..n).flat_map(|_| ["[0..=5]", "[0..=0, 2..=2]"]).collect();
                assert_eq!(hulls, exact, "n = {n}, chain = {chain}, credits {zn}");
                assert!(skipped.is_empty());
            }
        }
    }
}

/// `y` is 0 or 2, `y == 1 || w == 4 || w == 6`, `w == 5 || x >= 1` and `x <= 9`: `y == 1`
/// goes, which leaves `w` 4 or 6, so `w == 5` goes and `x` is at least 1. Each removal needs
/// the one before; the hulls are the same in each order of the disjunctions and of their
/// disjuncts, and under each sign of the equations.
#[test]
fn removals_by_values_cascade_in_any_order() {
    let parts = |flip: bool| -> Vec<Vec<Formula>> {
        let s = if flip { -1 } else { 1 };
        vec![
            vec![eq(&[("y", s)], 0), eq(&[("y", s)], -2 * s)],
            vec![
                eq(&[("y", s)], -s),
                eq(&[("w", s)], -4 * s),
                eq(&[("w", s)], -6 * s),
            ],
            vec![eq(&[("w", s)], -5 * s), ge(&[("x", 1)], -1)],
        ]
    };
    let syms = [sym("x"), sym("w"), sym("y")];
    let orders: [[usize; 3]; 6] = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    for flip in [false, true] {
        for order in orders {
            for reverse in [false, true] {
                let ors = parts(flip);
                let mut fs: Vec<Formula> = (order.iter())
                    .map(|&j| {
                        let mut ds = ors[j].clone();
                        if reverse {
                            ds.reverse();
                        }
                        Formula::or(ds)
                    })
                    .collect();
                fs.push(ge(&[("x", -1)], 9));
                let f = Formula::and(fs);
                let (each, skipped) = project_each(&f, &syms).expect("answered");
                let hulls: Vec<String> = (each.iter())
                    .map(|h| h.as_ref().expect("not refused").to_string())
                    .collect();
                assert_eq!(
                    hulls,
                    ["[1..=9]", "[4..=4, 6..=6]", "[0..=0, 2..=2]"],
                    "{f}"
                );
                assert!(skipped.is_empty());
            }
        }
    }
}

/// A disjunct is removed by the values of each form read alone: with `x` and `y` each 0 or 2,
/// `x + y == 1` of `x + y == 1 || z >= 0` is kept, though `x + y` is 0, 2 or 4, so `z` keeps
/// no lower bound. A sound hull, wider than the exact `[0..=5]` (the complexity tradeoff on
/// `drop_outside_values`, COMPLEXITY.md PROJECT-hull-credit-lower).
#[test]
fn a_sum_of_forms_with_gaps_is_not_read() {
    let f = Formula::and(vec![
        Formula::or(vec![eq(&[("x", 1)], 0), eq(&[("x", 1)], -2)]),
        Formula::or(vec![eq(&[("y", 1)], 0), eq(&[("y", 1)], -2)]),
        Formula::or(vec![eq(&[("x", 1), ("y", 1)], -1), ge(&[("z", 1)], 0)]),
        ge(&[("z", -1)], 5),
    ]);
    let (each, skipped) = project_each(&f, &[sym("z")]).expect("answered");
    let z = each[0].as_ref().expect("not refused");
    let exact = IntervalSet::of(0, 5);
    assert_eq!(z.join(&exact), *z, "the exact hull is inside");
    assert_eq!(z.to_string(), "[..=5]");
    assert!(skipped.is_empty());
}

/// Projecting the first and the last credit of a pipeline of `n` stages costs O(n log n),
/// chained or not (stages not chained are alike, so they are projected as sets): the stalls
/// are removed by the values of each state, one pass over the disjuncts' ranges, and each
/// credit's hull is then `[0..=5]` (item PROJECT-hull-credit-lower).
#[test]
fn the_first_and_last_credits_of_a_pipeline_scale() {
    for chain in [false, true] {
        let (small, large) = (
            dead2(16, chain, "z"),
            dead2(16 * scaling::FACTOR, chain, "z"),
        );
        let (s_small, s_large) = (
            [sym("z0"), sym("z15")],
            [sym("z0"), sym(&format!("z{}", 16 * scaling::FACTOR - 1))],
        );
        scaling::check_order(
            &format!("the first and last credits of a pipeline of stages, chained {chain}"),
            16,
            1,
            |n| {
                let (f, s) = if n == 16 {
                    (&small, &s_small)
                } else {
                    (&large, &s_large)
                };
                let _ = std::hint::black_box(zedc::store::presburger::project_each(f, s));
            },
        );
    }
}

/// Projecting every state and credit of an unchained pipeline of `n` stages costs
/// O(n log n): each hull is tightened over its own stage, not the whole formula, which cost
/// O(n) per symbol before, 56.1 times the bytes from 16 to 128 stages (item
/// TIGHTEN-each-whole). The chained pipeline is left out: its tightening is now O(n log n),
/// but each disjunct is still projected onto every symbol of the chain, O(n) per disjunction
/// (item PROJECT-each-chain-all).
#[test]
fn every_state_and_credit_of_a_pipeline_scale() {
    let syms = |n: usize| -> Vec<Atom> {
        (0..n)
            .flat_map(|k| [sym(&format!("z{k}")), sym(&format!("y{k}"))])
            .collect()
    };
    let inputs = scaling::inputs(16, |n| (dead2(n, false, "z"), syms(n)));
    scaling::check_order(
        "every state and credit of a pipeline of stages",
        16,
        1,
        |n| {
            let (f, s) = &inputs[&n];
            let _ = std::hint::black_box(zedc::store::presburger::project_each(f, s));
        },
    );
}

/// `n` stages that share no atom, each with `0 <= x[k]`, `x[k] <= 1 || x[k] == 2`,
/// `y[k] == 0 || y[k] == 2` and `x[k] + y[k] == 1 || x[k] + y[k] == 3`. Each stage's points
/// are `x[k] == 1` with `y[k]` 0 or 2: `x[k] == 0` needs `y[k]` 1 or 3, and `x[k] == 2` needs
/// `y[k]` -1 or 1. The rows the disjunctions imply allow `0 <= x[k] <= 2`, so each end of
/// `x[k]` is moved only by questions.
fn joint_stages(n: usize) -> Formula {
    let mut fs = Vec::new();
    for k in 0..n {
        let (x, y) = (format!("x{k}"), format!("y{k}"));
        fs.push(ge(&[(&x, 1)], 0));
        fs.push(Formula::or(vec![ge(&[(&x, -1)], 1), eq(&[(&x, 1)], -2)]));
        fs.push(Formula::or(vec![eq(&[(&y, 1)], 0), eq(&[(&y, 1)], -2)]));
        fs.push(Formula::or(vec![
            eq(&[(&x, 1), (&y, 1)], -1),
            eq(&[(&x, 1), (&y, 1)], -3),
        ]));
    }
    Formula::and(fs)
}

/// The symbols `x[k]` and `y[k]` of [`joint_stages`] of `n` stages, in stage order.
fn joint_syms(n: usize) -> Vec<Atom> {
    (0..n)
        .flat_map(|k| [sym(&format!("x{k}")), sym(&format!("y{k}"))])
        .collect()
}

/// Every stage of [`joint_stages`] gives `x[k]` exactly `[1..=1]` and `y[k]` exactly
/// `{0, 2}`, however many stages there are: each stage is asked alone, and the answer is the
/// one the whole formula gives. The values are those of one stage's rows counted one by one
/// over a box that holds all its points (the stages share no atom and each has a point).
/// Before item TIGHTEN-each-whole each question was asked of the whole formula, and from 3
/// stages on the solver refused them, leaving `x[k]` at `[0..=2]`.
#[test]
fn joint_stage_hulls_are_exact() {
    let (mut xs, mut ys) = (Vec::new(), Vec::new());
    for x in -4i128..=6 {
        for y in -4i128..=6 {
            let holds =
                x >= 0 && (x <= 1 || x == 2) && (y == 0 || y == 2) && (x + y == 1 || x + y == 3);
            if holds {
                xs.push(x);
                ys.push(y);
            }
        }
    }
    xs.sort_unstable();
    xs.dedup();
    ys.sort_unstable();
    ys.dedup();
    assert_eq!((xs, ys), (vec![1], vec![0, 2]), "one stage's points");
    for n in [1, 2, 3, 16] {
        let (each, skipped) = project_each(&joint_stages(n), &joint_syms(n)).expect("projected");
        assert!(skipped.is_empty(), "n = {n}: {skipped:?}");
        for (i, h) in each.into_iter().enumerate() {
            let h = h.expect("a hull");
            let want = if i % 2 == 0 {
                "[1..=1]"
            } else {
                "[0..=0, 2..=2]"
            };
            assert_eq!(h.to_string(), want, "n = {n}, symbol {i}");
        }
    }
}

/// Projecting every symbol of [`joint_stages`] of `n` stages costs O(n log n): each end is
/// asked of its own stage, not of the whole formula, which cost O(n) per question and O(n²)
/// in all before (item TIGHTEN-each-whole).
#[test]
fn independent_stages_scale() {
    let inputs = scaling::inputs(16, |n| (joint_stages(n), joint_syms(n)));
    scaling::check_order("every symbol of stages that share no atom", 16, 1, |n| {
        let (f, s) = &inputs[&n];
        let _ = std::hint::black_box(project_each(f, s));
    });
}

/// Projecting the first credit of a chained pipeline of `n` stages costs O(n log n): each
/// choice is tested against the rows projected onto its own stage, not against the whole
/// chain, which cost `n` solves of `n` rows before (40.6 times the instructions from 16 to
/// 128 stages).
#[test]
fn project_each_on_a_chained_pipeline_scales() {
    let (small, large) = (
        dead2(128, true, "z"),
        dead2(128 * scaling::FACTOR, true, "z"),
    );
    let syms = [sym("z0")];
    scaling::check_order(
        "the first credit of a chained pipeline of stages",
        128,
        1,
        |n| {
            let f = if n == 128 { &small } else { &large };
            let _ = std::hint::black_box(zedc::store::presburger::project_each(f, &syms));
        },
    );
}

/// Families of `n` holes, each a disjunction, on a chain of difference rows (item
/// PROJECT-each-chain-xr). `chain`: [`dead2`] chained; `both`: [`dead2`] chained both ways (`|y[k+1] - y[k]| <= 2`);
/// `slope`: `1 <= y[k+1] - y[k] <= 5`, `y[k]` in `{3k, 3k + 2}`; `acc`: `x[k+1] == x[k] + y[k]`,
/// `x0 == 0`, `y[k]` in `{0, 2}`; `mono`/`mono1`: `y[k+1] >= y[k]`, `0 <= y[k] <= 20`, `y[k]` in
/// `{9, 11}` / `{10, 11}`; `eqchain`: `y[k+1] == y[k]`; `band`: `0 <= y[k+1] - y[k] <= 1`, both with
/// `y[k]` in `{0, 10}`; `wide`: `band` with `y[k]` in `{0, 4n}`; `twoway`: `|y[k+1] - y[k]| <= 2`,
/// `y[k]` in `{0, 2}`, `y[k] == 1 || z[k] >= 0`, `z[k] <= 5`; `pair`: `y[k+1] >= y[k] - 2`,
/// `(y[k], y[k+1])` in `{(0, 0), (2, 2)}` for even `k`; `steps`: `x[k+1] - x[k]` in `{0, 10}`,
/// `x0 == 0`; `pinned`: also `x[n] == 0`; `pinlast`: also `x[n] <= 10`.
fn holes_family(fam: &str, n: usize) -> (Formula, Vec<Atom>) {
    let y = |k: usize| format!("y{k}");
    let x = |k: usize| format!("x{k}");
    match fam {
        "chain" => (
            dead2(n, true, "z"),
            (0..n)
                .flat_map(|k| [sym(&format!("z{k}")), sym(&y(k))])
                .collect(),
        ),
        "both" => {
            let mut fs = vec![dead2(n, true, "z")];
            for k in 0..n.saturating_sub(1) {
                fs.push(ge(&[(&y(k), 1), (&y(k + 1), -1)], 2));
            }
            let syms = (0..n)
                .flat_map(|k| [sym(&format!("z{k}")), sym(&y(k))])
                .collect();
            (Formula::and(fs), syms)
        }
        "mono" | "mono1" | "eqchain" | "band" | "wide" | "twoway" | "pair" => {
            let mut fs = Vec::new();
            let mut names = Vec::new();
            for k in 0..n {
                let (yk, y1) = (y(k), y(k + 1));
                match fam {
                    "mono" | "mono1" => {
                        let lo = if fam == "mono" { -9 } else { -10 };
                        if k + 1 < n {
                            fs.push(ge(&[(&y1, 1), (&yk, -1)], 0));
                        }
                        fs.push(ge(&[(&yk, 1)], 0));
                        fs.push(ge(&[(&yk, -1)], 20));
                        fs.push(Formula::or(vec![eq(&[(&yk, 1)], lo), eq(&[(&yk, 1)], -11)]));
                    }
                    "eqchain" | "band" | "wide" => {
                        if k + 1 < n {
                            if fam == "eqchain" {
                                fs.push(eq(&[(&y1, 1), (&yk, -1)], 0));
                            } else {
                                fs.push(ge(&[(&y1, 1), (&yk, -1)], 0));
                                fs.push(ge(&[(&yk, 1), (&y1, -1)], 1));
                            }
                        }
                        let top = if fam == "wide" { -4 * n as i128 } else { -10 };
                        fs.push(Formula::or(vec![eq(&[(&yk, 1)], 0), eq(&[(&yk, 1)], top)]));
                    }
                    "twoway" => {
                        let z = format!("z{k}");
                        if k + 1 < n {
                            fs.push(ge(&[(&y1, 1), (&yk, -1)], 2));
                            fs.push(ge(&[(&yk, 1), (&y1, -1)], 2));
                        }
                        fs.push(Formula::or(vec![eq(&[(&yk, 1)], 0), eq(&[(&yk, 1)], -2)]));
                        fs.push(Formula::or(vec![eq(&[(&yk, 1)], -1), ge(&[(&z, 1)], 0)]));
                        fs.push(ge(&[(&z, -1)], 5));
                        names.push(sym(&z));
                    }
                    _ => {
                        fs.push(ge(&[(&y1, 1), (&yk, -1)], 2));
                        if k % 2 == 0 {
                            fs.push(Formula::or(vec![
                                Formula::and(vec![eq(&[(&yk, 1)], 0), eq(&[(&y1, 1)], 0)]),
                                Formula::and(vec![eq(&[(&yk, 1)], -2), eq(&[(&y1, 1)], -2)]),
                            ]));
                        }
                    }
                }
                names.push(sym(&yk));
            }
            (Formula::and(fs), names)
        }
        "steps" | "pinned" | "pinlast" => {
            let mut fs = vec![eq(&[(&x(0), 1)], 0)];
            for k in 0..n {
                fs.push(Formula::or(vec![
                    eq(&[(&x(k + 1), 1), (&x(k), -1)], 0),
                    eq(&[(&x(k + 1), 1), (&x(k), -1)], -10),
                ]));
            }
            if fam == "pinned" {
                fs.push(eq(&[(&x(n), 1)], 0));
            }
            if fam == "pinlast" {
                fs.push(ge(&[(&x(n), -1)], 10));
            }
            (Formula::and(fs), (1..=n).map(|k| sym(&x(k))).collect())
        }
        "slope" => {
            let mut fs = Vec::new();
            for k in 0..n {
                if k + 1 < n {
                    fs.push(ge(&[(&y(k + 1), 1), (&y(k), -1)], -1));
                    fs.push(ge(&[(&y(k), 1), (&y(k + 1), -1)], 5));
                }
                let c = 3 * k as i128;
                fs.push(Formula::or(vec![
                    eq(&[(&y(k), 1)], -c),
                    eq(&[(&y(k), 1)], -c - 2),
                ]));
            }
            (Formula::and(fs), (0..n).map(|k| sym(&y(k))).collect())
        }
        f => panic!("no family {f}"),
    }
}

/// `x[k+1] - x[k]` in `{0, 10}` from `x0 == 0` gives `x[k]` exactly the multiples of 10 up to
/// `10k`; with `x[n] == 0` every `x[k]` is 0, and with `x[n] <= 10` every `x[k]` is 0 or 10
/// (the steps rise and never fall). Before item PROJECT-each-chain-xr each answer was the hull,
/// `[0..=10k]` and `[0..=10]`.
#[test]
fn steps_of_ten_are_exact() {
    let n = 6;
    for fam in ["steps", "pinned", "pinlast"] {
        let (f, syms) = holes_family(fam, n);
        let (each, skipped) = project_each(&f, &syms).expect("projected");
        assert!(skipped.is_empty(), "{fam}: {skipped:?}");
        for (i, h) in each.into_iter().enumerate() {
            let k = i as i128 + 1;
            let values: Vec<i128> = match fam {
                "steps" => (0..=k).map(|j| 10 * j).collect(),
                "pinned" => vec![0],
                _ => vec![0, 10],
            };
            assert_eq!(
                h.expect("a set").to_string(),
                runs(&values),
                "{fam}: x{k} of {n}"
            );
        }
    }
}

/// `values`, sorted, as [`IntervalSet`] prints them: `[a..=b, c..=d]`, one piece per run.
fn runs(values: &[i128]) -> String {
    let mut pieces: Vec<(i128, i128)> = Vec::new();
    for &v in values {
        match pieces.last_mut() {
            Some((_, hi)) if *hi + 1 == v => *hi = v,
            _ => pieces.push((v, v)),
        }
    }
    let inner: Vec<String> = pieces.iter().map(|(a, b)| format!("{a}..={b}")).collect();
    format!("[{}]", inner.join(", "))
}

/// A row `Σ c·v[i] + k >= 0`, or `== 0` with `eq`, over atoms `v0, v1, ...`.
#[derive(Clone)]
struct Row {
    terms: Vec<(usize, i128)>,
    k: i128,
    eq: bool,
}

impl Row {
    fn formula(&self) -> Formula {
        let names: Vec<String> = self.terms.iter().map(|(i, _)| format!("v{i}")).collect();
        let terms: Vec<(&str, i128)> = (names.iter().zip(&self.terms))
            .map(|(s, (_, c))| (s.as_str(), *c))
            .collect();
        if self.eq {
            eq(&terms, self.k)
        } else {
            ge(&terms, self.k)
        }
    }

    fn holds(&self, p: &[i128]) -> bool {
        let s: i128 = self.terms.iter().map(|(i, c)| c * p[*i]).sum::<i128>() + self.k;
        if self.eq { s == 0 } else { s >= 0 }
    }
}

/// A random row between the atoms `a` and `b` (the same atom for a bound): `b - a >= k`,
/// `b - a == k`, `a <= k` or `b >= k`, with `|k| <= 2`.
fn random_row(rng: &mut Rng, a: usize, b: usize) -> Row {
    let k = rng.int(-2, 2) as i128;
    match rng.below(4) {
        0 if a != b => Row {
            terms: vec![(b, 1), (a, -1)],
            k: -k,
            eq: false,
        },
        1 if a != b => Row {
            terms: vec![(b, 1), (a, -1)],
            k: -k,
            eq: true,
        },
        2 => Row {
            terms: vec![(a, -1)],
            k,
            eq: false,
        },
        _ => Row {
            terms: vec![(b, 1)],
            k: -k,
            eq: false,
        },
    }
}

/// Random components that are forests once their tie classes are contracted: 2 to 3 classes
/// of 1 or 2 atoms (`v[j] == v[i] + c` ties the second to the first), each atom in `[-2..=2]`,
/// each tree edge a pair of difference rows or a disjunction of two conjunctions of one or
/// two rows over its two classes, and up to two disjunctions over one atom. Every atom's
/// answer is the set of values it takes at the points found by counting over `[-2..=2]` one
/// by one, which hold every point. Before item PROJECT-each-chain-xr an answer could be the
/// hull of that set.
#[test]
fn forest_answers_match_enumeration() {
    let mut rng = Rng::new(38);
    let mut checked = 0;
    for case in 0..150 {
        let classes = 2 + rng.below(2);
        let mut members: Vec<Vec<usize>> = Vec::new();
        let mut base: Vec<Row> = Vec::new();
        let mut atoms = 0;
        for _ in 0..classes {
            let first = atoms;
            atoms += 1;
            let mut m = vec![first];
            if rng.below(2) == 0 {
                let c = rng.int(-1, 1) as i128;
                base.push(Row {
                    terms: vec![(atoms, 1), (first, -1)],
                    k: -c,
                    eq: true,
                });
                m.push(atoms);
                atoms += 1;
            }
            members.push(m);
        }
        for v in 0..atoms {
            base.push(Row {
                terms: vec![(v, 1)],
                k: 2,
                eq: false,
            });
            base.push(Row {
                terms: vec![(v, -1)],
                k: 2,
                eq: false,
            });
        }
        let mut ors: Vec<Vec<Vec<Row>>> = Vec::new();
        for c in 1..classes {
            let p = rng.below(c);
            let a = rng.pick(&members[p]);
            let b = rng.pick(&members[c]);
            if rng.below(2) == 0 {
                base.push(random_row(&mut rng, a, b));
                base.push(random_row(&mut rng, a, b));
            } else {
                let mut d = Vec::new();
                for _ in 0..2 {
                    d.push(
                        (0..1 + rng.below(2))
                            .map(|_| random_row(&mut rng, a, b))
                            .collect(),
                    );
                }
                ors.push(d);
            }
        }
        for _ in 0..rng.below(3) {
            let v = rng.below(atoms);
            ors.push(vec![
                vec![random_row(&mut rng, v, v)],
                vec![random_row(&mut rng, v, v)],
            ]);
        }
        let mut seen: Vec<Vec<i128>> = vec![Vec::new(); atoms];
        let mut p = vec![-2i128; atoms];
        loop {
            let holds = base.iter().all(|r| r.holds(&p))
                && ors
                    .iter()
                    .all(|d| d.iter().any(|rs| rs.iter().all(|r| r.holds(&p))));
            if holds {
                for (s, v) in seen.iter_mut().zip(&p) {
                    s.push(*v);
                }
            }
            let Some(i) = p.iter().position(|v| *v < 2) else {
                break;
            };
            p[i] += 1;
            for v in &mut p[..i] {
                *v = -2;
            }
        }
        if seen[0].is_empty() {
            continue;
        }
        let mut fs: Vec<Formula> = base.iter().map(Row::formula).collect();
        for d in &ors {
            fs.push(Formula::or(
                d.iter()
                    .map(|rs| Formula::and(rs.iter().map(Row::formula).collect()))
                    .collect(),
            ));
        }
        let f = Formula::and(fs);
        let syms: Vec<Atom> = (0..atoms).map(|v| sym(&format!("v{v}"))).collect();
        let (each, skipped) = project_each(&f, &syms).expect("projected");
        assert!(skipped.is_empty(), "case {case}: {skipped:?}");
        for (v, (h, s)) in each.into_iter().zip(&mut seen).enumerate() {
            s.sort_unstable();
            s.dedup();
            assert_eq!(
                h.expect("a set").to_string(),
                runs(s),
                "case {case}: v{v} of {f}"
            );
        }
        checked += 1;
    }
    assert!(checked >= 50, "only {checked} cases have a point");
}

/// `Σ c·a + k`, where a name `qN` is the solver's own atom `N` ([`Atom::Aux`]) and any other
/// name is a symbol.
fn aux_lin(terms: &[(&str, i128)], k: i128) -> Lin {
    terms.iter().fold(Lin::constant(k), |l, (s, c)| {
        let a = match s.strip_prefix('q') {
            Some(n) => Atom::Aux(n.parse().expect("a number")),
            None => sym(s),
        };
        l.plus(&Lin::atom(a).times(*c))
    })
}

fn aux_ge(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::ge(&aux_lin(terms, k), &Lin::constant(0)))
}

fn aux_eq(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::eq(&aux_lin(terms, k), &Lin::constant(0)))
}

/// `(c && a) || (!c && b)`.
fn picked(c: Formula, a: Formula, b: Formula) -> Formula {
    let not = Formula::Not(Shared::new(c.clone()));
    Formula::or(vec![Formula::and(vec![c, a]), Formula::and(vec![not, b])])
}

/// `q == |x - k|`, written as the translator writes it.
fn abs_of(q: &str, x: &str, k: i128) -> Formula {
    picked(
        aux_ge(&[(x, 1)], -k),
        aux_eq(&[(x, 1), (q, -1)], -k),
        aux_eq(&[(x, 1), (q, 1)], -k),
    )
}

/// The values of `i` in `lo..=hi` at which `f` has a point, each decided by the solver.
fn values_of_i(f: &Formula, lo: i64, hi: i64) -> Vec<i64> {
    (lo..=hi)
        .filter(|&v| {
            let one = Formula::and(vec![f.clone(), eq(&[("i", 1)], -(v as i128))]);
            satisfiable(&one).expect("decided").is_some()
        })
        .collect()
}

/// `|i - k|` written twice for each `k` below `n`, as `q(2k)` and `q(2k+1)`, with each pair
/// summing to at least 6 and `i <= n + 10`: `i` in `..=-3` and `n+2..=n+10`.
fn twin_absolute_values(n: usize) -> Formula {
    let mut parts = Vec::new();
    for k in 0..n {
        let (a, b) = (format!("q{}", 2 * k), format!("q{}", 2 * k + 1));
        parts.push(abs_of(&a, "i", k as i128));
        parts.push(abs_of(&b, "i", k as i128));
        parts.push(aux_ge(&[(a.as_str(), 1), (b.as_str(), 1)], -6));
    }
    parts.push(aux_ge(&[("i", -1)], 10 + n as i128));
    Formula::and(parts)
}

/// s22 case 1185 of `l01_25_preimage_catalog` as the reference transfer writes it: a shared
/// term written once at each use, so `q2` and `q3`, `q4` and `q5`, `q7` and `q8`, and `q9`,
/// `q10` and `q11` are each defined alike. Its one point has `i == -9`.
fn case_1185() -> Formula {
    let mut parts = vec![
        aux_eq(&[("i", 1), ("q0", -3), ("q1", -1)], 0),
        aux_ge(&[("q1", 1)], 0),
        aux_ge(&[("q1", -1)], 2),
        abs_of("q2", "i", 0),
        abs_of("q3", "i", 0),
    ];
    for q in ["q4", "q5"] {
        parts.push(picked(
            aux_ge(&[("i", -1)], -5),
            aux_eq(&[("i", 2), (q, -1)], 0),
            aux_eq(&[("i", 1), (q, -1)], 3),
        ));
    }
    parts.push(picked(
        aux_ge(&[("q5", -1)], -6),
        aux_eq(&[("q5", 1), ("q6", -1)], 0),
        aux_eq(&[("q6", 1)], 6),
    ));
    for q in ["q7", "q8"] {
        parts.push(picked(
            aux_ge(&[("q3", 1)], -4),
            aux_eq(&[("q4", 1), (q, 1)], 5),
            aux_eq(&[("q6", 1), (q, -1)], 0),
        ));
    }
    for q in ["q9", "q10", "q11"] {
        parts.push(picked(
            aux_ge(&[("q2", 1)], -5),
            aux_eq(&[("q7", 1), (q, -1)], 0),
            aux_eq(&[("q8", 1), (q, 1)], 0),
        ));
    }
    parts.push(picked(
        aux_eq(&[("q1", 1)], 0),
        aux_eq(&[("q9", 1), ("q10", 1), ("q12", -1)], 0),
        aux_eq(&[("q11", 1), ("q12", 1)], 0),
    ));
    parts.extend([
        aux_ge(&[("i", -1)], 10),
        aux_ge(&[("q12", 1)], -21),
        aux_ge(&[("q12", -1)], 26),
    ]);
    Formula::and(parts)
}

#[test]
fn twin_definitions_are_merged_before_a_tied_projection() {
    // Two auxiliary atoms defined alike (`q0 == |i|` and `q1 == |i|`) cannot be told apart by
    // their names, so the projection is tied (`Refusal::Unordered`), and before item
    // PROJECT-box-half-open it kept only `i <= 11` from the rows: the bounded side of the
    // half-open box was not narrowed. Each pair is one atom at every point, so it is made one
    // and the merged formula projected; both answers are checked against the values the
    // solver finds one at a time.
    let f = twin_absolute_values(1);
    let set = |ps: &[(Option<i64>, i64)]| {
        IntervalSet::from_pieces(
            ps.iter()
                .map(|&(lo, hi)| {
                    (
                        lo.map_or(End::NegInf, |v| End::Fin(Num::from(v))),
                        End::Fin(Num::from(hi)),
                    )
                })
                .collect(),
        )
    };
    let (each, _) = project_each(&f, &[sym("i")]).expect("answered");
    let got = each[0].clone().expect("answered");
    assert_eq!(got, set(&[(None, -3), (Some(3), 11)]), "{f}");
    let values = values_of_i(&f, -40, 40);
    assert_eq!(values, (-40..=-3).chain(3..=11).collect::<Vec<_>>(), "{f}");
    // Case 1185 also needs a point of `f` with `i` at most a bound to show that `f` has a
    // point, where asking for `f` itself is refused (`Hull::asked`): its upper end is -9, the
    // one value, where it was 4.
    let f = case_1185();
    let (each, _) = project_each(&f, &[sym("i")]).expect("answered");
    let got = each[0].clone().expect("answered");
    assert_eq!(
        got.bounds(),
        Some((&End::NegInf, &End::Fin(Num::from(-9)))),
        "{f}"
    );
    assert_eq!(values_of_i(&f, -40, 40), vec![-9], "{f}");
}

#[test]
fn twin_definitions_merge_in_time_near_linear() {
    // n pairs of twins over the same symbol: numbering the definitions is one pass in the order
    // of their dependencies with a hash lookup each, and the merged formula has n absolute
    // values of one symbol. Control (once, not kept): an O(n²) scan of the definitions in the
    // merge failed this test.
    let n = 32;
    let (small, large) = (
        twin_absolute_values(n),
        twin_absolute_values(scaling::FACTOR * n),
    );
    for (m, f) in [(n, &small), (scaling::FACTOR * n, &large)] {
        let (each, _) = project_each(f, &[sym("i")]).expect("answered");
        let m = m as i64;
        let want = [
            (End::NegInf, End::Fin(Num::from(-3))),
            (End::Fin(Num::from(m + 2)), End::Fin(Num::from(m + 10))),
        ];
        assert_eq!(
            each[0].clone().expect("answered"),
            IntervalSet::from_pieces(want.to_vec()),
            "{m}"
        );
    }
    scaling::check_order(
        "twin definitions merged before a tied projection",
        n,
        1,
        |m| {
            drop(project_each(
                if m == n { &small } else { &large },
                &[sym("i")],
            ));
        },
    );
}
