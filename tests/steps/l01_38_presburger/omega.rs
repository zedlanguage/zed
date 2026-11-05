//! The Omega test's corner cases: each cause of a refusal with its own message, values past
//! `i128`, equalities with no unit coefficient, opposite rows that meet, and an answer that does
//! not depend on the order of the constraints.

use std::sync::Arc;

use zed_tests::{instances::Rng, scaling};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{
    Atom, Con, Entailment, Formula, Lin, Refusal, Relation, decide, entails, project, satisfiable,
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
        "the integer constraints have four variables or more, each of whose elimination \
         would enlarge them, so whether they hold at an integer point is not decided",
    );
    // A splinter of the dark elimination takes a dark shadow of its own that has no point,
    // over four variables: with three, `live3` decides the splinter's gray shadow.
    refused(
        Formula::and(vec![
            ge(&[("x", 9), ("y", -4), ("w", -8)], -3),
            ge(&[("x", 5), ("y", 11), ("w", 9)], -9),
            ge(&[("x", -7), ("y", -12), ("z", -2), ("w", 8)], -1),
            ge(&[("x", -9), ("y", 8), ("z", 7)], 0),
            ge(&[("x", -10), ("y", 4), ("z", -6), ("w", -4)], 22),
        ]),
        Refusal::Shadows,
        "an integer point of the integer constraints could lie only in a splinter of a \
         splinter of their projection, so whether one exists is not decided",
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
        "no choice among the disjunctions of the integer constraints was settled",
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
            "refused: the disjunctions of the integer constraints would be searched in an \
             order chosen by name: `a`, `b`, `c`, `d` occur alike"
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
        Formula::Not(g) => Formula::Not(Arc::new(turned(std::slice::from_ref(&**g)).remove(0))),
        Formula::And(gs) => Formula::And(Arc::new(turned(gs))),
        Formula::Or(gs) => Formula::Or(Arc::new(turned(gs))),
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
