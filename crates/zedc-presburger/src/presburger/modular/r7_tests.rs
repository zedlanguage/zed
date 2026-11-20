//! Round-7 tests of the one-variable modular solver (PERF-negated-chain-xr).

use super::*;
use crate::scaling;
mod bench;

/// `x mod 3 == 2`, `0 <= x <= 10000`, and `n` atoms fixed one after another: `a_n == 1` and
/// `2 a_i == 2 a_(i+1)`, the rows written so that each pass of the constant propagation of
/// step 1 can fix only one more atom.
fn fixed_chain(n: usize) -> Formula {
    let atoms: Vec<_> = (0..=n)
        .map(|i| Atom::Sym(format!("f{i:06}").into()))
        .collect();
    let mut parts = Vec::new();
    for pair in atoms.windows(2) {
        parts.push(Formula::Con(Con::eq(
            &Lin::atom(pair[0].clone()).times(2),
            &Lin::atom(pair[1].clone()).times(2),
        )));
    }
    parts.push(Formula::Con(Con::eq(
        &Lin::atom(atoms[n].clone()),
        &Lin::constant(1),
    )));
    let x = Lin::atom(Atom::Sym("x".into()));
    let q = Lin::atom(Atom::Aux(0));
    let r = Lin::atom(Atom::Aux(1));
    parts.extend([
        Formula::Con(Con::eq(&x, &q.times(3).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(2), &r)),
        Formula::Con(Con::eq(&r, &Lin::constant(2))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(10000), &x)),
    ]);
    Formula::And(crate::presburger::Shared::new(parts))
}

/// `(x mod 6) mod 2 == 1 && 0 <= x <= 20`: `x = 6 q + r`, `r = 2 p + s`, the rows of the two
/// divisions in the order given by `inner_first`, and in the coordinates of `names`.
fn nested_remainder(inner_first: bool, names: [&str; 5]) -> Formula {
    let [x, q, r, p, s] = names.map(|n| Lin::atom(Atom::Sym(n.into())));
    let outer = vec![
        Formula::Con(Con::eq(&x, &q.times(6).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(5), &r)),
    ];
    let inner = vec![
        Formula::Con(Con::eq(&r, &p.times(2).plus(&s))),
        Formula::Con(Con::ge(&s, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(1), &s)),
    ];
    let (a, b) = if inner_first {
        (inner, outer)
    } else {
        (outer, inner)
    };
    let mut parts = a;
    parts.extend(b);
    parts.extend([
        Formula::Con(Con::eq(&s, &Lin::constant(1))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(20), &x)),
    ]);
    Formula::and(parts)
}

#[test]
fn nested_remainder_answers_do_not_depend_on_row_order() {
    // R7-CLAUDE-2: step 3 kept the first row that defines a remainder and skipped a later row
    // whose `x_root` an earlier row had defined. Each writing has the point x = 1.
    let mut got = Vec::new();
    for names in [
        ["x", "q", "r", "p", "s"],
        ["x", "a", "b", "c", "d"],
        ["z", "y", "w", "v", "u"],
    ] {
        for inner_first in [false, true] {
            let f = nested_remainder(inner_first, names);
            let answer = solve_modular(&f, true).map(|m| m.map(|m| f.holds(&m)));
            got.push((names[0], inner_first, answer));
        }
    }
    println!("NESTED {got:?}");
    assert!(got.iter().all(|g| g.2 == got[0].2), "{got:?}");
}

/// The small instances of the benchmark in `bench.rs`: each chain of fixed atoms has a point.
#[test]
fn the_benchmark_inputs_have_their_answers_at_small_sizes() {
    for n in 1..=8 {
        assert!(
            matches!(solve_modular(&fixed_chain(n), false), Some(Some(_))),
            "{n}"
        );
    }
}

#[test]
fn a_unit_whose_factors_are_fixed_outside_its_set_empties_the_regime() {
    // FAIL-omega-boundary-modes-flake: `x mod 6 == 2` fixes `x mod 2` and `x mod 3`, so
    // `x mod 12 in {5, 6}` became the empty clause, which the regime step skipped; it gave
    // the point 2, where `x mod 12 == 2`. No x has both: x mod 12 in {5, 6} gives x mod 6 in
    // {5, 0}.
    let i = |v: i64| Int::from(v);
    let units: BTreeMap<Int, ResidueSet> =
        [(i(6), vec![(i(2), i(2))]), (i(12), vec![(i(5), i(6))])]
            .into_iter()
            .collect();
    let (lo, hi) = (Some(i(0)), Some(i(16)));
    let mut stack = Vec::new();
    let step = solve_regime_step(&lo, &hi, units.clone(), vec![], &mut stack);
    assert!(matches!(step, RegimeOut::Empty), "step: {:?}", found(&step));
    let whole = solve_regime_in(&lo, &hi, units, vec![]);
    assert!(
        matches!(whole, RegimeOut::Empty),
        "whole: {:?}",
        found(&whole)
    );
}

/// The fails question of `c2` of the unit of seed 4236942624890658512 (FAIL-one-scope-pairs-
/// seed-refusal), with its bindings in place, over `x` alone: seven division pairs
/// `x == k q + r + c`, `0 <= r < k`, and the negation of the body. The first disjunct of the
/// body is written flat (`a && b && c`) or nested (`(a && b) && c`), as the projected side and
/// the body side of `Extending::defined_with` wrote it.
fn bound_c2(nested: bool) -> Formula {
    use crate::presburger::Shared;
    let x = Lin::atom(Atom::Sym("x".into()));
    let q = |n: u32| Lin::atom(Atom::Aux(n));
    let c = Lin::constant;
    let le = |a: &Lin, b: &Lin| Formula::Con(Con::ge(b, a));
    let eq = |a: &Lin, b: &Lin| Formula::Con(Con::eq(a, b));
    let and = |v: Vec<Formula>| Formula::And(Shared::new(v));
    let or = |v: Vec<Formula>| Formula::Or(Shared::new(v));
    let mut parts = c2_pairs();
    let first = if nested {
        and(vec![
            and(vec![eq(&q(20), &c(0)), le(&x, &c(39))]),
            le(&c(10), &q(21)),
        ])
    } else {
        and(vec![eq(&q(20), &c(0)), le(&x, &c(39)), le(&c(10), &q(21))])
    };
    let inner = and(vec![
        and(vec![
            and(vec![
                and(vec![eq(&q(1), &c(0)), le(&x, &c(36))]),
                le(&c(10), &q(3)),
            ]),
            eq(&q(7), &c(0)),
        ]),
        le(&c(10), &q(9)),
    ]);
    let body = or(vec![
        first,
        le(&q(17), &c(2)),
        and(vec![
            or(vec![
                inner,
                le(&q(17), &c(1)),
                and(vec![le(&c(3), &x), le(&x, &c(54))]),
            ]),
            le(&x, &c(81)),
        ]),
    ]);
    parts.push(Formula::Not(Shared::new(body)));
    and(parts)
}

/// The seven division pairs of [`bound_c2`]: `x == k q + r + c`, `0 <= r <= k - 1`.
fn c2_pairs() -> Vec<Formula> {
    let x = Lin::atom(Atom::Sym("x".into()));
    let q = |n: u32| Lin::atom(Atom::Aux(n));
    let c = Lin::constant;
    let mut parts = Vec::new();
    for (k, qn, rn, off) in [
        (5, 16, 17, 7),
        (3, 21, 22, 6),
        (4, 19, 20, 3),
        (5, 9, 10, 4),
        (6, 6, 7, 3),
        (3, 3, 4, 3),
        (4, 0, 1, 0),
    ] {
        parts.push(Formula::Con(Con::eq(
            &x,
            &q(qn).times(k).plus(&q(rn)).plus(&c(off)),
        )));
        parts.push(Formula::Con(Con::ge(&q(rn), &c(0))));
        parts.push(Formula::Con(Con::ge(&c(k - 1), &q(rn))));
    }
    parts
}

#[test]
fn the_fails_question_of_c2_is_answered_however_its_conjunctions_nest() {
    // FAIL-one-scope-pairs-seed-refusal: the two sides of `Extending::defined_with` gave this
    // formula nested two ways, which made the search read the disjuncts of one disjunction in
    // two orders; in one, the first choice it tried was a conjunction the Omega test refused
    // (Shadows), and the question was refused. x = 85 is a point: 85 >= 82, and
    // q17 = (85 - 7) mod 5 = 3, so no disjunct of the body holds.
    for nested in [false, true] {
        let f = bound_c2(nested);
        assert_eq!(
            crate::presburger::decide(&f),
            Ok(true),
            "nested: {nested}, {f}"
        );
    }
}

#[test]
fn division_pairs_with_a_lower_bound_have_their_point_found() {
    // The conjunction the search above tried: the pairs, `x >= 82` and `q17 >= 3`. The Omega
    // test refuses it (Shadows); `solve` gives the point the modular solver finds, checked
    // against every row.
    let x = Lin::atom(Atom::Sym("x".into()));
    let mut parts = c2_pairs();
    parts.push(Formula::Con(Con::ge(&x, &Lin::constant(82))));
    parts.push(Formula::Con(Con::ge(
        &Lin::atom(Atom::Aux(17)),
        &Lin::constant(3),
    )));
    let cons: Vec<Con> = parts
        .iter()
        .map(|g| match g {
            Formula::Con(c) => c.clone(),
            _ => unreachable!("rows only"),
        })
        .collect();
    let m = crate::presburger::solve(&cons, true)
        .expect("answered")
        .expect("a point");
    assert!(cons.iter().all(|c| c.holds_linear(&m)), "{m:?}");
    assert_eq!(
        crate::presburger::solve(&cons, false),
        Ok(Some(Model::new()))
    );
}

/// `n` division pairs `x == k q_i + r_i + c_i`, `0 <= r_i <= k - 1`, with k going through
/// 5, 3, 4, 6 and `c_i = i mod 7`, and `x >= 82`, `r_0 >= 3`: the shape of
/// [`division_pairs_with_a_lower_bound_have_their_point_found`] at any size, for the benchmark
/// of `solve`'s answer where the Omega test refuses.
fn division_pairs(n: usize) -> Vec<Con> {
    let x = Lin::atom(Atom::Sym("x".into()));
    let c = Lin::constant;
    let mut cons = Vec::new();
    for i in 0..n {
        let k = [5, 3, 4, 6][i % 4];
        let (q, r) = (
            Lin::atom(Atom::Aux(2 * i as u32)),
            Lin::atom(Atom::Aux(2 * i as u32 + 1)),
        );
        cons.push(Con::eq(&x, &q.times(k).plus(&r).plus(&c((i % 7) as i64))));
        cons.push(Con::ge(&r, &c(0)));
        cons.push(Con::ge(&c(k - 1), &r));
    }
    cons.push(Con::ge(&x, &c(82)));
    cons.push(Con::ge(&Lin::atom(Atom::Aux(1)), &c(3)));
    cons
}

#[test]
fn division_pairs_have_their_point_found_where_the_omega_test_refuses() {
    // The small instances of `bench::division_pairs_scale`. From 7 pairs the Omega test alone
    // refuses (Shadows; 2026-11-16), so the benchmark times the answer `solve` gives in its
    // place; below that it answers.
    for n in [1, 2, 3, 4, 7, 8, 16] {
        let cons = division_pairs(n);
        let omega = crate::presburger::solve_omega(&cons, false);
        assert_eq!(omega.is_err(), n >= 7, "{n}: {omega:?}");
        let m = crate::presburger::solve(&cons, true);
        let m = m.expect("answered").expect("a point");
        assert!(cons.iter().all(|c| c.holds_linear(&m)), "{n}: {m:?}");
    }
}

#[test]
fn an_unbounded_regime_whose_clause_repeats_its_unit_is_decided() {
    // FAIL-modular-unbounded-regime-undecided (seed 2125, case 28 of
    // `one_scope::one_variable_boundary_modes_do_not_depend_on_names`): the regime with no
    // bound, `x mod 10 != 8 && (x mod 8 != 4 || x mod 10 != 8)`, as `solve_regime` writes it.
    // x = 0 holds both.
    let i = |v: i64| Int::from(v);
    let not8: ResidueSet = vec![(i(0), i(7)), (i(9), i(9))];
    let units: BTreeMap<Int, ResidueSet> = [(i(10), not8.clone())].into_iter().collect();
    let clauses = vec![BTreeMap::from([
        (i(8), vec![(i(0), i(3)), (i(5), i(7))]),
        (i(10), not8),
    ])];
    let out = solve_regime_in(&None, &None, units.clone(), clauses.clone());
    let x = found(&out).expect("a point");
    assert!(holds_modular_point(&x, &units, &clauses), "{x:?}");
    // The whole formula, with its aliases and remainders as the test drew it.
    let f = seed_2125_case_28();
    let m = solve_modular(&f, true);
    let m = m.expect("decided").expect("a point");
    assert!(f.holds(&m), "{m:?}");
}

/// The small instances of `bench::absorbed_clauses_scale`: each has a point, and each clause
/// holds there.
#[test]
fn absorbed_clauses_have_their_point_found() {
    for n in [1, 2, 3, 8, 50] {
        let (units, clauses) = absorbed_clauses(n);
        let out = solve_regime_in(&None, &None, units.clone(), clauses.clone());
        let x = found(&out).unwrap_or_else(|| panic!("{n}: a point"));
        assert!(holds_modular_point(&x, &units, &clauses), "{n}: {x:?}");
    }
}

/// `x mod 10 != 8` and `n` clauses `x mod p_i == 0 || x mod 10 != 8` over the primes
/// `p_i` from 11: each clause repeats the unit, so the regime is the unit alone.
pub(super) fn absorbed_clauses(
    n: usize,
) -> (BTreeMap<Int, ResidueSet>, Vec<BTreeMap<Int, ResidueSet>>) {
    let i = |v: i64| Int::from(v);
    let not8: ResidueSet = vec![(i(0), i(7)), (i(9), i(9))];
    let units: BTreeMap<Int, ResidueSet> = [(i(10), not8.clone())].into_iter().collect();
    // Every prime from 2, by trial division by the primes found so far; the first four (2, 3,
    // 5, 7) share a factor with 10 or are skipped so each clause's modulus is new.
    let mut primes: Vec<i64> = Vec::with_capacity(n + 4);
    let mut k = 2;
    while primes.len() < n + 4 {
        if primes
            .iter()
            .take_while(|p| *p * *p <= k)
            .all(|p| k % p != 0)
        {
            primes.push(k);
        }
        k += 1;
    }
    let clauses = (primes.into_iter().skip(4))
        .map(|p| BTreeMap::from([(i(p), vec![(i(0), i(0))]), (i(10), not8.clone())]))
        .collect();
    (units, clauses)
}

/// A clause whose literal on a unit's modulus does not hold the unit's set is kept: with the
/// unit `x mod 10 in {3, 4}`, the clause `x mod 10 == 4 || x mod 7 == 2` leaves `x = 3` out
/// unless `x mod 7 == 2`, and the clause `x mod 10 == 5` leaves no point.
#[test]
fn a_clause_the_units_do_not_imply_is_kept() {
    let i = |v: i64| Int::from(v);
    let units: BTreeMap<Int, ResidueSet> = [(i(10), vec![(i(3), i(4))])].into_iter().collect();
    let clauses = vec![BTreeMap::from([
        (i(10), vec![(i(4), i(4))]),
        (i(7), vec![(i(2), i(2))]),
    ])];
    let out = solve_regime_in(&None, &None, units.clone(), clauses.clone());
    let x = found(&out).expect("a point");
    assert!(holds_modular_point(&x, &units, &clauses), "{x:?}");
    let none = vec![BTreeMap::from([(i(10), vec![(i(5), i(5))])])];
    let out = solve_regime_in(&None, &None, units, none);
    assert!(found(&out).is_none(), "{:?}", found(&out));
}

/// [`res_within`] against the definition, on every pair of sets modulo 1 to 6.
#[test]
fn res_within_is_the_subset_test() {
    let set = |bits: u32, m: i64| -> ResidueSet {
        res_normalize(
            (0..m)
                .filter(|r| bits >> r & 1 == 1)
                .map(|r| (Int::from(r), Int::from(r)))
                .collect(),
            &Int::from(m),
        )
    };
    for m in 1..=6i64 {
        for a in 0..1u32 << m {
            for b in 0..1u32 << m {
                let want = a & !b == 0;
                assert_eq!(
                    res_within(&set(a, m), &set(b, m), &Int::from(m)),
                    want,
                    "{m} {a:b} {b:b}"
                );
            }
        }
    }
}

/// The formula of seed 2125, case 28, of
/// `one_scope::one_variable_boundary_modes_do_not_depend_on_names`, as that test drew it.
fn seed_2125_case_28() -> Formula {
    let s = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let q = |i: u32| Lin::atom(Atom::Aux(i));
    let c = |v: i64| Lin::constant(v);
    let con = |c: Con| Formula::Con(c);
    let not = |c: Con| Formula::Not(crate::presburger::Shared::new(Formula::Con(c)));
    let (x, x1, x2, x3) = (s("x"), s("x@1"), s("x@2"), s("x@3"));
    let mut parts = vec![
        con(Con::eq(&x, &x1.minus(&c(1)))),
        con(Con::eq(&x1, &x2.minus(&c(5)))),
        con(Con::eq(&x2, &x3.plus(&c(7)))),
    ];
    for (v, k, qi, off) in [
        (&x1, 10, 0, 0),
        (&x3, 4, 2, 5),
        (&x1, 8, 4, 0),
        (&x3, 4, 6, 5),
        (&x2, 2, 8, 3),
    ] {
        parts.push(con(Con::eq(
            v,
            &q(qi).times(k).plus(&q(qi + 1)).plus(&c(off)),
        )));
        parts.push(con(Con::ge(&q(qi + 1), &c(0))));
        parts.push(con(Con::ge(&c(k - 1), &q(qi + 1))));
    }
    parts.push(Formula::or(vec![
        not(Con::eq(&q(1), &c(0))),
        not(Con::eq(&q(5), &c(6))),
    ]));
    parts.push(not(Con::eq(&q(1), &c(0))));
    Formula::and(parts)
}

/// The point a regime's answer gives, for messages.
fn found(out: &RegimeOut) -> Option<Int> {
    match out {
        RegimeOut::Found(x) => Some(x.clone()),
        _ => None,
    }
}

/// `sweep_bounded` (FAIL-omega-negations-slow-13254895221319191796) gives the least point of
/// `[l, h]` that every unit and every clause holds, or none, as testing each point does: over
/// 500 drawn regimes of 1 to 4 units and 0 to 12 clauses of 1 to 3 literals over the moduli
/// 2 to 9, with intervals from 1 point to past the period, and at the regime of chain 1 of
/// seed 13254895221319191796, `[12, 23]` under clauses over the moduli 2 to 8.
#[test]
fn a_short_interval_over_many_moduli_is_decided_by_the_sweep() {
    let holds = |x: i64, m: i64, s: &[(i64, i64)]| {
        let r = x.rem_euclid(m);
        s.iter().any(|&(a, b)| a <= r && r <= b)
    };
    type Lits = Vec<(i64, Vec<(i64, i64)>)>;
    let check = |l: i64, h: i64, units: &Lits, clauses: &[Lits]| {
        let set = |s: &[(i64, i64)]| -> ResidueSet {
            s.iter()
                .map(|&(a, b)| (Int::from(a), Int::from(b)))
                .collect()
        };
        let unit_mods: BTreeMap<Int, ResidueSet> =
            units.iter().map(|(m, s)| (Int::from(*m), set(s))).collect();
        let cls: Vec<BTreeMap<Int, ResidueSet>> = clauses
            .iter()
            .map(|cl| cl.iter().map(|(m, s)| (Int::from(*m), set(s))).collect())
            .collect();
        let want = (l..=h).find(|&x| {
            units.iter().all(|(m, s)| holds(x, *m, s))
                && clauses
                    .iter()
                    .all(|cl| cl.iter().any(|(m, s)| holds(x, *m, s)))
        });
        let got = sweep_bounded(&Int::from(l), &Int::from(h), &unit_mods, &cls);
        assert_eq!(
            found(&got),
            want.map(Int::from),
            "[{l}, {h}] units {units:?} clauses {clauses:?}"
        );
        if want.is_none() {
            assert!(matches!(got, RegimeOut::Empty));
        }
        want.is_some()
    };
    // A regime of the shape of `p9`'s question in chain 1 of seed 13254895221319191796: its
    // bounds `[12, 23]` and units as the walk gave them to `solve_regime_step`; the clauses
    // written by hand from the chain's residue conditions, not taken from the walk.
    let not = |m: i64, r: i64| -> Vec<(i64, i64)> {
        [(0, r - 1), (r + 1, m - 1)]
            .into_iter()
            .filter(|(a, b)| a <= b)
            .collect()
    };
    check(
        12,
        23,
        &vec![(2, vec![(0, 0)]), (8, vec![(0, 0), (2, 7)])],
        &[
            vec![(7, vec![(5, 5)]), (5, not(5, 1))],
            vec![(3, vec![(2, 2)]), (4, not(4, 1))],
            vec![(6, vec![(4, 4)]), (7, not(7, 1))],
            vec![(9, not(9, 4))],
        ],
    );
    // A small linear congruential generator (Knuth's MMIX constants), so the draws are fixed.
    let mut state = 0x5eed_u64;
    let mut below = |n: i64| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 33) % n as u64) as i64
    };
    let lit = |below: &mut dyn FnMut(i64) -> i64| {
        let m = 2 + below(8);
        let a = below(m);
        let b = a + below(m - a);
        (m, vec![(a, b)])
    };
    // One literal per modulus in a unit list and in a clause, as the maps hold them.
    let lits = |k: i64, below: &mut dyn FnMut(i64) -> i64| -> Lits {
        let by_modulus: BTreeMap<i64, Vec<(i64, i64)>> = (0..k).map(|_| lit(below)).collect();
        by_modulus.into_iter().collect()
    };
    let mut with_point = 0;
    for _ in 0..500 {
        let k = 1 + below(4);
        let units = lits(k, &mut below);
        let clauses: Vec<Lits> = (0..below(13))
            .map(|_| {
                let k = 1 + below(3);
                lits(k, &mut below)
            })
            .collect();
        let l = below(200) - 100;
        let h = l + below(3000) - 2;
        with_point += usize::from(check(l, h, &units, &clauses));
    }
    // Both answers are drawn often, so neither is checked only by chance.
    assert!(
        (60..=440).contains(&with_point),
        "{with_point} of 500 with a point"
    );
}

/// Under a cover's meter, `sweep_bounded` is charged its pieces before it makes them
/// (`meter::charge_pieces`): `x mod 2 == 0 && x mod 991 == 5 && x mod 997 == 1` on
/// `[0, 1000000]`, a span shorter than the period 1,976,054, has about 500,000 pieces of
/// modulus 2, 8,000,000 units past [`meter::EXACT_LIMIT`]'s 3,100,000, so the question is
/// refused there; with no limit the sweep answers as testing each point does.
#[test]
fn a_sweep_past_the_limit_is_refused_under_the_meter() {
    use super::super::meter::{EXACT_LIMIT, Work};
    use super::super::{Refusal, SOLVER};
    let unit_mods: BTreeMap<Int, ResidueSet> = [(2, 0), (991, 5), (997, 1)]
        .into_iter()
        .map(|(m, r)| (Int::from(m), vec![(Int::from(r), Int::from(r))]))
        .collect();
    let (l, h) = (Int::ZERO, Int::from(1_000_000));
    let work = |limit: u64| Work {
        used: 0,
        limit,
        solver: SOLVER,
    };
    let refused = work(EXACT_LIMIT).metered(|| sweep_bounded(&l, &h, &unit_mods, &[]));
    assert!(
        matches!(refused, Err(Refusal::Questions)),
        "{:?}",
        refused.map(|o| found(&o))
    );
    let want = (0..=1_000_000_i64).find(|x| x % 2 == 0 && x % 991 == 5 && x % 997 == 1);
    let answered = work(u64::MAX).metered(|| sweep_bounded(&l, &h, &unit_mods, &[]));
    let Ok(out) = answered else {
        panic!("refused with no limit");
    };
    assert_eq!(found(&out), want.map(Int::from));
}
