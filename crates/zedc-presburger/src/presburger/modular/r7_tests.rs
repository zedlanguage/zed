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

/// A regime with both bounds is decided by `solve_regime_in`, never left undecided, and its
/// answer is that of testing each point (FAIL-omega-negations-slow-7837918895420161952). The
/// draws hold residue sets of up to two intervals over composite moduli, as `x mod 6 in {0,
/// 2..5}` (that is, `x mod 6 != 1`), which is no product of a set modulo 2 and a set modulo 3, so
/// `literal_to_base_cnf` cannot write it on the coprime base and the regime was left to the
/// general path, which took past 60 s on the chains of that seed. The first case is written by
/// hand in the shape of the regime the walk gave there (`[0, 20]` with such a literal beside
/// residues modulo 11 and 8); the base decided it before the fix, so the draws are what fail
/// without it (the first undecided draw: `[-73, 193]` under clauses over 6, 7, 9, 10, 12, 13).
#[test]
fn a_bounded_regime_the_base_cannot_write_is_decided() {
    check_regime(
        Some(0),
        Some(20),
        &vec![(11, vec![(0, 3), (5, 10)])],
        &[
            vec![(6, vec![(0, 0), (2, 5)]), (8, vec![(0, 5), (7, 7)])],
            vec![(6, vec![(0, 2), (4, 5)]), (11, vec![(4, 4)])],
        ],
    );
    let mut state = 0x7837_u64;
    let mut below = |n: i64| lcg_below(&mut state, n);
    let mut with_point = 0;
    for _ in 0..500 {
        let units = draw_lits(1 + below(3), &mut below);
        let clauses: Vec<Lits> = (0..below(8))
            .map(|_| draw_lits(1 + below(3), &mut below))
            .collect();
        let l = below(200) - 100;
        let h = l + below(400);
        with_point += usize::from(check_regime(Some(l), Some(h), &units, &clauses));
    }
    assert!(
        (60..=440).contains(&with_point),
        "{with_point} of 500 with a point"
    );
}

/// A regime with one bound is decided by `solve_regime_in` on one period of its moduli past the
/// bound, never left undecided, and its answer is that of testing each point of that period
/// (FAIL-omega-negations-slow-7837918895420161952, the 4 refusals left in
/// `bench::one_scope::the_5000_one_variable_modular_formulas_of_seed_0x70dec1de_match_enumeration`:
/// each a variable with one lower bound and residue conditions). The draws are those of
/// [`a_bounded_regime_the_base_cannot_write_is_decided`] with one bound dropped, half of them the
/// upper one; without the sweep of one period, some are left undecided.
#[test]
fn a_regime_with_one_bound_the_base_cannot_write_is_decided() {
    let mut state = 0x0b0d_u64;
    let mut below = |n: i64| lcg_below(&mut state, n);
    let mut with_point = 0;
    for i in 0..300 {
        let units = draw_lits(1 + below(3), &mut below);
        let clauses: Vec<Lits> = (0..below(8))
            .map(|_| draw_lits(1 + below(3), &mut below))
            .collect();
        let b = below(200) - 100;
        let (lo, hi) = if i % 2 == 0 {
            (Some(b), None)
        } else {
            (None, Some(b))
        };
        with_point += usize::from(check_regime(lo, hi, &units, &clauses));
    }
    assert!(
        (40..=290).contains(&with_point),
        "{with_point} of 300 with a point"
    );
}

/// A regime with no bound is decided by `solve_regime_in` on one period `[0, p - 1]` of its
/// moduli, never left undecided, and its answer is that of testing each point of that period
/// (PRES-one-variable-no-bound-witness). The draws are those of
/// [`a_regime_with_one_bound_the_base_cannot_write_is_decided`] (seed 0x0b0e) with no bound;
/// without the sweep, some are left undecided. That the window's start does not depend on the
/// names is a property of the coordinate `solve_regime` writes, tested by
/// `one_scope::one_variable_answers_do_not_depend_on_names` and the tests named with it.
#[test]
fn a_regime_with_no_bound_the_base_cannot_write_is_decided() {
    let mut state = 0x0b0e_u64;
    let mut below = |n: i64| lcg_below(&mut state, n);
    let mut with_point = 0;
    for _ in 0..300 {
        let units = draw_lits(1 + below(3), &mut below);
        let clauses: Vec<Lits> = (0..below(8))
            .map(|_| draw_lits(1 + below(3), &mut below))
            .collect();
        with_point += usize::from(check_regime(None, None, &units, &clauses));
    }
    assert!(
        (40..=290).contains(&with_point),
        "{with_point} of 300 with a point"
    );
}

/// The input of `bench::a_regime_with_one_bound_and_n_clauses_scales`: the first draw of
/// [`a_regime_with_one_bound_the_base_cannot_write_is_decided`] that was undecided before the
/// sweep of one period, `[81, inf)` under units `x mod 8 == 7`, `x mod 12 in {6, 7, 9..11}`, `x mod
/// 13 in {2..7, 12}` and clauses whose second, `x mod 8 in 4..6`, the unit modulo 8 contradicts, so
/// the regime is empty; and `n` clauses more, the `i`-th `x mod 4 == i mod 4 || x mod 9 == i mod
/// 9`. Every modulus divides 4,680, so the period swept stays the same at every `n`.
pub(super) fn one_bound_clauses(
    n: usize,
) -> (
    Int,
    BTreeMap<Int, ResidueSet>,
    Vec<BTreeMap<Int, ResidueSet>>,
) {
    let i = |v: i64| Int::from(v);
    let set = |s: &[(i64, i64)]| -> ResidueSet { s.iter().map(|&(a, b)| (i(a), i(b))).collect() };
    let units: BTreeMap<Int, ResidueSet> = [
        (i(8), set(&[(7, 7)])),
        (i(12), set(&[(6, 7), (9, 11)])),
        (i(13), set(&[(2, 7), (12, 12)])),
    ]
    .into_iter()
    .collect();
    let mut clauses: Vec<BTreeMap<Int, ResidueSet>> = vec![
        [
            (i(4), set(&[(0, 0), (2, 2)])),
            (i(9), set(&[(1, 4), (6, 8)])),
            (i(13), set(&[(5, 9), (11, 11)])),
        ]
        .into_iter()
        .collect(),
        [(i(8), set(&[(4, 6)]))].into_iter().collect(),
        [
            (i(3), set(&[(0, 0), (2, 2)])),
            (i(10), set(&[(9, 9)])),
            (i(12), set(&[(4, 8), (10, 11)])),
        ]
        .into_iter()
        .collect(),
    ];
    for k in 0..n as i64 {
        clauses.push(
            [
                (i(4), set(&[(k % 4, k % 4)])),
                (i(9), set(&[(k % 9, k % 9)])),
            ]
            .into_iter()
            .collect(),
        );
    }
    (i(81), units, clauses)
}

/// [`one_bound_clauses`] at small sizes: the coprime base leaves it undecided, so the sweep of one
/// period is what decides it, and it is empty.
#[test]
fn one_bound_clauses_are_empty_and_left_by_the_base() {
    for n in 0..=8 {
        let (l, units, clauses) = one_bound_clauses(n);
        assert!(
            matches!(
                solve_on_bases(&Some(l.clone()), &None, &units, &clauses, &mut false),
                RegimeOut::Undecided
            ),
            "{n}"
        );
        let out = solve_regime_in(&Some(l), &None, units, clauses);
        assert!(matches!(out, RegimeOut::Empty), "{n}: {:?}", found(&out));
    }
}

/// The literals of a unit or a clause: `(m, s)` is `x mod m` in the intervals `s`.
type Lits = Vec<(i64, Vec<(i64, i64)>)>;

/// Whether `x mod m` lies in one of the intervals `s`.
fn residue_holds(x: i64, m: i64, s: &[(i64, i64)]) -> bool {
    let r = x.rem_euclid(m);
    s.iter().any(|&(a, b)| a <= r && r <= b)
}

/// Whether `x` meets every unit and some literal of every clause.
fn regime_holds(x: i64, units: &Lits, clauses: &[Lits]) -> bool {
    units.iter().all(|(m, s)| residue_holds(x, *m, s))
        && clauses
            .iter()
            .all(|cl| cl.iter().any(|(m, s)| residue_holds(x, *m, s)))
}

/// Solves the regime `lo <= x <= hi` (a missing bound is no bound) under `units` and `clauses`
/// by `solve_regime_in`, checks its answer against testing each point, and returns whether a
/// point lies. With both bounds every point is tested; with one, the period `p`, the lcm of the
/// moduli, past it: `[l, l + p - 1]` or `[h - p + 1, h]`. That is exact: each literal reads `x mod
/// m` for an `m` dividing `p`, so `x` and `x - k p` meet the same literals, and a point `x >= l`
/// gives the point `x - ((x - l) div p) p` of `[l, l + p - 1]` (likewise below `h`). A point
/// found is checked against the bounds given and every literal directly.
fn check_regime(lo: Option<i64>, hi: Option<i64>, units: &Lits, clauses: &[Lits]) -> bool {
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
    let p = units
        .iter()
        .chain(clauses.iter().flatten())
        .fold(1i64, |p, (m, _)| p / gcd_i64(p, *m) * m);
    let (l, h) = match (lo, hi) {
        (Some(l), Some(h)) => (l, h),
        (Some(l), None) => (l, l + p - 1),
        (None, Some(h)) => (h - p + 1, h),
        (None, None) => (0, p - 1),
    };
    let want = (l..=h).any(|x| regime_holds(x, units, clauses));
    let (lo_int, hi_int) = (lo.map(Int::from), hi.map(Int::from));
    let got = solve_regime_in(&lo_int, &hi_int, unit_mods.clone(), cls.clone());
    let what = format!("[{lo:?}, {hi:?}] units {units:?} clauses {clauses:?}");
    match got {
        // Past `SWEEP_SWITCHOVER` the regime goes to the general path, which must decide its
        // formula the same way.
        RegimeOut::Undecided => {
            let f = regime_formula(lo_int.as_ref(), hi_int.as_ref(), &unit_mods, &cls);
            assert_eq!(
                super::super::decide_named(&f),
                Ok(want),
                "general path: {what}"
            );
        }
        RegimeOut::Empty => assert!(!want, "empty, but a point lies: {what}"),
        RegimeOut::Found(x) => {
            let x = x.to_i128().expect("small") as i64;
            assert!(want, "{x}, but none lies: {what}");
            assert!(
                lo.is_none_or(|l| l <= x) && hi.is_none_or(|h| x <= h),
                "{x} out of the bounds: {what}"
            );
            assert!(regime_holds(x, units, clauses), "{x} is no point: {what}");
        }
    }
    want
}

/// The gcd of two positive integers.
fn gcd_i64(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd_i64(b, a % b) }
}

/// The next draw below `n` of a small linear congruential generator (Knuth's MMIX constants),
/// so the draws are fixed by the seed.
fn lcg_below(state: &mut u64, n: i64) -> i64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    ((*state >> 33) % n as u64) as i64
}

/// The literals of `k` draws, one per modulus (a later draw over the same modulus replaces an
/// earlier one), each one or two intervals of residues modulo 2 to 13, as a normal list (sorted,
/// disjoint, not adjacent).
fn draw_lits(k: i64, below: &mut dyn FnMut(i64) -> i64) -> Lits {
    let mut lit = || {
        let m = 2 + below(12);
        let a = below(m);
        let b = a + below(m - a);
        let mut s = vec![(a, b)];
        if b + 2 < m {
            let c = b + 2 + below(m - b - 2);
            s.push((c, c + below(m - c)));
        }
        (m, s)
    };
    let by_modulus: BTreeMap<i64, Vec<(i64, i64)>> = (0..k).map(|_| lit()).collect();
    by_modulus.into_iter().collect()
}

/// A cover's work at the limit of its meter, or with no limit.
fn work(limit: u64) -> super::super::meter::Work {
    super::super::meter::Work {
        used: 0,
        limit,
        solver: super::super::SOLVER,
    }
}

/// Units `x mod m in {r}`, one for each pair.
fn point_units(pairs: &[(i64, i64)]) -> BTreeMap<Int, ResidueSet> {
    pairs
        .iter()
        .map(|&(m, r)| (Int::from(m), vec![(Int::from(r), Int::from(r))]))
        .collect()
}

/// The split of `k` smallest moduli, with their lcm, where it is at most 10,000: past the
/// windows of about 3,000 points the test draws, so splits read modulo more residues than the
/// window has are tried too, while a tree of 100,000 residues made the test take 15 s alone in a
/// debug build at load 33, against the limit of the unit-test piece (merge check of pres10).
fn split_of(weights: &BTreeMap<Int, u128>, k: usize) -> Option<(BTreeSet<&Int>, usize)> {
    let small: BTreeSet<&Int> = weights.keys().take(k).collect();
    let mut q = Int::ONE;
    for m in &small {
        q = &q.div_floor(&q.gcd(m)) * *m;
    }
    let q = q.to_i128().and_then(|v| usize::try_from(v).ok())?;
    (q <= 10_000).then_some((small, q))
}

/// Under a cover's meter, `sweep_bounded` is charged its work before it does it
/// (`meter::charge_pieces`). The units `x mod p in [0, p) - {r_p}` for the 12 primes from 101
/// to 157 on `[0, 2000000]` are simultaneous incongruences (Garey and Johnson 1979, p. 249,
/// problem AN2, quoted in the crate's `lib.rs`, References), the class that
/// [`cheapest_split`] leaves costly at every split: cutting every modulus makes about 2 * 12 *
/// 2000000 / 125 = 380,000 pieces, 6,100,000 units past [`meter::EXACT_LIMIT`]'s 3,100,000, and
/// reading the smallest primes modulo their product costs more (the bound of each split is
/// checked by `the_split_is_the_one_of_least_bound`). So the question is refused there, with
/// the message of `Refusal::Questions`; with no limit the sweep answers as testing each point
/// does.
#[test]
fn a_sweep_past_the_limit_is_refused_under_the_meter() {
    use super::super::Refusal;
    use super::super::meter::EXACT_LIMIT;
    let primes = [101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157];
    let units: Vec<(i64, i64)> = (0..)
        .zip(primes)
        .map(|(i, p)| (p, (7 * i + 3) % p))
        .collect();
    let unit_mods: BTreeMap<Int, ResidueSet> = units
        .iter()
        .map(|&(m, r)| {
            let s = [(0, r - 1), (r + 1, m - 1)]
                .into_iter()
                .filter(|(a, b)| a <= b)
                .map(|(a, b)| (Int::from(a), Int::from(b)))
                .collect();
            (Int::from(m), s)
        })
        .collect();
    let (l, h) = (Int::ZERO, Int::from(2_000_000));
    let refused = work(EXACT_LIMIT).metered(|| sweep_bounded(&l, &h, &unit_mods, &[]));
    let Err(why) = refused else {
        panic!("answered under the limit: {:?}", refused.map(|o| found(&o)));
    };
    assert_eq!(why, Refusal::Questions);
    assert!(
        why.to_string()
            .contains("Here those questions would take more work than the checker allows."),
        "{why}"
    );
    let want = (0..=2_000_000_i64).find(|x| units.iter().all(|&(m, r)| x % m != r));
    let answered = work(u64::MAX).metered(|| sweep_bounded(&l, &h, &unit_mods, &[]));
    let Ok(out) = answered else {
        panic!("refused with no limit");
    };
    assert_eq!(found(&out), want.map(Int::from));
}

/// `x mod 2 == 0 && x mod 991 == 5 && x mod 997 == 1` on `[0, 1000000]`, a span shorter than
/// the period 1,976,054, which the meter refused when every modulus was cut into pieces (about
/// 500,000 of modulus 2, 8,000,000 units past [`meter::EXACT_LIMIT`]'s 3,100,000; that sweep is
/// the split with no small modulus, refused here as the negative control). Read modulo 2, the
/// smallest modulus leaves about 2,000 pieces of the others, and the question is answered under
/// the limit, as testing each point answers it (PERF-sweep-bounded-wide-interval).
#[test]
fn a_wide_window_cut_by_large_moduli_is_answered_under_the_meter() {
    use super::super::Refusal;
    use super::super::meter::EXACT_LIMIT;
    let unit_mods = point_units(&[(2, 0), (991, 5), (997, 1)]);
    let (l, h) = (Int::ZERO, Int::from(1_000_000));
    let want = (0..=1_000_000_i64).find(|x| x % 2 == 0 && x % 991 == 5 && x % 997 == 1);
    let answered = work(EXACT_LIMIT).metered(|| sweep_bounded(&l, &h, &unit_mods, &[]));
    let Ok(out) = answered else {
        panic!("refused under the limit");
    };
    assert_eq!(found(&out), want.map(Int::from));
    let (e, _) = sweep_window(&l, &h, &unit_mods, &[]);
    let cut_all =
        work(EXACT_LIMIT).metered(|| sweep_split(&l, &e, &unit_mods, &[], &BTreeSet::new(), 1));
    assert!(
        matches!(cut_all, Err(Refusal::Questions)),
        "{:?}",
        cut_all.map(|o| found(&o))
    );
}

/// A window `[l, h]` and a regime on it: its units and its clauses.
pub(super) type Window = (
    Int,
    Int,
    BTreeMap<Int, ResidueSet>,
    Vec<BTreeMap<Int, ResidueSet>>,
);

/// A regime on a window of about 2^107 points from 2^200 on: the unit `x mod P == 0` with `P =
/// 2^100 + 3`, and `n` clauses `x mod Q_j in [0, Q_j div 2] || x mod m_j == r_j`, with `Q_j =
/// 2^101 + 2 j + 1` and `m_j` from 4, 6, 9 and 10. Cutting every modulus into pieces makes
/// about 2^105 of modulus 4; read modulo 180, the small moduli leave about `100 + 50 n` pieces
/// of the large ones. With `empty`, also the unit `x mod 2 == 1` and the clause `x mod 4 in {0,
/// 2}`, which no point meets, so the walk passes every event of the window before it answers
/// `Empty`, at every `n` alike. The window and its regime, for the tests and the benchmark.
pub(super) fn wide_clauses(n: usize, periods: i64, empty: bool) -> Window {
    let p = &Int::pow2(100) + &Int::from(3);
    let l = &Int::pow2(200) + &Int::from(12_345);
    let h = &l + &(&p * &Int::from(periods));
    let mut unit_mods: BTreeMap<Int, ResidueSet> = [(p, vec![(Int::ZERO, Int::ZERO)])].into();
    let small = [4i64, 6, 9, 10];
    let mut clauses: Vec<BTreeMap<Int, ResidueSet>> = (0..n)
        .map(|j| {
            let q = &Int::pow2(101) + &Int::from(2 * j as i64 + 1);
            let half = q.div_floor(&Int::from(2));
            let m = small[j % small.len()];
            let r = Int::from((3 * j as i64 + 1) % m);
            [
                (q, vec![(Int::ZERO, half)]),
                (Int::from(m), vec![(r.clone(), r)]),
            ]
            .into()
        })
        .collect();
    if empty {
        unit_mods.insert(Int::from(2), vec![(Int::ONE, Int::ONE)]);
        let even = vec![(Int::ZERO, Int::ZERO), (Int::from(2), Int::from(2))];
        clauses.push([(Int::from(4), even)].into());
    }
    (l, h, unit_mods, clauses)
}

/// The least point of [`wide_clauses`]' regime by testing each candidate: every point is a
/// multiple of `P`, so the candidates are the multiples of `P` in the window, `periods + 1` of
/// them at most.
fn wide_clauses_by_candidates(
    l: &Int,
    h: &Int,
    unit_mods: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> Option<Int> {
    let p = unit_mods.keys().next_back().expect("the unit over P");
    let mut x = &l.div_ceil(p) * p;
    while &x <= h {
        if holds_modular_point(&x, unit_mods, clauses) {
            return Some(x);
        }
        x = &x + p;
    }
    None
}

/// [`wide_clauses`] with 1 to 6 clauses over 100 periods of `P`, with and without the
/// conditions that empty it, answered under a cover's meter as testing each multiple of `P`
/// answers it. Cutting every modulus into pieces, the split with no small modulus, is refused
/// there (the negative control), as `sweep_bounded` was before PERF-sweep-bounded-wide-interval.
#[test]
fn a_window_of_200_bits_is_answered_under_the_meter() {
    use super::super::Refusal;
    use super::super::meter::EXACT_LIMIT;
    for empty in [false, true] {
        for n in 1..=6 {
            let what = format!("{n} clauses, empty {empty}");
            let (l, h, unit_mods, clauses) = wide_clauses(n, 100, empty);
            let want = wide_clauses_by_candidates(&l, &h, &unit_mods, &clauses);
            if empty {
                assert_eq!(want, None, "{what}");
            }
            let answered =
                work(EXACT_LIMIT).metered(|| sweep_bounded(&l, &h, &unit_mods, &clauses));
            let Ok(out) = answered else {
                panic!("{what}: refused under the limit");
            };
            assert_eq!(found(&out), want, "{what}");
            if want.is_none() {
                assert!(matches!(out, RegimeOut::Empty), "{what}");
            }
            let (e, _) = sweep_window(&l, &h, &unit_mods, &clauses);
            let cut_all = work(EXACT_LIMIT)
                .metered(|| sweep_split(&l, &e, &unit_mods, &clauses, &BTreeSet::new(), 1));
            assert!(matches!(cut_all, Err(Refusal::Questions)), "{what}");
        }
    }
}

/// [`sweep_split`] at every split of the moduli (the `k` smallest read modulo their lcm, for
/// each `k` whose lcm is at most 10,000) and `sweep_bounded` give the least point of `[l, h]`
/// that every unit and clause holds, or none, as testing each point does: over 400 drawn
/// regimes of 1 to 4 units and 0 to 10 clauses of 1 to 3 literals, each modulus small (2 to 9)
/// or large (30 to 300) by a coin, on intervals from 1 point to about 3,000.
#[test]
fn every_split_of_the_moduli_decides_a_regime_as_testing_each_point_does() {
    let holds = |x: i64, m: i64, s: &[(i64, i64)]| {
        let r = x.rem_euclid(m);
        s.iter().any(|&(a, b)| a <= r && r <= b)
    };
    type Lits = Vec<(i64, Vec<(i64, i64)>)>;
    // Knuth's MMIX constants, so the draws are fixed.
    let mut state = 0x5eed_5917_u64;
    let mut below = |n: i64| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 33) % n as u64) as i64
    };
    let lit = |below: &mut dyn FnMut(i64) -> i64| {
        let m = if below(2) == 0 {
            2 + below(8)
        } else {
            30 + below(271)
        };
        let a = below(m);
        let b = a + below(m - a);
        let mut s = vec![(a, b)];
        // Now and then a second interval, so a literal's set is not always one run.
        if b + 2 < m && below(3) == 0 {
            let c = b + 2 + below(m - b - 2);
            s.push((c, c + below(m - c)));
        }
        (m, s)
    };
    let lits = |k: i64, below: &mut dyn FnMut(i64) -> i64| -> Lits {
        let by_modulus: BTreeMap<i64, Vec<(i64, i64)>> = (0..k).map(|_| lit(below)).collect();
        by_modulus.into_iter().collect()
    };
    let set = |s: &[(i64, i64)]| -> ResidueSet {
        s.iter()
            .map(|&(a, b)| (Int::from(a), Int::from(b)))
            .collect()
    };
    // Splits tried, and those whose lcm exceeds the window, where the walk wraps in the tree.
    let (mut with_point, mut splits, mut past_window) = (0, 0, 0);
    for _ in 0..400 {
        let units = lits(1 + below(4), &mut below);
        let clauses: Vec<Lits> = (0..below(11))
            .map(|_| {
                let k = 1 + below(3);
                lits(k, &mut below)
            })
            .collect();
        let l = below(400) - 200;
        let h = l + below(3000) - 2;
        let want = (l..=h).find(|&x| {
            units.iter().all(|(m, s)| holds(x, *m, s))
                && clauses
                    .iter()
                    .all(|cl| cl.iter().any(|(m, s)| holds(x, *m, s)))
        });
        let unit_mods: BTreeMap<Int, ResidueSet> =
            units.iter().map(|(m, s)| (Int::from(*m), set(s))).collect();
        let cls: Vec<BTreeMap<Int, ResidueSet>> = clauses
            .iter()
            .map(|cl| cl.iter().map(|(m, s)| (Int::from(*m), set(s))).collect())
            .collect();
        let (li, hi) = (Int::from(l), Int::from(h));
        let what = format!("[{l}, {h}] units {units:?} clauses {clauses:?}");
        let got = sweep_bounded(&li, &hi, &unit_mods, &cls);
        assert_eq!(found(&got), want.map(Int::from), "{what}");
        if li <= hi {
            let (e, weights) = sweep_window(&li, &hi, &unit_mods, &cls);
            for k in 0..=weights.len() {
                let Some((small, q)) = split_of(&weights, k) else {
                    break;
                };
                let got = sweep_split(&li, &e, &unit_mods, &cls, &small, q);
                assert_eq!(found(&got), want.map(Int::from), "split {k}: {what}");
                if want.is_none() {
                    assert!(matches!(got, RegimeOut::Empty), "split {k}: {what}");
                }
                splits += 1;
                past_window += usize::from(q as i64 > h - l + 1);
            }
        }
        with_point += usize::from(want.is_some());
    }
    assert!(
        (60..=340).contains(&with_point),
        "{with_point} of 400 with a point"
    );
    assert!(splits >= 800, "only {splits} splits tried");
    assert!(
        past_window >= 100,
        "only {past_window} of {splits} splits read modulo more residues than the window has"
    );
}

/// PERF-sweep-lazy-pieces: [`LargeMerge`] gives, in order, the places where each list's set is
/// entered or left and the lists whose state changes there, as making every piece on `[l, e]`
/// with `concrete_intervals_in_span`, joining each list's with `intervals::coalesce` and taking
/// the low end `a` and `b + 1` (where `b < e`) of each joined piece does (the sweep before this
/// change, whose event count the meter's charge keeps). Over 500 drawn sets of 1 to 5 lists of 0
/// to 3 literals, moduli 1 to 60, a literal's interval now and then all of `[0, m)` (so a run's
/// end and its next start are at one place) and lists whose pieces overlap (so a count changes
/// where no state does), on windows of 1 to 500 points.
#[test]
fn the_merge_of_large_pieces_gives_the_ends_of_the_joined_pieces() {
    let mut state = 0x1a2e_9e3c_u64;
    let mut below = |n: i64| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 33) % n as u64) as i64
    };
    let (mut passed_over, mut touching) = (0usize, 0usize);
    for _ in 0..500 {
        let mut owned: Vec<Vec<(Int, ResidueSet)>> = Vec::new();
        for _ in 0..1 + below(5) {
            let mut list = Vec::new();
            for _ in 0..below(4) {
                let m = 1 + below(60);
                let mut s: ResidueSet = Vec::new();
                for _ in 0..1 + below(2) {
                    let (a, b) = if below(4) == 0 {
                        (0, m - 1)
                    } else {
                        let a = below(m);
                        (a, a + below(m - a))
                    };
                    s.push((Int::from(a), Int::from(b)));
                }
                list.push((Int::from(m), s));
            }
            owned.push(list);
        }
        let lists: Vec<Vec<(&Int, &ResidueSet)>> = owned
            .iter()
            .map(|list| list.iter().map(|(m, s)| (m, s)).collect())
            .collect();
        let l = Int::from(below(400) - 200);
        let e = &l + &Int::from(below(500));
        let mut want: BTreeMap<Int, BTreeSet<(usize, bool)>> = BTreeMap::new();
        let mut raw_ends: BTreeSet<Int> = BTreeSet::new();
        for (j, list) in lists.iter().enumerate() {
            let mut raw = Vec::new();
            for (m, s) in list {
                for (ra, rb) in s.iter() {
                    raw.extend(concrete_intervals_in_span(&l, &e, m, ra, rb));
                }
            }
            for (a, b) in &raw {
                raw_ends.insert(a.clone());
                raw_ends.insert(b + &Int::ONE);
            }
            for (a, b) in intervals::coalesce(raw) {
                want.entry(a).or_default().insert((j, true));
                if b < e {
                    want.entry(&b + &Int::ONE).or_default().insert((j, false));
                }
            }
        }
        let mut merge = LargeMerge::new(&l, &e, &lists);
        let mut got: BTreeMap<Int, BTreeSet<(usize, bool)>> = BTreeMap::new();
        let mut last: Option<Int> = None;
        while let Some(at) = merge.next_change() {
            assert!(last.as_ref().is_none_or(|p| *p < at), "places out of order");
            let changed: BTreeSet<(usize, bool)> =
                merge.changed.iter().map(|&j| (j, merge.holds[j])).collect();
            assert_eq!(changed.len(), merge.changed.len(), "a list given twice");
            got.insert(at.clone(), changed);
            last = Some(at);
        }
        assert_eq!(got, want, "lists {owned:?} on [{l}, {e}]");
        passed_over += raw_ends
            .iter()
            .filter(|x| **x <= e && !want.contains_key(*x))
            .count();
        touching += owned
            .iter()
            .flatten()
            .filter(|(m, s)| s.iter().any(|(a, b)| a.is_zero() && *b == m - &Int::ONE))
            .count();
    }
    assert!(
        passed_over >= 200,
        "only {passed_over} raw ends where no state changes"
    );
    assert!(
        touching >= 200,
        "only {touching} literals over all residues"
    );
}

/// [`cheapest_split`]'s choice is the `k` of least bound `U_k`, the least `k` at a tie, and the
/// bound it gives is that `U_k`, with each bound computed here from its definition (each sum
/// formed again at each `k`), over 300 drawn sets of 1 to 8 moduli from 2 to 400 with weights 1
/// to 4, spans 0 to 100,000, and up to 12 lists.
#[test]
fn the_split_is_the_one_of_least_bound() {
    let mut state = 0x5917_u64;
    let mut below = |n: u64| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 33) % n
    };
    let mut chose_some = 0;
    for _ in 0..300 {
        let weights: BTreeMap<Int, u128> = (0..1 + below(8))
            .map(|_| (Int::from(2 + below(399) as i64), 1 + below(4) as u128))
            .collect();
        let span = below(100_001) as u128;
        let lists = below(13) as u128;
        let ms: Vec<(u128, u128)> = weights
            .iter()
            .map(|(m, w)| (m.to_i128().expect("small") as u128, *w))
            .collect();
        let gcd = |mut a: u128, mut b: u128| {
            while b != 0 {
                (a, b) = (b, a % b);
            }
            a
        };
        let mut best: Option<(u128, usize, usize)> = None;
        for k in 0..=ms.len() {
            let mut q = 1u128;
            for &(m, _) in &ms[..k] {
                q = q / gcd(q, m) * m;
            }
            let p: u128 = ms[k..].iter().map(|&(m, w)| w * (span / m + 2)).sum();
            let d: u128 = 1 + ms[..k].iter().map(|&(m, w)| w * (q / m + 2)).sum::<u128>();
            let u = p + q + (2 * p + lists + 1) * d;
            if best.is_none_or(|(b, _, _)| u < b) {
                best = Some((u, k, q as usize));
            }
        }
        let (u, k, q) = best.expect("k = 0 is always a choice");
        assert_eq!(
            cheapest_split(&Int::from(span as i128), &weights, lists),
            (k, q, u),
            "weights {weights:?} span {span} lists {lists}"
        );
        chose_some += usize::from(k > 0);
    }
    // A split other than cutting every modulus is chosen often, so both kinds are checked.
    assert!(
        (30..=270).contains(&chose_some),
        "{chose_some} of 300 split"
    );
}

/// The residue sets `x mod m in {r}`.
fn point_set(r: i64) -> ResidueSet {
    vec![(Int::from(r), Int::from(r))]
}

/// A clause `x mod a == r || x mod b == s`.
fn pair_clause(a: i64, r: i64, b: i64, s: i64) -> BTreeMap<Int, ResidueSet> {
    [(Int::from(a), point_set(r)), (Int::from(b), point_set(s))]
        .into_iter()
        .collect()
}

/// The empty regime of [`SWEEP_SWITCHOVER`]'s cost model over the primes 3 and the first `k`
/// primes from 5: the unit `x mod 3 == 0` and, for each two consecutive primes `a`, `b` of
/// them, the clause `x mod 3 a == r || x mod 3 b == s` with `r` and `s` both 1 mod 3 (and `j`,
/// `j + 1` modulo `a`, `b` for the `j`-th clause), so every clause contradicts the unit and
/// the regime is empty. Each literal becomes two clauses over the primes, so the coprime base
/// cannot write a clause (the two would multiply out). Its period is `3` times the product of
/// the `k` primes: 3,234,846,615 at `k = 8`, the product of the 9 primes from 3 to 29.
fn coupled_empty_chain(k: usize) -> Regime {
    // The first `k` primes from 5, by trial division by the primes found before.
    let mut primes: Vec<i64> = Vec::with_capacity(k);
    let mut c = 5i64;
    while primes.len() < k {
        if c % 3 != 0
            && primes
                .iter()
                .take_while(|&&p| p * p <= c)
                .all(|&p| c % p != 0)
        {
            primes.push(c);
        }
        c += 2;
    }
    coupled_empty_chain_over(&primes)
}

/// [`coupled_empty_chain`] over the integers `a` (each above 1 and not a multiple of 3) in place
/// of the primes: the unit `x mod 3 == 0` and, for consecutive `a`, `b` of them, the `j`-th
/// clause `x mod 3 a == r || x mod 3 b == s` with `r = j mod a` and `s = (j + 1) mod b` lifted to
/// the residue 1 mod 3 (by the CRT, as 3 and `a` are coprime), which the unit contradicts: so
/// the regime is empty. Each literal's modulus `3 a` has the base factor 3 and those of `a`, so
/// the coprime base cannot write a clause.
fn coupled_empty_chain_over(a: &[i64]) -> Regime {
    // `t mod p + k p` for the `k` in 0..3 that makes it 1 mod 3: as `p` is a unit modulo 3, the
    // three values cover the three residues modulo 3, and each is `t` modulo `p` and below `3 p`.
    let one_mod_3 = |p: i64, t: i64| (0..3).map(|k| t % p + k * p).find(|r| r % 3 == 1);
    let units = [(Int::from(3), point_set(0))].into_iter().collect();
    let clauses = (0..a.len() - 1)
        .map(|j| {
            let (x, y) = (a[j], a[j + 1]);
            let r = one_mod_3(x, j as i64).expect("a residue 1 mod 3");
            let s = one_mod_3(y, j as i64 + 1).expect("a residue 1 mod 3");
            pair_clause(3 * x, r, 3 * y, s)
        })
        .collect();
    (units, clauses)
}

/// A regime over the 9 primes from 3 to 29, period 3,234,846,615, in three groups of moduli
/// that no clause couples: over 3, 5, 7 the clause `x mod 15 == 7 || x mod 21 == 4`, over 11,
/// 13, 17 the clause `x mod 143 == 5 || x mod 221 == 9`, over 19, 23, 29 the clause `x mod
/// 437 == 11 || x mod 667 == 12`, none of which the coprime base can write (each literal is
/// two clauses over the primes). With `empty`, the unit `x mod 3 == 0` too, which both
/// literals of the first clause contradict (7 and 4 are 1 mod 3), so the regime is empty.
fn nine_primes_in_groups(empty: bool) -> Regime {
    let mut units = BTreeMap::new();
    if empty {
        units.insert(Int::from(3), point_set(0));
    }
    let clauses = vec![
        pair_clause(15, 7, 21, 4),
        pair_clause(143, 5, 221, 9),
        pair_clause(437, 11, 667, 12),
    ];
    (units, clauses)
}

/// The formula of the regime `lo <= x <= hi` (a missing bound is no bound) under `units` and
/// `clauses`: for each modulus `m`, `x = q_m m + r_m` with `0 <= r_m <= m - 1`, and each
/// literal `x mod m in s` as `r_m` in one of the intervals of `s`. Its points' `x` are the
/// regime's points.
fn regime_formula(
    lo: Option<&Int>,
    hi: Option<&Int>,
    units: &BTreeMap<Int, ResidueSet>,
    clauses: &[BTreeMap<Int, ResidueSet>],
) -> Formula {
    let x = Lin::atom(Atom::Sym("x".into()));
    let mut rem: BTreeMap<Int, Lin> = BTreeMap::new();
    let mut parts = Vec::new();
    if let Some(l) = lo {
        parts.push(Formula::Con(Con::ge(&x, &Lin::constant(l.clone()))));
    }
    if let Some(h) = hi {
        parts.push(Formula::Con(Con::ge(&Lin::constant(h.clone()), &x)));
    }
    let mut n = 0u32;
    let mut r_of = |m: &Int, parts: &mut Vec<Formula>| -> Lin {
        rem.entry(m.clone())
            .or_insert_with(|| {
                let q = Lin::atom(Atom::Aux(n));
                let r = Lin::atom(Atom::Aux(n + 1));
                n += 2;
                parts.push(Formula::Con(Con::eq(&x, &q.times(m.clone()).plus(&r))));
                parts.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
                parts.push(Formula::Con(Con::ge(&Lin::constant(m - &Int::ONE), &r)));
                r
            })
            .clone()
    };
    let lit = |r: &Lin, s: &ResidueSet| {
        Formula::or(
            s.iter()
                .map(|(a, b)| {
                    Formula::and(vec![
                        Formula::Con(Con::ge(r, &Lin::constant(a.clone()))),
                        Formula::Con(Con::ge(&Lin::constant(b.clone()), r)),
                    ])
                })
                .collect(),
        )
    };
    for (m, s) in units {
        let r = r_of(m, &mut parts);
        parts.push(lit(&r, s));
    }
    for cl in clauses {
        let mut d = Vec::new();
        for (m, s) in cl {
            let r = r_of(m, &mut parts);
            d.push(lit(&r, s));
        }
        parts.push(Formula::or(d));
    }
    Formula::and(parts)
}

/// The rows [`System::tie`] reads while [`decide_named`] decides the formula of
/// [`coupled_empty_chain_over`] `n` and `8n` moduli `3 a` (no point, past [`SWEEP_SWITCHOVER`], so
/// the general path decides it) grow less than 9 times. Before, [`System::least`] formed the tie
/// of the whole least class at every step, for callers that read it only at a fill of at most 0:
/// the class holds O(n) rows at each of the O(n) steps, so the count grew about 64 times
/// (FAIL-omega-negations-slow-7837918895420161952, the coordinator's order of 2026-11-21).
#[test]
fn ties_are_read_only_where_a_step_takes_them() {
    let rows = |n: usize| {
        let a: Vec<i64> = (1i64 << 20..).filter(|a| a % 3 != 0).take(n).collect();
        let (units, clauses) = coupled_empty_chain_over(&a);
        let f = regime_formula(None, None, &units, &clauses);
        let before = super::super::TIE_ROWS.with(std::cell::Cell::get);
        assert_eq!(super::super::decide_named(&f), Ok(false));
        super::super::TIE_ROWS.with(std::cell::Cell::get) - before
    };
    let (small, large) = (rows(32), rows(256));
    eprintln!("rows read by tie: n=32 {small}, 8n=256 {large}");
    assert!(
        large < 9 * small.max(1),
        "rows read by tie: {small} at 32 moduli and {large} at 256"
    );
}

/// A regime the coprime base cannot write, over the 9 primes from 3 to 29 (period
/// 3,234,846,615), is decided in well under 1 s (FAIL-omega-negations-slow-7837918895420161952,
/// the coordinator's order of 2026-11-21). Before [`SWEEP_SWITCHOVER`] the sweep took the whole
/// period: past 60 s on [`coupled_empty_chain`]`(8)`, and 24 s already at 7 primes. Now the
/// coupled regime, one group with a bound past the switchover, is `Undecided` and its formula
/// is decided by the general path; the regimes of [`nine_primes_in_groups`] are swept group by
/// group, `105 + 2,431 + 12,673` points in place of the period, with each bound and with none.
#[test]
fn a_regime_over_nine_primes_the_base_cannot_write_is_decided() {
    let nine = Int::from(3_234_846_615i64);
    let in_time = |t: std::time::Instant, what: &str| {
        let secs = t.elapsed().as_secs_f64();
        assert!(secs < 1.0, "{what}: {secs} s");
    };
    let (units, clauses) = coupled_empty_chain(8);
    assert_eq!(period_of(&units, &clauses), nine);
    let mut written = false;
    let base = solve_on_bases(&None, &None, &units, &clauses, &mut written);
    assert!(matches!(base, RegimeOut::Undecided) && !written);
    assert!(coprime_groups(&units, &clauses).is_none());
    let t = std::time::Instant::now();
    let out = solve_regime_in(&None, &None, units.clone(), clauses.clone());
    assert!(matches!(out, RegimeOut::Undecided));
    let f = regime_formula(None, None, &units, &clauses);
    assert_eq!(super::super::decide_named(&f), Ok(false));
    in_time(t, "the coupled chain over 9 primes");
    let huge = Int::from(1_000_000_000_000i64);
    for empty in [true, false] {
        let (units, clauses) = nine_primes_in_groups(empty);
        assert_eq!(period_of(&units, &clauses), nine);
        let mut written = false;
        let base = solve_on_bases(&None, &None, &units, &clauses, &mut written);
        assert!(matches!(base, RegimeOut::Undecided) && !written);
        assert_eq!(coprime_groups(&units, &clauses).map(|g| g.len()), Some(3));
        let bounds = [
            (None, None),
            (Some(&Int::ZERO - &huge), None),
            (None, Some(huge.clone())),
            (Some(Int::from(5)), Some(&nine + &Int::from(4))),
            (Some(Int::from(-1000)), Some(Int::from(1000))),
        ];
        for (lo, hi) in bounds {
            let what = format!("groups, empty {empty}, [{lo:?}, {hi:?}]");
            let t = std::time::Instant::now();
            let out = solve_regime_in(&lo, &hi, units.clone(), clauses.clone());
            in_time(t, &what);
            // A window shorter than the period is tested point by point; one of a whole period
            // or more has a point exactly when the regime with no bound has one.
            let want = match (&lo, &hi) {
                (Some(l), Some(h)) if &(h - l) + &Int::ONE < nine => {
                    let (l, h) = (l.to_i128().expect("small"), h.to_i128().expect("small"));
                    (l..=h).any(|x| holds_modular_point(&Int::from(x), &units, &clauses))
                }
                _ => !empty,
            };
            match out {
                RegimeOut::Empty => assert!(!want, "{what}: empty"),
                RegimeOut::Found(x) => {
                    assert!(want, "{what}: {x}");
                    assert!(lo.as_ref().is_none_or(|l| l <= &x), "{what}: {x}");
                    assert!(hi.as_ref().is_none_or(|h| &x <= h), "{what}: {x}");
                    assert!(holds_modular_point(&x, &units, &clauses), "{what}: {x}");
                }
                RegimeOut::Undecided => panic!("{what}: undecided"),
            }
        }
    }
}

/// [`sweep_unwritten`] decides regimes whose moduli fall into two groups that no clause couples
/// as testing each point does: 400 drawn regimes, each literal over the moduli 2, 3, 4, 6, 8,
/// 9, 12 (period 72) or 5, 7, 25, 35 (period 175), each clause over one group, with no bound,
/// one bound, or both, a window of a whole period of 12,600 or more (so the groups are swept
/// apart and combined by the CRT) or shorter (swept whole). A point found must lie in the bounds
/// and meet every literal; `Empty` must be right by testing each point of the window.
#[test]
fn groups_of_moduli_are_decided_as_testing_each_point_does() {
    let mut state = 0x6c0b_7e57_u64;
    let mut below = |n: i64| lcg_below(&mut state, n);
    let lit = |group: &[i64], below: &mut dyn FnMut(i64) -> i64| {
        let m = group[below(group.len() as i64) as usize];
        let a = below(m);
        (m, vec![(a, a + below((m - a).min(3)))])
    };
    let lits = |k: i64, group: &[i64], below: &mut dyn FnMut(i64) -> i64| -> Lits {
        let by_modulus: BTreeMap<i64, Vec<(i64, i64)>> =
            (0..k).map(|_| lit(group, below)).collect();
        by_modulus.into_iter().collect()
    };
    let set = |s: &[(i64, i64)]| -> ResidueSet {
        s.iter()
            .map(|&(a, b)| (Int::from(a), Int::from(b)))
            .collect()
    };
    let groups: [&[i64]; 2] = [&[2, 3, 4, 6, 8, 9, 12], &[5, 7, 25, 35]];
    let p = 12_600i64;
    let (mut with_point, mut split) = (0, 0);
    for _ in 0..400 {
        let mut units: Lits = Vec::new();
        let mut clauses: Vec<Lits> = Vec::new();
        for g in groups {
            units.extend(lits(below(2), g, &mut below));
            for _ in 0..below(4) {
                clauses.push(lits(1 + below(2), g, &mut below));
            }
        }
        let units: Lits = units
            .into_iter()
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .collect();
        let b = below(2 * p) - p;
        let (lo, hi) = match below(5) {
            0 => (None, None),
            1 => (Some(b), None),
            2 => (None, Some(b)),
            3 => (Some(b), Some(b + p + below(p))),
            _ => (Some(b), Some(b + below(p))),
        };
        let (l, h) = match (lo, hi) {
            (Some(l), Some(h)) => (l, h),
            (Some(l), None) => (l, l + p - 1),
            (None, Some(h)) => (h - p + 1, h),
            (None, None) => (0, p - 1),
        };
        let want = (l..=h).any(|x| regime_holds(x, &units, &clauses));
        let unit_mods: BTreeMap<Int, ResidueSet> =
            units.iter().map(|(m, s)| (Int::from(*m), set(s))).collect();
        let cls: Vec<BTreeMap<Int, ResidueSet>> = clauses
            .iter()
            .map(|cl| cl.iter().map(|(m, s)| (Int::from(*m), set(s))).collect())
            .collect();
        split += usize::from(h - l + 1 >= p && coprime_groups(&unit_mods, &cls).is_some());
        let what = format!("[{lo:?}, {hi:?}] units {units:?} clauses {clauses:?}");
        let (lo, hi) = (lo.map(Int::from), hi.map(Int::from));
        match sweep_unwritten(&lo, &hi, &unit_mods, &cls) {
            RegimeOut::Empty => assert!(!want, "empty, but a point lies: {what}"),
            RegimeOut::Found(x) => {
                let x = x.to_i128().expect("small") as i64;
                assert!(want, "{x}, but none lies: {what}");
                assert!(l <= x && x <= h, "{x} out of the window: {what}");
                assert!(regime_holds(x, &units, &clauses), "{x} is no point: {what}");
                with_point += 1;
            }
            RegimeOut::Undecided => panic!("undecided: {what}"),
        }
    }
    // The draws reach both answers, and the split on most of them.
    assert!(
        (100..=300).contains(&with_point),
        "{with_point} with a point"
    );
    assert!(split >= 100, "{split} split");
}
