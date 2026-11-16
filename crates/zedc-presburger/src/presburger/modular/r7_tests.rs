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

/// The point a regime's answer gives, for messages.
fn found(out: &RegimeOut) -> Option<Int> {
    match out {
        RegimeOut::Found(x) => Some(x.clone()),
        _ => None,
    }
}
