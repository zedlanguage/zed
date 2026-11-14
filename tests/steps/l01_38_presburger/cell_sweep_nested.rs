//! Disjunctions with disjunctions inside their disjuncts, on the chains of `cell_sweep`, which
//! reach the branches of the cell sweep's resolution of one disjunction (`resolve_disj`) that
//! flat chains do not (row TEST-presburger-unreached-paths): a disjunct dead through its inner
//! disjunction, a disjunct the guard of its parent leaves no cell, a node shared by two
//! disjunctions of one parent or by two parents, two inner disjunctions that both define the
//! value, an inner disjunction on `i` alone, and overlapping guards whose definitions are one
//! constant, two constants, three constants, a constant beside a sum, or two sums.
//!
//! Each formula is the `mid` chain of `cell_sweep` at depth `n`, a shape over `i` whose values
//! are given to a payload name (a free name `q`, or the chain's last level `t_n`), and a target.
//! Every answer is checked against enumeration of `i`, the chain's values of `t_n` at each `i`,
//! and `q`. At depth 3 the sweep may refuse (`Err(Disjuncts)`, eight of the cases, all with no
//! point); an answer it gives must be the enumerated one. Below depth 3 every case is answered.

use std::collections::BTreeSet;
use std::sync::Arc;

use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide};

use super::cell_sweep::{Target, mid};

fn i() -> Atom {
    Atom::Sym(Arc::from("i"))
}

fn q() -> Atom {
    Atom::Sym(Arc::from("q"))
}

/// The chain's last level `t_n`, as `cell_sweep` names it.
fn tn(n: usize) -> Atom {
    Atom::Aux(2 * (n as u32 - 1))
}

fn le(k: i128) -> Formula {
    Formula::Con(Con::ge(&Lin::constant(k), &Lin::atom(i())))
}

fn ge(k: i128) -> Formula {
    Formula::Con(Con::ge(&Lin::atom(i()), &Lin::constant(k)))
}

fn is(a: &Atom, k: i128) -> Formula {
    Formula::Con(Con::eq(&Lin::atom(a.clone()), &Lin::constant(k)))
}

fn and(v: Vec<Formula>) -> Formula {
    Formula::and(v)
}

fn or(v: Vec<Formula>) -> Formula {
    Formula::or(v)
}

/// The values of `t_n` of the `mid` chain (`k` left out, so 2) at `i`: `t_j` is `t_{j-1}`
/// where `i <= 1` and `2 - t'_{j-1}` where `i >= -1`, the twin copies chosen independently.
fn mid_values(n: usize, i: i128) -> BTreeSet<i128> {
    let mut pairs: BTreeSet<(i128, i128)> = [(i, i)].into();
    for j in 1..=n {
        let mut next = BTreeSet::new();
        for &(t, u) in &pairs {
            let mut opts = Vec::new();
            if i <= 1 {
                opts.push(t);
            }
            if i >= -1 {
                opts.push(2 - u);
            }
            for &a in &opts {
                if j == n {
                    next.insert((a, a));
                } else {
                    for &b in &opts {
                        next.insert((a, b));
                    }
                }
            }
        }
        pairs = next;
    }
    pairs.into_iter().map(|(t, _)| t).collect()
}

/// The shape `name` with the payload name `p`.
fn shape(name: &str, p: &Atom) -> Formula {
    let pis = |k: i128| is(p, k);
    // `q + p == k`: with `p` the name `t_n`, an equation of two names with like signs.
    let sum_is = |k: i128| {
        Formula::Con(Con::eq(
            &Lin::atom(q()).plus(&Lin::atom(p.clone())),
            &Lin::constant(k),
        ))
    };
    let two = |g: Formula, a: Formula, b: Formula| and(vec![g, or(vec![a, b])]);
    match name {
        // The second disjunct's inner disjunction has no live disjunct on `-6..=6`.
        "dead_inner" => or(vec![
            and(vec![le(0), pis(1)]),
            two(ge(1), and(vec![ge(10), pis(2)]), and(vec![ge(12), pis(3)])),
        ]),
        // The guard `i <= 0` leaves `i >= 3` no cell.
        "pruned_child" => or(vec![
            two(le(0), and(vec![ge(3), pis(1)]), and(vec![le(-1), pis(2)])),
            and(vec![ge(1), pis(3)]),
        ]),
        // One node under two parents.
        "diamond" => {
            let c = and(vec![ge(-2), pis(4)]);
            or(vec![
                two(le(0), c.clone(), and(vec![le(-3), pis(5)])),
                two(ge(1), c, and(vec![ge(4), pis(6)])),
            ])
        }
        // One node in two inner disjunctions of one parent.
        "shared_in_one_parent" => {
            let c = and(vec![ge(-5), pis(4)]);
            or(vec![
                and(vec![
                    le(0),
                    or(vec![c.clone(), and(vec![le(-3), pis(5)])]),
                    or(vec![c, and(vec![le(-4), pis(6)])]),
                ]),
                and(vec![ge(1), pis(4)]),
            ])
        }
        // Two inner disjunctions of one disjunct, both defining the payload.
        "pay_and_pay" => or(vec![
            and(vec![
                le(0),
                or(vec![and(vec![le(-2), pis(2)]), and(vec![ge(-1), pis(3)])]),
                or(vec![and(vec![le(-4), pis(2)]), and(vec![ge(-3), pis(5)])]),
            ]),
            and(vec![ge(1), pis(4)]),
        ]),
        // An inner disjunction on `i` alone, beside a disjunct that defines the payload.
        "nested_pure" => or(vec![two(le(0), le(-3), ge(-1)), and(vec![ge(2), pis(0)])]),
        // Overlapping guards inside and outside, each defining the payload as a constant.
        "nested_overlap" => or(vec![
            two(le(1), and(vec![le(-2), pis(1)]), and(vec![ge(-3), pis(2)])),
            and(vec![ge(-1), pis(3)]),
        ]),
        // Three constants on overlapping guards.
        "overlap_three" => or(vec![
            and(vec![le(2), pis(1)]),
            and(vec![ge(-2), pis(2)]),
            and(vec![ge(0), le(1), pis(3)]),
        ]),
        // A constant and a sum on overlapping guards.
        "constant_and_sum" => or(vec![and(vec![le(2), pis(1)]), and(vec![ge(-2), sum_is(3)])]),
        // The same with the sum first.
        "sum_and_constant" => or(vec![and(vec![le(2), sum_is(3)]), and(vec![ge(-2), pis(1)])]),
        // Two sums on overlapping guards.
        "two_sums" => or(vec![
            and(vec![le(2), sum_is(3)]),
            and(vec![ge(-2), sum_is(4)]),
        ]),
        // No disjunct is live; answered before the sweep.
        "every_top_dead_inside" => or(vec![
            two(le(0), and(vec![ge(10), pis(1)]), and(vec![ge(12), pis(2)])),
            two(ge(1), and(vec![ge(11), pis(3)]), and(vec![ge(13), pis(4)])),
        ]),
        // Each leaf is outside its parent's guard; answered before the sweep.
        "every_leaf_blocked" => or(vec![
            two(le(0), and(vec![ge(3), pis(1)]), and(vec![ge(5), pis(2)])),
            two(ge(1), and(vec![le(-1), pis(3)]), and(vec![le(-3), pis(4)])),
        ]),
        _ => unreachable!("no shape {name}"),
    }
}

/// Decides the shape on the chain at depths 1 to 3, with each payload and each target, and
/// asserts every answer against enumeration.
fn check(name: &str) {
    let mut wrong = Vec::new();
    for n in 1..=3 {
        for p in [q(), tn(n)] {
            let s = shape(name, &p);
            let mut targets: Vec<(String, Formula)> = vec![("none".into(), and(vec![]))];
            for v in -1..=7 {
                targets.push((format!("{p:?} = {v}"), is(&p, v)));
            }
            for v in [-6, -2, 0, 1, 3, 6] {
                targets.push((format!("i = {v}"), is(&i(), v)));
            }
            for (tname, target) in targets {
                let g = and(vec![s.clone(), target]);
                let f = and(vec![mid(None, false).chain(n, Target::None), g.clone()]);
                let mut want = false;
                for iv in -6..=6 {
                    for t in mid_values(n, iv) {
                        // The sums need `q` up to 9 where `t_n` is -6.
                        for qv in -20..=20 {
                            let mut m = Model::new();
                            m.insert(i(), Int::from(iv));
                            m.insert(tn(n), Int::from(t));
                            m.insert(q(), Int::from(qv));
                            want |= g.holds(&m);
                        }
                    }
                }
                match decide(&f) {
                    Ok(got) if got == want => {}
                    Err(_) if n == 3 => {}
                    got => wrong.push(format!(
                        "n = {n}, payload {p:?}, target {tname}: {got:?}, expected Ok({want})"
                    )),
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{name}:\n{}", wrong.join("\n"));
}

#[test]
fn a_disjunct_dead_through_its_inner_disjunction() {
    check("dead_inner");
}

#[test]
fn a_disjunct_outside_its_parents_guard() {
    check("pruned_child");
}

#[test]
fn a_node_under_two_parents() {
    check("diamond");
}

#[test]
fn a_node_in_two_disjunctions_of_one_parent() {
    check("shared_in_one_parent");
}

#[test]
fn two_inner_disjunctions_define_the_value() {
    check("pay_and_pay");
}

#[test]
fn an_inner_disjunction_on_i_alone() {
    check("nested_pure");
}

#[test]
fn overlapping_guards_inside_and_outside() {
    check("nested_overlap");
}

#[test]
fn three_constants_on_overlapping_guards() {
    check("overlap_three");
}

#[test]
fn a_constant_and_a_sum_on_overlapping_guards_in_either_order() {
    check("constant_and_sum");
    check("sum_and_constant");
}

#[test]
fn two_sums_on_overlapping_guards() {
    check("two_sums");
}

#[test]
fn no_live_disjunct() {
    check("every_top_dead_inside");
    check("every_leaf_blocked");
}
