//! Emptiness of recursive types (DESIGN.md sec:type_language, cross-review X14): a cycle of
//! definitions through a tuple component is empty, since a value is finite, and a cycle through
//! a morphism's value type is inhabited, since a morphism need not be built from a value of its
//! value type before it is applied: `type S = (int) -> S` holds `fn s(x) = s`.

use super::bes_families::{FAMILIES, G, K, family, reference};
use std::collections::BTreeMap;

use zed_kernel::types::bes::{Answer, decide};
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Type, Verdict};
use zed_tests::scaling;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn group(bodies: Vec<Expr>) -> Result<Vec<Type>, String> {
    let defs = bodies
        .into_iter()
        .enumerate()
        .map(|(i, body)| Def {
            name: format!("N{i}"),
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs)
        .map(|g| g.instance(vec![]))
        .map_err(|e| e.message)
}

#[test]
fn a_cycle_through_a_value_type_is_inhabited_and_one_through_a_tuple_is_empty() {
    Type::forget_emptiness();
    let int = || Expr::Type(Type::int());
    // type S = (int) -> S
    let s = group(vec![Expr::exact(int(), r(0))]).unwrap();
    assert!(!s[0].is_empty(), "S = (int) -> S holds fn s(x) = s");
    // type W = (W) -> int
    let w = group(vec![Expr::exact(r(0), int())]).unwrap();
    assert!(!w[0].is_empty(), "W = (W) -> int");
    // type E = (E, int)
    let e = group(vec![Expr::Tuple(vec![r(0), int()])]).unwrap();
    assert!(e[0].is_empty(), "E = (E, int) has no finite value");
    // type P = (int) -> (P, P): a pair of functions, each again such a pair.
    let p = group(vec![Expr::exact(int(), Expr::Tuple(vec![r(0), r(0)]))]).unwrap();
    assert!(!p[0].is_empty());
    // type Q = (Q, (int) -> Q): the tuple cycle makes it empty.
    let q = group(vec![Expr::Tuple(vec![r(0), Expr::exact(int(), r(0))])]).unwrap();
    assert!(q[0].is_empty());
    // type L = () | (int, L) and type F = (int) -> (F | ()) are inhabited.
    let l = group(vec![Expr::Union(vec![
        Expr::Tuple(vec![]),
        Expr::Tuple(vec![int(), r(0)]),
    ])])
    .unwrap();
    assert!(!l[0].is_empty());
}

/// Each node of a family as a definition: `Or` a union, `And` a tuple, `Mor` the morphism type
/// `(int) -> child`, `Top` `int` and `Bot` `empty`.
fn bodies(g: &G) -> Vec<Expr> {
    (0..g.k.len())
        .map(|v| {
            let cs = || g.c[v].iter().map(|&w| r(w as usize)).collect();
            match g.k[v] {
                K::Or => Expr::Union(cs()),
                K::And => Expr::Tuple(cs()),
                K::Mor => Expr::exact(Expr::Type(Type::int()), r(g.c[v][0] as usize)),
                K::Top => Expr::Type(Type::int()),
                K::Bot => Expr::Type(Type::empty()),
            }
        })
        .collect()
}

/// On every family group the definitions admit, emptiness agrees with the classical solver of
/// the Büchi game the group's fixed points describe.
#[test]
fn emptiness_of_family_groups_agrees_with_the_reference() {
    let (mut checked, mut refused) = (0, 0);
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            Type::forget_emptiness();
            let want = reference::answers(&g);
            let decided = decide(&g.bes()).answers;
            for (v, (t, w)) in types.iter().zip(&want).enumerate() {
                match decided[v] {
                    // The search decides a refused member, and may count an empty one as
                    // inhabited, never the other way.
                    Answer::Refused => {
                        assert!(!t.is_empty() || !w, "{name}:{n}: node {v} counted empty");
                        refused += 1;
                    }
                    Answer::Empty | Answer::Inhabited => {
                        assert_eq!(!t.is_empty(), *w, "{name}:{n}: node {v}")
                    }
                }
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "some family group is admitted");
    eprintln!("family groups checked: {checked}, refused members: {refused}");
}

/// On the same groups, a verdict of `Empty` or `Inhabited` agrees with the reference, every
/// refusal names its cause, and the verdicts read in reverse with nothing kept are the same.
#[test]
fn verdicts_of_family_groups_agree_with_the_reference() {
    let (mut decided, mut refused) = (0, BTreeMap::new());
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            let want = reference::answers(&g);
            Type::forget_emptiness();
            let first: Vec<Verdict> = types.iter().map(Type::verdict).collect();
            Type::forget_emptiness();
            let again: Vec<Verdict> = types.iter().rev().map(Type::verdict).collect();
            assert!(first.iter().eq(again.iter().rev()), "{name}:{n}");
            for (v, (verdict, w)) in first.iter().zip(&want).enumerate() {
                match verdict {
                    Verdict::Empty => assert!(!w, "{name}:{n}: node {v} is inhabited"),
                    Verdict::Inhabited => assert!(*w, "{name}:{n}: node {v} is empty"),
                    Verdict::Refused(why) => {
                        *refused.entry(format!("{why:?}")).or_insert(0) += 1;
                        continue;
                    }
                }
                decided += 1;
            }
        }
    }
    eprintln!("family members decided: {decided}, refused: {refused:?}");
    assert!(decided > 0);
}

/// A ring of `n` definitions, each a morphism type into a pair of the next and `int`, decided
/// in time linear in `n`.
#[test]
fn deciding_a_group_scales() {
    let ring = |n: usize| {
        let defs = (0..n)
            .map(|i| Def {
                name: format!("N{i}"),
                params: vec![],
                body: Expr::exact(
                    Expr::Type(Type::int()),
                    Expr::Tuple(vec![r((i + 1) % n), Expr::Type(Type::int())]),
                ),
            })
            .collect();
        Group::new(defs).unwrap()
    };
    let (n, small, large) = (256, ring(256), ring(scaling::FACTOR * 256));
    let run = |g: &Group| {
        Type::forget_emptiness();
        let types = g.instance(vec![]);
        assert!(types.iter().all(|t| !t.is_empty()));
    };
    run(&small);
    scaling::check_order("deciding a ring of definitions", n, 1, |m| {
        run(if m == n { &small } else { &large })
    });
}

/// `bodies` with node `v` placed at `place[v]`, its references moved with it.
fn renumbered(g: &G, place: &[usize]) -> Vec<Expr> {
    let mut out: Vec<Option<Expr>> = vec![None; place.len()];
    for v in 0..g.k.len() {
        let cs = || g.c[v].iter().map(|&w| r(place[w as usize])).collect();
        out[place[v]] = Some(match g.k[v] {
            K::Or => Expr::Union(cs()),
            K::And => Expr::Tuple(cs()),
            K::Mor => Expr::exact(Expr::Type(Type::int()), r(place[g.c[v][0] as usize])),
            K::Top => Expr::Type(Type::int()),
            K::Bot => Expr::Type(Type::empty()),
        });
    }
    out.into_iter()
        .map(|e| e.expect("`place` is a permutation"))
        .collect()
}

/// No answer depends on the questions asked before it or on the numbering of the definitions
/// (SYNTHESIS Q2/Q3 item 4): each member of every admitted family group is decided cold, in a
/// batch, in a reversed batch, and in a copy whose definitions are numbered in reverse, and
/// the four answers agree.
#[test]
fn answers_do_not_depend_on_order_or_numbering() {
    let mut checked = 0;
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            let cold: Vec<bool> = types
                .iter()
                .map(|t| {
                    Type::forget_emptiness();
                    t.is_empty()
                })
                .collect();
            Type::forget_emptiness();
            let batch: Vec<bool> = types.iter().map(Type::is_empty).collect();
            Type::forget_emptiness();
            let mut reversed: Vec<bool> = types.iter().rev().map(Type::is_empty).collect();
            reversed.reverse();
            let k = g.k.len();
            let place: Vec<usize> = (0..k).map(|v| k - 1 - v).collect();
            let copy = group(renumbered(&g, &place)).expect("a renumbered group is admitted");
            Type::forget_emptiness();
            let renamed: Vec<bool> = (0..k).map(|v| copy[place[v]].is_empty()).collect();
            assert_eq!(cold, batch, "{name}:{n}: cold, then in a batch");
            assert_eq!(cold, reversed, "{name}:{n}: cold, then reversed");
            assert_eq!(cold, renamed, "{name}:{n}: cold, then renumbered");
            checked += 1;
        }
    }
    assert!(checked > 0, "some family group is admitted");
}
