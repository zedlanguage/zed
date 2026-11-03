//! Verdicts against exact oracles on two kinds of random types, with every inhabited one shown
//! by a value: Boolean combinations of lists whose lengths are periodic, whose lengths modulo
//! 12 decide them, alone or paired with an integer; and Boolean combinations of tuples of sets
//! of 1, 2 and 3, decided by listing the tuples. The first kind is refused only at a fork of
//! an empty type, the second never.

use std::collections::BTreeMap;

use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

/// The lists of integers whose length is `k` modulo `p`; `p = 1` is every list.
fn period(p: usize, k: usize) -> Type {
    let defs = (0..p)
        .map(|i| {
            let cons = Expr::Atom(
                "cons".into(),
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            let body = match i == k {
                true => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                false => cons,
            };
            Def {
                name: format!("P{i}"),
                params: vec![],
                body,
            }
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![]).remove(0)
}

#[test]
fn periodic_lists_agree_with_their_lengths() {
    let mut r = Rng::new(3);
    let ps = [1, 2, 3, 4, 6, 12];
    let mut seen = BTreeMap::new();
    for _ in 0..600 {
        let p = ps[r.below(ps.len())];
        let k = r.below(p);
        let (mut t, mut lengths) = (period(p, k), [false; 12]);
        for (n, l) in lengths.iter_mut().enumerate() {
            *l = n % p == k;
        }
        for _ in 0..1 + r.below(5) {
            let p = ps[1 + r.below(ps.len() - 1)];
            let k = r.below(p);
            let op = r.below(3);
            t = match op {
                0 => &t | &period(p, k),
                1 => &t & &period(p, k),
                _ => &t - &period(p, k),
            };
            for (n, l) in lengths.iter_mut().enumerate() {
                let at = n % p == k;
                *l = match op {
                    0 => *l || at,
                    1 => *l && at,
                    _ => *l && !at,
                };
            }
        }
        let empty = !lengths.contains(&true);
        let t = match r.below(2) {
            0 => Type::tuple(vec![t, Type::int()]),
            _ => t,
        };
        Type::forget_emptiness();
        let v = t.verdict();
        match v {
            Verdict::Empty => assert!(empty, "{t} is inhabited"),
            Verdict::Inhabited => assert!(!empty, "{t} is empty"),
            Verdict::Refused(why) => assert!(empty, "{t} is inhabited, and refused: {why:?}"),
        }
        assert_eq!(t.is_empty(), empty, "{t}");
        *seen.entry(format!("{v:?}")).or_insert(0) += 1;
    }
    assert!(seen["Empty"] > 100 && seen["Inhabited"] > 100, "{seen:?}");
}

#[derive(Clone)]
enum E {
    Box(Vec<u8>),
    Or(Box<E>, Box<E>),
    And(Box<E>, Box<E>),
    Diff(Box<E>, Box<E>),
}

fn holds(e: &E, v: &[u8]) -> bool {
    match e {
        E::Box(m) => v.iter().zip(m).all(|(x, m)| m >> x & 1 == 1),
        E::Or(a, b) => holds(a, v) || holds(b, v),
        E::And(a, b) => holds(a, v) && holds(b, v),
        E::Diff(a, b) => holds(a, v) && !holds(b, v),
    }
}

/// The integers 1, 2 and 3 named by the bits of `m`.
fn small(m: u8) -> Type {
    (1..=3)
        .filter(|i| m >> (i - 1) & 1 == 1)
        .fold(Type::empty(), |t, i| &t | &lit(i))
}

fn build(e: &E) -> Type {
    match e {
        E::Box(m) => Type::tuple(m.iter().map(|&m| small(m)).collect()),
        E::Or(a, b) => &build(a) | &build(b),
        E::And(a, b) => &build(a) & &build(b),
        E::Diff(a, b) => &build(a) - &build(b),
    }
}

fn random(r: &mut Rng, depth: usize, n: usize) -> E {
    if depth == 0 || r.below(4) == 0 {
        return E::Box((0..n).map(|_| 1 + r.below(7) as u8).collect());
    }
    let (a, b) = (
        Box::new(random(r, depth - 1, n)),
        Box::new(random(r, depth - 1, n)),
    );
    match r.below(3) {
        0 => E::Or(a, b),
        1 => E::And(a, b),
        _ => E::Diff(a, b),
    }
}

#[test]
fn tuples_of_small_sets_are_decided_and_shown() {
    let mut r = Rng::new(7);
    let mut seen = BTreeMap::new();
    for i in 0..1500 {
        let n = 2 + i % 3;
        let e = random(&mut r, 7, n);
        let tuples = (0..3usize.pow(n as u32)).map(|k| {
            (0..n)
                .map(|j| (k / 3usize.pow(j as u32) % 3) as u8)
                .collect::<Vec<_>>()
        });
        let empty = !tuples.into_iter().any(|v| holds(&e, &v));
        let t = build(&e);
        Type::forget_emptiness();
        let v = t.verdict();
        let want = match empty {
            true => Verdict::Empty,
            false => Verdict::Inhabited,
        };
        assert_eq!(v, want, "{t}");
        *seen.entry(format!("{v:?}")).or_insert(0) += 1;
    }
    assert!(seen["Empty"] > 300 && seen["Inhabited"] > 300, "{seen:?}");
}

#[test]
fn the_shortest_list_of_a_period_is_built_in_linear_time() {
    // The list of length `n - 1` is built one link at a time, and each link is checked once.
    scaling::check("the shortest list of a period, by period", 64, |n| {
        let t = Type::tuple(vec![period(n, n - 1), Type::int()]);
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn the_residue_rule_agrees_with_listing_the_lengths() {
    // Lists in one class and in none of up to six others, with periods whose lcm is at most
    // 360, against the lengths below the lcm. A refusal is made only of an empty type, and `is_empty` claims
    // empty only of an empty type.
    let gcd = |mut a: usize, mut b: usize| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let ps = [1, 2, 3, 4, 5, 6, 8, 9, 10, 12];
    let mut r = Rng::new(17);
    let mut seen = BTreeMap::new();
    for _ in 0..2000 {
        let (p, k) = (ps[r.below(ps.len())], r.below(12));
        let mut t = period(p, k % p);
        let mut classes = vec![];
        for _ in 0..1 + r.below(6) {
            let q = ps[1 + r.below(ps.len() - 1)];
            let at = r.below(q);
            t = &t - &period(q, at);
            classes.push((q, at));
        }
        let lcm = classes.iter().fold(p, |l, &(q, _)| l / gcd(l, q) * q);
        let empty = !(0..lcm).any(|n| n % p == k % p && classes.iter().all(|&(q, at)| n % q != at));
        Type::forget_emptiness();
        let v = t.verdict();
        match v {
            Verdict::Empty => assert!(empty, "{p} {k} {classes:?}"),
            Verdict::Inhabited => assert!(!empty, "{p} {k} {classes:?}"),
            Verdict::Refused(why) => assert!(
                empty,
                "{p} {k} {classes:?} is inhabited, and refused: {why:?}"
            ),
        }
        if t.is_empty() {
            assert!(empty, "{p} {k} {classes:?}");
        } else if v != Verdict::Refused(Refusal::Residues) {
            assert!(!empty, "{p} {k} {classes:?}");
        }
        *seen.entry(format!("{v:?}")).or_insert(0) += 1;
    }
    println!("residues: {seen:?}");
    assert!(seen["Empty"] > 200 && seen["Inhabited"] > 200, "{seen:?}");
}

/// Answers do not depend on the ids the diagram nodes are given (SYNTHESIS fact 2): the same
/// types, built on two fresh threads in opposite orders, the second after unrelated types
/// that shift every id, get the same verdicts and the same printed form.
#[test]
fn answers_do_not_depend_on_the_order_types_are_built() {
    let mut r = Rng::new(11);
    let es: Vec<E> = (0..300).map(|i| random(&mut r, 6, 2 + i % 3)).collect();
    let answers = |order: Vec<usize>, shift: usize| {
        let es: Vec<E> = order.iter().map(|&i| es[i].clone()).collect();
        let mut out = std::thread::spawn(move || {
            for i in 0..shift {
                let _ = &Type::tuple(vec![lit(i as i64), Type::int()]) | &period(1 + i % 5, 0);
            }
            es.iter()
                .map(|e| {
                    let t = build(e);
                    (t.verdict(), t.is_empty(), t.to_string())
                })
                .collect::<Vec<_>>()
        })
        .join()
        .unwrap();
        let mut sorted = vec![None; out.len()];
        for (k, a) in order.into_iter().zip(out.drain(..)) {
            sorted[k] = Some(a);
        }
        sorted
    };
    let forward = answers((0..es.len()).collect(), 0);
    let backward = answers((0..es.len()).rev().collect(), 500);
    assert_eq!(forward, backward);
}

/// Recursive types have no canonical form: a group is one type per member when its definitions
/// are written alike (`rec::INSTANCES`), but a copy with its definitions renamed and listed in
/// another order is another node. No answer reads the node: each copy gets the same verdict,
/// each holds the other, and a type made of either is decided alike.
#[test]
fn copies_of_a_group_built_apart_get_the_same_answers() {
    let renamed = |p: usize, k: usize| {
        // `period(p, k)` with each `P{i}` named `Q{p - 1 - i}` and listed in reverse.
        let at = |i: usize| p - 1 - i;
        let defs = (0..p)
            .rev()
            .map(|i| {
                let cons = Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(Type::int()), Expr::Ref(at((i + 1) % p), vec![])],
                );
                Def {
                    name: format!("Q{}", at(i)),
                    params: vec![],
                    body: match i == k {
                        true => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                        false => cons,
                    },
                }
            })
            .collect();
        Group::new(defs).unwrap().instance(vec![]).remove(at(0))
    };
    for p in [1, 2, 3, 4, 6] {
        for k in 0..p {
            let (a, b, c) = (period(p, k), period(p, k), renamed(p, k));
            assert!(
                a == b && a != c,
                "{p} {k}: written alike, one node; renamed, another"
            );
            for x in [&b, &c] {
                Type::forget_emptiness();
                assert_eq!(a.verdict(), x.verdict(), "{p} {k}");
                assert!(a.subtype(x) && x.subtype(&a), "{p} {k}");
                let other = period(p, (k + 1) % p);
                Type::forget_emptiness();
                assert_eq!((&a - &other).verdict(), (x - &other).verdict(), "{p} {k}");
                assert_eq!((&a - x).verdict(), Verdict::Empty, "{p} {k}");
            }
        }
    }
}
