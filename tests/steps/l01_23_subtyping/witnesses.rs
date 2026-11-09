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
        // `is_empty` decides what the verdict decides: a type the verdict refuses at a fork
        // (5 of the 600, all empty, mixing periods) counts as inhabited for it too.
        assert_eq!(t.is_empty(), v == Verdict::Empty, "{t}");
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
fn a_list_of_a_period_is_shown_in_linear_time() {
    // The list is kept as its length, `n - 1`; the work is the walk of the cycle of `n`
    // definitions.
    scaling::check("a list of a period, by period", 64, |n| {
        let t = Type::tuple(vec![period(n, n - 1), Type::int()]);
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

const PRIMES: [usize; 25] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
];

/// The lists whose length is one less than a multiple of each of the first `k` primes: the meet
/// of `k` cycles, `2 + 3 + 5 + ...` definitions. The shortest has as many links as the product
/// of the primes less one, 6,469,693,229 for `k = 10`.
fn prime_cycles(k: usize) -> Type {
    PRIMES[..k]
        .iter()
        .fold(Type::top(), |t, &p| &t & &period(p, p - 1))
}

#[test]
fn a_meet_of_cycles_is_shown_by_its_length() {
    // A tax form that takes a list of entries whose count is one less than a multiple of each
    // of the first ten primes. Building the shortest list one link at a time took 31 s at nine
    // primes; the list is kept as its length, and each test of it against a type is the rule on
    // residues.
    let t = prime_cycles(10);
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Inhabited);
    assert!(!t.is_empty());
    assert!(!t.subtype(&Type::empty()));
    // In a tuple, the list is a component of a value tested against each tuple type.
    let pair = Type::tuple(vec![t.clone(), Type::int()]);
    assert_eq!(pair.verdict(), Verdict::Inhabited);
    // Every length is 2 modulo 3, so none is outside the lists of length 2 modulo 3.
    let thirds = Type::tuple(vec![period(3, 2), Type::int()]);
    assert_eq!((&pair - &thirds).verdict(), Verdict::Empty);
    assert!(pair.subtype(&thirds));
    // The lengths are 1 or 3 modulo 4, so the pairs with a list of length 3 modulo 4 leave
    // those of length 1 modulo 4: a value is shown, with a length the rule picks for that class.
    let fourths = Type::tuple(vec![period(4, 3), Type::int()]);
    assert_eq!((&pair - &fourths).verdict(), Verdict::Inhabited);
    assert!(!pair.subtype(&fourths));
    // Every length is 1 modulo 2, so none is outside a union holding the lists of odd length.
    let odd = &period(2, 1) | &period(3, 0);
    let held = &pair - &Type::tuple(vec![odd, Type::int()]);
    assert_eq!(held.verdict(), Verdict::Empty);
    // A union of list types of one item and two rest types, which holds the lists of length 3
    // modulo 4 and none of length 1 modulo 4: the walk of a list through it would follow both
    // rests, so whether the list shown is in it is not known, and no value is shown. The
    // search finds the type not empty, and the verdict is a refusal that says no value was
    // built (the tradeoff in `Search::list_member`).
    let other = &period(4, 3) | &period(3, 0);
    let left = &pair - &Type::tuple(vec![other, Type::int()]);
    assert_eq!(left.verdict(), Verdict::Refused(Refusal::NoWitness));
    assert!(!left.is_empty());
}

#[test]
fn the_meet_of_prime_cycles_scales() {
    // Ten primes are 129 definitions, twenty-five are 1060, 8.2 times as many; the shortest
    // lists have about 10^10 and 10^36 links.
    let (small, large) = (prime_cycles(10), prime_cycles(25));
    let defs = |k: usize| PRIMES[..k].iter().sum::<usize>();
    assert_eq!((defs(10), defs(25)), (129, 1060));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        "a meet of cycles, the first 10 and 25 primes",
        "the input has 8.2 times the definitions; for work of order n log n in them the rule \
         of low complexity allows at most 24 times (DESIGN.md Part G)",
        24.0,
        || run(&small),
        || run(&large),
    );
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

/// Recursive types have a canonical form (item REC-canon): a copy of a group with its definitions
/// listed in another order is the same node, member for member, as a group written alike. A copy
/// with its definitions renamed prints otherwise, so it is another node (deterministic checking:
/// a union keeps one of two equal nodes, and which must not show). No answer reads the node:
/// each copy gets the same verdict, each holds the other, and a type made of either is decided
/// alike.
#[test]
fn copies_of_a_group_built_apart_get_the_same_answers() {
    let copy = |p: usize, k: usize, letter: &str| {
        // `period(p, k)` with each `P{i}` named `{letter}{i}` and listed in reverse.
        let at = |i: usize| p - 1 - i;
        let defs = (0..p)
            .rev()
            .map(|i| {
                let cons = Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(Type::int()), Expr::Ref(at((i + 1) % p), vec![])],
                );
                Def {
                    name: format!("{letter}{i}"),
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
            let (a, b) = (period(p, k), period(p, k));
            let (c, d) = (copy(p, k, "P"), copy(p, k, "Q"));
            assert!(
                a == b && a == c && a != d,
                "{p} {k}: written alike or reordered, one node; renamed, another"
            );
            for x in [&b, &c, &d] {
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
