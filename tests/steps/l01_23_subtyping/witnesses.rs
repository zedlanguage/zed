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

/// Checks the verdict and `is_empty` of `t` against `empty`, the answer of its lengths.
fn check_lengths(t: &Type, empty: bool, run: &str) -> Verdict {
    Type::forget_emptiness();
    let v = t.verdict();
    match &v {
        Verdict::Empty => assert!(empty, "{t} is inhabited ({run})"),
        Verdict::Inhabited => assert!(!empty, "{t} is empty ({run})"),
        // A union of meets that take out different classes may be refused at a fork whether
        // it is empty or not (COMPLEXITY.md K113, given up); the check is sound, not
        // complete. Seed 3 drew only empty ones; new seeds also draw inhabited ones.
        Verdict::Refused(why) => {
            assert_eq!(*why, Refusal::Fork, "{t} (empty: {empty}) ({run})")
        }
    }
    // `is_empty` decides what the verdict decides: a type the verdict refuses at a fork
    // (3 of 600 at seed 3, unions whose meets take out different cycles) counts as
    // inhabited for it too.
    assert_eq!(t.is_empty(), v == Verdict::Empty, "{t} ({run})");
    v
}

#[test]
fn periodic_lists_agree_with_their_lengths() {
    // Ran 600 types from seed 3; now 300 from a new seed each run, printed
    // (TEST-bench-move-l0123, author P169).
    let (mut r, seed) = Rng::fresh("periodic lists");
    let seen = periodic_lists(&mut r, &format!("ZED_TEST_SEED={seed}"));
    println!("verdicts {seen:?}");
    // Each answer from a type built to give it, on every run (PROOF-test-count-thresholds):
    // no length is both even and odd, so `period(2, 0) & period(2, 1)` is empty; the empty list
    // has length 0, which is 0 modulo 2 and modulo 3, so `period(2, 0) & period(3, 0)` holds it.
    let none = &period(2, 0) & &period(2, 1);
    assert_eq!(
        check_lengths(&none, true, "built"),
        Verdict::Empty,
        "{none}"
    );
    let nil = &period(2, 0) & &period(3, 0);
    assert_eq!(
        check_lengths(&nil, false, "built"),
        Verdict::Inhabited,
        "{nil}"
    );
    // The lengths 1 and 0 modulo 3 and 1 and 2 modulo 6 taken out leave those 5 modulo 6. The
    // shares of the four classes sum to one, and two of them meet, so a length is left; the
    // choice of a length by its expected classes alone ties on both primes, took 0 and gave
    // no value (KERNEL-witness-length-miss, ZED_TEST_SEED=16903030027676086283).
    let mut five = period(1, 0);
    for (p, k) in [(3, 1), (6, 1), (3, 0), (6, 2)] {
        five = &five - &period(p, k);
    }
    let five = Type::tuple(vec![five, Type::int()]);
    assert_eq!(
        check_lengths(&five, false, "built"),
        Verdict::Inhabited,
        "{five}"
    );
    // The small instance of `bench::a_list_of_cycles_less_many_scales`: the classes 1 and 2
    // modulo 4, 9 and 25 taken out, whose shares sum to 0.80, leave lengths, 0 among them.
    let mut less = period(1, 0);
    for p in [2, 3, 5] {
        less = &(&less - &period(p * p, 1)) - &period(p * p, 2);
    }
    let less = Type::tuple(vec![less, Type::int()]);
    assert_eq!(
        check_lengths(&less, false, "built"),
        Verdict::Inhabited,
        "{less}"
    );
}

/// The run of `periodic_lists_agree_with_their_lengths` that drew a type whose length the
/// kernel chose by expectations alone and missed (KERNEL-witness-length-miss).
#[test]
fn periodic_lists_agree_with_their_lengths_at_a_seed_that_missed_a_length() {
    let seed = 16903030027676086283;
    periodic_lists(&mut Rng::new(seed), &format!("ZED_TEST_SEED={seed}"));
}

/// Seed 13375960689831104485 drew lists whose length is in none of 7 modulo 12, 0 modulo 2, 1
/// and 3 modulo 4 and 0 modulo 3: empty, but a split on 2 must go down to classes modulo 4 to
/// show it, and the split went down one level only, so the kernel refused with Residues
/// (FAIL-periodic-lists-13375960689).
#[test]
fn periodic_lists_agree_with_their_lengths_at_seed_13375960689831104485() {
    let seed = 13_375_960_689_831_104_485;
    periodic_lists(&mut Rng::new(seed), &format!("ZED_TEST_SEED={seed}"));
}

/// 300 random Boolean combinations of `period` types, alone or paired with an integer, each
/// checked by `check_lengths`; gives how many had each verdict.
fn periodic_lists(r: &mut Rng, run: &str) -> BTreeMap<String, usize> {
    let ps = [1, 2, 3, 4, 6, 12];
    let mut seen = BTreeMap::new();
    for _ in 0..300 {
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
        let v = check_lengths(&t, empty, run);
        *seen.entry(format!("{v:?}")).or_insert(0) += 1;
    }
    seen
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

/// Checks the verdict of `e`, a combination of tuples of `n` components, against listing its
/// tuples; returns the verdict.
fn check_small_sets(e: &E, n: usize, run: &str) -> Verdict {
    let tuples = (0..3usize.pow(n as u32)).map(|k| {
        (0..n)
            .map(|j| (k / 3usize.pow(j as u32) % 3) as u8)
            .collect::<Vec<_>>()
    });
    let empty = !tuples.into_iter().any(|v| holds(e, &v));
    let t = build(e);
    Type::forget_emptiness();
    let v = t.verdict();
    let want = match empty {
        true => Verdict::Empty,
        false => Verdict::Inhabited,
    };
    assert_eq!(v, want, "{t} ({run})");
    v
}

/// Draw 37 of `tuples_of_small_sets_are_decided_and_shown` under `ZED_TEST_SEED=4`, kept
/// (TEST-kernel-unreached-paths-14): a type of 3-tuples whose exclusive-or reading meets a
/// `|` of two parts that are not apart, neither valid, with no choice in either
/// (`sat == Some(false)` in the kernel's `read`), which only that seed's draws reached. The
/// draws before it are made and dropped, so the generator is where the random test had it.
#[test]
fn seed_4_draw_37_of_the_small_set_tuples_is_decided() {
    let mut r = Rng::new(4);
    for i in 0..37 {
        random(&mut r, 7, 2 + i % 3);
    }
    let e = random(&mut r, 7, 2 + 37 % 3);
    check_small_sets(&e, 2 + 37 % 3, "ZED_TEST_SEED=4, draw 37");
}

#[test]
fn tuples_of_small_sets_are_decided_and_shown() {
    // Ran 1500 types from seed 7, over 300 empty and 300 inhabited; now 300 from a new seed
    // each run, printed, over 50 of each (TEST-bench-move-l0123, author P169: random tests run
    // fewer cases).
    let (mut r, seed) = Rng::fresh("random tuples of small sets");
    let check = check_small_sets;
    let mut seen = BTreeMap::new();
    for i in 0..300 {
        let n = 2 + i % 3;
        let e = random(&mut r, 7, n);
        let v = check(&e, n, &format!("ZED_TEST_SEED={seed}"));
        *seen.entry(format!("{v:?}")).or_insert(0) += 1;
    }
    println!("verdicts {seen:?}");
    // Each answer from a type built to give it, on every run (PROOF-test-count-thresholds):
    // `(1, 1)` holds the tuple (1, 1), and `(1, 1) & (2, 2)` holds none, since no component is
    // both 1 and 2 (a mask's bit `i` names the integer `i + 1`).
    let one = || Box::new(E::Box(vec![1, 1]));
    assert_eq!(check(&one(), 2, "built (1, 1)"), Verdict::Inhabited);
    let none = E::And(one(), Box::new(E::Box(vec![2, 2])));
    assert_eq!(check(&none, 2, "built (1, 1) & (2, 2)"), Verdict::Empty);
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
    // Ran 2000 cases from seed 17 (463 empty, 1536 inhabited, 1 refused); now 400 from a new
    // seed each run, printed, over 40 of each verdict (TEST-bench-move-l0123, author P169:
    // random tests run fewer cases). The residue refusal is checked on its own in refusals.rs
    // (the Erdős covering system).
    let (mut r, seed) = Rng::fresh("residue classes");
    // Builds the lists of length `k` modulo `p` and in none of `classes`, and checks its
    // verdict and `is_empty` against the lengths below the lcm; returns the verdict.
    let check = |p: usize, k: usize, classes: &[(usize, usize)], run: &str| -> Verdict {
        let t = classes
            .iter()
            .fold(period(p, k % p), |t, &(q, at)| &t - &period(q, at));
        let lcm = classes.iter().fold(p, |l, &(q, _)| l / gcd(l, q) * q);
        let empty = !(0..lcm).any(|n| n % p == k % p && classes.iter().all(|&(q, at)| n % q != at));
        Type::forget_emptiness();
        let v = t.verdict();
        match &v {
            Verdict::Empty => assert!(empty, "{p} {k} {classes:?} ({run})"),
            Verdict::Inhabited => assert!(!empty, "{p} {k} {classes:?} ({run})"),
            Verdict::Refused(why) => assert!(
                empty,
                "{p} {k} {classes:?} is inhabited, and refused: {why:?} ({run})"
            ),
        }
        if t.is_empty() {
            assert!(empty, "{p} {k} {classes:?} ({run})");
        } else if v != Verdict::Refused(Refusal::Residues) {
            assert!(!empty, "{p} {k} {classes:?} ({run})");
        }
        v
    };
    let mut seen = BTreeMap::new();
    for _ in 0..400 {
        let (p, k) = (ps[r.below(ps.len())], r.below(12));
        let mut classes = vec![];
        for _ in 0..1 + r.below(6) {
            let q = ps[1 + r.below(ps.len() - 1)];
            let at = r.below(q);
            classes.push((q, at));
        }
        let v = check(p, k, &classes, &format!("ZED_TEST_SEED={seed}"));
        *seen.entry(format!("{v:?}")).or_insert(0) += 1;
    }
    println!("residues: {seen:?}");
    // Each answer from a type built to give it, on every run (PROOF-test-count-thresholds):
    // an even length is 0 or 2 modulo 4, so the even lengths outside both classes are none,
    // and outside only the class of 0 they hold 2.
    let both = [(4, 0), (4, 2)];
    assert_eq!(check(2, 0, &both, "built"), Verdict::Empty);
    assert_eq!(check(2, 0, &both[..1], "built"), Verdict::Inhabited);
}

/// Answers do not depend on the ids the diagram nodes are given (SYNTHESIS fact 2): the same
/// types, built on two fresh threads in opposite orders, the second after unrelated types
/// that shift every id, get the same verdicts and the same printed form.
#[test]
fn answers_do_not_depend_on_the_order_types_are_built() {
    // Ran 300 types from seed 11; now 100 from a new seed each run, printed
    // (TEST-bench-move-l0123, author P169: random tests run fewer cases).
    let (mut r, seed) = Rng::fresh("types built in two orders");
    let es: Vec<E> = (0..100).map(|i| random(&mut r, 6, 2 + i % 3)).collect();
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
    assert_eq!(forward, backward, "ZED_TEST_SEED={seed}");
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

/// The list of `n` integers, each 0.
fn zeros(n: usize) -> Value {
    (0..n).fold(Value::atom("nil"), |rest, _| {
        Value::atom_with("cons", vec![Value::Int(0), rest])
    })
}

#[test]
fn a_union_of_cycles_less_one_is_decided() {
    // Every length 4 modulo 6 or 12 is 1 modulo 3, and every length 9 or 3 modulo 12 is 3
    // modulo 6: each class of the union lies inside the class taken out, so nothing is left.
    // Refused at a fork before REFUSAL-periodic-split.
    for (union, out) in [
        (&period(6, 4) | &period(12, 4), period(3, 1)),
        (&period(12, 9) | &period(12, 3), period(6, 3)),
    ] {
        let t = &union - &out;
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Empty, "{t}");
        assert!(t.is_empty(), "{t}");
        assert!(union.subtype(&out), "{union} <: {out}");
        let pair = |l: Type| Type::tuple(vec![l, Type::int()]);
        assert_eq!(
            (&pair(union.clone()) - &pair(out.clone())).verdict(),
            Verdict::Empty
        );
        // The union met with the class taken out is the union, shown by a list of its first
        // class; met with a class it misses it is empty.
        let met = &union & &out;
        Type::forget_emptiness();
        assert_eq!(met.verdict(), Verdict::Inhabited, "{met}");
        assert_eq!(pair(met).verdict(), Verdict::Inhabited);
    }
    let missed = &(&period(6, 4) | &period(12, 4)) & &period(3, 0);
    Type::forget_emptiness();
    assert_eq!(missed.verdict(), Verdict::Empty, "{missed}");
    // 5 modulo 12 is 2 modulo 3, outside 1 modulo 3: the lists of that class are left, and a
    // list of them is shown. A wrong rule that took the union for its first class, or that
    // took a class for inside the one taken out when only its period divides, says empty.
    let union = &period(6, 4) | &period(12, 5);
    let t = &union - &period(3, 1);
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Inhabited, "{t}");
    assert!(!t.is_empty());
    assert!(!union.subtype(&period(3, 1)));
    for n in [5, 17, 29] {
        assert!(t.contains(&zeros(n)), "{n} links");
    }
    for n in [4, 10, 16, 3, 6] {
        assert!(!t.contains(&zeros(n)), "{n} links");
    }
    // In a pair, the list is the shown value's first component, built from its length by the
    // rule on residues and checked against the pair type.
    let pair = Type::tuple(vec![t.clone(), Type::int()]);
    assert_eq!(pair.verdict(), Verdict::Inhabited);
    // The class 2 modulo 3 of the union lies inside none taken out, and has lengths outside
    // them all, 2 modulo 12 among them: shown with the classes of the other side unread.
    let t = &(&period(3, 2) | &period(6, 4)) - &(&period(4, 0) | &period(3, 1));
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Inhabited, "{t}");
    assert!(t.contains(&zeros(2)) && !t.contains(&zeros(4)) && !t.contains(&zeros(8)));
}

#[test]
fn a_union_of_cycles_covered_only_jointly_is_not_decided_by_the_rule() {
    // The lengths 0 modulo 2 lie inside no class taken out, but 0 and 2 modulo 4 cover them
    // together: whether classes cover one jointly is the covering problem for residues, so the
    // rule leaves it to the search, which refuses it at a fork, as before. The type is empty.
    let t = &(&period(2, 0) | &period(6, 4)) - &(&(&period(4, 0) | &period(4, 2)) | &period(3, 1));
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Refused(Refusal::Fork), "{t}");
    assert!(!t.is_empty());
}

/// The lists whose length is `r` modulo `2q` for `q` in `k..2k` and `r < q / 2`, less those
/// whose length is `s` modulo `q` for `s < q / 2`: each class of the union lies inside one
/// taken out, so the type is empty. With the definitions each class costs.
fn halves(k: usize) -> (Type, usize) {
    let (mut union, mut out, mut defs) = (Type::empty(), Type::empty(), 0);
    for q in k..2 * k {
        for r in 0..q / 2 {
            union = &union | &period(2 * q, r);
            out = &out | &period(q, r);
            defs += 3 * q;
        }
    }
    (&union - &out, defs)
}

/// Small instance of `bench::the_meet_of_prime_cycles_scales` (TEST-bench-move-l0123, author
/// P170): the meets of the first 16 and 17 primes' cycles, whose shortest lists have more links
/// than 2^64 (the product of the first 16 primes is about 3.26 * 10^19), are shown alone and in
/// a pair, and a class they all miss is decided as at ten primes. Before, only the benchmark's
/// 25 primes reached lengths past 64 bits.
#[test]
fn a_meet_of_cycles_longer_than_64_bits_is_shown() {
    for k in [16, 17] {
        let t = prime_cycles(k);
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited, "{k}");
        let pair = Type::tuple(vec![t, Type::int()]);
        assert_eq!(pair.verdict(), Verdict::Inhabited, "{k}");
        // Every length is 2 modulo 3, so none is outside the lists of length 2 modulo 3.
        let thirds = Type::tuple(vec![period(3, 2), Type::int()]);
        assert_eq!((&pair - &thirds).verdict(), Verdict::Empty, "{k}");
    }
}

/// Small instance of `bench::a_union_of_cycles_less_one_scales` (TEST-bench-move-l0123, author
/// P170): a union of classes less a union of classes, each class of the first inside a
/// different one of the second, is empty. `a_union_of_cycles_less_one_is_decided` takes out
/// one class only.
#[test]
fn a_union_of_cycles_less_a_union_holding_each_is_empty() {
    for k in 2..=5 {
        let (t, _) = halves(k);
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Empty, "{k}");
        assert!(t.is_empty(), "{k}");
    }
}

mod bench;
