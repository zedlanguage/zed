use super::*;
use crate::seed::{Rng, Xorshift64};

/// The region of the part `f` on the box `r`, made by a search of its own.
fn region(r: Vec<Type>, f: &Part<Row>) -> Region {
    let f = f.clone();
    Search::default().run(move |d| Box::pin(async move { d.region(r, &f).await }))
}

/// The classes of `overlaps` on everyday types: a finite set and a cofinite one are joined
/// exactly when they meet, at the top and inside an atom payload; two types of one atom
/// name or tuple length are apart when they are disjoint inside it, a payload of a payload
/// too, and two tuples that share a first component are apart when they are disjoint on
/// another; tuples that share a key on every component are joined even when they are
/// disjoint, as `(7, 7) | (8, 8)` and `(7, 8)` (the tradeoff at `overlaps`). A type that holds
/// every tuple of the lengths it does not list is joined with the pairs it meets.
#[test]
fn classes_are_exact_on_cofinite_sets_names_lengths_and_components() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let one = |t: Type| Type::tuple(vec![t]);
    let ts = [
        lit(3),                              // 0, in no cofinite set
        &Type::int() - &lit(3),              // 1, meets 2, 7 and 8
        lit(4),                              // 2
        Type::atom_with("a", &one(lit(1))),  // 3, disjoint from 4 and 14
        Type::atom_with("a", &one(lit(2))),  // 4
        one(lit(1)),                         // 5, disjoint from 6
        one(lit(2)),                         // 6
        &Type::int() - &(&lit(3) | &lit(5)), // 7
        lit(5),                              // 8, in 1, not in 7
        // 9, every atom but `#a`, `#a(..)`, `#b` and `#b(..)`, so apart from 12 and 13
        &(&(&(&Type::with(|p| p.atoms = crate::types::Atoms::all())
            - &Type::atom_with("a", &Type::top()))
            - &Type::atom("a"))
            - &Type::atom_with("b", &Type::top()))
            - &Type::atom("b"),
        Type::tuple(vec![lit(1), lit(2)]), // 10, disjoint from 11, 15 and 16
        Type::tuple(vec![lit(1), lit(3)]), // 11
        Type::atom_with("b", &one(Type::atom_with("c", &one(lit(1))))), // 12, apart from 13
        Type::atom_with("b", &one(Type::atom_with("c", &one(lit(2))))), // 13
        Type::atom_with("a", &one(&Type::int() - &lit(1))), // 14, meets 4, not 3
        Type::tuple(vec![lit(1), &Type::int() - &lit(2)]), // 15, meets 11, not 10
        // 16, disjoint from 17 and joined with it
        &Type::tuple(vec![lit(7), lit(7)]) | &Type::tuple(vec![lit(8), lit(8)]),
        Type::tuple(vec![lit(7), lit(8)]), // 17
    ];
    let classes = overlaps(ts.iter());
    let expected: Vec<Vec<usize>> = vec![
        vec![0],
        vec![1, 2, 7, 8],
        vec![3],
        vec![4, 14],
        vec![5],
        vec![6],
        vec![9],
        vec![10],
        vec![11, 15],
        vec![12],
        vec![13],
        vec![16, 17],
    ];
    assert_eq!(classes, expected);
    let pairs = [
        Type::tuple(vec![lit(1), lit(2)]),
        Type::tuple(vec![lit(1), lit(3)]),
    ];
    let tuples = Type::universe(crate::types::Universe::Tuple);
    let but_one_tuples = &tuples - &one(Type::int());
    let ts = [but_one_tuples, pairs[0].clone(), pairs[1].clone()];
    assert_eq!(overlaps(ts.iter()), vec![vec![0, 1, 2]]);
}

/// `meeting_pairs` keys a class by one component of its tuples when that leaves the fewest
/// pairs (`component_keys`): `(7, 7) | (7, 9) | (8, 8)`, `(7, 8)` and `(8, 7)` share a key on
/// every component, so `overlaps` puts them in one class, but their first components `{7, 8}`,
/// `{7}` and `{8}` pair the union with each pair and leave `(7, 8)` and `(8, 7)` apart, which
/// they are. The literals give no keys here (each type is a tuple), which would pair all three.
/// Before TEST-kernel-unreached-paths-10 only the searches of some runs reached the keying by a
/// component (`l01_23_groups_and_refusals::judgments`, as the seed of the maps keyed by text
/// fell); this test reaches it in every run. Negative controls: `component_keys` answering
/// `None`, or its keys not deduplicated (the union has two rows whose first component is 7),
/// fail it.
#[test]
fn a_class_of_tuples_is_keyed_by_the_component_that_leaves_the_fewest_pairs() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let pair = |a: i64, b: i64| Type::tuple(vec![lit(a), lit(b)]);
    let ts = [
        &(&pair(8, 8) | &pair(7, 7)) | &pair(7, 9),
        pair(7, 8),
        pair(8, 7),
    ];
    assert_eq!(overlaps(ts.iter()), vec![vec![0, 1, 2]], "one class");
    let held = Held::default();
    let int = |i: i64| Key::Lit(0, Value::Int(i));
    let keys: Vec<Option<Vec<Key>>> = (ts.iter())
        .map(|t| component_keys(t.p_held(&held), 0, &held))
        .collect();
    assert!(
        keys == vec![
            Some(vec![int(7), int(8)]),
            Some(vec![int(7)]),
            Some(vec![int(8)])
        ],
        "the first components, in order and once each, are the keys"
    );
    let refs: Vec<&Type> = ts.iter().collect();
    assert_eq!(
        meeting_pairs(&refs),
        BTreeSet::from([(0, 1), (0, 2)]),
        "the two pairs are apart"
    );
}

/// The other two cases of the tradeoff at `overlaps`. A negated pair type, `(int, int) \ (1, 1)`,
/// is keyed by the components of `(int, int)`, so it is joined with `(1, 1)` although the two
/// are disjoint; a negated one-tuple type, `(int,) \ (1,)`, is placed at the first components
/// it can hold, `int \ 1`, so it is apart from `(1,)` and joined with `(2,)`. A type met at
/// two nodes inside one type, the `1` of `(1,) | #e((1,))`, merges the two nodes, so `(2,)`
/// and `#e((2,))` are joined although they are disjoint; `(3,)` stays apart, and so do the classes of disjoint types under the merged node. The classes
/// do not depend on whether the two `1`s are one shared type or two equal ones. A recursive
/// type that holds itself as a first component merges a node with one below it.
#[test]
fn classes_join_under_a_tuple_part_outside_its_types_and_merge_the_nodes_of_a_type_met_twice() {
    use super::super::rec::{Def, Expr, Group};
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let one = |t: Type| Type::tuple(vec![t]);
    let e = |t: Type| Type::atom_with("e", &one(t));
    let negated = [one(lit(1)), &one(Type::int()) - &one(lit(1)), one(lit(2))];
    let classes = overlaps(negated.iter());
    assert_eq!(classes, vec![vec![0], vec![1, 2]]);
    let two = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let negated = [
        two(lit(1), lit(1)),
        &two(Type::int(), Type::int()) - &two(lit(1), lit(1)),
        two(lit(2), lit(2)),
    ];
    let classes = overlaps(negated.iter());
    assert_eq!(classes, vec![vec![0, 1, 2]]);
    let shared = lit(1);
    for twice in [
        &one(shared.clone()) | &e(shared.clone()),
        &one(lit(1)) | &e(lit(1)),
    ] {
        let ts = [twice, one(lit(2)), e(lit(2)), one(lit(3)), e(lit(4))];
        let classes = overlaps(ts.iter());
        assert_eq!(classes, vec![vec![0], vec![1, 2], vec![3], vec![4]]);
    }
    // `T = #nil | #cons((T, int))`.
    let cons = Expr::Atom(
        "cons".into(),
        vec![Expr::Ref(0, vec![]), Expr::Type(Type::int())],
    );
    let def = Def {
        name: "T".into(),
        params: vec![],
        body: Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
    };
    let t = Group::new(vec![def])
        .expect("a group")
        .instance(vec![])
        .remove(0);
    let ts = [t, Type::atom("nil"), Type::atom("x"), lit(5)];
    let classes = overlaps(ts.iter());
    assert_eq!(classes, vec![vec![0, 1], vec![2], vec![3]]);
}

/// `inverse` against a scan, and `residue_length` against a scan of the lengths from 1 on
/// every choice of at most two classes of `all` and four of `none` with periods 1 to 6,
/// from a fixed sequence: a length it gives is in every class of `all` and in none of
/// `none`; it gives one whenever the rule (`residues_meet`) finds that one exists; and it
/// gives one only when the scan finds one.
#[test]
fn the_residue_length_agrees_with_a_scan() {
    for m in 1..40u64 {
        for a in 0..m {
            let found = inverse(a, m);
            let scanned = (0..m).find(|&x| a * x % m == 1 % m);
            assert_eq!(found, scanned, "the inverse of {a} modulo {m}");
        }
    }
    let (mut rng, _) = Rng::fresh("the_residue_length_agrees_with_a_scan");
    let mut next = |below: u64| rng.below_u64(below);
    let (mut exists, mut given) = (0, 0);
    for _ in 0..20_000 {
        // Up to four classes of `none`: the case of KERNEL-witness-length-miss has four, and
        // with up to three the scan drew no miss of the choice by expectations alone.
        let (a, b) = (next(3), next(5));
        let mut classes: Vec<(u64, u64)> = (0..a + b)
            .map(|_| {
                let p = 1 + next(6);
                (p, next(p))
            })
            .collect();
        let none = classes.split_off(a as usize);
        let (e, g) = residue_agrees(&classes, &none);
        exists += usize::from(e);
        given += usize::from(g);
    }
    eprintln!("a length given for {given} of the {exists} that have one");
    // The choice is checked on each case where it must give a length: the shares of the
    // classes left out sum below one (the assert in `residue_agrees`). Until 2026-11-15 the
    // test also asserted that 9 in 10 of the drawn cases that had a length were given one
    // (PROOF-test-count-thresholds); that count rested on the draws, the per-case check does
    // not. Built so that the choice must give a length: odd lengths not a multiple of 3, which
    // 1 is, so one exists, and the one share, gcd(2, 3) / 3 = 1/3, is below one.
    assert_eq!(residue_agrees(&[(2, 1)], &[(3, 0)]), (true, true));
}

/// `meeting_pair` finds a pair exactly when some two classes share a length, by the Chinese
/// remainder theorem, and the pair it gives does share one. The classes are drawn with periods
/// of many common divisors (PERF-residue-length-cost).
#[test]
fn a_meeting_pair_agrees_with_every_pair() {
    let (mut rng, _) = Rng::fresh("a_meeting_pair_agrees_with_every_pair");
    let mut next = |below: u64| rng.below_u64(below);
    let periods = [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 5, 10, 30];
    let meet = |a: (u64, u64), b: (u64, u64)| {
        let g = gcd_u64(a.0, b.0);
        a.1 % g == b.1 % g
    };
    let mut found = 0;
    for _ in 0..20_000 {
        let k = next(7);
        let classes: Vec<(u64, u64)> = (0..k)
            .map(|_| {
                let p = periods[next(periods.len() as u64) as usize];
                (p, next(p))
            })
            .collect();
        let any = (0..classes.len()).any(|i| (0..i).any(|j| meet(classes[i], classes[j])));
        match meeting_pair(&classes) {
            Some((i, j)) => {
                assert!(
                    i != j && meet(classes[i], classes[j]),
                    "{classes:?}: {i} {j}"
                );
                found += 1;
            }
            None => assert!(!any, "{classes:?}: a pair meets"),
        }
    }
    // Built: a disjoint cover modulo 6, and one where 3 modulo 4 meets 3 modulo 6 at 3.
    assert_eq!(meeting_pair(&[(2, 0), (6, 1), (6, 3), (6, 5)]), None);
    assert!(meeting_pair(&[(2, 0), (6, 1), (6, 3), (12, 5), (4, 3)]).is_some());
    eprintln!("{found} of 20000 drawn lists had a meeting pair");
}

/// Lengths 1 and 0 modulo 3 and 1 and 2 modulo 6 taken out leave those 5 modulo 6: the shares
/// sum to one and (3, 1) meets (6, 1), so the rule finds a length. The choice by the expected
/// number of classes alone ties on 2 and on 3, takes 0 on both, and the length 0 is in (3, 0)
/// (KERNEL-witness-length-miss). Larger: the same four classes with each period times a prime
/// `r` from 5 to 47 and residues times `r`, with `all` fixing 0 modulo `r`.
#[test]
fn a_length_is_given_when_two_classes_taken_out_meet_and_their_shares_sum_to_one() {
    let none = [(3, 1), (6, 1), (3, 0), (6, 2)];
    assert!(residues_meet(&[], &none) == Lengths::Some);
    let n = residue_length(&[], &none).expect("a length 5 modulo 6");
    assert_eq!(&n % 6u32, BigUint::from(5u32));
    assert_eq!(residue_agrees(&[], &none), (true, true));
    for r in [5u64, 7, 11, 13, 47] {
        let none: Vec<(u64, u64)> = none.iter().map(|&(p, k)| (p * r, k * r)).collect();
        let n = residue_length(&[(r, 0)], &none).expect("a length 5r modulo 6r");
        assert_eq!(&n % (6 * r), BigUint::from(5 * r), "r = {r}");
    }
}

/// Two more sets of classes whose shares sum to one with two that meet, each missed by a
/// plausible wrong choice (found by the XR-wlen cross-review, round 1). Lengths not 0 modulo 2,
/// 1 modulo 6 nor 2 modulo 3 are those 3 modulo 6: weighing each class on a prime by all the
/// residues left on the later primes, not by its own share of them, takes 0 modulo 2 and gives
/// 6. Lengths not 0 or 1 modulo 3, 9 or 11 modulo 12, nor 2 modulo 6 are those 5 modulo 12:
/// the choice by the expected number of classes alone gives 12 when it breaks ties toward the
/// first residue and 11 when toward the last.
#[test]
fn a_length_is_given_where_plausible_wrong_choices_miss() {
    for (none, period, left) in [
        (vec![(2, 0), (6, 1), (3, 2)], 6u32, 3u32),
        (vec![(3, 1), (12, 9), (3, 0), (12, 11), (6, 2)], 12, 5),
    ] {
        assert!(residues_meet(&[], &none) == Lengths::Some, "{none:?}");
        let n = residue_length(&[], &none).expect("a length");
        assert_eq!(&n % period, BigUint::from(left), "{none:?}");
        assert_eq!(residue_agrees(&[], &none), (true, true));
    }
}

/// Erdős's covering system alone is decided by `split_on(2)` going down to the classes modulo
/// 4; with 1 modulo 6 added, the class 3 modulo 4 and the class 1 modulo 3 are each refused by
/// `shares` and no negated class has a finer power of 2 or 3, so no one-prime split decides it
/// (the `erdos_cover` refusal tests in l01_23_groups_and_refusals rest on this;
/// FAIL-periodic-lists-13375960689).
#[test]
fn residues_meet_refuses_erdos_cover_with_1_mod_6() {
    let erdos = [(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)];
    assert!(residues_meet(&[], &erdos) == Lengths::None);
    let mut more = erdos.to_vec();
    more.push((6, 1));
    assert!(residues_meet(&[], &more) == Lengths::Refused);
    assert!(shares(&[(4, 3)], &more) == Lengths::Refused);
    assert!(shares(&[(3, 1)], &more) == Lengths::Refused);
}

/// Odd lengths not 1 modulo 6 are 3 or 5 modulo 6: a choice on 2 that weighs (6, 1) without
/// the residues left on 3 takes 0 modulo 2 and gives 6 (XR-wlen round 1).
#[test]
fn residue_length_weights_the_next_prime() {
    let none = [(2, 0), (6, 1)];
    assert!(residues_meet(&[], &none) == Lengths::Some);
    let length = residue_length(&[], &none).expect("a length 3 or 5 modulo 6");
    let at = &length % 6u32;
    assert!(
        at == BigUint::from(3u32) || at == BigUint::from(5u32),
        "{length}"
    );
}

/// Lengths 1 modulo 4 and 2 modulo 9 are 29 or 65 modulo 72; (72, 29) and (8, 5) both hold 29
/// and (4, 0) and (3, 0) hold neither, so only 65 modulo 72 is left: two positive classes, two
/// classes taken out that are the same inside them, and two that miss them (XR-wlen round 1).
#[test]
fn residue_length_counts_an_overlap_inside_two_positive_classes() {
    let all = [(4, 1), (9, 2)];
    let none = [(72, 29), (8, 5), (4, 0), (3, 0)];
    assert!(residues_meet(&all, &none) == Lengths::Some);
    let length = residue_length(&all, &none).expect("a length 65 modulo 72");
    assert_eq!(&length % 72u32, BigUint::from(65u32));
}

/// A power of a prime above 2^63: the step of the Chinese remainder theorem added two residues
/// of it in `u64` and overflowed (XR-wlen round 1).
#[test]
fn residue_length_handles_a_prime_power_above_half_the_u64_range() {
    let q = 3u64.pow(40);
    let all = [(q, q - 1)];
    assert!(residues_meet(&all, &[]) == Lengths::Some);
    assert_eq!(residue_length(&all, &[]), Some(BigUint::from(q - 1)));
}

/// Checks `residue_length` on the lengths in every class of `all` and in no class of `none`:
/// a length given is one, the rule (`residues_meet`) agrees with the scan where it decides,
/// and a length is given whenever the rule finds one. Gives whether a length exists and
/// whether one was given.
fn residue_agrees(all: &[(u64, u64)], none: &[(u64, u64)]) -> (bool, bool) {
    {
        let fits = |n: u64| {
            all.iter().all(|&(p, at)| n % p == at) && none.iter().all(|&(p, at)| n % p != at)
        };
        // Every class repeats within the lcm of the periods, at most 60.
        let scanned = (1..=60).find(|&n| fits(n));
        let found = residue_length(all, none);
        if let Some(n) = &found {
            let n = u64::try_from(n).expect("below the lcm");
            assert!(n >= 1 && fits(n), "{all:?} {none:?}: {n}");
        }
        assert!(found.is_none() || scanned.is_some(), "{all:?} {none:?}");
        let sum: f64 = none
            .iter()
            .filter(|&&(p, at)| (1..=60).any(|n| fits_all(all, n) && n % p == at))
            .map(|&(p, _)| {
                let l = all.iter().fold(1, |l, &(q, _)| l / gcd_u64(l, q) * q);
                gcd_u64(l, p) as f64 / p as f64
            })
            .sum();
        if sum < 1.0 && scanned.is_some() {
            assert!(found.is_some(), "{all:?} {none:?}: shares {sum}");
        }
        match residues_meet(all, none) {
            Lengths::Some => {
                assert!(
                    scanned.is_some(),
                    "{all:?} {none:?}: the rule finds a length"
                );
                assert!(found.is_some(), "{all:?} {none:?}: the rule finds a length");
            }
            Lengths::None => assert!(scanned.is_none(), "{all:?} {none:?}: the rule finds none"),
            Lengths::Refused => {}
        }
        (scanned.is_some(), found.is_some())
    }
}

fn fits_all(all: &[(u64, u64)], n: u64) -> bool {
    all.iter().all(|&(p, at)| n % p == at)
}

/// In `(a - b) | (b - a)` the diagram tests `b` on two nodes; the region gives each tuple
/// type one entry, so each is tested once and counted once among those open on a component.
#[test]
fn a_region_lists_each_tuple_type_once() {
    let a = Type::tuple(vec![Type::int(), Type::top()]);
    let b = Type::tuple(vec![Type::top(), Type::int()]);
    let t = &(&a - &b) | &(&b - &a);
    let f = &t.p().tuples.lens[&2];
    let mut nodes = 0;
    f.atoms(&mut |_| {
        nodes += 1;
        true
    });
    assert!(nodes >= 3);
    let g = region(vec![Type::top(); 2], f);
    assert_eq!((g.atoms.len(), g.missed.len()), (2, 2));
    assert_eq!(g.opens, [1, 1]);
}

/// The kind test of a region reads every kind bit of `outer_kinds`, `f32` too (`KINDS`): a part
/// whose only values are tuples of `f32` is not empty by kind. With nine bits read, the `f32`
/// bit was left out, such a region was called empty, and so were `(f32) - (int)` and every
/// type below, and `(f32)` was called a subtype of `(int)`.
#[test]
fn a_region_whose_only_kind_is_f32_is_not_empty_by_kind() {
    let (f, i) = (Type::f32, Type::int);
    let one = |a: Type| Type::tuple(vec![a]);
    let two = |a: Type, b: Type| Type::tuple(vec![a, b]);
    for (t, len) in [(one(f()), 1), (two(f(), f()), 2)] {
        assert!(!t.is_empty(), "{len}");
        let g = region(vec![Type::top(); len], &t.p().tuples.lens[&len]);
        assert!(!g.structural_empty, "{len}");
    }
    let not_empty = [
        ("(f32) - (int)", &one(f()) - &one(i())),
        (
            "((f32) | (int)) - (int)",
            &(&one(f()) | &one(i())) - &one(i()),
        ),
        (
            "(f32, f32) - (int, _)",
            &two(f(), f()) - &two(i(), Type::top()),
        ),
        ("(f32) & (f32 | int)", &one(f()) & &one(&f() | &i())),
        (
            "((f32) - (int)) & ((f32) - (string))",
            &(&one(f()) - &one(i())) & &(&one(f()) - &one(Type::string())),
        ),
        (
            "(f32, f32) - (f32, int) - (int, f32)",
            &(&two(f(), f()) - &two(f(), i())) - &two(i(), f()),
        ),
        ("(f32 | int) - (int)", &one(&f() | &i()) - &one(i())),
        (
            "(f32, _) - (_, int)",
            &two(f(), Type::top()) - &two(Type::top(), i()),
        ),
    ];
    for (name, t) in &not_empty {
        assert!(!t.is_empty(), "{name}");
    }
    assert!(!one(f()).subtype(&one(i())));
    let either = &two(i(), Type::top()) | &two(Type::top(), i());
    assert!(!two(f(), f()).subtype(&either));
    assert!(one(f()).subtype(&one(&f() | &i())));
}

/// Tuple types with one type in a component share its cell there, which is tested once
/// for all of them; a type that holds the box there is closed, and one open on it is open.
#[test]
fn tuple_types_with_one_component_type_share_its_cell() {
    let lit = |i| Type::lit(&Value::Int(i)).unwrap();
    let ints = Type::int();
    let rows: Vec<Type> = (0..4)
        .map(|i| Type::tuple(vec![lit(i), ints.clone(), lit(i % 2)]))
        .collect();
    let t = Type::union_all(rows);
    let f = &t.p().tuples.lens[&3];
    let g = region(vec![Type::top(); 3], f);
    let sizes: Vec<Vec<usize>> = g
        .cells
        .iter()
        .map(|cells| cells.iter().map(|c| c.rows.len()).collect())
        .collect();
    assert_eq!(sizes, [vec![1, 1, 1, 1], vec![4], vec![2, 2]]);
    assert_eq!(g.opens, [4, 4, 4]);
    let mut h = region(vec![Type::top(), Type::int(), Type::top()], f);
    assert_eq!(h.opens, [4, 0, 4]);
    assert!(h.loose.iter().all(|&(n, at)| (n, at) == (2, 2)));
    // Narrowing the last component to `0` closes the cell `1` as missed for both of its
    // tuple types at once, and leaves `0` to be tested again.
    h.shrink(2, lit(0));
    let h = Search::default().run(move |d| {
        Box::pin(async move {
            let mut h = h;
            d.retest(&mut h).await;
            h
        })
    });
    for (k, a) in h.atoms.iter().enumerate() {
        assert_eq!(h.missed[k], usize::from(a[2] == lit(1)), "{k}");
    }
    assert_eq!(h.opens, [4, 0, 0]);
}

/// Random clauses of one and two literals on `vars` variables.
fn clauses(s: &mut Rng, vars: usize) -> Vec<(Literal2, Literal2)> {
    let m = 1 + s.below(3 * vars);
    let lit = |s: &mut Rng| s.below(2 * vars);
    (0..m)
        .map(|_| {
            let a = lit(s);
            if s.below(3) == 0 { (a, a) } else { (a, lit(s)) }
        })
        .collect()
}

/// Whether the literal `l` holds of the values `x`.
fn holds2(x: &[bool], l: Literal2) -> bool {
    x[l / 2] == l.is_multiple_of(2)
}

/// `TwoSat::solve` answers as enumeration does on random clause sets of up to 12
/// variables, and each solution it gives holds every clause.
#[test]
fn two_sat_solve_agrees_with_enumeration_and_its_solutions_hold() {
    let (mut s, _) = Rng::fresh("two_sat_solve_agrees_with_enumeration_and_its_solutions_hold");
    let mut seen = [0usize; 2];
    for vars in 1..=12 {
        for _ in 0..40 {
            let cs = clauses(&mut s, vars);
            seen[usize::from(two_sat_agrees(vars, &cs))] += 1;
        }
    }
    eprintln!("unsatisfiable, satisfiable: {seen:?}");
    // Both answers on clause sets built to give them, whatever the draws met (PROOF-test-
    // count-thresholds; until 2026-11-15 the test asserted more than 20 of each among the
    // draws). Literal `2v` is variable v true, `2v + 1` false: `x0` and `!x0` hold of no
    // value; `x0` alone holds of x0 true.
    assert!(!two_sat_agrees(1, &[(0, 0), (1, 1)]));
    assert!(two_sat_agrees(1, &[(0, 0)]));
}

/// Checks that `TwoSat::solve` finds a solution of `cs` on `vars` variables exactly when
/// enumeration does, and that the one it gives holds every clause; gives whether one exists.
fn two_sat_agrees(vars: usize, cs: &[(Literal2, Literal2)]) -> bool {
    let sat = (0u64..1 << vars).any(|m| {
        let x: Vec<bool> = (0..vars).map(|v| m >> v & 1 == 1).collect();
        cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b))
    });
    let t = TwoSat {
        vars,
        clauses: cs.to_vec(),
        meets: HashMap::new(),
    };
    let x = t.solve();
    assert_eq!(x.is_some(), sat, "{vars} variables, {cs:?}");
    if let Some(x) = x {
        assert!(cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b)));
    }
    sat
}

/// The five tuple types the tests of [`read_two_sat`] build parts over, `(i)` for `i < 5`,
/// each an atom of its own, read as the variable `i`.
fn two_sat_rows() -> Vec<Row> {
    (0..5)
        .map(|i| {
            Row::new(vec![
                Type::lit(&crate::value::Value::Int(i)).expect("a literal"),
            ])
        })
        .collect()
}

/// Checks [`read_two_sat`] on the part `f` over [`two_sat_rows`], each row the variable of its
/// place: when it reads a 2-CNF, the 2-CNF has a solution exactly when some setting of the five
/// rows puts a tuple in `f` (enumerated), and the solution's first five variables are such a
/// setting. Gives `None` when `f` is no 2-CNF by its structure, else whether it is satisfiable.
fn read_two_sat_agrees(f: &Part<Row>) -> Option<bool> {
    let rows = two_sat_rows();
    let var = |a: &Row| rows.iter().position(|r| r == a);
    let holds = |x: &[bool]| f.eval3(&|a| var(a).map(|v| x[v])) == Some(true);
    let s = read_two_sat(f, rows.len(), &|a| var(a).map(|v| 2 * v))?;
    let sat = (0u32..1 << rows.len())
        .any(|m| holds(&(0..5).map(|v| m >> v & 1 == 1).collect::<Vec<_>>()));
    let x = s.solve();
    assert_eq!(x.is_some(), sat, "{f:?}");
    if let Some(x) = x {
        assert!(
            holds(&x[..rows.len()]),
            "{f:?}: the solution {x:?} is not in the part"
        );
    }
    Some(sat)
}

/// [`read_two_sat`] reads parts built to take its paths, and random parts of the five rows, as
/// enumeration answers them: a part `false` (a contradiction, no solution) and `true`; a choice
/// `a & b | !a & c`, an `or` of two meets each given a variable of its own; a meet of unions; the
/// complement of a meet of unions (an `or` of meets under negation); a clause of three literals
/// and a row with no literal (no 2-CNF). Each random part read as a 2-CNF agrees with
/// enumeration.
#[test]
fn read_two_sat_agrees_with_enumeration_on_built_and_random_parts() {
    use crate::types::bdd::Op;
    let rows = two_sat_rows();
    let [a, b, c, d, e] = [0, 1, 2, 3, 4].map(|i| Part::literal(rows[i].clone()));
    let or = |x: &Part<Row>, y: &Part<Row>| x.zip(y, Op::Or);
    let and = |x: &Part<Row>, y: &Part<Row>| x.zip(y, Op::And);
    assert_eq!(read_two_sat_agrees(&Part::leaf(false)), Some(false));
    assert_eq!(read_two_sat_agrees(&Part::leaf(true)), Some(true));
    let choice = or(&and(&a, &b), &and(&a.not(), &c));
    assert_eq!(read_two_sat_agrees(&choice), Some(true));
    assert_eq!(
        read_two_sat_agrees(&and(&choice, &and(&b.not(), &c.not()))),
        Some(false)
    );
    let meet = and(&or(&a, &b), &or(&c, &d));
    assert_eq!(read_two_sat_agrees(&meet), Some(true));
    assert_eq!(read_two_sat_agrees(&meet.not()), Some(true));
    assert_eq!(
        read_two_sat_agrees(&and(&meet.not(), &and(&a, &c))),
        Some(false)
    );
    assert_eq!(read_two_sat_agrees(&and(&meet.not(), &a)), Some(true));
    assert_eq!(
        read_two_sat_agrees(&and(&meet, &and(&a.not(), &b.not()))),
        Some(false)
    );
    assert_eq!(read_two_sat_agrees(&or(&or(&a, &b), &c)), None);
    let stranger = Part::literal(Row::new(vec![Type::bool()]));
    assert_eq!(read_two_sat_agrees(&and(&a, &stranger)), None);
    // Random parts: each part read as a 2-CNF agrees (the check above); a part of another
    // structure is `None`, which is allowed of any part.
    let (mut s, _) = Rng::fresh("read_two_sat_agrees_with_enumeration_on_built_and_random_parts");
    fn random(s: &mut Rng, depth: u32, atoms: &[Part<Row>]) -> Part<Row> {
        let pick = s.next_u64();
        if depth == 0 || pick.is_multiple_of(4) {
            let p = &atoms[(pick >> 8) as usize % atoms.len()];
            return if pick >> 4 & 1 == 1 {
                p.not()
            } else {
                p.clone()
            };
        }
        let (x, y) = (random(s, depth - 1, atoms), random(s, depth - 1, atoms));
        match pick % 4 {
            1 => x.zip(&y, Op::Or),
            2 => x.zip(&y, Op::And),
            _ => x.zip(&y, Op::Or).not(),
        }
    }
    let atoms = [a, b, c, d, e];
    let mut read = [0usize; 3];
    for _ in 0..3000 {
        let f = random(&mut s, 4, &atoms);
        read[read_two_sat_agrees(&f).map_or(2, usize::from)] += 1;
    }
    eprintln!("unsatisfiable, satisfiable, not a 2-CNF: {read:?}");
}

/// The value the search shows for a satisfiable 2-CNF of 48 bits is a tuple of 48 bits
/// that holds every clause, read from the values shown, not from the search's own check.
#[test]
fn the_value_shown_for_a_two_cnf_holds_every_clause() {
    let vars = 48;
    let (mut s, _) = Rng::fresh("the_value_shown_for_a_two_cnf_holds_every_clause");
    let mut shown = 0;
    for _ in 0..12 {
        let cs: Vec<(Literal2, Literal2)> = (0..vars)
            .map(|_| {
                let mut l = || s.below(2 * vars);
                (l(), l())
            })
            .collect();
        shown += usize::from(shown_holds(vars, &cs));
    }
    eprintln!("{shown} of 12 shown");
    // A satisfiable 2-CNF built, so that a value is shown whatever the draws met (PROOF-test-
    // count-thresholds; until 2026-11-15 the test asserted that one of the 12 drawn was
    // shown): `x_i | x_(i+1)` for each i, every literal `2v` taken, holds of every bit 1.
    let ring: Vec<(Literal2, Literal2)> =
        (0..vars).map(|i| (2 * i, 2 * ((i + 1) % vars))).collect();
    assert!(shown_holds(vars, &ring));
}

/// Checks that the value the search shows for the 2-CNF `cs` on `vars` bits, if any, holds
/// every clause, and that one is shown when `TwoSat::solve` finds the 2-CNF satisfiable;
/// gives whether one is shown.
fn shown_holds(vars: usize, cs: &[(Literal2, Literal2)]) -> bool {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    {
        let cylinder = |l: Literal2| {
            let mut c = vec![Type::top(); vars];
            c[l / 2] = lit(i64::from(l.is_multiple_of(2)));
            Type::tuple(c)
        };
        let mut t = Type::tuple(vec![&lit(0) | &lit(1); vars]);
        for &(a, b) in cs {
            t = &t & &(&cylinder(a) | &cylinder(b));
        }
        let sat = TwoSat {
            vars,
            clauses: cs.to_vec(),
            meets: HashMap::new(),
        }
        .solve()
        .is_some();
        let mut search = Search {
            strict: true,
            refuse_forks: true,
            ..Search::default()
        };
        let Some(v) = search.rep(&t) else {
            assert!(!sat, "{cs:?}");
            return false;
        };
        let Rep::Tuple(vs) = &search.shown[v] else {
            panic!("a tuple is shown")
        };
        let x: Vec<bool> = (vs.iter())
            .map(|&i| match &search.shown[i] {
                Rep::Value(Value::Int(1)) => true,
                Rep::Value(Value::Int(0)) => false,
                _ => panic!("a bit is shown"),
            })
            .collect();
        assert!(cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b)));
        true
    }
}

/// The classes of types inside a recursive group, placed as the group's trie (the walk at
/// `overlaps`). With `P = #a((Q,)) | (int \ 1)` and `Q = #a((P,)) | (int \ 2)`, the cell
/// `#a((P,))` puts `int \ 1` under `#a((..,))`, `int \ 2` one `#a((..,))` deeper, and meets `P`
/// again one deeper still, which merges that node with the first. So `1` two deep meets
/// `int \ 2` and is joined with the cell; `1` one deep is in no value of it; and `1` three deep
/// is at the merged node, where it shares the key `1` with the `1` one deep. The classes are
/// the same with the groups made before, in the other order, and made again after
/// `Type::forget_emptiness`.
#[test]
fn classes_inside_a_recursive_group_follow_its_merged_nodes() {
    use super::super::rec::{Def, Expr, Group};
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let a = |t: Type| Type::atom_with("a", &Type::tuple(vec![t]));
    let def = |name: &str, other: usize, not: i64| Def {
        name: name.into(),
        params: vec![],
        body: Expr::Union(vec![
            Expr::Atom("a".into(), vec![Expr::Ref(other, vec![])]),
            Expr::Type(&Type::int() - &lit(not)),
        ]),
    };
    let group = Group::new(vec![def("P", 1, 1), def("Q", 0, 2)]).expect("a group");
    let p = group.instance(vec![]).remove(0);
    let ts = [a(p), a(a(lit(1))), a(lit(1)), a(a(a(lit(1))))];
    let expected = vec![vec![0, 1], vec![2, 3]];
    Type::forget_emptiness();
    assert_eq!(overlaps(ts.iter()), expected);
    assert_eq!(overlaps(ts.iter()), expected, "with the groups made before");
    let mut classes = overlaps(ts.iter().rev());
    for is in &mut classes {
        for i in is.iter_mut() {
            *i = 3 - *i;
        }
        is.sort();
    }
    classes.sort();
    assert_eq!(classes, expected, "in the other order");
    Type::forget_emptiness();
    assert_eq!(overlaps(ts.iter()), expected, "with the groups made again");
}

/// k types that each reach one ring of k types `T_j = #a_j((T_{j+1},)) | j`, each with an
/// atom name of its own, are apart: the trie of the ring merges no node, and each type places
/// it below its own name (the second tradeoff at `overlaps`, order k^2).
#[test]
fn types_that_each_reach_a_ring_of_names_are_apart() {
    use super::super::rec::{Def, Expr, Group};
    let k = 8;
    let defs = (0..k)
        .map(|j| Def {
            name: format!("T{j}"),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Atom(format!("a{j}"), vec![Expr::Ref((j + 1) % k, vec![])]),
                Expr::Type(Type::lit(&Value::Int(j as i64)).expect("an integer literal")),
            ]),
        })
        .collect();
    let ts = Group::new(defs).expect("a group").instance(vec![]);
    let apart: Vec<Vec<usize>> = (0..k).map(|j| vec![j]).collect();
    assert_eq!(overlaps(ts.iter()), apart);
    // Beside them `#a0((1,))`: only `T0` holds `T1`, and so `1`, under `#a0((..,))` at the root;
    // the other types reach `#a0` only below their own names, so it is joined with `T0` alone.
    let mut with = ts.clone();
    with.push(Type::atom_with(
        "a0",
        &Type::tuple(vec![Type::lit(&Value::Int(1)).expect("1")]),
    ));
    let mut classes: Vec<Vec<usize>> = (1..k).map(|j| vec![j]).collect();
    classes.insert(0, vec![0, k]);
    assert_eq!(overlaps(with.iter()), classes);
}

/// The members of a ring of k types, each `T_j = wrap(j, T_{j+1}) | j`.
fn ring(
    k: usize,
    wrap: impl Fn(usize, super::super::rec::Expr) -> super::super::rec::Expr,
) -> Vec<Type> {
    use super::super::rec::{Def, Expr, Group};
    let defs = (0..k)
        .map(|j| Def {
            name: format!("T{j}"),
            params: vec![],
            body: Expr::Union(vec![
                wrap(j, Expr::Ref((j + 1) % k, vec![])),
                Expr::Type(Type::lit(&Value::Int(j as i64)).expect("an integer literal")),
            ]),
        })
        .collect();
    Group::new(defs).expect("a group").instance(vec![])
}

/// A family of rings: what it is, its k types and the classes they fall into.
pub(super) type Ring = (&'static str, Vec<Type>, Vec<Vec<usize>>);

/// The six families of rings of k types that the benchmarks in `bench.rs` scale, each with its
/// name and the classes `overlaps` gives it:
/// - `T_j = #a_j((T_{j+1},)) | j`, a ring of names, all apart;
/// - `U_j = (#a_j((U_{j+1},)),) | j`, which all share the node of `(..,)` at the root, all apart;
/// - the ring of names beside `#a_j(any \ (0,))` for each j, whose every one-tuple under `#a_j`
///   holds every value under the rest of the ring: `T_j` joined with the j-th whole;
/// - the ring of names, each member also holding `#b_j((int,))`, a type of a lower group;
/// - each holding `#b((int,))`, one name for all, so every type shares the node of `#b` at the
///   root and all are in one class;
/// - each holding `#c_j((L,))` for the list type `L = #nil | #cons((int, L))`, a recursive
///   lower group.
pub(super) fn rings(k: usize) -> Vec<Ring> {
    (0..RINGS).map(|i| ring_family(k, i)).collect()
}

/// The number of families [`rings`] gives.
pub(super) const RINGS: usize = 6;

/// The family `i` of [`rings`] alone, so a benchmark builds only the one it measures.
pub(super) fn ring_family(k: usize, i: usize) -> Ring {
    use super::super::rec::{Def, Expr, Group};
    let apart = || (0..k).map(|j| vec![j]).collect();
    let names = |j: usize, t: Expr| Expr::Atom(format!("a{j}"), vec![t]);
    let int = || Type::tuple(vec![Type::int()]);
    let holding =
        |lower: &dyn Fn(usize) -> Expr| ring(k, |j, t| Expr::Union(vec![names(j, t), lower(j)]));
    match i {
        0 => (
            "k types that each reach a ring of k names",
            ring(k, names),
            apart(),
        ),
        1 => (
            "k types that share a node and reach a ring of k names",
            ring(k, |j, t| Expr::Tuple(vec![names(j, t)])),
            apart(),
        ),
        2 => {
            let zero = Type::tuple(vec![Type::lit(&Value::Int(0)).expect("0")]);
            let mut beside = ring(k, names);
            beside
                .extend((0..k).map(|j| Type::atom_with(&format!("a{j}"), &(&Type::top() - &zero))));
            (
                "a ring of k names beside a whole under each name",
                beside,
                (0..k).map(|j| vec![j, k + j]).collect(),
            )
        }
        3 => (
            "k types that each reach a ring of k names holding a lower type",
            holding(&|j| Expr::Type(Type::atom_with(&format!("b{j}"), &int()))),
            apart(),
        ),
        4 => (
            "k types that each reach a ring of k names holding one lower type under one name",
            holding(&|_| Expr::Type(Type::atom_with("b", &int()))),
            vec![(0..k).collect()],
        ),
        5 => {
            let list = Group::new(vec![Def {
                name: "L".into(),
                params: vec![],
                body: Expr::Union(vec![
                    Expr::Type(Type::atom("nil")),
                    Expr::Atom(
                        "cons".into(),
                        vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
                    ),
                ]),
            }])
            .expect("a group")
            .instance(vec![])
            .remove(0);
            (
                "k types that each reach a ring of k names holding a list type",
                holding(&|j| Expr::Atom(format!("c{j}"), vec![Expr::Type(list.clone())])),
                apart(),
            )
        }
        _ => panic!("rings has {RINGS} families, not a family {i}"),
    }
}

/// The classes of the ring families of [`rings`] at a few small sizes, each the one its
/// benchmark in `bench.rs` checks at 2048 and 16384 types.
#[test]
fn the_rings_of_names_have_the_classes_their_shapes_give() {
    for k in [1, 2, 3, 8] {
        for (what, ts, classes) in rings(k) {
            assert_eq!(overlaps(ts.iter()), classes, "{what}, k = {k}");
        }
    }
}

/// A ring of `k` alike lists of `int`, `R_i = #nil | #cons((int, R_{i+1}))` with `R_k = R_0`,
/// has a group trie of the same nodes for every `k` in both directions, and in direction 1,
/// which follows the tail, its members are one group at one node, their nodes bisimilar and
/// merged ([`quotient`], PERF-group-overlaps-dir1), and every pair of its members
/// is one class. Without the quotient the trie has a set of nodes per member, and two types
/// placed at two members walk the whole ring in step.
#[test]
fn a_ring_of_alike_lists_has_one_trie_whatever_its_length() {
    use super::super::rec::{Def, Expr, Group};
    let ring = |k: usize| -> Vec<Type> {
        let defs = (0..k)
            .map(|d| {
                let r = Expr::Ref((d + 1) % k, vec![]);
                let cons = Expr::Atom(
                    "cons".to_string(),
                    vec![Expr::Tuple(vec![Expr::Type(Type::int()), r])],
                );
                Def {
                    name: format!("R{d}"),
                    params: vec![],
                    body: Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                }
            })
            .collect();
        Group::new(defs).expect("a ring").instance(vec![])
    };
    for dir in 0..2 {
        let sizes: Vec<usize> = [1, 2, 3, 64]
            .into_iter()
            .map(|k| {
                let ts = ring(k);
                assert_eq!(
                    overlaps(ts[..2.min(k)].iter()).len(),
                    1,
                    "k = {k}, dir = {dir}"
                );
                let (g, c0) = group_of(&ts[0], dir);
                let (h, c1) = group_of(&ts[k - 1], dir);
                // Direction 0 follows the head, `int`, so there each member is its own group.
                if dir == 1 {
                    assert!(std::rc::Rc::ptr_eq(&g, &h), "k = {k}");
                    assert_eq!(c0, c1, "the members are at one node, k = {k}");
                }
                g.nodes.len()
            })
            .collect();
        assert!(
            sizes.iter().all(|&s| s == sizes[0]),
            "dir = {dir}: {sizes:?}"
        );
    }
}

/// A number in `0..n`, from xorshift64. [`random_cells`] and [`random_group`] draw with it,
/// not with [`Rng`]: `types_that_meet_are_joined_at_the_seeds_that_split_by_order` names
/// seeds whose cases split by order under this stream.
fn below(s: &mut Xorshift64, n: usize) -> usize {
    (s.next_u64() >> 11) as usize % n
}

/// Every value but the one-tuple of the literal `r`: under a node, it holds every one-tuple there
/// but one.
fn all_but_one(r: usize) -> Type {
    let r = Type::lit(&Value::Int(r as i64)).expect("a literal");
    &Type::top() - &Type::tuple(vec![r])
}

/// A random group of one to four members over the types `pool` of lower groups: each member a
/// union of one to three of `#x((T,))`, `#x((P,))`, `(T,)`, `(P, T)`, `(T, P)`, `P`,
/// `#x(any \ (r,))` and a literal `r`, `T` a member, `P` a type of `pool`, `x` one of three
/// names. None if the group is refused.
fn random_group(s: &mut Xorshift64, pool: &[Type], tag: &str) -> Option<Vec<Type>> {
    use super::super::rec::{Def, Expr, Group};
    let n = 1 + below(s, 4);
    let defs = (0..n)
        .map(|d| {
            let alts = (0..1 + below(s, 3))
                .map(|_| {
                    let r = Expr::Ref(below(s, n), vec![]);
                    let p = Expr::Type(pool[below(s, pool.len())].clone());
                    let name = ["a", "b", "c"][below(s, 3)].to_string();
                    match below(s, 8) {
                        0 => Expr::Atom(name, vec![r]),
                        1 => Expr::Atom(name, vec![p]),
                        2 => Expr::Tuple(vec![r]),
                        3 => Expr::Tuple(vec![p, r]),
                        4 => Expr::Tuple(vec![r, p]),
                        5 => p,
                        6 => Expr::Type(Type::atom_with(&name, &all_but_one(below(s, 3)))),
                        _ => Expr::Type(
                            Type::lit(&Value::Int(below(s, 3) as i64)).expect("a literal"),
                        ),
                    }
                })
                .collect();
            Def {
                name: format!("{tag}{d}"),
                params: vec![],
                body: Expr::Union(alts),
            }
        })
        .collect();
    Some(Group::new(defs).ok()?.instance(vec![]))
}

/// Random cells: plain types, the members of a group over them and of a group over both, each
/// type alone, under a name or a one-tuple, or joined with another; and `#x(any \ (r,))` and
/// `(any \ (r,),)`, which hold every value under a node but the one-tuple of a literal `r`.
fn random_cells(s: &mut Xorshift64) -> Vec<Type> {
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("a literal");
    let one = |t: &Type| Type::tuple(vec![t.clone()]);
    let mut pool: Vec<Type> = (0..2 + below(s, 3))
        .map(|_| {
            let r = lit(below(s, 3));
            match below(s, 7) {
                0 => r,
                1 => Type::int(),
                2 => &Type::int() - &r,
                3 => one(&r),
                4 => one(&Type::int()),
                5 => Type::atom_with(["a", "b", "c"][below(s, 3)], &one(&r)),
                _ => Type::atom(["a", "b", "c"][below(s, 3)]),
            }
        })
        .collect();
    for tag in ["L", "U"] {
        if let Some(ms) = random_group(s, &pool, tag) {
            pool.extend(ms);
        }
    }
    (0..3 + below(s, 6))
        .map(|_| {
            let t = &pool[below(s, pool.len())];
            match below(s, 7) {
                0 => Type::atom_with(["a", "b", "c"][below(s, 3)], &one(t)),
                1 => one(t),
                2 => t | &pool[below(s, pool.len())],
                3 => Type::atom_with(["a", "b", "c"][below(s, 3)], &all_but_one(below(s, 3))),
                4 => one(&all_but_one(below(s, 3))),
                _ => t.clone(),
            }
        })
        .collect()
}

/// After the draws, which met `met` pairs that meet and `apart` pairs in different classes,
/// checks both kinds on types built to give them, whatever the draws met (PROOF-test-count-
/// thresholds; until 2026-11-15 each test asserted that the draws met one of each): `(0,)`
/// and `(int,)` meet in `(0,)`, one pair met; `(1, 1)`, of two components, meets neither
/// one-tuple type, so it is a class of its own, two pairs apart.
fn classes_met_and_apart_built(met: usize, apart: usize) {
    eprintln!("{met} pairs met, {apart} apart");
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("a literal");
    let ts = [
        Type::tuple(vec![lit(0)]),
        Type::tuple(vec![Type::int()]),
        Type::tuple(vec![lit(1), lit(1)]),
    ];
    let (mut met, mut apart) = (0, 0);
    check_classes(0, &ts, &mut met, &mut apart);
    assert_eq!((met, apart), (1, 2));
}

/// Checks the classes of `overlaps` on `ts`: two types whose meet is shown inhabited are in one
/// class, and the classes are the same with the types in the other order. Adds the pairs that
/// meet to `met` and the pairs in different classes to `apart`.
fn check_classes(case: usize, ts: &[Type], met: &mut usize, apart: &mut usize) {
    let classes = overlaps(ts.iter());
    let mut class = vec![usize::MAX; ts.len()];
    for (c, is) in classes.iter().enumerate() {
        for &i in is {
            class[i] = c;
        }
    }
    for i in 0..ts.len() {
        for j in i + 1..ts.len() {
            if (&ts[i] & &ts[j]).verdict() == Verdict::Inhabited {
                *met += 1;
                assert_eq!(class[i], class[j], "case {case}: {i} and {j} meet");
            } else if class[i] != class[j] {
                *apart += 1;
            }
        }
    }
    let n = ts.len();
    let mut reversed = overlaps(ts.iter().rev());
    for is in &mut reversed {
        for i in is.iter_mut() {
            *i = n - 1 - *i;
        }
        is.sort();
    }
    reversed.sort();
    assert_eq!(reversed, classes, "case {case} in the other order");
}

/// `overlaps` on random groups whose members hold types of lower groups, recursive ones too
/// ([`check_classes`]).
#[test]
fn types_that_meet_are_joined_in_random_groups_holding_lower_types() {
    joined_in_random_groups_holding_lower_types(crate::seed::seed(
        "types_that_meet_are_joined_in_random_groups_holding_lower_types",
    ));
}

/// The seeds of [`types_that_meet_are_joined_in_random_groups_holding_lower_types`] that split
/// by order before the shared-chain shortcut waited for the chain's first cell
/// (FLAKE-empty-random-groups-joined, found by share1; the cause of
/// FAIL-overlaps-order-ddc1ec274, fixed by 8de5fdf5b): classes `[[0, 2, 3, 4], [1], [5, 7],
/// [6]]` against `[[0, 1, 2, 3, 4], [5, 7], [6]]`, and `[[0, 2, 3, 4, 5, 7], [1, 6]]` against
/// one class of all eight.
#[test]
fn types_that_meet_are_joined_at_the_seeds_that_split_by_order() {
    for seed in [7851126336577227156, 11248837811923780436] {
        joined_in_random_groups_holding_lower_types(seed);
    }
}

/// 400 cases of random groups from `seed` ([`check_classes`]).
fn joined_in_random_groups_holding_lower_types(seed: u64) {
    let mut s = Xorshift64::new(seed | 1);
    let (mut met, mut apart) = (0, 0);
    for case in 0..400 {
        let ts = random_cells(&mut s);
        check_classes(case, &ts, &mut met, &mut apart);
    }
    classes_met_and_apart_built(met, apart);
}

/// The case that split by order (FAIL-overlaps-order-ddc1ec274: case 78 of
/// `ZED_TEST_SEED=1225632394908755589` above). `#b(((0,),)) | (0,)` places `0` at the node of
/// `(0,)`, and under `#b` leaves the node below `((0,),)` waiting; `#b(((0,),))` placed after it
/// reads that node, so `0` is placed there too and the two nodes merge, joining `((0,),)`. The
/// shortcut for a shared chain joined `#b(((0,),))` without reading the waiting node, so in this
/// order the merge was lost and `((0,),)` stood apart, and in the other it was not: classes
/// `[[0], [1], [2, 3, 4, 5]]` against `[[0], [1, 2, 3, 4, 5]]`.
#[test]
fn overlaps_are_the_same_in_both_orders_when_a_chain_waits() {
    let lit0 = Type::lit(&Value::Int(0)).expect("a literal");
    let one = |t: &Type| Type::tuple(vec![t.clone()]);
    let b = Type::atom_with("b", &one(&one(&lit0)));
    let ts = [
        Type::atom_with("c", &all_but_one(0)),
        one(&one(&lit0)),
        b.clone(),
        &b | &one(&lit0),
        Type::atom_with("b", &all_but_one(0)),
        b,
    ];
    let (mut met, mut apart) = (0, 0);
    check_classes(0, &ts, &mut met, &mut apart);
}

/// Checks that [`group_of`], ported onto `zed_graph::Search` (GRAPH-lazy-tarjan), makes the
/// same groups as its walk before the port ([`groups_by_old_walk`]) for `t` and each type
/// inside it, in the same order and each with its members in the same order, so each group's
/// trie is made from the same member. Returns the number of groups of two or more members.
fn group_of_agrees_with_its_old_walk(case: usize, t: &Type) -> usize {
    let none = Type::empty();
    let held = Held::default();
    let mut ts = vec![t.clone()];
    for kid in local(t.p_held(&held), &none).kids {
        ts.extend(kid.inside.into_iter().cloned());
    }
    let mut shared = 0;
    for t in &ts {
        let old = groups_by_old_walk(t);
        let new = groups_by_search(t);
        assert_eq!(new, old, "case {case}: the groups of {t:?}");
        shared += new.iter().filter(|g| g.len() > 1).count();
    }
    shared
}

/// The groups of [`group_of`] are those of its walk before GRAPH-lazy-tarjan, members in the
/// same order: on the two-member group of `classes_inside_a_recursive_group_follow_its_merged_
/// nodes`, from each member, and on the types of random cells over random groups, with the
/// groups made by earlier cases kept, as `overlaps` keeps them, and made again after
/// `Type::forget_emptiness`.
#[test]
fn group_of_makes_the_groups_of_its_walk_before_the_shared_search() {
    use super::super::rec::{Def, Expr, Group};
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let def = |name: &str, other: usize, not: i64| Def {
        name: name.into(),
        params: vec![],
        body: Expr::Union(vec![
            Expr::Atom("a".into(), vec![Expr::Ref(other, vec![])]),
            Expr::Type(&Type::int() - &lit(not)),
        ]),
    };
    for first in 0..2 {
        Type::forget_emptiness();
        let group = Group::new(vec![def("P", 1, 1), def("Q", 0, 2)]).expect("a group");
        let pq = group.instance(vec![]);
        assert_eq!(group_of_agrees_with_its_old_walk(first, &pq[first]), 1);
    }
    let mut s = Xorshift64::new(crate::seed::seed(
        "group_of_makes_the_groups_of_its_walk_before_the_shared_search",
    ));
    let mut shared = 0;
    Type::forget_emptiness();
    for case in 0..400 {
        if case == 200 {
            Type::forget_emptiness();
        }
        for t in random_cells(&mut s) {
            shared += group_of_agrees_with_its_old_walk(case, &t);
        }
    }
    eprintln!("{shared} groups of two or more members compared");
}

/// A random component: one of the integers 0 to 2, every integer, or every integer but one.
fn random_component(s: &mut Rng) -> Type {
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("a literal");
    match s.below(5) {
        3 => Type::int(),
        4 => &Type::int() - &lit(s.below(3)),
        i => lit(i),
    }
}

/// A random tuple type of length one to three.
fn random_tuple(s: &mut Rng) -> Type {
    let m = 1 + s.below(3);
    Type::tuple((0..m).map(|_| random_component(s)).collect())
}

/// Three to eight random types of tuples: tuple types, unions of two, one less another, and
/// every tuple less one or two tuple types.
fn random_tuples(s: &mut Rng) -> Vec<Type> {
    let tuples = Type::universe(crate::types::Universe::Tuple);
    (0..3 + s.below(6))
        .map(|_| match s.below(6) {
            0 => &random_tuple(s) | &random_tuple(s),
            1 => &random_tuple(s) - &random_tuple(s),
            2 => &tuples - &random_tuple(s),
            3 => &(&tuples - &random_tuple(s)) - &random_tuple(s),
            _ => random_tuple(s),
        })
        .collect()
}

/// `overlaps` on random types of tuples of one to three components, negated ones and the
/// tuples of every length less some among them ([`check_classes`]): the runs on later
/// components and the first components of a negated one-tuple type.
#[test]
fn types_that_meet_are_joined_in_random_unions_and_negations_of_tuples() {
    let (mut s, _) =
        Rng::fresh("types_that_meet_are_joined_in_random_unions_and_negations_of_tuples");
    let (mut met, mut apart) = (0, 0);
    for case in 0..1000 {
        let ts = random_tuples(&mut s);
        check_classes(case, &ts, &mut met, &mut apart);
    }
    classes_met_and_apart_built(met, apart);
}

/// The readers a rollback leaves (`Search::drop_reads_since`), read off the first read of
/// each type, agree with a scan of the reads kept, the rule before FAIL-refusals-forked-pair-
/// bench: on random reads of 12 types by 4, made at epochs that do not fall, with types read
/// more than once, rolled back from random epochs, taken out in full and read again.
#[test]
fn a_rollback_keeps_a_reader_exactly_when_a_read_before_it_is_kept() {
    const TYPES: usize = 12;
    const READERS: usize = 4;
    let (mut rng, _) =
        Rng::fresh("a_rollback_keeps_a_reader_exactly_when_a_read_before_it_is_kept");
    let mut next = |below: usize| rng.below(below);
    let mut r = Rollbacks::new(TYPES, READERS);
    let (mut kept, mut dropped) = (0, 0);
    let mut ep = 0;
    for step in 0..20_000 {
        ep += next(2);
        let c = next(READERS);
        let op = match next(8) {
            0 => Rollback::Since(ep.saturating_sub(next(6))),
            1 => Rollback::TakeAll,
            _ => {
                let u = next(TYPES);
                Rollback::Read(pack_read(u, next(2) == 0), ep)
            }
        };
        let (k, d) = r.step(step, c, op);
        (kept, dropped) = (kept + k, dropped + d);
    }
    eprintln!("{kept} kept, {dropped} dropped");
    // Both kinds on reads built to give them, whatever the draws met (PROOF-test-count-
    // thresholds; until 2026-11-15 the test asserted that the draws met one of each). Reader
    // 0 reads type 0 at epochs 0 and 1 and rolls back from 1: the read at 1 goes, and the
    // read at 0 of the same type keeps reader 0 a reader of it. Reader 1 reads type 1 at
    // epoch 2 and rolls back from 2: its only read of type 1 goes, so it is dropped.
    let mut r = Rollbacks::new(TYPES, READERS);
    r.step(0, 0, Rollback::Read(pack_read(0, true), 0));
    r.step(1, 0, Rollback::Read(pack_read(0, true), 1));
    assert_eq!(r.step(2, 0, Rollback::Since(1)), (1, 0));
    r.step(3, 1, Rollback::Read(pack_read(1, true), 2));
    assert_eq!(r.step(4, 1, Rollback::Since(2)), (0, 1));
}

/// One step of [`a_rollback_keeps_a_reader_exactly_when_a_read_before_it_is_kept`] by a reader:
/// a rollback from an epoch, every read taken out, or a read packed by `pack_read` at an epoch.
enum Rollback {
    Since(usize),
    TakeAll,
    Read(usize, usize),
}

/// A search's reads and readers beside a scan of the reads of each reader as kept, and the
/// readers the scan leaves.
struct Rollbacks {
    s: Search,
    scan: Vec<Vec<(usize, usize)>>,
    scan_readers: Vec<BTreeSet<usize>>,
}

impl Rollbacks {
    fn new(types: usize, readers: usize) -> Rollbacks {
        let mut s = Search::default();
        for _ in 0..types {
            s.readers.push(BTreeSet::new());
            s.reads.push(Vec::new());
            s.first_reads.push(DigestMap::default());
        }
        Rollbacks {
            s,
            scan: vec![Vec::new(); readers],
            scan_readers: vec![BTreeSet::new(); types],
        }
    }

    /// Takes `op` by reader `c` in the search and in the scan, and checks they leave the same
    /// reads and readers. Gives the reads a rollback took whose type the reader still reads,
    /// so it stays a reader, and those whose type it no longer reads.
    fn step(&mut self, step: usize, c: usize, op: Rollback) -> (usize, usize) {
        let Rollbacks {
            s,
            scan,
            scan_readers,
        } = self;
        let (mut kept, mut dropped) = (0, 0);
        match op {
            Rollback::Since(from) => {
                let start = scan[c].partition_point(|&(_, e)| e < from);
                let gone: Vec<usize> = scan[c].drain(start..).map(|(p, _)| p).collect();
                let left: BTreeSet<usize> =
                    scan[c].iter().map(|&(p, _)| unpack_read(p).0).collect();
                for &p in &gone {
                    let u = unpack_read(p).0;
                    if left.contains(&u) {
                        kept += 1;
                    } else {
                        scan_readers[u].remove(&c);
                        dropped += 1;
                    }
                }
                assert_eq!(s.drop_reads_since(c, from), gone, "step {step}");
            }
            Rollback::TakeAll => {
                for (p, _) in std::mem::take(&mut scan[c]) {
                    scan_readers[unpack_read(p).0].remove(&c);
                }
                for (p, _) in s.take_reads(c) {
                    s.readers[unpack_read(p).0].remove(&c);
                }
            }
            Rollback::Read(p, ep) => {
                let u = unpack_read(p).0;
                scan[c].push((p, ep));
                scan_readers[u].insert(c);
                s.add_reader(u, c);
                s.push_read(c, p, ep);
            }
        }
        assert_eq!(&s.readers, scan_readers, "step {step}");
        (kept, dropped)
    }
}

/// `#a(∪ i<n: (i, int | bool) \ (i, bool))` holds `#a((i, k))` for each i and integer k and
/// nothing of `#a(∪ i<n: (i, bool))`: their meet is empty, the first is no subtype of the second,
/// and with one tuple left out of the taken-away union the meet holds that tuple's integers only
/// if they were never taken away. The small instance of
/// `the_emptiness_of_a_meet_of_tuple_differences_scales` (FAIL-kernel-empty-tuple-diff-union).
#[test]
fn a_union_of_tuple_differences_is_disjoint_from_the_tuples_taken_away() {
    for n in [1, 2, 5] {
        let (part, paid) = tuple_diff_union_pair(n);
        assert!((&part & &paid).is_empty(), "n = {n}");
        assert!(!part.subtype(&paid), "n = {n}");
        assert!(!paid.subtype(&part), "n = {n}");
        let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("an integer literal");
        let one_int = Type::atom_with("a", &Type::tuple(vec![lit(n - 1), Type::int()]));
        assert!(one_int.subtype(&part), "n = {n}");
        assert!(!(&part & &one_int).is_empty(), "n = {n}");
        let one_true = Type::atom_with("a", &Type::tuple(vec![lit(0), Type::bool()]));
        assert!((&part & &one_true).is_empty(), "n = {n}");
        assert!(one_true.subtype(&paid), "n = {n}");
    }
}

/// Small instances of `the_emptiness_of_a_meet_of_tuple_differences_with_payloads_scales`: a
/// witness tuple whose first component is a scalar and whose second is an atom with a payload,
/// tested against the rows that list that scalar and the rows whose column does not list
/// scalars alone.
#[test]
fn a_union_of_tuple_differences_with_payloads_is_disjoint_from_the_tuples_taken_away() {
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("an integer literal");
    let a = |p: Type| Type::atom_with("a", &p);
    let b = |p: Type| Type::atom_with("b", &Type::tuple(vec![p]));
    for n in [1, 2, 5] {
        let (part, paid) = tuple_diff_union_payload_pair(n);
        assert!((&part & &paid).is_empty(), "n = {n}");
        assert!(!part.subtype(&paid), "n = {n}");
        assert!(!paid.subtype(&part), "n = {n}");
        let one_int = a(Type::tuple(vec![lit(n - 1), b(Type::int())]));
        assert!(one_int.subtype(&part), "n = {n}");
        assert!(!(&part & &one_int).is_empty(), "n = {n}");
        let one_true = a(Type::tuple(vec![lit(0), b(Type::bool())]));
        assert!((&part & &one_true).is_empty(), "n = {n}");
        assert!(one_true.subtype(&paid), "n = {n}");
        // A first component no row lists.
        let unlisted = a(Type::tuple(vec![lit(n + 3), b(Type::int())]));
        assert!((&part & &unlisted).is_empty(), "n = {n}");
        // A row whose first column is all of `int`, so it holds every first component.
        let open = &part | &a(Type::tuple(vec![Type::int(), b(Type::string())]));
        let any_str = a(Type::tuple(vec![lit(n + 3), b(Type::string())]));
        assert!(!(&open & &any_str).is_empty(), "n = {n}");
        assert!(any_str.subtype(&open), "n = {n}");
        assert!((&open & &unlisted).is_empty(), "n = {n}");
    }
}

/// Small instances of `the_emptiness_of_a_meet_of_tuple_differences_with_payload_keys_scales`:
/// a witness tuple whose first component is an atom with a payload and none a scalar
/// (FAIL-kernel-empty-payload-key-tuple).
#[test]
fn a_union_of_tuple_differences_with_payload_keys_is_disjoint_from_the_tuples_taken_away() {
    let a = |p: Type| Type::atom_with("a", &p);
    let k = |i: usize| {
        let lit = Type::lit(&Value::Int(i as i64)).expect("an integer literal");
        Type::atom_with("k", &Type::tuple(vec![lit]))
    };
    for n in [1, 2, 5] {
        let (part, paid) = tuple_diff_union_payload_key_pair(n);
        assert!((&part & &paid).is_empty(), "n = {n}");
        assert!(!part.subtype(&paid), "n = {n}");
        assert!(!paid.subtype(&part), "n = {n}");
        let one_int = a(Type::tuple(vec![k(n - 1), Type::int()]));
        assert!(one_int.subtype(&part), "n = {n}");
        assert!(!(&part & &one_int).is_empty(), "n = {n}");
        let one_true = a(Type::tuple(vec![k(0), Type::bool()]));
        assert!((&part & &one_true).is_empty(), "n = {n}");
        assert!(one_true.subtype(&paid), "n = {n}");
        // A first component no row lists.
        let unlisted = a(Type::tuple(vec![k(n + 3), Type::int()]));
        assert!((&part & &unlisted).is_empty(), "n = {n}");
        // Another atom name, and the same name with another payload shape.
        let other = a(Type::tuple(vec![Type::atom("j"), Type::int()]));
        assert!((&part & &other).is_empty(), "n = {n}");
        // A row whose first column is every `#k` with an integer payload.
        let wide = Type::atom_with("k", &Type::tuple(vec![Type::int()]));
        let open = &part | &a(Type::tuple(vec![wide, Type::string()]));
        let any_str = a(Type::tuple(vec![k(n + 3), Type::string()]));
        assert!(!(&open & &any_str).is_empty(), "n = {n}");
        assert!(any_str.subtype(&open), "n = {n}");
        assert!((&open & &unlisted).is_empty(), "n = {n}");
    }
}

/// The keys `Columns` files a column type under ([`Reading::Payloads`]) are sound: a value in
/// a listed type has a key ([`leaf`]) that the type lists, read along first components and the
/// tuple payloads of atoms at any depth; a type with an atom name whose payload is not listed,
/// or with names not listed, is not listed (FAIL-kernel-empty-payload-key-tuple).
#[test]
fn a_value_in_a_listed_column_type_has_a_key_the_type_lists() {
    let int = |i: i64| Value::Int(i);
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let k = |p: Type| Type::atom_with("k", &Type::tuple(vec![p]));
    let j = |p: Type, q: Type| Type::atom_with("j", &Type::tuple(vec![p, q]));
    let kv = |v: Value| Value::atom_with("k", vec![v]);
    let jv = |v: Value, w: Value| Value::atom_with("j", vec![v, w]);
    let listed = [
        (k(&lit(1) | &lit(2)), vec![kv(int(1)), kv(int(2))]),
        (
            k(j(lit(3), Type::string())),
            vec![kv(jv(int(3), Value::str("s")))],
        ),
        (
            Type::tuple(vec![k(lit(4)), Type::int()]),
            vec![Value::tuple(vec![kv(int(4)), int(9)])],
        ),
        (
            &Type::atom("b") | &k(Type::tuple(vec![lit(5), Type::bool()])),
            vec![
                Value::atom("b"),
                kv(Value::tuple(vec![int(5), Value::Bool(true)])),
            ],
        ),
        (
            k(Type::tuple(Vec::new())),
            vec![kv(Value::tuple(Vec::new()))],
        ),
    ];
    let mut filer = Filer::default();
    for (t, values) in &listed {
        let filed = filer.file(t, Reading::Payloads);
        assert!(filed.listed, "{t} is listed");
        for x in values {
            assert!(t.contains(x), "{x} is in {t}");
            let key = leaf(x).expect("a value of these types has a key");
            assert!(filed.keys.contains(&key), "{t} lists the key {key} of {x}");
        }
    }
    for t in [k(Type::int()), &j(lit(1), Type::int()) | &k(Type::string())] {
        assert!(
            !filer.file(&t, Reading::Payloads).listed,
            "{t} is not listed"
        );
    }
}

/// The search keeps one row index and one `Columns` per tuple part it tests a tuple against,
/// keyed by the part's id. A diagram leaf's id is its value, the same for every tuple length,
/// so the empty part (leaf `false`) of length 1 and that of length 2 shared one entry here:
/// `Columns` made for length 1 was read with the keys of a pair, and `candidates` indexed a
/// column it did not have ("index out of bounds: the len is 1 but the index is 1"). The types
/// are those of the smallest pair seen, `#box((#pair(), 1,))` and `#box((#pair((), 1),))`
/// (seed 6869086033364754509 of the l01_29 round-trip test), built here without the reader
/// (FAIL-kernel-candidates-key-past-columns).
#[test]
fn leaf_parts_of_different_tuple_lengths_keep_separate_indexes() {
    let one = Type::lit(&Value::Int(1)).expect("an integer literal");
    let unit = Type::tuple(Vec::new());
    let boxed = |t: Type| Type::atom_with("box", &Type::tuple(vec![t]));
    let a = boxed(Type::tuple(vec![
        Type::atom_with("pair", &unit),
        one.clone(),
    ]));
    let b = boxed(Type::tuple(vec![Type::atom_with(
        "pair",
        &Type::tuple(vec![unit.clone(), one.clone()]),
    )]));
    assert!(!a.subtype(&b), "{a} is not a subtype of {b}");
    assert!(!b.subtype(&a), "{b} is not a subtype of {a}");
}

/// The atom of a union of n tuple differences, `#a(∪ i<n: (i, int | bool) \ (i, bool))`, and the
/// atom of the union of the n tuples taken away, `#a(∪ i<n: (i, bool))`. They are disjoint, and
/// the first is not a subtype of the second. FAIL-kernel-empty-tuple-diff-union.
pub(super) fn tuple_diff_union_pair(n: usize) -> (Type, Type) {
    let a = |p: Type| Type::atom_with("a", &p);
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("an integer literal");
    let ib = &Type::int() | &Type::bool();
    let part = a(Type::union_all((0..n).map(|i| {
        &Type::tuple(vec![lit(i), ib.clone()]) - &Type::tuple(vec![lit(i), Type::bool()])
    })));
    let paid = a(Type::union_all(
        (0..n).map(|i| Type::tuple(vec![lit(i), Type::bool()])),
    ));
    (part, paid)
}

/// [`tuple_diff_union_pair`] with the second component an atom with a payload, which is not a
/// plain value: `#a(∪ i<n: (i, #b((int | bool))) \ (i, #b((bool))))` and
/// `#a(∪ i<n: (i, #b((bool))))`. Disjoint, and the first not a subtype of the second.
pub(super) fn tuple_diff_union_payload_pair(n: usize) -> (Type, Type) {
    let a = |p: Type| Type::atom_with("a", &p);
    let b = |p: Type| Type::atom_with("b", &Type::tuple(vec![p]));
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("an integer literal");
    let ib = &Type::int() | &Type::bool();
    let part = a(Type::union_all((0..n).map(|i| {
        &Type::tuple(vec![lit(i), b(ib.clone())]) - &Type::tuple(vec![lit(i), b(Type::bool())])
    })));
    let paid = a(Type::union_all(
        (0..n).map(|i| Type::tuple(vec![lit(i), b(Type::bool())])),
    ));
    (part, paid)
}

/// [`tuple_diff_union_pair`] with the first component an atom with a payload, `#k((i))`, so no
/// component of a witness tuple is a scalar: `#a(∪ i<n: (#k((i)), int | bool) \ (#k((i)),
/// bool))` and `#a(∪ i<n: (#k((i)), bool))`. Disjoint, and the first not a subtype of the second.
/// FAIL-kernel-empty-payload-key-tuple.
pub(super) fn tuple_diff_union_payload_key_pair(n: usize) -> (Type, Type) {
    let a = |p: Type| Type::atom_with("a", &p);
    let k = |i: usize| {
        let lit = Type::lit(&Value::Int(i as i64)).expect("an integer literal");
        Type::atom_with("k", &Type::tuple(vec![lit]))
    };
    let ib = &Type::int() | &Type::bool();
    let part = a(Type::union_all((0..n).map(|i| {
        &Type::tuple(vec![k(i), ib.clone()]) - &Type::tuple(vec![k(i), Type::bool()])
    })));
    let paid = a(Type::union_all(
        (0..n).map(|i| Type::tuple(vec![k(i), Type::bool()])),
    ));
    (part, paid)
}

/// The seed of a root skips the rows its payload excludes (`Searching::find_rep`, COMPLEXITY.md
/// K126), and the verdicts are those of a search that tries every row: a payload whose one
/// kept row's first value fails is still found inhabited by the search after the seed; one
/// whose kept rows are all excluded again is empty; a union of differences, where no row is
/// excluded, is found inhabited through either arm; and a kept row with one value left
/// outside the excluded row is found inhabited.
#[test]
fn a_seed_skips_excluded_rows_with_the_same_verdicts() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let two = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let a = |t: Type| Type::atom_with("a", &t);
    let int = Type::int;
    let cases = [
        // The kept row `(int, int)` gives `(0, 0)`, which the excluded `(0, int)` holds.
        (
            a(&two(int(), int()) - &two(lit(0), int())),
            Verdict::Inhabited,
        ),
        // `(0 | 1, int)` less both of its first components.
        (
            a(&(&two(&lit(0) | &lit(1), int()) - &two(lit(0), int())) - &two(lit(1), int())),
            Verdict::Empty,
        ),
        // No row is excluded from a union of two differences.
        (
            a(&(&two(lit(0), int()) - &two(lit(0), lit(0)))
                | &(&two(lit(1), int()) - &two(lit(1), lit(1)))),
            Verdict::Inhabited,
        ),
        // Every value of the kept row but `(2, 5)` is excluded.
        (
            a(&two(lit(2), int()) - &two(lit(2), &int() - &lit(5))),
            Verdict::Inhabited,
        ),
    ];
    for (i, (t, want)) in cases.iter().enumerate() {
        assert_eq!(t.verdict(), *want, "case {i}");
        assert_eq!(t.is_empty(), *want == Verdict::Empty, "case {i}");
    }
}

/// The list of length exactly `k`, `#nil` or `#cons((int, R_{k-1}))`, of height `2k`.
fn fixed_list(k: usize) -> Type {
    (0..k).fold(Type::atom("nil"), |r, _| {
        Type::atom_with("cons", &Type::tuple(vec![Type::int(), r]))
    })
}

/// The recursive list type `L = #nil | #cons((int, L))`, and with `cycle` alone the type
/// `G = #cons((int, G))`, which has no value.
fn list_group(cycle: bool) -> Type {
    use super::super::rec::{Def, Expr, Group};
    let cons = Expr::Atom(
        "cons".into(),
        vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
    );
    let body = if cycle {
        cons
    } else {
        Expr::Union(vec![Expr::Type(Type::atom("nil")), cons])
    };
    (Group::new(vec![Def {
        name: "L".into(),
        params: vec![],
        body,
    }]))
    .expect("a group")
    .instance(vec![])
    .remove(0)
}

/// `Heights::height_bounds` on the shapes its proof names (COMPLEXITY.md K126): a fixed-length
/// list is bounded exactly; two of different lengths meet in nothing, as do two pairs whose
/// second components are such lists, and two of one length meet in that length; a recursive
/// list is bounded from below only, and its meet with a fixed-length list is bounded above; a
/// cycle that derives nothing, `G = #cons((int, G))`, is `None`; the atoms outside a finite set
/// and the tuples of every length are unbounded above, and the tuples from the empty one up; a
/// bare atom beside the same name with a payload spans both; a one-tuple type less another is
/// bounded through the tuple types refused before it is taken; and each bound agrees with
/// `is_empty`.
#[test]
fn height_bounds_are_exact_on_lists_cycles_and_open_parts() {
    let int = Type::int;
    let top = u64::MAX;
    let r = fixed_list;
    let one = |t: Type| Type::tuple(vec![t]);
    let cases = [
        ("R_0", r(0), Some((0, 0))),
        ("R_5", r(5), Some((10, 10))),
        ("R_3 & R_5", &r(3) & &r(5), None),
        ("R_4 & R_4", &r(4) & &r(4), Some((8, 8))),
        (
            "(int, R_2) & (int, R_3)",
            &Type::tuple(vec![int(), r(2)]) & &Type::tuple(vec![int(), r(3)]),
            None,
        ),
        ("L", list_group(false), Some((0, top))),
        // The lower end is `least_height`'s, the least over the meet's tuple types one by one,
        // here `(int, L)`; the upper end is the meet's.
        ("L & R_4", &list_group(false) & &r(4), Some((2, 8))),
        ("G", list_group(true), None),
        ("G & R_4", &list_group(true) & &r(4), None),
        (
            "cofinite atoms",
            Type::with(|p| p.atoms = crate::types::Atoms::all()),
            Some((0, top)),
        ),
        (
            "all tuples",
            Type::universe(crate::types::Universe::Tuple),
            Some((1, top)),
        ),
        (
            "#a | #a((R_1,))",
            &Type::atom("a") | &Type::atom_with("a", &one(r(1))),
            Some((0, 4)),
        ),
        (
            "(top,) \\ (int,)",
            &one(Type::top()) - &one(int()),
            Some((1, top)),
        ),
        ("(R_2,) \\ (R_3,)", &one(r(2)) - &one(r(3)), Some((5, 5))),
        ("(R_2,) \\ (R_2,)", &one(r(2)) - &one(r(2)), None),
    ];
    for (name, t, want) in cases {
        let got = Heights::default().height_bounds(&t);
        assert_eq!(got, want, "{name}");
        // The bounds kept for every search (`HEIGHTS`) are the same, asked once and again.
        assert_eq!(height_bounds(&t), want, "{name}, kept");
        assert_eq!(height_bounds(&t), want, "{name}, kept, again");
        assert_eq!(t.is_empty(), want.is_none(), "{name}");
    }
}

/// A witness plan of the prefix-chain sweep that does not check out is dropped, and the list is
/// decided, or given a value, by the general search (TEST-kernel-unreached-paths-11).
/// `chain_rep` answers `None` when a head of the plan has no value (its first `return None`)
/// or when the list the plan gives is not in the type (`check_chain_witness` false, its
/// second). `decided` then forgets the plan and reads the type's parts (the fallback after
/// `chain_rep` in `decided`), and `find_rep` forgets it and builds a value its own way, from
/// the payload of `#cons` under `list_fallback`. No run reached these lines,
/// since the sweep never gave such a plan; whether it can is the sweep's soundness, which no
/// proof here covers, so the fallbacks stay and are tested by placing a wrong plan in the
/// search's table of plans (`Search::chains`) before the search runs. The front sweep is told
/// to leave the types alone (`Search::swept`), and the rule on pure cycles leaves them, as
/// their rows have different items (`int` and `1`). Each plan claims a value: one has a head of
/// no value, and one gives a list in neither type. `E`, which has no value, must come out empty
/// with nothing refused, and the value built for `I` must be in `I`. `E` as a root reads the plan
/// in `find_rep` only: `solve` first seeds a root with atoms by `rep`, which forgets the plan, so
/// `decided` never sees it. `(E,)` has no atoms of its own and is not seeded, so `decided` meets
/// the plan on `E` first and takes its fallback. Negative controls (run 2026-11-20, each failed
/// this test): in `decided`, a failed `chain_rep` taken as a value found (the plan kept and `E`
/// counted inhabited) answers `(E,)` inhabited; the second `return None` of `chain_rep` replaced
/// by going on (the list shown though not checked) answers `E` inhabited. Answering `false` once
/// from the fallback after the plan is forgotten is not caught, and need not be: the next round
/// of `decided` on `E` finds no plan and reads its parts.
#[test]
fn a_witness_plan_that_does_not_check_out_is_dropped_for_the_search() {
    let l = list_group(false);
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let cons = |h: Type, t: Type| Type::atom_with("cons", &Type::tuple(vec![h, t]));
    // `E = L \ #nil \ #cons((int, #nil)) \ #cons((int, #cons((int, L))))`: no value.
    let e = &(&(&l - &Type::atom("nil")) - &cons(Type::int(), Type::atom("nil")))
        - &cons(Type::int(), cons(Type::int(), l.clone()));
    // `I = L \ #nil \ #cons((1, L))`: the lists that do not start with 1, `#nil` not among them,
    // so `find_rep` does not answer it with a bare atom before it reads the plan.
    let i = &(&l - &Type::atom("nil")) - &cons(lit(1), l.clone());
    // The heads `[1, 1]` give `#cons((1, #cons((1, #nil))))`, in neither type.
    let plans = [
        ("a head of no value", vec![Type::empty()]),
        ("a list in neither type", vec![lit(1), lit(1)]),
    ];
    let search = |t: &Type, heads: Vec<Type>| {
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            ..Search::default()
        };
        s.roots.insert(t.clone(), ());
        s.swept.insert(t.clone(), None);
        let plan = ChainPlan::Inhabited {
            stop: "nil".into(),
            link: "cons".into(),
            heads,
            hints: Vec::new(),
        };
        s.chains.insert(t.clone(), Some(plan));
        s
    };
    for (what, heads) in plans {
        let mut s = search(&e, heads.clone());
        let empty = s.solve(&e);
        assert_eq!(s.refused, None, "E, {what}: nothing refused");
        assert!(empty, "E, {what}: E is empty");
        assert!(
            s.chains.get(&e).is_some_and(Option::is_none),
            "E, {what}: the plan is forgotten"
        );
        let pair = Type::tuple(vec![e.clone()]);
        let mut s = search(&e, heads.clone());
        s.roots.insert(pair.clone(), ());
        let empty = s.solve(&pair);
        assert_eq!(s.refused, None, "(E,), {what}: nothing refused");
        assert!(empty, "(E,), {what}: (E,) is empty");
        let mut s = search(&i, heads);
        let r = s.rep(&i).expect("I has a value");
        let v = s.value(r).expect("the value shown is built");
        assert!(i.contains(&v), "I, {what}: {v:?} is in I");
        assert!(
            s.chains.get(&i).is_some_and(Option::is_none),
            "I, {what}: the plan is forgotten"
        );
    }
}

/// A tuple part kept as an expression, not a decision list, that holds tuples outside all its
/// tuple types is not bounded (TEST-kernel-unreached-paths-7, the `Err` arm of
/// `Heights::part_heights`): `(!(1, int) | (int, 2)) & (!(3, int) | (int, 4))` holds
/// `(5, (1, 2))`, a pair in none of its four tuple types, of height 2, while each of those
/// types alone has height 1. Bounding the part by the union of its tuple types would give the
/// pairs the bounds `(1, 1)` and put that value outside them. Such a part is true where no
/// tuple type holds, which every part built by union, meet and difference from tuple types is
/// only in a type whose tuples of unlisted lengths are all in (`Tuples::rest`): a part is false
/// there in each tuple type, and union, meet and difference keep "false there exactly when
/// `rest` is false" (both false; either false; the first false or the second true). So
/// `Heights::most_height` has already taken no upper bound for the type, and the part's own
/// bounds are checked here directly.
#[test]
fn a_tuple_part_kept_as_an_expression_holding_other_tuples_is_not_bounded() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let tuples = Type::universe(crate::types::Universe::Tuple);
    let (int, top) = (Type::int, u64::MAX);
    let a = &(&tuples - &pair(lit(1), int())) | &pair(int(), lit(2));
    let b = &(&tuples - &pair(lit(3), int())) | &pair(int(), lit(4));
    let t = &a & &b;
    let f = &t.p().tuples.lens[&2];
    assert!(f.view().is_err(), "{t}: the part is kept as an expression");
    assert_eq!(f.eval3(&|_| Some(false)), Some(true), "{t}");
    let v = Value::tuple(vec![
        Value::Int(5),
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
    ]);
    assert!(t.contains(&v), "{t} holds {v}");
    let mut h = Heights::default();
    assert_eq!(h.height_bounds(&t), Some((1, top)), "{t}");
    assert_eq!(h.part_heights(2, f), Some(vec![(0, top); 2]), "{t}");
    assert_eq!(height_bounds(&t), Some((1, top)), "{t}, kept");
}

/// `Side::unseen` on a decision list gives the latest first block of a cell not seen and the
/// least block a cell not seen may give that is wanted (TEST-kernel-unreached-paths-7, the arm
/// that takes the lesser of the two candidates for the latter). Blocks 0 to 3 of values true,
/// false, true, false; the component's cells 10, 11 and 12 have first blocks 0, 2 and 3, and
/// the goal wants true with `low` 1 and `high` 2. A cell after `low` is cell 11, at block 2,
/// and the first cell of a block of value true is cell 10, at block 0, also wanted, as block 0
/// is up to `high` and of value true: the least is cell 10's. With cell 10 seen, the least is
/// cell 11's, at the latest block but one, and the latest is cell 12's. Random meets of
/// `nested_cover` reach the case on no run of 16 tried, so it is checked here directly.
#[test]
fn the_least_wanted_unseen_cell_of_a_list_is_the_lesser_of_two_candidates() {
    let component = ListComponent {
        at: HashMap::from([(10, 0), (11, 2), (12, 3)]),
        rest: 4,
        by_block: vec![(0, 10), (2, 11), (3, 12)],
        by_value: [vec![(3, 12)], vec![(0, 10), (2, 11)]],
    };
    let values = vec![true, false, true, false, false];
    let index = ListIndex {
        values: values.clone(),
        components: HashMap::from([(0, component)]),
        by_last: vec![(3, 0)],
        by_first: [vec![], vec![(0, 0)]],
    };
    let goal = Goal {
        values: &values,
        want: true,
        low: 1,
        high: 2,
    };
    let side = Side::List(&index, goal);
    assert_eq!(
        side.unseen(0, &HashSet::new()),
        [Some((3, 12)), Some((0, 10))]
    );
    assert_eq!(
        side.unseen(0, &HashSet::from([10])),
        [Some((3, 12)), Some((2, 11))]
    );
}

/// `Search::value_height`, `Heights::least_height` and `Heights::height_bounds` agree on every
/// value the search finds: for each type of a pool of lists, pairs, atoms and their unions,
/// meets and differences, the value found, when its height is known, lies within the type's
/// bounds, and the least height is the bounds' lower end; a type with no bounds has no value.
#[test]
fn every_value_found_lies_within_its_types_height_bounds() {
    let int = Type::int;
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let mut pool: Vec<Type> = vec![
        list_group(false),
        list_group(true),
        Type::atom("a"),
        int(),
        lit(1),
    ];
    pool.extend((0..4).map(fixed_list));
    let mut types = pool.clone();
    for a in &pool {
        for b in &pool {
            types.push(Type::tuple(vec![a.clone(), b.clone()]));
            types.push(Type::atom_with(
                "a",
                &Type::tuple(vec![a.clone(), b.clone()]),
            ));
            types.push(a | b);
            types.push(a & b);
            types.push(a - b);
        }
    }
    let mut checked = 0;
    for (i, t) in types.iter().enumerate() {
        let mut s = Search::default();
        let mut heights = Heights::default();
        let bounds = heights.height_bounds(t);
        let lo = heights.least_height(t);
        assert_eq!(height_bounds(t), bounds, "type {i}, kept");
        match bounds {
            None => assert!(t.is_empty(), "type {i} has no bounds but a value"),
            Some((l, h)) => {
                assert_eq!(l, lo, "type {i}");
                assert!(l <= h, "type {i}");
                if let Some(v) = s.rep(t)
                    && let Some(x) = s.value_height(v)
                {
                    assert!(l <= x && x <= h, "type {i}: height {x} outside {l}..={h}");
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 100, "only {checked} values measured");
}

/// Checks the 3-SAT reduction in the comment at `residue_length`: variable `i` gets the prime
/// `PRIMES[i]` with its residues 2 and above taken out, so a length's residue 0 or 1 is the
/// variable's value (1 is true), and each clause takes out the one class modulo the product of
/// its three primes where all its literals are false. On fixed and pseudo-random formulas over
/// four variables, a length exists exactly when the formula is satisfiable (scanned up to the
/// product of the primes, where every class repeats); each length decodes to a satisfying
/// assignment and each satisfying assignment encodes, by the Chinese remainder theorem, to a
/// length; and `residue_length` gives no length for an unsatisfiable formula and, when it gives
/// one, a length that decodes to a satisfying assignment.
#[test]
fn the_three_sat_reduction_at_residue_length_is_correct() {
    const PRIMES: [u64; 4] = [3, 5, 7, 11];
    let product: u64 = PRIMES.iter().product();
    // A literal is (variable, positive).
    type Clause = [(usize, bool); 3];
    let satisfies = |f: &[Clause], v: u32| {
        f.iter()
            .all(|c| c.iter().any(|&(i, pos)| ((v >> i) & 1 == 1) == pos))
    };
    let reduce = |f: &[Clause]| {
        let mut none = Vec::new();
        for &p in &PRIMES {
            none.extend((2..p).map(|r| (p, r)));
        }
        for c in f {
            let m: u64 = c.iter().map(|&(i, _)| PRIMES[i]).product();
            // All literals false: residue 0 for a positive literal, 1 for a negative one.
            let at = (0..m)
                .find(|&n| c.iter().all(|&(i, pos)| n % PRIMES[i] == u64::from(!pos)))
                .expect("the Chinese remainder theorem gives one");
            none.push((m, at));
        }
        none
    };
    let decode = |n: u64| (0..4).fold(0u32, |v, i| v | (((n % PRIMES[i]) as u32) << i));
    let encode = |v: u32| {
        (0..product)
            .find(|&n| (0..4).all(|i| n % PRIMES[i] == u64::from((v >> i) & 1)))
            .expect("the Chinese remainder theorem gives one")
    };
    let mut formulas: Vec<Vec<Clause>> = vec![
        // Satisfiable: x0 or x1 or x2.
        vec![[(0, true), (1, true), (2, true)]],
        // Unsatisfiable: all eight clauses over x0, x1, x2.
        (0..8)
            .map(|s: usize| [(0, s & 1 == 1), (1, s & 2 == 2), (2, s & 4 == 4)])
            .collect(),
        // Satisfiable only by x0 = x1 = x2 = true: seven of the eight.
        (1..8)
            .map(|s: usize| [(0, s & 1 == 1), (1, s & 2 == 2), (2, s & 4 == 4)])
            .collect(),
    ];
    // xorshift64 from a fixed seed, kept: the assertion of at least 20 formulas of each kind
    // below counts the formulas of this stream.
    let mut rng = Xorshift64::new(0x2545_f491_4f6c_dd1d);
    let mut next = |k: u64| rng.below(k);
    for _ in 0..200 {
        let clauses = 10 + next(51) as usize;
        let f = (0..clauses)
            .map(|_| {
                let vars = [0usize, 1, 2, 3];
                let skip = next(4) as usize;
                let mut c = [(0, false); 3];
                let mut k = 0;
                for (j, &i) in vars.iter().enumerate() {
                    if j != skip {
                        c[k] = (i, next(2) == 1);
                        k += 1;
                    }
                }
                c
            })
            .collect();
        formulas.push(f);
    }
    let (mut sat, mut unsat) = (0, 0);
    for f in &formulas {
        let none = reduce(f);
        let fits = |n: u64| none.iter().all(|&(p, at)| n % p != at);
        let satisfiable = (0..16).any(|v| satisfies(f, v));
        let lengths: Vec<u64> = (0..product).filter(|&n| fits(n)).collect();
        assert_eq!(!lengths.is_empty(), satisfiable, "{f:?}");
        for &n in &lengths {
            assert!(satisfies(f, decode(n)), "{f:?}: length {n}");
        }
        for v in (0..16).filter(|&v| satisfies(f, v)) {
            assert!(fits(encode(v)), "{f:?}: assignment {v:04b}");
        }
        match residue_length(&[], &none) {
            Some(n) => {
                let n = u64::try_from(&n % product).expect("below the product");
                assert!(fits(n) && satisfies(f, decode(n)), "{f:?}: given {n}");
            }
            None => assert!(
                !satisfiable || residues_meet(&[], &none) == Lengths::Refused,
                "{f:?}"
            ),
        }
        if satisfiable { sat += 1 } else { unsat += 1 }
    }
    assert!(
        sat >= 20 && unsat >= 20,
        "{sat} satisfiable, {unsat} unsatisfiable"
    );
}

/// Cases that catch slips in `greedy_length` the random scan draws rarely (XR-wlen round 1,
/// Gemini seat): a term dead on one prime revived on a later one, a ratio taken one power too
/// far, a meeting pair picked outside the lengths of `all`, and three powers of one prime.
#[test]
fn greedy_length_handles_three_primes_disjoint_pairs_and_deep_trees() {
    // Three primes, shares 29/30: only 0 modulo 30 is left. `(30, 15)` fails on 2 and matches 0
    // on 3; revived on 5, it would pick 6, which `(30, 6)` holds.
    let three_primes = [
        (30, 6),
        (30, 12),
        (30, 18),
        (30, 24),
        (6, 4),
        (6, 2),
        (6, 1),
        (6, 5),
        (10, 1),
        (30, 15),
        (30, 15),
    ];
    assert_eq!(residue_agrees(&[], &three_primes), (true, true));
    // Shares 25/30, leaving 4 modulo 6 (and so even): a ratio one power too far drops the
    // prime 3 at the first step and picks an odd length, which `(10, 1..=9)` all cover.
    let ratio_step = [(10, 1), (10, 3), (10, 5), (10, 7), (10, 9), (6, 0), (6, 2)];
    assert_eq!(residue_agrees(&[], &ratio_step), (true, true));
    // On `all = [(2, 0)]` the shares sum to one; the two `(2, 1)` meet each other but not the
    // even lengths, so the pair must be taken among the classes that meet `all`; 10 modulo 12.
    let disjoint_pair = [(2, 1), (2, 1), (6, 2), (12, 2), (6, 0), (12, 4)];
    let n = residue_length(&[(2, 0)], &disjoint_pair).expect("a length 10 modulo 12");
    assert_eq!(&n % 12u32, BigUint::from(10u32));
    // Three powers of one prime, shares 7/8, leaving 7 modulo 8.
    let deep = [(2, 0), (4, 1), (8, 3)];
    let n = residue_length(&[], &deep).expect("a length 7 modulo 8");
    assert_eq!(&n % 8u32, BigUint::from(7u32));
}

/// Random types for [`kept_height_bounds_agree_with_fresh_ones_across_rebuilds`], made from the
/// draws of `s` alone: the cells of [`random_cells`] (plain types, the members of two random
/// groups, under names and one-tuples), lists, and pairs, meets, unions and differences of
/// them. The same draws make equal types, new nodes and new group instances each time.
fn random_height_types(s: &mut Xorshift64) -> Vec<Type> {
    let mut ts = random_cells(s);
    ts.push(list_group(below(s, 2) == 0));
    ts.push(fixed_list(below(s, 4)));
    for _ in 0..below(s, 6) {
        let a = ts[below(s, ts.len())].clone();
        let b = ts[below(s, ts.len())].clone();
        ts.push(match below(s, 5) {
            0 => Type::tuple(vec![a, b]),
            1 => Type::atom_with("cons", &Type::tuple(vec![a, b])),
            2 => &a | &b,
            3 => &a & &b,
            _ => &a - &b,
        });
    }
    ts
}

/// The first type of `ts` whose bounds kept in `HEIGHTS` ([`height_bounds`]) differ from those
/// a fresh `Heights` finds, with both.
#[expect(clippy::type_complexity, reason = "an index and two pairs of bounds")]
fn first_stale(ts: &[Type]) -> Option<(usize, Option<(u64, u64)>, Option<(u64, u64)>)> {
    ts.iter().enumerate().find_map(|(i, t)| {
        let (kept, fresh) = (height_bounds(t), Heights::default().height_bounds(t));
        (kept != fresh).then_some((i, kept, fresh))
    })
}

/// The bounds kept in `HEIGHTS` never go stale (TEST-heights-cache-invalidation; the proof at
/// `HEIGHTS`): on random types, asked in random order, the kept bounds equal those a fresh
/// `Heights` finds, both before and after the same types are built again from the same draws
/// (new nodes, new instances of the groups, unfoldings made again) with the kept map left
/// as it was, and after `Type::forget_emptiness`, which ends the unit and drops the unfoldings,
/// called between some rounds. Negative control: a wrong entry put in the kept map for one type
/// is found by the same comparison, for that type.
#[test]
fn kept_height_bounds_agree_with_fresh_ones_across_rebuilds() {
    let (mut s, _) = Rng::fresh("kept_height_bounds_agree_with_fresh_ones_across_rebuilds");
    Type::forget_emptiness();
    let mut compared = 0;
    for case in 0..150 {
        let draws = s.next_u64();
        let ts = random_height_types(&mut Xorshift64::new(draws));
        // Ask the kept bounds of some types first, in random order, so later ones find
        // children kept by earlier questions.
        for _ in 0..ts.len() {
            height_bounds(&ts[s.below(ts.len())]);
        }
        assert_eq!(first_stale(&ts), None, "case {case}, as built");
        if s.below(3) == 0 {
            Type::forget_emptiness();
        }
        let again = random_height_types(&mut Xorshift64::new(draws));
        assert_eq!(again.len(), ts.len(), "case {case}: the same draws");
        assert_eq!(first_stale(&again), None, "case {case}, built again");
        compared += ts.len() + again.len();
        // Negative control: a wrong kept entry is seen.
        let k = s.below(again.len());
        let t = &again[k];
        let wrong = match height_bounds(t) {
            None => Some((0, 0)),
            Some((lo, hi)) => Some((lo, hi.saturating_add(1).max(lo + 1))),
        };
        let wrong = if wrong == height_bounds(t) {
            None
        } else {
            wrong
        };
        HEIGHTS.with_borrow_mut(|h| h.bounds.insert(t.clone(), wrong));
        let found = first_stale(&again).expect("a wrong kept entry is found");
        assert_eq!(height_bounds(&again[found.0]), wrong, "case {case}");
        assert_eq!(found.1, wrong, "case {case}");
        Type::forget_emptiness();
    }
    eprintln!("{compared} kept bounds compared with fresh ones");
    assert!(compared > 1000, "only {compared} compared");
}

/// The values the random types are checked on, and the type `bound` that holds exactly them:
/// the integers -2 to 2 and the bare atoms `#a` and `#b` (level 0); their one-tuples, pairs
/// and `#a(x)`, `#b(x)` (level 1); and the one-tuples, `#a(u)`, `#b(u)` and pairs with a
/// level-0 value of each level-1 value `u`.
fn values_and_bound() -> (Vec<Value>, Type) {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let level0: Vec<Value> = (-2..=2)
        .map(Value::Int)
        .chain([Value::atom("a"), Value::atom("b")])
        .collect();
    let above = |xs: &[Value], ys: &[Value]| -> Vec<Value> {
        let mut out = Vec::new();
        for x in xs {
            out.push(Value::tuple(vec![x.clone()]));
            out.push(Value::atom_with("a", vec![x.clone()]));
            out.push(Value::atom_with("b", vec![x.clone()]));
            for y in ys {
                out.push(Value::tuple(vec![x.clone(), y.clone()]));
                out.push(Value::tuple(vec![y.clone(), x.clone()]));
            }
        }
        out
    };
    let level1 = above(&level0, &level0);
    let level2 = above(&level1, &level0);
    let values: Vec<Value> = level0
        .iter()
        .chain(&level1)
        .chain(&level2)
        .cloned()
        .collect();
    let t0 = Type::union_all((-2..=2).map(lit).chain([Type::atom("a"), Type::atom("b")]));
    let above_t = |x: &Type, y: &Type| {
        Type::union_all([
            Type::tuple(vec![x.clone()]),
            Type::atom_with("a", &Type::tuple(vec![x.clone()])),
            Type::atom_with("b", &Type::tuple(vec![x.clone()])),
            Type::tuple(vec![x.clone(), y.clone()]),
            Type::tuple(vec![y.clone(), x.clone()]),
        ])
    };
    let t1 = above_t(&t0, &t0);
    let bound = Type::union_all([t0.clone(), t1.clone(), above_t(&t1, &t0)]);
    (values, bound)
}

/// A random type of depth at most `d` over integers, the atoms `#a` and `#b`, tuples of one and
/// two components, unions, meets and differences, and (when `rec`) instances of random
/// recursive groups.
fn random_type(draw: &mut Rng, d: u32, rec: bool) -> Type {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let name = |draw: &mut Rng| if draw.below_u64(2) == 0 { "a" } else { "b" };
    let small = |draw: &mut Rng| draw.below_u64(5) as i64 - 2;
    let pick = if d == 0 {
        draw.below_u64(5)
    } else {
        draw.below_u64(13)
    };
    let sub = |draw: &mut Rng| random_type(draw, d.saturating_sub(1), rec);
    match pick {
        0 => lit(small(draw)),
        1 => Type::int(),
        2 => &Type::int() - &lit(small(draw)),
        3 => Type::atom(name(draw)),
        4 => Type::top(),
        5 => {
            let n = name(draw);
            Type::atom_with(n, &Type::tuple(vec![sub(draw)]))
        }
        6 => Type::tuple(vec![sub(draw)]),
        7 => Type::tuple(vec![sub(draw), sub(draw)]),
        8 => &sub(draw) | &sub(draw),
        9 => &sub(draw) & &sub(draw),
        10 => &sub(draw) - &sub(draw),
        11 => &Type::universe(crate::types::Universe::Tuple) - &sub(draw),
        _ if rec => random_instance(draw).unwrap_or_else(|| sub(draw)),
        _ => sub(draw),
    }
}

/// An instance of a random recursive group of one or two definitions, or none when the group
/// is rejected.
fn random_instance(draw: &mut Rng) -> Option<Type> {
    use super::super::rec::{Def, Expr, Group};
    fn expr(draw: &mut Rng, defs: usize, d: u32) -> Expr {
        let pick = if d == 0 {
            draw.below_u64(2)
        } else {
            draw.below_u64(8)
        };
        match pick {
            0 => Expr::Type(random_type(draw, 1, false)),
            1 => Expr::Ref(draw.below_u64(defs as u64) as usize, vec![]),
            2 => Expr::Tuple(vec![expr(draw, defs, d - 1)]),
            3 => Expr::Tuple(vec![expr(draw, defs, d - 1), expr(draw, defs, d - 1)]),
            4 => {
                let n = if draw.below_u64(2) == 0 { "a" } else { "b" };
                Expr::Atom(n.into(), vec![expr(draw, defs, d - 1)])
            }
            5 => Expr::Union(vec![expr(draw, defs, d - 1), expr(draw, defs, d - 1)]),
            6 => Expr::And(vec![expr(draw, defs, d - 1), expr(draw, defs, d - 1)]),
            _ => Expr::Diff(
                Box::new(expr(draw, defs, d - 1)),
                Box::new(expr(draw, defs, d - 1)),
            ),
        }
    }
    let defs = 1 + draw.below_u64(2) as usize;
    let group: Vec<Def> = (0..defs)
        .map(|i| Def {
            name: format!("T{i}"),
            params: vec![],
            body: expr(draw, defs, 3),
        })
        .collect();
    let at = draw.below_u64(defs as u64) as usize;
    Some(Group::new(group).ok()?.instance(vec![]).remove(at))
}

/// Random types against membership on a finite set of values (`values_and_bound`): the meet
/// `t & bound` holds exactly the listed values that `Type::contains` puts in `t`, so its verdict
/// has one right answer; `t` itself is never proved empty when a listed value is in it; a
/// subtype found holds only values of its supertype. `Type::contains` reads values against the
/// parts, apart from the search the verdicts come from. A refusal is allowed and counted
/// (row TEST-kernel-unreached-paths-4: the search's paths for cofinite sets, tuples, atoms and
/// recursive groups, reached here with an answer to check).
#[test]
fn random_types_agree_with_membership_on_a_finite_set_of_values() {
    let (values, bound) = values_and_bound();
    assert!(
        values.iter().all(|v| bound.contains(v)),
        "a value outside the bound"
    );
    let mut draw = Rng::new(0x5eed);
    let (mut decided, mut refused) = (0, 0);
    let mut previous = Type::top();
    for case in 0..3000 {
        let rec = case % 3 == 0;
        let t = random_type(&mut draw, 3, rec);
        let held: Vec<bool> = values.iter().map(|v| t.contains(v)).collect();
        let any = held.iter().any(|&h| h);
        let bounded = &t & &bound;
        match bounded.verdict() {
            Verdict::Empty => assert!(!any, "case {case}: {t:?} & bound proved empty"),
            Verdict::Inhabited => assert!(any, "case {case}: {t:?} & bound inhabited"),
            Verdict::Refused(_) => refused += 1,
        }
        if !matches!(bounded.verdict(), Verdict::Refused(_)) {
            decided += 1;
        }
        if bounded.is_empty() {
            assert!(!any, "case {case}: {t:?} & bound is_empty");
        }
        if t.verdict() == Verdict::Empty {
            assert!(!any, "case {case}: {t:?} proved empty");
        }
        for (s, u) in [(&t, &previous), (&previous, &t)] {
            if s.subtype(u) {
                for v in &values {
                    assert!(
                        !s.contains(v) || u.contains(v),
                        "case {case}: {s:?} <: {u:?}, but {v:?} is only in the first"
                    );
                }
            }
        }
        previous = t;
    }
    eprintln!("{decided} decided, {refused} refused");
    assert!(decided > 2000, "only {decided} decided");
}

// Append to: `crates/zed-kernel/src/types/empty/tests.rs`
// Round 3 cross-review kernel unit tests for Q3 (`overlaps` comparison, 1-tuple meet fix, and S_3 permutation check).

#[test]
fn xr_r2_q3_pi_sym_strictly_refines_mirrored_overlaps() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let triple = |a: Type, b: Type, c: Type| Type::tuple(vec![a, b, c]);

    Type::forget_emptiness();
    let w1 = [
        &Type::atom("a") | &pair(pair(lit(1), lit(2)), lit(1)),
        &Type::atom("b") | &pair(pair(lit(1), lit(3)), lit(1)),
    ];
    assert_eq!((&w1[0] & &w1[1]).verdict(), Verdict::Empty);
    assert_eq!(overlaps(w1.iter()), vec![vec![0], vec![1]]);

    Type::forget_emptiness();
    let w2 = [
        &Type::atom("a") | &triple(lit(1), lit(2), lit(1)),
        &Type::atom("b") | &triple(lit(1), lit(3), lit(1)),
    ];
    assert_eq!((&w2[0] & &w2[1]).verdict(), Verdict::Empty);
    assert_eq!(overlaps(w2.iter()), vec![vec![0], vec![1]]);

    Type::forget_emptiness();
    let five = |a: Type, b: Type, c: Type, d: Type, e: Type| Type::tuple(vec![a, b, c, d, e]);
    let w3 = [
        &pair(lit(1), lit(2)) | &five(lit(1), lit(2), lit(2), lit(2), lit(1)),
        &pair(lit(2), lit(1)) | &five(lit(1), lit(2), lit(3), lit(2), lit(1)),
    ];
    assert_eq!((&w3[0] & &w3[1]).verdict(), Verdict::Empty);
    assert_eq!(overlaps(w3.iter()), vec![vec![0], vec![1]]);
}

#[test]
fn xr_r2_q3_one_tuple_meet_reversal_symmetry() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let one = |a: Type| Type::tuple(vec![a]);
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let s = Type::atom("s");

    for k in 1..=20i64 {
        Type::forget_emptiness();
        let c0_w = &one(&pair(lit(k), lit(100 + k)) | &s) & &one(pair(lit(200 + k), lit(k)));
        let c1_w = one(s.clone());
        assert_eq!((&c0_w & &c1_w).verdict(), Verdict::Empty);
        let ts_w = [c0_w, c1_w];
        let g_w = overlaps(ts_w.iter());

        Type::forget_emptiness();
        let c0_r = &one(&pair(lit(100 + k), lit(k)) | &s) & &one(pair(lit(k), lit(200 + k)));
        let c1_r = one(s.clone());
        let ts_r = [c0_r, c1_r];
        let g_r = overlaps(ts_r.iter());

        assert_eq!(g_w, g_r, "1-tuple meet reversal asymmetry at k={k}");
        assert_eq!(
            g_w,
            vec![vec![0], vec![1]],
            "1-tuple meet failed to intersect out #s at k={k}"
        );
    }
}

#[test]
fn xr_r2_q3_three_tuple_non_reversal_permutation_boundary() {
    let triple = |a: Type, b: Type, c: Type| Type::tuple(vec![a, b, c]);
    let (a, b, x, y) = (
        Type::atom("a"),
        Type::atom("b"),
        Type::atom("x"),
        Type::atom("y"),
    );

    Type::forget_emptiness();
    let id_order = [
        triple(
            y.clone(),
            triple(x.clone(), a.clone(), x.clone()),
            y.clone(),
        ),
        triple(
            y.clone(),
            triple(x.clone(), b.clone(), x.clone()),
            y.clone(),
        ),
    ];
    assert_eq!((&id_order[0] & &id_order[1]).verdict(), Verdict::Empty);
    let g_id = overlaps(id_order.iter());

    Type::forget_emptiness();
    let perm_12 = [
        triple(y.clone(), y.clone(), triple(x.clone(), x.clone(), a)),
        triple(y.clone(), y, triple(x.clone(), x, b)),
    ];
    let g_perm = overlaps(perm_12.iter());

    assert_eq!(g_id, vec![vec![0, 1]]);
    assert_eq!(g_perm, vec![vec![0], vec![1]]);
}

/// Plan row PERF-value-key-sites-bench: classes keyed by [`ValueKey`], given as `stored_class`
/// gives them (`entry` and `or_insert` of the next number), to families. Every value of a group
/// of `value::key_forms::family_key_groups` (a range, its map and a `++` list; `0.0` and `-0.0`,
/// two classes; a rational, a key past 64 bits and a string key in two forms; nested families;
/// values swapped between keys; families one entry apart) gets its group's class, and the groups
/// get one class each. A tuple key of those classes is one class per group too.
#[test]
fn equal_families_get_one_class_by_value_key() {
    let keys = crate::value::key_forms::family_keys();
    let mut classes: HashMap<ValueKey, usize> = HashMap::new();
    let mut of_group: BTreeMap<usize, usize> = BTreeMap::new();
    for (v, g) in &keys {
        let next = classes.len();
        let class = *classes.entry(ValueKey::Value(v.clone())).or_insert(next);
        assert_eq!(*of_group.entry(*g).or_insert(class), class, "{v}");
    }
    let groups = of_group.len();
    assert_eq!(classes.len(), groups);
    for (v, g) in &keys {
        let class = classes[&ValueKey::Value(v.clone())];
        let next = classes.len();
        let pair = ValueKey::Tuple(vec![class, *g]);
        let paired = *classes.entry(pair).or_insert(next);
        assert_eq!(classes[&ValueKey::Tuple(vec![of_group[g], *g])], paired);
    }
    assert_eq!(classes.len(), 2 * groups);
}

/// Lists and the fork-refused type `nfa` of the refusal step tests, built in the kernel.
mod fork_inputs {
    use super::super::super::rec::{Def, Expr, Group};
    use super::*;

    pub(super) fn r(i: usize) -> Expr {
        Expr::Ref(i, vec![])
    }

    pub(super) fn cons(head: Expr, tail: Expr) -> Expr {
        Expr::Atom("cons".into(), vec![head, tail])
    }

    pub(super) fn nil() -> Expr {
        Expr::Type(Type::atom("nil"))
    }

    pub(super) fn def(name: &str, body: Expr) -> Def {
        Def {
            name: name.into(),
            params: vec![],
            body,
        }
    }

    pub(super) fn lit(i: i64) -> Type {
        Type::lit(&Value::Int(i)).expect("an integer literal")
    }

    pub(super) fn list(head: Type) -> Type {
        let body = Expr::Union(vec![nil(), cons(Expr::Type(head), r(0))]);
        Group::new(vec![def("L", body)])
            .expect("a group")
            .instance(vec![])
            .remove(0)
    }

    /// `by_place_from_the_end` of the step tests: the lists of integers with a 1 at each place
    /// `i` from the end for `i` up to `n`, with a 1 beyond `n`, or with no 1.
    pub(super) fn by_place_from_the_end(n: usize) -> Type {
        let int = || Expr::Type(Type::int());
        let mut defs = vec![def("R0", nil())];
        defs.extend((1..=n).map(|k| def(&format!("R{k}"), cons(int(), r(k - 1)))));
        defs.extend((1..=n).map(|i| {
            let body = Expr::Union(vec![
                cons(int(), r(n + i)),
                cons(Expr::Type(lit(1)), r(i - 1)),
            ]);
            def(&format!("G{i}"), body)
        }));
        let a = 2 * n + 1;
        defs.push(def("A0", Expr::Union(vec![nil(), cons(int(), r(a))])));
        defs.extend((1..=n).map(|k| def(&format!("A{k}"), cons(int(), r(a + k - 1)))));
        let far = Expr::Union(vec![
            cons(int(), r(a + n + 1)),
            cons(Expr::Type(lit(1)), r(a + n)),
        ]);
        defs.push(def("H", far));
        let ts = Group::new(defs).expect("a group").instance(vec![]);
        let no_one = list(&Type::int() - &lit(1));
        (1..=n)
            .map(|i| &ts[n + i])
            .chain([&ts[a + n + 1], &no_one])
            .fold(Type::empty(), |u, t| &u | t)
    }

    /// Empty, refused for a fork: the decision would follow places 1 and 2 from the end at once.
    pub(super) fn nfa() -> Type {
        &list(Type::int()) - &by_place_from_the_end(2)
    }
}

/// A member of a second group that reads a fork-refused type only through another member is
/// still decided: `group_verdict` blames the fork on the member that reads it (the
/// `blame.push` of a `Refused(Fork)` member), so the search of the group goes on past it.
/// Negative control: with that arm made to refuse the whole search instead, `F` comes back
/// `Refused(Fork)` in both orders.
#[test]
fn fork_read_by_another_group_is_blamed_on_its_reader() {
    use super::super::rec::{Expr, Group};
    use fork_inputs::*;
    for f_first in [true, false] {
        Type::forget_emptiness();
        let d = Group::new(vec![def(
            &format!("BlameD{f_first}"),
            Expr::Union(vec![Expr::Type(nfa()), cons(Expr::Type(Type::int()), r(0))]),
        )])
        .expect("a group")
        .instance(vec![])
        .remove(0);
        assert_eq!(d.verdict(), Verdict::Refused(Refusal::Fork));
        let es = Group::new(vec![
            def(
                &format!("BlameE{f_first}"),
                Expr::Union(vec![
                    cons(Expr::Type(Type::int()), Expr::Type(d)),
                    cons(Expr::Type(Type::bool()), r(0)),
                ]),
            ),
            def(
                &format!("BlameF{f_first}"),
                Expr::Union(vec![
                    cons(Expr::Type(Type::bool()), r(1)),
                    Expr::And(vec![r(0), nil()]),
                ]),
            ),
        ])
        .expect("a group")
        .instance(vec![]);
        let (e, f) = if f_first {
            let f = es[1].verdict();
            (es[0].verdict(), f)
        } else {
            (es[0].verdict(), es[1].verdict())
        };
        assert_eq!(f, Verdict::Empty, "F first: {f_first}");
        assert_eq!(e, Verdict::Refused(Refusal::Fork), "F first: {f_first}");
    }
}

/// Item TEST-kernel-unreached-paths-6: the fixed priority by which a search picks the refusal
/// it reports (`Search::refusal_rank`) puts the kinds in one strict order: a fork first, then a
/// group, residues, shared cells by component, a tuple split, a morphism split, and no witness
/// last, so the refusal kept does not depend on the order the give-ups are met in. No test meets a search that gives up on residues or on no witness
/// beside another refusal, so the ranks of those two were not read.
#[test]
fn the_refusals_a_search_gives_up_on_are_ranked_in_a_fixed_order() {
    let order = [
        Refusal::Fork,
        Refusal::Group,
        Refusal::Residues,
        Refusal::SharedCells(0),
        Refusal::SharedCells(1),
        Refusal::TupleSplit,
        Refusal::MorphismSplit,
        Refusal::NoWitness,
    ];
    for w in order.windows(2) {
        assert!(
            Search::refusal_rank(w[0]) < Search::refusal_rank(w[1]),
            "{:?} before {:?}",
            w[0],
            w[1]
        );
    }
}

/// Item TEST-kernel-unreached-paths-8: the check of a list witness
/// (`Searching::check_chain_witness`), called on lists whose tails it cannot read as a chain,
/// passes no list that is not in the type (`Type::contains`), and passes every list of a plain
/// list type. Each system below is `L` and the tails its links lead to, of a shape the check
/// gives up on: a link of another name, another stop, an integer beside the atoms, two stops,
/// link payloads of two lengths, two self-looping rows with different items, two rows that do
/// not loop, a link of any pair, a link whose payload may be a struct (one row of pairs), and
/// two rows whose tails share a tail it cannot read; and a row whose tail never stops. Every
/// list of up to four items from `1` and `2` is tried, with no hint and with each hint
/// ([`ChainHint`]) on each row of the link payload, which must not change the answer. Changing the `return None` for another link or stop, or for two
/// rows that do not loop, into a pass makes this test fail (negative controls,
/// TEST-kernel-unreached-paths-8). Since KERNEL-verify-step-self-loop-tail the check reads two
/// self-looping rows with different items (one as the chain, one as the exit); that system stays
/// here as a test that the reading passes no list outside the type. Since
/// TEST-kernel-unreached-paths-12 the check also reads one row beside records (the system of a
/// payload that may be a struct), which stays here for the same reason; its membership is tested
/// by `the_check_of_a_list_witness_is_membership_beside_records`.
#[test]
fn the_check_of_a_list_witness_passes_no_list_outside_the_type() {
    use super::super::rec::{Expr, Group};
    use fork_inputs::{cons, def, lit, nil, r};
    let ty = |t: Type| Expr::Type(t);
    let atom = |name: &str, head: Expr, tail: Expr| Expr::Atom(name.into(), vec![head, tail]);
    let int = || ty(Type::int());
    let end = || ty(Type::atom("end"));
    // Each system, as its definitions: `L` first, read through `r(0)`.
    let systems: Vec<(&str, Vec<Expr>)> = vec![
        ("plain", vec![Expr::Union(vec![nil(), cons(int(), r(0))])]),
        (
            "a link of another name",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), atom("node", int(), r(1))]),
            ],
        ),
        (
            "another stop",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![end(), cons(int(), r(1))]),
            ],
        ),
        (
            "an integer beside the atoms",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), ty(lit(5)), cons(int(), r(1))]),
            ],
        ),
        (
            "two stops",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), end(), cons(int(), r(1))]),
            ],
        ),
        (
            "link payloads of two lengths",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![
                    nil(),
                    cons(int(), r(1)),
                    Expr::Atom("cons".into(), vec![int(), int(), int()]),
                ]),
            ],
        ),
        (
            "two self-looping rows with different items",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(2)), cons(ty(lit(2)), r(3))]),
                Expr::Union(vec![nil(), cons(int(), r(2))]),
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(3))]),
            ],
        ),
        (
            "two rows that do not loop",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(2)), cons(ty(lit(2)), nil())]),
                cons(int(), nil()),
            ],
        ),
        (
            "a link of any pair",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), cons(ty(Type::top()), ty(Type::top()))]),
            ],
        ),
        (
            "a link whose payload may be a struct",
            vec![Expr::Union(vec![
                nil(),
                cons(int(), r(0)),
                ty(Type::atom_with(
                    "cons",
                    &Type::universe(crate::types::Universe::Struct),
                )),
            ])],
        ),
        (
            "two rows into one tail it cannot read",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1)), cons(ty(lit(1)), r(2))]),
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(3))]),
                cons(ty(lit(2)), r(3)),
                Expr::Union(vec![nil(), atom("node", int(), r(3))]),
            ],
        ),
        (
            "a tail that never stops",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1)), cons(ty(lit(2)), r(2))]),
                cons(int(), r(1)),
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(2))]),
            ],
        ),
    ];
    let mut lists: Vec<Vec<i64>> = vec![vec![]];
    for k in 0..4 {
        let longer: Vec<Vec<i64>> = (lists.iter())
            .filter(|l| l.len() == k)
            .flat_map(|l| [1, 2].map(|x| [l.clone(), vec![x]].concat()))
            .collect();
        lists.extend(longer);
    }
    for (name, bodies) in systems {
        let defs = (bodies.into_iter().enumerate())
            .map(|(k, b)| def(&format!("W{k}"), b))
            .collect();
        let t = Group::new(defs)
            .expect("a group")
            .instance(vec![])
            .remove(0);
        let rows = (t.p().atoms.names().get("cons"))
            .and_then(|a| a.payload.p().tuples.lens.get(&2)?.union_rows())
            .unwrap_or_default();
        let mut passed = 0;
        for l in &lists {
            Type::forget_emptiness();
            let value = (l.iter().rev()).fold(Value::atom("nil"), |rest, &x| {
                Value::atom_with("cons", vec![Value::Int(x), rest])
            });
            let check = |hints: Vec<(crate::types::Row, ChainHint)>| {
                let (t2, items) = (t.clone(), l.clone());
                Search::default().run(move |d| {
                    Box::pin(async move {
                        let ids: Vec<usize> = (items.iter())
                            .map(|&x| d.s().show(Rep::Value(Value::Int(x))))
                            .collect();
                        let (link, stop) = ("cons".into(), "nil".into());
                        d.check_chain_witness(&t2, &link, &ids, &stop, &hints).await
                    })
                })
            };
            let ok = check(vec![]);
            assert!(
                !ok || t.contains(&value),
                "{name}: {l:?} passed, not in the type"
            );
            passed += usize::from(ok);
            // A hint, on any row and whether it holds or not, changes no answer.
            for row in &rows {
                let hints = (0..=l.len() + 1).map(ChainHint::Miss);
                for hint in hints.chain([ChainHint::Len]) {
                    Type::forget_emptiness();
                    assert_eq!(
                        check(vec![(row.clone(), hint)]),
                        ok,
                        "{name}: {l:?} with {hint:?} on a row"
                    );
                }
            }
        }
        if name == "plain" {
            assert_eq!(
                passed,
                lists.len(),
                "every list of the plain list type passes"
            );
        }
    }
}

/// Item TEST-kernel-unreached-paths-9: on list types the check of a list witness
/// (`Searching::check_chain_witness`) reads as a chain, its answer is membership
/// (`Type::contains`), both ways, for every list of up to five items from `1`, `2` and `9`. Each
/// system is `W0` and its tails; most have tails whose link payload is a chain row and a row
/// into a self-looping tail `L` (a node with an `emit`: a list may leave the chain there and end
/// in the loop), with alternating heads (one link a node, so the walk jumps by binary lifting)
/// or equal heads (runs of links), acyclic or on a cycle, and tails with no stop; one system's
/// link has one field, so no pair is under it and only the empty list is in it. The acyclic
/// chains end in `nil` alone; chains ending in a last tail `nil | cons(h, itself)` are in
/// `the_check_of_a_list_witness_reads_a_chain_ending_in_a_self_looping_tail`. Equal items share one shown id, so
/// they form runs: an item in both a chain head and its exit's head stops a jump at that node
/// (the `emit` stop of the pass walk, `pass_memo` set to 0), and an item leaving the chain for
/// the loop answers at once (`break 'walk Some(true)`).
#[test]
fn the_check_of_a_list_witness_is_membership_on_chains_with_exits() {
    use super::super::rec::Expr;
    use fork_inputs::{cons, lit, nil, r};
    let ty = |t: Type| Expr::Type(t);
    let one = || ty(lit(1));
    let nine = || ty(lit(9));
    let int = || ty(Type::int());
    // `W0` first; the last definition is the loop `L` where a system has one.
    let systems: Vec<(&str, Vec<Expr>)> = vec![
        (
            "alternating heads, an exit of 9 into a loop of 2",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(one(), r(2)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(int(), r(3)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(one(), r(4)), cons(nine(), r(5))]),
                Expr::Union(vec![nil()]),
                Expr::Union(vec![nil(), cons(ty(lit(2)), r(5))]),
            ],
        ),
        (
            "alternating heads, an exit of 9 into a loop of int",
            vec![
                Expr::Union(vec![nil(), cons(one(), r(1)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(int(), r(2)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(one(), r(3)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(int(), r(4)), cons(nine(), r(5))]),
                Expr::Union(vec![nil()]),
                Expr::Union(vec![nil(), cons(int(), r(5))]),
            ],
        ),
        (
            "equal heads, an exit of int into a loop of 2",
            vec![
                Expr::Union(vec![nil(), cons(one(), r(1)), cons(int(), r(4))]),
                Expr::Union(vec![nil(), cons(one(), r(2)), cons(int(), r(4))]),
                Expr::Union(vec![nil(), cons(one(), r(3)), cons(int(), r(4))]),
                Expr::Union(vec![nil()]),
                Expr::Union(vec![nil(), cons(ty(lit(2)), r(4))]),
            ],
        ),
        (
            "heads of int, an exit of 9 into a loop of 9",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), cons(int(), r(2)), cons(nine(), r(5))]),
                Expr::Union(vec![nil(), cons(one(), r(3))]),
                Expr::Union(vec![nil(), cons(int(), r(4)), cons(nine(), r(5))]),
                Expr::Union(vec![nil()]),
                Expr::Union(vec![nil(), cons(nine(), r(5))]),
            ],
        ),
        (
            "a cycle of two heads, each with an exit of 9",
            vec![
                Expr::Union(vec![nil(), cons(one(), r(1)), cons(nine(), r(2))]),
                Expr::Union(vec![nil(), cons(int(), r(0)), cons(nine(), r(2))]),
                Expr::Union(vec![nil(), cons(ty(lit(2)), r(2))]),
            ],
        ),
        (
            "tails with no stop, an exit of 9",
            vec![
                Expr::Union(vec![cons(int(), r(1)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(one(), r(2)), cons(nine(), r(4))]),
                Expr::Union(vec![cons(int(), r(3)), cons(nine(), r(4))]),
                Expr::Union(vec![nil()]),
                Expr::Union(vec![nil(), cons(int(), r(4))]),
            ],
        ),
        // No pairs under the link: only the empty list is in it.
        (
            "a link of one field",
            vec![Expr::Union(vec![
                nil(),
                Expr::Atom("cons".into(), vec![int()]),
            ])],
        ),
    ];
    assert_check_is_membership(systems);
}

/// Item TEST-kernel-unreached-paths-12: the check of a list witness
/// (`Searching::check_chain_witness`) on lists whose link payloads hold records beside their
/// pairs: its answer is membership (`Type::contains`), both ways, for every list of up to five
/// items from `1`, `2` and `9`. No record is a pair, so a list is in such a step exactly when it
/// is in its rows; the check reads the rows and leaves the records out (proof at `verify_step`).
/// Negative control: `verify_step` refusing a step with records (`(_, true) => return None` on
/// its `step_shape`, as `find_prefix_chains` does) passes no list of one item or more through
/// these steps, and this test fails; so does reading one row beside records as no step, as
/// `verify_step` did before (`rows.len() < 2`).
#[test]
fn the_check_of_a_list_witness_is_membership_beside_records() {
    use super::super::rec::Expr;
    use fork_inputs::{cons, lit, nil, r};
    let ty = |t: Type| Expr::Type(t);
    let int = || ty(Type::int());
    let records = || {
        ty(Type::atom_with(
            "cons",
            &Type::universe(crate::types::Universe::Struct),
        ))
    };
    let systems: Vec<(&str, Vec<Expr>)> = vec![
        (
            "records at the root, two rows beside records, one row beside records on a cycle",
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1)), records()]),
                Expr::Union(vec![
                    nil(),
                    cons(ty(lit(1)), r(2)),
                    cons(ty(lit(9)), r(3)),
                    records(),
                ]),
                Expr::Union(vec![nil(), cons(ty(lit(2)), r(0)), records()]),
                Expr::Union(vec![nil(), cons(ty(lit(9)), r(3))]),
            ],
        ),
        (
            "a chain of one row beside records, an exit of 9 into a loop of 2",
            vec![
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(1)), records()]),
                Expr::Union(vec![
                    nil(),
                    cons(int(), r(2)),
                    cons(ty(lit(9)), r(3)),
                    records(),
                ]),
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(0)), records()]),
                Expr::Union(vec![nil(), cons(ty(lit(2)), r(3))]),
            ],
        ),
        (
            "a self-looping tail beside records",
            vec![
                Expr::Union(vec![nil(), cons(ty(lit(1)), r(1))]),
                Expr::Union(vec![nil(), cons(int(), r(1)), records()]),
            ],
        ),
    ];
    assert_check_is_membership(systems);
}

/// For each system (its definitions, `W0` first), asserts that the check of a list witness
/// (`Searching::check_chain_witness`) on `W0` is membership (`Type::contains`) for every list of
/// up to five items from `1`, `2` and `9`, and that some lists are in `W0` and some are not.
/// Then, for each list and each k, the check with its k-th test of a member answering "not
/// known" (the test-only `Search::unknown_in`) passes no list outside `W0`, and refuses some
/// list inside: the refusals of the check on an unknown member (TEST-kernel-unreached-paths-12).
fn assert_check_is_membership(systems: Vec<(&str, Vec<super::super::rec::Expr>)>) {
    use super::super::rec::Group;
    use fork_inputs::def;
    let mut lists: Vec<Vec<i64>> = vec![vec![]];
    for k in 0..5 {
        let longer: Vec<Vec<i64>> = (lists.iter())
            .filter(|l| l.len() == k)
            .flat_map(|l| [1, 2, 9].map(|x| [l.clone(), vec![x]].concat()))
            .collect();
        lists.extend(longer);
    }
    let mut unknown_refused = 0;
    for (name, bodies) in systems {
        let defs = (bodies.into_iter().enumerate())
            .map(|(k, b)| def(&format!("W{k}"), b))
            .collect();
        let t = Group::new(defs)
            .expect("a group")
            .instance(vec![])
            .remove(0);
        let (mut inside, mut outside) = (0, 0);
        for l in &lists {
            Type::forget_emptiness();
            let value = (l.iter().rev()).fold(Value::atom("nil"), |rest, &x| {
                Value::atom_with("cons", vec![Value::Int(x), rest])
            });
            let (t2, items) = (t.clone(), l.clone());
            let ok = Search::default().run(move |d| {
                Box::pin(async move {
                    // Each value is shown once, so equal items share one id and form runs.
                    let mut shown: BTreeMap<i64, usize> = BTreeMap::new();
                    let ids: Vec<usize> = (items.iter())
                        .map(|&x| {
                            *(shown.entry(x))
                                .or_insert_with(|| d.s().show(Rep::Value(Value::Int(x))))
                        })
                        .collect();
                    let (link, stop) = ("cons".into(), "nil".into());
                    d.check_chain_witness(&t2, &link, &ids, &stop, &[]).await
                })
            });
            let member = t.contains(&value);
            assert_eq!(ok, member, "{name}: {l:?}, check {ok}, member {member}");
            if member {
                inside += 1;
            } else {
                outside += 1;
            }
            // The same check with the k-th test of a member answering "not known", for each k
            // the check reaches: it may then refuse the list, and never passes one outside.
            for k in 0.. {
                Type::forget_emptiness();
                let (t2, items) = (t.clone(), l.clone());
                let (ok, fired) = Search::default().run(move |d| {
                    Box::pin(async move {
                        d.s().unknown_in = Some(k);
                        // Equal items share one id, as above, so that they form runs.
                        let mut shown: BTreeMap<i64, usize> = BTreeMap::new();
                        let ids: Vec<usize> = (items.iter())
                            .map(|&x| {
                                *(shown.entry(x))
                                    .or_insert_with(|| d.s().show(Rep::Value(Value::Int(x))))
                            })
                            .collect();
                        let (link, stop) = ("cons".into(), "nil".into());
                        let ok = d.check_chain_witness(&t2, &link, &ids, &stop, &[]).await;
                        (ok, d.s().unknown_in.is_none())
                    })
                });
                assert!(
                    !ok || member,
                    "{name}: {l:?} with test {k} unknown, check passes"
                );
                unknown_refused += usize::from(member && !ok);
                if !fired {
                    break;
                }
            }
        }
        assert!(inside > 0 && outside > 0, "{name}: lists on both sides");
    }
    assert!(
        unknown_refused > 0,
        "some list refused on an unknown member"
    );
}

/// Item KERNEL-verify-step-self-loop-tail: a chain of tails ending in a tail that loops on
/// itself (`Wn = nil | cons(h, Wn)`) with exits into a loop `L` of another item leaves, at the
/// tail before `Wn`, rows whose tails loop on themselves with two different items; the check of
/// a list witness (`Searching::check_chain_witness`) reads the rows of one item as the chain and
/// the others as the exit, the heads of rows with one tail joined (also two loop items with two
/// rows each, and two rows into one tail that does not loop), and its answer is membership
/// (`Type::contains`), both ways, for every list of up to five items from `1`, `2` and `9`.
/// Before, `verify_step` gave up on these tails and the check passed no list through them.
/// Negative controls: tails of three loop items, of two loop items beside a row that does not
/// loop, or of two rows into two tails neither of which loops, have no reading as one chain and
/// one exit, and the check still passes no list of two items or more through them (while some
/// are in the type).
#[test]
fn the_check_of_a_list_witness_reads_a_chain_ending_in_a_self_looping_tail() {
    use super::super::rec::{Expr, Group};
    use fork_inputs::{cons, def, lit, nil, r};
    let ty = |t: Type| Expr::Type(t);
    let one = || ty(lit(1));
    let two = || ty(lit(2));
    let nine = || ty(lit(9));
    let int = || ty(Type::int());
    // `W0` first; `true` where the check must read every tail, `false` where it must give up.
    let systems: Vec<(&str, bool, Vec<Expr>)> = vec![
        (
            "a chain into a tail looping on 1, exits of 9 into a loop of 2",
            true,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(int(), r(2)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(one(), r(3)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(one(), r(3))]),
                Expr::Union(vec![nil(), cons(two(), r(4))]),
            ],
        ),
        (
            "alternating heads into a tail looping on int, exits of 9 into a loop of 9",
            true,
            vec![
                Expr::Union(vec![nil(), cons(one(), r(1)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(two(), r(2)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(one(), r(3)), cons(nine(), r(4))]),
                Expr::Union(vec![nil(), cons(int(), r(3))]),
                Expr::Union(vec![nil(), cons(nine(), r(4))]),
            ],
        ),
        (
            "one exit of 1 and 9 into a loop of 2, a tail looping on 9",
            true,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![
                    nil(),
                    cons(two(), r(2)),
                    cons(one(), r(3)),
                    cons(nine(), r(3)),
                ]),
                Expr::Union(vec![nil(), cons(nine(), r(2))]),
                Expr::Union(vec![nil(), cons(two(), r(3))]),
            ],
        ),
        (
            "two loop items with two rows each",
            true,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![
                    nil(),
                    cons(one(), r(2)),
                    cons(two(), r(2)),
                    cons(one(), r(3)),
                    cons(nine(), r(3)),
                ]),
                Expr::Union(vec![nil(), cons(nine(), r(2))]),
                Expr::Union(vec![nil(), cons(two(), r(3))]),
            ],
        ),
        (
            "two rows into one tail that does not loop",
            true,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), cons(one(), r(2)), cons(nine(), r(2))]),
                Expr::Union(vec![nil(), cons(two(), r(3))]),
                Expr::Union(vec![nil(), cons(int(), r(3))]),
            ],
        ),
        (
            "two tails, neither loops",
            false,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![nil(), cons(one(), r(2)), cons(nine(), r(3))]),
                Expr::Union(vec![nil(), cons(two(), r(3))]),
                Expr::Union(vec![nil(), cons(int(), nil())]),
            ],
        ),
        (
            "three loop items",
            false,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![
                    nil(),
                    cons(one(), r(2)),
                    cons(nine(), r(3)),
                    cons(two(), r(4)),
                ]),
                Expr::Union(vec![nil(), cons(int(), r(2))]),
                Expr::Union(vec![nil(), cons(nine(), r(3))]),
                Expr::Union(vec![nil(), cons(two(), r(4))]),
            ],
        ),
        (
            "two loop items beside a row that does not loop",
            false,
            vec![
                Expr::Union(vec![nil(), cons(int(), r(1))]),
                Expr::Union(vec![
                    nil(),
                    cons(one(), r(2)),
                    cons(nine(), r(3)),
                    cons(two(), r(4)),
                ]),
                Expr::Union(vec![nil(), cons(int(), nil())]),
                Expr::Union(vec![nil(), cons(nine(), r(3))]),
                Expr::Union(vec![nil(), cons(two(), r(4))]),
            ],
        ),
    ];
    let mut lists: Vec<Vec<i64>> = vec![vec![]];
    for k in 0..5 {
        let longer: Vec<Vec<i64>> = (lists.iter())
            .filter(|l| l.len() == k)
            .flat_map(|l| [1, 2, 9].map(|x| [l.clone(), vec![x]].concat()))
            .collect();
        lists.extend(longer);
    }
    for (name, read, bodies) in systems {
        let defs = (bodies.into_iter().enumerate())
            .map(|(k, b)| def(&format!("W{k}"), b))
            .collect();
        let t = Group::new(defs)
            .expect("a group")
            .instance(vec![])
            .remove(0);
        let (mut inside, mut outside) = (0, 0);
        for l in &lists {
            Type::forget_emptiness();
            let value = (l.iter().rev()).fold(Value::atom("nil"), |rest, &x| {
                Value::atom_with("cons", vec![Value::Int(x), rest])
            });
            let (t2, items) = (t.clone(), l.clone());
            let ok = Search::default().run(move |d| {
                Box::pin(async move {
                    // Each value is shown once, so equal items share one id and form runs.
                    let mut shown: BTreeMap<i64, usize> = BTreeMap::new();
                    let ids: Vec<usize> = (items.iter())
                        .map(|&x| {
                            *(shown.entry(x))
                                .or_insert_with(|| d.s().show(Rep::Value(Value::Int(x))))
                        })
                        .collect();
                    let (link, stop) = ("cons".into(), "nil".into());
                    d.check_chain_witness(&t2, &link, &ids, &stop, &[]).await
                })
            });
            let member = t.contains(&value);
            if read || l.len() < 2 {
                assert_eq!(ok, member, "{name}: {l:?}, check {ok}, member {member}");
            } else {
                assert!(!ok, "{name}: {l:?} passed through a tail with no reading");
            }
            if l.len() >= 2 {
                if member {
                    inside += 1;
                } else {
                    outside += 1;
                }
            }
        }
        assert!(
            inside > 0 && outside > 0,
            "{name}: lists of two items or more on both sides"
        );
    }
}

/// The list type `W0` of `n + 1` definitions `Wk = nil | cons(Hk, W(k+1))` for `k < n` and
/// `Wn = nil | cons(int, Wn)`, where `Hk` is `2` at `k = special`, `1` at other odd `k` and
/// `int` at even `k`: its rest after the first item passes `n - 1` tails before the cycle `Wn`,
/// and its heads alternate, so the check of a list witness (`Searching::check_chain_witness`)
/// crosses them by binary lifting and not by its runs of equal links (DRY-empty-lift-levels).
pub(super) fn long_chain(n: usize, special: usize) -> Type {
    use super::super::rec::{Expr, Group};
    use fork_inputs::{cons, def, lit, nil, r};
    let head = |k: usize| match k {
        _ if k == special => lit(2),
        _ if k % 2 == 1 => lit(1),
        _ => Type::int(),
    };
    let defs = (0..=n)
        .map(|k| {
            let link = if k == n {
                cons(Expr::Type(Type::int()), r(n))
            } else {
                cons(Expr::Type(head(k)), r(k + 1))
            };
            def(&format!("W{k}"), Expr::Union(vec![nil(), link]))
        })
        .collect();
    Group::new(defs)
        .expect("a group")
        .instance(vec![])
        .remove(0)
}

/// The answers of the check of a list witness on [`long_chain`] at `n` with `special` odd: the
/// list of `n + 4` ones is outside the type (its item `special` is not 2), and the same list
/// with a 2 at `special` is in it, with no hint, and with each hint `Miss(special)`,
/// `Miss(special + 1)` and `Len` on the type's one row, which must not change the answer. A
/// hint `Miss(special)` reaches item `special` by one jump of `special - 1` links. Returns the
/// four answers of each list, `false` expected for the first and `true` for the second.
pub(super) fn long_chain_answers(t: &Type, n: usize, special: usize) -> [[bool; 4]; 2] {
    [false, true]
        .map(|in_type| [0, 1, 2, 3].map(|hint| long_chain_check(t, n, special, in_type, hint)))
}

/// One answer of [`long_chain_answers`]: for the list of ones (`in_type` false) or the list
/// with a 2 at `special` (`in_type` true), under hint `hint` of none, `Miss(special)`,
/// `Miss(special + 1)` and `Len`, in that order. Each answer is decided afresh.
pub(super) fn long_chain_check(
    t: &Type,
    n: usize,
    special: usize,
    in_type: bool,
    hint: usize,
) -> bool {
    let rows = (t.p().atoms.names().get("cons"))
        .and_then(|a| a.payload.p().tuples.lens.get(&2)?.union_rows())
        .expect("one row of pairs");
    let row = rows[0].clone();
    let hints = match hint {
        0 => vec![],
        1 => vec![(row, ChainHint::Miss(special))],
        2 => vec![(row, ChainHint::Miss(special + 1))],
        _ => vec![(row, ChainHint::Len)],
    };
    Type::forget_emptiness();
    let t = t.clone();
    Search::default().run(move |d| {
        Box::pin(async move {
            let one = d.s().show(Rep::Value(Value::Int(1.into())));
            let two = d.s().show(Rep::Value(Value::Int(2.into())));
            let mut ids = vec![one; n + 4];
            if in_type {
                ids[special] = two;
            }
            let (link, stop) = ("cons".into(), "nil".into());
            d.check_chain_witness(&t, &link, &ids, &stop, &hints).await
        })
    })
}

/// Item DRY-empty-lift-levels: the check of a list witness jumps along a chain of tails by the
/// shared binary lifting (`zed_graph::Lift`), with levels sized from the longest jump. On
/// [`long_chain`] at each `n` up to 40 and each odd `special` below it, the jump to item
/// `special` lands on the tail whose head is 2, and the other jumps on the right tails too: the
/// list of ones is outside, and the list with a 2 there is in, whatever the hint. A chain past
/// `2^18` links, where the fixed 18 levels this replaced ran out, is in the benchmark module
/// (`bench::a_list_witness_jumps_more_than_2_to_the_18_tails_at_once`), as is the scaling check
/// `bench::a_list_witness_jumps_a_long_chain_of_tails_in_log_time`. Negative controls, run: a
/// jump one link short (`tree.depth(u) - k + 1`) fails it at `n 2, special 1`, the list with a
/// 2 refused under the hint `Miss(2)`; a jump that drops its highest bit fails it at `n 4,
/// special 3`, both answers wrong with no hint.
#[test]
fn a_list_witness_jumps_a_chain_of_tails_to_the_right_tail() {
    for n in 2..=40 {
        for special in (1..n).step_by(2) {
            let t = long_chain(n, special);
            assert_eq!(
                long_chain_answers(&t, n, special),
                [[false; 4], [true; 4]],
                "n {n}, special {special}"
            );
        }
    }
}

/// A meet of a morphism type every value takes with a union of morphism types gives a closure
/// for each arm, met with the type taken (`Searching::find_rep`). When an arm's keys are not
/// permitted as written, the closure is built only if it is never called: its own keys and
/// the keys of the type taken, asked once for all arms (`shared_none`), are both proved empty.
/// Here every key is a pair whose first component is an empty recursive type (`E = cons(int,
/// E)`), so the shared keys `(E1, int)` are not known empty until the search proves them so,
/// and the type has a closure, which is never called. Before TEST-kernel-unreached-paths-10
/// only the searches of some runs asked the shared keys there; this test asks them in every
/// run. Negative control: the shared keys answered as not empty leave the closure unbuilt and
/// the type refused (`Refusal::NoWitness`).
#[test]
fn a_closure_of_a_meet_with_a_union_is_built_when_the_shared_keys_are_proved_empty() {
    use super::super::rec::{Expr, Group};
    use fork_inputs::{cons, def, r};
    let int = || Expr::Type(Type::int());
    let g = Group::new(vec![
        def("E1", cons(int(), r(0))),
        def("E2", cons(int(), r(1))),
        def("E3", cons(int(), r(2))),
    ])
    .expect("a group")
    .instance(vec![]);
    let m = |k: &Type, v: Type| {
        Type::morphism(Type::tuple(vec![k.clone(), Type::int()]), Type::int(), v)
    };
    let t = &m(&g[0], Type::int()) & &(&m(&g[1], Type::int()) | &m(&g[2], Type::string()));
    assert_eq!(t.verdict(), Verdict::Inhabited, "{t}");
}

/// A meet of morphism types, every one taken, gives one closure of their meet
/// (`Searching::find_rep`): the promised keys joined, the permitted keys and the values met.
/// Where both sides of a join or meet are one recursive type, that type is kept as written,
/// since `cut` would give its unfolding, a type compared as different from it. Here
/// `L = nil | cons(int, L)` and the type is `(L -> int) & (L -> int | bool)`, both exact, so the
/// closure has the keys `L` promised and permitted. Before TEST-kernel-unreached-paths-11 only
/// some runs built such a closure. The verdicts do not show these lines: with each of the
/// controls below every verdict here is unchanged, since a closure is built only for a type
/// already found inhabited. The closure built shows them. Negative controls, each failing this
/// test: `Type::empty()` in place of the kept guarantee (`x.clone()` in `join`), a closure that
/// promises no key, a value of `L ->? int` and not of the type; `Type::top()` in place of the
/// kept permission (`x.clone()` in `both`), a closure that permits every key; and the shortcut
/// off (`cut` taken for every pair), which gives the unfolding of `L` in place of `L`.
#[test]
fn a_meet_of_morphism_types_with_one_recursive_key_type_keeps_it_as_written() {
    use fork_inputs::list;
    let l = list(Type::int());
    let ib = &Type::int() | &Type::bool();
    let t = &Type::exact(l.clone(), Type::int()) & &Type::exact(l.clone(), ib.clone());
    assert_eq!(t.verdict(), Verdict::Inhabited, "{t}");
    let mut s = Search {
        strict: true,
        refuse_forks: true,
        trials: Some(0),
        ..Search::default()
    };
    s.swept.insert(t.clone(), None);
    s.solve(&t);
    assert_eq!(s.refused, None, "{t}: nothing refused");
    let r = s.rep(&t).expect("the type has a closure");
    let Rep::Closure(m) = &s.shown[r] else {
        panic!("{t}: the value shown is not a closure");
    };
    assert_eq!(m.guarantee, l, "{t}: the keys promised are L as written");
    assert_eq!(m.permission, l, "{t}: the keys permitted are L as written");
    // Where the values differ the meet is `cut`; `int` here.
    assert!(
        m.value.subtype(&Type::int()) && Type::int().subtype(&m.value),
        "{t}"
    );
    // One recursive type in the values alone (`v`) and a meet whose values are disjoint.
    let v = &Type::morphism(Type::int(), Type::int(), l.clone())
        & &Type::morphism(Type::int(), ib.clone(), l.clone());
    assert_eq!(v.verdict(), Verdict::Inhabited, "{v}");
    let none = &Type::exact(l.clone(), Type::int()) & &Type::exact(l.clone(), Type::bool());
    assert_eq!(none.verdict(), Verdict::Empty, "{none}");
}

/// `fields` reads a payload diagram shared by several atoms once (`Rows`): each atom pushes the
/// groups of components whose names it does not have, and keeps the rest unpushed for the next
/// atom. With `#x`, `#y` and `#z` over one payload whose rows hold `#x(int)`, `#y(int)` and
/// `#z(int)`, the first two atoms read leave no group unpushed, so the third finds the list
/// empty and pushes nothing; every component is still a field, once. Before
/// TEST-kernel-unreached-paths-10 only the searches of some runs met an empty list there; this
/// test meets it in every run, whichever order the atoms are read in. Negative control: a group
/// matched by the atom read first and not kept unpushed is never pushed, and one component is
/// missing.
#[test]
fn a_payload_shared_by_three_atoms_gives_each_component_once() {
    let tag = |n: &str, t: Type| Type::atom_with(n, &Type::tuple(vec![t]));
    let b = &(&Type::tuple(vec![tag("x", Type::int())])
        | &Type::tuple(vec![tag("y", Type::int())]))
        | &Type::tuple(vec![tag("z", Type::int())]);
    let t = &(&Type::atom_with("x", &b) | &Type::atom_with("y", &b)) | &Type::atom_with("z", &b);
    let (out, wraps, items) = fields(std::slice::from_ref(&t));
    let got: BTreeSet<String> = out.iter().map(|t| t.to_string()).collect();
    let want: BTreeSet<String> = [t.to_string(), Type::int().to_string()]
        .into_iter()
        .chain(["x", "y", "z"].map(|n| tag(n, Type::int()).to_string()))
        .collect();
    assert_eq!(got, want);
    assert_eq!(out.len(), want.len(), "each type once");
    let wraps: BTreeSet<String> = wraps.iter().map(|t| t.to_string()).collect();
    let want: BTreeSet<String> = ["x", "y", "z"]
        .map(|n| tag(n, Type::int()).to_string())
        .into();
    assert_eq!(wraps, want);
    assert!(items.is_empty());
}

/// The numbers of a search's types ([`Ids`]): a type numbered again keeps one entry with its
/// new number, a type not held is removed as a no-op, and the last type of a digest removed
/// leaves no list behind (TEST-kernel-unreached-paths-12). Negative control: `insert` pushing
/// where a key is held leaves the old number found first.
#[test]
fn a_type_numbered_again_keeps_one_entry_and_a_type_not_held_is_not_removed() {
    let (t, u) = (Type::int(), Type::atom("q"));
    let mut ids = Ids::default();
    ids.insert(t.clone(), 1);
    ids.insert(t.clone(), 2);
    assert_eq!(ids.get(&t), Some(&2));
    assert_eq!(ids.0[&t.digest()].len(), 1, "one entry for the type");
    ids.remove(&u);
    assert_eq!(
        ids.get(&t),
        Some(&2),
        "removing a type not held keeps the others"
    );
    ids.remove(&t);
    assert_eq!(ids.get(&t), None);
    assert!(ids.0.is_empty(), "no list left for the digest");
}

/// A type that is not a recursive member is not refused by a group decider, whatever it
/// holds (`Type::refused_by_group`); and the roots of carriers put the types that are not
/// recursive first (`carrier_root_order`), whatever their order among the members
/// (TEST-kernel-unreached-paths-12).
#[test]
fn types_that_are_not_recursive_are_not_refused_by_a_group_and_come_first_among_roots() {
    let list = fork_inputs::list(Type::int());
    for t in [
        Type::int(),
        Type::atom("nil"),
        &Type::atom("nil") | &Type::int(),
    ] {
        assert!(!t.refused_by_group(), "{t}");
    }
    assert!(matches!(&*list.0, Node::Rec(_)));
    assert_eq!(carrier_root_order(&[list.clone(), Type::int()]), [1, 0]);
    assert_eq!(carrier_root_order(&[Type::int(), list]), [0, 1]);
}

/// The key value of a value ([`leaf`]): the last value along first components and atom
/// tuple payloads; the empty tuple for an atom of an empty payload; none for an atom with a
/// struct payload, a path or a family (TEST-kernel-unreached-paths-12).
#[test]
fn the_leaf_of_a_value_follows_first_components_and_stops_at_records_and_paths() {
    let one = Value::Int(1);
    let nested = Value::tuple(vec![Value::atom_with(
        "a",
        vec![one.clone(), Value::Int(2)],
    )]);
    assert_eq!(leaf(&nested), Some(one.clone()));
    assert_eq!(leaf(&Value::atom("b")), Some(Value::atom("b")));
    assert_eq!(
        leaf(&Value::atom_with("c", vec![])),
        Some(Value::tuple(Vec::new()))
    );
    assert_eq!(
        leaf(&Value::tuple(Vec::new())),
        Some(Value::tuple(Vec::new()))
    );
    let record = Value::atom_named("d", vec![("x".into(), one.clone())]).expect("a record");
    assert_eq!(leaf(&record), None);
    assert_eq!(leaf(&Value::tuple(vec![record])), None);
    assert_eq!(leaf(&Value::path(vec![one.clone()])), None);
    let family = Value::merge_failures([Value::atom("e"), Value::atom("f")]);
    let Value::Atom(a) = &family else {
        panic!("an atom")
    };
    let inner = a.payload.as_ref().expect("a payload").as_slice()[0].clone();
    assert!(matches!(inner, Value::Family(_)));
    assert_eq!(leaf(&inner), None);
}
