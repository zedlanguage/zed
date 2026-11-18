use super::*;

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
        &(&(&(&Type::with(|p| p.atoms.cofinite = true) - &Type::atom_with("a", &Type::top()))
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
    let mut seed = crate::seed::seed("the_residue_length_agrees_with_a_scan");
    let mut next = |below: u64| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) % below
    };
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
                let l = all.iter().fold(1, |l, &(q, _)| l / gcd(l, q) * q);
                gcd(l, p) as f64 / p as f64
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

/// A small generator for the tests below: xorshift.
fn next(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

/// Random clauses of one and two literals on `vars` variables.
fn clauses(s: &mut u64, vars: usize) -> Vec<(Literal2, Literal2)> {
    let m = 1 + next(s) as usize % (3 * vars);
    let lit = |s: &mut u64| next(s) as usize % (2 * vars);
    (0..m)
        .map(|_| {
            let a = lit(s);
            if next(s).is_multiple_of(3) {
                (a, a)
            } else {
                (a, lit(s))
            }
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
    let mut s =
        crate::seed::seed("two_sat_solve_agrees_with_enumeration_and_its_solutions_hold") | 1;
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

/// The value the search shows for a satisfiable 2-CNF of 48 bits is a tuple of 48 bits
/// that holds every clause, read from the values shown, not from the search's own check.
#[test]
fn the_value_shown_for_a_two_cnf_holds_every_clause() {
    let vars = 48;
    let mut s = crate::seed::seed("the_value_shown_for_a_two_cnf_holds_every_clause") | 1;
    let mut shown = 0;
    for _ in 0..12 {
        let cs: Vec<(Literal2, Literal2)> = (0..vars)
            .map(|_| {
                let mut l = || next(&mut s) as usize % (2 * vars);
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

/// A number in `0..n`, from the generator [`next`].
fn below(s: &mut u64, n: usize) -> usize {
    (next(s) >> 11) as usize % n
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
fn random_group(s: &mut u64, pool: &[Type], tag: &str) -> Option<Vec<Type>> {
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
fn random_cells(s: &mut u64) -> Vec<Type> {
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
    let mut s =
        crate::seed::seed("types_that_meet_are_joined_in_random_groups_holding_lower_types") | 1;
    let (mut met, mut apart) = (0, 0);
    for case in 0..400 {
        let ts = random_cells(&mut s);
        check_classes(case, &ts, &mut met, &mut apart);
    }
    classes_met_and_apart_built(met, apart);
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
    let mut s =
        crate::seed::seed("group_of_makes_the_groups_of_its_walk_before_the_shared_search") | 1;
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
fn random_component(s: &mut u64) -> Type {
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("a literal");
    match below(s, 5) {
        3 => Type::int(),
        4 => &Type::int() - &lit(below(s, 3)),
        i => lit(i),
    }
}

/// A random tuple type of length one to three.
fn random_tuple(s: &mut u64) -> Type {
    let m = 1 + below(s, 3);
    Type::tuple((0..m).map(|_| random_component(s)).collect())
}

/// Three to eight random types of tuples: tuple types, unions of two, one less another, and
/// every tuple less one or two tuple types.
fn random_tuples(s: &mut u64) -> Vec<Type> {
    let tuples = Type::universe(crate::types::Universe::Tuple);
    (0..3 + below(s, 6))
        .map(|_| match below(s, 6) {
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
    let mut s =
        crate::seed::seed("types_that_meet_are_joined_in_random_unions_and_negations_of_tuples")
            | 1;
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
    let mut seed =
        crate::seed::seed("a_rollback_keeps_a_reader_exactly_when_a_read_before_it_is_kept");
    let mut next = |below: usize| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) as usize % below
    };
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
            Type::with(|p| p.atoms.cofinite = true),
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
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let mut next = |k: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % k
    };
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
fn random_height_types(s: &mut u64) -> Vec<Type> {
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
    let mut s = crate::seed::seed("kept_height_bounds_agree_with_fresh_ones_across_rebuilds") | 1;
    Type::forget_emptiness();
    let mut compared = 0;
    for case in 0..150 {
        let draws = next(&mut s) | 1;
        let ts = random_height_types(&mut draws.clone());
        // Ask the kept bounds of some types first, in random order, so later ones find
        // children kept by earlier questions.
        for _ in 0..ts.len() {
            height_bounds(&ts[below(&mut s, ts.len())]);
        }
        assert_eq!(first_stale(&ts), None, "case {case}, as built");
        if below(&mut s, 3) == 0 {
            Type::forget_emptiness();
        }
        let again = random_height_types(&mut draws.clone());
        assert_eq!(again.len(), ts.len(), "case {case}: the same draws");
        assert_eq!(first_stale(&again), None, "case {case}, built again");
        compared += ts.len() + again.len();
        // Negative control: a wrong kept entry is seen.
        let k = below(&mut s, again.len());
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
