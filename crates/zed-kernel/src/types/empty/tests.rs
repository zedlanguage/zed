use super::*;

/// The region of the part `f` on the box `r`, made by a search of its own.
fn region(r: Vec<Type>, f: &Part<Row>) -> Region {
    let f = f.clone();
    Search::default().run(move |d| Box::pin(async move { d.region(r, &f).await }))
}

/// The classes of `overlaps` on everyday types: a finite set and a cofinite one are joined
/// exactly when they meet, at the top and inside an atom payload; two types of one atom
/// name or tuple length are apart when they are disjoint inside it, a payload of a payload
/// too; two tuples that share a first component are joined even when they are disjoint
/// (the tradeoff at `overlaps`).
#[test]
fn classes_are_exact_on_cofinite_sets_names_and_lengths_and_join_tuples_by_first_component() {
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
        Type::tuple(vec![lit(1), lit(2)]), // 10, disjoint from 11 and joined with it
        Type::tuple(vec![lit(1), lit(3)]), // 11
        Type::atom_with("b", &one(Type::atom_with("c", &one(lit(1))))), // 12, apart from 13
        Type::atom_with("b", &one(Type::atom_with("c", &one(lit(2))))), // 13
        Type::atom_with("a", &one(&Type::int() - &lit(1))), // 14, meets 4, not 3
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
        vec![10, 11],
        vec![12],
        vec![13],
    ];
    assert_eq!(classes, expected);
}

/// The other two cases of the tradeoff at `overlaps`. A tuple part outside its tuple types,
/// `(int,) \ (1,)`, holds every one-tuple, so it is joined with `(1,)` although the two are
/// disjoint. A type met at two nodes inside one type, the `1` of `(1,) | #e((1,))`, merges
/// the two nodes, so `(2,)` and `#e((2,))` are joined although they are disjoint; `(3,)`
/// stays apart, and so do the classes of disjoint types under the merged node. The classes
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
/// every choice of at most two classes of `all` and three of `none` with periods 1 to 6,
/// from a fixed sequence: a length it gives is in every class of `all` and in none of
/// `none`; it gives one whenever the shares of `none` sum to less than one; and it gives one
/// only when the scan finds one.
#[test]
fn the_residue_length_agrees_with_a_scan() {
    for m in 1..40u64 {
        for a in 0..m {
            let found = inverse(a, m);
            let scanned = (0..m).find(|&x| a * x % m == 1 % m);
            assert_eq!(found, scanned, "the inverse of {a} modulo {m}");
        }
    }
    let mut seed = 7u64;
    let mut next = |below: u64| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) % below
    };
    let (mut exists, mut given) = (0, 0);
    for _ in 0..20_000 {
        let (a, b) = (next(3), next(4));
        let mut classes: Vec<(u64, u64)> = (0..a + b)
            .map(|_| {
                let p = 1 + next(6);
                (p, next(p))
            })
            .collect();
        let none = classes.split_off(a as usize);
        let all = classes;
        let fits = |n: u64| {
            all.iter().all(|&(p, at)| n % p == at) && none.iter().all(|&(p, at)| n % p != at)
        };
        // Every class repeats within the lcm of the periods, at most 60.
        let scanned = (1..=60).find(|&n| fits(n));
        let found = residue_length(&all, &none);
        if let Some(n) = &found {
            let n = u64::try_from(n).expect("below the lcm");
            assert!(n >= 1 && fits(n), "{all:?} {none:?}: {n}");
        }
        assert!(found.is_none() || scanned.is_some(), "{all:?} {none:?}");
        let sum: f64 = none
            .iter()
            .filter(|&&(p, at)| (1..=60).any(|n| fits_all(&all, n) && n % p == at))
            .map(|&(p, _)| {
                let l = all.iter().fold(1, |l, &(q, _)| l / gcd(l, q) * q);
                gcd(l, p) as f64 / p as f64
            })
            .sum();
        if sum < 1.0 && scanned.is_some() {
            assert!(found.is_some(), "{all:?} {none:?}: shares {sum}");
        }
        exists += usize::from(scanned.is_some());
        given += usize::from(found.is_some());
    }
    // The choice misses a length only when the shares sum to one or more.
    assert!(given * 10 >= exists * 9, "{given} of {exists}");
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
    let mut s = 0x9e37_79b9_7f4a_7c15;
    let mut seen = [0usize; 2];
    for vars in 1..=12 {
        for _ in 0..40 {
            let cs = clauses(&mut s, vars);
            let sat = (0u64..1 << vars).any(|m| {
                let x: Vec<bool> = (0..vars).map(|v| m >> v & 1 == 1).collect();
                cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b))
            });
            let t = TwoSat {
                vars,
                clauses: cs.clone(),
                meets: HashMap::new(),
            };
            let x = t.solve();
            assert_eq!(x.is_some(), sat, "{vars} variables, {cs:?}");
            if let Some(x) = x {
                assert!(cs.iter().all(|&(a, b)| holds2(&x, a) || holds2(&x, b)));
            }
            seen[usize::from(sat)] += 1;
        }
    }
    assert!(seen[0] > 20 && seen[1] > 20, "{seen:?}");
}

/// The value the search shows for a satisfiable 2-CNF of 48 bits is a tuple of 48 bits
/// that holds every clause, read from the values shown, not from the search's own check.
#[test]
fn the_value_shown_for_a_two_cnf_holds_every_clause() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    let vars = 48;
    let mut s = 0x2545_f491_4f6c_dd1d;
    let mut shown = 0;
    for _ in 0..12 {
        let cs: Vec<(Literal2, Literal2)> = (0..vars)
            .map(|_| {
                let mut l = || next(&mut s) as usize % (2 * vars);
                (l(), l())
            })
            .collect();
        let cylinder = |l: Literal2| {
            let mut c = vec![Type::top(); vars];
            c[l / 2] = lit(i64::from(l.is_multiple_of(2)));
            Type::tuple(c)
        };
        let mut t = Type::tuple(vec![&lit(0) | &lit(1); vars]);
        for &(a, b) in &cs {
            t = &t & &(&cylinder(a) | &cylinder(b));
        }
        let sat = TwoSat {
            vars,
            clauses: cs.clone(),
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
            continue;
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
        shown += 1;
    }
    assert!(shown > 0);
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

/// k types that each reach one ring of k types with a name each, `T_j = #a_j((T_{j+1},)) | j`,
/// cost order k log k, though each reaches all k: the ring placed for a type is read only where
/// another type reaches it (the second tradeoff at `overlaps`). So do the types of the ring
/// `U_j = (#a_j((U_{j+1},)),) | j`, which all share the node of `(..,)` at the root, and the
/// ring of names beside `#a_j(any \ (0,))` for each j, whose every one-tuple under `#a_j` holds
/// every value under the rest of the ring.
#[test]
fn types_that_each_reach_a_ring_of_names_scale() {
    use super::super::rec::Expr;
    let names = |j: usize, t: Expr| Expr::Atom(format!("a{j}"), vec![t]);
    let ring_of_names = crate::scaling::inputs(64, |k| ring(k, names));
    crate::scaling::check("k types that each reach a ring of k names", 64, |k| {
        let classes = overlaps(ring_of_names[&k].iter());
        assert_eq!(classes, (0..k).map(|j| vec![j]).collect::<Vec<_>>());
    });
    let tuples = |j: usize, t: Expr| Expr::Tuple(vec![names(j, t)]);
    let tuple_ring = crate::scaling::inputs(64, |k| ring(k, tuples));
    crate::scaling::check(
        "k types that share a node and reach a ring of k names",
        64,
        |k| {
            let classes = overlaps(tuple_ring[&k].iter());
            assert_eq!(classes, (0..k).map(|j| vec![j]).collect::<Vec<_>>());
        },
    );
    let zero = Type::tuple(vec![Type::lit(&Value::Int(0)).expect("0")]);
    let beside = crate::scaling::inputs(64, |k| {
        let mut ts = ring(k, names);
        ts.extend((0..k).map(|j| Type::atom_with(&format!("a{j}"), &(&Type::top() - &zero))));
        ts
    });
    crate::scaling::check(
        "a ring of k names beside a whole under each name",
        64,
        |k| {
            let classes = overlaps(beside[&k].iter());
            assert_eq!(classes, (0..k).map(|j| vec![j, k + j]).collect::<Vec<_>>());
        },
    );
}

/// The ring of names whose members each hold a type of a lower group,
/// `T_j = #a_j((T_{j+1},)) | #b_j((int,)) | j`.
fn ring_holding_a_lower_type(k: usize) -> Vec<Type> {
    use super::super::rec::Expr;
    let int = Type::tuple(vec![Type::int()]);
    ring(k, |j, t| {
        Expr::Union(vec![
            Expr::Atom(format!("a{j}"), vec![t]),
            Expr::Type(Type::atom_with(&format!("b{j}"), &int)),
        ])
    })
}

/// k types that each reach one ring of k names whose members hold types of lower groups cost
/// order k log k: the lower types of a node of the ring are placed only when the node is read
/// (the second tradeoff at `overlaps`). The rings: each member holding `#b_j((int,))`; each
/// holding `#b((int,))`, one name for all, so every type shares the node of `#b` at the root
/// and is in one class; and each holding `#c_j((L,))` for a list type `L`, a recursive lower
/// group.
#[test]
fn types_that_each_reach_a_ring_holding_lower_types_scale() {
    use super::super::rec::{Def, Expr, Group};
    let lower = crate::scaling::inputs(64, ring_holding_a_lower_type);
    crate::scaling::check(
        "k types that each reach a ring of k names holding a lower type",
        64,
        |k| {
            let classes = overlaps(lower[&k].iter());
            assert_eq!(classes, (0..k).map(|j| vec![j]).collect::<Vec<_>>());
        },
    );
    let int = Type::tuple(vec![Type::int()]);
    let one_name = crate::scaling::inputs(64, |k| {
        ring(k, |j, t| {
            Expr::Union(vec![
                Expr::Atom(format!("a{j}"), vec![t]),
                Expr::Type(Type::atom_with("b", &int)),
            ])
        })
    });
    crate::scaling::check(
        "k types that each reach a ring of k names holding one lower type under one name",
        64,
        |k| {
            let classes = overlaps(one_name[&k].iter());
            assert_eq!(classes, vec![(0..k).collect::<Vec<_>>()]);
        },
    );
    // `L = #nil | #cons((int, L))`.
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
    let lists = crate::scaling::inputs(64, |k| {
        ring(k, |j, t| {
            Expr::Union(vec![
                Expr::Atom(format!("a{j}"), vec![t]),
                Expr::Atom(format!("c{j}"), vec![Expr::Type(list.clone())]),
            ])
        })
    });
    crate::scaling::check(
        "k types that each reach a ring of k names holding a list type",
        64,
        |k| {
            let classes = overlaps(lists[&k].iter());
            assert_eq!(classes, (0..k).map(|j| vec![j]).collect::<Vec<_>>());
        },
    );
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

/// `overlaps` on random groups whose members hold types of lower groups, recursive ones too:
/// two types whose meet is shown inhabited are in one class, and the classes are the same with
/// the types in the other order.
#[test]
fn types_that_meet_are_joined_in_random_groups_holding_lower_types() {
    let mut s = 0x2545_f491_4f6c_dd1d;
    let (mut met, mut apart) = (0, 0);
    for case in 0..400 {
        let ts = random_cells(&mut s);
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
                    met += 1;
                    assert_eq!(class[i], class[j], "case {case}: {i} and {j} meet");
                } else if class[i] != class[j] {
                    apart += 1;
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
    assert!(met > 0 && apart > 0, "{met} pairs met, {apart} apart");
}
