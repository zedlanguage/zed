//! The call node `Formula::Holes` (LOAD-call-disj-spread, design-b22-load5.md section 2, META3
//! H5-H7): its set of holes against a list of integers, its order and hash by content, the
//! constant folding of H6, and the solver's answer on a node through the generic route checked
//! against the node's clauses written out.

use super::extend::counts;
use super::*;

fn y(s: &str) -> Lin {
    Lin::atom(Atom::Sym(s.into()))
}

fn k(v: i128) -> Lin {
    Lin::constant(v)
}

fn set(runs: &[(i128, i128)]) -> Shared<HoleSet> {
    HoleSet::of(
        runs.iter()
            .map(|&(l, h)| (Int::from(l), Int::from(h)))
            .collect(),
    )
}

/// The node's clauses written by hand, one a hole: `t <= lo - 1 || t >= hi + 1`.
fn written(runs: &[(i128, i128)], t: &Lin) -> Formula {
    Formula::and(
        (runs.iter())
            .filter(|(l, h)| l <= h)
            .map(|&(l, h)| {
                Formula::or(vec![
                    Formula::Con(Con::ge(&k(l - 1), t)),
                    Formula::Con(Con::ge(t, &k(h + 1))),
                ])
            })
            .collect(),
    )
}

fn leaves(f: &Formula) -> usize {
    match f {
        Formula::Holes(_) => 1,
        Formula::Con(_) => 0,
        Formula::Not(g) => leaves(g),
        Formula::And(gs) | Formula::Or(gs) => gs.iter().map(leaves).sum(),
    }
}

/// A small generator, so the runs are the same on every run of the tests.
fn next(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *seed >> 33
}

#[test]
fn a_set_of_holes_merges_its_runs_and_finds_each_member() {
    let mut seed = 7u64;
    for _ in 0..300 {
        let n = (next(&mut seed) % 6) as usize;
        let runs: Vec<(i128, i128)> = (0..n)
            .map(|_| {
                let lo = (next(&mut seed) % 40) as i128 - 20;
                (lo, lo + (next(&mut seed) % 6) as i128 - 1)
            })
            .collect();
        let s = set(&runs);
        // Sorted, disjoint, and not touching.
        for w in s.runs().windows(2) {
            assert!(&w[0].1 + &Int::from(1) < w[1].0, "{runs:?}: {:?}", s.runs());
        }
        for v in -25i128..25 {
            let member = runs.iter().any(|&(l, h)| l <= v && v <= h);
            assert_eq!(s.run_of(&Int::from(v)).is_some(), member, "{runs:?} at {v}");
        }
    }
}

#[test]
fn a_call_on_a_constant_is_decided_by_membership() {
    // META3 H6: a fixed value outside the holes holds, one inside fails.
    let s = set(&[(0, 0), (5, 9)]);
    for v in -2i128..12 {
        let member = v == 0 || (5..=9).contains(&v);
        let f = Formula::outside(&s, k(v));
        assert!(!matches!(f, Formula::Holes(_)));
        assert_eq!(f.holds(&Model::new()), !member, "at {v}");
    }
    // No holes: `true` for every term.
    assert_eq!(Formula::outside(&set(&[]), y("x")), Formula::top());
}

#[test]
fn a_fixed_value_in_a_hole_is_empty() {
    // META3 H6, the control: `x = 0 && outside({0}, x)` has no point, and `x = 1 && ...` has.
    let s = set(&[(0, 0)]);
    let at = |v: i128| {
        Formula::and(vec![
            Formula::Con(Con::eq(&y("x"), &k(v))),
            Formula::outside(&s, y("x")),
        ])
    };
    assert_eq!(satisfiable(&at(0)).expect("decided"), None);
    let m = satisfiable(&at(1)).expect("decided").expect("a point");
    assert_eq!(m.get(&Atom::Sym("x".into())), Some(&Int::from(1)));
}

#[test]
fn two_calls_of_one_callee_are_two_leaves() {
    // design section 2, G7: `h(x: x) && h(x: x + 1)` keeps one node a call, sharing one set.
    let s = set(&[(0, 3), (10, 12)]);
    let a = Formula::outside(&s, y("x"));
    let b = Formula::outside(&s, y("x").plus(&k(1)));
    assert_ne!(a, b);
    let f = Formula::and(vec![a.clone(), b.clone(), a.clone()]);
    assert!(leaves(&f) >= 2, "{f:?}");
    // The two terms meet the holes at once: x and x + 1 both outside [0, 3] and [10, 12].
    let runs = [(0, 3), (10, 12)];
    let want = Formula::and(vec![
        written(&runs, &y("x")),
        written(&runs, &y("x").plus(&k(1))),
    ]);
    for v in -5i128..20 {
        let m = Model::from([(Atom::Sym("x".into()), Int::from(v))]);
        assert_eq!(f.holds(&m), want.holds(&m), "at {v}");
    }
}

#[test]
fn nodes_of_equal_content_are_equal_and_hash_alike() {
    // META3 H5: two sets built apart with the same runs give equal nodes, whatever was built
    // first; the order is by content and not by id.
    let (s1, s2) = (set(&[(1, 2), (4, 4)]), set(&[(4, 4), (1, 1), (2, 2)]));
    let (a, b) = (Formula::outside(&s1, y("x")), Formula::outside(&s2, y("x")));
    assert_eq!(a, b);
    assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal);
    use std::hash::{Hash, Hasher};
    let hash = |f: &Formula| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        f.hash(&mut h);
        h.finish()
    };
    assert_eq!(hash(&a), hash(&b));
    // Built in the other order, the two sets still compare the same way against a third.
    let c = Formula::outside(&set(&[(1, 2), (5, 5)]), y("x"));
    let (s3, s4) = (set(&[(4, 4), (1, 2)]), set(&[(1, 2), (5, 5)]));
    let (a2, c2) = (Formula::outside(&s3, y("x")), Formula::outside(&s4, y("x")));
    assert_eq!(a.cmp(&c), a2.cmp(&c2));
    assert_ne!(a.cmp(&c), std::cmp::Ordering::Equal);
    // A node and its clauses written out are different formulas.
    assert_ne!(a, written(&[(1, 2), (4, 4)], &y("x")));
}

#[test]
fn the_solver_reads_a_node_as_its_clauses() {
    // The generic route (META3 H7): each answer on random boxes and holes is the answer on the
    // clauses written out, and the node is written once and counted.
    let mut seed = 11u64;
    for i in 0..120 {
        let n = 1 + (next(&mut seed) % 4) as usize;
        let runs: Vec<(i128, i128)> = (0..n)
            .map(|_| {
                let lo = (next(&mut seed) % 16) as i128 - 4;
                (lo, lo + (next(&mut seed) % 4) as i128)
            })
            .collect();
        let (lo, hi) = (
            (next(&mut seed) % 8) as i128 - 2,
            (next(&mut seed) % 14) as i128,
        );
        let t = y("x").plus(&y("z"));
        let bx = vec![
            Formula::Con(Con::ge(&y("x"), &k(lo))),
            Formula::Con(Con::ge(&k(hi), &y("x"))),
            Formula::Con(Con::ge(&y("z"), &k(0))),
            Formula::Con(Con::ge(&k(1), &y("z"))),
        ];
        let node = Formula::outside(&set(&runs), t.clone());
        let mut with_node = bx.clone();
        with_node.push(node);
        let mut with_clauses = bx;
        with_clauses.push(written(&runs, &t));
        counts::take();
        let got = satisfiable(&Formula::and(with_node)).expect("decided");
        let lowered = counts::take()[counts::HOLES_LOWERED];
        let want = satisfiable(&Formula::and(with_clauses)).expect("decided");
        assert_eq!(
            got.is_some(),
            want.is_some(),
            "case {i}: {runs:?} in [{lo}, {hi}]"
        );
        if let Some(m) = &got {
            let at = |s: &str| m.get(&Atom::Sym(s.into())).cloned().unwrap_or(Int::ZERO);
            let v = &at("x") + &at("z");
            assert!(
                !runs
                    .iter()
                    .any(|&(l, h)| Int::from(l) <= v && v <= Int::from(h)),
                "{i}"
            );
        }
        assert!(lowered <= 1, "case {i}: written {lowered} times");
    }
}

#[test]
fn a_node_is_shown_as_its_clauses() {
    // Printed formulas are syntax: the node is written as its clauses, with parentheses where
    // its parent needs them.
    let one = Formula::outside(&set(&[(0, 0)]), y("x"));
    let two = Formula::outside(&set(&[(0, 0), (5, 6)]), y("x"));
    let c = Formula::Con(Con::ge(&y("x"), &k(-3)));
    for f in [
        one.clone(),
        two.clone(),
        Formula::and(vec![c.clone(), one.clone()]),
        Formula::or(vec![c.clone(), two.clone()]),
        Formula::negate(one.clone()),
    ] {
        // The same formula with each node replaced by its clauses (`map_cons` writes them).
        let out = f.map_cons(&|c| Formula::Con(c.clone()));
        assert_eq!(leaves(&out), 0);
        assert_eq!(f.to_string(), out.to_string());
    }
    // One hole beside a constraint: the disjunction in parentheses.
    let (below, above) = (Con::ge(&k(-1), &y("x")), Con::ge(&y("x"), &k(1)));
    let text = Formula::and(vec![c.clone(), one]).to_string();
    assert!(
        text.ends_with(&format!(
            " && ({} || {})",
            Formula::Con(below),
            Formula::Con(above)
        )),
        "{text}"
    );
}

#[test]
fn nodes_beside_a_part_read_twice_are_compared_by_content() {
    // The order of two formulas reads the rest of a level by its parse (`deep::canon`) once a
    // shared part is met a second time. The parse read every call node as one symbol, so two
    // conjunctions that differ only in their nodes compared equal (wildcard-arm audit,
    // b22-load10 step 0). `p`, `q` and `r` are three equal conjunctions built apart, each
    // shared: the pair (p, q) is entered, and the pair (p, r) meets `p` again.
    let part = || {
        Formula::And(Shared::new(vec![
            Formula::Con(Con::ge(&y("x"), &k(0))),
            Formula::Con(Con::ge(&y("z"), &k(0))),
        ]))
    };
    let (p, q, r) = (part(), part(), part());
    let ha = Formula::outside(&set(&[(0, 3)]), y("x"));
    let hb = Formula::outside(&set(&[(5, 9)]), y("x"));
    let a = Formula::And(Shared::new(vec![p.clone(), p.clone(), ha.clone()]));
    let b = Formula::And(Shared::new(vec![q.clone(), r.clone(), hb.clone()]));
    assert_eq!(a.cmp(&b), ha.cmp(&hb), "{a:?} against {b:?}");
    assert_eq!(b.cmp(&a), hb.cmp(&ha));
    assert_ne!(a, b);
    // Equal nodes built apart still compare equal on that path.
    let hc = Formula::outside(&set(&[(0, 3)]), y("x"));
    let c = Formula::And(Shared::new(vec![q.clone(), r.clone(), hc]));
    assert_eq!(a.cmp(&c), std::cmp::Ordering::Equal);
    assert_eq!(a, c);
}
