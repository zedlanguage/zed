//! Tests on names linked into one component: the blocks a relation is projected by are kept
//! as conjuncts come and go, equal to those found afresh, and a test assumed on a linked
//! component costs near its own block, not the component (COMPLEXITY.md S20).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::conjuncts::{Conjuncts, names};
use zedc::store::presburger::{Atom, Con, Formula, Lin};
use zedc::store::product::Scope;

use super::ints;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

/// `a - b >= c`.
fn ge(a: &str, b: &str, c: i64) -> Term {
    prim(Prim::Ge, prim(Prim::Sub, var(a), var(b)), int(c))
}

fn named(k: usize, p: &str) -> Vec<Arc<str>> {
    (0..k).map(|i| format!("{p}{i}").into()).collect()
}

/// The scope and the tests of each shape at size `k`, all on one linked component, each test
/// assumed on the scope the one before it gave.
fn shape(which: &str, k: usize) -> (Scope, Vec<Term>) {
    match which {
        // x0 - x1 >= 1, x1 - x2 >= 1, …: a chain.
        "chain" => {
            let n = named(k + 1, "x");
            let ts = (0..k).map(|i| ge(&n[i], &n[i + 1], 1)).collect();
            (ints(&n), ts)
        }
        // The chain from x0 within 0..=10^9, so each test moves the new name's upper bound.
        "bounded chain" => {
            let n = named(k + 1, "x");
            let p = Premises::new();
            let s = ints(&n)
                .assume(&prim(Prim::Ge, var("x0"), int(0)), true, &p)
                .assume(&prim(Prim::Le, var("x0"), int(1_000_000_000)), true, &p);
            let ts = (0..k).map(|i| ge(&n[i], &n[i + 1], 1)).collect();
            (s, ts)
        }
        // x - y0 >= 0, x - y1 >= 0, …: a star on x.
        "star" => {
            let mut n = named(k, "y");
            let ts = (0..k).map(|i| ge("x", &n[i], 0)).collect();
            n.push("x".into());
            (ints(&n), ts)
        }
        // x0 - x1 >= 1 || x1 - x0 >= 1, …: a chain of disjunctions.
        "or chain" => {
            let n = named(k + 1, "x");
            let ts = (0..k)
                .map(|i| prim(Prim::Or, ge(&n[i], &n[i + 1], 1), ge(&n[i + 1], &n[i], 1)))
                .collect();
            (ints(&n), ts)
        }
        _ => unreachable!("{which}"),
    }
}

#[test]
fn tests_assumed_one_by_one_on_one_linked_component_take_time_near_their_number() {
    // Each test projects the block it joins and the blocks a moved bound reaches, not the
    // whole component. The scopes and tests are built before the timing.
    for which in ["chain", "bounded chain", "star", "or chain"] {
        let built: BTreeMap<usize, (Scope, Vec<Term>)> = [50, 400]
            .into_iter()
            .map(|k| (k, shape(which, k)))
            .collect();
        scaling::check_order(&format!("a {which} assumed one by one"), 50, 1, |k| {
            let (s, ts) = &built[&k];
            let p = Premises::new();
            ts.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        });
    }
}

#[test]
fn a_chain_from_a_bounded_name_bounds_each_name_of_the_chain() {
    let (s, ts) = shape("bounded chain", 20);
    let p = Premises::new();
    let s = ts.iter().fold(s, |s, t| s.assume(t, true, &p));
    assert!(!s.bottom, "{s}");
    let x20 = s.names.get("x20").expect("x20");
    assert_eq!(
        x20.ints().to_string(),
        "[..=999999980]",
        "x20 is at most x0 - 20: {s}"
    );
}

const NAMES: [&str; 6] = ["a", "b", "c", "d", "e", "f"];

/// A random conjunct over the names of [`NAMES`]: a constraint on one to three atoms, now and
/// then a product of two names, or a disjunction of two such constraints.
fn conjunct(r: &mut Rng) -> Formula {
    let con = |r: &mut Rng| {
        let mut lin = Lin::constant(r.int(-3, 3));
        for _ in 0..1 + r.below(3) {
            let a = if r.below(6) == 0 {
                let (x, y) = (r.pick(&NAMES), r.pick(&NAMES));
                if x == y {
                    Atom::Sym(x.into())
                } else {
                    Atom::product(&x.into(), &y.into())
                }
            } else {
                Atom::Sym(r.pick(&NAMES).into())
            };
            lin = lin.plus(&Lin::atom(a).times(r.int(-2, 2)));
        }
        Formula::Con(Con::ge(&lin, &Lin::constant(0)))
    };
    if r.below(4) == 0 {
        Formula::or(vec![con(r), con(r)])
    } else {
        con(r)
    }
}

/// The blocks of `c`, each as the set of its conjuncts.
fn partition(c: &Conjuncts) -> BTreeSet<BTreeSet<Arc<Formula>>> {
    let blocks = c.blocks();
    let mut by: BTreeMap<u64, BTreeSet<Arc<Formula>>> = BTreeMap::new();
    for g in c.set() {
        let b = blocks.of(g).unwrap_or_else(|| panic!("{g} has no block"));
        by.entry(b).or_default().insert(g.clone());
    }
    for (b, gs) in &by {
        let members: BTreeSet<Arc<Formula>> = blocks.members(*b).cloned().collect();
        assert_eq!(&members, gs, "the members of block {b}");
    }
    by.into_values().collect()
}

/// The blocks of `c` by their definition, by brute force: conjuncts that share an atom other
/// than a name are one group, and two groups are in one block when no single name separates
/// them in the graph of groups and the names they mention as atoms of their own.
fn partition_by_definition(c: &Conjuncts) -> BTreeSet<BTreeSet<Arc<Formula>>> {
    let gs: Vec<Arc<Formula>> = c.set().iter().cloned().collect();
    let n = gs.len();
    let mut group: Vec<usize> = (0..n).collect();
    fn find(g: &mut [usize], i: usize) -> usize {
        if g[i] == i {
            i
        } else {
            let r = find(g, g[i]);
            g[i] = r;
            r
        }
    }
    let atoms: Vec<BTreeSet<Atom>> = gs.iter().map(|g| g.atoms()).collect();
    for i in 0..n {
        for j in 0..i {
            if atoms[i]
                .iter()
                .any(|a| !matches!(a, Atom::Sym(_)) && atoms[j].contains(a))
            {
                let (a, b) = (find(&mut group, i), find(&mut group, j));
                group[a] = b;
            }
        }
    }
    let group: Vec<usize> = (0..n).map(|i| find(&mut group, i)).collect();
    let syms: Vec<BTreeSet<Arc<str>>> = atoms
        .iter()
        .map(|s| {
            s.iter()
                .filter_map(|a| match a {
                    Atom::Sym(x) => Some(x.clone()),
                    _ => None,
                })
                .collect()
        })
        .collect();
    let all: BTreeSet<Arc<str>> = syms.iter().flatten().cloned().collect();
    // Whether groups `a` and `b` are linked when name `cut`, if any, is taken out.
    let linked = |a: usize, b: usize, cut: Option<&Arc<str>>| {
        let mut seen: BTreeSet<usize> = BTreeSet::from([a]);
        let mut work = vec![a];
        while let Some(x) = work.pop() {
            for i in 0..n {
                if group[i] != x {
                    continue;
                }
                for m in syms[i].iter().filter(|m| Some(*m) != cut) {
                    for j in 0..n {
                        if syms[j].contains(m) && seen.insert(group[j]) {
                            work.push(group[j]);
                        }
                    }
                }
            }
        }
        seen.contains(&b)
    };
    let mut blocks: Vec<BTreeSet<Arc<Formula>>> = Vec::new();
    let mut of: Vec<Option<usize>> = vec![None; n];
    for i in 0..n {
        if of[i].is_some() {
            continue;
        }
        let k = blocks.len();
        blocks.push(BTreeSet::new());
        for j in i..n {
            let same = group[i] == group[j]
                || (linked(group[i], group[j], None)
                    && all.iter().all(|m| linked(group[i], group[j], Some(m))));
            if same {
                of[j] = Some(k);
                blocks[k].insert(gs[j].clone());
            }
        }
    }
    blocks.into_iter().collect()
}

#[test]
fn the_blocks_kept_as_conjuncts_come_and_go_are_those_of_the_definition() {
    let mut r = Rng::new(0xb10c);
    // How many states had a block of several conjuncts beside another block, so that the
    // test is known to reach blocks that are neither one conjunct nor the whole relation.
    let mut mixed = 0;
    for case in 0..200 {
        let mut c = Conjuncts::default();
        let mut log: Vec<String> = Vec::new();
        for _ in 0..24 {
            match r.below(8) {
                0 if !c.is_top() => {
                    let gs: Vec<Arc<Formula>> = c.set().iter().cloned().collect();
                    let g = r.pick(&gs);
                    log.push(format!("remove {g}"));
                    c.remove(&g);
                }
                1 => {
                    let x: Arc<str> = r.pick(&NAMES).into();
                    log.push(format!("forget {x}"));
                    c.forget(&x);
                }
                _ => {
                    let g = conjunct(&mut r);
                    log.push(format!("and {g}"));
                    c.and(g);
                }
            }
            let got = partition(&c);
            mixed += usize::from(got.len() > 1 && got.iter().any(|b| b.len() > 1));
            assert_eq!(
                got,
                partition_by_definition(&c),
                "case {case} after {log:#?}"
            );
            // The same conjuncts added afresh, in the reverse order, give the same blocks.
            let mut fresh = Conjuncts::default();
            for g in c.set().iter().rev() {
                fresh.and(Formula::clone(g));
            }
            assert_eq!(fresh.set(), c.set(), "case {case}");
            assert_eq!(partition(&fresh), got, "case {case} afresh after {log:#?}");
            for g in c.set() {
                assert!(names(g).iter().all(|n| c.mentioning(n).any(|h| h == g)));
            }
        }
    }
    assert!(mixed > 500, "{mixed} states with mixed blocks");
}
