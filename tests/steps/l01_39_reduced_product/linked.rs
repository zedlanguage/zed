//! Tests on names linked into one component: the blocks a relation is projected by are kept
//! as conjuncts come and go, equal to those found afresh, and a test assumed on a linked
//! component costs near its own block, not the component (COMPLEXITY.md S20).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::conjuncts::{Conjuncts, edges, names};
use zedc::store::interval::End;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Rel, Shared};
use zedc::store::product::{Product, Scope};

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

/// A random conjunct as [`conjunct`] gives, or, four times in five, one of the shape of a star's
/// ([`stars_by_definition`]): one of `c` to `f`, each with a sign of its own, against one or
/// both of the hubs `a` and `b`, the sign now and then the other one, so that stars of two
/// hubs come and go.
fn star_conjunct(r: &mut Rng) -> Formula {
    if r.below(5) == 0 {
        return conjunct(r);
    }
    let i = r.below(4);
    let flip = |r: &mut Rng| if r.below(8) == 0 { -1 } else { 1 };
    let up = if i.is_multiple_of(2) { 1 } else { -1 };
    let leaf = Atom::Sym(["c", "d", "e", "f"][i].into());
    let mut lin = Lin::constant(r.int(-3, 3)).plus(&Lin::atom(leaf).times(up * flip(r)));
    let hubs = match r.below(3) {
        0 => &["a"][..],
        1 => &["b"][..],
        _ => &["a", "b"][..],
    };
    for h in hubs {
        lin = lin.plus(&Lin::atom(Atom::Sym((*h).into())).times(-up * flip(r)));
    }
    Formula::Con(Con::ge(&lin, &Lin::constant(0)))
}

/// The blocks of `c`, each as the set of its conjuncts.
pub(super) fn partition(c: &Conjuncts) -> BTreeSet<BTreeSet<Arc<Formula>>> {
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

/// The stars of `c` by their definition ([`Conjuncts::star`]), by brute force, each leaf with
/// its conjuncts: a name no written constraint holds of, each conjunct at which is a
/// constraint `>= 0` of names alone with another name, its coefficient of one sign at all of
/// them and each hub's of one sign, each hub of more conjuncts than it, and unbounded on the
/// side away from each conjunct of two hubs or more; with one hub, or with every hub's
/// conjuncts each the conjunct of such a leaf other than the hub, of the hub alone, or one
/// whose other names are each a hub or a satellite whose other related names are hubs.
pub(super) fn stars_by_definition(c: &Conjuncts) -> BTreeMap<Arc<str>, BTreeSet<Arc<Formula>>> {
    let at = |x: &Arc<str>| -> Vec<Arc<Formula>> {
        c.set()
            .iter()
            .filter(|g| names(g).contains(x))
            .cloned()
            .collect()
    };
    // The leaves of that shape, each with its hubs.
    let mut shaped: BTreeMap<Arc<str>, BTreeSet<Arc<str>>> = BTreeMap::new();
    'name: for x in c.set().iter().flat_map(|g| names(g)) {
        if shaped.contains_key(&x) || c.pinned(&x) {
            continue;
        }
        let gs = at(&x);
        let mut signs: BTreeMap<Arc<str>, bool> = BTreeMap::new();
        for g in &gs {
            let Formula::Con(k) = &**g else {
                continue 'name;
            };
            if k.rel != Rel::Ge || k.lin.terms.keys().any(|a| !matches!(a, Atom::Sym(_))) {
                continue 'name;
            }
            let Some(a) = k.lin.terms.get(&Atom::Sym(x.clone())) else {
                continue 'name;
            };
            if k.lin.terms.len() < 2 {
                continue 'name;
            }
            if k.lin.terms.len() > 2 && c.bounded(&x, a.is_positive()) {
                continue 'name;
            }
            for (t, b) in &k.lin.terms {
                let Atom::Sym(h) = t else { unreachable!() };
                if *signs.entry(h.clone()).or_insert(b.is_positive()) != b.is_positive() {
                    continue 'name;
                }
            }
        }
        signs.remove(&x);
        if signs.keys().any(|h| at(h).len() <= gs.len()) {
            continue;
        }
        shaped.insert(x, signs.into_keys().collect());
    }
    let owner = |g: &Arc<Formula>| shaped.keys().find(|x| names(g).contains(*x));
    let alone = |g: &Arc<Formula>, h: &Arc<str>| g.atoms().into_iter().eq([Atom::Sym(h.clone())]);
    // The free conjuncts at a name: neither another leaf's nor of it alone.
    let free = |n: &Arc<str>| -> Vec<Arc<Formula>> {
        at(n)
            .into_iter()
            .filter(|g| !owner(g).is_some_and(|x| x != n) && !alone(g, n))
            .collect()
    };
    // Of a satellite, a name each of whose free conjuncts mentions it and one other name, the
    // names it relates to; `None` for any other name.
    let related = |y: &Arc<str>| -> Option<BTreeSet<Arc<str>>> {
        let mut out = BTreeSet::new();
        for g in free(y) {
            let ns = names(&g);
            if ns.len() != 2 {
                return None;
            }
            out.extend(ns.into_iter().filter(|n| n != y));
        }
        Some(out)
    };
    // A hub admits a leaf when each other name of each free conjunct at it is a hub of the
    // leaf, or a satellite whose related names other than the hub are.
    let admits = |h: &Arc<str>, hubs: &BTreeSet<Arc<str>>| {
        free(h).iter().all(|g| {
            names(g)
                .iter()
                .filter(|y| *y != h)
                .all(|y| match related(y) {
                    Some(s) => s.iter().filter(|z| *z != h).all(|z| hubs.contains(z)),
                    None => hubs.contains(y),
                })
        })
    };
    shaped
        .iter()
        .filter(|(_, hubs)| hubs.len() == 1 || hubs.iter().all(|h| admits(h, hubs)))
        .map(|(x, _)| (x.clone(), at(x).into_iter().collect()))
        .collect()
}

/// The blocks of `c` by their definition, by brute force: each star is a block
/// ([`stars_by_definition`]); of the other conjuncts, those that share an atom other than a
/// name are one group, and two groups are in one block when no single name separates them in
/// the graph of groups and the names they mention as atoms of their own.
pub(super) fn partition_by_definition(c: &Conjuncts) -> BTreeSet<BTreeSet<Arc<Formula>>> {
    let stars = stars_by_definition(c);
    let starred: BTreeSet<&Arc<Formula>> = stars.values().flatten().collect();
    let gs: Vec<Arc<Formula>> = c
        .set()
        .iter()
        .filter(|g| !starred.contains(g))
        .cloned()
        .collect();
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
    blocks.into_iter().chain(stars.into_values()).collect()
}

#[test]
fn the_blocks_kept_as_conjuncts_come_and_go_are_those_of_the_definition() {
    let mut r = Rng::new(0xb10c);
    // How many states had a block of several conjuncts beside another block, so that the
    // test is known to reach blocks that are neither one conjunct nor the whole relation.
    let mut mixed = 0;
    // How many states had a star of two hubs or more, and a star of two conjuncts or more.
    let mut starred = 0;
    let mut wide = 0;
    // How many states had a star of two hubs that a conjunct of no leaf relates.
    let mut related = 0;
    // The names marked as having holes or a class ([`Conjuncts::gapped`]), drawn apart so that
    // the other draws stay as they were, and how many states had a tree of difference
    // constraints and bounds of two conjuncts or more, and one held back by a name with holes
    // (32 and 36 states; [`the_counts_of_a_tree_of_differences_are_those_of_the_definition`]
    // draws mostly differences).
    let mut gr = Rng::new(0x6a95);
    let (mut differences, mut gapped) = (0, 0);
    for case in 0..200 {
        let mut c = Conjuncts::default();
        let mut log: Vec<String> = Vec::new();
        let mut gaps: BTreeSet<Arc<str>> = BTreeSet::new();
        for _ in 0..24 {
            let (x, on): (Arc<str>, bool) = (gr.pick(&NAMES).into(), gr.below(3) == 0);
            log.push(format!("gap {x} {on}"));
            c.gapped(&x, on);
            if on {
                gaps.insert(x);
            } else {
                gaps.remove(&x);
            }
            match r.below(10) {
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
                // As a join does: one or two conjuncts go, and a new one comes, now and then
                // a constraint on the same term as one that goes, which takes its place.
                2 if !c.is_top() => {
                    let gs: Vec<Arc<Formula>> = c.set().iter().cloned().collect();
                    let mut gone = vec![r.pick(&gs)];
                    if r.below(2) == 0 {
                        gone.push(r.pick(&gs));
                    }
                    let g = match &*gone[0] {
                        Formula::Con(k) if r.below(2) == 0 => {
                            Formula::Con(Con::ge(&k.lin, &Lin::constant(r.int(-2, 2))))
                        }
                        _ => star_conjunct(&mut r),
                    };
                    log.push(format!("swap {gone:?} for {g}"));
                    c.swap(&gone, g);
                }
                // As a scope does: a written constraint holds of a name or no longer does, and a
                // name is bounded or unbounded on a side, which a star's leaf reads.
                8 => {
                    let (x, on): (Arc<str>, bool) = (r.pick(&NAMES).into(), r.below(2) == 0);
                    log.push(format!("pin {x} {on}"));
                    c.pin(&x, on);
                }
                9 => {
                    let x: Arc<str> = r.pick(&NAMES).into();
                    let (below, above) = (r.below(2) == 0, r.below(2) == 0);
                    log.push(format!("bound {x} {below} {above}"));
                    c.bound(&x, below, above);
                }
                _ => {
                    let g = star_conjunct(&mut r);
                    log.push(format!("and {g}"));
                    c.and(g);
                }
            }
            // A conjunct of no names, such as `-1 >= 0` when every coefficient drawn is zero,
            // is decided when added: a false one makes the conjunction `false`, which has no
            // blocks. The case then goes on from `true`.
            if c.is_bottom() {
                assert_eq!(c.set().len(), 1, "case {case}");
                assert!(c.blocks().all().next().is_none(), "case {case}");
                c = Conjuncts::default();
                gaps.clear();
                log.push("false; from true again".into());
                continue;
            }
            let got = partition(&c);
            mixed += usize::from(got.len() > 1 && got.iter().any(|b| b.len() > 1));
            let stars = stars_by_definition(&c);
            starred += usize::from(stars.values().any(|gs| {
                gs.iter()
                    .flat_map(|g| names(g))
                    .collect::<BTreeSet<_>>()
                    .len()
                    > 2
            }));
            wide += usize::from(stars.values().any(|gs| gs.len() > 1));
            related += usize::from(stars.iter().any(|(x, gs)| {
                let hubs: BTreeSet<Arc<str>> = gs
                    .iter()
                    .flat_map(|g| names(g))
                    .filter(|n| n != x)
                    .collect();
                hubs.len() > 1
                    && c.set().iter().any(|g| {
                        let ns = names(g);
                        ns.len() > 1 && ns.iter().all(|n| hubs.contains(n))
                    })
            }));
            for (x, gs) in &stars {
                let b = c
                    .star(x)
                    .unwrap_or_else(|| panic!("{x} is a star's leaf after {log:#?}"));
                let got: BTreeSet<Arc<Formula>> = c.blocks().members(b).cloned().collect();
                assert_eq!(&got, gs, "case {case}: the star of {x} after {log:#?}");
            }
            for x in c.names() {
                assert_eq!(
                    c.star(x).is_some(),
                    stars.contains_key(x),
                    "case {case}: {x} after {log:#?}"
                );
            }
            assert_eq!(
                got,
                partition_by_definition(&c),
                "case {case} after {log:#?}"
            );
            // The same conjuncts added afresh, in the reverse order, give the same blocks.
            let mut fresh = Conjuncts::default();
            for x in NAMES {
                let x: Arc<str> = x.into();
                fresh.pin(&x, c.pinned(&x));
                fresh.bound(&x, c.bounded(&x, false), c.bounded(&x, true));
            }
            for g in c.set().iter().rev() {
                fresh.and(Formula::clone(g));
            }
            assert_eq!(fresh.set(), c.set(), "case {case}");
            assert_eq!(partition(&fresh), got, "case {case} afresh after {log:#?}");
            for g in c.set() {
                assert!(names(g).iter().all(|n| c.mentioning(n).any(|h| h == g)));
            }
            let (alone, held) = differences_only_by_definition(&c, &gaps, &log, case);
            differences += usize::from(alone);
            gapped += usize::from(held);
        }
    }
    assert!(mixed > 500, "{mixed} states with mixed blocks");
    assert!(
        differences > 20,
        "{differences} states with a tree of differences alone"
    );
    assert!(
        gapped > 20,
        "{gapped} states with a tree of differences and a name with holes"
    );
    assert!(starred > 75, "{starred} states with a star of two hubs");
    assert!(wide > 40, "{wide} states with a star of two conjuncts");
    assert!(
        related > 100,
        "{related} states with a star of related hubs"
    );
}

#[test]
fn the_counts_of_a_tree_of_differences_are_those_of_the_definition() {
    // Mostly difference constraints and bounds, now and then another conjunct, added,
    // removed, swapped and forgotten, with names marked as having holes: each tree's counts
    // ([`zedc::store::conjuncts::Blocks::differences_only`]) say what the definition says.
    let mut r = Rng::new(0xd1ff);
    let (mut alone, mut held) = (0, 0);
    let difference = |r: &mut Rng| {
        let (x, y) = (
            Atom::Sym(r.pick(&NAMES).into()),
            Atom::Sym(r.pick(&NAMES).into()),
        );
        let mut lin = Lin::constant(r.int(-3, 3)).plus(&Lin::atom(x));
        if r.below(4) != 0 {
            lin = lin.plus(&Lin::atom(y).times(-1));
        } else if r.below(2) == 0 {
            lin = lin.times(-1);
        }
        let k = Con::ge(&lin, &Lin::constant(0));
        Formula::Con(if r.below(8) == 0 {
            Con::eq(&lin, &Lin::constant(0))
        } else {
            k
        })
    };
    for case in 0..300 {
        let mut c = Conjuncts::default();
        let mut log: Vec<String> = Vec::new();
        let mut gaps: BTreeSet<Arc<str>> = BTreeSet::new();
        for _ in 0..30 {
            match r.below(12) {
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
                2 if !c.is_top() => {
                    let gs: Vec<Arc<Formula>> = c.set().iter().cloned().collect();
                    let gone = vec![r.pick(&gs)];
                    let g = difference(&mut r);
                    log.push(format!("swap {gone:?} for {g}"));
                    c.swap(&gone, g);
                }
                3 | 4 => {
                    let (x, on): (Arc<str>, bool) = (r.pick(&NAMES).into(), r.below(3) == 0);
                    log.push(format!("gap {x} {on}"));
                    c.gapped(&x, on);
                    if on {
                        gaps.insert(x);
                    } else {
                        gaps.remove(&x);
                    }
                }
                5 => {
                    let g = conjunct(&mut r);
                    log.push(format!("and {g}"));
                    c.and(g);
                }
                _ => {
                    let g = difference(&mut r);
                    log.push(format!("and {g}"));
                    c.and(g);
                }
            }
            if c.is_bottom() {
                c = Conjuncts::default();
                gaps.clear();
                log.push("false; from true again".into());
                continue;
            }
            let (a, h) = differences_only_by_definition(&c, &gaps, &log, case);
            alone += usize::from(a);
            held += usize::from(h);
        }
    }
    assert!(
        alone > 1000,
        "{alone} states with a tree of differences alone"
    );
    assert!(
        held > 500,
        "{held} states with a tree of differences and a name with holes"
    );
}

/// Checks that each tree of the forest of `c` holds only difference constraints and bounds
/// ([`edges`]) and no name of `gaps`, exactly when its counts say so
/// ([`zedc::store::conjuncts::Blocks::differences_only`]); whether one such tree of two
/// conjuncts or more lies beside a tree that is not.
fn differences_only_by_definition(
    c: &Conjuncts,
    gaps: &BTreeSet<Arc<str>>,
    log: &[String],
    case: usize,
) -> (bool, bool) {
    let blocks = c.blocks();
    let mut trees: BTreeMap<_, Vec<&Arc<Formula>>> = BTreeMap::new();
    for g in c.set() {
        if let Some(b) = blocks.of(g).filter(|b| !blocks.is_apart(*b)) {
            trees.entry(blocks.tree(b)).or_default().push(g);
        }
    }
    let (mut alone, mut held) = (false, false);
    for (t, gs) in &trees {
        let want = gs
            .iter()
            .all(|g| edges(g).is_some() && names(g).iter().all(|n| !gaps.contains(n)));
        assert_eq!(
            blocks.differences_only(*t),
            want,
            "case {case}: the tree of {gs:?} after {log:#?}"
        );
        // A name inside a product of names is no node of the forest; its conjunct links it
        // through the product (`Blocks::shared`).
        for a in gs.iter().flat_map(|g| g.atoms()) {
            let Atom::Sym(n) = a else { continue };
            assert_eq!(blocks.tree_of_name(&n), Some(*t), "case {case}: {n}");
            assert_eq!(c.differences_only_at(&n), want, "case {case}: {n}");
        }
        alone |= want && gs.len() > 1;
        held |= !want && gs.len() > 1 && gs.iter().all(|g| edges(g).is_some());
    }
    (alone, held)
}

/// As a join of two arms does: many conjuncts go at once, often most of a block, and the
/// disjunction of some of them with a new conjunct takes their place. The blocks stay those
/// of the definition when a block loses several conjuncts in one removal.
#[test]
fn the_blocks_stay_those_of_the_definition_when_many_conjuncts_go_at_once() {
    let mut r = Rng::new(0x5a1e);
    let mut many = 0;
    for case in 0..200 {
        let mut c = Conjuncts::default();
        let mut log: Vec<String> = Vec::new();
        for _ in 0..16 {
            if r.below(3) == 0 && !c.is_top() {
                let gs: Vec<Arc<Formula>> = c.set().iter().cloned().collect();
                let gone: Vec<Arc<Formula>> = gs.into_iter().filter(|_| r.below(3) != 0).collect();
                many += usize::from(gone.len() > 2);
                let mut either: Vec<Formula> = gone
                    .iter()
                    .filter(|_| r.below(2) == 0)
                    .map(|g| Formula::clone(g))
                    .collect();
                either.push(conjunct(&mut r));
                let g = Formula::or(either);
                log.push(format!("swap {} conjuncts for {g}", gone.len()));
                c.swap(&gone, g);
            } else {
                let g = conjunct(&mut r);
                log.push(format!("and {g}"));
                c.and(g);
            }
            if c.is_bottom() {
                c = Conjuncts::default();
                log.push("false; from true again".into());
                continue;
            }
            assert_eq!(
                partition(&c),
                partition_by_definition(&c),
                "case {case} after {log:#?}"
            );
        }
    }
    assert!(many > 250, "{many} removals of three conjuncts or more");
}

#[test]
#[ignore = "PRODUCT-lin-rows: 15.5 times the work at 50 and 400 if statements, over the n log n limit 13.5 since SCALE-ratio; open"]
fn if_statements_joined_one_after_another_on_a_linked_chain_take_time_near_their_number() {
    // x0 - x1 >= 1, x1 - x2 >= 1, … then, for each link, an `if x_i - x_{i+1} >= 2` whose two
    // arms are joined. The arms differ in the link's conjunct, which the join replaces in its
    // block; removing it first would cut the chain in two and build its blocks again, which
    // made the joins quadratic (COMPLEXITY.md S20).
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Vec<Term>)> = [50, 400]
        .into_iter()
        .map(|k| {
            let (s, chain) = shape("chain", k);
            let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
            let n = named(k + 1, "x");
            let tests = (0..k).map(|i| ge(&n[i], &n[i + 1], 2)).collect();
            (k, (s, tests))
        })
        .collect();
    scaling::check_order("if statements joined on a chain", 50, 1, |k| {
        let (s, tests) = &built[&k];
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        });
    });
}

#[test]
fn if_statements_joined_on_a_chain_keep_the_chain() {
    // Each join keeps `x_i - x_{i+1} >= 1`, which both arms hold, so `x0 - x20 >= 20`.
    let p = Premises::new();
    let (s, chain) = shape("bounded chain", 20);
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
    let n = named(21, "x");
    let s = (0..20).fold(s, |s, i| {
        let t = ge(&n[i], &n[i + 1], 2);
        let mut j = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
        j.reduce();
        j
    });
    assert!(!s.bottom, "{s}");
    assert_eq!(s.names["x20"].ints().to_string(), "[..=999999980]", "{s}");
}

/// The constraint `a - b - c >= 0` as a formula.
fn diff(a: &str, b: &str, c: i64) -> Formula {
    let at = |n: &str| Lin::atom(Atom::Sym(n.into()));
    Formula::Con(Con::ge(&at(a).minus(&at(b)), &Lin::constant(c)))
}

#[test]
fn a_disjunction_of_a_constraint_and_its_complement_is_true() {
    // x - y >= 3 || x - y <= 2 holds at every integer point; x - y >= 3 || x - y <= 1 does
    // not (x - y = 2), nor does x - y >= 3 || y - z >= 0, so both are kept as written.
    let le = |a: &str, b: &str, c: i64| Formula::negate(diff(a, b, c + 1));
    let below = Formula::Con(Con::ge(
        &Lin::constant(2),
        &Lin::atom(Atom::Sym("x".into())).minus(&Lin::atom(Atom::Sym("y".into()))),
    ));
    assert_eq!(Formula::or(vec![diff("x", "y", 3), below]), Formula::top());
    assert_eq!(
        Formula::or(vec![diff("x", "y", 3), le("x", "y", 2)]),
        Formula::top()
    );
    assert_eq!(
        Formula::or(vec![diff("x", "y", 3), diff("z", "w", 0), le("x", "y", 2)]),
        Formula::top()
    );
    let gap = Formula::Con(Con::ge(
        &Lin::constant(1),
        &Lin::atom(Atom::Sym("x".into())).minus(&Lin::atom(Atom::Sym("y".into()))),
    ));
    let kept = Formula::or(vec![diff("x", "y", 3), gap.clone()]);
    assert_eq!(kept, Formula::Or(Shared::new(vec![diff("x", "y", 3), gap])));
    let apart = Formula::or(vec![diff("x", "y", 3), diff("y", "z", 0)]);
    assert_eq!(
        apart,
        Formula::Or(Shared::new(vec![diff("x", "y", 3), diff("y", "z", 0)]))
    );
    // Twice the same constraint is not its own complement.
    assert_eq!(
        Formula::or(vec![diff("x", "y", 0), diff("x", "y", 0)]),
        Formula::Or(Shared::new(vec![diff("x", "y", 0), diff("x", "y", 0)]))
    );
}

/// `x >= d - 1 || (y >= d - 1 && (x >= d - 2 || (y >= d - 2 && … (x >= 0 || y >= 0))))`, as
/// written by a nest of `d` conditions `if x >= i || (y >= i && …)`, built by `Formula::or` and
/// `Formula::and` from the given constraints, innermost first.
fn nested(xs: &[Formula], ys: &[Formula]) -> Formula {
    let first = Formula::or(vec![xs[0].clone(), ys[0].clone()]);
    xs.iter().zip(ys).skip(1).fold(first, |f, (x, y)| {
        Formula::or(vec![x.clone(), Formula::and(vec![y.clone(), f])])
    })
}

#[test]
fn a_compound_disjunct_and_its_negation_are_kept_as_written() {
    // `(x >= y + 3 && y >= z) || !(x >= y + 3 && y >= z)` holds at every point, but only a
    // constraint and its negation are looked up (the tradeoff at `Formula::complementary`).
    let g = Formula::and(vec![diff("x", "y", 3), diff("y", "z", 0)]);
    let not_g = Formula::negate(g.clone());
    assert_eq!(
        Formula::or(vec![g.clone(), not_g.clone()]),
        Formula::Or(Shared::new(vec![g, not_g]))
    );
    // Inside a nest, a constraint and its negation are still found at any depth.
    let inner = Formula::or(vec![diff("x", "y", 3), Formula::negate(diff("x", "y", 3))]);
    let nest = Formula::or(vec![
        diff("z", "w", 0),
        Formula::and(vec![diff("y", "z", 1), inner]),
    ]);
    assert_eq!(
        nest,
        Formula::or(vec![diff("z", "w", 0), diff("y", "z", 1)])
    );
}

#[test]
fn a_nested_or_and_formula_keeps_every_case() {
    let at = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let xs: Vec<Formula> = (0..6)
        .map(|i| Formula::Con(Con::ge(&at("x"), &Lin::constant(i))))
        .collect();
    let ys: Vec<Formula> = (0..6)
        .map(|i| Formula::Con(Con::ge(&at("y"), &Lin::constant(i))))
        .collect();
    let f = nested(&xs, &ys);
    // Mapping every constraint to itself gives the formula back.
    assert_eq!(f.map_cons(&|c| Formula::Con(c.clone())), f);
    assert_eq!(f.cons().len(), 12);
    // At (x, y): the nest of six holds when x >= 5, or y >= 5 and the nest of five holds, …
    for x in -1..7i64 {
        for y in -1..7i64 {
            let mut want = x >= 0 || y >= 0;
            for i in 1..6 {
                want = x >= i || y >= i && want;
            }
            let model = [
                (Atom::Sym("x".into()), x.into()),
                (Atom::Sym("y".into()), y.into()),
            ]
            .into();
            assert_eq!(f.holds(&model), want, "({x}, {y}): {f}");
        }
    }
}

#[test]
fn a_nested_or_and_formula_is_built_and_mapped_in_time_near_its_size() {
    // Each `Formula::or` looks up only the constraints among its disjuncts, never a compound
    // disjunct through its depth, so building and mapping a nest of depth d costs O(d).
    let at = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let built: BTreeMap<usize, (Vec<Formula>, Vec<Formula>)> = [250, 2000]
        .into_iter()
        .map(|d| {
            let side = |n: &str| -> Vec<Formula> {
                (0..d as i64)
                    .map(|i| Formula::Con(Con::ge(&at(n), &Lin::constant(i))))
                    .collect()
            };
            (d, (side("x"), side("y")))
        })
        .collect();
    let shift = |c: &Con| Formula::Con(Con::ge(&c.lin, &Lin::constant(1)));
    scaling::check_order("a nested or/and formula built and mapped", 250, 1, |d| {
        let (xs, ys) = &built[&d];
        let f = nested(xs, ys);
        std::hint::black_box(f.map_cons(&shift));
    });
}

#[test]
fn an_if_on_a_chain_whose_arms_cover_every_value_leaves_no_disjunction() {
    // x_i - x_{i+1} >= 1 along the chain, then `if x_i - x_{i+2} >= 3`: the arms differ in
    // that test and its complement, so the join is the chain again and nothing more.
    let p = Premises::new();
    let (s, chain) = shape("chain", 8);
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
    let n = named(9, "x");
    let r = (0..7).fold(s.clone(), |s, i| {
        let t = ge(&n[i], &n[i + 2], 3);
        let mut j = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
        j.reduce();
        j
    });
    assert_eq!(r.relation.set(), s.relation.set(), "{r}");
}

#[test]
fn a_join_whose_arms_leave_a_gap_keeps_the_disjunction() {
    // The chain gives x0 - x2 >= 2. One arm has x0 - x2 >= 4 and the other x0 - x2 <= 2: the
    // join leaves out x0 - x2 == 3.
    let p = Premises::new();
    let (s, chain) = shape("chain", 2);
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
    let mut j =
        s.assume(&ge("x0", "x2", 4), true, &p)
            .join(&s.assume(&ge("x2", "x0", -2), true, &p));
    j.reduce();
    let point = |x0: i64, x1: i64, x2: i64| -> BTreeMap<Arc<str>, Value> {
        [("x0", x0), ("x1", x1), ("x2", x2)]
            .into_iter()
            .map(|(n, v)| (n.into(), Value::Int(v)))
            .collect()
    };
    assert!(j.contains(&point(4, 1, 0)), "{j}");
    assert!(j.contains(&point(2, 1, 0)), "{j}");
    assert!(!j.contains(&point(3, 1, 0)), "{j}");
    assert!(
        j.relation
            .set()
            .iter()
            .any(|g| matches!(**g, Formula::Or(_))),
        "{j}"
    );
}

#[test]
#[ignore = "PRODUCT-lin-rows: 14.8 times the work at 50 and 400 if statements, over the n log n limit 13.5 since SCALE-ratio; open"]
fn if_statements_on_skip_links_of_a_chain_take_time_near_their_number() {
    // The chain, then for each i an `if x_i - x_{i+2} >= 3` whose two arms are joined. The
    // test and its complement made a disjunction `true` at every point that each later test
    // split into cases, about k^4 in all; and removing the test's conjunct from the cycle it
    // closed with x_{i+1} built the blocks of the whole chain again, k^2 (COMPLEXITY.md S20).
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Vec<Term>)> = [50, 400]
        .into_iter()
        .map(|k| {
            let (s, chain) = shape("chain", k);
            let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
            let n = named(k + 1, "x");
            let tests = (0..k - 1).map(|i| ge(&n[i], &n[i + 2], 3)).collect();
            (k, (s, tests))
        })
        .collect();
    scaling::check_order("if statements on skip links of a chain", 50, 1, |k| {
        let (s, tests) = &built[&k];
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        });
    });
}

/// The chain `x_i - x_(i+1) >= 1` with every rung `x_i - x_(i+2) >= 2`: one block of 2k
/// difference constraints.
fn ladder(k: usize, p: &Premises) -> Scope {
    let (s, chain) = shape("chain", k);
    let n = named(k + 1, "x");
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, p));
    (0..k - 1).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 2], 2), true, p))
}

#[test]
fn one_test_on_a_ladder_takes_time_near_its_size() {
    // The block's bounds come from one shortest-path pass over its difference constraints
    // (`presburger::difference_hulls`), not O(log d) solver questions per name, each over
    // the whole block (COMPLEXITY.md S25: 19/80/359/1,680 M at k = 10/20/40/80).
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Term)> = [10, 80]
        .into_iter()
        .map(|k| {
            let n = named(k + 1, "x");
            (k, (ladder(k, &p), ge(&n[0], &n[k], k as i64)))
        })
        .collect();
    scaling::check("one test on a ladder of k rungs", 10, |k| {
        let (s, t) = &built[&k];
        s.assume(t, true, &p);
    });
}

#[test]
#[ignore = "PRODUCT-lin-rows: 15.2 times the work at 40 and 320 if statements, over the n log n limit 13.8 since SCALE-ratio; open"]
fn a_ladder_grown_by_k_if_statements_is_linear() {
    // Each `if x_i - x_(i+2) >= 2` on the chain is implied, so its join keeps the true arm and
    // the block grows by one rung. The chain holds difference constraints alone, so each test
    // repairs the scope's potential and moves the bounds by shortest paths from its own edge
    // (`Scope::shortest`), not by projecting the block: O(log k) each, in either order. It
    // was O(k^2) by projecting the whole block each time (COMPLEXITY.md S25), and O(k^3)
    // before (16/89/608/4,869 M at k = 5/10/20/40).
    let p = Premises::new();
    for reverse in [false, true] {
        let built: BTreeMap<usize, (Scope, Vec<Term>)> = [40, 320]
            .into_iter()
            .map(|k| {
                let (s, chain) = shape("chain", k);
                let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
                let n = named(k + 1, "x");
                let mut tests: Vec<Term> = (0..k - 1).map(|i| ge(&n[i], &n[i + 2], 2)).collect();
                if reverse {
                    tests.reverse();
                }
                (k, (s, tests))
            })
            .collect();
        let name = if reverse {
            "a ladder grown by k if statements, the last rung first"
        } else {
            "a ladder grown by k if statements"
        };
        scaling::check_order(name, 40, 1, |k| {
            let (s, tests) = &built[&k];
            tests.iter().fold(s.clone(), |s, t| {
                let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
                j.reduce();
                j
            });
        });
    }
}

#[test]
fn if_statements_that_leave_a_ladder_block_by_block_between_rungs_are_linear() {
    // The chain from x0 within 0..=10^9, each rung's `if` after an `if` that leaves the tree to
    // the projection block by block in its arms: `x_i + w_i >= 0`, not a difference
    // constraint, with w_i unbounded. The edges that come while the tree goes block by block
    // are put in the potential all the same (`Scope::repair`), so no later test finds it again
    // from the whole tree (`Scope::reseed`). The same mix with a hole, `x_i != 5`, in place of
    // the sum, is quadratic in its output: the arm where x_i is 5 moves the bounds of the
    // names below it, which the ladder bounds from x0 alone (COMPLEXITY.md row S25).
    // `if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_linear` bounds each name.
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Vec<Term>)> = [40, 320]
        .into_iter()
        .map(|k| {
            let n = named(k + 1, "x");
            let w = named(k, "w");
            let s = ints(&[n.clone(), w.clone()].concat())
                .assume(&prim(Prim::Ge, var("x0"), int(0)), true, &p)
                .assume(&prim(Prim::Le, var("x0"), int(1_000_000_000)), true, &p);
            let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
            let mut tests: Vec<Term> = Vec::new();
            for i in 0..k - 1 {
                tests.push(prim(
                    Prim::Ge,
                    prim(Prim::Add, var(&n[i]), var(&w[i])),
                    int(0),
                ));
                tests.push(ge(&n[i], &n[i + 2], 2));
            }
            (k, (s, tests))
        })
        .collect();
    let name = "a ladder grown by k if statements, each after an if on a sum";
    scaling::check_order(name, 40, 1, |k| {
        let (s, tests) = &built[&k];
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        });
    });
}

#[test]
#[ignore = "PRODUCT-lin-rows: 13.8 times the bytes at 40 and 320 if statements, over the n log n limit 13.76 since SCALE-ratio; open"]
fn if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_linear() {
    // The chain from x0 with each x_i within its own ten values, 10 (k - i) to 10 (k - i) + 9,
    // so that no edge moves a bound, each rung's `if` after an `if` that puts a hole in a name,
    // `x_i != 10 (k - i) + 5`. The arms are taken as the checker takes them
    // (`Scope::assume_case`), since the arm where a rung fails is empty. The arm where the
    // hole holds projects the tree by shortest paths, the gap of the name with the hole held in
    // the potential (`Scope::raise`), and the join keeps that arm's last projection, whose tree
    // had a hole and is still read by shortest paths (`Seeds::unsure`). 9.4 times the work and
    // 8.5 times the bytes from k = 40 to 320; on the code before, which projected the tree's
    // blocks one by one at each test, 62.2 times the bytes (COMPLEXITY.md row S25).
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Vec<Term>)> = [40, 320]
        .into_iter()
        .map(|k| {
            let n = named(k + 1, "x");
            let base = |i: usize| (10 * (k - i)) as i64;
            let s = (0..=k).fold(ints(&n), |s, i| {
                s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, &p)
                    .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, &p)
            });
            let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
            let mut tests: Vec<Term> = Vec::new();
            for i in 0..k - 1 {
                tests.push(prim(Prim::Ne, var(&n[i]), int(base(i) + 5)));
                tests.push(ge(&n[i], &n[i + 2], 2));
            }
            (k, (s, tests))
        })
        .collect();
    let name = "a ladder grown by k if statements, each after an if that puts a hole in a name";
    scaling::check_order(name, 40, 1, |k| {
        let (s, tests) = &built[&k];
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s
                .assume_case(t, true, &p)
                .join(&s.assume_case(t, false, &p));
            j.reduce();
            j
        });
    });
}

/// The scope of integers `ns`, each within `0..=10` unless given.
fn within(ns: &[&str], given: &[(&str, Product)]) -> Scope {
    let p = Premises::new();
    let mut s = Scope::new(ns.iter().map(|n| {
        let at = given.iter().find(|(m, _)| m == n);
        let q = at.map_or_else(|| Product::of_type(Type::int()), |(_, q)| q.clone());
        (Arc::<str>::from(*n), q)
    }));
    for n in ns {
        if !given.iter().any(|(m, _)| m == n) {
            s = s.assume(&prim(Prim::Ge, var(n), int(0)), true, &p).assume(
                &prim(Prim::Le, var(n), int(10)),
                true,
                &p,
            );
        }
    }
    s
}

#[test]
fn a_name_with_holes_keeps_its_tree_from_shortest_paths() {
    // x >= z >= y, z in {0, 10}, x and y within 0..=10. Then y >= x moves no interval's
    // bound, but makes x = y = z, so x and y are in {0, 10}: shortest paths over the
    // intervals would leave them 0..=10. The name with holes keeps the tree to the projection
    // block by block (`Blocks::differences_only`).
    let p = Premises::new();
    let mut z = Product::literal(&Value::Int(0));
    z.join(&Product::literal(&Value::Int(10)));
    assert_eq!(z.ints().pieces().len(), 2, "{z:?}");
    let s = within(&["x", "y", "z"], &[("z", z)])
        .assume(&ge("x", "z", 0), true, &p)
        .assume(&ge("z", "y", 0), true, &p);
    assert!(!s.bottom, "{s}");
    let s = s.assume(&ge("y", "x", 0), true, &p);
    assert!(!s.bottom, "{s}");
    for n in ["x", "y", "z"] {
        let got: Vec<(Option<i64>, Option<i64>)> = s
            .get(n)
            .ints()
            .pieces()
            .iter()
            .map(|(a, b)| (a.to_i64(), b.to_i64()))
            .collect();
        assert_eq!(
            got,
            [(Some(0), Some(0)), (Some(10), Some(10))],
            "{n} in {s}"
        );
    }
}

/// The intervals of `s` at `ns`, or `None` when it is bottom.
fn intervals(s: &Scope, ns: &[Arc<str>]) -> Option<Vec<String>> {
    if s.bottom {
        return None;
    }
    Some(
        ns.iter()
            .map(|n| format!("{n}: {:?}", s.get(n).ints()))
            .collect(),
    )
}

#[test]
fn shortest_paths_give_the_intervals_of_the_projection_block_by_block() {
    // Random ladders of difference constraints and bounds, now and then an equality, a
    // negation or an `if` joined, assumed in one order and in the other: each step's
    // intervals are those the projection block by block finds from scratch
    // (`Scope::forget_projections`), which never uses the potential.
    let mut r = Rng::new(0x1add);
    let p = Premises::new();
    let (mut moved, mut empty) = (0, 0);
    for case in 0..150 {
        let k = 3 + r.below(6);
        let ns = named(k, "x");
        let mut tests: Vec<(Term, bool, bool)> = Vec::new();
        for _ in 0..k + r.below(2 * k) {
            let (i, j) = (r.below(k), r.below(k));
            let c = r.int(-3, 3);
            let t = match r.below(8) {
                0 => prim(Prim::Ge, var(&ns[i]), int(r.int(-5, 5))),
                1 => prim(Prim::Le, var(&ns[i]), int(r.int(-5, 5))),
                2 if i != j => prim(Prim::Eq, prim(Prim::Sub, var(&ns[i]), var(&ns[j])), int(c)),
                _ if i != j => ge(&ns[i], &ns[j], c),
                _ => continue,
            };
            tests.push((t, r.below(6) != 0, r.below(10) == 0));
        }
        for reverse in [false, true] {
            let mut order = tests.clone();
            if reverse {
                order.reverse();
            }
            let mut s = ints(&ns);
            for (step, (t, holds, joined)) in order.iter().enumerate() {
                let before = intervals(&s, &ns);
                let next = |s: &Scope| {
                    if *joined {
                        let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
                        j.reduce();
                        j
                    } else {
                        s.assume(t, *holds, &p)
                    }
                };
                let got = next(&s);
                let mut fresh = s.clone();
                fresh.forget_projections();
                let mut want = next(&fresh);
                want.forget_projections();
                want.reduce();
                assert_eq!(
                    intervals(&got, &ns),
                    intervals(&want, &ns),
                    "case {case} reverse {reverse} step {step}: {order:?}"
                );
                moved += usize::from(intervals(&got, &ns) != before);
                if got.bottom {
                    empty += 1;
                    break;
                }
                s = got;
            }
        }
    }
    assert!(moved > 500, "{moved} steps moved an interval");
    assert!(empty > 50, "{empty} ladders became empty");
}

#[test]
fn shortest_paths_with_holes_and_sums_between_give_the_projection_block_by_block() {
    // As above, with tests that leave a tree to the projection block by block between the
    // difference constraints: `x != c`, which gives `x` a hole until a bound closes it, and
    // `x + y >= c`, not a difference constraint. An edge that comes while its tree goes block
    // by block is in the potential before any later edge is read (`Scope::repair`).
    let mut r = Rng::new(0x401e);
    let p = Premises::new();
    let (mut moved, mut empty, mut holes) = (0, 0, 0);
    for case in 0..150 {
        let k = 3 + r.below(6);
        let ns = named(k, "x");
        let mut tests: Vec<(Term, bool, bool)> = Vec::new();
        for _ in 0..k + r.below(3 * k) {
            let (i, j) = (r.below(k), r.below(k));
            let c = r.int(-3, 3);
            let t = match r.below(10) {
                0 => prim(Prim::Ge, var(&ns[i]), int(r.int(-5, 5))),
                1 => prim(Prim::Le, var(&ns[i]), int(r.int(-5, 5))),
                2 | 3 => prim(Prim::Ne, var(&ns[i]), int(r.int(-3, 3))),
                4 if i != j => prim(Prim::Ge, prim(Prim::Add, var(&ns[i]), var(&ns[j])), int(c)),
                5 if i != j => prim(Prim::Eq, prim(Prim::Sub, var(&ns[i]), var(&ns[j])), int(c)),
                _ if i != j => ge(&ns[i], &ns[j], c),
                _ => continue,
            };
            tests.push((t, r.below(6) != 0, r.below(10) == 0));
        }
        for reverse in [false, true] {
            let mut order = tests.clone();
            if reverse {
                order.reverse();
            }
            let mut s = ints(&ns);
            for (step, (t, holds, joined)) in order.iter().enumerate() {
                let before = intervals(&s, &ns);
                let next = |s: &Scope| {
                    if *joined {
                        let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
                        j.reduce();
                        j
                    } else {
                        s.assume(t, *holds, &p)
                    }
                };
                let got = next(&s);
                let mut fresh = s.clone();
                fresh.forget_projections();
                let mut want = next(&fresh);
                want.forget_projections();
                want.reduce();
                assert_eq!(
                    intervals(&got, &ns),
                    intervals(&want, &ns),
                    "case {case} reverse {reverse} step {step}: {order:?}"
                );
                moved += usize::from(intervals(&got, &ns) != before);
                holes += usize::from(ns.iter().any(|n| got.get(n).ints().pieces().len() > 1));
                if got.bottom {
                    empty += 1;
                    break;
                }
                s = got;
            }
        }
    }
    assert!(moved > 500, "{moved} steps moved an interval");
    assert!(empty > 50, "{empty} ladders became empty");
    assert!(holes > 200, "{holes} steps left a name with holes");
}

/// Counts of [`holes_in_trees`]: tests that moved an interval, left a name with holes, left
/// two names or more with holes, or made the scope empty; pairs of inequalities that made a
/// cycle of weight 0; tests that joined both arms.
#[derive(Debug, Default)]
struct HoleCounts {
    moved: usize,
    holes: usize,
    piled: usize,
    empty: usize,
    tied: usize,
    joined: usize,
}

/// Trees of difference constraints, each step a test `x != c` asked both ways on the scope so
/// far and compared with the projection from scratch, then the step's own test. A name whose
/// holes lie within the gap the potential holds with keeps its tree on shortest paths
/// (`Scope::raise`); holes of two integers, cycles lighter than the sum of their names' gaps,
/// and cycles of weight 0 from equalities and from two inequalities go block by block. With
/// `pile`, the step's own test is the hole test half the time, so that holes pile up in many
/// names of one tree.
fn holes_in_trees(seed: u64, pile: bool) -> HoleCounts {
    let mut r = Rng::new(seed);
    let p = Premises::new();
    let mut out = HoleCounts::default();
    for case in 0..150 {
        let k = 3 + r.below(6);
        let ns = named(k, "x");
        let mut s = ints(&ns);
        for n in &ns {
            let lo = r.int(-6, 0);
            s = s.assume(&prim(Prim::Ge, var(n), int(lo)), true, &p);
            s = s.assume(&prim(Prim::Le, var(n), int(lo + r.int(2, 12))), true, &p);
        }
        for step in 0..2 * k + r.below(3 * k) {
            let (i, j) = (r.below(k), r.below(k));
            let c = r.int(-2, 2);
            // Mostly inside the name's interval, so that the test makes a hole; with a
            // difference constraint in the same test, the end the bounds move it to may be one.
            let hole = |r: &mut Rng| {
                let n = r.below(k);
                let c = match s.get(&ns[n]).ints().bounds() {
                    Some((End::Fin(lo), End::Fin(hi))) if r.below(4) != 0 => {
                        let (lo, hi) = (lo.to_i64().unwrap_or(0), hi.to_i64().unwrap_or(0));
                        r.int(lo, hi)
                    }
                    _ => r.int(-4, 6),
                };
                let h = prim(Prim::Ne, var(&ns[n]), int(c));
                let m = r.below(k);
                match r.below(3) {
                    0 if m != n => prim(Prim::And, h, ge(&ns[m], &ns[n], r.int(-2, 2))),
                    _ => h,
                }
            };
            let asked = [hole(&mut r), hole(&mut r), hole(&mut r)];
            for (hole, holds) in asked.iter().flat_map(|h| [(h, true), (h, false)]) {
                let got = s.assume(hole, holds, &p);
                let mut fresh = s.clone();
                fresh.forget_projections();
                let mut want = fresh.assume(hole, holds, &p);
                want.forget_projections();
                want.reduce();
                assert_eq!(
                    intervals(&got, &ns),
                    intervals(&want, &ns),
                    "case {case} step {step} {holds}: {hole:?} on {:?}",
                    s.relation
                );
                let holed = ns
                    .iter()
                    .filter(|n| got.get(n).ints().pieces().len() > 1)
                    .count();
                out.moved += usize::from(intervals(&got, &ns) != intervals(&s, &ns));
                out.holes += usize::from(holed > 0);
                out.piled += usize::from(holed > 1);
                out.empty += usize::from(got.bottom);
            }
            if pile && r.below(2) == 0 {
                let next = s.assume(&asked[0], true, &p);
                if next.bottom {
                    break;
                }
                s = next;
                continue;
            }
            let t = match r.below(12) {
                0 => asked[0].clone(),
                1 if i != j => prim(Prim::Eq, prim(Prim::Sub, var(&ns[i]), var(&ns[j])), int(c)),
                // An `if` whose arms join: the join keeps the last projection of the arm that
                // held, with the hole, and the next steps are projected from it.
                3 => {
                    out.joined += 1;
                    let mut j = s
                        .assume(&asked[1], true, &p)
                        .join(&s.assume(&asked[1], false, &p));
                    j.reduce();
                    if j.bottom {
                        break;
                    }
                    s = j;
                    continue;
                }
                2 if i != j => {
                    out.tied += 1;
                    s = s.assume(&ge(&ns[i], &ns[j], c), true, &p);
                    ge(&ns[j], &ns[i], -c)
                }
                _ if i != j => ge(&ns[i], &ns[j], c),
                _ => continue,
            };
            let next = s.assume(&t, r.below(8) != 0, &p);
            if next.bottom {
                break;
            }
            s = next;
        }
    }
    out
}

#[test]
fn holes_in_a_tree_of_differences_give_the_projection_from_scratch() {
    let n = holes_in_trees(0x1e4e, false);
    assert!(n.moved > 5000, "{n:?}");
    assert!(n.holes > 2000, "{n:?}");
    assert!(n.empty > 500, "{n:?}");
    assert!(n.tied > 60, "{n:?}");
    assert!(n.joined > 80, "{n:?}");
}

/// As [`holes_in_a_tree_of_differences_give_the_projection_from_scratch`], with the holes piled
/// up in many names of each tree.
#[test]
fn holes_piled_in_many_names_of_a_tree_give_the_projection_from_scratch() {
    let n = holes_in_trees(0x9a1e, true);
    assert!(n.moved > 5000, "{n:?}");
    assert!(n.holes > 4000, "{n:?}");
    assert!(n.piled > 2000, "{n:?}");
    assert!(n.empty > 500, "{n:?}");
    assert!(n.tied > 30, "{n:?}");
    assert!(n.joined > 30, "{n:?}");
}

/// A star goes when one step both takes a conjunct from its hub and gives one to its leaf:
/// `a + f <= 1` is the star of `f` while `a` has more conjuncts than `f`, and a swap of the
/// other conjunct at `a` for `f >= a` leaves each of them two, so that neither is a leaf.
/// Two hubs need both to admit the leaf: with `b` beside `a`, `a + b + f <= 1` is no star while
/// `a` has a conjunct no star holds that mentions `d`, no hub of `f`.
#[test]
fn a_star_goes_when_one_step_moves_its_counts() {
    let s = |x: &str| Lin::atom(Atom::Sym(x.into()));
    let ge = |l: Lin| Formula::Con(Con::ge(&l, &Lin::constant(0)));
    let product = |x: &str, y: &str| Lin::atom(Atom::product(&x.into(), &y.into()));
    let same = |c: &Conjuncts| {
        let stars = stars_by_definition(c);
        for x in ["a", "b", "d", "f"] {
            assert_eq!(c.star(x).is_some(), stars.contains_key(x), "{x} in {c}");
        }
        assert_eq!(partition(c), partition_by_definition(c), "{c}");
    };
    let mut c = Conjuncts::default();
    c.and(Formula::or(vec![
        ge(product("a", "b").times(-2).plus(&Lin::constant(-2))),
        ge(s("a").plus(&product("b", "d"))),
    ]));
    c.and(ge(s("a").plus(&s("f")).times(-1).plus(&Lin::constant(1))));
    assert!(c.star("f").is_some(), "{c}");
    same(&c);
    let gs: Vec<Arc<Formula>> = c
        .set()
        .iter()
        .filter(|g| matches!(&***g, Formula::Or(_)))
        .cloned()
        .collect();
    c.swap(&gs, ge(s("f").plus(&s("a").times(-1))));
    assert!(c.star("f").is_none() && c.star("a").is_none(), "{c}");
    same(&c);

    let mut c = Conjuncts::default();
    c.and(Formula::or(vec![
        ge(product("a", "b").times(-2).plus(&Lin::constant(-2))),
        ge(s("a").plus(&product("b", "d"))),
    ]));
    c.and(ge(s("a")
        .plus(&s("b"))
        .plus(&s("f"))
        .times(-1)
        .plus(&Lin::constant(1))));
    assert!(c.star("f").is_none(), "{c}");
    same(&c);
}

/// The ladder of `if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_linear` at size
/// `k`, and its tests: before each rung, a hole `x_i != 10 (k - i) + 5` that holds, so that
/// the holes pile up, one in each name.
fn piled_holes(k: usize, p: &Premises) -> (Scope, Vec<(Term, bool)>) {
    let n = named(k + 1, "x");
    let base = |i: usize| (10 * (k - i)) as i64;
    let s = (0..=k).fold(ints(&n), |s, i| {
        s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, p)
            .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, p)
    });
    let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, p));
    let mut tests: Vec<(Term, bool)> = Vec::new();
    for i in 0..k - 1 {
        tests.push((prim(Prim::Ne, var(&n[i]), int(base(i) + 5)), false));
        tests.push((ge(&n[i], &n[i + 2], 2), true));
    }
    (s, tests)
}

/// The ladder of [`piled_holes`] at `k`, each hole held and each rung an `if` whose arms join.
fn piled_holes_run(k: usize, p: &Premises) -> Scope {
    let (s, tests) = piled_holes(k, p);
    tests.iter().fold(s, |s, (t, joined)| {
        if *joined {
            let mut j = s.assume_case(t, true, p).join(&s.assume_case(t, false, p));
            j.reduce();
            j
        } else {
            s.assume(t, true, p)
        }
    })
}

/// Holes that pile up in the names of one chain stay on shortest paths, and each name keeps its
/// hole. Quadratic, open as item ST-holes-moves (COMPLEXITY.md S25): each hole lowers the
/// potential at its name, and on a chain whose edges have no slack in the potential every name
/// below it moves too, about k/2 names a hole (`Scope::raise`). Before, block by block, cubic.
#[test]
fn holes_piled_in_the_names_of_a_chain_take_quadratic_time() {
    let p = Premises::new();
    let s = piled_holes_run(12, &p);
    assert!(!s.bottom);
    for i in 0..11 {
        let base = 10 * (12 - i) as i64;
        let ints = s.get(&format!("x{i}")).ints().clone();
        assert!(!ints.contains(base + 5), "x{i}: {ints:?}");
        assert!(ints.contains(base + 4), "x{i}: {ints:?}");
    }
    scaling::check_order("holes piled in the names of a chain", 40, 2, |k| {
        piled_holes_run(k, &p);
    });
}

/// An `m` by `m` grid of names, each in its own ten values, each greater than the names right of
/// and below it, then a hole in each name in rows; the names, their bases and the scope.
fn grid_holes(m: usize, p: &Premises) -> Scope {
    let n = named(m * m, "g");
    let at = |r: usize, c: usize| &n[r * m + c];
    let base = |r: usize, c: usize| (10 * (2 * (m - 1) - r - c)) as i64;
    let mut s = ints(&n);
    for r in 0..m {
        for c in 0..m {
            s = s
                .assume(&prim(Prim::Ge, var(at(r, c)), int(base(r, c))), true, p)
                .assume(&prim(Prim::Le, var(at(r, c)), int(base(r, c) + 9)), true, p);
        }
    }
    for r in 0..m {
        for c in 0..m {
            if c + 1 < m {
                s = s.assume(&ge(at(r, c), at(r, c + 1), 1), true, p);
            }
            if r + 1 < m {
                s = s.assume(&ge(at(r, c), at(r + 1, c), 1), true, p);
            }
        }
    }
    for r in 0..m {
        for c in 0..m {
            s = s.assume(&prim(Prim::Ne, var(at(r, c)), int(base(r, c) + 5)), true, p);
        }
    }
    s
}

/// Holes in every name of a grid of difference constraints: each hole moves about `m - 1`
/// names of the potential, so `m^3`, `n^1.5` in the `n = m^2` names (order 3 in `m`). Open as
/// item ST-holes-moves (COMPLEXITY.md S25): the names a hole moves are those within its shift
/// of it by reduced distance, which on a grid are no range of one order of the names.
#[test]
fn holes_in_every_name_of_a_grid_take_time_m_cubed() {
    let p = Premises::new();
    let s = grid_holes(4, &p);
    assert!(!s.bottom);
    for (i, b) in [(0usize, 60i64), (5, 40), (15, 0)] {
        let ints = s.get(&format!("g{i}")).ints().clone();
        assert!(!ints.contains(b + 5), "g{i}: {ints:?}");
        assert!(ints.contains(b + 4), "g{i}: {ints:?}");
    }
    scaling::check_order("holes in every name of a grid, by its side", 4, 3, |m| {
        grid_holes(m, &p);
    });
}
