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
use zedc::store::conjuncts::{Blocks, Conjuncts, edges, names};
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
/// hubs come and go. One time in six such a conjunct is a disjunction of two of them of one
/// leaf, such as `c < a || c < b`, which a star's leaf may hold as well.
fn star_conjunct(r: &mut Rng) -> Formula {
    if r.below(5) == 0 {
        return conjunct(r);
    }
    let i = r.below(4);
    let flip = |r: &mut Rng| if r.below(8) == 0 { -1 } else { 1 };
    let up = if i.is_multiple_of(2) { 1 } else { -1 };
    let leaf = Atom::Sym(["c", "d", "e", "f"][i].into());
    let one = |r: &mut Rng| {
        let mut lin =
            Lin::constant(r.int(-3, 3)).plus(&Lin::atom(leaf.clone()).times(up * flip(r)));
        let hubs = match r.below(3) {
            0 => &["a"][..],
            1 => &["b"][..],
            _ => &["a", "b"][..],
        };
        for h in hubs {
            lin = lin.plus(&Lin::atom(Atom::Sym((*h).into())).times(-up * flip(r)));
        }
        Formula::Con(Con::ge(&lin, &Lin::constant(0)))
    };
    if r.below(6) == 0 {
        let (f, g) = (one(r), one(r));
        return Formula::or(vec![f, g]);
    }
    one(r)
}

/// The blocks of `c`, each as the set of its conjuncts.
pub(super) fn partition(c: &Conjuncts) -> BTreeSet<BTreeSet<Arc<Formula>>> {
    let blocks = c.blocks();
    if let Err(e) = blocks.well_formed() {
        panic!("the forest of {:?}: {e}", c.set());
    }
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
/// constraint `>= 0` of names alone with another name, or a disjunction of such constraints,
/// its coefficient of one sign at all of them and each hub's of one sign, each hub of more
/// conjuncts than it, and unbounded on the
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
            let lone = matches!(&**g, Formula::Con(_));
            let parts: Vec<&Con> = match &**g {
                Formula::Con(k) => vec![k],
                Formula::Or(fs) if fs.len() > 1 => {
                    let ks: Vec<&Con> = (fs.iter())
                        .filter_map(|f| match f {
                            Formula::Con(k) => Some(k),
                            _ => None,
                        })
                        .collect();
                    if ks.len() != fs.len() {
                        continue 'name;
                    }
                    ks
                }
                _ => continue 'name,
            };
            // The names other than `x` of the conjunct, over all its constraints.
            let mut others: BTreeSet<&Atom> = BTreeSet::new();
            for k in parts {
                if k.rel != Rel::Ge || k.lin.terms.keys().any(|a| !matches!(a, Atom::Sym(_))) {
                    continue 'name;
                }
                // A disjunction may hold a part of `x` alone, as `x >= 5` of `x >= n || x >= 5`.
                if !k.lin.terms.contains_key(&Atom::Sym(x.clone()))
                    || (lone && k.lin.terms.len() < 2)
                {
                    continue 'name;
                }
                others.extend(k.lin.terms.keys().filter(|a| **a != Atom::Sym(x.clone())));
                for (t, b) in &k.lin.terms {
                    let Atom::Sym(h) = t else { unreachable!() };
                    if *signs.entry(h.clone()).or_insert(b.is_positive()) != b.is_positive() {
                        continue 'name;
                    }
                }
            }
            if others.is_empty() {
                continue 'name;
            }
            if others.len() > 1 && c.bounded(&x, signs[&x]) {
                continue 'name;
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
    blocks_by_definition(&gs)
        .into_iter()
        .chain(stars.into_values())
        .collect()
}

/// The root of `i` in the union-find `g`.
fn find(g: &mut [usize], i: usize) -> usize {
    if g[i] == i {
        i
    } else {
        let r = find(g, g[i]);
        g[i] = r;
        r
    }
}

/// The blocks of the conjuncts `gs`, stars left aside, by brute force: those that share an
/// atom other than a name are one group, and two groups are in one block when no single name
/// separates them in the graph of groups and the names they mention as atoms of their own.
fn blocks_by_definition(gs: &[Arc<Formula>]) -> Vec<BTreeSet<Arc<Formula>>> {
    let n = gs.len();
    let mut group: Vec<usize> = (0..n).collect();
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
    blocks
}

#[test]
fn the_blocks_kept_as_conjuncts_come_and_go_are_those_of_the_definition() {
    let (mut r, seed) = Rng::fresh("blocks kept as conjuncts");
    // How many states had a block of several conjuncts beside another block, so that the
    // test is known to reach blocks that are neither one conjunct nor the whole relation.
    let mut mixed = 0;
    // How many states had a star of two hubs or more.
    let mut starred = 0;
    // How many states had a star of two hubs that a conjunct of no leaf relates.
    let mut related = 0;
    // The names marked as having holes or a class ([`Conjuncts::gapped`]), drawn apart so that
    // the other draws stay as they were. Over 30 cases a star of two conjuncts, a tree of
    // difference constraints and bounds of two conjuncts or more, and one held back by a name
    // with holes come 1 to 27, 1 to 7 and 0 to 15 times (10 seeds), too few to assert;
    // [`the_counts_of_a_tree_of_differences_are_those_of_the_definition`] draws mostly
    // differences and counts the trees.
    let mut gr = Rng::new(seed.wrapping_add(0x6a95));
    for case in 0..30 {
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
                assert_eq!(c.set().len(), 1, "seed {seed} case {case}");
                assert!(c.blocks().all().next().is_none(), "seed {seed} case {case}");
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
                assert_eq!(
                    &got, gs,
                    "seed {seed} case {case}: the star of {x} after {log:#?}"
                );
            }
            for x in c.names() {
                assert_eq!(
                    c.star(x).is_some(),
                    stars.contains_key(x),
                    "seed {seed} case {case}: {x} after {log:#?}"
                );
            }
            assert_eq!(
                got,
                partition_by_definition(&c),
                "seed {seed} case {case} after {log:#?}"
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
            assert_eq!(fresh.set(), c.set(), "seed {seed} case {case}");
            assert_eq!(
                partition(&fresh),
                got,
                "seed {seed} case {case} afresh after {log:#?}"
            );
            for g in c.set() {
                assert!(names(g).iter().all(|n| c.mentioning(n).any(|h| h == g)));
            }
            differences_only_by_definition(&c, &gaps, &log, seed, case);
        }
    }
    // Over 10 seeds: mixed 227 to 287, starred 44 to 71, related 15 to 35; seeds 48 and 60 gave
    // related 3 and 4.
    assert!(mixed > 100, "seed {seed}: {mixed} states with mixed blocks");
    assert!(
        starred > 20,
        "seed {seed}: {starred} states with a star of two hubs"
    );
    assert!(
        related > 0,
        "seed {seed}: {related} states with a star of related hubs"
    );
}

#[test]
fn the_counts_of_a_tree_of_differences_are_those_of_the_definition() {
    // Mostly difference constraints and bounds, now and then another conjunct, added,
    // removed, swapped and forgotten, with names marked as having holes: each tree's counts
    // ([`zedc::store::conjuncts::Blocks::differences_only`]) say what the definition says.
    let (mut r, seed) = Rng::fresh("counts of a tree of differences");
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
    for case in 0..150 {
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
            let (a, h) = differences_only_by_definition(&c, &gaps, &log, seed, case);
            alone += usize::from(a);
            held += usize::from(h);
        }
    }
    // Over 10 seeds: alone 821 to 1002, held 352 to 460.
    assert!(
        alone > 400,
        "seed {seed}: {alone} states with a tree of differences alone"
    );
    assert!(
        held > 150,
        "seed {seed}: {held} states with a tree of differences and a name with holes"
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
    seed: u64,
    case: usize,
) -> (bool, bool) {
    let blocks = c.blocks();
    if let Err(e) = blocks.well_formed() {
        panic!("seed {seed} case {case}: the forest: {e} after {log:#?}");
    }
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
            "seed {seed} case {case}: the tree of {gs:?} after {log:#?}"
        );
        // A name inside a product of names is no node of the forest; its conjunct links it
        // through the product (`Blocks::shared`).
        for a in gs.iter().flat_map(|g| g.atoms()) {
            let Atom::Sym(n) = a else { continue };
            assert_eq!(
                blocks.tree_of_name(&n),
                Some(*t),
                "seed {seed} case {case}: {n}"
            );
            assert_eq!(
                c.differences_only_at(&n),
                want,
                "seed {seed} case {case}: {n}"
            );
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
    let (mut r, seed) = Rng::fresh("many conjuncts go at once");
    let mut many = 0;
    for case in 0..100 {
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
                "seed {seed} case {case} after {log:#?}"
            );
        }
    }
    // Over 10 seeds: 133 to 159.
    assert!(
        many > 60,
        "seed {seed}: {many} removals of three conjuncts or more"
    );
}

const PAIR_NAMES: [&str; 8] = ["a", "b", "c", "d", "e", "f", "g", "h"];

/// A random conjunct over [`PAIR_NAMES`], seventeen times in twenty a constraint on two names
/// and no other atom, which [`Blocks::remove`] takes out alone (`Blocks::cut`); otherwise a
/// bound on one name, a constraint on three names or fewer, or one with a product of two names.
fn pair_conjunct(r: &mut Rng) -> Formula {
    let x = r.pick(&PAIR_NAMES);
    let other = |r: &mut Rng| loop {
        let y = r.pick(&PAIR_NAMES);
        if y != x {
            break y;
        }
    };
    let sym = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let mut lin = Lin::constant(r.int(-3, 3)).plus(&sym(x));
    match r.below(20) {
        0 => {}
        1 => {
            let (y, z) = (other(r), r.pick(&PAIR_NAMES));
            lin = lin.plus(&sym(y).times(-1)).plus(&sym(z).times(2));
        }
        2 => {
            let y = other(r);
            lin = lin.plus(&Lin::atom(Atom::product(&x.into(), &y.into())));
        }
        _ => lin = lin.plus(&sym(other(r)).times(-1)),
    }
    Formula::Con(Con::ge(&lin, &Lin::constant(0)))
}

/// Mostly constraints on two names come and go, one at a time and several at once, in the
/// forest of blocks alone ([`Blocks`]): after each step the forest is well formed
/// ([`Blocks::well_formed`]), its blocks are those of the definition, and its trees are the
/// conjuncts linked by a name or another atom. One removal often splits a block in three
/// pieces or more (`Blocks::peel`) and a tree in two (`Blocks::bridge`).
#[test]
fn the_blocks_stay_those_of_the_definition_as_constraints_on_two_names_come_and_go() {
    let (mut r, seed) = Rng::fresh("constraints on two names come and go");
    // States where one removal split a block in three pieces or more, or split a tree, and
    // removals of several constraints on two names at once (196, 500 and 434 states).
    let (mut pieces, mut trees, mut several) = (0, 0, 0);
    for case in 0..40 {
        let mut b = Blocks::default();
        let mut set: BTreeSet<Arc<Formula>> = BTreeSet::new();
        let mut log: Vec<String> = Vec::new();
        for _ in 0..40 {
            let k = r.below(10);
            if k < 4 && !set.is_empty() {
                let gs: Vec<Arc<Formula>> = set.iter().cloned().collect();
                let gone: Vec<Arc<Formula>> = if k == 0 {
                    gs.into_iter().filter(|_| r.below(3) == 0).collect()
                } else {
                    vec![r.pick(&gs)]
                };
                let pair = |g: &Formula| {
                    let a = g.atoms();
                    a.len() == 2 && a.iter().all(|a| matches!(a, Atom::Sym(_)))
                };
                several += usize::from(gone.len() > 1 && gone.iter().all(|g| pair(g)));
                let mates: Vec<Arc<Formula>> = match &gone[..] {
                    [g] => b
                        .members(b.of(g).expect("a block"))
                        .filter(|h| *h != g)
                        .cloned()
                        .collect(),
                    _ => Vec::new(),
                };
                let tree_count = |b: &Blocks, gs: &mut dyn Iterator<Item = &Arc<Formula>>| {
                    gs.map(|g| b.tree(b.of(g).expect("a block")))
                        .collect::<BTreeSet<_>>()
                        .len()
                };
                let rest = || set.iter().filter(|g| !gone.contains(g));
                let before = tree_count(&b, &mut rest());
                log.push(format!("remove {gone:?}"));
                b.remove(&gone);
                let after = tree_count(&b, &mut rest());
                let split: BTreeSet<_> = mates.iter().map(|h| b.of(h)).collect();
                pieces += usize::from(split.len() > 2);
                trees += usize::from(gone.len() == 1 && after > before);
                for g in &gone {
                    set.remove(g);
                }
            } else {
                let g = Arc::new(pair_conjunct(&mut r));
                if set.insert(g.clone()) {
                    log.push(format!("add {g}"));
                    b.add(&g);
                }
            }
            if let Err(e) = b.well_formed() {
                panic!("seed {seed} case {case}: {e} after {log:#?}");
            }
            let gs: Vec<Arc<Formula>> = set.iter().cloned().collect();
            let mut got: BTreeMap<u64, BTreeSet<Arc<Formula>>> = BTreeMap::new();
            for g in &gs {
                let id = b.of(g).unwrap_or_else(|| panic!("{g} has no block"));
                got.entry(id).or_default().insert(g.clone());
            }
            for (id, ms) in &got {
                let members: BTreeSet<Arc<Formula>> = b.members(*id).cloned().collect();
                assert_eq!(
                    &members, ms,
                    "seed {seed} case {case}: block {id} after {log:#?}"
                );
            }
            assert_eq!(
                b.all().count(),
                got.len(),
                "seed {seed} case {case} after {log:#?}"
            );
            let want: BTreeSet<_> = blocks_by_definition(&gs).into_iter().collect();
            let got: BTreeSet<_> = got.into_values().collect();
            assert_eq!(got, want, "seed {seed} case {case} after {log:#?}");
            // The trees: the conjuncts linked by any atom they share.
            let mut comp: Vec<usize> = (0..gs.len()).collect();
            let mut first: BTreeMap<Atom, usize> = BTreeMap::new();
            for (i, g) in gs.iter().enumerate() {
                for a in g.atoms() {
                    let j = *first.entry(a).or_insert(i);
                    let (x, y) = (find(&mut comp, i), find(&mut comp, j));
                    comp[x] = y;
                }
            }
            let (mut tree_of, mut comp_of) = (BTreeMap::new(), BTreeMap::new());
            for (i, g) in gs.iter().enumerate() {
                let (c, t) = (find(&mut comp, i), b.tree(b.of(g).expect("a block")));
                assert_eq!(
                    *tree_of.entry(c).or_insert(t),
                    t,
                    "seed {seed} case {case}: {g}"
                );
                assert_eq!(
                    *comp_of.entry(t).or_insert(c),
                    c,
                    "seed {seed} case {case}: {g}"
                );
            }
        }
    }
    // Over 10 seeds: pieces 16 to 25, trees 34 to 57, several 37 to 52.
    assert!(
        pieces > 6,
        "seed {seed}: {pieces} removals that split a block in three"
    );
    assert!(
        trees > 15,
        "seed {seed}: {trees} removals that split a tree"
    );
    assert!(
        several > 15,
        "seed {seed}: {several} removals of several pairs at once"
    );
}

/// Random constraints on two names come and go as in the test above, and after each removal
/// the blocks the conjuncts of an earlier block went to ([`Blocks::now_of`]) and the names of
/// each block ([`Blocks::names_of`]) are those found by reading every conjunct: the block of
/// each conjunct of the earlier block that is still here, and the names its conjuncts mention.
/// Many removals take out a constraint whose two names another constraint of its block links
/// alone (`x - y >= 1` beside `x - y >= -2`), where the block stays whole without a search
/// (`Blocks::cut`), and many take out one with no such twin, where the block may split; both
/// are counted so that each is met, and the blocks after both are checked against those of
/// the definition by the test above.
#[test]
fn the_blocks_an_earlier_block_went_to_and_the_names_of_a_block_are_those_of_its_conjuncts() {
    let (mut r, seed) = Rng::fresh("blocks an earlier block went to");
    // Removals of a constraint on two names with a twin left in its block, and without one.
    let (mut twins, mut alone) = (0, 0);
    for case in 0..200 {
        let mut b = Blocks::default();
        let mut set: BTreeSet<Arc<Formula>> = BTreeSet::new();
        for step in 0..40 {
            if r.below(10) < 4 && !set.is_empty() {
                let gs: Vec<Arc<Formula>> = set.iter().cloned().collect();
                let gone: Vec<Arc<Formula>> = if r.below(4) == 0 {
                    gs.into_iter().filter(|_| r.below(3) == 0).collect()
                } else {
                    vec![r.pick(&gs)]
                };
                let old = b.clone();
                if let [g] = &gone[..] {
                    let two = |h: &Formula| {
                        let a = h.atoms();
                        (a.len() == 2 && a.iter().all(|a| matches!(a, Atom::Sym(_))))
                            .then(|| names(h))
                    };
                    if let Some(uv) = two(g) {
                        let ob = old.of(g).expect("a block");
                        if old
                            .members(ob)
                            .any(|h| h != g && two(h).as_ref() == Some(&uv))
                        {
                            twins += 1;
                        } else {
                            alone += 1;
                        }
                    }
                }
                b.remove(&gone);
                for g in &gone {
                    set.remove(g);
                }
                let lost: BTreeSet<u64> = gone.iter().filter_map(|g| old.of(g)).collect();
                for ob in lost {
                    let want: BTreeSet<u64> = old
                        .members(ob)
                        .filter(|h| set.contains(*h))
                        .map(|h| b.of(h).expect("a block"))
                        .collect();
                    assert_eq!(
                        b.now_of(&old, ob),
                        want,
                        "seed {seed} case {case} step {step}: block {ob}"
                    );
                }
            } else {
                let g = Arc::new(pair_conjunct(&mut r));
                if set.insert(g.clone()) {
                    b.add(&g);
                }
            }
            for id in b.all() {
                let want: BTreeSet<Arc<str>> = b.members(id).flat_map(|h| names(h)).collect();
                let got: BTreeSet<Arc<str>> = b.names_of(id).cloned().collect();
                assert_eq!(got, want, "seed {seed} case {case} step {step}: block {id}");
            }
        }
    }
    // Over 10 seeds: twins 189 to 245, alone 1837 to 1940.
    assert!(twins > 90, "seed {seed}: {twins} removals with a twin left");
    assert!(alone > 900, "seed {seed}: {alone} removals without one");
}

/// `x - y >= 0` as a conjunct.
fn at_least(x: &str, y: &str) -> Arc<Formula> {
    let lin = Lin::atom(Atom::Sym(x.into())).plus(&Lin::atom(Atom::Sym(y.into())).times(-1));
    Arc::new(Formula::Con(Con::ge(&lin, &Lin::constant(0))))
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

/// The chain `x_i - x_(i+1) >= 1` with every rung `x_i - x_(i+2) >= 2`: one block of 2k
/// difference constraints.
fn ladder(k: usize, p: &Premises) -> Scope {
    let (s, chain) = shape("chain", k);
    let n = named(k + 1, "x");
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, p));
    (0..k - 1).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 2], 2), true, p))
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
    assert_eq!(z.ints().len(), 2, "{z:?}");
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
    let (mut r, seed) = Rng::fresh("shortest paths block by block");
    let p = Premises::new();
    let (mut moved, mut empty) = (0, 0);
    for case in 0..20 {
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
                    "seed {seed} case {case} reverse {reverse} step {step}: {order:?}"
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
    // Over 10 seeds: moved 75 to 134, empty 12 to 26.
    assert!(moved > 30, "seed {seed}: {moved} steps moved an interval");
    assert!(empty > 4, "seed {seed}: {empty} ladders became empty");
}

#[test]
fn shortest_paths_with_holes_and_sums_between_give_the_projection_block_by_block() {
    // As above, with tests that leave a tree to the projection block by block between the
    // difference constraints: `x != c`, which gives `x` a hole until a bound closes it, and
    // `x + y >= c`, not a difference constraint. An edge that comes while its tree goes block
    // by block is in the potential before any later edge is read (`Scope::repair`).
    let (mut r, seed) = Rng::fresh("shortest paths with holes and sums");
    let p = Premises::new();
    let (mut moved, mut empty, mut holes) = (0, 0, 0);
    for case in 0..15 {
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
                    "seed {seed} case {case} reverse {reverse} step {step}: {order:?}"
                );
                moved += usize::from(intervals(&got, &ns) != before);
                holes += usize::from(ns.iter().any(|n| got.get(n).ints().len() > 1));
                if got.bottom {
                    empty += 1;
                    break;
                }
                s = got;
            }
        }
    }
    // Over 10 seeds: moved 129 to 168, empty 12 to 20, holes 92 to 161.
    assert!(moved > 60, "seed {seed}: {moved} steps moved an interval");
    assert!(empty > 4, "seed {seed}: {empty} ladders became empty");
    assert!(
        holes > 40,
        "seed {seed}: {holes} steps left a name with holes"
    );
}

/// Counts of [`holes_in_trees`]: tests that moved an interval, left a name with holes, left
/// two names or more with holes, or made the scope empty; pairs of inequalities that made a
/// cycle of weight 0; tests that joined both arms; trees drawn.
#[derive(Debug, Default)]
struct HoleCounts {
    trees: usize,
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
/// names of one tree. The trees of `seed` are checked and counted in turn until `enough` holds
/// of the counts: the counts of a few trees vary widely from seed to seed (piled, over 4 trees
/// of 300 seeds, 0 to 234), so a test asks for the cases it means to meet and draws trees
/// until they are met, rather than asserting them of a fixed number of trees. A change that
/// stops the trees from meeting them makes the test run past its time limit.
fn holes_in_trees(seed: u64, pile: bool, enough: impl Fn(&HoleCounts) -> bool) -> HoleCounts {
    let mut r = Rng::new(seed);
    let p = Premises::new();
    let mut out = HoleCounts::default();
    for case in 0.. {
        if enough(&out) {
            break;
        }
        out.trees += 1;
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
            let checks = asked.iter().flat_map(|h| [(h, true), (h, false)]);
            for (hole, holds) in checks {
                let got = s.assume(hole, holds, &p);
                let mut fresh = s.clone();
                fresh.forget_projections();
                let mut want = fresh.assume(hole, holds, &p);
                want.forget_projections();
                want.reduce();
                assert_eq!(
                    intervals(&got, &ns),
                    intervals(&want, &ns),
                    "seed {seed} case {case} step {step} {holds}: {hole:?} on {:?}",
                    s.relation
                );
                let holed = ns.iter().filter(|n| got.get(n).ints().len() > 1).count();
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

/// [`holes_in_trees`] without piling, on trees of a new seed each run, at least 4 and until
/// the counts are met. As one test of the 150 trees of seed 0x1e4e it took about 20 s alone at
/// load 23 to 25, and as three tests of 50 trees about 5 s each (item SPLIT-l01_39-linked);
/// those 150 trees counted moved 6096, holes 2330, empty 662, tied 77, joined 109. Each tree
/// has about one tied pair and one joined `if`, too few in a few trees to ask for a count.
/// 4 trees took 0.15 to 1.3 s alone at load 49 on 32 cores.
#[test]
fn holes_in_a_tree_of_differences_give_the_projection_from_scratch() {
    let (_, seed) = Rng::fresh("holes in a tree of differences");
    // Over 17 seeds, 4 trees each: moved 66 to 275, holes 15 to 137, empty 6 to 41.
    holes_in_trees(seed, false, met_without_piling);
}

/// At least 4 trees, and more than 30 tests that moved an interval, 6 that left a hole and 2
/// that made the scope empty.
fn met_without_piling(n: &HoleCounts) -> bool {
    n.trees >= 4 && n.moved > 30 && n.holes > 6 && n.empty > 2
}

/// As [`holes_in_a_tree_of_differences_give_the_projection_from_scratch`], with the holes piled
/// up in many names of each tree, on trees of a new seed each run, at least 4 and until the
/// counts are met (4 trees took 0.8 s at load 42). As one test of the 150 trees of seed 0x9a1e
/// it took about 22 s alone at load 23 to 25 (item SPLIT-l01_39-linked); those trees counted
/// moved 6773, holes 4803, piled 2296, empty 763, tied 45, joined 45.
#[test]
fn holes_piled_in_many_names_of_a_tree_give_the_projection_from_scratch() {
    let (_, seed) = Rng::fresh("holes piled in many names of a tree");
    holes_in_trees(seed, true, met_with_piling);
}

/// At least 4 trees, and more than 60 tests that moved an interval, 45 that left a hole, 10
/// that left holes in two names or more, and 3 that made the scope empty. Over 4 trees of each
/// of 300 seeds (1000 to 1299), 11 seeds met fewer: piled 0 to 9 in those, and 0 to 234 over
/// all, with holes 15 to 68 and moved 51 to 149 in the 11 (item FAIL-linked-piled-holes-count).
fn met_with_piling(n: &HoleCounts) -> bool {
    n.trees >= 4 && n.moved > 60 && n.holes > 45 && n.piled > 10 && n.empty > 3
}

/// The first 4 trees of `seed`, with piling, count `first` (moved, holes, piled, empty), short
/// of [`met_with_piling`], so a test that asserted the counts of 4 trees failed on it
/// (FAIL-linked-piled-holes-count); the trees after them meet the counts.
fn met_after_four_trees(seed: u64, first: [usize; 4]) {
    let n = holes_in_trees(seed, true, |n| n.trees == 4);
    assert_eq!([n.moved, n.holes, n.piled, n.empty], first, "{n:?}");
    let n = holes_in_trees(seed, true, met_with_piling);
    assert!(n.trees > 4 && met_with_piling(&n), "{n:?}");
}

/// Piled 9, where more than 10 are asked for.
#[test]
fn holes_piled_in_the_trees_of_seed_10423609239771793175() {
    met_after_four_trees(10423609239771793175, [130, 67, 9, 15]);
}

/// Empty 2, where more than 3 are asked for (found by FAIL-zir-text-reader-messages).
#[test]
fn holes_piled_in_the_trees_of_seed_12717323168360931590() {
    met_after_four_trees(12717323168360931590, [101, 62, 32, 2]);
}

/// Holes 42, where more than 45 are asked for (found by FAIL-bitword-arity-message).
#[test]
fn holes_piled_in_the_trees_of_seed_9834632220024286056() {
    met_after_four_trees(9834632220024286056, [112, 42, 13, 8]);
}

/// No holes piled at all, and holes 22, where more than 45 are asked for.
#[test]
fn holes_piled_in_the_trees_of_seed_1226() {
    met_after_four_trees(1226, [86, 22, 0, 9]);
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

/// Hubs `h0` to `hd`, leaves `ai >= hi && ai >= h(i+1)` of two hubs each, and a satellite `y`
/// with `y >= hi` for every hub ([`Conjuncts::star`]), its conjuncts added before the leaves'
/// (`first`) or after.
fn satellite_of_every_hub(d: usize, first: bool) -> Conjuncts {
    let ge = |a: &str, b: &str| {
        let s = |x: &str| Lin::atom(Atom::Sym(x.into()));
        Formula::Con(Con::ge(&s(a), &s(b)))
    };
    let leaves = (0..d).flat_map(|i| {
        let a = format!("a{i}");
        [ge(&a, &format!("h{i}")), ge(&a, &format!("h{}", i + 1))]
    });
    let satellite = (0..=d).map(|i| ge("y", &format!("h{i}")));
    let mut c = Conjuncts::default();
    if first {
        satellite.chain(leaves).for_each(|g| c.and(g));
    } else {
        leaves.chain(satellite).for_each(|g| c.and(g));
    }
    c
}

/// The conjuncts of [`satellite_of_every_hub`] at `d`, the leaves' and the satellite's, and
/// with `bounds` a bound `hi >= 0` on each hub too, which gives each hub more conjuncts than
/// its leaves while the satellite's conjuncts are missing, so that leaves become stars and stop
/// being stars as the satellite's conjuncts come and go.
fn satellite_conjuncts(d: usize, bounds: bool) -> Vec<Formula> {
    let s = |x: &str| Lin::atom(Atom::Sym(x.into()));
    let ge = |a: &str, b: &str| Formula::Con(Con::ge(&s(a), &s(b)));
    let leaves = (0..d).flat_map(|i| {
        let a = format!("a{i}");
        [ge(&a, &format!("h{i}")), ge(&a, &format!("h{}", i + 1))]
    });
    let satellite = (0..=d).map(|i| ge("y", &format!("h{i}")));
    let bounds = (0..=d)
        .filter(|_| bounds)
        .map(|i| Formula::Con(Con::ge(&s(&format!("h{i}")), &Lin::constant(0))));
    leaves.chain(satellite).chain(bounds).collect()
}

/// `0..n` in a random order drawn from `rng`.
fn shuffled(n: usize, rng: &mut Rng) -> Vec<usize> {
    let mut order: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        order.swap(i, rng.below(i + 1));
    }
    order
}

/// The conjuncts of [`satellite_conjuncts`] at `d` and `8d`, from [`scaling::inputs`], each with
/// a seeded random order to add them in and one to take them away in.
type SatelliteOrders = std::collections::HashMap<usize, (Vec<Formula>, Vec<usize>, Vec<usize>)>;

/// [`SatelliteOrders`] at `d` and `8d`.
fn satellite_orders(d: usize, bounds: bool) -> SatelliteOrders {
    scaling::inputs(d, |d| {
        let mut rng = Rng::new(d as u64);
        let gs = satellite_conjuncts(d, bounds);
        let (add, take) = (shuffled(gs.len(), &mut rng), shuffled(gs.len(), &mut rng));
        (gs, add, take)
    })
}

/// The conjuncts at `d` of `orders`, added in their order.
fn built(orders: &SatelliteOrders, d: usize) -> Conjuncts {
    let (gs, add, _) = &orders[&d];
    let mut c = Conjuncts::default();
    for &i in add {
        c.and(gs[i].clone());
    }
    c
}

/// Checks that building the conjuncts of [`satellite_conjuncts`] in a seeded random order at
/// `d` and `8d` is linear.
fn satellite_built_in_a_random_order(d: usize, bounds: bool) {
    let orders = satellite_orders(d, bounds);
    let what = format!("a satellite of every hub (bounds on the hubs: {bounds})");
    scaling::check(&format!("{what} built in a random order"), d, |d| {
        std::hint::black_box(built(&orders, d));
    });
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

/// The scope of integers `x0`, …, `x{k-1}`, each at least 0, and the tests
/// `x{i+1} - x{i} >= 1` in turn, a chain each of whose edges is put in against the order the
/// potential keeps its names in.
fn chain_against_the_order(k: usize) -> (Scope, Vec<Term>) {
    let n = named(k, "x");
    let low = n
        .iter()
        .map(|x| prim(Prim::Ge, var(x), int(0)))
        .reduce(super::nests::and);
    let s = ints(&n).assume(&low.expect("a name"), true, &Premises::new());
    let tests = (0..k - 1).map(|i| ge(&n[i + 1], &n[i], 1)).collect();
    (s, tests)
}

#[test]
fn a_chain_put_in_against_the_order_keeps_its_bounds_and_its_cycles() {
    // The chain of the test above, then `x0 - x{k-1} >= c`: at c = -(k - 1) the edge closes a
    // cycle of weight 0, which the search that ends first finds, merging the chain into one
    // component; at c = -(k - 2) the cycle is positive and the scope empty.
    let p = Premises::new();
    for k in [2, 3, 16] {
        let (s, tests) = chain_against_the_order(k);
        let s = tests.iter().fold(s, |s, t| s.assume(t, true, &p));
        let last = format!("x{}", k - 1);
        let bound = |s: &Scope| {
            s.names
                .get(last.as_str())
                .expect("the last name")
                .ints()
                .to_string()
        };
        assert!(!s.bottom, "k = {k}: {s}");
        assert_eq!(bound(&s), format!("[{}..]", k - 1), "k = {k}: {s}");
        let tied = s.assume(&ge("x0", &last, -(k as i64 - 1)), true, &p);
        assert!(!tied.bottom, "k = {k}: {tied}");
        assert_eq!(bound(&tied), format!("[{}..]", k - 1), "k = {k}: {tied}");
        let empty = s.assume(&ge("x0", &last, -(k as i64 - 2)), true, &p);
        assert!(empty.bottom, "k = {k}: {empty}");
    }
}

/// A satellite related to `d + 1` hubs, each a hub of leaves of two hubs: no leaf is a star,
/// as by the definition, and the needs held across the hubs stay within three per hub
/// ([`Conjuncts::needs_held`]). With bounds on the hubs, the satellite's conjuncts taken away
/// one by one make leaves stars as the definition says at each step. The time of building it
/// is `bench::a_satellite_of_every_hub_costs_its_related_names_once`.
#[test]
fn a_satellite_of_every_hub_costs_its_related_names_once() {
    for first in [true, false] {
        let c = satellite_of_every_hub(12, first);
        let stars = stars_by_definition(&c);
        for i in 0..12 {
            let a = format!("a{i}");
            assert_eq!(c.star(&a).is_some(), stars.contains_key(&*a), "{a} in {c}");
            assert!(c.star(&a).is_none(), "{a} in {c}");
        }
        for d in [12, 96] {
            let held = satellite_of_every_hub(d, first).needs_held();
            assert!(
                held <= 3 * (d + 1),
                "{held} names needed across {} hubs (satellite first: {first})",
                d + 1
            );
        }
        // The satellite's conjuncts taken away one by one, its anchor first, until its related
        // names fit the hubs of the last leaves, which become stars: as by the definition at
        // each step, and with bounds on the hubs, so that they have more conjuncts than a leaf.
        let mut c = satellite_of_every_hub(4, first);
        for i in 0..=4 {
            let h = Lin::atom(Atom::Sym(format!("h{i}").into()));
            c.and(Formula::Con(Con::ge(&h, &Lin::constant(0))));
        }
        let mut starred = 0;
        for i in 0..=4 {
            let stars = stars_by_definition(&c);
            let found: BTreeSet<Arc<str>> = c.stars().keys().cloned().collect();
            assert_eq!(found, stars.keys().cloned().collect(), "{c}");
            starred += found.len();
            let g = c.set().iter().find(|g| {
                let ns = names(g);
                ns.contains("y") && ns.contains(&*format!("h{i}"))
            });
            let g = g.cloned().expect("the satellite's conjunct");
            c.remove(&g);
        }
        let stars = stars_by_definition(&c);
        let found: BTreeSet<Arc<str>> = c.stars().keys().cloned().collect();
        assert_eq!(found, stars.keys().cloned().collect(), "{c}");
        assert!(starred + found.len() > 0, "no leaf became a star: {c}");
    }
}

/// Holes piled in the names of one chain, each held, with each rung an `if` whose arms join:
/// each name keeps its hole. The time is `bench::holes_piled_in_the_names_of_a_chain_take_
/// quadratic_time`.
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
}

/// A hole in every name of a grid of difference constraints: each name keeps its hole. The
/// time is `bench::holes_in_every_name_of_a_grid_take_time_m_cubed`.
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
}

/// `s` after each of `tests` as an `if` whose two arms are joined (taken by `assume_case` when
/// `case`, as the checker takes them), each step's intervals at `ns` checked against the same
/// step on the scope with its projections forgotten.
fn joined_as_from_scratch(
    s: &Scope,
    tests: &[Term],
    ns: &[Arc<str>],
    case: bool,
    what: &str,
) -> Scope {
    let p = Premises::new();
    let step = |s: &Scope, t: &Term| {
        let (yes, no) = if case {
            (s.assume_case(t, true, &p), s.assume_case(t, false, &p))
        } else {
            (s.assume(t, true, &p), s.assume(t, false, &p))
        };
        let mut j = yes.join(&no);
        j.reduce();
        j
    };
    tests.iter().enumerate().fold(s.clone(), |s, (i, t)| {
        let got = step(&s, t);
        let mut fresh = s.clone();
        fresh.forget_projections();
        let mut want = step(&fresh, t);
        want.forget_projections();
        want.reduce();
        assert_eq!(
            intervals(&got, ns),
            intervals(&want, ns),
            "{what}, test {i}: {t:?}"
        );
        got
    })
}

/// The point giving each name its value.
fn point(vs: &[(&str, i64)]) -> BTreeMap<Arc<str>, Value> {
    vs.iter().map(|&(n, v)| (n.into(), Value::Int(v))).collect()
}

/// Each shape of `bench::tests_assumed_one_by_one_on_one_linked_component_take_time_near_their_
/// number`, small: its tests assumed one by one give the intervals of the projection from
/// scratch, hold a point of the tests and leave out one that breaks a test.
#[test]
fn each_shape_assumed_one_by_one_keeps_its_points_and_its_projection() {
    let p = Premises::new();
    let xs = named(4, "x");
    let star: Vec<Arc<str>> = named(3, "y").into_iter().chain(["x".into()]).collect();
    // The shape, its names, a point it holds and a point it does not.
    let cases = [
        (
            "chain",
            &xs,
            point(&[("x0", 3), ("x1", 2), ("x2", 1), ("x3", 0)]),
            point(&[("x0", 0), ("x1", 0), ("x2", 0), ("x3", 0)]),
        ),
        (
            "bounded chain",
            &xs,
            point(&[("x0", 10), ("x1", 9), ("x2", 8), ("x3", 7)]),
            point(&[("x0", -1), ("x1", -2), ("x2", -3), ("x3", -4)]),
        ),
        (
            "star",
            &star,
            point(&[("y0", -1), ("y1", 0), ("y2", -5), ("x", 0)]),
            point(&[("y0", 1), ("y1", 0), ("y2", 0), ("x", 0)]),
        ),
        (
            "or chain",
            &xs,
            point(&[("x0", 0), ("x1", 1), ("x2", 0), ("x3", 1)]),
            point(&[("x0", 0), ("x1", 0), ("x2", 1), ("x3", 2)]),
        ),
    ];
    for (which, ns, holds, fails) in cases {
        let (s, ts) = shape(which, 3);
        let got = ts.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        let mut want = s;
        for t in &ts {
            want.forget_projections();
            want = want.assume(t, true, &p);
        }
        want.forget_projections();
        want.reduce();
        assert!(!got.bottom, "{which}: {got}");
        assert_eq!(intervals(&got, ns), intervals(&want, ns), "{which}");
        assert!(got.contains(&holds), "{which}: {got}");
        assert!(!got.contains(&fails), "{which}: {got}");
    }
}

/// The shape of `bench::a_constraint_taken_from_a_block_beside_a_name_of_many_blocks_takes_
/// time_near_the_block`, small: a name `h` in `d` blocks of one constraint, beside a block of
/// five that loses `a - b >= 0` and gets it back. After each step the forest is well formed
/// and its blocks are those of the definition.
#[test]
fn a_constraint_taken_from_a_block_beside_a_name_of_many_blocks_and_put_back_keeps_the_blocks() {
    let check = |b: &Blocks, gs: &[Arc<Formula>], when: &str| {
        if let Err(e) = b.well_formed() {
            panic!("{when}: {e}");
        }
        let mut got: BTreeMap<u64, BTreeSet<Arc<Formula>>> = BTreeMap::new();
        for g in gs {
            let id = b
                .of(g)
                .unwrap_or_else(|| panic!("{when}: {g} has no block"));
            got.entry(id).or_default().insert(g.clone());
        }
        for (id, ms) in &got {
            let members: BTreeSet<Arc<Formula>> = b.members(*id).cloned().collect();
            assert_eq!(&members, ms, "{when}: block {id}");
        }
        assert_eq!(b.all().count(), got.len(), "{when}");
        let want: BTreeSet<_> = blocks_by_definition(gs).into_iter().collect();
        assert_eq!(got.into_values().collect::<BTreeSet<_>>(), want, "{when}");
    };
    for d in 1..=3 {
        let mut b = Blocks::default();
        let mut gs: Vec<Arc<Formula>> = (0..d).map(|i| at_least("h", &format!("y{i}"))).collect();
        let ab = at_least("a", "b");
        gs.extend([
            at_least("h", "a"),
            ab.clone(),
            at_least("b", "h"),
            at_least("a", "x"),
            at_least("x", "b"),
        ]);
        for g in &gs {
            b.add(g);
        }
        check(&b, &gs, &format!("d = {d}, built"));
        let without: Vec<Arc<Formula>> = gs.iter().filter(|g| **g != ab).cloned().collect();
        for round in 0..2 {
            b.remove(std::slice::from_ref(&ab));
            check(&b, &without, &format!("d = {d}, round {round}, a - b gone"));
            b.add(&ab);
            check(&b, &gs, &format!("d = {d}, round {round}, a - b back"));
        }
    }
}

/// The joins of `bench::if_statements_joined_one_after_another_on_a_linked_chain_take_time_
/// near_their_number` on an unbounded chain, small: each step gives the projection from
/// scratch, and the chain stays.
#[test]
fn if_statements_joined_on_an_unbounded_chain_keep_the_chain() {
    let p = Premises::new();
    let (s, chain) = shape("chain", 4);
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
    let n = named(5, "x");
    let tests: Vec<Term> = (0..4).map(|i| ge(&n[i], &n[i + 1], 2)).collect();
    let r = joined_as_from_scratch(&s, &tests, &n, false, "joins on a chain");
    assert!(!r.bottom, "{r}");
    // Each join keeps x_i - x_{i+1} >= 1, which both arms hold.
    let at = |v: [i64; 5]| {
        point(&[
            ("x0", v[0]),
            ("x1", v[1]),
            ("x2", v[2]),
            ("x3", v[3]),
            ("x4", v[4]),
        ])
    };
    assert!(r.contains(&at([4, 3, 2, 1, 0])), "{r}");
    assert!(!r.contains(&at([0, 0, 0, 0, 0])), "{r}");
}

/// The map of `bench::a_nested_or_and_formula_is_built_and_mapped_in_time_near_its_size`, which
/// changes each constraint, small: the nest mapped holds where the nest of the mapped
/// constraints holds.
#[test]
fn a_nested_or_and_formula_mapped_is_the_nest_of_the_mapped_constraints() {
    let at = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let side = |n: &str| -> Vec<Formula> {
        (0..6)
            .map(|i| Formula::Con(Con::ge(&at(n), &Lin::constant(i))))
            .collect()
    };
    let (xs, ys) = (side("x"), side("y"));
    let shift = |c: &Con| Formula::Con(Con::ge(&c.lin, &Lin::constant(1)));
    let shifted = |fs: &[Formula]| -> Vec<Formula> {
        fs.iter()
            .map(|f| match f {
                Formula::Con(c) => shift(c),
                _ => unreachable!("{f}"),
            })
            .collect()
    };
    let got = nested(&xs, &ys).map_cons(&shift);
    let want = nested(&shifted(&xs), &shifted(&ys));
    for x in -8..9i64 {
        for y in -8..9i64 {
            let model = [
                (Atom::Sym("x".into()), x.into()),
                (Atom::Sym("y".into()), y.into()),
            ]
            .into();
            assert_eq!(
                got.holds(&model),
                want.holds(&model),
                "({x}, {y}): {got} against {want}"
            );
        }
    }
}

/// The test of `bench::one_test_on_a_ladder_takes_time_near_its_size`, small, implied and not:
/// the intervals are those of the projection from scratch.
#[test]
fn one_test_on_a_ladder_gives_the_intervals_of_the_projection() {
    let p = Premises::new();
    let n = named(4, "x");
    let s = ladder(3, &p);
    assert!(!s.bottom, "{s}");
    // x0 - x3 >= 3 is implied by the chain; >= 4 and >= 7 are not.
    for c in [3, 4, 7] {
        let got = s.assume(&ge("x0", "x3", c), true, &p);
        let mut fresh = s.clone();
        fresh.forget_projections();
        let mut want = fresh.assume(&ge("x0", "x3", c), true, &p);
        want.forget_projections();
        want.reduce();
        assert!(!got.bottom, "c = {c}: {got}");
        assert_eq!(intervals(&got, &n), intervals(&want, &n), "c = {c}");
        let at = point(&[("x0", 3), ("x1", 2), ("x2", 1), ("x3", 0)]);
        assert_eq!(got.contains(&at), c <= 3, "c = {c}: {got}");
    }
}

/// The ladder of `bench::a_ladder_grown_by_k_if_statements_is_linear`, small, in either order:
/// each step gives the projection from scratch, and the rungs hold.
#[test]
fn a_ladder_grown_by_if_statements_in_either_order_gives_the_projection() {
    let p = Premises::new();
    let (s, chain) = shape("chain", 4);
    let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
    let n = named(5, "x");
    let at = |v: [i64; 5]| {
        point(&[
            ("x0", v[0]),
            ("x1", v[1]),
            ("x2", v[2]),
            ("x3", v[3]),
            ("x4", v[4]),
        ])
    };
    for reverse in [false, true] {
        let mut tests: Vec<Term> = (0..3).map(|i| ge(&n[i], &n[i + 2], 2)).collect();
        if reverse {
            tests.reverse();
        }
        let r = joined_as_from_scratch(&s, &tests, &n, false, &format!("reverse {reverse}"));
        assert!(!r.bottom, "{r}");
        assert!(r.contains(&at([4, 3, 2, 1, 0])), "reverse {reverse}: {r}");
        assert!(!r.contains(&at([1, 0, 0, 0, 0])), "reverse {reverse}: {r}");
    }
}

/// The ladder of `bench::if_statements_that_leave_a_ladder_block_by_block_between_rungs_are_
/// linear`, small: each `if` on a sum and each rung gives the projection from scratch, and the
/// chain still bounds each name from x0.
#[test]
fn if_statements_that_leave_a_ladder_block_by_block_give_the_projection() {
    let p = Premises::new();
    let k = 3;
    let n = named(k + 1, "x");
    let w = named(k, "w");
    let all = [n.clone(), w.clone()].concat();
    let s = ints(&all)
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
    let r = joined_as_from_scratch(&s, &tests, &all, false, "sums between rungs");
    assert!(!r.bottom, "{r}");
    // Each x_i is at most x0 - i, so at most 10^9 - i.
    assert_eq!(r.get("x3").ints().to_string(), "[..=999999997]", "{r}");
}

/// The boxed ladder of `bench::if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_
/// linear`, small: each hole and each rung, taken as the checker takes them, gives the
/// projection from scratch, and the join of the arms gives each name its box back.
#[test]
fn holes_put_in_a_ladder_between_rungs_keep_each_box() {
    let p = Premises::new();
    let k = 3;
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
    let r = joined_as_from_scratch(&s, &tests, &n, true, "holes between rungs");
    assert!(!r.bottom, "{r}");
    for (i, x) in n.iter().enumerate() {
        assert_eq!(
            r.get(x).ints(),
            &zedc::store::interval::IntervalSet::range(End::of(base(i)), End::of(base(i) + 9)),
            "x{i}: {r}"
        );
    }
}

/// The ladder of `bench::holes_put_in_a_ladder_built_first_are_linear`, small, the holes in
/// either order: each step gives the projection from scratch, and each name keeps its box.
#[test]
fn holes_put_in_a_ladder_built_first_keep_each_box() {
    let p = Premises::new();
    let k = 3;
    let n = named(k + 1, "x");
    let base = |i: usize| (10 * (k - i)) as i64;
    let s = (0..=k).fold(ints(&n), |s, i| {
        s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, &p)
            .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, &p)
    });
    let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
    let s = (0..k - 1).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 2], 2), true, &p));
    for reverse in [false, true] {
        let mut tests: Vec<Term> = (0..=k)
            .map(|i| prim(Prim::Ne, var(&n[i]), int(base(i) + 5)))
            .collect();
        if reverse {
            tests.reverse();
        }
        let r = joined_as_from_scratch(&s, &tests, &n, true, &format!("reverse {reverse}"));
        assert!(!r.bottom, "{r}");
        for (i, x) in n.iter().enumerate() {
            assert_eq!(
                r.get(x).ints(),
                &zedc::store::interval::IntervalSet::range(End::of(base(i)), End::of(base(i) + 9)),
                "reverse {reverse}, x{i}: {r}"
            );
        }
    }
}

/// The chain of `bench::a_chain_linked_from_a_source_made_later_is_linear`, small: pinned
/// names `u` and `v` made after the chain, linked into its head, and the chain's `if`
/// statements joined. The order u >= v >= x0 >= … stays.
#[test]
fn a_chain_linked_from_a_source_made_later_keeps_its_order() {
    let p = Premises::new();
    let k = 3;
    let n = named(k + 1, "x");
    let mut s = ints(&[n.clone(), vec!["u".into(), "v".into()]].concat());
    s.relation.pin(&"u".into(), true);
    s.relation.pin(&"v".into(), true);
    let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
    let s = s
        .assume(&ge("u", "v", 0), true, &p)
        .assume(&ge("v", "x0", 0), true, &p);
    assert!(!s.bottom, "{s}");
    let r = (0..k).fold(s, |s, i| {
        let t = ge(&n[i], &n[i + 1], 2);
        let mut j = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
        j.reduce();
        j
    });
    assert!(!r.bottom, "{r}");
    let at = |u, v| {
        point(&[
            ("x0", 3),
            ("x1", 2),
            ("x2", 1),
            ("x3", 0),
            ("u", u),
            ("v", v),
        ])
    };
    assert!(r.contains(&at(5, 4)), "{r}");
    assert!(!r.contains(&at(4, 5)), "u >= v: {r}");
    assert!(!r.contains(&at(5, 2)), "v >= x0: {r}");
}

/// The satellite of `bench::stars_formed_in_the_block_of_a_satellite_take_time_near_the_block`,
/// small, built in a seeded random order and taken apart in another: after each step the
/// stars and the blocks are those of the definition.
#[test]
fn stars_formed_in_the_block_of_a_satellite_in_a_random_order_are_those_of_the_definition() {
    for d in 2..=4 {
        let orders = satellite_orders(d, true);
        let mut c = built(&orders, d);
        let (gs, _, take) = &orders[&d];
        let check = |c: &Conjuncts, when: &str| {
            let found: BTreeSet<Arc<str>> = c.stars().keys().cloned().collect();
            assert_eq!(
                found,
                stars_by_definition(c).keys().cloned().collect(),
                "d = {d}, {when}: {c}"
            );
            assert_eq!(
                partition(c),
                partition_by_definition(c),
                "d = {d}, {when}: {c}"
            );
        };
        check(&c, "built");
        let set: Vec<Arc<Formula>> = c.set().iter().cloned().collect();
        assert_eq!(set.len(), gs.len(), "d = {d}: {c}");
        for (step, &i) in take.iter().enumerate() {
            c.remove(&set[i]);
            check(&c, &format!("step {step}"));
        }
    }
}

mod bench;
