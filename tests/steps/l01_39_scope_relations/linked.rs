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
use zedc::store::interval::{End, IntervalSet};
use zedc::store::presburger::{Atom, Con, Factor, Formula, Lin, Rel, Shared};
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

/// The blocks of the conjuncts `gs`, stars left aside, by brute force: those that share an
/// atom other than a name are one group, and two groups are in one block when no single name
/// separates them in the graph of groups and the names they mention as atoms of their own.
fn blocks_by_definition(gs: &[Arc<Formula>]) -> Vec<BTreeSet<Arc<Formula>>> {
    let n = gs.len();
    // Halving with rank (the root that stays is rank's): O(α(n)) amortized a step, Tarjan and van
    // Leeuwen 1984 (doi:10.1145/62.2160), Theorem 3; halving walks the path once.
    let mut group =
        zed_graph::UnionFind::new(n, zed_graph::Compression::Halving, zed_graph::Linking::Rank);
    let atoms: Vec<BTreeSet<Atom>> = gs.iter().map(|g| g.atoms()).collect();
    for i in 0..n {
        for j in 0..i {
            if atoms[i]
                .iter()
                .any(|a| !matches!(a, Atom::Sym(_)) && atoms[j].contains(a))
            {
                group.union(i, j);
            }
        }
    }
    let group: Vec<usize> = (0..n).map(|i| group.find(i)).collect();
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
    // How many states were of each kind of [`BLOCK_KINDS`].
    let mut met = [0; 3];
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
            let at = format!("seed {seed} case {case}");
            for (n, k) in met.iter_mut().zip(blocks_checked(&c, &gaps, &log, &at)) {
                *n += usize::from(k);
            }
        }
    }
    eprintln!("seed {seed}: mixed, starred, related {met:?}");
    block_kinds_met();
}

/// What [`blocks_checked`] tells apart: a state with a block of several conjuncts beside
/// another block, so that blocks are neither one conjunct nor the whole relation; one with a
/// star of two hubs or more; and one with a star of two hubs that a conjunct of no leaf
/// relates.
const BLOCK_KINDS: [&str; 3] = ["mixed", "starred", "related"];

/// Checks the blocks and stars of `c`, whose names of `gaps` have holes, against their
/// definitions, and those of the same conjuncts added afresh in the reverse order (`at` and
/// `log` name the state in a failure): which kinds of [`BLOCK_KINDS`] the state is.
fn blocks_checked(c: &Conjuncts, gaps: &BTreeSet<Arc<str>>, log: &[String], at: &str) -> [bool; 3] {
    let got = partition(c);
    let mixed = got.len() > 1 && got.iter().any(|b| b.len() > 1);
    let stars = stars_by_definition(c);
    let starred = stars.values().any(|gs| {
        gs.iter()
            .flat_map(|g| names(g))
            .collect::<BTreeSet<_>>()
            .len()
            > 2
    });
    let related = stars.iter().any(|(x, gs)| {
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
    });
    for (x, gs) in &stars {
        let b = c
            .star(x)
            .unwrap_or_else(|| panic!("{x} is a star's leaf after {log:#?}"));
        let got: BTreeSet<Arc<Formula>> = c.blocks().members(b).cloned().collect();
        assert_eq!(&got, gs, "{at}: the star of {x} after {log:#?}");
    }
    for x in c.names() {
        assert_eq!(
            c.star(x).is_some(),
            stars.contains_key(x),
            "{at}: {x} after {log:#?}"
        );
    }
    assert_eq!(got, partition_by_definition(c), "{at} after {log:#?}");
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
    assert_eq!(fresh.set(), c.set(), "{at}");
    assert_eq!(partition(&fresh), got, "{at} afresh after {log:#?}");
    for g in c.set() {
        assert!(names(g).iter().all(|n| c.mentioning(n).any(|h| h == g)));
    }
    differences_only_by_definition(c, gaps, log, at);
    [mixed, starred, related]
}

/// The conjuncts built to give each kind of [`BLOCK_KINDS`], checked in every run whatever
/// the drawn states gave, so that no count of the draws is relied on
/// (PROOF-test-count-thresholds; until 2026-11-15 the test asserted more than 100 mixed, 20
/// starred and 1 related states over its 30 cases): `c - a - b >= 0`, `a >= 0`, `b >= 0`,
/// `a - b >= 0`, `d - e >= 0` and `e - d + 3 >= 0`. The name `c` is a star's leaf with the
/// hubs `a` and `b` ([`stars_by_definition`]): no constraint is written of it, its one
/// conjunct is a constraint `>= 0` of names alone, with `c` of sign + and each hub of sign -,
/// each hub has three conjuncts, more than its one, it is unbounded, and each other conjunct
/// of a hub is of the hub alone or of the other hub. So the star has three names (starred),
/// and `a - b >= 0`, the conjunct of no leaf, relates its two hubs (related). The two
/// conjuncts of `d` and `e` are one block, since no single name separates them, and not a
/// star, since each has `d` (and `e`) of both signs; beside it lie the other blocks (mixed).
fn block_kinds_met() {
    let sym = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let at_least = |l: Lin| Formula::Con(Con::ge(&l, &Lin::constant(0)));
    let gs = [
        at_least(sym("c").minus(&sym("a")).minus(&sym("b"))),
        at_least(sym("a")),
        at_least(sym("b")),
        at_least(sym("a").minus(&sym("b"))),
        at_least(sym("d").minus(&sym("e"))),
        at_least(sym("e").minus(&sym("d")).plus(&Lin::constant(3))),
    ];
    let mut c = Conjuncts::default();
    let mut log = Vec::new();
    for g in gs {
        log.push(format!("and {g}"));
        c.and(g);
    }
    let met = blocks_checked(&c, &BTreeSet::new(), &log, "the built conjuncts");
    for (kind, m) in BLOCK_KINDS.iter().zip(met) {
        assert!(
            m,
            "the built conjuncts give no {kind} state: {met:?} after {log:#?}"
        );
    }
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
            let (a, h) = differences_only_by_definition(
                &c,
                &gaps,
                &log,
                &format!("seed {seed} case {case}"),
            );
            alone += usize::from(a);
            held += usize::from(h);
        }
    }
    eprintln!("seed {seed}: {alone} states with a tree of differences alone, {held} held back");
    differences_kinds_met();
}

/// The tree built to give each state [`differences_only_by_definition`] tells apart, checked
/// in every run whatever the drawn states gave, so that no count of the draws is relied on
/// (PROOF-test-count-thresholds; until 2026-11-15 the test asserted more than 400 states with a
/// tree of differences alone and 150 with one held back over its 150 cases): `a - b >= 0` and
/// `b - a >= -3` are two difference constraints ([`edges`]) of one block, since no single name
/// separates them, and in no star, since each of `a` and `b` has both signs in them; so they
/// are one tree of two conjuncts outside every star. With no name marked as having holes the
/// tree holds differences only (alone); once `a` is marked, the same tree of two difference
/// constraints holds a name with holes (held). (A path `a - b >= 0`, `b - c >= 0` will not do:
/// `a` and `c` are leaves of stars of the hub `b`, which leave their conjuncts apart.)
fn differences_kinds_met() {
    let mut c = Conjuncts::default();
    let mut log = Vec::new();
    for g in [diff("a", "b", 0), diff("b", "a", -3)] {
        log.push(format!("and {g}"));
        c.and(g);
    }
    let (alone, _) = differences_only_by_definition(&c, &BTreeSet::new(), &log, "the built tree");
    assert!(
        alone,
        "the built tree of differences is not alone: {log:#?}"
    );
    let a: Arc<str> = "a".into();
    c.gapped(&a, true);
    log.push("gap a true".into());
    let gaps = BTreeSet::from([a]);
    let (_, held) = differences_only_by_definition(&c, &gaps, &log, "the built tree, a gapped");
    assert!(
        held,
        "the built tree of differences is not held back by a: {log:#?}"
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
    at: &str,
) -> (bool, bool) {
    let blocks = c.blocks();
    if let Err(e) = blocks.well_formed() {
        panic!("{at}: the forest: {e} after {log:#?}");
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
            "{at}: the tree of {gs:?} after {log:#?}"
        );
        // A name inside a product of names is no node of the forest; its conjunct links it
        // through the product (`Blocks::shared`).
        for a in gs.iter().flat_map(|g| g.atoms()) {
            let Atom::Sym(n) = a else { continue };
            assert_eq!(blocks.tree_of_name(&n), Some(*t), "{at}: {n}");
            assert_eq!(c.differences_only_at(&n), want, "{at}: {n}");
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
    eprintln!("seed {seed}: {many} removals of three conjuncts or more");
    // The draws may take out no three conjuncts at once, so the conjuncts built below lose
    // three in one removal in every run (PROOF-test-count-thresholds; until 2026-11-15 the test
    // asserted more than 60 such removals over its 100 cases). The cycle `a - b >= 0`,
    // `b - c >= 0`, `c - d >= 0`, `d - a >= 0` is one block, since no single name separates
    // its conjuncts; beside it `e - f >= 0`. The first three of the five, in the order of the
    // set, go at once, and `a - b >= 1 || e - f >= 2` takes their place.
    let mut c = Conjuncts::default();
    for (x, y) in [("a", "b"), ("b", "c"), ("c", "d"), ("d", "a"), ("e", "f")] {
        c.and(diff(x, y, 0));
    }
    let gone: Vec<Arc<Formula>> = c.set().iter().take(3).cloned().collect();
    assert_eq!(gone.len(), 3, "the built conjuncts: {:?}", c.set());
    c.swap(
        &gone,
        Formula::or(vec![diff("a", "b", 1), diff("e", "f", 2)]),
    );
    assert_eq!(
        partition(&c),
        partition_by_definition(&c),
        "the built conjuncts after three of them went: {:?}",
        c.set()
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
    // Removals of each kind of [`PAIR_KINDS`].
    let mut met = [0; 3];
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
                let kinds = pairs_removed(&mut b, &mut set, &gone, &mut log);
                for (n, k) in met.iter_mut().zip(kinds) {
                    *n += usize::from(k);
                }
            } else {
                let g = Arc::new(pair_conjunct(&mut r));
                if set.insert(g.clone()) {
                    log.push(format!("add {g}"));
                    b.add(&g);
                }
            }
            pairs_checked(&b, &set, &log, &format!("seed {seed} case {case}"));
        }
    }
    eprintln!("seed {seed}: pieces, trees, several {met:?}");
    pair_kinds_met();
}

/// The removals [`pairs_removed`] tells apart: one removal that split a block in three pieces
/// or more, one that split a tree, and a removal of several constraints on two names at once.
const PAIR_KINDS: [&str; 3] = ["pieces", "trees", "several"];

/// Takes `gone` out of the forest `b` and the set `set` of its conjuncts: which kinds of
/// [`PAIR_KINDS`] the removal is.
fn pairs_removed(
    b: &mut Blocks,
    set: &mut BTreeSet<Arc<Formula>>,
    gone: &[Arc<Formula>],
    log: &mut Vec<String>,
) -> [bool; 3] {
    let pair = |g: &Formula| {
        let a = g.atoms();
        a.len() == 2 && a.iter().all(|a| matches!(a, Atom::Sym(_)))
    };
    let several = gone.len() > 1 && gone.iter().all(|g| pair(g));
    let mates: Vec<Arc<Formula>> = match gone {
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
    let before = tree_count(b, &mut rest());
    log.push(format!("remove {gone:?}"));
    b.remove(gone);
    let after = tree_count(b, &mut rest());
    let split: BTreeSet<_> = mates.iter().map(|h| b.of(h)).collect();
    let pieces = split.len() > 2;
    let trees = gone.len() == 1 && after > before;
    for g in gone {
        set.remove(g);
    }
    [pieces, trees, several]
}

/// Checks that the forest `b` of the conjuncts `set` is well formed, that its blocks are those
/// of the definition, and that its trees are the conjuncts linked by any atom they share (`at`
/// and `log` name the state in a failure).
fn pairs_checked(b: &Blocks, set: &BTreeSet<Arc<Formula>>, log: &[String], at: &str) {
    if let Err(e) = b.well_formed() {
        panic!("{at}: {e} after {log:#?}");
    }
    let gs: Vec<Arc<Formula>> = set.iter().cloned().collect();
    let mut got: BTreeMap<u64, BTreeSet<Arc<Formula>>> = BTreeMap::new();
    for g in &gs {
        let id = b.of(g).unwrap_or_else(|| panic!("{g} has no block"));
        got.entry(id).or_default().insert(g.clone());
    }
    for (id, ms) in &got {
        let members: BTreeSet<Arc<Formula>> = b.members(*id).cloned().collect();
        assert_eq!(&members, ms, "{at}: block {id} after {log:#?}");
    }
    assert_eq!(b.all().count(), got.len(), "{at} after {log:#?}");
    let want: BTreeSet<_> = blocks_by_definition(&gs).into_iter().collect();
    let got: BTreeSet<_> = got.into_values().collect();
    assert_eq!(got, want, "{at} after {log:#?}");
    // The trees: the conjuncts linked by any atom they share.
    // Halving with rank (the root that stays is rank's): O(α(n)) amortized a step, Tarjan and van
    // Leeuwen 1984 (doi:10.1145/62.2160), Theorem 3; halving walks the path once.
    let mut comp = zed_graph::UnionFind::new(
        gs.len(),
        zed_graph::Compression::Halving,
        zed_graph::Linking::Rank,
    );
    let mut first: BTreeMap<Atom, usize> = BTreeMap::new();
    for (i, g) in gs.iter().enumerate() {
        for a in g.atoms() {
            let j = *first.entry(a).or_insert(i);
            comp.union(i, j);
        }
    }
    let (mut tree_of, mut comp_of) = (BTreeMap::new(), BTreeMap::new());
    for (i, g) in gs.iter().enumerate() {
        let (c, t) = (comp.find(i), b.tree(b.of(g).expect("a block")));
        assert_eq!(*tree_of.entry(c).or_insert(t), t, "{at}: {g}");
        assert_eq!(*comp_of.entry(t).or_insert(c), c, "{at}: {g}");
    }
}

/// The removals built to give each kind of [`PAIR_KINDS`], checked in every run whatever the
/// drawn removals gave, so that no count of the draws is relied on
/// (PROOF-test-count-thresholds; until 2026-11-15 the test asserted more than 6, 15 and 15
/// removals of the three kinds over its 40 cases). The cycle `a - b >= 0`, `b - c >= 0`,
/// `c - d >= 0`, `d - a >= 0` is one block, since no single name separates two of its
/// conjuncts. Taking out `a - b >= 0` leaves the path `b - c`, `c - d`, `d - a`, where `c`
/// separates the first from the second and `d` the second from the third: three blocks
/// (pieces). Taking out `c - d >= 0` then leaves `b - c` and `d - a`, which share no atom:
/// two trees where there was one (trees). Taking out those two at once is a removal of
/// several constraints on two names (several).
fn pair_kinds_met() {
    let (mut b, mut set, mut log) = (Blocks::default(), BTreeSet::new(), Vec::new());
    for (x, y) in [("a", "b"), ("b", "c"), ("c", "d"), ("d", "a")] {
        let g = at_least(x, y);
        log.push(format!("add {g}"));
        b.add(&g);
        set.insert(g);
    }
    pairs_checked(&b, &set, &log, "the built cycle");
    let removals = [
        vec![at_least("a", "b")],
        vec![at_least("c", "d")],
        vec![at_least("b", "c"), at_least("d", "a")],
    ];
    for (i, gone) in removals.iter().enumerate() {
        let kinds = pairs_removed(&mut b, &mut set, gone, &mut log);
        pairs_checked(&b, &set, &log, &format!("the built removal {i}"));
        assert!(
            kinds[i],
            "the built removal {i} is not of the kind {}: {kinds:?} after {log:#?}",
            PAIR_KINDS[i]
        );
    }
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
                let at = format!("seed {seed} case {case} step {step}");
                let (twin, lone) = removed_with_twins(&mut b, &mut set, &gone, &at);
                twins += usize::from(twin);
                alone += usize::from(lone);
            } else {
                let g = Arc::new(pair_conjunct(&mut r));
                if set.insert(g.clone()) {
                    b.add(&g);
                }
            }
            names_checked(&b, &format!("seed {seed} case {case} step {step}"));
        }
    }
    eprintln!("seed {seed}: {twins} removals with a twin left, {alone} without one");
    twin_kinds_met();
}

/// Takes `gone` out of the forest `b` and the set `set` of its conjuncts, and checks the
/// blocks each earlier block of `gone` went to ([`Blocks::now_of`]) against the blocks of its
/// conjuncts still here (`at` names the state in a failure): whether the removal is of one
/// constraint on two names with a twin, a constraint on the same two names, left in its block,
/// and whether it is of one with no twin.
fn removed_with_twins(
    b: &mut Blocks,
    set: &mut BTreeSet<Arc<Formula>>,
    gone: &[Arc<Formula>],
    at: &str,
) -> (bool, bool) {
    let old = b.clone();
    let (mut twin, mut alone) = (false, false);
    if let [g] = gone {
        let two = |h: &Formula| {
            let a = h.atoms();
            (a.len() == 2 && a.iter().all(|a| matches!(a, Atom::Sym(_)))).then(|| names(h))
        };
        if let Some(uv) = two(g) {
            let ob = old.of(g).expect("a block");
            twin = old
                .members(ob)
                .any(|h| h != g && two(h).as_ref() == Some(&uv));
            alone = !twin;
        }
    }
    b.remove(gone);
    for g in gone {
        set.remove(g);
    }
    let lost: BTreeSet<u64> = gone.iter().filter_map(|g| old.of(g)).collect();
    for ob in lost {
        let want: BTreeSet<u64> = old
            .members(ob)
            .filter(|h| set.contains(*h))
            .map(|h| b.of(h).expect("a block"))
            .collect();
        assert_eq!(b.now_of(&old, ob), want, "{at}: block {ob}");
    }
    (twin, alone)
}

/// Checks that the names of each block of `b` ([`Blocks::names_of`]) are those its conjuncts
/// mention (`at` names the state in a failure).
fn names_checked(b: &Blocks, at: &str) {
    for id in b.all() {
        let want: BTreeSet<Arc<str>> = b.members(id).flat_map(|h| names(h)).collect();
        let got: BTreeSet<Arc<str>> = b.names_of(id).cloned().collect();
        assert_eq!(got, want, "{at}: block {id}");
    }
}

/// The removals built to give a removal with a twin left and one without, checked in every
/// run whatever the drawn removals gave, so that no count of the draws is relied on
/// (PROOF-test-count-thresholds; until 2026-11-15 the test asserted more than 90 and 900 such
/// removals over its 200 cases). `x - y >= 0` and `x - y + 2 >= 0` are constraints on the same
/// two names, so one block holds both. Taking out the first leaves the second, its twin, in
/// that block; taking out the second then leaves no constraint on `x` and `y`.
fn twin_kinds_met() {
    let first = at_least("x", "y");
    let sym = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let second = Arc::new(Formula::Con(Con::ge(
        &sym("x").minus(&sym("y")).plus(&Lin::constant(2)),
        &Lin::constant(0),
    )));
    let (mut b, mut set) = (Blocks::default(), BTreeSet::new());
    for g in [&first, &second] {
        b.add(g);
        set.insert(g.clone());
    }
    names_checked(&b, "the built twins");
    let got = removed_with_twins(&mut b, &mut set, &[first], "the built twins, first out");
    assert_eq!(
        got,
        (true, false),
        "the first built removal has no twin left"
    );
    names_checked(&b, "the built twins, first out");
    let got = removed_with_twins(&mut b, &mut set, &[second], "the built twins, second out");
    assert_eq!(
        got,
        (false, true),
        "the second built removal has a twin left"
    );
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
fn a_compound_disjunct_and_its_negation_are_true() {
    // `(x >= y + 3 && y >= z) || !(x >= y + 3 && y >= z)` holds at every point, and the
    // compound `g` is looked up by the hash kept in its node (`Formula::complementary`,
    // PRES-again-monotone), as a disjunction `g` is too.
    let g = Formula::and(vec![diff("x", "y", 3), diff("y", "z", 0)]);
    let not_g = Formula::negate(g.clone());
    assert_eq!(
        Formula::or(vec![g.clone(), not_g.clone(), diff("z", "w", 0)]),
        Formula::and(vec![])
    );
    let h = Formula::or(vec![diff("x", "y", 3), diff("y", "z", 0)]);
    let not_h = Formula::negate(h.clone());
    assert_eq!(Formula::or(vec![not_h, h]), Formula::and(vec![]));
    // A compound disjunct beside the negation of another compound stays a disjunction.
    let other = Formula::and(vec![diff("x", "y", 4), diff("y", "z", 0)]);
    assert_eq!(
        Formula::or(vec![other.clone(), not_g.clone()]),
        Formula::Or(Shared::new(vec![other, not_g]))
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
    let (_, seed) = Rng::fresh("shortest paths block by block");
    let met = random_ladders(seed);
    // Over 10 seeds: moved 75 to 134, empty 12 to 26. A kind the 20 ladders missed is met by
    // the ladder built for it, so no count of ladders is relied on
    // (PROOF-test-coverage-constructive; until 2026-11-15 the counts were held above 30 and 4).
    eprintln!("seed {seed}: moved, empty, holes {met:?}");
    ladder_kinds_met(&met[..2]);
}

/// The 20 random ladders of `seed` of the test above, each checked by [`ladder_checked`]: the
/// counts of [`LADDER_KINDS`] over them.
fn random_ladders(seed: u64) -> [usize; 3] {
    let mut r = Rng::new(seed);
    let p = Premises::new();
    let mut met = [0usize; 3];
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
        let m = ladder_checked(&ns, &tests, &p, &format!("seed {seed} case {case}"));
        for (n, x) in met.iter_mut().zip(m) {
            *n += x;
        }
    }
    met
}

#[test]
fn an_edge_on_two_negative_cycles_empties_the_scope_whichever_side_finds_one() {
    // Item PROOF-put-in-repair-direction. `x2` has the holes 0 and 1 within -2..=4, so the
    // edges into it are lowered by the gap 2. The last test, `x0 - x1 >= 3`, closes two
    // cycles: through `x2`, of weight 0 without the gap and -2 with it, and through `x3`, of
    // weight -4. The search forward from `x1` reaches the first, the one backward from `x0`
    // the second (found by a search over the weights of such a square). Until the repair
    // asked whether any cycle is negative without the gaps, the forward side fell back to the
    // projection block by block, and the backward side emptied the scope; both answers were
    // empty here, as that projection is exact on this tree, but a refused projection would
    // have kept a box where the other side found none.
    use zedc::store::preimage::counts::{negative_cycles, set_put_in_side};
    let p = Premises::new();
    let ns = named(4, "x");
    let tests = [
        prim(Prim::Ne, var("x2"), int(0)),
        prim(Prim::Ne, var("x2"), int(1)),
        ge("x1", "x2", 0),
        ge("x2", "x0", -3),
        ge("x1", "x3", 1),
        ge("x3", "x0", 0),
        ge("x0", "x1", 3),
    ];
    let mut runs = Vec::new();
    for side in [Some(true), Some(false), None] {
        set_put_in_side(side);
        let mut s = ints(&ns);
        for n in &ns {
            s = s.assume(&prim(Prim::Ge, var(n), int(-2)), true, &p);
            s = s.assume(&prim(Prim::Le, var(n), int(4)), true, &p);
        }
        let before = negative_cycles();
        for t in &tests {
            s = s.assume(t, true, &p);
        }
        let after = negative_cycles();
        let cycles = [after[0] - before[0], after[1] - before[1]];
        runs.push((side, cycles, intervals(&s, &ns)));
    }
    set_put_in_side(None);
    for run in &runs {
        assert_eq!((run.1, &run.2), ([1, 0], &None), "{runs:?}");
    }
}

#[test]
fn either_side_of_the_repair_of_the_potential_gives_the_same_answers() {
    // Item PROOF-put-in-repair-direction. The repair of the potential (`product::put_in`)
    // runs a search forward from the edge's head and one backward from its tail in step and
    // takes the first to end. Here the random ladders and the sums-between ladders of one
    // seed run with the forward side alone, the backward side alone, and both in step. Every
    // step of each run is checked against the projection block by block from scratch, which
    // never reads the potential, so the three give the same answers; the steps that moved an
    // interval, emptied the scope or left a hole are counted the same. A cycle negative with
    // the gaps empties the scope or sends its tree to the projection block by block whichever
    // side found it, so the counts of each outcome agree too. The cycles of weight 0 tied may
    // differ, as the sides may tie different cycles; they are printed.
    use zedc::store::preimage::counts::{negative_cycles, set_put_in_side, zero_cycles_tied};
    let (_, seed) = Rng::fresh("either side of the repair");
    let mut runs = Vec::new();
    for side in [Some(true), Some(false), None] {
        set_put_in_side(side);
        let (tied, cycles) = (zero_cycles_tied(), negative_cycles());
        let met = (random_ladders(seed), sums_between(seed));
        let after = negative_cycles();
        let cycles = [after[0] - cycles[0], after[1] - cycles[1]];
        runs.push((side, met, zero_cycles_tied() - tied, cycles));
    }
    set_put_in_side(None);
    eprintln!("seed {seed}: side, kinds met, cycles of weight 0 tied, negative cycles {runs:?}");
    for run in &runs[1..] {
        assert_eq!(
            (run.1, run.3),
            (runs[0].1, runs[0].3),
            "seed {seed}: {runs:?}"
        );
    }
}

/// The kinds of step a run of ladders means to meet, in the order [`ladder_checked`] counts
/// them: steps that moved an interval, ladders that became empty, steps that left a name with
/// holes.
const LADDER_KINDS: [&str; 3] = ["moved", "empty", "holes"];

/// Checks the ladder `tests` over the names `ns`, in its order and reversed: each step's
/// intervals are those the projection block by block finds from scratch
/// (`Scope::forget_projections`), which never uses the potential. Each test is assumed as it
/// holds or not, or with both of its arms joined. `at` names the ladder in a failure. Gives
/// the counts of [`LADDER_KINDS`].
fn ladder_checked(ns: &[Arc<str>], tests: &[Step], p: &Premises, at: &str) -> [usize; 3] {
    let (mut moved, mut empty, mut holes) = (0, 0, 0);
    for reverse in [false, true] {
        let mut order = tests.to_vec();
        if reverse {
            order.reverse();
        }
        let mut s = ints(ns);
        for (step, (t, holds, joined)) in order.iter().enumerate() {
            let before = intervals(&s, ns);
            let next = |s: &Scope| {
                if *joined {
                    let mut j = s.assume(t, true, p).join(&s.assume(t, false, p));
                    j.reduce();
                    j
                } else {
                    s.assume(t, *holds, p)
                }
            };
            let got = next(&s);
            let mut fresh = s.clone();
            fresh.forget_projections();
            let mut want = next(&fresh);
            want.forget_projections();
            want.reduce();
            assert_eq!(
                intervals(&got, ns),
                intervals(&want, ns),
                "{at} reverse {reverse} step {step}: {order:?}"
            );
            moved += usize::from(intervals(&got, ns) != before);
            holes += usize::from(ns.iter().any(|n| got.get(n).ints().len() > 1));
            if got.bottom {
                empty += 1;
                break;
            }
            s = got;
        }
    }
    [moved, empty, holes]
}

/// A step of a ladder: the test, the outcome assumed, and whether the step joins the scopes
/// of both outcomes instead.
type Step = (Term, bool, bool);

/// A ladder built to meet each of [`LADDER_KINDS`]: `x0 != 0` moves `x0` and leaves it a
/// hole, `x1 - x0 >= 1` and `x0 >= 1` move it again, and `x0 <= 0` empties the scope; in the
/// reverse order `x0 <= 0` moves `x0` and `x0 >= 1` empties the scope.
fn built_ladder() -> (Vec<Arc<str>>, Vec<Step>) {
    let tests = vec![
        (prim(Prim::Ne, var("x0"), int(0)), true, false),
        (ge("x1", "x0", 1), true, false),
        (prim(Prim::Ge, var("x0"), int(1)), true, false),
        (prim(Prim::Le, var("x0"), int(0)), true, false),
    ];
    (named(2, "x"), tests)
}

/// Each of [`LADDER_KINDS`] whose count in `met` is 0 is met by [`built_ladder`], which gives
/// the projection from scratch at every step.
fn ladder_kinds_met(met: &[usize]) {
    for (i, kind) in LADDER_KINDS.iter().enumerate().take(met.len()) {
        if met[i] == 0 {
            let (ns, tests) = built_ladder();
            let built = ladder_checked(&ns, &tests, &Premises::new(), "the built ladder");
            assert!(built[i] > 0, "{kind} not met: {built:?}");
            eprintln!("{kind} met only by the ladder built for it");
        }
    }
}

#[test]
fn a_join_that_moves_a_name_to_another_tree_keeps_its_cycles_found() {
    // Item FLAKE-l01-39-scope-one-failure, seed 60 of
    // `shortest_paths_give_the_intervals_of_the_projection_block_by_block`, minimized. The join
    // drops `x4 - x2 == -1`, so `x2` leaves the tree of `x4` and `x5` but keeps its component
    // of the potential, which is never split. `x2 - x3 >= 1` puts `x2` in a second tree. Then
    // a reorder of the first tree (`x4 - x1 >= 0`) that read the first tree's edges alone
    // either took `x2` out of its component's ends, its one edge being of the other tree (the
    // first ladder), or moved its component past that of `x3` (the second), and
    // `x2 - x3 <= -1` closed a negative cycle that no search saw: the scope was not bottom.
    let eq = |a: &str, b: &str, c: i64| prim(Prim::Eq, prim(Prim::Sub, var(a), var(b)), int(c));
    let p = Premises::new();
    let ns = named(7, "x");
    for ladder in [
        vec![
            (eq("x5", "x4", 2), true, false),
            (eq("x4", "x2", -1), true, true),
            (ge("x2", "x3", 1), true, false),
            (ge("x6", "x1", -1), false, false),
            (ge("x4", "x1", 0), true, false),
            (ge("x2", "x3", 0), false, false),
        ],
        vec![
            (eq("x5", "x4", 2), true, false),
            (eq("x4", "x2", -1), true, true),
            (ge("x6", "x4", -3), true, false),
            (ge("x2", "x3", 1), true, false),
            (ge("x6", "x1", -1), false, false),
            (ge("x4", "x1", 0), true, false),
            (ge("x2", "x3", 0), false, false),
        ],
    ] {
        let [_, empty, _] = ladder_checked(&ns, &ladder, &p, "a minimized ladder");
        // Both orders hold `x2 - x3 >= 1` and its negation, so both end empty.
        assert_eq!(empty, 2, "{ladder:?}");
    }
}

/// The ladder built for [`LADDER_KINDS`] meets each of them.
#[test]
fn the_ladder_built_for_each_kind_of_step_meets_it() {
    let (ns, tests) = built_ladder();
    let built = ladder_checked(&ns, &tests, &Premises::new(), "the built ladder");
    for (kind, n) in LADDER_KINDS.iter().zip(built) {
        assert!(n > 0, "{kind}: {built:?}");
    }
}

#[test]
fn shortest_paths_with_holes_and_sums_between_give_the_projection_block_by_block() {
    let (_, seed) = Rng::fresh("shortest paths with holes and sums");
    sums_between(seed);
}

/// As in the ladders above, with tests that leave a tree to the projection block by block
/// between the difference constraints: `x != c`, which gives `x` a hole until a bound closes
/// it, and `x + y >= c`, not a difference constraint. An edge that comes while its tree goes
/// block by block is in the potential before any later edge is read (`Scope::repair`). 15
/// cases of `seed` are drawn; each of [`LADDER_KINDS`] they miss is met by the ladder built for
/// it (PROOF-test-coverage-constructive; until 2026-11-15 cases were drawn until more than 60
/// moved, 4 empty and 40 with holes were met, with no limit: over 15 cases the empty ladders
/// vary from seed to seed, and 4 of 400 runs met only 4, FAIL-linked-sums-between-seed).
/// Gives the counts of [`LADDER_KINDS`] over the 15 cases.
fn sums_between(seed: u64) -> [usize; 3] {
    let mut r = Rng::new(seed);
    let p = Premises::new();
    let mut met = [0usize; 3];
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
        let m = ladder_checked(&ns, &tests, &p, &format!("seed {seed} case {case}"));
        for (n, x) in met.iter_mut().zip(m) {
            *n += x;
        }
    }
    eprintln!("seed {seed}: moved, empty, holes {met:?}");
    ladder_kinds_met(&met);
    met
}

/// The sums-between ladders of seed 4360659011783558506 give the projection from scratch: a
/// cycle of weight 0 made of two edges that are opposite only after an equality's names merge
/// ties `x2` to the hole of `x1` (`holes::tie_cycles`).
#[test]
fn shortest_paths_with_holes_and_sums_between_of_seed_4360659011783558506() {
    sums_between(4360659011783558506);
}

/// The sums-between ladders of seed 16499876031534905745 give the projection from scratch.
#[test]
fn shortest_paths_with_holes_and_sums_between_of_seed_16499876031534905745() {
    sums_between(16499876031534905745);
}

/// Seed 8574908458420171230 empties only 4 ladders in 15 cases, where more than 4 were asked
/// for until 2026-11-15 (FAIL-linked-sums-between-seed).
#[test]
fn shortest_paths_with_holes_and_sums_between_of_seed_8574908458420171230() {
    assert_eq!(sums_between(8574908458420171230)[1], 4);
}

/// Seed 16626066307386781116 empties only 4 ladders in 15 cases, as seed 8574908458420171230.
#[test]
fn shortest_paths_with_holes_and_sums_between_of_seed_16626066307386781116() {
    assert_eq!(sums_between(16626066307386781116)[1], 4);
}

/// Counts of [`holes_in_trees`]: tests that moved an interval, left a name with holes, left
/// two names or more with holes, or made the scope empty; pairs of inequalities that made a
/// cycle of weight 0; tests that joined both arms; trees drawn.
#[derive(Clone, Debug, Default)]
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
/// names of one tree. The first `trees` trees of `seed` are checked and counted. The counts
/// vary widely from seed to seed (piled, over 4 trees of 300 seeds, 0 to 234), so a test that
/// means to meet a case does so by [`hole_kinds_met`], with a tree built for each case its
/// trees missed, never by drawing more (PROOF-test-coverage-constructive; until 2026-11-15
/// trees were drawn until counts were met, with no limit).
fn holes_in_trees(seed: u64, pile: bool, trees: usize) -> HoleCounts {
    let mut r = Rng::new(seed);
    let p = Premises::new();
    let mut out = HoleCounts::default();
    for case in 0..trees {
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
                hole_checked(&s, hole, holds, &ns, &p, &mut out, || {
                    format!("seed {seed} case {case} step {step}")
                });
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

/// The test `hole` asked of the scope `s`, holding or not (`holds`), gives the intervals of
/// the projection from scratch; counted in `out`. `at` names the step in a failure. Gives the
/// scope after the test.
fn hole_checked(
    s: &Scope,
    hole: &Term,
    holds: bool,
    ns: &[Arc<str>],
    p: &Premises,
    out: &mut HoleCounts,
    at: impl Fn() -> String,
) -> Scope {
    let got = s.assume(hole, holds, p);
    let mut fresh = s.clone();
    fresh.forget_projections();
    let mut want = fresh.assume(hole, holds, p);
    want.forget_projections();
    want.reduce();
    assert_eq!(
        intervals(&got, ns),
        intervals(&want, ns),
        "{} {holds}: {hole:?} on {:?}",
        at(),
        s.relation
    );
    let holed = ns.iter().filter(|n| got.get(n).ints().len() > 1).count();
    out.moved += usize::from(intervals(&got, ns) != intervals(s, ns));
    out.holes += usize::from(holed > 0);
    out.piled += usize::from(holed > 1);
    out.empty += usize::from(got.bottom);
    got
}

/// The trees [`holes_in_trees`] draws in a random run: 4 took 0.15 to 1.3 s alone at load 49
/// on 32 cores.
const HOLE_TREES: usize = 4;

/// The cases a run of trees means to meet, by their counts in [`HoleCounts`]: tests that moved
/// an interval, left a name with holes, left two names or more with holes, made the scope
/// empty. Each is met by the tree of [`built_hole_trees`] at its index.
const HOLE_KINDS: [&str; 4] = ["moved", "holes", "piled", "empty"];

/// The counts of [`HOLE_KINDS`] in `n`.
fn hole_kinds(n: &HoleCounts) -> [usize; 4] {
    [n.moved, n.holes, n.piled, n.empty]
}

/// A tree built for each of [`HOLE_KINDS`]: `x0` and `x1` in `[0..=4]` with `x1 - x0 >= 0`,
/// then holes asked in turn, each checked as [`holes_in_trees`] checks one. `x0 != 2` moves
/// `x0` and leaves it a hole; `x1 != 3` after it leaves both names holes; `x0 != 0` after
/// `x0 <= 0` makes the scope empty. Gives the counts of each tree.
fn built_hole_trees() -> [HoleCounts; 4] {
    let p = Premises::new();
    let ns = named(2, "x");
    let ne = |n: &str, c: i64| prim(Prim::Ne, var(n), int(c));
    let mut s = ints(&ns);
    for n in &ns {
        s = s.assume(&prim(Prim::Ge, var(n), int(0)), true, &p);
        s = s.assume(&prim(Prim::Le, var(n), int(4)), true, &p);
    }
    let tree = s.assume(&ge("x1", "x0", 0), true, &p);
    let run = |steps: &[Term]| {
        let mut out = HoleCounts {
            trees: 1,
            ..HoleCounts::default()
        };
        let mut s = tree.clone();
        for (i, t) in steps.iter().enumerate() {
            s = hole_checked(&s, t, true, &ns, &p, &mut out, || format!("built step {i}"));
        }
        out
    };
    let one = run(&[ne("x0", 2)]);
    let piled = run(&[ne("x0", 2), ne("x1", 3)]);
    let empty = run(&[prim(Prim::Le, var("x0"), int(0)), ne("x0", 0)]);
    [one.clone(), one, piled, empty]
}

/// Each of [`HOLE_KINDS`] that `n` missed (all but `piled` when `pile` is false) is met by its
/// tree of [`built_hole_trees`], which gives the projection from scratch at every step.
fn hole_kinds_met(n: &HoleCounts, pile: bool) {
    let kinds = hole_kinds(n);
    for (i, kind) in HOLE_KINDS.into_iter().enumerate() {
        if kinds[i] == 0 && (pile || kind != "piled") {
            let built = &built_hole_trees()[i];
            assert!(hole_kinds(built)[i] > 0, "{kind} not met: {built:?}");
            eprintln!("{kind} met only by the tree built for it");
        }
    }
}

/// [`holes_in_trees`] without piling, on [`HOLE_TREES`] trees of a new seed each run. As one
/// test of the 150 trees of seed 0x1e4e it took about 20 s alone at load 23 to 25, and as three
/// tests of 50 trees about 5 s each (item SPLIT-l01_39-linked); those 150 trees counted moved
/// 6096, holes 2330, empty 662, tied 77, joined 109.
#[test]
fn holes_in_a_tree_of_differences_give_the_projection_from_scratch() {
    let (_, seed) = Rng::fresh("holes in a tree of differences");
    // Over 17 seeds, 4 trees each: moved 66 to 275, holes 15 to 137, empty 6 to 41.
    let n = holes_in_trees(seed, false, HOLE_TREES);
    eprintln!("{n:?}");
    hole_kinds_met(&n, false);
}

/// As [`holes_in_a_tree_of_differences_give_the_projection_from_scratch`], with the holes piled
/// up in many names of each tree, on [`HOLE_TREES`] trees of a new seed each run (4 trees took
/// 0.8 s at load 42). As one test of the 150 trees of seed 0x9a1e it took about 22 s alone at
/// load 23 to 25 (item SPLIT-l01_39-linked); those trees counted moved 6773, holes 4803, piled
/// 2296, empty 763, tied 45, joined 45. Over 4 trees of each of 300 seeds (1000 to 1299),
/// piled ranged from 0 to 234 (item FAIL-linked-piled-holes-count).
#[test]
fn holes_piled_in_many_names_of_a_tree_give_the_projection_from_scratch() {
    let (_, seed) = Rng::fresh("holes piled in many names of a tree");
    let n = holes_in_trees(seed, true, HOLE_TREES);
    eprintln!("{n:?}");
    hole_kinds_met(&n, true);
}

/// Each tree built for a kind of [`HOLE_KINDS`] meets it.
#[test]
fn each_tree_built_for_a_kind_of_hole_meets_it() {
    for (i, (kind, built)) in HOLE_KINDS.into_iter().zip(built_hole_trees()).enumerate() {
        assert!(hole_kinds(&built)[i] > 0, "{kind}: {built:?}");
    }
}

/// The first 4 trees of `seed`, with piling, count `first` (moved, holes, piled, empty): seeds
/// on which a test that asked for counts over 4 trees failed (FAIL-linked-piled-holes-count).
/// Every step of them gives the projection from scratch.
fn met_after_four_trees(seed: u64, first: [usize; 4]) {
    let n = holes_in_trees(seed, true, HOLE_TREES);
    assert_eq!(hole_kinds(&n), first, "{n:?}");
}

/// Piled 9, where more than 10 were asked for until 2026-11-15.
#[test]
fn holes_piled_in_the_trees_of_seed_10423609239771793175() {
    met_after_four_trees(10423609239771793175, [130, 67, 9, 15]);
}

/// Empty 2, where more than 3 were asked for until 2026-11-15 (found by
/// FAIL-zir-text-reader-messages).
#[test]
fn holes_piled_in_the_trees_of_seed_12717323168360931590() {
    met_after_four_trees(12717323168360931590, [101, 62, 32, 2]);
}

/// Holes 42, where more than 45 were asked for until 2026-11-15 (found by
/// FAIL-bitword-arity-message).
#[test]
fn holes_piled_in_the_trees_of_seed_9834632220024286056() {
    met_after_four_trees(9834632220024286056, [112, 42, 13, 8]);
}

/// No holes piled at all, and holes 22, where more than 45 were asked for until 2026-11-15.
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

/// The satellite of every hub built in seeded random orders, which merges blocks of every
/// size into one another (`Blocks::merge`, which moves a block's indexes by name and by pair):
/// after each conjunct the forest is well formed ([`Blocks::well_formed`], which rebuilds every
/// index from the blocks' conjuncts), every order ends with the same blocks, and each name's
/// blocks with a moving conjunct come in ascending order of their numbers.
#[test]
fn a_satellite_built_in_any_order_merges_into_the_same_well_formed_blocks() {
    for bounds in [false, true] {
        let gs = satellite_conjuncts(12, bounds);
        let mut ends: BTreeSet<BTreeSet<BTreeSet<Arc<Formula>>>> = BTreeSet::new();
        for seed in 0..8u64 {
            let mut rng = Rng::new(seed);
            let mut c = Conjuncts::default();
            for i in shuffled(gs.len(), &mut rng) {
                c.and(gs[i].clone());
                if let Err(e) = c.blocks().well_formed() {
                    panic!("bounds {bounds} seed {seed}, after {}: {e}", gs[i]);
                }
            }
            let b = c.blocks();
            let names: BTreeSet<Arc<str>> = b.all().flat_map(|k| b.names_of(k).cloned()).collect();
            for n in &names {
                let moving: Vec<_> = b.moving_blocks(n).collect();
                assert!(
                    moving.windows(2).all(|w| w[0] < w[1]),
                    "bounds {bounds} seed {seed}: blocks of {n} {moving:?}"
                );
            }
            ends.insert(b.all().map(|k| b.members(k).cloned().collect()).collect());
        }
        assert_eq!(
            ends.len(),
            1,
            "bounds {bounds}: the blocks depend on the order"
        );
    }
}

/// `a >= b` of two atoms.
fn atom_ge(a: Atom, b: Atom) -> Arc<Formula> {
    Arc::new(Formula::Con(Con::ge(&Lin::atom(a), &Lin::atom(b))))
}

/// `d` triangles of names joined in a balanced tree: at each level the blocks of each pair are
/// linked by one conjunct and closed into one by a second, so every merge joins two blocks of
/// equal size. The names are numbered in bit-reversed order, so that the names of the two
/// blocks of a merge alternate in the order of names.
fn balanced_triangles(d: usize) -> Vec<Arc<Formula>> {
    assert!(d.is_power_of_two());
    let name = |i: usize, side: &str| {
        let id = i.reverse_bits().rotate_left(d.ilog2());
        Atom::Sym(format!("{side}{id:08}").into())
    };
    let mut gs = Vec::new();
    for i in 0..d {
        let (a, b, c) = (name(i, "a"), name(i, "b"), name(i, "c"));
        gs.extend([
            atom_ge(a.clone(), b.clone()),
            atom_ge(a, c.clone()),
            atom_ge(b, c),
        ]);
    }
    for level in 0..d.ilog2() {
        let width = 1 << level;
        for i in (0..d).step_by(2 * width) {
            gs.push(atom_ge(name(i, "a"), name(i + width, "b")));
            gs.push(atom_ge(name(i, "b"), name(i + width, "c")));
        }
    }
    gs
}

/// The one block of `blocks`, as a set of conjuncts.
fn one_block(blocks: &Blocks) -> BTreeSet<Arc<Formula>> {
    assert_eq!(blocks.all().count(), 1);
    let b = blocks.all().next().expect("one block");
    blocks.members(b).cloned().collect()
}

/// Merges of blocks of equal size whose names alternate (cross-review R1-CODEX, Q5): after each
/// conjunct, added in order or in reverse, the forest is well formed; before the last conjunct
/// there are three blocks, after it one of every conjunct; and taking the last conjunct away and
/// adding it again splits and merges the two halves, three times over.
#[test]
fn blocks_of_equal_size_whose_names_alternate_merge_into_one() {
    for d in [1, 2, 4, 8, 16, 32, 64] {
        let gs = balanced_triangles(d);
        let all: BTreeSet<Arc<Formula>> = gs.iter().cloned().collect();
        let mut blocks = Blocks::default();
        for (i, g) in gs.iter().enumerate() {
            blocks.add(g);
            if let Err(e) = blocks.well_formed() {
                panic!("d {d}, after {g}: {e}");
            }
            if d > 1 && i == gs.len() - 2 {
                assert_eq!(blocks.all().count(), 3, "d {d}: before the last conjunct");
            }
        }
        assert_eq!(one_block(&blocks), all, "d {d}");
        let mut reversed = Blocks::default();
        for g in gs.iter().rev() {
            reversed.add(g);
            if let Err(e) = reversed.well_formed() {
                panic!("d {d}, in reverse, after {g}: {e}");
            }
        }
        assert_eq!(one_block(&reversed), all, "d {d}, in reverse");
        if d > 1 {
            for _ in 0..3 {
                blocks.remove(&gs[gs.len() - 1..]);
                if let Err(e) = blocks.well_formed() {
                    panic!("d {d}, the last conjunct taken away: {e}");
                }
                assert_eq!(blocks.all().count(), 3, "d {d}: split");
                blocks.add(&gs[gs.len() - 1]);
                if let Err(e) = blocks.well_formed() {
                    panic!("d {d}, the last conjunct added again: {e}");
                }
                assert_eq!(one_block(&blocks), all, "d {d}: merged again");
            }
        }
    }
}

/// A name met only in products (`z` in `a * z` and `b * z`) is moving in each block that holds
/// such a conjunct not hung at it, through a merge of the two blocks, and in none once both are
/// hung; it has no tree of its own (cross-review R1-CODEX, Q1).
#[test]
fn a_name_met_only_in_products_is_moving_where_it_is_not_hung() {
    let z: Arc<str> = "z".into();
    let product = |n: &str| Atom::Product(Factor::Sym(n.into()), Factor::Sym(z.clone()));
    let gs = [
        atom_ge(product("a"), Atom::Aux(0)),
        atom_ge(product("b"), Atom::Aux(1)),
        atom_ge(Atom::Aux(0), Atom::Aux(1)),
    ];
    let mut blocks = Blocks::default();
    blocks.add(&gs[0]);
    blocks.add(&gs[1]);
    assert_eq!(blocks.well_formed(), Ok(()));
    assert_eq!(blocks.moving_blocks("z").count(), 2);
    blocks.hang(&z, &gs[0], true);
    assert_eq!(blocks.well_formed(), Ok(()));
    assert_eq!(blocks.moving_blocks("z").count(), 1);
    blocks.add(&gs[2]);
    assert_eq!(blocks.well_formed(), Ok(()));
    let b = blocks.of(&gs[2]).expect("the block of the last conjunct");
    assert_eq!(blocks.moving_blocks("z").collect::<Vec<_>>(), [b]);
    assert!(blocks.names_of(b).any(|n| *n == z));
    blocks.hang(&z, &gs[1], true);
    assert_eq!(blocks.well_formed(), Ok(()));
    assert_eq!(blocks.moving_blocks("z").count(), 0);
    assert!(names(&gs[1]).contains(&z));
    assert!(blocks.tree_of_name("z").is_none());
}

/// 64 conjuncts `x_i * z >= aux` are in one block when they share one auxiliary atom and in 64
/// when each has its own; `z`, met only in products, is moving in each of those blocks and has
/// no tree (cross-review R1-CODEX, Q5).
#[test]
fn a_name_met_only_in_products_is_moving_in_each_block_that_holds_it() {
    for shared in [false, true] {
        let mut blocks = Blocks::default();
        for i in 0..64 {
            let product =
                Atom::Product(Factor::Sym(format!("x{i}").into()), Factor::Sym("z".into()));
            blocks.add(&atom_ge(product, Atom::Aux(if shared { 0 } else { i })));
        }
        assert_eq!(blocks.well_formed(), Ok(()), "shared {shared}");
        let want = if shared { 1 } else { 64 };
        assert_eq!(blocks.moving_blocks("z").count(), want, "shared {shared}");
        assert!(blocks.tree_of_name("z").is_none(), "shared {shared}");
    }
}

/// Conjuncts whose blocks merge in pairs of equal size, level by level, `m` a power of two:
/// block `i` is the four conjuncts `a_i >= h_i`, `a_i >= h_{i+1}`, `b_i >= h_i`,
/// `b_i >= h_{i+1}`, a cycle through `h_i` and `h_{i+1}`, so the blocks make a chain along the
/// names `h`; then, for each level `l` from 1 and each `i` a multiple of `2^l`, the two
/// conjuncts `c >= h_i` and `c >= h_{i + 2^l}` of a new name `c`, the second of which closes a
/// cycle through the two blocks of the level below. Each name `a`, `b` and `c` has a bound
/// `1000 >= a` of its own, so it is no leaf of a star ([`Conjuncts::star`]) and its conjuncts
/// stay in the forest. Each level moves near half of the conjuncts, so a conjunct moves near
/// log2 m times ([`Blocks::merge`]). From the Opus seat of cross-review round 1.
fn balanced_merges(m: usize) -> Vec<Formula> {
    let s = |x: &str| Lin::atom(Atom::Sym(x.into()));
    let above = |a: &str, b: &str| Formula::Con(Con::ge(&s(a), &s(b)));
    let pin = |a: &str| Formula::Con(Con::ge(&Lin::constant(1000), &s(a)));
    let mut gs = Vec::new();
    for i in 0..m {
        let (h, k) = (format!("h{i}"), format!("h{}", i + 1));
        for t in [format!("a{i}"), format!("b{i}")] {
            gs.push(pin(&t));
            gs.push(above(&t, &h));
            gs.push(above(&t, &k));
        }
    }
    let mut w = 2;
    while w <= m {
        for i in (0..m).step_by(w) {
            let c = format!("c{w}_{i}");
            gs.push(pin(&c));
            gs.push(above(&c, &format!("h{i}")));
            gs.push(above(&c, &format!("h{}", i + w)));
        }
        w *= 2;
    }
    gs
}

/// The conjuncts of [`balanced_merges`] added in their own order and in seeded random orders:
/// after each conjunct the forest is well formed ([`Blocks::well_formed`]), every order ends
/// with the same blocks, those of two names all in one, and each name's blocks with a moving
/// conjunct come in ascending order. Fails if `Blocks::merge` leaves out any one of `up`,
/// `moving_at`, `at`, `pairs` or `names_in` (checked by the seat, one fault at a time).
#[test]
fn blocks_merged_in_pairs_of_equal_size_stay_well_formed_in_any_order() {
    let gs = balanced_merges(16);
    let mut ends: BTreeSet<BTreeSet<BTreeSet<Arc<Formula>>>> = BTreeSet::new();
    let orders = std::iter::once((0..gs.len()).collect::<Vec<_>>())
        .chain((0..8u64).map(|seed| shuffled(gs.len(), &mut Rng::new(seed))));
    for (o, order) in orders.enumerate() {
        let mut c = Conjuncts::default();
        for i in order {
            c.and(gs[i].clone());
            if let Err(e) = c.blocks().well_formed() {
                panic!("order {o}, after {}: {e}", gs[i]);
            }
        }
        let b = c.blocks();
        for k in b.all() {
            for n in b.names_of(k) {
                let moving: Vec<_> = b.moving_blocks(n).collect();
                assert!(
                    moving.windows(2).all(|w| w[0] < w[1]),
                    "order {o}: {n} {moving:?}"
                );
            }
        }
        let end: BTreeSet<BTreeSet<Arc<Formula>>> =
            b.all().map(|k| b.members(k).cloned().collect()).collect();
        let merged = end.iter().filter(|k| k.len() > 1).count();
        assert_eq!(
            merged, 1,
            "order {o}: the conjuncts of two names end in one block"
        );
        ends.insert(end);
    }
    assert_eq!(ends.len(), 1, "the blocks depend on the order");
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

/// The band of ST-band-quintic at size `k`: names `x_0..=x_k`, `x_i` in `10 (k - i) ..= 10 (k -
/// i) + 9` and `10 <= x_i - x_(i+1) <= 11`, then for each `i < k - 1` a hole
/// `x_i != 10 (k - i) + 5` that holds and a rung `x_i - x_(i+2) >= 20` as an `if` whose arms
/// join. The path alone, each step `10 <= x_i - x_(i+1) <= 11` two opposite edges, already joins
/// its names both ways in more than one directed cycle (one directed cycle per step: one
/// strongly connected component of the graph of edges), and the holes pile up in three names or
/// more, so the ends are found by snap-Dijkstra (`holes::Run::snaps`). Scope's blocks are the
/// biconnected components of the graph of conjuncts and names, not these: on the path alone each
/// name between two steps cuts it, and the rungs `x_i - x_(i+2)`, when kept, merge the blocks
/// into one that grows with `k`.
fn band_holes_run(k: usize, p: &Premises) -> Scope {
    let n = named(k + 1, "x");
    let base = |i: usize| (10 * (k - i)) as i64;
    let s = (0..=k).fold(ints(&n), |s, i| {
        s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, p)
            .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, p)
    });
    let s = (0..k).fold(s, |s, i| {
        s.assume(&ge(&n[i], &n[i + 1], 10), true, p)
            .assume(&ge(&n[i + 1], &n[i], -11), true, p)
    });
    (0..k - 1).fold(s, |s, i| {
        let s = s.assume(&prim(Prim::Ne, var(&n[i]), int(base(i) + 5)), true, p);
        let t = ge(&n[i], &n[i + 2], 20);
        let mut j = s
            .assume_case(&t, true, p)
            .join(&s.assume_case(&t, false, p));
        j.reduce();
        j
    })
}

/// The band of [`band_holes_run`] with its rungs `x_i - x_(i+2) >= 20` assumed as plain
/// conjuncts, not joined, and chords `x_i - x_(i+3) >= 30` (XR-st-band-quintic r1, Claude Q3):
/// both are implied by the steps, so each name keeps the band's closed form.
fn band_chords_run(k: usize, p: &Premises) -> Scope {
    let n = named(k + 1, "x");
    let base = |i: usize| (10 * (k - i)) as i64;
    let s = (0..=k).fold(ints(&n), |s, i| {
        s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, p)
            .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, p)
    });
    let s = (0..k).fold(s, |s, i| {
        s.assume(&ge(&n[i], &n[i + 1], 10), true, p)
            .assume(&ge(&n[i + 1], &n[i], -11), true, p)
    });
    (0..k - 1).fold(s, |s, i| {
        let s = s
            .assume(&prim(Prim::Ne, var(&n[i]), int(base(i) + 5)), true, p)
            .assume(&ge(&n[i], &n[i + 2], 20), true, p);
        if i + 3 <= k {
            s.assume(&ge(&n[i], &n[i + 3], 30), true, p)
        } else {
            s
        }
    })
}

/// A chain whose top moves at each fact (XR-st-band-quintic r1, Claude's `moving_top`): names
/// `x_0..=x_k`, `x_i` in `[b_i, b_i + W - 1]` with `b_i = W (k - i)`, `W = w + 10`, and
/// `W <= x_i - x_(i+1) <= W + 1`, then `w` holes taken off the top of `x_0` one at a time, each
/// of which lowers the greatest value of every name. The ends change `w (k + 1)` times in all,
/// so any exact method does that much work: the output bounds the cost from below.
fn moving_top_run(k: usize, w: usize, p: &Premises) -> Scope {
    let width = (w + 10) as i64;
    let s = top_chain(k, width, p);
    let n = named(k + 1, "x");
    (0..w as i64).fold(s, |s, j| {
        s.assume(
            &prim(Prim::Ne, var(&n[0]), int(width * k as i64 + width - 1 - j)),
            true,
            p,
        )
    })
}

/// [`moving_top_run`] with three holes inside the chain first, `x_i != b_i + 1` for `i < 3`
/// (`k >= 2`), so that its names are holed and the ends are found by `Scope::by_holes` rather
/// than by shortest paths alone (XR-st-band-quintic r2, Gemini finding 2). Each of the three
/// holes stays at its own name: a value `b_i + c` of a neighbor is met at offset `c` or `c + 1`
/// of `x_i`, one of which is not 1 while the top is at least 3.
fn holed_moving_top_run(k: usize, w: usize, p: &Premises) -> Scope {
    let width = (w + 10) as i64;
    let n = named(k + 1, "x");
    let s = (0..3).fold(top_chain(k, width, p), |s, i| {
        s.assume(
            &prim(Prim::Ne, var(&n[i]), int(width * (k - i) as i64 + 1)),
            true,
            p,
        )
    });
    (0..w as i64).fold(s, |s, j| {
        s.assume(
            &prim(Prim::Ne, var(&n[0]), int(width * k as i64 + width - 1 - j)),
            true,
            p,
        )
    })
}

/// Holes inside `x_0` that move no other name (XR-st-band-quintic r2, Claude finding 2): the
/// chain of [`top_chain`] at width `2 w + 10`, then `x_0 != b_0 + 1 + 2 j` for `j < w`. Each
/// value `b_i + c` of `x_1` is met at offset `c` or `c + 1` of `x_0`, one of them even and so
/// never a hole, so the other names keep their whole ranges: the output is the `w` holes, and
/// a method that reads the whole chain at each hole costs about `k w`.
fn interior_holes_run(k: usize, w: usize, p: &Premises) -> Scope {
    let width = (2 * w + 10) as i64;
    let n = named(k + 1, "x");
    (0..w as i64).fold(top_chain(k, width, p), |s, j| {
        s.assume(
            &prim(Prim::Ne, var(&n[0]), int(width * k as i64 + 1 + 2 * j)),
            true,
            p,
        )
    })
}

/// Names `x_0..=x_k`, `x_i` in `[b_i, b_i + width - 1]` with `b_i = width (k - i)`, and
/// `width <= x_i - x_(i+1) <= width + 1`: the chain of [`moving_top_run`],
/// [`holed_moving_top_run`] and [`interior_holes_run`].
fn top_chain(k: usize, width: i64, p: &Premises) -> Scope {
    let n = named(k + 1, "x");
    let base = |i: usize| width * (k - i) as i64;
    let s = (0..=k).fold(ints(&n), |s, i| {
        s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, p)
            .assume(
                &prim(Prim::Le, var(&n[i]), int(base(i) + width - 1)),
                true,
                p,
            )
    });
    (0..k).fold(s, |s, i| {
        s.assume(&ge(&n[i], &n[i + 1], width), true, p).assume(
            &ge(&n[i + 1], &n[i], -width - 1),
            true,
            p,
        )
    })
}

/// The closed form of the band of [`band_holes_run`] at name `i`: `[b, b + 9]` less `b + 5` for
/// `i < k - 1`, `[b, b + 9]` otherwise, `b = 10 (k - i)`.
fn band_closed_form(k: usize, i: usize) -> IntervalSet {
    let b = (10 * (k - i)) as i64;
    let all = IntervalSet::of(b, b + 9);
    if i < k - 1 {
        all.minus(&IntervalSet::single(b + 5))
    } else {
        all
    }
}

/// The band with chords keeps the band's closed form
/// ([`a_band_with_holes_and_joined_rungs_is_exact`]), and the moving top lowers every name's
/// greatest value by one per hole: after `j` holes each name `x_i` is exactly
/// `[b, b + width - 1 - j]`, `b = width (k - i)`, `width = j + 10` (all names at one offset
/// `c` from their bases meet every step, and the step `x_i - x_(i+1) >= width` carries the top
/// of `x_0` down the chain); with the three holes of [`holed_moving_top_run`] the same less
/// `b + 1` for `i < 3`. Interior holes ([`interior_holes_run`]) leave `x_0` less its holes and
/// every other name whole. The whole set is compared, so a lost value inside it fails too
/// (XR-st-band-quintic r2, D4).
#[test]
fn a_band_with_chords_and_a_moving_top_are_exact() {
    let p = Premises::new();
    for k in [5, 10] {
        let s = band_chords_run(k, &p);
        let n = named(k + 1, "x");
        for (i, x) in n.iter().enumerate() {
            let ints = s.get(x).ints().clone();
            assert_eq!(ints, band_closed_form(k, i), "chords: {x} at k = {k}");
        }
        let w = 4;
        for j in 0..=w {
            // The width of the runs with `j` holes ([`moving_top_run`]).
            let width = (j + 10) as i64;
            let s = moving_top_run(k, j, &p);
            let holed = holed_moving_top_run(k, j, &p);
            for (i, x) in n.iter().enumerate() {
                let b = width * (k - i) as i64;
                let want = IntervalSet::of(b, b + width - 1 - j as i64);
                let ints = s.get(x).ints().clone();
                assert_eq!(ints, want, "moving top: {x} at k = {k} after {j} holes");
                let want = if i < 3 {
                    want.minus(&IntervalSet::single(b + 1))
                } else {
                    want
                };
                let ints = holed.get(x).ints().clone();
                assert_eq!(
                    ints, want,
                    "holed moving top: {x} at k = {k} after {j} holes"
                );
            }
        }
        let width = (2 * w + 10) as i64;
        let s = interior_holes_run(k, w, &p);
        for (i, x) in n.iter().enumerate() {
            let b = width * (k - i) as i64;
            let holes = (0..w as i64).map(|j| IntervalSet::single(b + 1 + 2 * j));
            let want = if i == 0 {
                holes.fold(IntervalSet::of(b, b + width - 1), |a, h| a.minus(&h))
            } else {
                IntervalSet::of(b, b + width - 1)
            };
            assert_eq!(
                s.get(x).ints().clone(),
                want,
                "interior holes: {x} at k = {k}"
            );
        }
    }
}

/// The sets of each name of `x_0..=x_k` by enumeration: `x_i` in `dom[i]`, each step
/// `lo <= x_i - x_(i+1) <= hi`, and each `(i, j, lo, hi)` of `spans` holding
/// `lo <= x_i - x_j <= hi`. Names are chosen from `x_0` down, the step bounding each next name to
/// `hi - lo + 1` values, so the search is `|dom[0]| (hi - lo + 1)^k` leaves at most.
fn chain_sets_by_enumeration(
    dom: &[IntervalSet],
    step: (i64, i64),
    spans: &[(usize, usize, i64, i64)],
) -> Vec<IntervalSet> {
    fn go(
        dom: &[IntervalSet],
        step: (i64, i64),
        spans: &[(usize, usize, i64, i64)],
        at: &mut Vec<i64>,
        out: &mut Vec<BTreeSet<i64>>,
    ) {
        let i = at.len();
        if i == dom.len() {
            if spans
                .iter()
                .all(|&(a, b, lo, hi)| (lo..=hi).contains(&(at[a] - at[b])))
            {
                for (o, &v) in out.iter_mut().zip(at.iter()) {
                    o.insert(v);
                }
            }
            return;
        }
        let (lo, hi) = match i {
            0 => {
                let (Some((lo, _)), Some((_, hi))) = (dom[0].first(), dom[0].last()) else {
                    return;
                };
                (lo.to_i64().expect("finite"), hi.to_i64().expect("finite"))
            }
            _ => (at[i - 1] - step.1, at[i - 1] - step.0),
        };
        for v in lo..=hi {
            if dom[i].contains(v) {
                at.push(v);
                go(dom, step, spans, at, out);
                at.pop();
            }
        }
    }
    let mut out = vec![BTreeSet::new(); dom.len()];
    go(dom, step, spans, &mut Vec::new(), &mut out);
    out.iter()
        .map(|vs| {
            vs.iter().fold(IntervalSet::empty(), |s, &v| {
                s.join(&IntervalSet::single(v))
            })
        })
        .collect()
}

/// A chord that is not implied: the band of [`band_holes_run`] with its rungs as plain
/// conjuncts and, for each `i`, `x_i - x_(i+3) >= 31` or, in a second run, `<= 30`, where the
/// steps alone give `[30, 33]`. Write `x_i = b_i + c_i`, `b_i = 10 (k - i)`: the steps keep
/// `c_i - c_(i+1)` in `[0, 1]`. Each chord cuts values the steps keep: `>= 31` needs
/// `c_i >= c_(i+3) + 1`, so `x_i = b_i` goes; `<= 30` needs `c_i = c_(i+1) = .. = c_(i+3)`, so
/// the hole of `x_i` at `c = 5` reaches `x_(i+3)`, which for `i + 3 >= k - 1` has no hole of its
/// own. A scope that drops the chord, or keeps only its hull, fails against the sets by
/// enumeration, and the test checks that the chords do cut (XR-st-band-quintic r2, D4, Codex
/// finding 7; such chords make the graph of edges a band of strongly connected parts, row
/// XR-st-band-quintic-rtscc).
#[test]
fn a_band_with_chords_not_implied_keeps_the_sets_of_enumeration() {
    let p = Premises::new();
    for k in [3, 4] {
        for at_least in [true, false] {
            let n = named(k + 1, "x");
            let base = |i: usize| (10 * (k - i)) as i64;
            let mut s = ints(&n);
            let mut dom: Vec<IntervalSet> = Vec::new();
            for (i, name) in n.iter().enumerate() {
                s = s
                    .assume(&prim(Prim::Ge, var(name), int(base(i))), true, &p)
                    .assume(&prim(Prim::Le, var(name), int(base(i) + 9)), true, &p);
                dom.push(IntervalSet::of(base(i), base(i) + 9));
            }
            for i in 0..k {
                s = s.assume(&ge(&n[i], &n[i + 1], 10), true, &p).assume(
                    &ge(&n[i + 1], &n[i], -11),
                    true,
                    &p,
                );
            }
            let mut spans: Vec<(usize, usize, i64, i64)> = Vec::new();
            for i in 0..k - 1 {
                s = s
                    .assume(&prim(Prim::Ne, var(&n[i]), int(base(i) + 5)), true, &p)
                    .assume(&ge(&n[i], &n[i + 2], 20), true, &p);
                dom[i] = dom[i].minus(&IntervalSet::single(base(i) + 5));
                spans.push((i, i + 2, 20, i64::MAX / 4));
            }
            for i in 0..k.saturating_sub(2) {
                let (chord, span) = if at_least {
                    (ge(&n[i], &n[i + 3], 31), (i, i + 3, 31, i64::MAX / 4))
                } else {
                    (ge(&n[i + 3], &n[i], -30), (i, i + 3, i64::MIN / 4, 30))
                };
                s = s.assume(&chord, true, &p);
                spans.push(span);
            }
            let want = chain_sets_by_enumeration(&dom, (10, 11), &spans);
            let plain: Vec<IntervalSet> =
                chain_sets_by_enumeration(&dom, (10, 11), &spans[..k - 1]);
            assert_ne!(
                want, plain,
                "the chords at k = {k} cut no value: not a test of them"
            );
            for (i, x) in n.iter().enumerate() {
                let ints = s.get(x).ints().clone();
                assert_eq!(ints, want[i], "{x} at k = {k}, chords >= 31: {at_least}");
            }
        }
    }
}

/// Random chains against the sets by enumeration (ST-band-quintic D1): `x_0..=x_k`, `k` in 2 to
/// 6, each `x_i` in `[b, b + 9]`, `b = 10 (k - i)`, less one random value or none, the steps
/// `10 <= x_i - x_(i+1) <= 11`, and spans `x_i - x_j >= c` or `<= c` for `j >= i + 2`, `c`
/// drawn around the steps' sums `[10 (j - i), 11 (j - i)]` so that a span is implied by the
/// steps, cuts values, or empties the scope; all assumed in a random order, so a span comes
/// before or after the steps that imply it. A span implied by a tree path of blocks of two
/// names is kept out of the relation ([`Scope`]'s implied differences) and one refuted by it
/// empties the scope without the solver; both must give the sets of enumeration.
#[test]
fn random_chains_with_spans_keep_the_sets_of_enumeration() {
    let (mut r, seed) = Rng::fresh("linked: random chains with spans");
    let p = Premises::new();
    let (mut implied, mut cutting, mut empty) = (0, 0, 0);
    for case in 0..40 {
        let k = 2 + r.below(5);
        let n = named(k + 1, "x");
        let base = |i: usize| (10 * (k - i)) as i64;
        let mut dom: Vec<IntervalSet> = Vec::new();
        let mut tests: Vec<Term> = Vec::new();
        for (i, x) in n.iter().enumerate() {
            tests.push(prim(Prim::Ge, var(x), int(base(i))));
            tests.push(prim(Prim::Le, var(x), int(base(i) + 9)));
            let mut d = IntervalSet::of(base(i), base(i) + 9);
            if r.coin() {
                let h = base(i) + r.below(10) as i64;
                tests.push(prim(Prim::Ne, var(x), int(h)));
                d = d.minus(&IntervalSet::single(h));
            }
            dom.push(d);
        }
        for i in 0..k {
            tests.push(ge(&n[i], &n[i + 1], 10));
            tests.push(ge(&n[i + 1], &n[i], -11));
        }
        let mut spans: Vec<(usize, usize, i64, i64)> = Vec::new();
        for _ in 0..1 + r.below(3) {
            if k < 2 {
                break;
            }
            let i = r.below(k - 1);
            let j = i + 2 + r.below(k - i - 1);
            let (lo, hi) = (10 * (j - i) as i64, 11 * (j - i) as i64);
            let c = lo - 1 + r.below((hi - lo + 3) as usize) as i64;
            if r.coin() {
                tests.push(ge(&n[i], &n[j], c));
                spans.push((i, j, c, i64::MAX / 4));
            } else {
                tests.push(ge(&n[j], &n[i], -c));
                spans.push((i, j, i64::MIN / 4, c));
            }
        }
        let mut s = ints(&n);
        for t in shuffled(tests.len(), &mut r) {
            s = s.assume(&tests[t], true, &p);
        }
        let want = chain_sets_by_enumeration(&dom, (10, 11), &spans);
        let plain = chain_sets_by_enumeration(&dom, (10, 11), &[]);
        if want.iter().all(IntervalSet::is_empty) {
            empty += 1;
            assert!(
                s.to_string() == "unreachable\n" || n.iter().any(|x| s.get(x).ints().is_empty()),
                "seed {seed} case {case}: reachable where enumeration has no point\n{s}"
            );
            continue;
        }
        if want == plain {
            implied += 1;
        } else {
            cutting += 1;
        }
        for (i, x) in n.iter().enumerate() {
            assert_eq!(
                s.get(x).ints().clone(),
                want[i],
                "seed {seed} case {case}: {x}, spans {spans:?}\n{s}"
            );
        }
    }
    eprintln!("seed {seed}: implied {implied}, cutting {cutting}, empty {empty}");
}

/// A span implied by the steps and kept out of the relation is put back when a name inside its
/// path is forgotten (ST-band-quintic D1): on `x_0..=x_3`, `b = 10 (3 - i)`, each in
/// `[b, b + 9]`, steps in `[10, 11]`, the span `x_0 - x_2 >= 20` is implied; `x_1` is bound
/// anew, which forgets every conjunct that mentions it, so the steps through it go; then
/// `x_0 == 30` leaves `x_2` at `{10}` only through the span (`x_2 <= x_0 - 20`). Also after a
/// join of two scopes that both keep the span out. Negative control: without the span the same
/// tests leave `x_2` at `[10, 19]`, so the test sees a lost span.
#[test]
fn an_implied_span_is_put_back_when_a_name_on_its_path_is_forgotten() {
    let p = Premises::new();
    let n = named(4, "x");
    let build = |span: bool| {
        let mut s = ints(&n);
        for (i, x) in n.iter().enumerate() {
            let b = (10 * (3 - i)) as i64;
            s = s.assume(&prim(Prim::Ge, var(x), int(b)), true, &p).assume(
                &prim(Prim::Le, var(x), int(b + 9)),
                true,
                &p,
            );
        }
        for i in 0..3 {
            s = s.assume(&ge(&n[i], &n[i + 1], 10), true, &p).assume(
                &ge(&n[i + 1], &n[i], -11),
                true,
                &p,
            );
        }
        if span {
            s = s.assume(&ge(&n[0], &n[2], 20), true, &p);
        }
        s
    };
    let forget_fix = |mut s: Scope| {
        let _ = s.bind(
            &n[1],
            Product::of_type(Type::int()),
            &zed_kernel::Shared::new(Term::Var(n[1].clone())),
        );
        s.assume(&prim(Prim::Eq, var(&n[0]), int(30)), true, &p)
    };
    let joined = |span: bool| {
        let s = build(span);
        let a = s.assume(&prim(Prim::Ne, var(&n[3]), int(1)), true, &p);
        let b = s.assume(&prim(Prim::Ne, var(&n[3]), int(2)), true, &p);
        a.join(&b)
    };
    for (what, s, want) in [
        ("kept", forget_fix(build(true)), IntervalSet::single(10)),
        ("joined", forget_fix(joined(true)), IntervalSet::single(10)),
        ("control", forget_fix(build(false)), IntervalSet::of(10, 19)),
        (
            "joined control",
            forget_fix(joined(false)),
            IntervalSet::of(10, 19),
        ),
    ] {
        assert_eq!(s.get(&n[2]).ints().clone(), want, "{what}\n{s}");
    }
}

/// The band of [`band_holes_run`] at `k = 5`, 10 and 20: no refusal, and each name keeps
/// exactly its values in the closed form `x_i = [b, b + 9]` less `b + 5` for `i < k - 1`,
/// `[b, b + 9]` otherwise, `b = 10 (k - i)`. Proof (cross-review XR-st-band-quintic r1, Claude
/// Q3): `x_i = 10 (k - i) + c` with one constant `c != 5` meets every step and rung, so each
/// value but `b + 5` is reached; for `c = 5` at a name `x_j` with no hole (`j >= k - 1`), the
/// names before it take `c = 6`, each step falling by at most 1 so each difference stays in
/// `[10, 11]`, and each rung holds as two steps sum to 20 or more. A hull narrowing also passes
/// the sets (Claude's negative control); the refusal check is what fails before D1
/// (a54e9543a). `bench::a_band_with_holes_and_joined_rungs_takes_near_linear_time` measures its
/// cost.
#[test]
fn a_band_with_holes_and_joined_rungs_is_exact() {
    for k in [5, 10, 20] {
        check_band_holes(k);
    }
}

fn check_band_holes(k: usize) {
    let p = Premises::new();
    let s = band_holes_run(k, &p);
    let n = named(k + 1, "x");
    assert!(
        s.refused_on(n.iter().map(|x| &**x)).is_empty(),
        "a refusal on the band at k = {k}"
    );
    for (i, x) in n.iter().enumerate() {
        let ints = s.get(x).ints().clone();
        assert_eq!(ints, band_closed_form(k, i), "{x} at k = {k}");
    }
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

/// The trees of differences of seed 1597508919132665080 give the projection from scratch: at
/// case 3 step 9, `x0 - x6 >= -1`, `x6 - x2 >= 1`, `x2 - x0 >= 0` with `x6` in `{0, 2}` make a
/// cycle of weight 0 of three edges, so `x0 = x2 = x6 - 1` keep the hole of `x6`
/// (`holes::tie_cycles`; the projection from scratch kept the hulls).
#[test]
fn holes_in_the_tree_of_differences_of_seed_1597508919132665080() {
    holes_in_trees(1597508919132665080, false, HOLE_TREES);
}

/// The piled trees of seed 7824212788089549554 give the projection from scratch: the join of
/// the cases of a test placed a star whose hub moved against its own relation, where the star
/// was not yet a leaf, so the order lost it and a later move of the hub left the star's
/// projection as it was (FAIL-linked-held-wider-seed, `Order::unmark`).
#[test]
fn holes_piled_in_the_trees_of_seed_7824212788089549554_give_the_projection_from_scratch() {
    holes_in_trees(7824212788089549554, true, HOLE_TREES);
}

/// The piled trees of seed 5509389503070729707 give the projection from scratch, as those of
/// seed 7824212788089549554.
#[test]
fn holes_piled_in_the_trees_of_seed_5509389503070729707_give_the_projection_from_scratch() {
    holes_in_trees(5509389503070729707, true, HOLE_TREES);
}

/// The trees of seed 14632382012997512814 give the projection from scratch, as those of
/// seed 7824212788089549554.
#[test]
fn holes_in_the_trees_of_seed_14632382012997512814_give_the_projection_from_scratch() {
    holes_in_trees(14632382012997512814, false, HOLE_TREES);
}

/// Seed 7824212788089549554 made minimal: after the join of the cases of
/// `x4 != -1 && x3 - x4 >= 2`, the star of `x2` at its hub `x3` is placed in the order again,
/// so that `x3 != 0` failing, which fixes `x3` at 0, also moves `x2` to `[..0]`, where
/// the held projection left it at `[..1]`. Each step's intervals are those of the projection
/// from scratch.
#[test]
fn a_star_unmarked_by_a_join_is_projected_again_when_its_hub_moves() {
    let p = Premises::new();
    let ns = named(5, "x");
    let v = |n: usize| var(&ns[n]);
    let d = |a: usize, b: usize| prim(Prim::Sub, v(a), v(b));
    let mut s = ints(&ns);
    s = s.assume(&prim(Prim::Ge, v(0), int(-3)), true, &p);
    s = s.assume(&prim(Prim::Le, v(3), int(1)), true, &p);
    s = s.assume(&prim(Prim::Ge, d(4, 0), int(2)), true, &p);
    s = s.assume(&prim(Prim::Ge, d(3, 2), int(0)), true, &p);
    let t = prim(
        Prim::And,
        prim(Prim::Ne, v(4), int(-1)),
        prim(Prim::Ge, d(3, 4), int(2)),
    );
    let mut s = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
    s.reduce();
    let hole = prim(Prim::Ne, v(3), int(0));
    let got = s.assume(&hole, false, &p);
    let mut fresh = s.clone();
    fresh.forget_projections();
    let mut want = fresh.assume(&hole, false, &p);
    want.forget_projections();
    want.reduce();
    assert_eq!(intervals(&got, &ns), intervals(&want, &ns));
}

/// The trees of seed 15479193071854034191 give the projection from scratch.
#[test]
fn holes_in_the_trees_of_seed_15479193071854034191_give_the_projection_from_scratch() {
    holes_in_trees(15479193071854034191, false, HOLE_TREES);
}

/// The steps of `steps` and then `hole` assumed false give the projection from scratch.
fn hole_false_gives_the_projection_from_scratch(k: usize, steps: &[(Term, bool)], hole: &Term) {
    let p = Premises::new();
    let ns = named(k, "x");
    let mut s = ints(&ns);
    for (t, h) in steps {
        s = s.assume(t, *h, &p);
    }
    let got = s.assume(hole, false, &p);
    let mut fresh = s.clone();
    fresh.forget_projections();
    let mut want = fresh.assume(hole, false, &p);
    want.forget_projections();
    want.reduce();
    assert_eq!(intervals(&got, &ns), intervals(&want, &ns));
}

/// Seed 15479193071854034191 made minimal: one case of the hole survives.
#[test]
fn a_hole_left_with_one_case_wakes_the_parts_of_its_groups() {
    let ns = named(4, "x");
    let v = |n: usize| var(&ns[n]);
    let d = |a: usize, b: usize| prim(Prim::Sub, v(a), v(b));
    let and = |a: Term, b: Term| prim(Prim::And, a, b);
    let steps = [
        (prim(Prim::Le, v(1), int(4)), true),
        (
            and(
                prim(Prim::Ne, v(2), int(7)),
                prim(Prim::Ge, d(0, 2), int(-2)),
            ),
            true,
        ),
        (
            and(
                prim(Prim::Ne, v(2), int(-4)),
                prim(Prim::Ge, d(1, 2), int(2)),
            ),
            true,
        ),
        (prim(Prim::Ge, d(2, 1), int(-2)), true),
        (prim(Prim::Ge, d(1, 0), int(2)), true),
        (prim(Prim::Ge, d(1, 3), int(2)), true),
        (
            and(
                prim(Prim::Ne, v(2), int(1)),
                prim(Prim::Ge, d(3, 2), int(-1)),
            ),
            false,
        ),
    ];
    let hole = and(
        prim(Prim::Ne, v(3), int(2)),
        prim(Prim::Ge, d(0, 3), int(2)),
    );
    hole_false_gives_the_projection_from_scratch(4, &steps, &hole);
}

/// The test above with the hole's two conditions swapped, so that the case left is the first
/// one split off and the empty one (`x3 == 2`) the second.
#[test]
fn a_hole_left_with_its_first_case_wakes_the_parts_of_its_groups() {
    let ns = named(4, "x");
    let v = |n: usize| var(&ns[n]);
    let d = |a: usize, b: usize| prim(Prim::Sub, v(a), v(b));
    let and = |a: Term, b: Term| prim(Prim::And, a, b);
    let steps = [
        (prim(Prim::Le, v(1), int(4)), true),
        (
            and(
                prim(Prim::Ne, v(2), int(7)),
                prim(Prim::Ge, d(0, 2), int(-2)),
            ),
            true,
        ),
        (
            and(
                prim(Prim::Ne, v(2), int(-4)),
                prim(Prim::Ge, d(1, 2), int(2)),
            ),
            true,
        ),
        (prim(Prim::Ge, d(2, 1), int(-2)), true),
        (prim(Prim::Ge, d(1, 0), int(2)), true),
        (prim(Prim::Ge, d(1, 3), int(2)), true),
        (
            and(
                prim(Prim::Ne, v(2), int(1)),
                prim(Prim::Ge, d(3, 2), int(-1)),
            ),
            false,
        ),
    ];
    let hole = and(
        prim(Prim::Ge, d(0, 3), int(2)),
        prim(Prim::Ne, v(3), int(2)),
    );
    hole_false_gives_the_projection_from_scratch(4, &steps, &hole);
}

/// The trees of seed 1217883182935025609 give the projection from scratch.
#[test]
fn holes_in_the_trees_of_seed_1217883182935025609_give_the_projection_from_scratch() {
    holes_in_trees(1217883182935025609, false, HOLE_TREES);
}

/// The trees of seed 5815247056960035517 give the projection from scratch.
#[test]
fn holes_in_the_trees_of_seed_5815247056960035517_give_the_projection_from_scratch() {
    holes_in_trees(5815247056960035517, false, HOLE_TREES);
}

/// Seed 216 of [`holes_in_a_tree_of_differences_give_the_projection_from_scratch`], case 2 step
/// 12: the hole `x2 != x0 + 1` is held, and the test `x3 != 0 && x0 - x3 >= 2` is false with
/// both its cases alive. The second case's `x0 - x3 <= 1` joins the group of differences that
/// holds `x0` and `x2`, so it narrows the hole's part only through that group: `x3 = -6` needs
/// `x2 = -4`, `x1 = -2` and `x0 = -5 = x2 - 1`, which the hole excludes, so `x3` is in
/// `[-5..=2]` (FAIL-linked-two-cases-seed-216; held `[-6..=2]` before the fix).
#[test]
fn holes_in_the_trees_of_seed_216_give_the_projection_from_scratch() {
    holes_in_trees(216, false, HOLE_TREES);
}

/// The piled trees of seed 14072984267085997581 give the projection from scratch: both cases of
/// a hole survive (FAIL-linked-case-group-wake; held `x2` `[0..]` before the fix, from scratch
/// `[1..]`).
#[test]
fn holes_piled_in_the_trees_of_seed_14072984267085997581_give_the_projection_from_scratch() {
    holes_in_trees(14072984267085997581, true, HOLE_TREES);
}

/// Seed 14072984267085997581 made minimal: both cases of the hole survive, and the first one's
/// `x0 <= x2 - 3` reaches the part `!(x2 == x1 + 2)` only through the group of `x0 - x1 >= -1`.
#[test]
fn a_hole_left_with_two_cases_wakes_the_parts_of_their_groups() {
    let ns = named(3, "x");
    let v = |n: usize| var(&ns[n]);
    let d = |a: usize, b: usize| prim(Prim::Sub, v(a), v(b));
    let and = |a: Term, b: Term| prim(Prim::And, a, b);
    let steps = [
        (prim(Prim::Ge, v(1), int(-2)), true),
        (prim(Prim::Le, v(1), int(1)), true),
        (prim(Prim::Ge, v(2), int(0)), true),
        (
            and(
                prim(Prim::Ne, v(2), int(6)),
                prim(Prim::Ge, d(0, 2), int(1)),
            ),
            false,
        ),
        (prim(Prim::Ge, d(0, 1), int(-1)), true),
        (prim(Prim::Eq, d(2, 1), int(2)), false),
    ];
    let hole = and(
        prim(Prim::Ne, v(2), int(4)),
        prim(Prim::Ge, d(0, 2), int(-2)),
    );
    hole_false_gives_the_projection_from_scratch(3, &steps, &hole);
}

/// Seed 60 of [`shortest_paths_give_the_intervals_of_the_projection_block_by_block`], pinned
/// (LINKED-incremental-scratch-agree (a)). On 9bfce9cf8 its case 16 step 7, the test assumed
/// false, left the incremental scope at `x0 <= -5` where the projection from scratch was empty:
/// the incremental path missed a negative cycle. 614b9d0cf (FLAKE-l01-39-scope-one-failure)
/// found the cause, the potential's order read the edges of one tree only, and
/// [`a_join_that_moves_a_name_to_another_tree_keeps_its_cycles_found`] is its minimized form.
/// The draws of [`random_ladders`] are those of the test on 9bfce9cf8 (compared line by line
/// 2026-11-21), so this runs the failing case itself; every step agrees on 7b58d316e.
#[test]
fn shortest_paths_of_seed_60_agree_with_the_projection_from_scratch() {
    random_ladders(60);
}

/// Seed 25 of [`holes_in_trees`] at 6 trees, without and with piling, pinned
/// (LINKED-incremental-scratch-agree (b)). On 9bfce9cf8 its case 4 step 17, the hole `x0 != 1`
/// false, gave `x7` in `[-1, 1]` incrementally and `[-2, 1]` from scratch. The generator's
/// draws are those of the test on 9bfce9cf8 (compared line by line 2026-11-21); every step of
/// both runs agrees on 7b58d316e. The commit that made them agree was not found: this test
/// holds the agreement from now on.
#[test]
fn holes_of_seed_25_agree_with_the_projection_from_scratch() {
    holes_in_trees(25, false, 6);
    holes_in_trees(25, true, 6);
}

/// Seed 90 of [`holes_in_a_tree_of_differences_give_the_projection_from_scratch`], case 2 step
/// 11: with x3 >= x0 + 2, x1 <= x0 - 1, x2 <= x1 + 2, x2 - 1 <= x3 <= x2 + 2 and
/// x0 != x2 + 1 held, `x0 != -3` leaves x3 = -1 with no point (it needs x0 = -4, x1 = -5,
/// x2 = -4 and then x3 <= -2), so x3 is {-2} and [1..=5] (FAIL-linked-holes-seed-90; held
/// [-2..=-1] and [1..=5] while the scope's projection gave each disjunct its hull).
#[test]
fn holes_in_the_trees_of_seed_90_give_the_projection_from_scratch() {
    holes_in_trees(90, false, HOLE_TREES);
}
