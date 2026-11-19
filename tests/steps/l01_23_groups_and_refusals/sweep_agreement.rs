//! The front sweep agrees with an oracle that does not use it. Each case is a list of
//! definition groups whose bodies are `nil` and rows `cons(head, tail)`; a head is a union of
//! the eleven element classes below, which are the cells of every head used here, so a list
//! type is a finite automaton over eleven letters. The oracle runs a breadth-first search over
//! the sets of definitions a word can reach. Every family variant at n <= 6 is checked (each
//! skipped place, `m` from 1 to n + 2, the integer, boolean, tuple and atom head sets, split
//! and joined groups, meets and pairs), and random small families of chains. Then: redundant
//! chains of the `groupsholes` kind with cofinite heads (`int` less one integer), links whose
//! body is a union of rows (the `chain` kind), random links with cofinite heads, staggered
//! chains whose heads hold an atom the carrier's head leaves out (the `stagger` kind), and an order
//! test: each case built again with its definitions and every union's operands reversed has
//! the same verdict. Each case also checks the sweep's own answer (`Type::sweep_verdict`)
//! against the oracle, and the tallies count the cases the sweep decides.

use std::collections::{BTreeSet, HashSet, VecDeque};

use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::Rng;

// The element classes: 0 is an integer other than 1 to 5, 1 and 2 the integers, 3 false,
// 4 true, 5 a pair with a 1 first, 6 a pair of integers without, 7 the atom `a`, 8 to 10 the
// integers 3 to 5.
const CLASSES: usize = 11;
const INT: u16 = 0b111_0000_0111;
const ONE: u16 = 0b10;
const TWO: u16 = 0b100;
const BOOL: u16 = 0b11000;
const TRUE: u16 = 0b10000;
const PAIR: u16 = 0b110_0000;
const PAIR_ONE: u16 = 0b10_0000;
const ATOM: u16 = 0b1000_0000;
/// `int` less 3, 4 or 5: cofinite heads, distinct.
const HOLES: [u16; 3] = [INT & !(1 << 8), INT & !(1 << 9), INT & !(1 << 10)];

fn class(c: usize) -> Type {
    let lit = |v| Type::lit(&v).unwrap();
    let one = lit(Value::Int(1));
    match c {
        0 => (1..=5).fold(Type::int(), |t, k| &t - &lit(Value::Int(k))),
        1 => one,
        2 => lit(Value::Int(2)),
        3 => &Type::bool() - &lit(Value::Bool(true)),
        4 => lit(Value::Bool(true)),
        5 => Type::tuple(vec![one, Type::int()]),
        6 => Type::tuple(vec![&Type::int() - &one, Type::int()]),
        7 => Type::atom("a"),
        _ => lit(Value::Int(c as i64 - 5)),
    }
}

fn head(mask: u16) -> Type {
    // Both pair cells as one product, the form the sweep reads; the union of the two cells is
    // left to the search.
    if mask & PAIR == PAIR {
        return &head(mask & !PAIR) | &Type::tuple(vec![Type::int(), Type::int()]);
    }
    (0..CLASSES)
        .filter(|c| mask >> c & 1 == 1)
        .fold(Type::empty(), |u, c| &u | &class(c))
}

/// A definition: `nil` or not, and rows `cons(head, tail)` with the tail in the same group.
#[derive(Clone)]
struct D {
    nil: bool,
    rows: Vec<(u16, usize)>,
}

/// A list type: the words of every `pos` definition and of no `neg` definition, by (group,
/// definition).
struct Term {
    pos: Vec<(usize, usize)>,
    neg: Vec<(usize, usize)>,
}

struct Spec {
    groups: Vec<Vec<D>>,
}

impl Spec {
    /// The spec with each group's definitions and each definition's rows in reverse order, and
    /// the term mapped to it with its positive and negative operands reversed.
    fn reversed(&self, t: &Term) -> (Spec, Term) {
        let groups = (self.groups.iter())
            .map(|ds| {
                let k = ds.len();
                (ds.iter().rev())
                    .map(|d| D {
                        nil: d.nil,
                        rows: d.rows.iter().rev().map(|&(h, t)| (h, k - 1 - t)).collect(),
                    })
                    .collect()
            })
            .collect();
        let map = |v: &[(usize, usize)]| {
            (v.iter().rev())
                .map(|&(g, d)| (g, self.groups[g].len() - 1 - d))
                .collect()
        };
        let term = Term {
            pos: map(&t.pos),
            neg: map(&t.neg),
        };
        (Spec { groups }, term)
    }

    /// The types of the definitions; with `rev`, each body's operands in reverse order (`nil`
    /// last).
    fn build_in(&self, tag: &str, rev: bool) -> Vec<Vec<Type>> {
        self.groups
            .iter()
            .enumerate()
            .map(|(g, ds)| {
                let defs = ds
                    .iter()
                    .enumerate()
                    .map(|(i, d)| {
                        let mut alts = Vec::new();
                        if d.nil {
                            alts.push(Expr::Type(Type::atom("nil")));
                        }
                        alts.extend(d.rows.iter().map(|&(h, t)| {
                            Expr::Atom(
                                "cons".into(),
                                vec![Expr::Type(head(h)), Expr::Ref(t, vec![])],
                            )
                        }));
                        if rev {
                            alts.reverse();
                        }
                        let body = if alts.len() == 1 {
                            alts.remove(0)
                        } else {
                            Expr::Union(alts)
                        };
                        Def {
                            name: format!("D{g}_{i}{tag}"),
                            params: vec![],
                            body,
                        }
                    })
                    .collect();
                Group::new(defs).unwrap().instance(vec![])
            })
            .collect()
    }

    fn build(&self, tag: &str) -> Vec<Vec<Type>> {
        self.build_in(tag, false)
    }

    fn ty(&self, ts: &[Vec<Type>], t: &Term) -> Type {
        let pos = t.pos.iter().fold(None, |a: Option<Type>, &(g, d)| {
            Some(a.map_or(ts[g][d].clone(), |a| &a & &ts[g][d]))
        });
        let neg = t
            .neg
            .iter()
            .fold(Type::empty(), |u, &(g, d)| &u | &ts[g][d]);
        &pos.unwrap() - &neg
    }

    fn step(&self, s: &BTreeSet<(usize, usize)>, c: usize) -> BTreeSet<(usize, usize)> {
        s.iter()
            .flat_map(|&(g, d)| {
                self.groups[g][d]
                    .rows
                    .iter()
                    .filter(move |r| r.0 >> c & 1 == 1)
                    .map(move |r| (g, r.1))
            })
            .collect()
    }

    fn nil(&self, s: &BTreeSet<(usize, usize)>) -> bool {
        s.iter().any(|&(g, d)| self.groups[g][d].nil)
    }

    /// The oracle: some word reaches a state where every positive set accepts `nil` and the
    /// negative set does not.
    fn inhabited(&self, t: &Term) -> bool {
        type S = Vec<BTreeSet<(usize, usize)>>;
        let mut start: S = t.pos.iter().map(|&p| BTreeSet::from([p])).collect();
        start.push(t.neg.iter().copied().collect());
        let mut seen: HashSet<S> = HashSet::from([start.clone()]);
        let mut queue = VecDeque::from([start]);
        while let Some(s) = queue.pop_front() {
            let (ps, n) = s.split_at(s.len() - 1);
            if ps.iter().all(|p| self.nil(p)) && !self.nil(&n[0]) {
                return true;
            }
            for c in 0..CLASSES {
                let next: S = s.iter().map(|x| self.step(x, c)).collect();
                if next[..next.len() - 1].iter().all(|p| !p.is_empty()) && seen.insert(next.clone())
                {
                    queue.push_back(next);
                }
            }
        }
        false
    }
}

#[derive(Default, Debug)]
struct Tally {
    cases: usize,
    empty: usize,
    inhabited: usize,
    refused: usize,
    /// The cases the sweep decides, and of those the empty ones.
    swept: usize,
    swept_empty: usize,
    /// The cases the sweep leaves to the search in both orders and whose two verdicts differ:
    /// the search's own, which depends on order there, printed, not failed.
    base_order: usize,
}

impl Tally {
    /// Checks one verdict, and the sweep's own when it gives one, against the oracle's answer.
    fn check(&mut self, t: &Type, inhabited: bool, what: &str) {
        Type::forget_emptiness();
        let s = t.sweep_verdict();
        Type::forget_emptiness();
        // The prefix chains alone, also where the front sweep answers first (R5).
        let c = t.chain_verdict();
        Type::forget_emptiness();
        let v = t.verdict();
        if let Some(c) = c {
            assert_eq!(
                c, v,
                "{what}: the prefix chains say {c:?}, the verdict is {v:?}"
            );
        }
        if let Some(s) = s {
            assert_eq!(s, v, "{what}: the sweep says {s:?}, the verdict is {v:?}");
            self.swept += 1;
            self.swept_empty += usize::from(s == Verdict::Empty);
        }
        Type::forget_emptiness();
        let e = t.is_empty();
        self.cases += 1;
        match v {
            Verdict::Empty => {
                assert!(!inhabited, "{what}: Empty, but the oracle finds a value");
                self.empty += 1;
            }
            Verdict::Inhabited => {
                assert!(inhabited, "{what}: Inhabited, but the oracle finds none");
                self.inhabited += 1;
            }
            Verdict::Refused(_) => self.refused += 1,
        }
        assert!(
            !(e && inhabited),
            "{what}: is_empty, but the oracle finds a value"
        );
    }
}

/// The front family as a spec: `L` the lists of `all`, `F1 = cons(one, L)`,
/// `Fi = cons(all, F{i-1})`, `Mk = nil | cons(all - one, M{k-1})` (with `M0 = L`); `split` puts
/// the `M{k}` in a group of their own with its own `L`. The term is `L` less every `Fi` but
/// `skip`, and `Mm`.
fn family(n: usize, skip: usize, m: usize, all: u16, one: u16, split: bool) -> (Vec<Vec<D>>, Term) {
    let l = D {
        nil: true,
        rows: vec![(all, 0)],
    };
    let mut f = vec![
        l.clone(),
        D {
            nil: false,
            rows: vec![(one, 0)],
        },
    ];
    f.extend((2..=n).map(|i| D {
        nil: false,
        rows: vec![(all, i - 1)],
    }));
    let base = if split { 0 } else { n };
    let mut ms = if split { vec![l] } else { vec![] };
    ms.extend((1..=m).map(|k| D {
        nil: true,
        rows: vec![(all & !one, if k == 1 { 0 } else { base + k - 1 })],
    }));
    let groups = if split {
        vec![f, ms]
    } else {
        vec![f.into_iter().chain(ms).collect()]
    };
    let neg = (1..=n)
        .filter(|&i| i != skip)
        .map(|i| (0, i))
        .chain([(if split { 1 } else { 0 }, base + m)])
        .collect();
    (
        groups,
        Term {
            pos: vec![(0, 0)],
            neg,
        },
    )
}

/// The head sets: integers by a 1, booleans by `true`, pairs by a 1 first, integers and an
/// atom by a 1 or by the atom.
const HEADS: [(u16, u16); 5] = [
    (INT, ONE),
    (BOOL, TRUE),
    (PAIR, PAIR_ONE),
    (INT | ATOM, ONE),
    (INT | ATOM, ATOM),
];

fn families(heads: &[(u16, u16)], splits: &[bool]) -> Tally {
    let mut tally = Tally::default();
    let mut id = 0;
    for &(all, one) in heads {
        for &split in splits {
            for n in 1..=6 {
                for skip in 0..=n {
                    for m in 1..=n + 2 {
                        let (groups, term) = family(n, skip, m, all, one, split);
                        let spec = Spec { groups };
                        id += 1;
                        let ts = spec.build(&format!("_xa{id}"));
                        let what = format!(
                            "family all {all:#b} one {one:#b} split {split} n {n} skip {skip} m {m}"
                        );
                        tally.check(&spec.ty(&ts, &term), spec.inhabited(&term), &what);
                    }
                }
            }
        }
    }
    tally
}

#[test]
fn the_sweep_agrees_on_integer_families() {
    let t = families(&HEADS[..1], &[false, true]);
    eprintln!("integer families: {t:?}");
}

#[test]
fn the_sweep_agrees_on_boolean_families() {
    let t = families(&HEADS[1..2], &[false, true]);
    eprintln!("boolean families: {t:?}");
}

#[test]
fn the_sweep_agrees_on_pair_head_families() {
    let t = families(&HEADS[2..3], &[false, true]);
    eprintln!("pair head families: {t:?}");
}

#[test]
fn the_sweep_agrees_on_atom_head_families() {
    let t = families(&HEADS[3..], &[false, true]);
    eprintln!("atom head families: {t:?}");
}

/// Meets of two families of one size, and pairs of two families: every skipped place of each,
/// with `m = n`.
#[test]
fn the_sweep_agrees_on_meets_and_pairs() {
    let t = {
        let mut tally = Tally::default();
        let mut id = 0;
        for &(all, one) in &HEADS[..2] {
            for n in 1..=5 {
                for s1 in 0..=n {
                    for s2 in 0..=n {
                        let (g1, t1) = family(n, s1, n, all, one, false);
                        let (g2, t2) = family(n, s2, n, all, one, false);
                        let k = g1.len();
                        let spec = Spec {
                            groups: g1.into_iter().chain(g2).collect(),
                        };
                        id += 1;
                        let ts = spec.build(&format!("_xm{id}"));
                        let shift = |v: Vec<(usize, usize)>| {
                            v.into_iter().map(|(g, d)| (g + k, d)).collect()
                        };
                        let t2 = Term {
                            pos: shift(t2.pos),
                            neg: shift(t2.neg),
                        };
                        let (a, b) = (spec.ty(&ts, &t1), spec.ty(&ts, &t2));
                        let meet = Term {
                            pos: t1.pos.iter().chain(&t2.pos).copied().collect(),
                            neg: t1.neg.iter().chain(&t2.neg).copied().collect(),
                        };
                        let what = format!("all {all:#b} n {n} skips {s1} {s2}");
                        tally.check(&(&a & &b), spec.inhabited(&meet), &format!("meet {what}"));
                        let pair = spec.inhabited(&t1) && spec.inhabited(&t2);
                        tally.check(&Type::tuple(vec![a, b]), pair, &format!("pair {what}"));
                    }
                }
            }
        }
        tally
    };
    eprintln!("meets and pairs: {t:?}");
}

/// Random families of chains: a list `L` of all heads used, and up to six definitions with
/// `nil` or not and one or two rows of random heads and tails, some of them less the union of
/// a random set of the definitions; one group, or two with the second's tails into itself.
#[test]
fn the_sweep_agrees_on_random_chains() {
    let t = {
        let mut tally = Tally::default();
        let (mut rng, _) = Rng::fresh("random chains");
        let palette = [
            INT,
            ONE,
            INT & !ONE,
            TWO,
            INT & !ONE & !TWO,
            BOOL,
            TRUE,
            BOOL & !TRUE,
            PAIR,
            PAIR_ONE,
            PAIR & !PAIR_ONE,
            INT | ATOM,
            ATOM,
        ];
        for id in 0..500 {
            let k = 1 + rng.below(6);
            let all = (0..3).fold(0, |a, _| a | palette[rng.below(palette.len())]);
            let mut ds = vec![D {
                nil: true,
                rows: vec![(all, 0)],
            }];
            for _ in 0..k {
                let rows = (0..1 + rng.below(2))
                    .map(|_| (palette[rng.below(palette.len())] & all, rng.below(k + 1)))
                    .filter(|r| r.0 != 0)
                    .collect::<Vec<_>>();
                let nil = rows.is_empty() || rng.below(3) == 0;
                ds.push(D { nil, rows });
            }
            let neg = (1..=k)
                .filter(|_| rng.below(2) == 0)
                .map(|i| (0, i))
                .collect();
            let spec = Spec { groups: vec![ds] };
            let term = Term {
                pos: vec![(0, 0)],
                neg,
            };
            let ts = spec.build(&format!("_xr{id}"));
            tally.check(
                &spec.ty(&ts, &term),
                spec.inhabited(&term),
                &format!("random {id}"),
            );
        }
        tally
    };
    eprintln!("random chains: {t:?}");
}

/// Case 394 of `the_sweep_agrees_on_random_chains` with `ZED_TEST_SEED=256`, which never ended.
/// Inside the search, the cells of one tuple component, list types `cons(int \ 1 \ 2, _)` and
/// `cons(int \ 1, _)` over these definitions, were read as each within the next in a cycle,
/// though they are strictly nested, while one of them was still being decided. The walk up the
/// cells holding each piece then went round that cycle forever. The type is inhabited: `[3]` is
/// in `D0` and in none of `D1`, `D3` and `D6`.
#[test]
fn the_search_ends_when_cells_are_read_as_nested_in_a_cycle() {
    let int_less_1 = INT & !ONE;
    let int_less_1_2 = INT & !ONE & !TWO;
    let row = |h, t| (h, t);
    let d = |nil, rows| D { nil, rows };
    let spec = Spec {
        groups: vec![vec![
            d(true, vec![row(int_less_1, 0)]),
            d(true, vec![]),
            d(true, vec![row(int_less_1, 0), row(int_less_1, 4)]),
            d(true, vec![row(int_less_1_2, 3), row(int_less_1, 6)]),
            d(false, vec![row(int_less_1_2, 5)]),
            d(true, vec![]),
            d(true, vec![row(int_less_1, 1), row(int_less_1_2, 4)]),
        ]],
    };
    let term = Term {
        pos: vec![(0, 0)],
        neg: vec![(0, 1), (0, 3), (0, 6)],
    };
    assert!(spec.inhabited(&term));
    let ts = spec.build("_xr394");
    let mut tally = Tally::default();
    tally.check(&spec.ty(&ts, &term), true, "cells nested in a cycle");
    assert_eq!(tally.inhabited, 1, "{tally:?}");
}

/// Random families of links, the sweep's shape: up to eight definitions of one row each, with
/// `nil` or not, over the integer cells or the boolean ones, less the union of most of them.
#[test]
fn the_sweep_agrees_on_random_links() {
    let t = random_links(Rng::fresh("random links").0);
    eprintln!("random links: {t:?}");
}

/// The cases of [`the_sweep_agrees_on_random_links`], drawn from `rng`.
fn random_links(mut rng: Rng) -> Tally {
    let mut tally = Tally::default();
    let sets: [&[u16]; 2] = [
        &[INT, ONE, INT & !ONE, TWO, INT & !TWO, ONE | TWO],
        &[BOOL, TRUE, BOOL & !TRUE],
    ];
    for id in 0..400 {
        let palette = sets[rng.below(2)];
        let all = palette[0];
        let k = 1 + rng.below(8);
        let mut ds = vec![D {
            nil: true,
            rows: vec![(all, 0)],
        }];
        ds.extend((0..k).map(|_| D {
            nil: rng.below(3) == 0,
            rows: vec![(palette[rng.below(palette.len())], rng.below(k + 1))],
        }));
        let neg = (1..=k)
            .filter(|_| rng.below(4) != 0)
            .map(|i| (0, i))
            .collect();
        let spec = Spec { groups: vec![ds] };
        let term = Term {
            pos: vec![(0, 0)],
            neg,
        };
        let ts = spec.build(&format!("_xl{id}"));
        tally.check(
            &spec.ty(&ts, &term),
            spec.inhabited(&term),
            &format!("links {id}"),
        );
    }
    tally
}

/// Checks a case, then the case built again with every definition list, row list, body and
/// operand list reversed ([`Spec::reversed`], [`Spec::build_in`]); the two must have the same
/// answer from the sweep, and the same verdict when the sweep decides. When it decides neither,
/// a difference is the search's own, counted and printed.
fn both_orders(tally: &mut Tally, spec: &Spec, term: &Term, tag: &str, what: &str) {
    let inhabited = spec.inhabited(term);
    let ts = spec.build(tag);
    let a = spec.ty(&ts, term);
    tally.check(&a, inhabited, what);
    let (rspec, rterm) = spec.reversed(term);
    assert_eq!(
        rspec.inhabited(&rterm),
        inhabited,
        "{what}: the oracle depends on order"
    );
    let rts = rspec.build_in(&format!("{tag}r"), true);
    let b = rspec.ty(&rts, &rterm);
    tally.check(&b, inhabited, &format!("{what} reversed"));
    Type::forget_emptiness();
    let (sa, sb) = (a.sweep_verdict(), b.sweep_verdict());
    Type::forget_emptiness();
    let va = a.verdict();
    Type::forget_emptiness();
    let vb = b.verdict();
    Type::forget_emptiness();
    let ca = a.chain_verdict();
    Type::forget_emptiness();
    let cb = b.chain_verdict();
    assert_eq!(ca, cb, "{what}: the prefix chains depend on order");
    assert_eq!(sa, sb, "{what}: the sweep's answer depends on order");
    if sa.is_some() {
        assert_eq!(va, vb, "{what}: the verdict depends on order");
    } else if va != vb {
        tally.base_order += 1;
        eprintln!("base order: {what}: {va:?} / {vb:?}");
    }
}

/// The front family at `n` without `skip`, `m = n`, less also `B = cons(int, A)` with
/// `A = cons(h, t)` for each chain `(h, t)`: the redundant rows of the `groupsholes` kind
/// (`t = 1` is `F1`), with cofinite heads among the `h`.
fn holes(n: usize, skip: usize, chains: &[(u16, usize)]) -> (Spec, Term) {
    let (mut groups, mut term) = family(n, skip, n, INT, ONE, false);
    for &(h, t) in chains {
        let a = groups[0].len();
        groups[0].push(D {
            nil: false,
            rows: vec![(h, t)],
        });
        groups[0].push(D {
            nil: false,
            rows: vec![(INT, a)],
        });
        term.neg.push((0, a + 1));
    }
    (Spec { groups }, term)
}

/// The chain heads: three cofinite, `int`, a 1 or a 2, a 2.
const CHAIN_HEADS: [u16; 6] = [HOLES[0], HOLES[1], HOLES[2], INT, ONE | TWO, TWO];

/// Every front family at n <= 4, every skip, with no, one or two redundant chains, each a head
/// of [`CHAIN_HEADS`] and a tail `L`, `F1` or `F2`; in both orders. Each run asks every case with
/// no redundant chain and one in ten of the others, drawn afresh (author P169); every case was
/// asked, in 5 s, until TEST-bench-move-l0123.
#[test]
fn the_sweep_agrees_on_redundant_rows_with_cofinite_heads() {
    let t = {
        let mut tally = Tally::default();
        let mut id = 0;
        let (mut rng, _) = Rng::fresh("redundant rows");
        for n in 1..=4 {
            let tails: Vec<usize> = (0..=n.min(2)).collect();
            let opts: Vec<(u16, usize)> = (CHAIN_HEADS.iter())
                .flat_map(|&h| tails.iter().map(move |&t| (h, t)))
                .collect();
            let mut sets: Vec<Vec<(u16, usize)>> = vec![vec![]];
            sets.extend(opts.iter().map(|&o| vec![o]));
            for i in 0..opts.len() {
                sets.extend(opts[i..].iter().map(|&o| vec![opts[i], o]));
            }
            for skip in 0..=n {
                for chains in &sets {
                    if !chains.is_empty() && rng.below(10) != 0 {
                        continue;
                    }
                    let (spec, term) = holes(n, skip, chains);
                    id += 1;
                    let what = format!("holes n {n} skip {skip} chains {chains:?}");
                    both_orders(&mut tally, &spec, &term, &format!("_xh{id}"), &what);
                }
            }
        }
        tally
    };
    eprintln!("redundant rows: {t:?}");
}

/// The `chain` kind: `L`, `G1 = cons(1, L)`, `Gk = sides | cons(int, G{k-1})` with `sides` a
/// list of rows into `L` or `G1`, and `Mk` as in [`family`]. The terms are `L` less `Gg | Mm`,
/// and `Gg` less `Mm`, for every `g <= n <= 5` and `m <= n + 1`; in both orders. Each run asks one in
/// five of these, drawn afresh (author P169); every one was asked, in 2.5 s, until
/// TEST-bench-move-l0123.
#[test]
fn the_sweep_agrees_on_union_links() {
    let t = {
        let mut tally = Tally::default();
        let mut id = 0;
        let (mut rng, _) = Rng::fresh("union links");
        let sides: [&[(u16, usize)]; 7] = [
            &[(ONE, 0)],
            &[(TWO, 0)],
            &[(ONE | TWO, 0)],
            &[(HOLES[0], 0)],
            &[(ONE, 1)],
            &[(ONE, 0), (TWO, 0)],
            &[(ONE, 0), (ONE, 1)],
        ];
        for n in 1..=5 {
            for side in sides {
                let mut ds = vec![
                    D {
                        nil: true,
                        rows: vec![(INT, 0)],
                    },
                    D {
                        nil: false,
                        rows: vec![(ONE, 0)],
                    },
                ];
                ds.extend((2..=n).map(|k| D {
                    nil: false,
                    rows: side.iter().copied().chain([(INT, k - 1)]).collect(),
                }));
                ds.extend((1..=n + 1).map(|k| D {
                    nil: true,
                    rows: vec![(INT & !ONE, if k == 1 { 0 } else { n + k - 1 })],
                }));
                let spec = Spec { groups: vec![ds] };
                for g in 1..=n {
                    for m in 1..=n + 1 {
                        for pos in [0, g] {
                            if rng.below(5) != 0 {
                                continue;
                            }
                            let neg = if pos == 0 {
                                vec![(0, g), (0, n + m)]
                            } else {
                                vec![(0, n + m)]
                            };
                            let term = Term {
                                pos: vec![(0, pos)],
                                neg,
                            };
                            id += 1;
                            let what =
                                format!("union links n {n} sides {side:?} g {g} m {m} pos {pos}");
                            both_orders(&mut tally, &spec, &term, &format!("_xu{id}"), &what);
                        }
                    }
                }
            }
        }
        tally
    };
    eprintln!("union links: {t:?}");
}

/// Random links over the integer cells with cofinite heads, one row or (one time in four) two,
/// `nil` or not, less the union of most of them; in both orders.
#[test]
fn the_sweep_agrees_on_random_cofinite_links() {
    let t = {
        let mut tally = Tally::default();
        let (mut rng, _) = Rng::fresh("random cofinite links");
        let palette = [
            INT,
            ONE,
            INT & !ONE,
            TWO,
            ONE | TWO,
            HOLES[0],
            HOLES[1],
            HOLES[2],
            HOLES[0] & !ONE,
            INT & !HOLES[1],
        ];
        for id in 0..150 {
            let k = 1 + rng.below(7);
            let mut ds = vec![D {
                nil: true,
                rows: vec![(INT, 0)],
            }];
            ds.extend((0..k).map(|_| {
                D {
                    nil: rng.below(3) == 0,
                    rows: (0..1 + usize::from(rng.below(4) == 0))
                        .map(|_| (palette[rng.below(palette.len())], rng.below(k + 1)))
                        .collect(),
                }
            }));
            let neg = (1..=k)
                .filter(|_| rng.below(4) != 0)
                .map(|i| (0, i))
                .collect();
            let spec = Spec { groups: vec![ds] };
            let term = Term {
                pos: vec![(0, 0)],
                neg,
            };
            both_orders(
                &mut tally,
                &spec,
                &term,
                &format!("_xc{id}"),
                &format!("cofinite links {id}"),
            );
        }
        tally
    };
    eprintln!("random cofinite links: {t:?}");
}

/// The heads of the staggered chains: each holds the atom, so only the carrier's head makes
/// them alike; and `int`.
const STAGGER_HEADS: [u16; 4] = [INT | ATOM, ATOM, HOLES[0] | ATOM, INT];

/// The `stagger` kind (X12): `L = nil | cons(c, L)` with `c` the integers or the integers and
/// the atom, `Yi = cons(hi, Y{i+1})` for i <= m <= 3 with each `hi` of [`STAGGER_HEADS`],
/// `Y{m+1} = cons(1, L)`, and `Nj = nil | cons(hj, N{j+1})` for j <= m + 1 (`N{m+2}` is `L`)
/// with `hj` the integers for j <= s and the integers but 1 after: the lists with no 1 at
/// places s + 1 to m + 1. All in `L`'s group or a group of their own (with its own `L`); the
/// term is `L` less every nonempty set of the `Yi` and, for each s <= m or none, `N1`; in
/// both orders.
/// The carrier's head reads the atom out of the heads when `c` is the integers.
/// Each run asks every case at m = 1, one in four at m = 2 and one in 32 at m = 3, drawn afresh
/// (author P169); every case was asked, in 9 to 10 s, until TEST-bench-move-l0123.
fn staggered(c: u16) -> Tally {
    {
        let mut tally = Tally::default();
        let mut id = 0;
        let (mut rng, _) = Rng::fresh(&format!("staggered chains, carrier {c:#b}"));
        for m in 1..=3usize {
            let mut seqs: Vec<Vec<u16>> = vec![vec![]];
            for _ in 0..m {
                seqs = (seqs.iter())
                    .flat_map(|s| STAGGER_HEADS.iter().map(move |&h| [&s[..], &[h]].concat()))
                    .collect();
            }
            {
                for ns in 0..=m + 1 {
                    for split in [false, true] {
                        for hs in &seqs {
                            let l = D {
                                nil: true,
                                rows: vec![(c, 0)],
                            };
                            let mut ys = vec![l.clone()];
                            ys.extend(hs.iter().enumerate().map(|(i, &h)| D {
                                nil: false,
                                rows: vec![(h, i + 2)],
                            }));
                            ys.push(D {
                                nil: false,
                                rows: vec![(ONE, 0)],
                            });
                            // `ns` is s + 1, or 0 for no `N`; `N1` is at m + 2.
                            ys.extend((1..=m + 1).map(|j| D {
                                nil: true,
                                rows: vec![(
                                    if j < ns { INT } else { INT & !ONE },
                                    if j == m + 1 { 0 } else { m + 2 + j },
                                )],
                            }));
                            let (groups, g) = if split {
                                (vec![vec![l], ys], 1)
                            } else {
                                (vec![ys], 0)
                            };
                            let spec = Spec { groups };
                            for set in 1..(1usize << m) {
                                if rng.below([1, 1, 4, 32][m]) != 0 {
                                    continue;
                                }
                                let mut neg: Vec<(usize, usize)> = (0..m)
                                    .filter(|i| set >> i & 1 == 1)
                                    .map(|i| (g, i + 1))
                                    .collect();
                                if ns > 0 {
                                    neg.push((g, m + 2));
                                }
                                let term = Term {
                                    pos: vec![(0, 0)],
                                    neg,
                                };
                                id += 1;
                                let what = format!(
                                    "stagger c {c:#b} n {ns} split {split} heads {hs:?} roots {set:#b}"
                                );
                                both_orders(&mut tally, &spec, &term, &format!("_xs{id}"), &what);
                            }
                        }
                    }
                }
            }
        }
        tally
    }
}

/// [`staggered`] with the integers as the carrier's head: the heads are read without the atom.
#[test]
fn the_sweep_agrees_on_staggered_chains_in_the_integers() {
    eprintln!("staggered chains in int: {:?}", staggered(INT));
}

/// [`staggered`] with the integers and the atom as the carrier's head.
#[test]
fn the_sweep_agrees_on_staggered_chains_with_the_atom() {
    eprintln!("staggered chains in int | a: {:?}", staggered(INT | ATOM));
}

/// Random links on no cycle but through `L` (each tail is `L` or a later link), with heads that
/// may hold the atom, which `L`'s do not, and a positive side that is one of them, met with `L`
/// or not: a taken thread whose lists may leave `L`, so the rule that closes a class by `L`
/// when a taken thread's lists are all `L`'s (X17) is tested on both sides of its condition;
/// and several roots into one chain with the same or different holes, so a join below which
/// one class holds fewer negative heads than every other (the dominance choice) is met; and a
/// second carrier met in, so the carrier head is a meet.
#[test]
fn the_sweep_agrees_on_random_positive_chains() {
    let t = random_positive_chains(Rng::fresh("random positive chains").0);
    eprintln!("random positive chains: {t:?}");
    // The sweep decides a case on every run, built (PROOF-test-count-thresholds):
    // `D2 = cons(int, L)` less `D1 = cons(1, L)`, a positive chain of the shape drawn above,
    // holds `[0]` and is inhabited; the sweep decides it in both orders (measured; the negative
    // control of PROOF-test-count-thresholds fails here when the sweep declines it).
    let b = built(&[(ONE, 0), (INT, 0)], &[2], &[1], "pc");
    assert_eq!((b.swept, b.inhabited), (2, 2), "the built case: {b:?}");
}

/// The cases of [`the_sweep_agrees_on_random_positive_chains`], drawn from `rng`.
fn random_positive_chains(mut rng: Rng) -> Tally {
    let mut tally = Tally::default();
    let palette = [
        INT,
        ONE,
        INT & !ONE,
        INT | ATOM,
        ATOM,
        HOLES[0],
        HOLES[0],
        HOLES[1],
        INT & !HOLES[0],
        HOLES[0] | ATOM,
    ];
    for id in 0..300 {
        let k = 2 + rng.below(6);
        let mut ds = vec![D {
            nil: true,
            rows: vec![(INT, 0)],
        }];
        ds.extend((1..=k).map(|i| {
            let tail = |rng: &mut Rng| match rng.below(3) {
                0 => 0,
                _ if i < k => i + 1 + rng.below(k - i),
                _ => 0,
            };
            D {
                nil: rng.below(4) == 0,
                rows: (0..1 + usize::from(rng.below(5) == 0))
                    .map(|_| (palette[rng.below(palette.len())], tail(&mut rng)))
                    .collect(),
            }
        }));
        let p = 1 + rng.below(k);
        let mut pos = vec![(0, p)];
        if rng.below(2) == 0 {
            pos.push((0, 0));
        }
        // A second carrier, `L2 = nil | cons(h, L2)`, met in: the carrier head is the meet
        // of both, whichever comes first.
        if rng.below(3) == 0 {
            let h = [HOLES[0], INT & !ONE, INT | ATOM][rng.below(3)];
            ds.push(D {
                nil: true,
                rows: vec![(h, k + 1)],
            });
            pos.push((0, k + 1));
        }
        let neg = (1..=k)
            .filter(|&i| i != p && rng.below(3) != 0)
            .map(|i| (0, i))
            .collect();
        let spec = Spec { groups: vec![ds] };
        let term = Term { pos, neg };
        both_orders(
            &mut tally,
            &spec,
            &term,
            &format!("_xp{id}"),
            &format!("positive chains {id}"),
        );
    }
    tally
}

/// A case built for a random test of the sweep (PROOF-test-count-thresholds): the carrier
/// `L = nil | cons(int, L)` as definition 0, then a link `cons(head, tail)` for each
/// `(head, tail)` of `links`; checked in both orders ([`both_orders`]) on a tally of its own,
/// which it returns, so a test can assert that the sweep decides it.
fn built(links: &[(u16, usize)], pos: &[usize], neg: &[usize], tag: &str) -> Tally {
    let mut ds = vec![D {
        nil: true,
        rows: vec![(INT, 0)],
    }];
    ds.extend(links.iter().map(|&row| D {
        nil: false,
        rows: vec![row],
    }));
    let spec = Spec { groups: vec![ds] };
    let term = Term {
        pos: pos.iter().map(|&d| (0, d)).collect(),
        neg: neg.iter().map(|&d| (0, d)).collect(),
    };
    let mut tally = Tally::default();
    both_orders(&mut tally, &spec, &term, &format!("_built{tag}"), tag);
    tally
}

/// Disjoint-hole and overlapping-hole spines (X14 / Q2): a spine `Y1..Ym` (`m <= 3`) where each
/// link head is drawn from `HOLES` (`int \ {3}`, `int \ {4}`, `int \ {5}`). When the holes are
/// pairwise distinct, the spine is inside the Disjoint-Hole Spine class and decided by the sweep;
/// when two links share a hole, it is outside the class and left to the search.
#[test]
fn the_sweep_agrees_on_disjoint_and_overlapping_hole_spines() {
    let t = {
        let mut tally = Tally::default();
        let mut id = 0;
        for m in 2..=3usize {
            let mut seqs: Vec<Vec<u16>> = vec![vec![]];
            for _ in 0..m {
                seqs = (seqs.iter())
                    .flat_map(|s| HOLES.iter().map(move |&h| [&s[..], &[h]].concat()))
                    .collect();
            }
            for ns in 1..=m + 1 {
                for hs in &seqs {
                    let l = D {
                        nil: true,
                        rows: vec![(INT, 0)],
                    };
                    let mut ys = vec![l];
                    ys.extend(hs.iter().enumerate().map(|(i, &h)| D {
                        nil: false,
                        rows: vec![(h, i + 2)],
                    }));
                    ys.push(D {
                        nil: false,
                        rows: vec![(ONE, 0)],
                    });
                    ys.extend((1..=m + 1).map(|j| D {
                        nil: true,
                        rows: vec![(
                            if j < ns { INT } else { INT & !ONE },
                            if j == m + 1 { 0 } else { m + 2 + j },
                        )],
                    }));
                    let spec = Spec { groups: vec![ys] };
                    let mut neg: Vec<(usize, usize)> = (1..=m).map(|i| (0, i)).collect();
                    neg.push((0, m + 2));
                    let term = Term {
                        pos: vec![(0, 0)],
                        neg,
                    };
                    id += 1;
                    let what = format!("hole_spine m {m} ns {ns} heads {hs:?}");
                    both_orders(&mut tally, &spec, &term, &format!("_xhs{id}"), &what);
                }
            }
        }
        tally
    };
    eprintln!("hole spines: {t:?}");
}

/// R6: acyclic carrier-plus-chains, with stops, mixed positives and multi-value holes.
/// The DFA oracle reads masks only; no emptiness or membership query contributes to it.
#[test]
fn r6_random_carrier_chains_against_masks() {
    let tally = {
        let mut tally = Tally::default();
        let (mut rng, _) = Rng::fresh("R6 carrier chains");
        let palette = [
            INT,
            ONE,
            TWO,
            ONE | TWO,
            HOLES[0],
            HOLES[1],
            HOLES[0] & HOLES[1],
            INT & !(ONE | TWO),
            ONE | (1 << 8),
            INT & !ONE,
            INT & !TWO,
        ];
        for id in 0..300 {
            let n = 3 + rng.below(9);
            let mut ds = vec![D {
                nil: true,
                rows: vec![(INT, 0)],
            }];
            for i in 1..=n {
                ds.push(D {
                    nil: rng.below(4) == 0,
                    rows: vec![(palette[rng.below(palette.len())], rng.below(i))],
                });
            }
            let p = 1 + rng.below(n);
            let mut pos = vec![(0, p)];
            if rng.below(2) == 0 {
                pos.push((0, 0));
            }
            if rng.below(3) == 0 {
                pos.push((0, 1 + rng.below(n)));
            }
            let neg = (1..=n)
                .filter(|&i| i != p && rng.below(3) != 0)
                .map(|i| (0, i))
                .collect();
            let term = Term { pos, neg };
            let spec = Spec { groups: vec![ds] };
            both_orders(
                &mut tally,
                &spec,
                &term,
                &format!("_r6c{id}"),
                &format!("R6 chain masks {id}"),
            );
        }
        tally
    };
    eprintln!("R6 carrier chains: {tally:?}");
    // The sweep decides a case on every run, built (PROOF-test-count-thresholds): links
    // `D1 = cons(int, L)`, `D2 = cons(1, L)`, `D3 = cons(2, L)` with tails earlier than
    // themselves, as drawn above; `D1` less `D2` and `D3` holds `[0]` and is inhabited, and the
    // sweep decides it in both orders (measured, as for the positive chains).
    let b = built(&[(INT, 0), (ONE, 0), (TWO, 0)], &[1], &[2, 3], "r6");
    assert_eq!((b.swept, b.inhabited), (2, 2), "the built case: {b:?}");
}

/// Two escaping predicates per root do not imply 2-SAT when holes overlap.
/// Selector positions choose a literal of each 3-clause. Each implication
/// selector=j => literal_j holds has just two escaping predicates. `count` random formulas are
/// checked, drawn from a generator made with [`Rng::fresh`] (author P169); the 384 formulas of
/// one fixed seed were checked, in four pieces of 4 to 5 s, until TEST-bench-move-l0123.
pub(super) fn r6_two_predicate_reduction_matches_boolean_bruteforce(count: usize) {
    {
        let (mut rng, _) = Rng::fresh("R6 two-predicate selector reduction");
        for id in 0..count {
            let k = 1 + rng.below(4);
            let m = 1 + rng.below(4);
            let clauses: Vec<Vec<(usize, bool)>> = (0..m)
                .map(|_| (0..3).map(|_| (rng.below(k), rng.below(2) == 0)).collect())
                .collect();
            let sat = (0..1usize << k).any(|a| {
                clauses
                    .iter()
                    .all(|cl| cl.iter().any(|&(i, b)| ((a >> i) & 1 != 0) == b))
            });
            let (spec, term) = selector_reduction(k, &clauses);
            assert_eq!(
                spec.inhabited(&term),
                sat,
                "selector reduction {id}: {clauses:?}"
            );
            let mut tally = Tally::default();
            both_orders(
                &mut tally,
                &spec,
                &term,
                &format!("_r6sat{id}"),
                "two-predicate reduction",
            );
        }
        eprintln!(
            "R6 two-predicate selector reduction: {} formulas checked",
            count
        );
    };
}

/// The selector reduction of [`r6_two_predicate_reduction_matches_boolean_bruteforce`] for `k`
/// variables and the 3-clauses `clauses` (variable, sign): the term is inhabited iff the
/// formula is satisfiable.
fn selector_reduction(k: usize, clauses: &[Vec<(usize, bool)>]) -> (Spec, Term) {
    let domain = ONE | TWO | (1 << 8); // values 1,2,3
    let mut ds = vec![D {
        nil: true,
        rows: vec![(INT, 0)],
    }];
    let len = k + clauses.len();
    let mut positive = 0;
    for j in (0..len).rev() {
        ds.push(D {
            nil: false,
            rows: vec![(if j < k { ONE | TWO } else { domain }, positive)],
        });
        positive = ds.len() - 1;
    }
    let mut neg = Vec::new();
    for (c, cl) in clauses.iter().enumerate() {
        for (j, &(i, b)) in cl.iter().enumerate() {
            let mut root = 0;
            for s in (0..len).rev() {
                // Escape root iff selector != j OR the chosen literal is true.
                let hole = if s == k + c {
                    domain & ![ONE, TWO, 1 << 8][j]
                } else if s == i {
                    if b { TWO } else { ONE }
                } else {
                    0
                };
                ds.push(D {
                    nil: false,
                    rows: vec![(INT & !hole, root)],
                });
                root = ds.len() - 1;
            }
            neg.push((0, root));
        }
    }
    let spec = Spec { groups: vec![ds] };
    let term = Term {
        pos: vec![(0, positive)],
        neg,
    };
    (spec, term)
}

/// One case of [`the_u6_fork_cases_are_answered_or_refused_soundly`]: checked against the
/// oracle in both orders by [`both_orders`], then the verdicts, each asked afresh, of the build
/// as given (tag `tag`) and of the reversed build (tag `{tag}r`), and the oracle's answer.
fn u6_case(spec: &Spec, term: &Term, tag: &str) -> (bool, Verdict, Verdict) {
    let mut tally = Tally::default();
    both_orders(&mut tally, spec, term, tag, tag);
    let a = spec.ty(&spec.build(tag), term);
    let (rspec, rterm) = spec.reversed(term);
    let b = rspec.ty(&rspec.build_in(&format!("{tag}r"), true), &rterm);
    Type::forget_emptiness();
    let va = a.verdict();
    Type::forget_emptiness();
    let vb = b.verdict();
    Type::forget_emptiness();
    (spec.inhabited(term), va, vb)
}

/// The 22 cases of REFUSAL-front-post-r11-forks (zed-impl docs/handoff/REFUSAL-front-unsolved.md,
/// U6): answers kernel 19bc4e25 gave that a later kernel refused at a fork. U6 names one build
/// of each (the reversed one for a tag ending in `r`, the one as given otherwise); here both
/// builds of each of the 17 specs are pinned at their verdict now, which is the same in both
/// orders, and checked against the oracle. Four of the 22 are answered: `_xc1930` Inhabited,
/// and `_xc2359`, `_xp1550` and `_xp1550r` Empty, by the value search at the K26 fork in
/// `tuples_on` (a value of one tuple type of a plain union proves it inhabited). A fifth,
/// `_xc284r`, is Empty by the fork stages (PORT-u6-structured-fork, COMPLEXITY.md K137), as the
/// oracle says, and so is the other build, `_xc284`. `_r7rc_343f` and `_r7rc_343r`, in
/// [`r7_random_carrier_plus_chains_both_orders_against_bruteforce`], are Inhabited by the fork
/// stages, as the brute force there says. The other 15 are still refused, and never wrong: the
/// twelve `_r6sat` are the selector reduction of 3-SAT, and the rest need the subset
/// construction (row REFUSAL-front-u6-subset). The
/// control: two cases of the same builds that every kernel answers, one inhabited and one
/// empty.
#[test]
fn the_u6_fork_cases_are_answered_or_refused_soundly() {
    use Verdict::{Empty, Inhabited};
    let fork = Verdict::Refused(Refusal::Fork);
    let d = |nil: bool, rows: &[(u16, usize)]| D {
        nil,
        rows: rows.to_vec(),
    };
    let term = |pos: &[usize], neg: &[usize]| Term {
        pos: pos.iter().map(|&i| (0, i)).collect(),
        neg: neg.iter().map(|&i| (0, i)).collect(),
    };
    // (tag, spec, term, the oracle's answer, the verdict in both orders).
    let mut cases: Vec<(String, Spec, Term, bool, Verdict)> = Vec::new();
    let xc284r = Spec {
        groups: vec![vec![
            d(false, &[(1287, 2)]),
            d(true, &[(775, 0), (4, 2)]),
            d(true, &[(6, 4)]),
            d(true, &[(1799, 3), (4, 3)]),
            d(true, &[(512, 1)]),
            d(true, &[(1799, 5)]),
        ]],
    };
    let (s, t) = xc284r.reversed(&term(&[5], &[0, 2, 3, 4]));
    cases.push(("_xc284".into(), s, t, false, Empty));
    let xc363r = Spec {
        groups: vec![vec![
            d(false, &[(6, 0)]),
            d(false, &[(775, 4)]),
            d(false, &[(1797, 2), (1287, 3)]),
            d(false, &[(775, 4), (1799, 0)]),
            d(true, &[(2, 4)]),
            d(false, &[(2, 2), (1541, 3)]),
            d(true, &[(1799, 6)]),
        ]],
    };
    let (s, t) = xc363r.reversed(&term(&[6], &[0, 1, 2, 3, 4, 5]));
    cases.push(("_xc363".into(), s, t, true, fork));
    let xc1930 = || Spec {
        groups: vec![vec![
            d(true, &[(1799, 0)]),
            d(false, &[(1287, 1)]),
            d(true, &[(6, 5), (1541, 3)]),
            d(true, &[(1287, 3), (775, 0)]),
            d(true, &[(775, 5), (1543, 1)]),
            d(false, &[(512, 4), (1541, 3)]),
        ]],
    };
    cases.push((
        "_xc1930".into(),
        xc1930(),
        term(&[0], &[2, 4, 5]),
        true,
        Inhabited,
    ));
    let xc2359 = || Spec {
        groups: vec![vec![
            d(true, &[(1799, 0)]),
            d(true, &[(1799, 4)]),
            d(false, &[(1797, 0)]),
            d(false, &[(6, 1)]),
            d(false, &[(1287, 1), (1797, 0)]),
            d(true, &[(4, 3)]),
        ]],
    };
    cases.push((
        "_xc2359".into(),
        xc2359(),
        term(&[0], &[1, 2, 3, 5]),
        false,
        Empty,
    ));
    let xp43 = || Spec {
        groups: vec![vec![
            d(true, &[(1799, 0)]),
            d(false, &[(128, 0)]),
            d(false, &[(1287, 6)]),
            d(false, &[(128, 4)]),
            d(false, &[(1543, 6), (1927, 6)]),
            d(false, &[(1543, 6)]),
            d(false, &[(1287, 0), (1543, 0)]),
            d(true, &[(1927, 7)]),
        ]],
    };
    let t = term(&[4, 0, 7], &[3, 5, 6]);
    cases.push(("_xp43".into(), xp43(), t, false, fork));
    let xp1550 = || Spec {
        groups: vec![vec![
            d(true, &[(1799, 0)]),
            d(false, &[(1797, 5)]),
            d(false, &[(1543, 6)]),
            d(false, &[(128, 4), (1287, 5)]),
            d(false, &[(1287, 7), (1543, 5)]),
            d(false, &[(1287, 7)]),
            d(false, &[(128, 7)]),
            d(true, &[(2, 0)]),
            d(true, &[(1543, 8)]),
        ]],
    };
    let t = term(&[3, 8], &[1, 4, 5, 7]);
    cases.push(("_xp1550".into(), xp1550(), t, false, Empty));
    // The `_r6sat` cases: (id, k, clauses); all satisfiable. U6 names the reversed build of 6,
    // 19 and 133, both builds of 18 and 158, and the one as given of the rest.
    type Clause = [(usize, bool); 3];
    let r6: [(usize, usize, &[Clause]); 10] = [
        (
            6,
            4,
            &[
                [(1, true), (1, false), (1, false)],
                [(0, false), (3, true), (2, true)],
                [(3, true), (0, true), (3, false)],
                [(3, true), (3, true), (3, false)],
            ],
        ),
        (
            18,
            2,
            &[
                [(1, true), (1, false), (1, true)],
                [(1, true), (1, true), (1, false)],
                [(1, false), (0, true), (1, true)],
            ],
        ),
        (
            19,
            4,
            &[
                [(2, true), (1, true), (3, true)],
                [(1, true), (2, false), (2, false)],
                [(1, false), (0, true), (1, true)],
            ],
        ),
        (
            48,
            2,
            &[
                [(0, false), (0, false), (0, true)],
                [(0, true), (0, false), (0, false)],
                [(0, true), (1, false), (0, false)],
            ],
        ),
        (
            56,
            2,
            &[
                [(0, true), (1, true), (1, true)],
                [(0, false), (0, false), (1, false)],
                [(0, true), (0, false), (1, false)],
            ],
        ),
        (
            90,
            2,
            &[
                [(0, true), (1, false), (1, true)],
                [(1, true), (0, true), (0, false)],
                [(1, true), (1, true), (0, true)],
                [(0, true), (0, false), (0, false)],
            ],
        ),
        (
            124,
            3,
            &[
                [(0, false), (2, false), (1, false)],
                [(2, true), (2, false), (1, true)],
                [(1, true), (0, true), (1, true)],
            ],
        ),
        (
            133,
            4,
            &[
                [(1, false), (1, true), (1, false)],
                [(0, false), (3, false), (0, true)],
                [(3, true), (1, true), (0, false)],
            ],
        ),
        (
            147,
            3,
            &[
                [(2, true), (1, false), (1, true)],
                [(0, true), (2, true), (2, true)],
                [(2, true), (1, false), (2, true)],
                [(0, false), (2, true), (2, false)],
            ],
        ),
        (
            158,
            2,
            &[
                [(1, true), (0, true), (0, true)],
                [(1, true), (1, false), (0, true)],
                [(1, false), (1, false), (1, true)],
                [(0, true), (0, true), (1, false)],
            ],
        ),
    ];
    for &(id, k, clauses) in &r6 {
        let clauses: Vec<Vec<(usize, bool)>> = clauses.iter().map(|c| c.to_vec()).collect();
        let (s, t) = selector_reduction(k, &clauses);
        cases.push((format!("_r6sat{id}"), s, t, true, fork));
    }
    // Every case is run before any pin is checked, so a failure names all the changed pins.
    let mut changed = Vec::new();
    for (tag, spec, term, inhabited, want) in &cases {
        let (oracle, va, vb) = u6_case(spec, term, tag);
        assert_eq!(oracle, *inhabited, "{tag}: the oracle");
        if (va, vb) != (*want, *want) {
            changed.push(format!("{tag}: {va:?} and {vb:?}, pinned {want:?}"));
        }
    }
    assert!(
        changed.is_empty(),
        "the verdicts in both orders: {changed:#?}"
    );
    // The control: `_xc1930` less nothing holds `nil`; `_xc2359` less its own positive side is
    // empty. Both are answered in both orders.
    for (tag, spec, term, want) in [
        ("_u6c1", xc1930(), term(&[0], &[]), Inhabited),
        ("_u6c2", xc2359(), term(&[0], &[0, 1]), Empty),
    ] {
        let (oracle, va, vb) = u6_case(&spec, &term, tag);
        assert_eq!(oracle, want == Inhabited, "{tag}: the oracle");
        assert_eq!((va, vb), (want, want), "{tag}: the verdicts");
    }
}

/// Cases from the cross-review of REFUSAL-front-u6-subset (round 1, 2026-11-19). Each is checked
/// against the oracle in both orders ([`u6_case`]) and pinned at its verdict now, the same in
/// both orders:
///
/// - `_u6a167`: lists of integers less `#nil`, the lists that end in 1 and the lists that end in
///   another integer. Empty, since every list is one of the three; refused at the fork now. At
///   every element both ending types stay open, so the opus seat's rule (follow the fork when
///   the union taken out is deterministic after one element) refuses it too.
/// - `_u6gad`: the selector reduction of (v | a | b), (v | !a | !b), (!v | a | !b),
///   (!v | !a | b). Satisfiable (all true); refused at the fork now. The sol seat proved that its
///   prefix-box projection leaves all four clauses: each variable has both signs, so no pure
///   literal is eliminated. This gadget is how 3-SAT stays inside what that rule refuses.
/// - `_u6gadu`: the same with (v | v | v) and (!v | !v | !v). Not satisfiable; answered Empty.
#[test]
fn the_u6_review_cases_are_answered_or_refused_soundly() {
    let d = |nil: bool, rows: &[(u16, usize)]| D {
        nil,
        rows: rows.to_vec(),
    };
    let a167 = Spec {
        groups: vec![vec![
            d(true, &[(INT, 0)]),
            d(true, &[]),
            d(false, &[(ONE, 1), (INT, 2)]),
            d(false, &[(INT & !ONE, 1), (INT, 3)]),
        ]],
    };
    let a167_term = Term {
        pos: vec![(0, 0)],
        neg: vec![(0, 1), (0, 2), (0, 3)],
    };
    let gadget = vec![
        vec![(0, true), (1, true), (2, true)],
        vec![(0, true), (1, false), (2, false)],
        vec![(0, false), (1, true), (2, false)],
        vec![(0, false), (1, false), (2, true)],
    ];
    let mut forced = gadget.clone();
    forced.push(vec![(0, true); 3]);
    forced.push(vec![(0, false); 3]);
    let (gs, gt) = selector_reduction(3, &gadget);
    let (fs, ft) = selector_reduction(3, &forced);
    let fork = Verdict::Refused(Refusal::Fork);
    for (tag, spec, term, inhabited, want) in [
        ("_u6a167", &a167, &a167_term, false, fork),
        ("_u6gad", &gs, &gt, true, fork),
        ("_u6gadu", &fs, &ft, false, Verdict::Empty),
    ] {
        let (oracle, va, vb) = u6_case(spec, term, tag);
        assert_eq!(oracle, inhabited, "{tag}: the oracle");
        assert_eq!((va, vb), (want, want), "{tag}: the verdicts in both orders");
    }
}

/// The verdicts of `term` in both orders (the build as given, tag `tag`, and the reversed one,
/// tag `{tag}r`), each asked afresh, checked against `inhabited`: each is that answer or refused
/// at a fork. An `Inhabited` verdict is checked on the value [`Type::witness`] gives, an answer
/// against [`Type::is_empty`]. Unlike [`u6_case`] it does not run the oracle, so a case whose
/// oracle is too costly (a selector reduction with many clauses) passes the formula's answer.
fn fork_case(spec: &Spec, term: &Term, tag: &str, inhabited: bool) -> (Verdict, Verdict) {
    let a = spec.ty(&spec.build(tag), term);
    let (rspec, rterm) = spec.reversed(term);
    let b = rspec.ty(&rspec.build_in(&format!("{tag}r"), true), &rterm);
    let want = if inhabited {
        Verdict::Inhabited
    } else {
        Verdict::Empty
    };
    let mut out = Vec::new();
    for (t, order) in [(a, "as given"), (b, "reversed")] {
        Type::forget_emptiness();
        let v = t.verdict();
        assert!(
            v == want || v == Verdict::Refused(Refusal::Fork),
            "{tag} ({order}): {v:?}, the answer is {want:?}"
        );
        if v == Verdict::Inhabited {
            let w = t
                .witness()
                .unwrap_or_else(|| panic!("{tag} ({order}): no value"));
            assert!(t.contains(&w), "{tag} ({order}): {w} is not in {t}");
        }
        Type::forget_emptiness();
        if v == Verdict::Empty {
            assert!(
                t.is_empty(),
                "{tag} ({order}): Empty, but is_empty is false"
            );
        }
        Type::forget_emptiness();
        out.push(v);
    }
    (out[0], out[1])
}

/// Whether the 3-clauses `clauses` over `k` variables are satisfiable, by trying every
/// assignment: the answer of [`selector_reduction`]`(k, clauses)`.
fn satisfiable(k: usize, clauses: &[Vec<(usize, bool)>]) -> bool {
    (0..1u32 << k).any(|a| (clauses.iter()).all(|c| c.iter().any(|&(i, b)| (a >> i & 1 == 1) == b)))
}

/// `m` random 3-clauses over `k` variables, by the prototype's xorshift.
fn random_clauses(seed: &mut u64, k: usize, m: usize) -> Vec<Vec<(usize, bool)>> {
    let mut next = || {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    };
    (0..m)
        .map(|_| {
            (0..3)
                .map(|_| ((next() % k as u64) as usize, next() % 2 == 0))
                .collect()
        })
        .collect()
}

/// The tests t04 to t11 of the gemini seat's prototype of the fork stages (round 1 of
/// REFUSAL-front-u6-subset, `structured_fork.rs`), ported with Stages 1 and 2
/// (PORT-u6-structured-fork, COMPLEXITY.md K137); its t01 and t02 are the U6 cases above and
/// `_u6a167`, and t03 is `refusals::the_forked_difference_benches_at_16_and_their_controls`.
/// Each case is checked by [`fork_case`] in both orders against the oracle (or, for t11, the
/// formula), and pinned at its verdict now. The prototype answers t04 and t05 by its Stage 3
/// (the prefix-chain CSP), which is not ported: t04 stays refused, as do the cases the
/// prototype refuses (t06 to t09, t11), since the first element read already leaves two
/// negative chains (a fork, for Stage 1) and the answer needs two negative states at once (no
/// simulation, for Stage 2). t05, unsatisfiable, is Empty and t10 Inhabited, both by the
/// kernel before the fork stages (the same with the stages switched off): the fork stages
/// decide none of t04 to t11.
#[test]
fn the_prototype_fork_stage_cases_are_answered_or_refused_soundly() {
    use Verdict::Inhabited;
    let fork = Verdict::Refused(Refusal::Fork);
    let d = |nil: bool, rows: &[(u16, usize)]| D {
        nil,
        rows: rows.to_vec(),
    };
    let mut cases: Vec<(String, Spec, Term, bool, Verdict)> = Vec::new();
    // t04 and t05: 2-SAT as the selector reduction of 3-clauses, an implication chain
    // x0 -> x1 -> x2 -> x3 with a tautology beside each link; with x0 and !x3 forced, unsatisfiable.
    for unsat in [true, false] {
        let k = 4;
        let mut clauses = Vec::new();
        for i in 0..k - 1 {
            clauses.push(vec![(i, false), (i + 1, true), (i + 1, true)]);
            clauses.push(vec![(i, true), (i, false), (i + 1, true)]);
        }
        if unsat {
            clauses.push(vec![(0, true); 3]);
            clauses.push(vec![(k - 1, false); 3]);
        }
        let (s, t) = selector_reduction(k, &clauses);
        let want = if unsat { Verdict::Empty } else { fork };
        cases.push((format!("_pf2sat{}", u8::from(unsat)), s, t, !unsat, want));
    }
    // t06 and t07: coupled 3-SAT, (x0 | x1 | x2) & (!x0 | !x1 | !x2), satisfiable, and all eight
    // clauses over three variables, not.
    let signs = |m: usize| (0..3).map(|i| (i, m >> i & 1 == 1)).collect::<Vec<_>>();
    for (tag, clauses) in [
        ("_pf3sat", vec![signs(7), signs(0)]),
        ("_pf3unsat", (0..8).map(signs).collect()),
    ] {
        let (s, t) = selector_reduction(3, &clauses);
        cases.push((tag.into(), s, t, satisfiable(3, &clauses), fork));
    }
    // t08: the lists over {other, 1} by the place of a 1 from the end, `n` 4, every place
    // taken out (Empty) and place 3 left (inhabited). 0 is R0, 1 to 4 R1 to R4, 5 to 8 G1 to G4,
    // 9 to 13 A0 to A4, 14 H, 15 the lists with no 1.
    let both = 1 | ONE;
    for skip in [None, Some(3)] {
        let n = 4;
        let mut ds = vec![d(true, &[])];
        ds.extend((1..=n).map(|k| d(false, &[(both, k - 1)])));
        ds.extend((1..=n).map(|i| d(false, &[(both, n + i), (ONE, i - 1)])));
        let a0 = ds.len();
        ds.push(d(true, &[(both, a0)]));
        ds.extend((1..=n).map(|k| d(false, &[(both, a0 + k - 1)])));
        let h = ds.len();
        ds.push(d(false, &[(both, h), (ONE, a0 + n)]));
        ds.push(d(true, &[(1, h + 1)]));
        let mut neg = vec![(0, h), (0, h + 1)];
        neg.extend((1..=n).filter(|&i| Some(i) != skip).map(|i| (0, n + i)));
        let term = Term {
            pos: vec![(0, a0)],
            neg,
        };
        let tag = format!("_pfend{}", skip.unwrap_or(0));
        cases.push((tag, Spec { groups: vec![ds] }, term, skip.is_some(), fork));
    }
    // t09: the lists over {other, 1} less those with an even number of 1s and those with an odd
    // number: Empty, and the two negative automata read every list together.
    let parity = Spec {
        groups: vec![vec![
            d(true, &[(both, 0)]),
            d(true, &[(1, 1), (ONE, 2)]),
            d(false, &[(1, 2), (ONE, 1)]),
            d(false, &[(1, 3), (ONE, 4)]),
            d(true, &[(1, 4), (ONE, 3)]),
        ]],
    };
    let parity_term = Term {
        pos: vec![(0, 0)],
        neg: vec![(0, 1), (0, 3)],
    };
    cases.push(("_pfparity".into(), parity, parity_term, false, fork));
    // t10: the nonempty lists over {other, 1} less `[other]` and `[1]`: every list of length 1 is
    // taken out, so a value is longer, `[other, other]`; an Empty read off the first element alone
    // would be wrong.
    let longer = Spec {
        groups: vec![vec![
            d(true, &[(both, 0)]),
            d(false, &[(both, 0)]),
            d(true, &[]),
            d(false, &[(1, 2)]),
            d(false, &[(ONE, 2)]),
        ]],
    };
    let longer_term = Term {
        pos: vec![(0, 1)],
        neg: vec![(0, 3), (0, 4)],
    };
    cases.push(("_pflonger".into(), longer, longer_term, true, Inhabited));
    // Every case is run before any pin is checked, so a failure names all the changed pins.
    let mut changed = Vec::new();
    for (tag, spec, term, inhabited, want) in &cases {
        let (oracle, va, vb) = u6_case(spec, term, tag);
        assert_eq!(oracle, *inhabited, "{tag}: the oracle");
        let (fa, fb) = fork_case(spec, term, &format!("{tag}f"), *inhabited);
        assert_eq!((fa, fb), (va, vb), "{tag}: the verdicts asked twice");
        if (va, vb) != (*want, *want) {
            changed.push(format!("{tag}: {va:?} and {vb:?}, pinned {want:?}"));
        }
    }
    assert!(
        changed.is_empty(),
        "the verdicts in both orders: {changed:#?}"
    );
    // t11: 17 random 3-clauses over 4 variables, satisfiable; the oracle's subset construction
    // would read over a million sets, so the formula gives the answer.
    let clauses = random_clauses(&mut 0x9e37_79b9_7f4a_7c15, 4, 17);
    let sat = satisfiable(4, &clauses);
    assert!(sat, "t11: the prototype's formula is satisfiable");
    let (s, t) = selector_reduction(4, &clauses);
    assert_eq!(fork_case(&s, &t, "_pfr3sat", sat), (fork, fork), "t11");
}

/// R6-C2: avoiding the leaf head at an optional spine arrival is a
/// commitment. Another negative chain can distinguish that choice.
#[test]
fn r6_optional_spine_arrival_must_not_force_a_later_empty() {
    {
        // 0 L; 1 F1; 2 F2; 3 F3; 4 A4; 5 A3; 6 A2; 7 A1;
        // 8 P4; 9 P3; 10 P2; 11 P1.
        let ds = vec![
            D {
                nil: true,
                rows: vec![(INT, 0)],
            },
            D {
                nil: false,
                rows: vec![(ONE, 0)],
            },
            D {
                nil: false,
                rows: vec![(INT & !TWO, 1)],
            },
            D {
                nil: false,
                rows: vec![(HOLES[0], 2)],
            },
            D {
                nil: false,
                rows: vec![(INT, 0)],
            },
            D {
                nil: false,
                rows: vec![(INT & !ONE, 4)],
            },
            D {
                nil: false,
                rows: vec![(INT, 5)],
            },
            D {
                nil: false,
                rows: vec![(INT, 6)],
            },
            D {
                nil: false,
                rows: vec![(ONE, 0)],
            },
            D {
                nil: false,
                rows: vec![(INT, 8)],
            },
            D {
                nil: false,
                rows: vec![(INT, 9)],
            },
            D {
                nil: false,
                rows: vec![(INT, 10)],
            },
        ];
        let spec = Spec { groups: vec![ds] };
        let term = Term {
            pos: vec![(0, 11)],
            neg: vec![(0, 3), (0, 7)],
        };
        assert!(spec.inhabited(&term)); // [3,0,1,1]
        let mut tally = Tally::default();
        both_orders(
            &mut tally,
            &spec,
            &term,
            "_r6optional",
            "optional spine arrival",
        );
    };
}

#[test]
fn r6_greedy_guard_admits_a_partially_compatible_unused_slot() {
    {
        let spec = Spec {
            groups: vec![vec![
                D {
                    nil: true,
                    rows: vec![(INT, 0)],
                },
                D {
                    nil: false,
                    rows: vec![(ONE, 0)],
                },
                D {
                    nil: false,
                    rows: vec![(INT & !TWO, 1)],
                },
                D {
                    nil: false,
                    rows: vec![(HOLES[0], 2)],
                },
                D {
                    nil: false,
                    rows: vec![(HOLES[1], 3)],
                },
                D {
                    nil: false,
                    rows: vec![(ONE, 0)],
                },
                D {
                    nil: false,
                    rows: vec![(ONE, 5)],
                },
                D {
                    nil: false,
                    rows: vec![(ONE | TWO, 6)],
                },
                D {
                    nil: false,
                    rows: vec![(INT, 7)],
                },
            ]],
        };
        let term = Term {
            pos: vec![(0, 8)],
            neg: vec![(0, 4)],
        };
        let ts = spec.build("_r6guard");
        let t = spec.ty(&ts, &term);
        assert_eq!(t.chain_verdict(), Some(Verdict::Inhabited));
        let mut tally = Tally::default();
        both_orders(
            &mut tally,
            &spec,
            &term,
            "_r6guardorder",
            "unused partial slot",
        );
    };
}

/// R7: random cases of the X31 kind, against the masks. A positive straight chain of length 3
/// to 6 with cofinite heads and three or four negative straight chains of length 2 up to the
/// positive's, over the carrier `L`, so that a negative chain often reaches `L` (a spine
/// arrival) at a depth where the positive can still follow it or leave it; now and then a node
/// is also `nil` or a chain shares a suffix with an earlier one. Checked in both orders through
/// the sweep, the prefix chains and the verdict ([`both_orders`]). Without the X31 guard
/// (`optional_spine_choice`) the prefix chains say Empty on case 1479, which is Inhabited.
#[test]
fn r7_random_optional_spine_choices_against_masks() {
    let tally = r7_optional_spine_choices(Rng::fresh("R7 optional spine choices").0);
    eprintln!("R7 optional spine choices: {tally:?}");
    // The sweep decides a case on every run, built (PROOF-test-count-thresholds): the positive
    // straight chain `D3 = cons(int, D2)`, `D2 = cons(int, D1)`, `D1 = cons(int, L)` and the
    // negative chain `D5 = cons(int, D4)`, `D4 = cons(int, L)`, which holds every list of at
    // least two integers and so every list of `D3`: the case is empty, and the sweep decides it
    // in both orders (measured, as for the positive chains).
    let b = built(
        &[(INT, 0), (INT, 1), (INT, 2), (INT, 0), (INT, 4)],
        &[3],
        &[5],
        "r7",
    );
    assert_eq!((b.swept, b.empty), (2, 2), "the built case: {b:?}");
}

/// The cases of [`r7_random_optional_spine_choices_against_masks`], drawn from `rng`.
fn r7_optional_spine_choices(mut rng: Rng) -> Tally {
    let mut tally = Tally::default();
    // Cofinite heads for the positive chain, so that it can follow a negative chain past
    // that chain's arrival at `L` or leave it; any head for the negatives.
    let cofinite = [
        INT,
        INT,
        INT,
        HOLES[0],
        HOLES[1],
        INT & !ONE,
        INT & !TWO,
        ONE,
    ];
    let any = [
        INT,
        INT,
        INT,
        INT,
        ONE,
        TWO,
        HOLES[0],
        HOLES[1],
        INT & !ONE,
        INT & !TWO,
    ];
    for id in 0..150 {
        let mut ds = vec![D {
            nil: true,
            rows: vec![(INT, 0)],
        }];
        let chain = |ds: &mut Vec<D>, rng: &mut Rng, len: usize, heads: &[u16]| {
            // The end: the carrier, or now and then an earlier chain's node (a shared
            // suffix).
            let mut at = if ds.len() > 1 && rng.below(8) == 0 {
                1 + rng.below(ds.len() - 1)
            } else {
                0
            };
            for _ in 0..len {
                ds.push(D {
                    nil: rng.below(16) == 0,
                    rows: vec![(heads[rng.below(heads.len())], at)],
                });
                at = ds.len() - 1;
            }
            at
        };
        let plen = 3 + rng.below(4);
        let p = chain(&mut ds, &mut rng, plen, &cofinite);
        let negs = 3 + rng.below(2);
        let neg = (0..negs)
            .map(|_| {
                let len = 2 + rng.below(plen - 1);
                (0, chain(&mut ds, &mut rng, len, &any))
            })
            .collect();
        let term = Term {
            pos: vec![(0, p)],
            neg,
        };
        let spec = Spec { groups: vec![ds] };
        both_orders(
            &mut tally,
            &spec,
            &term,
            &format!("_r7o{id}"),
            &format!("R7 optional spine choices {id}"),
        );
    }
    tally
}

/// The random tests above under fixed seeds whose cases reach code no fixed case reaches
/// (TEST-types-unreached-paths-2; found by recording which code each case runs, over seeds 1
/// to 400). The positive chains under seed 153 reach a list sweep whose `Inhabited` witness
/// `check_list_value` cannot rebuild a row for, so `list_sweep` declines and the search
/// decides; under seeds 153 and 339 the prefix-chain search's memo of the last miss is read
/// again, and under 339 an emitting node's head is evaluated on a memo miss. The R7 optional
/// spine choices under seed 11 reach a partial negative group whose remaining head is cut to
/// empty. The random links under seed 12 reach the order of two sets of nodes in which the
/// first side's subtree is the smaller. Each case is checked against its oracle as in the
/// random test; a change to a generator moves these cases, and the record in
/// `crates/zedc-types/COMPLETENESS.md` says how to find new seeds.
#[test]
fn the_random_tests_under_seeds_reaching_rare_paths_agree_with_their_oracles() {
    for seed in [153, 339] {
        eprintln!(
            "positive chains, seed {seed}: {:?}",
            random_positive_chains(Rng::new(seed))
        );
    }
    eprintln!(
        "R7 optional spine choices, seed 11: {:?}",
        r7_optional_spine_choices(Rng::new(11))
    );
    eprintln!("random links, seed 12: {:?}", random_links(Rng::new(12)));
}

/// R7: two roots on one spine. `R1` reaches the leaf `S1` at step 2 and `R2` at step 3;
/// avoiding `S1`'s head at step 2 (w2 != 1) takes away `R2`'s only usable hole (w2 = 1), and
/// the first head meets no hole, so `greedy_unsafe` stays false. The one value is [a, 1, 1].
/// Built to tell the X31 guard from Gemini R6's `can_prove_empty` (cleared only when a
/// negative chain is active at the arrival); it does not: `R2` is an active group at step 2,
/// so both decline Empty (R7, Q2).
#[test]
fn r7_optional_spine_arrival_with_no_active_negative() {
    {
        // 0 L; 1 S1; 2 S2; 3 R1; 4 R2; 5 P3; 6 P2; 7 P1.
        let ds = vec![
            D {
                nil: true,
                rows: vec![(INT, 0)],
            },
            D {
                nil: false,
                rows: vec![(ONE, 0)],
            },
            D {
                nil: false,
                rows: vec![(INT & !ONE, 1)],
            },
            D {
                nil: false,
                rows: vec![(HOLES[0], 1)],
            },
            D {
                nil: false,
                rows: vec![(HOLES[1], 2)],
            },
            D {
                nil: false,
                rows: vec![(ONE, 0)],
            },
            D {
                nil: false,
                rows: vec![(INT, 5)],
            },
            D {
                nil: false,
                rows: vec![(HOLES[1] & !ONE, 6)],
            },
        ];
        let spec = Spec { groups: vec![ds] };
        let term = Term {
            pos: vec![(0, 7)],
            neg: vec![(0, 3), (0, 4)],
        };
        assert!(spec.inhabited(&term)); // [a, 1, 1]
        let mut tally = Tally::default();
        both_orders(
            &mut tally,
            &spec,
            &term,
            "_r7noactive",
            "optional arrival, no active negative",
        );
    };
}

/// R7 Q2(a): when `active_neg` is empty at an optional spine arrival (`r0 != r0_without_h1`),
/// `can_prove_empty` remains `true` and soundly decides both Case A (`committed_count == 0`) and
/// Case B (`committed_count > 0`) inputs where an unconditional `optional_spine_choice` flag
/// declines.
#[test]
fn r7_can_prove_empty_admits_empty_active_neg_where_codex_flag_declines() {
    {
        // Case A separation: `(P1 & Q1) \ F2` where `F2 = cons(int \ {3}, cons(1, L))` has an
        // optional spine arrival at step 2 with `active_neg` empty, and step 3 has `R_3 = {1} & {2} = empty`.
        let spec_a = Spec {
            groups: vec![vec![
                D {
                    nil: true,
                    rows: vec![(INT, 0)],
                }, // 0: L
                D {
                    nil: false,
                    rows: vec![(ONE, 0)],
                }, // 1: F1
                D {
                    nil: false,
                    rows: vec![(HOLES[0], 1)],
                }, // 2: F2 (hole {3})
                D {
                    nil: false,
                    rows: vec![(ONE, 0)],
                }, // 3: P3
                D {
                    nil: false,
                    rows: vec![(ONE | TWO, 3)],
                }, // 4: P2
                D {
                    nil: false,
                    rows: vec![(ONE | (1 << 8), 4)],
                }, // 5: P1 ({1, 3})
                D {
                    nil: false,
                    rows: vec![(TWO, 0)],
                }, // 6: Q3
                D {
                    nil: false,
                    rows: vec![(ONE | TWO, 6)],
                }, // 7: Q2
                D {
                    nil: false,
                    rows: vec![(ONE | (1 << 8), 7)],
                }, // 8: Q1 ({1, 3})
            ]],
        };
        let term_a = Term {
            pos: vec![(0, 5), (0, 8)],
            neg: vec![(0, 2)],
        };
        assert!(!spec_a.inhabited(&term_a));
        let ts_a = spec_a.build("_r7cpea");
        let t_a = spec_a.ty(&ts_a, &term_a);
        assert_eq!(t_a.chain_verdict(), Some(Verdict::Empty));
        let mut tally = Tally::default();
        both_orders(
            &mut tally,
            &spec_a,
            &term_a,
            "_r7cpea_ord",
            "Case A empty active_neg",
        );

        // Case B separation: `P1 \ (F2 | F3 | F4)` where step 2 is an optional spine arrival with
        // `active_neg` empty, step 3 commits step 1 to `{4}`, and step 4 proves `Empty` by Pigeonhole.
        let spec_b = Spec {
            groups: vec![vec![
                D {
                    nil: true,
                    rows: vec![(INT, 0)],
                }, // 0: L
                D {
                    nil: false,
                    rows: vec![(ONE, 0)],
                }, // 1: F1
                D {
                    nil: false,
                    rows: vec![(HOLES[0], 1)],
                }, // 2: F2 (hole {3})
                D {
                    nil: false,
                    rows: vec![(HOLES[1], 2)],
                }, // 3: F3 (hole {4})
                D {
                    nil: false,
                    rows: vec![(HOLES[2], 3)],
                }, // 4: F4 (hole {5})
                D {
                    nil: false,
                    rows: vec![(ONE, 0)],
                }, // 5: P4
                D {
                    nil: false,
                    rows: vec![(ONE, 5)],
                }, // 6: P3
                D {
                    nil: false,
                    rows: vec![(ONE | TWO, 6)],
                }, // 7: P2
                D {
                    nil: false,
                    rows: vec![((1 << 8) | (1 << 9) | (1 << 10), 7)],
                }, // 8: P1 ({3, 4, 5})
            ]],
        };
        let term_b = Term {
            pos: vec![(0, 8)],
            neg: vec![(0, 2), (0, 3), (0, 4)],
        };
        assert!(!spec_b.inhabited(&term_b));
        let ts_b = spec_b.build("_r7cpeb");
        let t_b = spec_b.ty(&ts_b, &term_b);
        assert_eq!(t_b.chain_verdict(), Some(Verdict::Empty));
        both_orders(
            &mut tally,
            &spec_b,
            &term_b,
            "_r7cpeb_ord",
            "Case B empty active_neg",
        );
    };
}

/// R7 Q2(b) / Q7(iii) Bug A: a struct payload inside `#cons` (`#cons(k: 99)` via
/// `Universe::Struct`, so `q.structs == true`) must not be ignored by `find_prefix_chains` or
/// `escape::decide`. On `cb709f13` both ignored `q.structs` and returned a wrong `Empty`.
#[test]
fn r7_bug_a_non_tuple_payload_in_cons_is_not_empty() {
    {
        use zed_kernel::types::Universe;
        let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
        let ts = Group::new(vec![
            Def {
                name: "L_bug_a".into(),
                params: vec![],
                body: Expr::Union(vec![
                    Expr::Type(Type::atom("nil")),
                    Expr::Atom(
                        "cons".into(),
                        vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
                    ),
                ]),
            },
            Def {
                name: "F1_bug_a".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(2)), Expr::Ref(0, vec![])],
                ),
            },
            Def {
                name: "F2_bug_a".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&Type::int() - &lit(0)), Expr::Ref(1, vec![])],
                ),
            },
            Def {
                name: "F3_bug_a".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&Type::int() - &lit(1)), Expr::Ref(1, vec![])],
                ),
            },
            Def {
                name: "P2_bug_a".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(2)), Expr::Type(Type::atom("nil"))],
                ),
            },
            Def {
                name: "P1_bug_a".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&lit(0) | &lit(1)), Expr::Ref(4, vec![])],
                ),
            },
        ])
        .unwrap()
        .instance(vec![]);
        let cons_struct = Type::atom_with("cons", &Type::universe(Universe::Struct));
        let w = Value::atom_named("cons", vec![("k".into(), Value::Int(99))]).unwrap();

        // 1. Triggers wrong `Empty` in `find_prefix_chains` on `cb709f13`.
        let cons_pair = Type::atom_with("cons", &Type::tuple(vec![lit(0), Type::atom("nil")]));
        let neg = Type::atom_with("cons", &Type::tuple(vec![Type::int(), ts[0].clone()]));
        let t_chains = &(&cons_struct | &cons_pair) - &neg;
        assert!(t_chains.contains(&w), "#cons(k: 99) is in t_chains");
        Type::forget_emptiness();
        assert_eq!(t_chains.chain_verdict(), None);
        Type::forget_emptiness();
        assert_eq!(t_chains.verdict(), Verdict::Refused(Refusal::NoWitness));
        assert!(!t_chains.is_empty());

        // 2. Triggers wrong `Empty` in `escape::decide` on `cb709f13` (unsat 2-SAT tuple rows
        // `(x1 = 0 | x1 = 1)` at length 2, unioned with `#cons(struct)`).
        let t_esc = &(&cons_struct | &ts[5]) - &(&(&ts[1] | &ts[2]) | &ts[3]);
        assert!(t_esc.contains(&w), "#cons(k: 99) is in t_esc");
        Type::forget_emptiness();
        assert_eq!(t_esc.chain_verdict(), None);
        Type::forget_emptiness();
        assert_eq!(t_esc.verdict(), Verdict::Refused(Refusal::NoWitness));
        assert!(!t_esc.is_empty());
    };
}

/// R7 Q2(b) / Q7(iii) Bug B: a tail union with two bare atoms (`#nil_a | #nil_z | #cons(0, L)`)
/// must not have `#nil_a` overwritten by `list_step`. On `cb709f13` both `find_prefix_chains` and
/// `escape::decide` returned a wrong `Empty`, although `#cons((0, #nil_a))` is in `t`.
#[test]
fn r7_bug_b_multiple_bare_atoms_in_tail_union_is_not_empty() {
    {
        let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
        let ts = Group::new(vec![
            Def {
                name: "L_bug_b".into(),
                params: vec![],
                body: Expr::Union(vec![
                    Expr::Type(Type::atom("nil_z")),
                    Expr::Atom(
                        "cons".into(),
                        vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
                    ),
                ]),
            },
            Def {
                name: "S_bug_b".into(),
                params: vec![],
                body: Expr::Union(vec![
                    Expr::Type(Type::atom("nil_a")),
                    Expr::Type(Type::atom("nil_z")),
                    Expr::Atom(
                        "cons".into(),
                        vec![Expr::Type(lit(0)), Expr::Ref(0, vec![])],
                    ),
                ]),
            },
            Def {
                name: "P_bug_b".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&lit(0) | &lit(1)), Expr::Ref(1, vec![])],
                ),
            },
            Def {
                name: "N0_bug_b".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(0)), Expr::Ref(0, vec![])],
                ),
            },
            Def {
                name: "N1_bug_b".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(1)), Expr::Ref(0, vec![])],
                ),
            },
        ])
        .unwrap()
        .instance(vec![]);
        let t = &ts[2] - &(&ts[3] | &ts[4]);
        let w = Value::atom_with("cons", vec![Value::Int(0), Value::atom("nil_a")]);
        assert!(t.contains(&w), "cons(0, nil_a) is in t");
        Type::forget_emptiness();
        assert_eq!(t.chain_verdict(), None);
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
        assert!(!t.is_empty());
    };
}

/// R7 Q7(i): in Gemini R6, `step_exact[step]` was false when `non_disjoint_stop_heads` was
/// non-empty while `can_prove_empty` stayed true, omitting step 2 from `active_spine_steps` and
/// returning a wrong `Empty` on `[7, 3, 7, 1]`.
#[test]
fn r7_gemini_r6_non_disjoint_stop_clause_omission_is_inhabited() {
    {
        let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
        let ts = Group::new(vec![
            Def {
                name: "L_gr6".into(),
                params: vec![],
                body: Expr::Union(vec![
                    Expr::Type(Type::atom("nil")),
                    Expr::Atom(
                        "cons".into(),
                        vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
                    ),
                ]),
            },
            Def {
                name: "F1_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(1)), Expr::Ref(0, vec![])],
                ),
            },
            Def {
                name: "F2_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&Type::int() - &lit(2)), Expr::Ref(1, vec![])],
                ),
            },
            Def {
                name: "F3_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&Type::int() - &lit(3)), Expr::Ref(2, vec![])],
                ),
            },
            Def {
                name: "F4_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&Type::int() - &lit(9)), Expr::Ref(3, vec![])],
                ),
            },
            Def {
                name: "Z2_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(2)), Expr::Type(Type::atom("nil"))],
                ),
            },
            Def {
                name: "N1_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(Type::int()), Expr::Ref(5, vec![])],
                ),
            },
            Def {
                name: "Z3_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(3)), Expr::Type(Type::atom("nil"))],
                ),
            },
            Def {
                name: "N2_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(Type::int()), Expr::Ref(7, vec![])],
                ),
            },
            Def {
                name: "P4_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(1)), Expr::Type(Type::atom("nil"))],
                ),
            },
            Def {
                name: "P3_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(7)), Expr::Ref(9, vec![])],
                ),
            },
            Def {
                name: "P2_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(&lit(2) | &lit(3)), Expr::Ref(10, vec![])],
                ),
            },
            Def {
                name: "P1_gr6".into(),
                params: vec![],
                body: Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(lit(7)), Expr::Ref(11, vec![])],
                ),
            },
        ])
        .unwrap()
        .instance(vec![]);
        let t = &ts[12] - &(&(&ts[4] | &ts[6]) | &ts[8]);
        let w = [7, 3, 7, 1]
            .iter()
            .rev()
            .fold(Value::atom("nil"), |tl, &x| {
                Value::atom_with("cons", vec![Value::Int(x), tl])
            });
        assert!(t.contains(&w), "[7, 3, 7, 1] is in t");
        Type::forget_emptiness();
        assert_ne!(t.chain_verdict(), Some(Verdict::Empty));
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
    };
}

/// R7 Q5(a): random carrier-plus-chains test (mixed finite/cofinite positive heads, 1-value and
/// many-value holes, stops, roots of different lengths, and optional spine choices as in X31)
/// checked against a pure brute-force word enumerator (calling neither emptiness nor membership)
/// through `chain_verdict` alone and through `verdict` in both definition/operand and query orders.
#[test]
fn r7_random_carrier_plus_chains_both_orders_against_bruteforce() {
    #[derive(Clone, Copy, Debug)]
    struct Pred {
        cof: bool,
        mask: u8, // bits 0..4 represent literals 0..4; symbol 4 stands for all other integers
    }
    impl Pred {
        fn holds(self, sym: u8) -> bool {
            if sym >= 4 {
                self.cof
            } else {
                ((self.mask >> sym) & 1 != 0) != self.cof
            }
        }
        fn ty(self) -> Type {
            let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
            let s = (0..4u8)
                .filter(|&b| (self.mask >> b) & 1 != 0)
                .fold(Type::empty(), |u, b| &u | &lit(b as i64));
            if self.cof { &Type::int() - &s } else { s }
        }
    }
    #[derive(Clone, Copy, Debug)]
    enum TailRef {
        Car,
        End,
        Node(usize),
    }
    #[derive(Clone, Debug)]
    struct ChainCase {
        car_head: Pred,
        nodes: Vec<(bool, Pred, TailRef)>,
        pos: Vec<(Pred, TailRef)>,
        neg: Vec<(Pred, TailRef)>,
    }
    fn brute_force_inhabited(c: &ChainCase) -> Option<Vec<u8>> {
        let mut depth = vec![0usize; c.nodes.len()];
        for i in 0..c.nodes.len() {
            depth[i] = 1 + match c.nodes[i].2 {
                TailRef::Node(j) => depth[j],
                _ => 0,
            };
        }
        let max_len = depth.into_iter().max().unwrap_or(0) + 2;
        fn tail_holds(c: &ChainCase, t: TailRef, rest: &[u8]) -> bool {
            match rest.split_first() {
                None => match t {
                    TailRef::Car | TailRef::End => true,
                    TailRef::Node(i) => c.nodes[i].0,
                },
                Some((&x, xs)) => match t {
                    TailRef::End => false,
                    TailRef::Car => c.car_head.holds(x) && tail_holds(c, TailRef::Car, xs),
                    TailRef::Node(i) => c.nodes[i].1.holds(x) && tail_holds(c, c.nodes[i].2, xs),
                },
            }
        }
        fn row_holds(c: &ChainCase, row: (Pred, TailRef), word: &[u8]) -> bool {
            let Some((&x, xs)) = word.split_first() else {
                return false;
            };
            row.0.holds(x) && tail_holds(c, row.1, xs)
        }
        fn search_words(c: &ChainCase, cur: &mut Vec<u8>, target_len: usize) -> bool {
            if cur.len() == target_len {
                return c.pos.iter().all(|&r| row_holds(c, r, cur))
                    && !c.neg.iter().any(|&r| row_holds(c, r, cur));
            }
            for sym in 0..5u8 {
                cur.push(sym);
                if search_words(c, cur, target_len) {
                    return true;
                }
                cur.pop();
            }
            false
        }
        let mut buf = Vec::with_capacity(max_len);
        for len in 1..=max_len {
            buf.clear();
            if search_words(c, &mut buf, len) {
                return Some(buf);
            }
        }
        None
    }
    fn build_case(c: &ChainCase, tag: &str, rev: bool) -> Type {
        // Definitions: 0 is carrier L, 1..=nodes.len() are pool nodes, then pos rows, then neg rows.
        let n_nodes = c.nodes.len();
        let n_pos = c.pos.len();
        let total = 1 + n_nodes + n_pos + c.neg.len();
        let map_idx = |idx: usize| if rev { total - 1 - idx } else { idx };
        let tail_expr = |t: TailRef| match t {
            TailRef::Car => Expr::Ref(map_idx(0), vec![]),
            TailRef::End => Expr::Type(Type::atom("nil")),
            TailRef::Node(i) => Expr::Ref(map_idx(1 + i), vec![]),
        };
        let mut defs: Vec<(usize, Def)> = Vec::with_capacity(total);
        let mut car_alts = vec![
            Expr::Type(Type::atom("nil")),
            Expr::Atom(
                "cons".into(),
                vec![Expr::Type(c.car_head.ty()), Expr::Ref(map_idx(0), vec![])],
            ),
        ];
        if rev {
            car_alts.reverse();
        }
        defs.push((
            0,
            Def {
                name: format!("L{tag}"),
                params: vec![],
                body: Expr::Union(car_alts),
            },
        ));
        for (i, &(has_stop, h, nx)) in c.nodes.iter().enumerate() {
            let step = Expr::Atom("cons".into(), vec![Expr::Type(h.ty()), tail_expr(nx)]);
            let body = if has_stop {
                let mut alts = vec![Expr::Type(Type::atom("nil")), step];
                if rev {
                    alts.reverse();
                }
                Expr::Union(alts)
            } else {
                step
            };
            defs.push((
                1 + i,
                Def {
                    name: format!("V{i}{tag}"),
                    params: vec![],
                    body,
                },
            ));
        }
        for (i, &(h, nx)) in c.pos.iter().chain(&c.neg).enumerate() {
            defs.push((
                1 + n_nodes + i,
                Def {
                    name: format!("R{i}{tag}"),
                    params: vec![],
                    body: Expr::Atom("cons".into(), vec![Expr::Type(h.ty()), tail_expr(nx)]),
                },
            ));
        }
        if rev {
            defs.reverse();
        }
        let ts = Group::new(defs.into_iter().map(|(_, d)| d).collect())
            .unwrap()
            .instance(vec![]);
        let mut pos_idxs: Vec<usize> = (0..n_pos).map(|i| map_idx(1 + n_nodes + i)).collect();
        let mut neg_idxs: Vec<usize> = (0..c.neg.len())
            .map(|i| map_idx(1 + n_nodes + n_pos + i))
            .collect();
        if rev {
            pos_idxs.reverse();
            neg_idxs.reverse();
        }
        let p = pos_idxs[1..]
            .iter()
            .fold(ts[pos_idxs[0]].clone(), |acc, &idx| &acc & &ts[idx]);
        let n = neg_idxs
            .iter()
            .fold(Type::empty(), |acc, &idx| &acc | &ts[idx]);
        &p - &n
    }

    {
        let (mut rng, _) = Rng::fresh("R7 carrier plus chains");
        let draw_pred = |rng: &mut Rng| -> Pred {
            match rng.below(7) {
                0 => Pred { cof: true, mask: 0 }, // int
                1 | 2 => Pred {
                    cof: true,
                    mask: 1u8 << rng.below(4), // 1-value hole
                },
                3 | 4 => {
                    // many-value hole (2 or 3 excluded values)
                    let m = (1u8 << rng.below(4)) | (1u8 << rng.below(4)) | (1u8 << rng.below(4));
                    Pred { cof: true, mask: m }
                }
                _ => {
                    // non-empty finite set over {0, 1, 2, 3}
                    Pred {
                        cof: false,
                        mask: 1 + rng.below(15) as u8,
                    }
                }
            }
        };

        // Checks one case against the brute force in both orders; returns what `chain_verdict`
        // says.
        fn check_case(case: &ChainCase, id: &str) -> Option<Verdict> {
            let witness = brute_force_inhabited(case);
            let inhab = witness.is_some();
            let a = build_case(case, &format!("_r7rc_{id}f"), false);
            let b = build_case(case, &format!("_r7rc_{id}r"), true);

            Type::forget_emptiness();
            let ca = a.chain_verdict();
            Type::forget_emptiness();
            let cb = b.chain_verdict();
            assert_eq!(
                ca, cb,
                "case {id}: chain_verdict order mismatch on {case:?}"
            );
            if let Some(cv) = ca {
                match cv {
                    Verdict::Empty => {
                        assert!(
                            !inhab,
                            "case {id}: chain_verdict Empty but brute force found {witness:?} on {case:?}"
                        );
                    }
                    Verdict::Inhabited => {
                        assert!(
                            inhab,
                            "case {id}: chain_verdict Inhabited but brute force found none on {case:?}"
                        );
                    }
                    Verdict::Refused(_) => {}
                }
            }

            // Query order 1 (`a` then `b`) and query order 2 (`b` then `a`).
            Type::forget_emptiness();
            let va1 = a.verdict();
            let vb1 = b.verdict();
            Type::forget_emptiness();
            let vb2 = b.verdict();
            let va2 = a.verdict();
            assert_eq!(va1, va2, "case {id}: query order changed `a` verdict");
            assert_eq!(vb1, vb2, "case {id}: query order changed `b` verdict");
            for (lbl, v) in [("a", va1), ("b", vb2)] {
                match v {
                    Verdict::Empty => assert!(
                        !inhab,
                        "case {id} ({lbl}): verdict Empty but brute force found {witness:?} on {case:?}"
                    ),
                    Verdict::Inhabited => assert!(
                        inhab,
                        "case {id} ({lbl}): verdict Inhabited but brute force found none on {case:?}"
                    ),
                    Verdict::Refused(_) => {}
                }
                if let Some(cv) = ca {
                    assert_eq!(cv, v, "case {id} ({lbl}): chain_verdict != verdict");
                }
            }
            ca
        }
        // A case a merge-push run drew (2026-11-18, seed not kept): inhabited by [1, 0, 0, 1],
        // yet `escape::decide` answered Empty. The refused row through node 2 has atoms at
        // places 1 to 4 and was read to its third; unit narrowing by the rows through nodes 5
        // and 6 then cut it to one atom, read as exact. Dropping the row through node 0 or the
        // one through node 1 (not both) leaves a case that failed alike.
        {
            let p = |cof: bool, mask: u8| Pred { cof, mask };
            use TailRef::{Car, Node};
            let fixed = ChainCase {
                car_head: p(true, 0),
                nodes: vec![
                    (false, p(false, 1), Car),
                    (false, p(true, 2), Node(0)),
                    (false, p(true, 2), Node(1)),
                    (false, p(true, 4), Node(2)),
                    (false, p(true, 1), Car),
                    (false, p(true, 0), Node(4)),
                    (false, p(true, 1), Car),
                    (true, p(true, 0), Car),
                    (false, p(true, 4), Node(7)),
                    (false, p(true, 0), Node(8)),
                    (false, p(true, 0), Node(9)),
                ],
                pos: vec![(p(true, 0), Node(10))],
                neg: vec![
                    (p(true, 2), Node(0)),
                    (p(true, 2), Node(1)),
                    (p(true, 4), Node(2)),
                    (p(true, 0), Node(5)),
                    (p(true, 0), Node(6)),
                ],
            };
            check_case(&fixed, "fixed");
        }
        // Case 343 of a fixed seed, two of the 22 cases of REFUSAL-front-post-r11-forks (U6):
        // inhabited by [0, 1]; kernel 19bc4e25 answered it in both orders, and the search
        // refused it at a fork in both from REFUSAL-front-post-r11-forks until
        // PORT-u6-structured-fork: Inhabited since, in both, by Stage 1 of the fork stages
        // (COMPLEXITY.md K137), which reads a value past the fork.
        {
            let p = |cof: bool, mask: u8| Pred { cof, mask };
            use TailRef::{Car, Node};
            let case = ChainCase {
                car_head: p(true, 0),
                nodes: vec![
                    (false, p(false, 2), Car),
                    (false, p(true, 5), Node(0)),
                    (false, p(true, 1), Node(1)),
                    (false, p(true, 8), Node(2)),
                    (false, p(true, 2), Car),
                    (false, p(false, 7), Car),
                ],
                pos: vec![(p(true, 0), Node(5)), (p(true, 0), Car)],
                neg: vec![
                    (p(true, 5), Node(0)),
                    (p(true, 8), Node(2)),
                    (p(true, 12), Node(4)),
                ],
            };
            assert_eq!(brute_force_inhabited(&case), Some(vec![0, 1]));
            check_case(&case, "343");
            let verdicts: Vec<Verdict> = [false, true]
                .into_iter()
                .map(|rev| {
                    let t = build_case(
                        &case,
                        &format!("_r7rc_343{}", ["f", "r"][usize::from(rev)]),
                        rev,
                    );
                    Type::forget_emptiness();
                    t.verdict()
                })
                .collect();
            assert_eq!(
                verdicts,
                [Verdict::Inhabited, Verdict::Inhabited],
                "r7 case 343, as given and reversed"
            );
            Type::forget_emptiness();
        }
        let mut chain_decided = 0usize;
        let mut chain_empty = 0usize;
        let mut chain_inhab = 0usize;
        for id in 0..300 {
            let x31_mode = id % 2 == 1;
            let car_head = if x31_mode || rng.below(3) != 0 {
                Pred { cof: true, mask: 0 }
            } else {
                Pred {
                    cof: true,
                    mask: 1u8 << rng.below(4),
                }
            };
            let mut nodes: Vec<(bool, Pred, TailRef)> = Vec::new();
            let mut pos: Vec<(Pred, TailRef)> = Vec::new();
            let mut neg: Vec<(Pred, TailRef)> = Vec::new();

            if x31_mode {
                // Spine F1..Fd with 1-value or many-value holes disjoint from F1's finite leaf head,
                // roots of different lengths along the spine (including optional arrivals where F1 is
                // not itself refused), auxiliary negative chains with holes/stops, and mixed positive
                // chains (exercising X31 as well as Case A and Case B).
                let leaf_bit = rng.below(2);
                let leaf_mask = 1u8 << leaf_bit;
                let leaf_h = Pred {
                    cof: false,
                    mask: leaf_mask,
                };
                let draw_spine_hole = |rng: &mut Rng| -> Pred {
                    let mut m = 0u8;
                    let k = if rng.below(2) == 0 { 1 } else { 2 };
                    for _ in 0..k {
                        let b = (leaf_bit + 1 + rng.below(3)) % 4;
                        m |= 1u8 << b;
                    }
                    Pred { cof: true, mask: m }
                };
                let sp_len = 1 + rng.below(3); // 1..=3 internal spine nodes above F1
                nodes.push((false, leaf_h, TailRef::Car)); // 0: F1 (depth 1)
                for d in 1..=sp_len {
                    nodes.push((false, draw_spine_hole(&mut rng), TailRef::Node(d - 1)));
                }
                // Spine roots of different lengths (when d > 0 is the lowest chosen root, arriving at
                // F1 is an optional spine choice as in X31).
                for (d, &(_, h, nx)) in nodes.iter().enumerate().take(sp_len + 1) {
                    if (d > 0 && rng.below(2) == 0) || d == sp_len || rng.below(5) == 0 {
                        neg.push((h, nx));
                    }
                }
                // Auxiliary negative chain(s) with stops, `int`, `int \ leaf_h`, or general predicates.
                let n_aux = 1 + rng.below(2);
                for _ in 0..n_aux {
                    let alen = 2 + rng.below(3); // 2..=4
                    let mut cur = if rng.below(5) == 0 {
                        TailRef::End
                    } else {
                        TailRef::Car
                    };
                    let mut chain_links: Vec<(bool, Pred)> = Vec::with_capacity(alen);
                    for _ in 0..alen {
                        let h = match rng.below(6) {
                            0..=2 => Pred { cof: true, mask: 0 },
                            3 | 4 => Pred {
                                cof: true,
                                mask: leaf_mask,
                            },
                            _ => draw_pred(&mut rng),
                        };
                        chain_links.push((rng.below(6) == 0, h));
                    }
                    for &(st, h) in &chain_links[..alen - 1] {
                        let idx = nodes.len();
                        nodes.push((st, h, cur));
                        cur = TailRef::Node(idx);
                    }
                    neg.push((chain_links[alen - 1].1, cur));
                }
                // Positive chain(s) of length 2..=5 with mixed heads (`int`, `leaf_h`, finite/cofinite).
                let n_pos_chains = if rng.below(3) == 0 { 2 } else { 1 };
                for _ in 0..n_pos_chains {
                    let plen = 2 + rng.below(4);
                    let mut pcur = if rng.below(5) == 0 {
                        TailRef::End
                    } else {
                        TailRef::Car
                    };
                    for step_rem in 0..plen - 1 {
                        let idx = nodes.len();
                        let ph = if step_rem == 0 && rng.below(2) == 0 {
                            leaf_h
                        } else if rng.below(2) == 0 {
                            Pred { cof: true, mask: 0 }
                        } else {
                            draw_pred(&mut rng)
                        };
                        nodes.push((rng.below(6) == 0, ph, pcur));
                        pcur = TailRef::Node(idx);
                    }
                    let top_ph = if rng.below(2) == 0 {
                        Pred { cof: true, mask: 0 }
                    } else {
                        draw_pred(&mut rng)
                    };
                    pos.push((top_ph, pcur));
                }
                if rng.below(4) == 0 {
                    pos.push((car_head, TailRef::Car));
                }
            } else {
                let np = 1 + rng.below(4);
                for i in 0..np {
                    let nx = if i > 0 && rng.below(3) != 0 {
                        TailRef::Node(rng.below(i))
                    } else if rng.below(4) == 0 {
                        TailRef::End
                    } else {
                        TailRef::Car
                    };
                    nodes.push((rng.below(3) == 0, draw_pred(&mut rng), nx));
                }
                let draw_tail = |rng: &mut Rng, np: usize| match rng.below(5) {
                    0 => TailRef::Car,
                    1 => TailRef::End,
                    _ => TailRef::Node(rng.below(np)),
                };
                pos.push((draw_pred(&mut rng), draw_tail(&mut rng, np)));
                if rng.below(2) == 0 {
                    if rng.below(2) == 0 {
                        pos.push((car_head, TailRef::Car));
                    } else {
                        pos.push((draw_pred(&mut rng), draw_tail(&mut rng, np)));
                    }
                }
                let n_neg = 1 + rng.below(5);
                for _ in 0..n_neg {
                    neg.push((draw_pred(&mut rng), draw_tail(&mut rng, np)));
                }
            }

            let case = ChainCase {
                car_head,
                nodes,
                pos,
                neg,
            };
            let ca = check_case(&case, &id.to_string());
            chain_decided += usize::from(ca.is_some());
            chain_empty += usize::from(ca == Some(Verdict::Empty));
            chain_inhab += usize::from(ca == Some(Verdict::Inhabited));
        }
        eprintln!(
            "R7 random carrier+chains: 300 cases, chain_decided={chain_decided} (empty={chain_empty}, inhab={chain_inhab})"
        );
        // Both answers of `chain_verdict` on every run, from cases built to give them
        // (PROOF-test-count-thresholds), in place of counts of the draws. Over the carrier
        // `L = nil | cons(int, L)`, `cons(1, L)` less `cons(int, L)` is empty, as every list
        // whose head is 1 and whose tail is in `L` is a list whose head is an integer and whose
        // tail is in `L`; and `cons(int, L)` less `cons(1, L)` holds `[0]`, so is inhabited.
        // `chain_verdict` decides both (measured: with no negative row, or with the same row
        // positive and negative, it leaves the case to the search).
        let int = Pred { cof: true, mask: 0 };
        let one = Pred {
            cof: false,
            mask: 0b10,
        };
        for (p, n, want) in [(one, int, Verdict::Empty), (int, one, Verdict::Inhabited)] {
            let case = ChainCase {
                car_head: int,
                nodes: vec![],
                pos: vec![(p, TailRef::Car)],
                neg: vec![(n, TailRef::Car)],
            };
            assert_eq!(
                check_case(&case, "built"),
                Some(want),
                "the built case {case:?}"
            );
        }
    };
}

/// R9 Q4: random chain families built to exercise the run-length tokens of the prefix-chain
/// search (runs of equal `(stop, head)` steps, negative rows entering a run at different depths,
/// several rows sharing a key, stops inside runs), checked against an exact decider: a
/// breadth-first search over the product of the rows' deterministic automata (no word-length
/// bound), through `chain_verdict` and `verdict` in both definition orders.
#[test]
fn r9_run_tokens_against_product_automaton() {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Pred {
        cof: bool,
        mask: u8, // literals 0..4; symbol 4 stands for every other integer
    }
    impl Pred {
        fn holds(self, sym: u8) -> bool {
            if sym >= 4 {
                self.cof
            } else {
                ((self.mask >> sym) & 1 != 0) != self.cof
            }
        }
        fn ty(self) -> Type {
            let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
            let s = (0..4u8)
                .filter(|&b| (self.mask >> b) & 1 != 0)
                .fold(Type::empty(), |u, b| &u | &lit(b as i64));
            if self.cof { &Type::int() - &s } else { s }
        }
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    enum Tail {
        Car,
        End,
        Node(usize),
    }
    #[derive(Clone, Debug)]
    struct Case {
        car: Pred,
        nodes: Vec<(bool, Pred, Tail)>,
        pos: Vec<(Pred, Tail)>,
        neg: Vec<(Pred, Tail)>,
    }
    // State of one row after a prefix: Start (nothing read), a tail, or dead (None).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    enum St {
        Start,
        At(Tail),
    }
    fn step(c: &Case, row: (Pred, Tail), s: Option<St>, x: u8) -> Option<St> {
        match s? {
            St::Start => row.0.holds(x).then_some(St::At(row.1)),
            St::At(Tail::End) => None,
            St::At(Tail::Car) => c.car.holds(x).then_some(St::At(Tail::Car)),
            St::At(Tail::Node(i)) => c.nodes[i].1.holds(x).then_some(St::At(c.nodes[i].2)),
        }
    }
    fn accepts(c: &Case, s: Option<St>) -> bool {
        match s {
            Some(St::At(Tail::Car | Tail::End)) => true,
            Some(St::At(Tail::Node(i))) => c.nodes[i].0,
            _ => false,
        }
    }
    fn exact_inhabited(c: &Case) -> bool {
        let rows: Vec<(Pred, Tail)> = c.pos.iter().chain(&c.neg).copied().collect();
        let np = c.pos.len();
        let start: Vec<Option<St>> = vec![Some(St::Start); rows.len()];
        let mut seen: HashSet<Vec<Option<St>>> = HashSet::new();
        let mut q = VecDeque::new();
        seen.insert(start.clone());
        q.push_back(start);
        while let Some(s) = q.pop_front() {
            let nonempty = s.iter().all(|x| *x != Some(St::Start));
            if nonempty
                && s[..np].iter().all(|&x| accepts(c, x))
                && !s[np..].iter().any(|&x| accepts(c, x))
            {
                return true;
            }
            for x in 0..5u8 {
                let t: Vec<Option<St>> = rows
                    .iter()
                    .zip(&s)
                    .map(|(&r, &st)| step(c, r, st, x))
                    .collect();
                if t[..np].iter().all(|x| x.is_some()) && seen.insert(t.clone()) {
                    q.push_back(t);
                }
            }
        }
        false
    }
    fn build(c: &Case, tag: &str, rev: bool) -> Type {
        let nn = c.nodes.len();
        let total = 1 + nn + c.pos.len() + c.neg.len();
        let mi = |i: usize| if rev { total - 1 - i } else { i };
        let tail = |t: Tail| match t {
            Tail::Car => Expr::Ref(mi(0), vec![]),
            Tail::End => Expr::Type(Type::atom("nil")),
            Tail::Node(i) => Expr::Ref(mi(1 + i), vec![]),
        };
        let alts = |mut v: Vec<Expr>| {
            if rev {
                v.reverse();
            }
            Expr::Union(v)
        };
        let mut defs = vec![Def {
            name: format!("L{tag}"),
            params: vec![],
            body: alts(vec![
                Expr::Type(Type::atom("nil")),
                Expr::Atom(
                    "cons".into(),
                    vec![Expr::Type(c.car.ty()), Expr::Ref(mi(0), vec![])],
                ),
            ]),
        }];
        for (i, &(stop, h, nx)) in c.nodes.iter().enumerate() {
            let st = Expr::Atom("cons".into(), vec![Expr::Type(h.ty()), tail(nx)]);
            defs.push(Def {
                name: format!("V{i}{tag}"),
                params: vec![],
                body: if stop {
                    alts(vec![Expr::Type(Type::atom("nil")), st])
                } else {
                    st
                },
            });
        }
        for (i, &(h, nx)) in c.pos.iter().chain(&c.neg).enumerate() {
            defs.push(Def {
                name: format!("R{i}{tag}"),
                params: vec![],
                body: Expr::Atom("cons".into(), vec![Expr::Type(h.ty()), tail(nx)]),
            });
        }
        if rev {
            defs.reverse();
        }
        let ts = Group::new(defs).unwrap().instance(vec![]);
        let mut pi: Vec<usize> = (0..c.pos.len()).map(|i| mi(1 + nn + i)).collect();
        let mut ni: Vec<usize> = (0..c.neg.len())
            .map(|i| mi(1 + nn + c.pos.len() + i))
            .collect();
        if rev {
            pi.reverse();
            ni.reverse();
        }
        let p = pi[1..].iter().fold(ts[pi[0]].clone(), |a, &i| &a & &ts[i]);
        let n = ni.iter().fold(Type::empty(), |a, &i| &a | &ts[i]);
        &p - &n
    }

    // Checks one case against the exact decider in both orders; returns the exact answer and
    // what `chain_verdict` says.
    fn check_case(case: &Case, id: &str) -> (bool, Option<Verdict>) {
        let ex = exact_inhabited(case);
        let a = build(case, &format!("_r9rt_{id}f"), false);
        let b = build(case, &format!("_r9rt_{id}r"), true);
        Type::forget_emptiness();
        let ca = a.chain_verdict();
        Type::forget_emptiness();
        let cb = b.chain_verdict();
        assert_eq!(
            ca, cb,
            "case {id}: chain_verdict order mismatch on {case:?}"
        );
        match ca {
            Some(Verdict::Empty) => {
                assert!(
                    !ex,
                    "case {id}: chain_verdict Empty, exact Inhabited on {case:?}"
                );
            }
            Some(Verdict::Inhabited) => {
                assert!(
                    ex,
                    "case {id}: chain_verdict Inhabited, exact Empty on {case:?}"
                );
            }
            _ => {}
        }
        for t in [&a, &b] {
            Type::forget_emptiness();
            match t.verdict() {
                Verdict::Empty => {
                    assert!(!ex, "case {id}: verdict Empty, exact Inhabited on {case:?}")
                }
                Verdict::Inhabited => {
                    assert!(ex, "case {id}: verdict Inhabited, exact Empty on {case:?}")
                }
                Verdict::Refused(_) => {}
            }
        }
        (ex, ca)
    }

    let tally = {
        let (mut rng, _) = Rng::fresh("R9 run tokens");
        let hole = |rng: &mut Rng| Pred {
            cof: true,
            mask: 1u8 << rng.below(4),
        };
        let pred = |rng: &mut Rng| match rng.below(6) {
            0 | 1 => Pred { cof: true, mask: 0 },
            2 | 3 => Pred {
                cof: true,
                mask: 1u8 << rng.below(4),
            },
            4 => Pred {
                cof: true,
                mask: (1u8 << rng.below(4)) | (1u8 << rng.below(4)),
            },
            _ => Pred {
                cof: false,
                mask: 1 + rng.below(15) as u8,
            },
        };
        let (mut decided, mut empty, mut inhab, mut exact_empty) = (0usize, 0usize, 0usize, 0usize);
        for id in 0..300 {
            let car = if rng.below(3) == 0 {
                hole(&mut rng)
            } else {
                Pred { cof: true, mask: 0 }
            };
            let mut nodes: Vec<(bool, Pred, Tail)> = Vec::new();
            // Chains made of runs: a run is r equal `(stop, head)` steps.
            let mut chains: Vec<Vec<usize>> = Vec::new();
            for _ in 0..1 + rng.below(3) {
                let mut cur = if rng.below(5) == 0 {
                    Tail::End
                } else {
                    Tail::Car
                };
                let mut ids = Vec::new();
                for _ in 0..1 + rng.below(3) {
                    let h = pred(&mut rng);
                    let stop = rng.below(5) == 0;
                    for _ in 0..1 + rng.below(4) {
                        nodes.push((stop, h, cur));
                        cur = Tail::Node(nodes.len() - 1);
                        ids.push(nodes.len() - 1);
                    }
                }
                chains.push(ids);
            }
            let any_node = |rng: &mut Rng, chains: &Vec<Vec<usize>>| {
                let ch = &chains[rng.below(chains.len())];
                Tail::Node(ch[rng.below(ch.len())])
            };
            let mut pos = Vec::new();
            let mut neg = Vec::new();
            pos.push((
                pred(&mut rng),
                if rng.below(2) == 0 {
                    Tail::Car
                } else {
                    any_node(&mut rng, &chains)
                },
            ));
            if rng.below(2) == 0 {
                pos.push((pred(&mut rng), any_node(&mut rng, &chains)));
            }
            // Negative rows entering the chains at different depths, often with a head equal
            // to the head of the node they enter (so their tokens share that run's key).
            for _ in 0..1 + rng.below(5) {
                let t = any_node(&mut rng, &chains);
                let h = match (rng.below(3), t) {
                    (0, Tail::Node(i)) => nodes[i].1,
                    _ => pred(&mut rng),
                };
                neg.push((h, t));
            }
            if rng.below(3) == 0 {
                neg.push((pred(&mut rng), Tail::Car));
            }
            let case = Case {
                car,
                nodes,
                pos,
                neg,
            };
            let (ex, ca) = check_case(&case, &id.to_string());
            exact_empty += usize::from(!ex);
            decided += usize::from(matches!(ca, Some(Verdict::Empty | Verdict::Inhabited)));
            empty += usize::from(ca == Some(Verdict::Empty));
            inhab += usize::from(ca == Some(Verdict::Inhabited));
        }
        (decided, empty, inhab, exact_empty)
    };
    eprintln!(
        "R9 run tokens: 300 cases, exact empty={}, chain decided={} (empty={}, inhab={})",
        tally.3, tally.0, tally.1, tally.2
    );
    // An `Empty` decided by the chain search on every run, from a case built to give it
    // (PROOF-test-count-thresholds), in place of a count of the draws: a run of two equal
    // steps `V0 = cons(int, L)`, `V1 = cons(int, V0)` over the carrier `L = nil | cons(int, L)`,
    // the positive row `cons(int, V1)`, the lists of at least three integers, and the negative
    // row `cons(int, V0)`, which enters the run one step later and holds the lists of at least
    // two, so every list of the positive row is taken out and the case is empty;
    // `chain_verdict` decides it (measured; with the same row positive and negative it leaves
    // the case to the search).
    let int = Pred { cof: true, mask: 0 };
    let case = Case {
        car: int,
        nodes: vec![(false, int, Tail::Car), (false, int, Tail::Node(0))],
        pos: vec![(int, Tail::Node(1))],
        neg: vec![(int, Tail::Node(0))],
    };
    assert_eq!(
        check_case(&case, "built"),
        (false, Some(Verdict::Empty)),
        "{case:?}"
    );
}

/// Random groups of list definitions of every shape the families above use at once: one or two
/// groups of two to six definitions, each `nil` or not with one to three rows whose heads are
/// drawn from every head set above (integers, booleans, pairs, the atom, and cofinite `int`
/// less one integer), terms of one or two positive definitions and up to three negative ones,
/// each checked in both orders against the oracle (TEST-kernel-unreached-paths-4: the prefix
/// chains' carrier and link checks, their refusals and the steps of their sweep that the
/// families above leave unread).
#[test]
fn the_sweep_agrees_on_random_groups_of_every_head() {
    let t = random_groups(Rng::new(0x5ee9));
    eprintln!("random groups: {t:?}");
}

fn random_groups(mut rng: Rng) -> Tally {
    const PALETTE: [u16; 13] = [
        INT,
        ONE,
        TWO,
        ONE | TWO,
        INT & !ONE,
        HOLES[0],
        HOLES[1],
        BOOL,
        TRUE,
        PAIR,
        PAIR_ONE,
        ATOM,
        INT | ATOM,
    ];
    let mut tally = Tally::default();
    for id in 0..300 {
        let groups: Vec<Vec<D>> = (0..1 + rng.below(2))
            .map(|_| {
                let k = 2 + rng.below(5);
                (0..k)
                    .map(|_| D {
                        nil: rng.below(3) == 0,
                        rows: (0..1 + rng.below(3))
                            .map(|_| (PALETTE[rng.below(PALETTE.len())], rng.below(k)))
                            .collect(),
                    })
                    .collect()
            })
            .collect();
        let pick = |rng: &mut Rng| {
            let g = rng.below(groups.len());
            (g, rng.below(groups[g].len()))
        };
        let pos = (0..1 + rng.below(2)).map(|_| pick(&mut rng)).collect();
        let neg = (0..rng.below(4)).map(|_| pick(&mut rng)).collect();
        let spec = Spec { groups };
        let term = Term { pos, neg };
        both_orders(
            &mut tally,
            &spec,
            &term,
            &format!("_xrg{id}"),
            &format!("random group {id}"),
        );
    }
    tally
}
