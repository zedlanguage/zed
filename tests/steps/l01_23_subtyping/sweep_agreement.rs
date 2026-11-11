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
use zed_kernel::types::{Type, Verdict};
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
            assert_eq!(c, v, "{what}: the prefix chains say {c:?}, the verdict is {v:?}");
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

fn big<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn the_sweep_agrees_on_integer_families() {
    let t = big(|| families(&HEADS[..1], &[false, true]));
    eprintln!("integer families: {t:?}");
}

#[test]
fn the_sweep_agrees_on_boolean_families() {
    let t = big(|| families(&HEADS[1..2], &[false, true]));
    eprintln!("boolean families: {t:?}");
}

#[test]
fn the_sweep_agrees_on_pair_head_families() {
    let t = big(|| families(&HEADS[2..3], &[false, true]));
    eprintln!("pair head families: {t:?}");
}

#[test]
fn the_sweep_agrees_on_atom_head_families() {
    let t = big(|| families(&HEADS[3..], &[false, true]));
    eprintln!("atom head families: {t:?}");
}

/// Meets of two families of one size, and pairs of two families: every skipped place of each,
/// with `m = n`.
#[test]
fn the_sweep_agrees_on_meets_and_pairs() {
    let t = big(|| {
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
    });
    eprintln!("meets and pairs: {t:?}");
}

/// Random families of chains: a list `L` of all heads used, and up to six definitions with
/// `nil` or not and one or two rows of random heads and tails, some of them less the union of
/// a random set of the definitions; one group, or two with the second's tails into itself.
#[test]
fn the_sweep_agrees_on_random_chains() {
    let t = big(|| {
        let mut tally = Tally::default();
        let mut rng = Rng::new(0x5eed_2026);
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
        for id in 0..3000 {
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
    });
    eprintln!("random chains: {t:?}");
}

/// Random families of links, the sweep's shape: up to eight definitions of one row each, with
/// `nil` or not, over the integer cells or the boolean ones, less the union of most of them.
#[test]
fn the_sweep_agrees_on_random_links() {
    let t = big(|| {
        let mut tally = Tally::default();
        let mut rng = Rng::new(0x11_2026);
        let sets: [&[u16]; 2] = [
            &[INT, ONE, INT & !ONE, TWO, INT & !TWO, ONE | TWO],
            &[BOOL, TRUE, BOOL & !TRUE],
        ];
        for id in 0..6000 {
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
    });
    eprintln!("random links: {t:?}");
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
/// of [`CHAIN_HEADS`] and a tail `L`, `F1` or `F2`; in both orders.
#[test]
fn the_sweep_agrees_on_redundant_rows_with_cofinite_heads() {
    let t = big(|| {
        let mut tally = Tally::default();
        let mut id = 0;
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
                    let (spec, term) = holes(n, skip, chains);
                    id += 1;
                    let what = format!("holes n {n} skip {skip} chains {chains:?}");
                    both_orders(&mut tally, &spec, &term, &format!("_xh{id}"), &what);
                }
            }
        }
        tally
    });
    eprintln!("redundant rows: {t:?}");
}

/// The `chain` kind: `L`, `G1 = cons(1, L)`, `Gk = sides | cons(int, G{k-1})` with `sides` a
/// list of rows into `L` or `G1`, and `Mk` as in [`family`]. The terms are `L` less `Gg | Mm`,
/// and `Gg` less `Mm`, for every `g <= n <= 5` and `m <= n + 1`; in both orders.
#[test]
fn the_sweep_agrees_on_union_links() {
    let t = big(|| {
        let mut tally = Tally::default();
        let mut id = 0;
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
    });
    eprintln!("union links: {t:?}");
}

/// Random links over the integer cells with cofinite heads, one row or (one time in four) two,
/// `nil` or not, less the union of most of them; in both orders.
#[test]
fn the_sweep_agrees_on_random_cofinite_links() {
    let t = big(|| {
        let mut tally = Tally::default();
        let mut rng = Rng::new(0xc0f1_2026);
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
        for id in 0..2500 {
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
    });
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
fn staggered(c: u16) -> Tally {
    big(|| {
        let mut tally = Tally::default();
        let mut id = 0;
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
    })
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
    let t = big(|| {
        let mut tally = Tally::default();
        let mut rng = Rng::new(0x5ab_2026);
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
        for id in 0..3000 {
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
                ds.push(D { nil: true, rows: vec![(h, k + 1)] });
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
    });
    eprintln!("random positive chains: {t:?}");
    assert!(t.swept > 0, "the sweep decides some");
}

/// Disjoint-hole and overlapping-hole spines (X14 / Q2): a spine `Y1..Ym` (`m <= 3`) where each
/// link head is drawn from `HOLES` (`int \ {3}`, `int \ {4}`, `int \ {5}`). When the holes are
/// pairwise distinct, the spine is inside the Disjoint-Hole Spine class and decided by the sweep;
/// when two links share a hole, it is outside the class and left to the search.
#[test]
fn the_sweep_agrees_on_disjoint_and_overlapping_hole_spines() {
    let t = big(|| {
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
    });
    eprintln!("hole spines: {t:?}");
}

/// R6: acyclic carrier-plus-chains, with stops, mixed positives and multi-value holes.
/// The DFA oracle reads masks only; no emptiness or membership query contributes to it.
#[test]
fn r6_random_carrier_chains_against_masks() {
    let tally = big(|| {
        let mut tally = Tally::default();
        let mut rng = Rng::new(0x6c0de2026);
        let palette = [INT, ONE, TWO, ONE | TWO, HOLES[0], HOLES[1],
            HOLES[0] & HOLES[1], INT & !(ONE | TWO),
            ONE | (1 << 8), INT & !ONE, INT & !TWO];
        for id in 0..4000 {
            let n = 3 + rng.below(9);
            let mut ds = vec![D { nil: true, rows: vec![(INT, 0)] }];
            for i in 1..=n {
                ds.push(D {
                    nil: rng.below(4) == 0,
                    rows: vec![(palette[rng.below(palette.len())], rng.below(i))],
                });
            }
            let p = 1 + rng.below(n);
            let mut pos = vec![(0, p)];
            if rng.below(2) == 0 { pos.push((0, 0)); }
            if rng.below(3) == 0 { pos.push((0, 1 + rng.below(n))); }
            let neg = (1..=n).filter(|&i| i != p && rng.below(3) != 0)
                .map(|i| (0, i)).collect();
            let term = Term { pos, neg };
            let spec = Spec { groups: vec![ds] };
            both_orders(&mut tally, &spec, &term, &format!("_r6c{id}"),
                &format!("R6 chain masks {id}"));
        }
        tally
    });
    eprintln!("R6 carrier chains: {tally:?}");
    assert!(tally.swept > 0);
}

/// Two escaping predicates per root do not imply 2-SAT when holes overlap.
/// Selector positions choose a literal of each 3-clause. Each implication
/// selector=j => literal_j holds has just two escaping predicates.
pub(super) fn r6_two_predicate_reduction_matches_boolean_bruteforce() {
    big(|| {
        let mut rng = Rng::new(0x6a705a7);
        let domain = ONE | TWO | (1 << 8); // values 1,2,3
        for id in 0..384 {
            let k = 1 + rng.below(4);
            let m = 1 + rng.below(4);
            let clauses: Vec<Vec<(usize,bool)>> = (0..m).map(|_| (0..3)
                .map(|_| (rng.below(k),rng.below(2)==0)).collect()).collect();
            let sat = (0..1usize<<k).any(|a| clauses.iter().all(|cl|
                cl.iter().any(|&(i,b)| ((a>>i)&1 != 0)==b)));
            let mut ds = vec![D { nil: true, rows: vec![(INT,0)] }];
            let len = k + m;
            let mut positive = 0;
            for j in (0..len).rev() {
                ds.push(D { nil:false, rows:vec![(if j<k {ONE|TWO} else {domain},positive)] });
                positive=ds.len()-1;
            }
            let mut neg=Vec::new();
            for (c,cl) in clauses.iter().enumerate() {
                for (j,&(i,b)) in cl.iter().enumerate() {
                    let mut root=0;
                    for s in (0..len).rev() {
                        // Escape root iff selector != j OR the chosen literal is true.
                        let hole = if s==k+c { domain & ![ONE,TWO,1<<8][j] }
                            else if s==i { if b {TWO} else {ONE} } else {0};
                        ds.push(D { nil:false, rows:vec![(INT & !hole,root)] });
                        root=ds.len()-1;
                    }
                    neg.push((0,root));
                }
            }
            let spec=Spec {groups:vec![ds]};
            let term=Term {pos:vec![(0,positive)],neg};
            assert_eq!(spec.inhabited(&term),sat,"selector reduction {id}: {clauses:?}");
            let mut tally=Tally::default();
            both_orders(&mut tally,&spec,&term,&format!("_r6sat{id}"),"two-predicate reduction");
        }
        eprintln!("R6 two-predicate selector reduction: 384 formulas checked");
    });
}

/// R6-C2: avoiding the leaf head at an optional spine arrival is a
/// commitment. Another negative chain can distinguish that choice.
#[test]
fn r6_optional_spine_arrival_must_not_force_a_later_empty() {
    big(|| {
        // 0 L; 1 F1; 2 F2; 3 F3; 4 A4; 5 A3; 6 A2; 7 A1;
        // 8 P4; 9 P3; 10 P2; 11 P1.
        let ds=vec![
            D {nil:true, rows:vec![(INT,0)]},
            D {nil:false, rows:vec![(ONE,0)]},
            D {nil:false, rows:vec![(INT & !TWO,1)]},
            D {nil:false, rows:vec![(HOLES[0],2)]},
            D {nil:false, rows:vec![(INT,0)]},
            D {nil:false, rows:vec![(INT & !ONE,4)]},
            D {nil:false, rows:vec![(INT,5)]},
            D {nil:false, rows:vec![(INT,6)]},
            D {nil:false, rows:vec![(ONE,0)]},
            D {nil:false, rows:vec![(INT,8)]},
            D {nil:false, rows:vec![(INT,9)]},
            D {nil:false, rows:vec![(INT,10)]},
        ];
        let spec=Spec {groups:vec![ds]};
        let term=Term {pos:vec![(0,11)],neg:vec![(0,3),(0,7)]};
        assert!(spec.inhabited(&term)); // [3,0,1,1]
        let mut tally=Tally::default();
        both_orders(&mut tally,&spec,&term,"_r6optional","optional spine arrival");
    });
}

#[test]
fn r6_greedy_guard_admits_a_partially_compatible_unused_slot() {
    big(|| {
        let spec=Spec {groups:vec![vec![
            D {nil:true, rows:vec![(INT,0)]},
            D {nil:false, rows:vec![(ONE,0)]},
            D {nil:false, rows:vec![(INT & !TWO,1)]},
            D {nil:false, rows:vec![(HOLES[0],2)]},
            D {nil:false, rows:vec![(HOLES[1],3)]},
            D {nil:false, rows:vec![(ONE,0)]},
            D {nil:false, rows:vec![(ONE,5)]},
            D {nil:false, rows:vec![(ONE|TWO,6)]},
            D {nil:false, rows:vec![(INT,7)]},
        ]]};
        let term=Term {pos:vec![(0,8)],neg:vec![(0,4)]};
        let ts=spec.build("_r6guard");
        let t=spec.ty(&ts,&term);
        assert_eq!(t.chain_verdict(),Some(Verdict::Inhabited));
        let mut tally=Tally::default();
        both_orders(&mut tally,&spec,&term,"_r6guardorder","unused partial slot");
    });
}
