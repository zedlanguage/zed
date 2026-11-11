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
        for id in 0..4000 {
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
    });
    eprintln!("R6 carrier chains: {tally:?}");
    assert!(tally.swept > 0);
}

/// Two escaping predicates per root do not imply 2-SAT when holes overlap.
/// Selector positions choose a literal of each 3-clause. Each implication
/// selector=j => literal_j holds has just two escaping predicates. Only the formulas `ids` (of
/// 384) are checked; the generator runs over all of them, so a piece checks the same formulas
/// whatever the split.
pub(super) fn r6_two_predicate_reduction_matches_boolean_bruteforce(ids: std::ops::Range<usize>) {
    big(|| {
        let mut rng = Rng::new(0x6a705a7);
        let domain = ONE | TWO | (1 << 8); // values 1,2,3
        for id in 0..384 {
            let k = 1 + rng.below(4);
            let m = 1 + rng.below(4);
            let clauses: Vec<Vec<(usize, bool)>> = (0..m)
                .map(|_| (0..3).map(|_| (rng.below(k), rng.below(2) == 0)).collect())
                .collect();
            if !ids.contains(&id) {
                continue;
            }
            let sat = (0..1usize << k).any(|a| {
                clauses
                    .iter()
                    .all(|cl| cl.iter().any(|&(i, b)| ((a >> i) & 1 != 0) == b))
            });
            let mut ds = vec![D {
                nil: true,
                rows: vec![(INT, 0)],
            }];
            let len = k + m;
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
            ids.len()
        );
    });
}

/// R6-C2: avoiding the leaf head at an optional spine arrival is a
/// commitment. Another negative chain can distinguish that choice.
#[test]
fn r6_optional_spine_arrival_must_not_force_a_later_empty() {
    big(|| {
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
    });
}

#[test]
fn r6_greedy_guard_admits_a_partially_compatible_unused_slot() {
    big(|| {
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
    });
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
    let tally = big(|| {
        let mut tally = Tally::default();
        let mut rng = Rng::new(0x70b7_1031);
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
        for id in 0..3000 {
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
    });
    eprintln!("R7 optional spine choices: {tally:?}");
    assert!(tally.swept > 0);
}

/// R7: two roots on one spine. `R1` reaches the leaf `S1` at step 2 and `R2` at step 3;
/// avoiding `S1`'s head at step 2 (w2 != 1) takes away `R2`'s only usable hole (w2 = 1), and
/// the first head meets no hole, so `greedy_unsafe` stays false. The one value is [a, 1, 1].
/// Built to tell the X31 guard from Gemini R6's `can_prove_empty` (cleared only when a
/// negative chain is active at the arrival); it does not: `R2` is an active group at step 2,
/// so both decline Empty (R7, Q2).
#[test]
fn r7_optional_spine_arrival_with_no_active_negative() {
    big(|| {
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
    });
}

/// R7 Q2(a): when `active_neg` is empty at an optional spine arrival (`r0 != r0_without_h1`),
/// `can_prove_empty` remains `true` and soundly decides both Case A (`committed_count == 0`) and
/// Case B (`committed_count > 0`) inputs where an unconditional `optional_spine_choice` flag
/// declines.
#[test]
fn r7_can_prove_empty_admits_empty_active_neg_where_codex_flag_declines() {
    big(|| {
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
    });
}

/// R7 Q2(b) / Q7(iii) Bug A: a struct payload inside `#cons` (`#cons(k: 99)` via
/// `Universe::Struct`, so `q.structs == true`) must not be ignored by `find_prefix_chains` or
/// `escape::decide`. On `cb709f13` both ignored `q.structs` and returned a wrong `Empty`.
#[test]
fn r7_bug_a_non_tuple_payload_in_cons_is_not_empty() {
    big(|| {
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
    });
}

/// R7 Q2(b) / Q7(iii) Bug B: a tail union with two bare atoms (`#nil_a | #nil_z | #cons(0, L)`)
/// must not have `#nil_a` overwritten by `list_step`. On `cb709f13` both `find_prefix_chains` and
/// `escape::decide` returned a wrong `Empty`, although `#cons((0, #nil_a))` is in `t`.
#[test]
fn r7_bug_b_multiple_bare_atoms_in_tail_union_is_not_empty() {
    big(|| {
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
    });
}

/// R7 Q7(i): in Gemini R6, `step_exact[step]` was false when `non_disjoint_stop_heads` was
/// non-empty while `can_prove_empty` stayed true, omitting step 2 from `active_spine_steps` and
/// returning a wrong `Empty` on `[7, 3, 7, 1]`.
#[test]
fn r7_gemini_r6_non_disjoint_stop_clause_omission_is_inhabited() {
    big(|| {
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
    });
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

    big(|| {
        let mut rng = Rng::new(0x77c0_ffee_2026);
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

        let mut chain_decided = 0usize;
        let mut chain_empty = 0usize;
        let mut chain_inhab = 0usize;
        for id in 0..1200 {
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
            let witness = brute_force_inhabited(&case);
            let inhab = witness.is_some();
            let a = build_case(&case, &format!("_r7rc_{id}f"), false);
            let b = build_case(&case, &format!("_r7rc_{id}r"), true);

            Type::forget_emptiness();
            let ca = a.chain_verdict();
            Type::forget_emptiness();
            let cb = b.chain_verdict();
            assert_eq!(
                ca, cb,
                "case {id}: chain_verdict order mismatch on {case:?}"
            );
            if let Some(cv) = ca {
                chain_decided += 1;
                match cv {
                    Verdict::Empty => {
                        assert!(
                            !inhab,
                            "case {id}: chain_verdict Empty but brute force found {witness:?} on {case:?}"
                        );
                        chain_empty += 1;
                    }
                    Verdict::Inhabited => {
                        assert!(
                            inhab,
                            "case {id}: chain_verdict Inhabited but brute force found none on {case:?}"
                        );
                        chain_inhab += 1;
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
        }
        eprintln!(
            "R7 random carrier+chains: 1200 cases, chain_decided={chain_decided} (empty={chain_empty}, inhab={chain_inhab})"
        );
        assert!(chain_empty > 50 && chain_inhab > 50);
    });
}
