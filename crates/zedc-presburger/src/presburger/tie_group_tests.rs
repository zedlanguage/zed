//! [`System::symmetries`] and [`System::rekey`] against brute force over every small system of a
//! stated family, under every naming (row PROOF-tie-depth2-generators-whole-group).
//!
//! A family is a set of slots (the pairs, or the triples, of `n` variables) and a list of
//! kinds, each kind the rows a slot may hold; a system of the family gives each slot one kind,
//! and every variable the bound `x >= 0`, so every variable is held by a row. The families are
//! closed under renaming the variables, so each system is checked through the least system of its
//! class (its encoding, the kinds slot by slot, least among all namings), once under each of the
//! `n!` namings, each naming built anew through [`System::add`].
//!
//! For each system: the rows are given to [`System::new`] (every variable of color 0) and
//! [`System::rekey`] is run. The group `Aut` is found by trying all `n!` permutations: those
//! that map the held rows, with their constants, onto themselves. Checked:
//! - every member of `Aut` keeps the colors [`System::rekey`] gave (the refinement is kept by the
//!   symmetries of the rows);
//! - under every naming `π`, the variable `π(v)` gets the color `v` got, and the held rows are the
//!   images of the held rows;
//! - for each color held by two variables or more (each such color is a set of variables `Aut`
//!   maps onto itself, as a tie of [`System::least`] is), [`System::symmetries`] is called with its
//!   variables in increasing order, and when it answers, every permutation it gives is in `Aut`
//!   and they make a group of `|Aut|` elements, so all of `Aut`; whether it answers, and the size
//!   of the group made, are the same under every naming.

use super::*;
use std::collections::HashSet;

mod bench;

/// A permutation of the variables, as the image of each.
type Perm = Vec<usize>;

/// A row of a kind: its coefficient at each place of the slot, and its constant; the row is
/// `Σ c[p]·x[slot[p]] + k >= 0`.
type KindRow = (Vec<i64>, i64);

struct Family {
    n: usize,
    /// The slots, each a tuple of variables in increasing order, all of one length.
    slots: Vec<Vec<usize>>,
    kinds: Vec<Vec<KindRow>>,
    /// Every permutation of the variables.
    perms: Vec<Perm>,
    /// For each permutation and each slot `t` of the image: the slot `s` whose image is `t`, and
    /// the kind each kind at `s` becomes at `t`.
    image: Vec<Vec<(usize, Vec<u8>)>>,
}

/// Every permutation of `0..n`, the identity first.
fn all_perms(n: usize) -> Vec<Perm> {
    let mut out = Vec::new();
    let mut p: Perm = (0..n).collect();
    loop {
        out.push(p.clone());
        // The next permutation in lexicographic order.
        let Some(i) = (1..n).rev().find(|&i| p[i - 1] < p[i]) else {
            return out;
        };
        let j = (i..n)
            .rev()
            .find(|&j| p[j] > p[i - 1])
            .expect("a larger one");
        p.swap(i - 1, j);
        p[i..].reverse();
    }
}

/// Every tuple of `k` of `0..n`, in increasing order, listed in lexicographic order.
fn tuples(n: usize, k: usize) -> Vec<Vec<usize>> {
    if k == 0 {
        return vec![Vec::new()];
    }
    let mut out = Vec::new();
    for t in tuples(n, k - 1) {
        let from = t.last().map_or(0, |l| l + 1);
        for v in from..n {
            let mut u = t.clone();
            u.push(v);
            out.push(u);
        }
    }
    out
}

/// The rows of a kind, sorted, as a key to compare kinds by.
fn sorted(rows: &[KindRow]) -> Vec<KindRow> {
    let mut rows = rows.to_vec();
    rows.sort();
    rows
}

impl Family {
    fn new(n: usize, arity: usize, kinds: Vec<Vec<KindRow>>) -> Family {
        let slots = tuples(n, arity);
        let perms = all_perms(n);
        let at: HashMap<Vec<usize>, usize> = (slots.iter().cloned().enumerate())
            .map(|(i, s)| (s, i))
            .collect();
        let keys: Vec<Vec<KindRow>> = kinds.iter().map(|k| sorted(k)).collect();
        let image = (perms.iter())
            .map(|p| {
                let mut by_target = vec![(0, Vec::new()); slots.len()];
                for (s, slot) in slots.iter().enumerate() {
                    let mut to: Vec<usize> = slot.iter().map(|&v| p[v]).collect();
                    to.sort_unstable();
                    // Place q[i] of the image holds the image of place i.
                    let q: Vec<usize> = (slot.iter())
                        .map(|&v| to.iter().position(|&w| w == p[v]).expect("in the image"))
                        .collect();
                    let map: Vec<u8> = (kinds.iter())
                        .map(|rows| {
                            let moved: Vec<KindRow> = (rows.iter())
                                .map(|(c, k)| {
                                    let mut d = vec![0; c.len()];
                                    for (i, &ci) in c.iter().enumerate() {
                                        d[q[i]] = ci;
                                    }
                                    (d, *k)
                                })
                                .collect();
                            let key = sorted(&moved);
                            let kind = keys.iter().position(|k| *k == key);
                            u8::try_from(kind.expect("the kinds are closed under renaming"))
                                .expect("few kinds")
                        })
                        .collect();
                    by_target[at[&to]] = (s, map);
                }
                by_target
            })
            .collect();
        Family {
            n,
            slots,
            kinds,
            perms,
            image,
        }
    }

    /// The encoding of the system that the permutation at `pi` makes of `enc`.
    fn renamed(&self, enc: &[u8], pi: usize) -> Vec<u8> {
        (self.image[pi].iter())
            .map(|(s, map)| map[usize::from(enc[*s])])
            .collect()
    }

    /// Whether `enc` is the least encoding of its class.
    fn least(&self, enc: &[u8]) -> bool {
        (1..self.perms.len()).all(|pi| {
            for (t, (s, map)) in self.image[pi].iter().enumerate() {
                let v = map[usize::from(enc[*s])];
                match v.cmp(&enc[t]) {
                    Ordering::Less => return false,
                    Ordering::Greater => return true,
                    Ordering::Equal => {}
                }
            }
            true
        })
    }

    /// The system of `enc`: the bounds, then the rows of each slot.
    fn system(&self, enc: &[u8]) -> System {
        let mut sys = System::new(std::iter::repeat_n(0, self.n));
        for v in 0..self.n {
            sys.add(Row {
                a: vec![(v, Int::ONE)].into(),
                k: Int::ZERO,
            });
        }
        for (slot, &kind) in self.slots.iter().zip(enc) {
            for (c, k) in &self.kinds[usize::from(kind)] {
                let a: Vec<Term> = (slot.iter().zip(c))
                    .filter(|(_, c)| **c != 0)
                    .map(|(&v, &c)| (v, Int::from(c)))
                    .collect();
                sys.add(Row {
                    a: a.into(),
                    k: Int::from(*k),
                });
            }
        }
        sys
    }
}

/// The held rows, sorted.
fn held(sys: &System) -> Vec<(Vec<Term>, Int)> {
    let mut rows: Vec<(Vec<Term>, Int)> = (sys.rows.iter())
        .map(|(a, h)| (a.to_vec(), h.k.clone()))
        .collect();
    rows.sort();
    rows
}

/// Whether `p` maps the held rows, with their constants, onto themselves.
fn keeps_rows(sys: &System, p: &[usize]) -> bool {
    (sys.rows.iter()).all(|(a, h)| {
        let image = moved_by(a, |i| p[i]);
        (sys.rows.get(image.as_slice())).is_some_and(|g| g.k == h.k)
    })
}

/// The group the permutations `gens` of `0..n` make, by closing under composition.
fn closure(n: usize, gens: &[Perm]) -> HashSet<Perm> {
    let id: Perm = (0..n).collect();
    let mut seen: HashSet<Perm> = HashSet::from([id.clone()]);
    let mut todo = vec![id];
    while let Some(h) = todo.pop() {
        for g in gens {
            let gh: Perm = h.iter().map(|&i| g[i]).collect();
            if seen.insert(gh.clone()) {
                todo.push(gh);
            }
        }
    }
    seen
}

/// What [`System::rekey`] and [`System::symmetries`] give for one system: the colors, and for
/// each color held by two variables or more, the permutations found, as whole permutations.
/// The key [`ALL`] holds what [`System::symmetries`] finds for all the variables, called
/// before [`System::rekey`], when every variable has the color 0.
struct Found {
    keys: Vec<usize>,
    by_color: BTreeMap<usize, Option<Vec<Perm>>>,
}

const ALL: usize = usize::MAX;

fn found(sys: &mut System, n: usize) -> Found {
    let whole = |sys: &System, vs: &[usize]| -> Option<Vec<Perm>> {
        sys.symmetries(vs).map(|moves| {
            (moves.iter())
                .map(|m| {
                    let mut p: Perm = (0..n).collect();
                    for &(v, w) in m {
                        p[v] = w;
                    }
                    p
                })
                .collect()
        })
    };
    let all: Vec<usize> = (0..n).collect();
    let before = whole(sys, &all);
    sys.rekey();
    let keys: Vec<usize> = sys.vars.iter().map(|v| v.key).collect();
    let mut classes: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (v, &k) in keys.iter().enumerate() {
        classes.entry(k).or_default().push(v);
    }
    let mut by_color: BTreeMap<usize, Option<Vec<Perm>>> = (classes.into_iter())
        .filter(|(_, vs)| vs.len() > 1)
        .map(|(k, vs)| (k, whole(sys, &vs)))
        .collect();
    by_color.insert(ALL, before);
    Found { keys, by_color }
}

/// Counts of what the check saw, so a test can show that each case was reached.
#[derive(Default, Debug)]
struct Seen {
    classes: usize,
    namings: usize,
    answered: usize,
    /// Answers whose group fixes the first variable in more ways than one: the cell `C` of
    /// [`System::symmetries`] was used.
    answered_with_cell: usize,
    refused: usize,
    /// Refusals where `Aut` does send the first variable to every other one of the color.
    refused_symmetric: usize,
    largest_group: usize,
}

/// Checks every system of `family` as the doc of this module says.
fn check(family: &Family) -> Seen {
    check_part(family, 0, 1)
}

/// Checks the classes of `family` whose place in the order of their least encodings is
/// `part` modulo `parts`, so that a large family is checked in pieces.
fn check_part(family: &Family, part: usize, parts: usize) -> Seen {
    let mut seen = Seen::default();
    let kinds = u8::try_from(family.kinds.len()).expect("few kinds");
    let mut enc = vec![0u8; family.slots.len()];
    let mut place = 0;
    loop {
        if family.least(&enc) {
            if place % parts == part {
                seen.classes += 1;
                check_class(family, &enc, &mut seen);
            }
            place += 1;
        }
        // The next encoding, counting in base `kinds`.
        let Some(i) = enc.iter().rposition(|&d| d + 1 < kinds) else {
            break;
        };
        enc[i] += 1;
        enc[i + 1..].fill(0);
    }
    seen
}

fn check_class(family: &Family, enc: &[u8], seen: &mut Seen) {
    let n = family.n;
    let mut sys = family.system(enc);
    let rows = held(&sys);
    let aut: HashSet<Perm> = (family.perms.iter())
        .filter(|p| keeps_rows(&sys, p))
        .cloned()
        .collect();
    let base = found(&mut sys, n);
    let show = || format!("system {enc:?}, rows {rows:?}");
    for p in &aut {
        assert!(
            (0..n).all(|v| base.keys[p[v]] == base.keys[v]),
            "a symmetry {p:?} does not keep the colors {:?}; {}",
            base.keys,
            show()
        );
    }
    seen.largest_group = seen.largest_group.max(aut.len());
    // The size of the group made for each color, where it answers.
    let mut sizes: BTreeMap<usize, Option<usize>> = BTreeMap::new();
    for (&k, perms) in &base.by_color {
        let class: Vec<usize> = (0..n).filter(|&v| k == ALL || base.keys[v] == k).collect();
        let x = class[0];
        match perms {
            Some(gens) => {
                for g in gens {
                    assert!(aut.contains(g), "{g:?} is no symmetry; {}", show());
                }
                let made = closure(n, gens);
                assert_eq!(
                    made.len(),
                    aut.len(),
                    "the permutations found for color {k} ({gens:?}) make {} of the {} \
                     symmetries; {}",
                    made.len(),
                    aut.len(),
                    show()
                );
                seen.answered += 1;
                let fixing_x = aut.iter().filter(|p| p[x] == x).count();
                if fixing_x > 1 {
                    seen.answered_with_cell += 1;
                }
                sizes.insert(k, Some(made.len()));
            }
            None => {
                seen.refused += 1;
                let orbit: HashSet<usize> = aut.iter().map(|p| p[x]).collect();
                if class.iter().all(|v| orbit.contains(v)) {
                    seen.refused_symmetric += 1;
                }
                sizes.insert(k, None);
            }
        }
    }
    for pi in 0..family.perms.len() {
        let p = &family.perms[pi];
        let renamed = family.renamed(enc, pi);
        let mut other = family.system(&renamed);
        let mut images: Vec<(Vec<Term>, Int)> = (rows.iter())
            .map(|(a, k)| (moved_by(a, |i| p[i]), k.clone()))
            .collect();
        images.sort();
        assert_eq!(
            held(&other),
            images,
            "naming {p:?}: other rows held; {}",
            show()
        );
        let f = found(&mut other, n);
        assert!(
            (0..n).all(|v| f.keys[p[v]] == base.keys[v]),
            "naming {p:?}: colors {:?} against {:?}; {}",
            f.keys,
            base.keys,
            show()
        );
        let inverse: Perm = {
            let mut q = vec![0; n];
            for (v, &w) in p.iter().enumerate() {
                q[w] = v;
            }
            q
        };
        for (k, perms) in &f.by_color {
            let size = perms.as_ref().map(|gens| {
                for g in gens {
                    // π⁻¹·g·π is a symmetry of the first naming.
                    let back: Perm = (0..n).map(|v| inverse[g[p[v]]]).collect();
                    assert!(
                        aut.contains(&back),
                        "naming {p:?}: {g:?} is no symmetry; {}",
                        show()
                    );
                }
                closure(n, gens).len()
            });
            assert_eq!(
                sizes.get(k),
                Some(&size),
                "naming {p:?}, color {k}: {size:?} against {:?}; {}",
                sizes.get(k),
                show()
            );
        }
        seen.namings += 1;
    }
}

/// Kinds of the rows of a pair `(x[i], x[j])`, `i < j`.
fn pair_kinds(which: &[usize]) -> Vec<Vec<KindRow>> {
    let all: [Vec<KindRow>; 7] = [
        // No row.
        vec![],
        // x[i] >= x[j], and the reverse.
        vec![(vec![1, -1], 0)],
        vec![(vec![-1, 1], 0)],
        // x[i] + x[j] >= 1.
        vec![(vec![1, 1], -1)],
        // x[i] == x[j], as two rows.
        vec![(vec![1, -1], 0), (vec![-1, 1], 0)],
        // x[i] + 2·x[j] >= 2, and the reverse.
        vec![(vec![1, 2], -2)],
        vec![(vec![2, 1], -2)],
    ];
    which.iter().map(|&w| all[w].clone()).collect()
}

/// Every system of two and three variables whose pairs each hold one of the seven kinds above.
/// Four variables, 24 namings of each of thousands of classes, is a benchmark
/// (`bench::pairs_of_seven_kinds_on_four_variables`).
#[test]
fn pairs_of_seven_kinds_on_two_and_three_variables() {
    for n in 2..=3 {
        let seen = check(&Family::new(n, 2, pair_kinds(&[0, 1, 2, 3, 4, 5, 6])));
        eprintln!("{n} variables: {seen:?}");
        assert!(seen.answered > 0 && seen.refused > 0);
    }
}

/// Every system of five variables whose pairs each hold no row or `x[i] + x[j] >= 1`: the
/// graphs. The oriented graphs on five variables, and the families on six, are benchmarks.
#[test]
fn graphs_on_five_variables() {
    let seen = check(&Family::new(5, 2, pair_kinds(&[0, 3])));
    eprintln!("{seen:?}");
    // The number of graphs on five vertices (OEIS A000088), which shows the enumeration misses
    // none.
    assert_eq!(seen.classes, 34);
    assert!(seen.answered_with_cell > 0 && seen.refused_symmetric > 0);
}

/// Every system of five variables whose pairs each hold `x[i] >= x[j]` or the reverse: the
/// tournaments, whose groups have odd order, so no symmetry swaps two variables.
#[test]
fn tournaments_on_five_variables() {
    let seen = check(&Family::new(5, 2, pair_kinds(&[1, 2])));
    eprintln!("{seen:?}");
    // The number of tournaments on five vertices (OEIS A000568).
    assert_eq!(seen.classes, 12);
    assert!(seen.answered > 0);
}

/// The system of six variables whose pairs `(0, 1)`, `(2, 3)` and `(4, 5)` each hold
/// `x[i] + x[j] >= 1` and whose other pairs hold no row: three disjoint pairs, which fixing two
/// variables does not tell apart, the case `bench::graphs_on_six_variables` was written for.
/// [`System::symmetries`] refuses a color whose variables `Aut` does send one to another;
/// checked here under all 720 namings.
#[test]
fn three_disjoint_pairs_on_six_variables() {
    let family = Family::new(6, 2, pair_kinds(&[0, 3]));
    let enc: Vec<u8> = (family.slots.iter())
        .map(|s| u8::from(matches!(s[..], [0, 1] | [2, 3] | [4, 5])))
        .collect();
    let mut seen = Seen::default();
    check_class(&family, &enc, &mut seen);
    eprintln!("{seen:?}");
    assert_eq!(seen.namings, 720);
    assert!(seen.refused_symmetric > 0);
}

/// Every system of five variables whose triples each hold no row or `x[i] + x[j] + x[k] >=
/// 1`.
#[test]
fn rows_of_three_on_five_variables() {
    let kinds = vec![vec![], vec![(vec![1, 1, 1], -1)]];
    let seen = check(&Family::new(5, 3, kinds));
    eprintln!("{seen:?}");
    // The number of 3-uniform hypergraphs on five vertices (OEIS A000665).
    assert_eq!(seen.classes, 34);
    assert!(seen.answered > 0);
}

/// A chain of `n` gadgets: links `w_0..w_n` and, for gadget `i`, `x_i0..x_i3`, each variable in
/// `[0, 10]`, with `1 <= w_i - w_{i+1} + Σ x_ij <= 3`. The gadgets are alike, so the counts of
/// [`System::shrinking`] tie again and again as the chain is eliminated (the scaling benchmark
/// `bench::names::a_chain_of_gadgets_ties_at_every_step` runs the same family). At every read
/// of the counts the Omega test checks them against fresh ones ([`System::stale`]); this test
/// runs it and requires that ties were met there (row PERF-shrink-tie-every-step, from
/// PROOF-shrink-counts-current).
#[test]
fn counts_read_at_a_tie_are_those_of_the_rows_held() {
    let (n, m) = (6, 4);
    let vars = n + 1 + n * m;
    let x = |i: usize, j: usize| n + 1 + i * m + j;
    let row = |a: Vec<(usize, i64)>, k: i64| {
        let a: Vec<Term> = a.into_iter().map(|(v, c)| (v, Int::from(c))).collect();
        (
            Row {
                a: a.into(),
                k: Int::from(k),
            },
            Rel::Ge,
        )
    };
    let mut base = Vec::new();
    for v in 0..vars {
        base.push(row(vec![(v, 1)], 0));
        base.push(row(vec![(v, -1)], 10));
    }
    for i in 0..n {
        let mut a = vec![(i, 1), (i + 1, -1)];
        a.extend((0..m).map(|j| (x(i, j), 1)));
        base.push(row(a.clone(), -1));
        base.push(row(a.iter().map(|&(v, c)| (v, -c)).collect(), 3));
    }
    let keys = vec![0; vars];
    let before = TIES_CHECKED.with(std::cell::Cell::get);
    let answer = search(vars, &base, &keys, false, &|i| format!("v{i}"));
    let ties = TIES_CHECKED.with(std::cell::Cell::get) - before;
    assert!(matches!(answer, Ok(Some(_))), "{answer:?}");
    eprintln!("{ties} ties met over {vars} variables");
    assert!(ties >= n, "{ties} ties met");
}

/// Random small systems: 7 variables in `[-3, 3]` and 8 rows of two to four terms, coefficients
/// in `{-2, -1, 1, 2}`. Rows over subsets of other rows' variables are common here, the case
/// [`System::touch`] marks; each run checks the counts at every read ([`System::stale`]).
#[test]
fn counts_read_are_those_of_the_rows_held_on_random_systems() {
    let mut rng = crate::seed::Rng::new(0x2545_f491_4f6c_dd1d);
    let vars = 7;
    let before = TIES_CHECKED.with(std::cell::Cell::get);
    for _ in 0..2000 {
        let mut base: Vec<(Row, Rel)> = Vec::new();
        for v in 0..vars {
            for c in [1, -1] {
                let a: Vec<Term> = vec![(v, Int::from(c))];
                base.push((
                    Row {
                        a: a.into(),
                        k: Int::from(3),
                    },
                    Rel::Ge,
                ));
            }
        }
        for _ in 0..8 {
            let len = 2 + rng.below(3);
            let mut vs: Vec<usize> = Vec::new();
            while vs.len() < len {
                let v = rng.below(vars);
                if !vs.contains(&v) {
                    vs.push(v);
                }
            }
            vs.sort_unstable();
            let a: Vec<Term> = (vs.iter())
                .map(|&v| (v, Int::from(rng.pick(&[-2_i64, -1, 1, 2]))))
                .collect();
            let k = Int::from(rng.int(-2, 2));
            base.push((Row { a: a.into(), k }, Rel::Ge));
        }
        let _ = search(vars, &base, &vec![0; vars], false, &|i| format!("v{i}"));
    }
    let ties = TIES_CHECKED.with(std::cell::Cell::get) - before;
    eprintln!("{ties} ties met");
    assert!(ties > 0);
}
