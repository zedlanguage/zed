//! Emptiness of recursive types (DESIGN.md sec:type_language, cross-review X14): a cycle of
//! definitions through a tuple component is empty, since a value is finite, and a cycle through
//! a morphism's value type is inhabited, since a morphism need not be built from a value of its
//! value type before it is applied: `type S = (int) -> S` holds `fn s(x) = s`.

use super::bes_families::{FAMILIES, G, K, family, reference};
use std::collections::BTreeMap;

use zed_kernel::types::bes::{Answer, decide};
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

pub(super) fn group(bodies: Vec<Expr>) -> Result<Vec<Type>, String> {
    let defs = bodies
        .into_iter()
        .enumerate()
        .map(|(i, body)| Def {
            name: format!("N{i}"),
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs)
        .map(|g| g.instance(vec![]))
        .map_err(|e| e.message)
}

#[test]
fn a_cycle_through_a_value_type_is_inhabited_and_one_through_a_tuple_is_empty() {
    Type::forget_emptiness();
    let int = || Expr::Type(Type::int());
    // type S = (int) -> S
    let s = group(vec![Expr::exact(int(), r(0))]).unwrap();
    assert!(!s[0].is_empty(), "S = (int) -> S holds fn s(x) = s");
    // type W = (W) -> int
    let w = group(vec![Expr::exact(r(0), int())]).unwrap();
    assert!(!w[0].is_empty(), "W = (W) -> int");
    // type E = (E, int)
    let e = group(vec![Expr::Tuple(vec![r(0), int()])]).unwrap();
    assert!(e[0].is_empty(), "E = (E, int) has no finite value");
    // type P = (int) -> (P, P): a pair of functions, each again such a pair.
    let p = group(vec![Expr::exact(int(), Expr::Tuple(vec![r(0), r(0)]))]).unwrap();
    assert!(!p[0].is_empty());
    // type Q = (Q, (int) -> Q): the tuple cycle makes it empty.
    let q = group(vec![Expr::Tuple(vec![r(0), Expr::exact(int(), r(0))])]).unwrap();
    assert!(q[0].is_empty());
    // type L = () | (int, L) and type F = (int) -> (F | ()) are inhabited.
    let l = group(vec![Expr::Union(vec![
        Expr::Tuple(vec![]),
        Expr::Tuple(vec![int(), r(0)]),
    ])])
    .unwrap();
    assert!(!l[0].is_empty());
}

/// Each node of a family as a definition: `Or` a union, `And` a tuple, `Mor` the morphism type
/// `(int) -> child`, `Top` `int` and `Bot` `empty`.
pub(super) fn bodies(g: &G) -> Vec<Expr> {
    (0..g.k.len())
        .map(|v| {
            let cs = || g.c[v].iter().map(|&w| r(w as usize)).collect();
            match g.k[v] {
                K::Or => Expr::Union(cs()),
                K::And => Expr::Tuple(cs()),
                K::Mor => Expr::exact(Expr::Type(Type::int()), r(g.c[v][0] as usize)),
                K::Top => Expr::Type(Type::int()),
                K::Bot => Expr::Type(Type::empty()),
            }
        })
        .collect()
}

/// On every family group the definitions admit, emptiness agrees with the classical solver of
/// the Büchi game the group's fixed points describe.
#[test]
fn emptiness_of_family_groups_agrees_with_the_reference() {
    let (mut checked, mut refused) = (0, 0);
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            Type::forget_emptiness();
            let want = reference::answers(&g);
            let decided = decide(&g.bes()).answers;
            for (v, (t, w)) in types.iter().zip(&want).enumerate() {
                match decided[v] {
                    // A member the decider refuses goes to the search (DESIGN.md L1.23), which
                    // may count an empty one as inhabited, never the other way; a verdict the
                    // search gives agrees with the reference, and one it does not is the
                    // group's refusal, which counts as inhabited.
                    Answer::Refused => {
                        assert!(!t.is_empty() || !w, "{name}:{n}: node {v} counted empty");
                        match t.verdict() {
                            Verdict::Refused(Refusal::Group) => {
                                assert!(!t.is_empty(), "{name}:{n}: node {v} refused, empty")
                            }
                            Verdict::Inhabited => assert!(*w, "{name}:{n}: node {v}"),
                            Verdict::Empty => assert!(!w, "{name}:{n}: node {v}"),
                            other => panic!("{name}:{n}: node {v}: {other:?}"),
                        }
                        refused += 1;
                    }
                    Answer::Empty | Answer::Inhabited => {
                        assert_eq!(!t.is_empty(), *w, "{name}:{n}: node {v}")
                    }
                }
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "some family group is admitted");
    eprintln!("family groups checked: {checked}, refused members: {refused}");
}

/// On the same groups, a verdict of `Empty` or `Inhabited` agrees with the reference, every
/// refusal names its cause, and the verdicts read in reverse with nothing kept are the same.
#[test]
fn verdicts_of_family_groups_agree_with_the_reference() {
    let (mut decided, mut refused) = (0, BTreeMap::new());
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            let want = reference::answers(&g);
            Type::forget_emptiness();
            let first: Vec<Verdict> = types.iter().map(Type::verdict).collect();
            Type::forget_emptiness();
            let again: Vec<Verdict> = types.iter().rev().map(Type::verdict).collect();
            assert!(first.iter().eq(again.iter().rev()), "{name}:{n}");
            for (v, (verdict, w)) in first.iter().zip(&want).enumerate() {
                match verdict {
                    Verdict::Empty => assert!(!w, "{name}:{n}: node {v} is inhabited"),
                    Verdict::Inhabited => assert!(*w, "{name}:{n}: node {v} is empty"),
                    Verdict::Refused(why) => {
                        *refused.entry(format!("{why:?}")).or_insert(0) += 1;
                        continue;
                    }
                }
                decided += 1;
            }
        }
    }
    eprintln!("family members decided: {decided}, refused: {refused:?}");
    assert!(decided > 0);
}

/// `bodies` with node `v` placed at `place[v]`, its references moved with it.
fn renumbered(g: &G, place: &[usize]) -> Vec<Expr> {
    let mut out: Vec<Option<Expr>> = vec![None; place.len()];
    for v in 0..g.k.len() {
        let cs = || g.c[v].iter().map(|&w| r(place[w as usize])).collect();
        out[place[v]] = Some(match g.k[v] {
            K::Or => Expr::Union(cs()),
            K::And => Expr::Tuple(cs()),
            K::Mor => Expr::exact(Expr::Type(Type::int()), r(place[g.c[v][0] as usize])),
            K::Top => Expr::Type(Type::int()),
            K::Bot => Expr::Type(Type::empty()),
        });
    }
    out.into_iter()
        .map(|e| e.expect("`place` is a permutation"))
        .collect()
}

/// No answer depends on the questions asked before it or on the numbering of the definitions
/// (SYNTHESIS Q2/Q3 item 4): each member of every admitted family group is decided cold, in a
/// batch, in a reversed batch, and in a copy whose definitions are numbered in reverse, and
/// the four answers agree.
#[test]
fn answers_do_not_depend_on_order_or_numbering() {
    let mut checked = 0;
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            let cold: Vec<bool> = types
                .iter()
                .map(|t| {
                    Type::forget_emptiness();
                    t.is_empty()
                })
                .collect();
            Type::forget_emptiness();
            let batch: Vec<bool> = types.iter().map(Type::is_empty).collect();
            Type::forget_emptiness();
            let mut reversed: Vec<bool> = types.iter().rev().map(Type::is_empty).collect();
            reversed.reverse();
            let k = g.k.len();
            let place: Vec<usize> = (0..k).map(|v| k - 1 - v).collect();
            let copy = group(renumbered(&g, &place)).expect("a renumbered group is admitted");
            Type::forget_emptiness();
            let renamed: Vec<bool> = (0..k).map(|v| copy[place[v]].is_empty()).collect();
            assert_eq!(cold, batch, "{name}:{n}: cold, then in a batch");
            assert_eq!(cold, reversed, "{name}:{n}: cold, then reversed");
            assert_eq!(cold, renamed, "{name}:{n}: cold, then renumbered");
            checked += 1;
        }
    }
    assert!(checked > 0, "some family group is admitted");
}

/// `bodies` named as [`group`] names them, node `v` placed at `place[v]` and keeping its name.
fn renumbered_named(g: &G, place: &[usize]) -> Vec<Type> {
    let mut names = vec![String::new(); place.len()];
    for (v, &at) in place.iter().enumerate() {
        names[at] = format!("N{v}");
    }
    let defs = names
        .into_iter()
        .zip(renumbered(g, place))
        .map(|(name, body)| Def {
            name,
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs)
        .expect("a renumbered group is admitted")
        .instance(vec![])
}

/// A copy of a group with its definitions listed in another order is the group, member for
/// member (item REC-canon), and gets the same verdicts, refusals with the same causes. Across
/// all the family groups, members that are one type get one answer from the reference, which
/// reads no node, and one verdict.
#[test]
fn reordered_copies_of_family_groups_are_the_groups() {
    let (mut checked, mut refused) = (0, BTreeMap::new());
    let mut by_type: BTreeMap<Type, Vec<(String, bool, Verdict)>> = BTreeMap::new();
    for name in FAMILIES {
        for n in [2, 3, 5] {
            let g = family(name, n);
            let Ok(types) = group(bodies(&g)) else {
                continue;
            };
            let k = g.k.len();
            let place: Vec<usize> = (0..k).map(|v| k - 1 - v).collect();
            let copy = renumbered_named(&g, &place);
            for v in 0..k {
                assert!(copy[place[v]] == types[v], "{name}:{n}: node {v}");
            }
            let want = reference::answers(&g);
            Type::forget_emptiness();
            let first: Vec<Verdict> = types.iter().map(Type::verdict).collect();
            Type::forget_emptiness();
            let again: Vec<Verdict> = (0..k).map(|v| copy[place[v]].verdict()).collect();
            assert_eq!(first, again, "{name}:{n}");
            for (v, t) in types.into_iter().enumerate() {
                if let Verdict::Refused(why) = &first[v] {
                    *refused.entry(format!("{why:?}")).or_insert(0) += 1;
                }
                let at = format!("{name}:{n}: node {v}");
                by_type.entry(t).or_default().push((at, want[v], first[v]));
            }
            checked += 1;
        }
    }
    let mut merged = 0;
    for same in by_type.values() {
        for (at, w, verdict) in &same[1..] {
            assert_eq!(
                (w, verdict),
                (&same[0].1, &same[0].2),
                "{at} and {}",
                same[0].0
            );
            merged += 1;
        }
    }
    eprintln!("family groups checked: {checked}, members merged: {merged}, refused: {refused:?}");
    assert!(checked > 0, "some family group is admitted");
}

/// A group of one member with its parameter renamed is the group; two groups that differ at
/// one member keep that member, and every member reaching it, apart; a member and the member of
/// another group that unfolds alike hold the same values, and members that differ in one element
/// type do not.
#[test]
fn the_canonical_form_keeps_apart_what_differs() {
    let ring = |a: &str| {
        let body = Expr::Union(vec![nil(), cons(Type::int(), r(0))]);
        single(a, body)
    };
    assert!(ring("L") == ring("L"));
    assert!(ring("L") != ring("M") && ring("L").subtype(&ring("M")));
    assert!(ring("L") != single("L", Expr::Union(vec![nil(), cons(Type::string(), r(0))])));
    let three = |tail: &str| {
        group_named(vec![
            (
                "A",
                Expr::Union(vec![nil(), Expr::Atom("a".into(), vec![r(1)])]),
            ),
            ("B", Expr::Atom(tail.into(), vec![r(0)])),
            ("C", Expr::Atom("c".into(), vec![r(2)])),
        ])
    };
    let (x, y) = (three("b"), three("d"));
    assert!(
        x[0] != y[0] && x[1] != y[1],
        "the differing member and the one reaching it"
    );
    assert!(x[0] == three("b")[0] && x[1] == three("b")[1]);
    // A cycle of two members that unfold alike, and a cycle of one: they hold the same values.
    // Whether the two members share one representation is not checked: only their meaning is.
    let twins = group_named(vec![
        ("L", Expr::Union(vec![nil(), cons(Type::int(), r(1))])),
        ("M", Expr::Union(vec![nil(), cons(Type::int(), r(0))])),
    ]);
    assert!(twins[0].subtype(&ring("L")) && ring("L").subtype(&twins[0]));
    assert!(twins[1].subtype(&ring("M")) && ring("M").subtype(&twins[1]));
    assert!(twins[0].subtype(&twins[1]) && twins[1].subtype(&twins[0]));
    // The contrast: a cycle of two members that differ at one element type. The lists [1] and
    // ["a"] each lie in one member only, so neither member is a subtype of the other; [1, "a"]
    // lies in `L` and not in the cycle of one, and [1, 2] in the cycle of one and not in `L`.
    let apart = group_named(vec![
        ("L", Expr::Union(vec![nil(), cons(Type::int(), r(1))])),
        ("M", Expr::Union(vec![nil(), cons(Type::string(), r(0))])),
    ]);
    assert!(!apart[0].subtype(&apart[1]) && !apart[1].subtype(&apart[0]));
    assert!(!apart[0].subtype(&ring("L")) && !ring("L").subtype(&apart[0]));
}

static RINGS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// A ring of `n` definitions, the first of which ends the list: `n` classes, the most the
/// refinement can split a group into, each split by one round from the end.
fn marked_ring(n: usize) -> Group {
    let ring = RINGS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let defs = (0..n)
        .map(|i| {
            let link = cons(Type::int(), r((i + 1) % n));
            Def {
                name: format!("R{ring}_{i}"),
                params: vec![],
                body: match i {
                    0 => Expr::Union(vec![nil(), link]),
                    _ => link,
                },
            }
        })
        .collect();
    Group::new(defs).unwrap()
}

/// A small instance of `bench::the_canonical_form_of_a_component_scales`: a ring of one to
/// eight definitions, the first of which ends the list, is that many classes. Its instance has
/// one type for each member, no two equal, and its first member holds the lists whose length is
/// a multiple of the ring's size, as `residue` writes them in one definition. No other test
/// makes a marked ring (TEST-bench-move-l0123, author P169).
#[test]
fn the_canonical_form_of_a_marked_ring_keeps_each_member_apart() {
    for m in 1..=8 {
        Type::forget_emptiness();
        let types = marked_ring(m).instance(vec![]);
        assert_eq!(types.len(), m);
        for i in 1..m {
            assert!(types[0] != types[i], "R0 and R{i} of {m}");
        }
        let lists = residue(m, 0);
        assert!(types[0].subtype(&lists) && lists.subtype(&types[0]), "{m}");
    }
}

/// A ring of `n` definitions `N{i} = (int) -> (N{i+1}, int)`, each a morphism type into a pair
/// of the next and `int`.
fn pair_ring(n: usize) -> Group {
    let defs = (0..n)
        .map(|i| Def {
            name: format!("N{i}"),
            params: vec![],
            body: Expr::exact(
                Expr::Type(Type::int()),
                Expr::Tuple(vec![r((i + 1) % n), Expr::Type(Type::int())]),
            ),
        })
        .collect();
    Group::new(defs).unwrap()
}

/// A small instance of `bench::deciding_a_group_scales`: a ring of one to eight definitions,
/// each a morphism type into a pair of the next and `int`, is inhabited in every member, by a
/// function returning a pair that holds the next. The only other cycle through a morphism into
/// a tuple has one member (TEST-bench-move-l0123, author P169).
#[test]
fn a_ring_of_morphisms_into_pairs_is_inhabited() {
    for n in 1..=8 {
        Type::forget_emptiness();
        let types = pair_ring(n).instance(vec![]);
        for (i, t) in types.iter().enumerate() {
            assert!(!t.is_empty(), "N{i} of {n}");
            assert_eq!(t.verdict(), Verdict::Inhabited, "N{i} of {n}");
        }
    }
}

/// The one type of a group of one definition, `name = body`.
fn single(name: &str, body: Expr) -> Type {
    group_named(vec![(name, body)]).remove(0)
}

fn group_named(defs: Vec<(&str, Expr)>) -> Vec<Type> {
    let defs = defs
        .into_iter()
        .map(|(name, body)| Def {
            name: name.into(),
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs)
        .expect("the corpus's definitions are admitted")
        .instance(vec![])
}

fn cons(head: Type, tail: Expr) -> Expr {
    Expr::Atom("cons".into(), vec![Expr::Type(head), tail])
}

fn nil() -> Expr {
    Expr::Type(Type::atom("nil"))
}

fn int_lit(i: i64) -> Type {
    Type::lit(&zed_kernel::Value::Int(i)).expect("an integer has a literal type")
}

/// Lists of ints whose length is `offset` modulo `period`.
fn residue(period: usize, offset: usize) -> Type {
    let body = (0..period).rev().fold(r(0), |body, k| {
        let link = cons(Type::int(), body);
        if k == offset {
            Expr::Union(vec![nil(), link])
        } else {
            link
        }
    });
    single("L", body)
}

/// Lists of ints whose `n`th item from the end is 1.
fn nth_from_end(n: usize) -> Type {
    let mut defs = vec![("R0".to_string(), nil())];
    for k in 1..n {
        defs.push((format!("R{k}"), cons(Type::int(), r(k - 1))));
    }
    defs.push((
        "G".to_string(),
        Expr::Union(vec![cons(Type::int(), r(n)), cons(int_lit(1), r(n - 1))]),
    ));
    let defs = defs.iter().map(|(n, b)| (n.as_str(), b.clone())).collect();
    group_named(defs).pop().expect("G is the last definition")
}

/// `n` types: the seeds below, then each a union, meet, difference, pair or morphism type of
/// two earlier ones, picked by `rng`.
fn corpus(rng: &mut Rng, n: usize) -> Vec<Type> {
    let int = || Expr::Type(Type::int());
    let mut ts = vec![
        Type::int(),
        int_lit(0),
        int_lit(1),
        Type::atom("nil"),
        residue(1, 0),
        residue(2, 0),
        residue(3, 0),
        nth_from_end(1),
        nth_from_end(2),
        nth_from_end(3),
        residue(2, 1),
        residue(3, 2),
        // `S = (int) -> S` and `W = (W) -> int`: cycles through a morphism, inhabited.
        single("S", Expr::exact(int(), r(0))),
        single("W", Expr::exact(r(0), int())),
    ];
    while ts.len() < n {
        let (a, b) = (
            ts[rng.below(ts.len())].clone(),
            ts[rng.below(ts.len())].clone(),
        );
        ts.push(match rng.below(5) {
            0 => &a | &b,
            1 => &a & &b,
            2 => &a - &b,
            3 => Type::tuple(vec![a, b]),
            _ => Type::morphism(a.clone(), a, b),
        });
    }
    ts
}

/// The queries one run of `subtype_answers_do_not_depend_on_the_queries_before_them` asks.
const QUERIES: usize = 200;

/// No subtype answer depends on the questions asked before it (DESIGN.md sec:plan, standing
/// rule of deterministic checking): on a corpus of 150 types with recursive lists, morphism
/// cycles and Boolean combinations, `QUERIES` queries `a <: b` are answered one at a time with
/// the kept results dropped before each, in one batch keeping them, and in the batch reversed,
/// and the three agree. A result kept that rested on an assumption, or that was read before the
/// search finished, makes a later answer differ (COMPLEXITY.md K51).
///
/// It ran 1500 queries on each of six corpora of fixed seeds 1 to 6, in eleven tests (0.5 to
/// 1.8 s each alone, the slower seeds split into parts by query index); now it runs `QUERIES`
/// queries on one corpus, the corpus and the queries drawn from a new seed each run, printed
/// (TEST-bench-move-l0123, author P169: random tests run fewer cases).
/// Its time depends on the corpus: over 26 runs of 300 queries the median was 0.07 s and the
/// slowest 1.09 s, so a run asks 200.
#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them() {
    // On the stack of its test thread, 2 MiB by default.
    let (_, seed) = Rng::fresh("subtype answers alone and in batches");
    order_free(seed);
}

/// The query whose answer depended on the queries before it at this seed (FAIL row
/// FAIL-judgments-query-order-seed): query 44, `ts[142] <: ts[72]`, was false alone and in the
/// batch, and true reversed, as it was after query 182 alone. The difference of the two holds
/// a pair whose first component is a pair with a `1 -> empty` in it, so the pair is empty; the
/// search of the difference met a fork before it reached that component and stopped, and the
/// search that sets forks aside (`empty_past_forks`), which proves the pair empty, ran only
/// when the fork was met in a component with others after it. Query 182 kept the pair empty,
/// and query 44 then read that without meeting the fork.
#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_at_a_fork_without_later_components() {
    let mut rng = Rng::new(10511391382961984112);
    let ts = corpus(&mut rng, 150);
    let (a, b) = (&ts[142], &ts[72]);
    Type::forget_emptiness();
    assert!(a.subtype(b), "{a} <: {b}");
    Type::forget_emptiness();
    assert_eq!((a - b).verdict(), Verdict::Empty, "{a} - {b}");
    order_free(10511391382961984112);
}

/// Asks `QUERIES` queries `a <: b` on the corpus of `seed` one at a time with the kept results
/// dropped before each, in one batch keeping them, and in the batch reversed, and asserts the
/// three agree.
fn order_free(seed: u64) {
    let mut rng = Rng::new(seed);
    let ts = corpus(&mut rng, 150);
    let qs: Vec<(usize, usize)> = (0..QUERIES)
        .map(|_| (rng.below(ts.len()), rng.below(ts.len())))
        .collect();
    let ask = |&(a, b): &(usize, usize)| ts[a].subtype(&ts[b]);
    let alone: Vec<bool> = qs
        .iter()
        .map(|q| {
            Type::forget_emptiness();
            ask(q)
        })
        .collect();
    Type::forget_emptiness();
    let batch: Vec<bool> = qs.iter().map(ask).collect();
    Type::forget_emptiness();
    let mut back: Vec<bool> = qs.iter().rev().map(ask).collect();
    back.reverse();
    let held = batch.iter().filter(|&&b| b).count();
    eprintln!("ZED_TEST_SEED={seed}: {held} of {} hold", qs.len());
    assert!(
        0 < held && held < qs.len(),
        "ZED_TEST_SEED={seed}: {held} hold"
    );
    for (i, &(a, b)) in qs.iter().enumerate() {
        assert!(
            alone[i] == batch[i] && alone[i] == back[i],
            "ZED_TEST_SEED={seed}, query {i}: {} <: {}: alone {}, in the batch {}, reversed {}",
            ts[a],
            ts[b],
            alone[i],
            batch[i],
            back[i]
        );
    }
}

/// A morphism cycle is inhabited, `W = (W) -> int` by a closure, except when what the cycle
/// returns is empty for another reason: in `V = int -> (V, bool -> empty)` the pair holds a
/// `bool -> empty`, which has no value, so the pair and `V` are empty, and `V -> empty` then
/// has a value, a closure that is never called. A decider that took every morphism cycle as
/// inhabited would show a closure for `V` and call `V -> empty` empty.
#[test]
fn a_morphism_cycle_through_an_empty_part_is_empty() {
    Type::forget_emptiness();
    let w = single("W", Expr::exact(r(0), Expr::Type(Type::int())));
    assert!(!w.is_empty(), "W = (W) -> int is inhabited");
    assert_eq!(w.verdict(), Verdict::Inhabited);
    assert!(w.subtype(&w), "W <: W");

    Type::forget_emptiness();
    let bool_to_empty = Type::morphism(Type::bool(), Type::bool(), Type::empty());
    assert!(bool_to_empty.is_empty(), "bool -> empty");
    let v = single(
        "V",
        Expr::exact(
            Expr::Type(Type::int()),
            Expr::Tuple(vec![r(0), Expr::Type(bool_to_empty.clone())]),
        ),
    );
    let n = Type::morphism(v.clone(), v.clone(), Type::empty());
    assert!(v.is_empty(), "V = int -> (V, bool -> empty) is empty");
    assert_eq!(v.verdict(), Verdict::Empty);
    assert!(!n.is_empty(), "N = V -> empty is inhabited");
    // The value shown is a closure that is never called: its key type `V` is empty, as its
    // recursive group decides, so it needs no return value, and `empty` having none does not
    // matter.
    assert_eq!(
        n.verdict(),
        Verdict::Inhabited,
        "N = V -> empty is inhabited"
    );
    // A key type that is not recursive, which only a search proves empty, gets the same closure:
    // the search that builds it proves its key type empty (plan item EMPTY-key-search).
    let m = Type::morphism(bool_to_empty.clone(), bool_to_empty, Type::empty());
    assert!(!m.is_empty(), "(bool -> empty) -> empty is inhabited");
    assert_eq!(m.verdict(), Verdict::Inhabited);
    // The same answers with the kept results of the other type in place.
    assert!(v.is_empty() && !n.is_empty() && !w.is_empty());
}

/// `bool -> empty` under `depth` more morphism types, each the key type of the next with the
/// value type `empty`: empty at an even depth, inhabited at an odd one, by a closure that is
/// never called since its key type is empty.
fn key_nest(depth: usize) -> Type {
    let mut t = Type::morphism(Type::bool(), Type::bool(), Type::empty());
    for _ in 0..depth {
        t = Type::morphism(t.clone(), t, Type::empty());
    }
    t
}

#[test]
fn a_key_type_only_a_search_proves_empty_gives_a_closure() {
    for depth in 0..8 {
        Type::forget_emptiness();
        let t = key_nest(depth);
        let (verdict, empty) = if depth % 2 == 0 {
            (Verdict::Empty, true)
        } else {
            (Verdict::Inhabited, false)
        };
        assert_eq!(t.verdict(), verdict, "depth {depth}");
        Type::forget_emptiness();
        assert_eq!(t.is_empty(), empty, "depth {depth}");
    }
}

mod bench;

// FAIL-types-meet-function-union: found by the kernel printer's round trip (l01_29 parens.rs).
/// A meet one of whose sides is a union holding a function keeps both sides: it is the union
/// of the meets of the other side with each member.
#[test]
fn a_meet_with_a_union_of_functions_keeps_both_sides() {
    use zedc::check::read::parse_type;
    let both = |a: &str, b: &str| {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        (x.subtype(&y), y.subtype(&x))
    };
    assert_eq!(
        both(
            "(rat -> #b) & ((bool -> ()) | String)",
            "(rat -> #b) & (bool -> ())"
        ),
        (true, true)
    );
    assert_eq!(
        both(
            "((f64 ->? int) | (int ->? bool)) & (String ->? #b)",
            "(String ->? #b) & ((f64 ->? int) | (int ->? bool))"
        ),
        (true, true)
    );
    assert_eq!(
        both(
            "((f64 ->? int) & (String ->? #b)) | ((int ->? bool) & (String ->? #b))",
            "((f64 ->? int) | (int ->? bool)) & (String ->? #b)"
        ),
        (true, true)
    );
    // Control (passes today): a meet of two arrows, in either order.
    assert_eq!(
        both("(rat -> #b) & (bool -> ())", "(bool -> ()) & (rat -> #b)"),
        (true, true)
    );
}

// FAIL-types-tuple-subtype: found by the kernel printer's round trip (l01_29 parens.rs).
/// Two tuple types equal part by part, or two unions of the same tuples in another order, are
/// each a subtype of the other.
#[test]
fn tuples_equal_part_by_part_are_subtypes_both_ways() {
    use zedc::check::read::parse_type;
    let both = |a: &str, b: &str| {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        (x.subtype(&y), y.subtype(&x))
    };
    assert_eq!(
        both(
            "((_ -> int) & (_ -> int | #a), (_ -> int, int))",
            "(_ -> int, (_ -> int, int))"
        ),
        (true, true)
    );
    assert_eq!(
        both(
            "(#a -> f64,) | (_,) | (String,)",
            "(String,) | (_,) | (#a -> f64,)"
        ),
        (true, true)
    );
    assert_eq!(
        both(
            "(_ .. (_ | rat) -> String, (rat .. (rat | _) -> bool, int))",
            "(_ -> String, (rat .. _ -> bool, int))"
        ),
        (true, true)
    );
    // A function equal to one of the other side at its place, and fitting another there, with
    // one function on one side of that place.
    let f = "(_ -> int) & (_ -> int | #a)";
    let sub = |a: &str, b: &str| parse_type(a).unwrap().subtype(&parse_type(b).unwrap());
    assert!(sub(
        &format!("({f}, 1)"),
        &format!("(_ -> int, 1) | ({f}, 2)")
    ));
    assert!(sub(
        &format!("({f}, 1) | ({f}, 2)"),
        &format!("(_ -> int, 1) | ({f}, 2)")
    ));
    assert!(sub("(_ -> int, 1)", &format!("({f}, 1) | (_ -> int, 2)")));
    // Controls (passed before the fix): the parts alone, and the same tuple without the nested
    // pair.
    assert_eq!(
        both("(_ -> int) & (_ -> int | #a)", "_ -> int"),
        (true, true)
    );
    assert_eq!(
        both(
            "((_ -> int) & (_ -> int | #a), _ -> int)",
            "(_ -> int, _ -> int)"
        ),
        (true, true)
    );
    assert_eq!(
        both("(#a -> f64,) | (_,) | (String,)", "(_,)"),
        (true, true)
    );
    assert_eq!(
        both("(String,) | (_,) | (#a -> f64,)", "(_,)"),
        (true, true)
    );
}

/// Where two or more functions of each side meet at one place, one equal to one of the other
/// side's, that one is compared with no other function there, and a comparison that fails
/// there is refused, not answered no (COMPLEXITY.md F124).
#[test]
fn functions_equal_on_both_sides_at_one_place_are_refused_where_unpaired() {
    use zedc::check::read::parse_type;
    let f = "(_ -> int) & (_ -> int | #a)";
    let a = parse_type(&format!("({f}, 1) | (String -> String, 2)")).unwrap();
    let b = parse_type(&format!("(_ -> int, 1) | ({f}, 2) | (String -> String, 3)")).unwrap();
    assert!(!a.subtype(&b));
    let why = a.refused(&b);
    assert!(
        why.contains("the checker does not try every way of pairing them"),
        "{why}"
    );
    // The same with one function at the place on the side compared is decided.
    let one = parse_type(&format!("({f}, 1)")).unwrap();
    assert!(one.subtype(&b));
}

/// Where both sides have two or more functions at one place, not all equal, the comparison is
/// refused only when some pairing of those functions could make it true: when even every
/// function of the type expected fitting every function of the side compared leaves a value
/// out, it is decided false, with no clause (FAIL-types-loose-over-refusal). Where a pairing
/// does make it true, it is still refused (COMPLEXITY.md F124).
#[test]
fn functions_at_one_place_are_refused_only_where_a_pairing_could_make_it_true() {
    use zedc::check::read::parse_type;
    let pairing = "the checker does not try every way of pairing them";
    let (f, g, h) = (
        "(int -> int)",
        "(int -> int | #a)",
        "((int | String) -> int)",
    );
    let s = "(String -> String)";
    // (side compared, type expected, true, refused when false)
    let cases = [
        // Two functions a side, one equal: a `9` no tuple expected holds.
        (
            format!("({f}, 1) | ({h}, 9)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            false,
            false,
        ),
        // Two a side, both equal: a `9`.
        (
            format!("({f}, 9) | ({h}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            false,
            false,
        ),
        // Three a side, with one unlike: a `"x"`.
        (
            format!("({f}, 1) | ({h}, 2) | ({s}, \"x\")"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3) | ({s}, 4)"),
            false,
            false,
        ),
        // Unlike on both sides (the class `Forms::tied` names): a `true`.
        (
            "((int | String) -> int, 1) | ((int | rat) -> int, true)".to_string(),
            "((int) -> int, int) | ((String) -> int, int)".to_string(),
            false,
            false,
        ),
        // `f` fits `g` and `h` fits `f`, so `(f, 1)` is in `(g, 1)` and `(h, 2)` in `(f, 2)`:
        // true, but finding it compares functions the checker does not pair; refused.
        (
            format!("({f}, 1) | ({h}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            false,
            true,
        ),
        // Three a side, the same way.
        (
            format!("({f}, 1) | ({h}, 2) | ({s}, 4)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3) | ({s}, 4)"),
            false,
            true,
        ),
        // `s` fits no function at `2`: false, and some pairing could have held, so refused.
        (
            format!("({f}, 1) | ({s}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({s}, 3)"),
            false,
            true,
        ),
        // Every function equal to one at its place is matched by equality: true.
        (
            format!("({f}, 2) | ({h}, 3)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            true,
            false,
        ),
    ];
    for (a, b, holds, refused) in &cases {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        assert_eq!(x.subtype(&y), *holds, "{a} <: {b}");
        if !holds {
            let why = x.refused(&y);
            assert_eq!(why.contains(pairing), *refused, "{a} <: {b}: {why:?}");
        }
    }
}

/// Where the right side's functions at one place are all equal to functions of the left side,
/// with two or more on each side, a subtype that holds through another pairing is answered
/// yes, or refused, never a definite no.
#[test]
fn equal_functions_on_the_right_all_held_on_the_left_are_no_definite_no() {
    use zedc::check::read::parse_type;
    let f = "(int | #z) -> int";
    let h = "(int) -> int | #z";
    assert!(parse_type(f).unwrap().subtype(&parse_type(h).unwrap()));
    let a = parse_type(&format!("({f}, #a) | ({h}, #b)")).unwrap();
    let b = parse_type(&format!("({h}, #a) | ({f}, #b) | ({h}, #b)")).unwrap();
    let why = a.refused(&b);
    assert!(
        a.subtype(&b) || why.contains("the checker does not try every way of pairing them"),
        "a definite no: {why:?}"
    );
}

/// Random unions of tuples that hold functions, compared with a slow reference that pairs every
/// function with every other: a left tuple is held when a right tuple of the same length holds
/// each of its components, a tag equal and a function fitting (a function of the left side is
/// one value to the comparison, so one right tuple must hold it all). Each subtype found must
/// hold by the reference, and each false found with no refusal must be false by the reference:
/// a refusal claims nothing. Before (FAIL-types-equal-functions-subset-no) the checker answered
/// a definite no where the right side's functions at a place were all among the left side's.
#[test]
fn random_unions_of_tuples_with_functions_agree_with_pairing_every_function() {
    use zedc::check::read::parse_type;
    // Fits, by `subtype` on one function each side: F <: G <: H, F <: K <: H, S alone.
    let pool = [
        "(int | #z) -> int",
        "(int) -> int",
        "(int) -> int | #z",
        "(int | #z) -> int | #z",
        "(String) -> String",
    ];
    let fits: Vec<Vec<bool>> = (pool.iter())
        .map(|f| {
            let f = parse_type(f).unwrap();
            (pool.iter())
                .map(|g| f.subtype(&parse_type(g).unwrap()))
                .collect()
        })
        .collect();
    assert!(fits[0][2] && !fits[2][0] && !fits[4][0] && !fits[0][4]);
    // A tuple: its functions, by number in `pool`, and its tag.
    type Row = (Vec<usize>, usize);
    let (mut rng, seed) = Rng::fresh("unions of tuples with functions");
    let draw = |rng: &mut Rng| -> Vec<Row> {
        (0..1 + rng.below(5))
            .map(|_| {
                let width = 1 + rng.below(2);
                (
                    (0..width).map(|_| rng.below(pool.len())).collect(),
                    rng.below(3),
                )
            })
            .collect()
    };
    let text = |rows: &[Row]| {
        (rows.iter())
            .map(|(fs, tag)| {
                let fs: Vec<&str> = fs.iter().map(|&i| pool[i]).collect();
                format!("({}, #{})", fs.join(", "), ["a", "b", "c"][*tag])
            })
            .collect::<Vec<_>>()
            .join(" | ")
    };
    let (mut yes, mut no, mut refused) = (0, 0, 0);
    for _ in 0..3_000 {
        let (a, mut b) = (draw(&mut rng), draw(&mut rng));
        // About half the left tuples get a right tuple that holds them, each function replaced by
        // one it fits, at a random place, so that many subtypes hold.
        for (fs, tag) in &a {
            if rng.below(2) == 0 {
                let up = |f: usize, rng: &mut Rng| {
                    let above: Vec<usize> = (0..pool.len()).filter(|&g| fits[f][g]).collect();
                    above[rng.below(above.len())]
                };
                let gs = fs.iter().map(|&f| up(f, &mut rng)).collect();
                let at = rng.below(b.len() + 1);
                b.insert(at, (gs, *tag));
            }
        }
        let expected = a.iter().all(|(fs, tag)| {
            b.iter().any(|(gs, t)| {
                t == tag && gs.len() == fs.len() && fs.iter().zip(gs).all(|(&f, &g)| fits[f][g])
            })
        });
        let (sa, sb) = (text(&a), text(&b));
        let (ta, tb) = (parse_type(&sa).unwrap(), parse_type(&sb).unwrap());
        let label = format!("ZED_TEST_SEED={seed}: {sa} <: {sb}");
        if ta.subtype(&tb) {
            assert!(expected, "{label}: a subtype found where none holds");
            yes += 1;
        } else if ta.refused(&tb).is_empty() {
            assert!(!expected, "{label}: a definite no where the subtype holds");
            no += 1;
        } else {
            refused += 1;
        }
    }
    eprintln!("ZED_TEST_SEED={seed}: {yes} yes, {no} no, {refused} refused");
}
