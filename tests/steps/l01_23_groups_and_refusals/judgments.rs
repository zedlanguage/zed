//! Emptiness of recursive types (DESIGN.md sec:type_language, cross-review X14): a cycle of
//! definitions through a tuple component is empty, since a value is finite, and a cycle through
//! a morphism's value type is inhabited, since a morphism need not be built from a value of its
//! value type before it is applied: `type S = (int) -> S` holds `fn s(x) = s`.

use super::bes_families::{FAMILIES, G, K, family, reference};
use std::collections::BTreeMap;

use zed_kernel::Value;
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
    // Fixed seed, so an exact count. It was 37 until PERF-set-digest-shape-free made the digests
    // of sets and lists functions of their contents: the new digests put the operands of
    // `ts[137]` (a morphism from a `#cons` of a meet) in another order, and the search, which
    // stops at the first fork in operand order (`verdict_alone`, `empty_past_forks`), now proves
    // it empty where it was refused at a fork, so queries 52 (`ts[137] <: ts[142]`) and 78
    // (`ts[137] <: ts[33]`) hold. The count is the same under every draw of the treaps'
    // priorities (`ZED_TREAP_SEED` 0, 1 and 2).
    assert_eq!(order_free(10511391382961984112), 39);
}

/// The two queries of the fixed seed above that PERF-set-digest-shape-free turned from refused
/// to holding, 52 (`ts[137] <: ts[142]`) and 78 (`ts[137] <: ts[33]`), checked without the
/// emptiness search (plan row CHECK-judgments-ts137-empty). The corpus draws
/// `ts[137] = morphism(ts[47], ts[47], ts[27])`, an exact morphism, with
/// `ts[27] = ts[10] & ts[18]` and `ts[18] = ts[11] & ts[1]`: `ts[1]` is the integer `0` and
/// `ts[11]` (`residue(3, 2)`) holds only `#nil` and `#cons` atoms, so their meet holds no value
/// and the value type is empty. `ts[47] = ts[44] & ts[33]` with `ts[44] = ts[8] - ts[36]`,
/// `ts[36] = ts[7] - ts[1]`, `ts[33] = ts[29] - ts[26]` and `ts[29] = ts[11] | ts[10]`; the
/// list `[1, 0]` is in it: its second item from the end is 1 (`nth_from_end(2)`), its last is
/// not (`nth_from_end(1)`), its length 2 is 2 modulo 3 (`residue(3, 2)`), and it is no tuple
/// (`ts[26]` is a pair). A morphism type whose guarantee holds a key and whose value type is
/// empty holds no morphism, as no value can be given at that key (`types/empty.rs`, module
/// documentation), so `ts[137]` is empty and is a subtype of every type: both queries hold.
/// The membership test `Type::contains` evaluates the one value, and the value type's
/// emptiness is its form (`Type::lists_nothing`), neither of them the search.
#[test]
fn the_morphism_the_fixed_seed_proves_empty_has_a_key_in_its_guarantee_and_no_value() {
    let mut rng = Rng::new(10511391382961984112);
    let ts = corpus(&mut rng, 150);
    let morphism = Type::morphism(ts[47].clone(), ts[47].clone(), ts[27].clone());
    assert!(ts[137] == morphism, "{} is not {morphism}", ts[137]);
    assert!(ts[18] == &ts[11] & &ts[1] && ts[27] == &ts[10] & &ts[18]);
    assert!(ts[27].lists_nothing(), "{}", ts[27]);
    let list = |xs: &[i64]| {
        (xs.iter().rev()).fold(Value::atom("nil"), |tl, &x| {
            Value::atom_with("cons", vec![Value::Int(x), tl])
        })
    };
    let key = list(&[1, 0]);
    assert!(ts[47].contains(&key), "[1, 0] in {}", ts[47]);
    // The same key read part by part, so a wrong part fails here by name.
    assert!(ts[8].contains(&key) && !ts[36].contains(&key) && ts[44].contains(&key));
    assert!(ts[11].contains(&key) && !ts[26].contains(&key) && ts[33].contains(&key));
    for b in [142, 33] {
        Type::forget_emptiness();
        assert!(ts[137].subtype(&ts[b]), "ts[137] <: ts[{b}]");
    }
    Type::forget_emptiness();
    assert_eq!(ts[137].verdict(), Verdict::Empty);
}

/// Asks `QUERIES` queries `a <: b` on the corpus of `seed` one at a time with the kept results
/// dropped before each, in one batch keeping them, and in the batch reversed, and asserts the
/// three agree; returns how many hold.
fn order_free(seed: u64) -> usize {
    let mut rng = Rng::new(seed);
    let ts = corpus(&mut rng, 150);
    let mut qs: Vec<(usize, usize)> = (0..QUERIES)
        .map(|_| (rng.below(ts.len()), rng.below(ts.len())))
        .collect();
    // Two queries built to give both answers on every run, asked last in the batch and first
    // reversed (PROOF-test-count-thresholds): `ts[1]` is `0` and `ts[0]` is `int`, so
    // `0 <: int` holds, and `int <: 0` does not, as `1` is in `int` and not in `0`.
    qs.extend([(1, 0), (0, 1)]);
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
    assert_eq!(batch[QUERIES..], [true, false], "the built queries");
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
    held
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
/// of the meets of the other side with each member. An intersection with an operand that is
/// no function type is the meet of sets, not an overload (DESIGN.md sec:type_language, point
/// (2) of "Relation to semantic subtyping"), so two exact arrows over different domains meet
/// in nothing, and two partial ones in their shared keys. Until
/// FAIL-types-meet-exact-arrows-differing-domains this test held such a meet equal to the
/// overload of the two, which holds functions of neither side.
#[test]
fn a_meet_with_a_union_of_functions_keeps_both_sides() {
    use zedc::check::read::parse_type;
    let both = |a: &str, b: &str| {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        (x.subtype(&y), y.subtype(&x))
    };
    assert!(
        parse_type("(rat -> #b) & ((bool -> ()) | String)")
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        both(
            "(rat -> #b) & ((rat -> ()) | String)",
            "(rat -> #b) & (rat -> ())"
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
    // The partial arrows share no key, so the meet holds only the map with no key: it is
    // within each side and within the overloads, which hold more.
    let meet = parse_type("((f64 ->? int) | (int ->? bool)) & (String ->? #b)").unwrap();
    for side in [
        "((f64 ->? int) & (String ->? #b)) | ((int ->? bool) & (String ->? #b))",
        "(f64 ->? int) | (int ->? bool)",
        "String ->? #b",
    ] {
        assert!(
            meet.subtype(&parse_type(side).unwrap()),
            "`{meet}` is not within `{side}`"
        );
    }
    // Control (passes today): a meet of two arrows, in either order.
    assert_eq!(
        both("(rat -> #b) & (bool -> ())", "(bool -> ()) & (rat -> #b)"),
        (true, true)
    );
}

/// A union holding `_` (every value) met with `G` is `G` (DESIGN.md sec:type_language, A92):
/// `_ | F` is `_`, and `_ & G` is `G`, on either side of `&` and inside a tuple. Before
/// (FAIL-types-meet-key-arrows-not-within, FAIL-kernel-print-seed-479643653593087009), the
/// meet of `_ | F` with `G` kept `F & G` beside `G`, and where `F` and `G` take the same
/// parameters `F & G` is an overload not within `G`. Each case but the last two is a type the
/// kernel printer's round trip met on a random seed (1730459861738794369, 6234523682986511799,
/// 2245270478369938153, 479643653593087009), with the print it read back as another type.
#[test]
fn a_meet_of_a_union_holding_the_unknown_is_the_other_side() {
    use zedc::check::read::parse_type;
    let within = |a: &str, b: &str| parse_type(a).unwrap().subtype(&parse_type(b).unwrap());
    for (meet, other) in [
        ("(_ | (int -> ())) & (String -> int)", "String -> int"),
        ("(_ | ((()) -> ())) & (String -> int)", "String -> int"),
        (
            "((_) | ((()) -> (()))) & (((String) | (String)) -> (((String), (#b), (String))))",
            "String -> (String, #b, String)",
        ),
        (
            "(((#a) ->? (())) | (_)) & ((rat) ->? (bool))",
            "rat ->? bool",
        ),
        (
            "((_) | ((bool) ->? (bool))) & ((#pair((()), (rat))) -> (#box((bool))))",
            "#pair((), rat) -> #box(bool)",
        ),
        (
            "(((#b) .. ((#b) | (_)) -> (String)) | ((()) | (_))) & ((#box((#a))) | ((bool) -> (int)))",
            "(bool -> int) | #box(#a)",
        ),
        ("(String -> int) & (_ | (int -> ()))", "String -> int"),
        (
            "((_ | (int -> ())), bool) & ((String -> int), bool)",
            "(String -> int, bool)",
        ),
    ] {
        assert!(
            within(meet, other) && within(other, meet),
            "`{meet}` is not `{other}`"
        );
    }
}

// FAIL-types-meet-exact-arrows-differing-domains: split from FAIL-types-meet-key-arrows-not-within.
/// A meet of two functions is within each of its sides, through `Ty::meet` as `is` narrows.
#[test]
fn a_meet_of_exact_arrows_of_different_domains_is_within_each_side() {
    use zedc::check::read::parse_type;
    let meet_of = |a: &str, b: &str| parse_type(a).unwrap().meet(&parse_type(b).unwrap());
    for (a, b) in [
        ("(()) -> ()", "String -> int"),
        ("int -> ()", "String -> int"),
        ("int -> ()", "rat ->? bool"),
    ] {
        let m = meet_of(a, b);
        for side in [a, b] {
            assert!(
                m.subtype(&parse_type(side).unwrap()),
                "the meet of `{a}` and `{b}`, `{m}`, is not within `{side}`"
            );
        }
    }
}

/// The meet of an exact arrow and a partial arrow over equal parameter types is the exact
/// arrow over them whose result is the meet of the two: a function of both has its domain
/// hold those types and its values there in both results. Before, the two arrows were kept
/// apart, and the meet was not found within that one arrow; the kernel printer writes the
/// meet as that arrow, so its text read back as another type.
#[test]
fn a_meet_of_an_exact_and_a_partial_arrow_over_one_domain_is_one_arrow() {
    use zedc::check::read::parse_type;
    let ty = |s: &str| parse_type(s).unwrap();
    for (a, b, one) in [
        (
            "#b ->? int",
            "#b .. (#b | #pair(#b, int)) -> int | f64",
            "#b -> int",
        ),
        (
            "f64 | (#b ->? int)",
            "#b .. (#b | #pair(#b, int)) -> int | f64",
            "#b -> int",
        ),
        ("int -> int | rat", "int ->? int", "int -> int"),
    ] {
        for (l, r) in [(a, b), (b, a)] {
            let m = ty(l).meet(&ty(r));
            for (x, y) in [(&m, &ty(one)), (&ty(one), &m)] {
                assert!(
                    x.subtype(y),
                    "the meet of `{l}` and `{r}` is `{m}`, which is not `{one}`"
                );
            }
        }
    }
}

/// The meet of two functions of one parameter list (DESIGN.md sec:type_language, "Morphism
/// types carry two domain bounds"): empty where a guarantee is proved outside the other side's
/// permission; otherwise the exact arrows of both, each partial arrow met with the other
/// side's permission, within each side; and in every case it holds each function of both
/// sides, as an `is` test needs.
#[test]
fn a_meet_of_functions_meets_their_domains() {
    use zedc::check::read::parse_type;
    let ty = |s: &str| parse_type(s).unwrap();
    // Empty: a guarantee outside the other side's permission, with overloads and several
    // parameters on either side.
    for (a, b) in [
        ("int -> ()", "String -> ()"),
        ("int -> ()", "rat ->? ()"),
        ("(int -> #a) & (String -> #a)", "int -> #a"),
        ("(int | String) ->? #a", "(int -> #a) & (bool -> #a)"),
        ("(x: int, y: int) -> int", "(x: int, y: String) -> int"),
        (
            "(x: int, y: int) -> int",
            "(x: int, y: String | bool) ->? int",
        ),
    ] {
        for (l, r) in [(a, b), (b, a)] {
            let m = ty(l).meet(&ty(r));
            assert!(
                m.is_empty(),
                "the meet of `{l}` and `{r}` is `{m}`, not empty"
            );
        }
    }
    // Within each side, and not empty: each case names a function of both sides, which the
    // meet holds.
    for (a, b, both) in [
        ("int -> #a | #b", "int -> #a | #c", "int -> #a"),
        ("int -> #a", "(int | String) ->? #a | #b", "int -> #a"),
        (
            "(int | String) ->? int",
            "(int | bool) ->? int | #a",
            "int ->? int",
        ),
        (
            "(int -> #a) & (String ->? #b)",
            "(int | bool) ->? #a | #c",
            "int -> #a",
        ),
        (
            "(int -> #a) & (String -> #b)",
            "(int | String) ->? #a | #b",
            "(int -> #a) & (String -> #b)",
        ),
        (
            "(x: int, y: int) -> int",
            "(x: int, y: int | String) ->? int",
            "(x: int, y: int) -> int",
        ),
    ] {
        for (l, r) in [(a, b), (b, a)] {
            let m = ty(l).meet(&ty(r));
            assert!(
                ty(both).subtype(&m),
                "the meet of `{l}` and `{r}`, `{m}`, does not hold `{both}`"
            );
            for side in [l, r] {
                assert!(
                    m.subtype(&ty(side)),
                    "the meet of `{l}` and `{r}`, `{m}`, is not within `{side}`"
                );
            }
        }
    }
    // A variable in a parameter type proves nothing outside, and its arrows are kept: the meet
    // holds each function of both sides, here one on `int | rat`.
    let (a, b, both) = (
        "(T) -> int for T in int | rat",
        "(int | rat | String) ->? int",
        "(int | rat) -> int",
    );
    for (l, r) in [(a, b), (b, a)] {
        let m = ty(l).meet(&ty(r));
        assert!(
            ty(both).subtype(&m),
            "the meet of `{l}` and `{r}`, `{m}`, does not hold `{both}`"
        );
    }
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
/// side's, and each tuple of one side meets one tuple of the other there, the functions of the
/// tuples that meet are compared and the comparison is decided (COMPLEXITY.md F124). Before
/// (FAIL-types-loose-pairing-decided), the equal one was compared with no other function there,
/// and this comparison, which fails at `2`, was refused.
#[test]
fn functions_equal_on_both_sides_at_one_place_meeting_one_by_one_are_decided() {
    use zedc::check::read::parse_type;
    let f = "(_ -> int) & (_ -> int | #a)";
    let a = parse_type(&format!("({f}, 1) | (String -> String, 2)")).unwrap();
    let b = parse_type(&format!("(_ -> int, 1) | ({f}, 2) | (String -> String, 3)")).unwrap();
    assert!(!a.subtype(&b));
    let why = a.refused(&b);
    assert!(
        !why.contains("the checker does not try every way of pairing them"),
        "{why}"
    );
    // The same with one function at the place on the side compared is decided.
    let one = parse_type(&format!("({f}, 1)")).unwrap();
    assert!(one.subtype(&b));
}

/// Where both sides have two or more functions at one place, not all equal, the comparison is
/// refused only when some pairing of those functions could make it true: when even every
/// function of the type expected fitting every function of the side compared leaves a value
/// out, it is decided false, with no clause (FAIL-types-loose-over-refusal). Where the tuples
/// of the two sides that meet there pair each function of one side with one of the other's,
/// or with functions that meet no other, those pairs are compared and it is decided
/// (FAIL-types-loose-pairing-decided). Elsewhere, where a pairing does make it true, it is
/// still refused (COMPLEXITY.md F124).
#[test]
fn functions_at_one_place_are_refused_only_where_a_pairing_could_make_it_true() {
    use zedc::check::read::parse_type;
    let pairing = "the checker does not try every way of pairing them";
    let (f, g, h) = ("(int -> int)", "(int -> int | #a)", "(int -> 1)");
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
        // each tuple compared meets one expected, so those pairs are compared; true.
        (
            format!("({f}, 1) | ({h}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            true,
            false,
        ),
        // Three a side, the same way.
        (
            format!("({f}, 1) | ({h}, 2) | ({s}, 4)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3) | ({s}, 4)"),
            true,
            false,
        ),
        // `s` fits `f`, the one function at `2`, not: a definite no.
        (
            format!("({f}, 1) | ({s}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({s}, 3)"),
            false,
            false,
        ),
        // Each of `(f, 1)` and `(h, 1 | 2)` meets both `(g, 1 | 2)` and `(f, 1 | 2)`, so the
        // pairs do not form stars, but they are 4, no more than the 5 functions: they are
        // compared, and `f` fits `g` and `h` fits `f`, so true (FAIL-types-loose-pairing-non-star;
        // it was refused).
        (
            format!("({f}, 1) | ({h}, 1 | 2)"),
            format!("({g}, 1 | 2) | ({f}, 1 | 2) | ({h}, 3)"),
            true,
            false,
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
    // A domain is exact (DESIGN.md sec:type_language), so `f` fits `h` by its result alone.
    let f = "(int) -> int";
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
    // Fits, by `subtype` on one function each side: F <: G <: H, F <: K <: H, S alone, and D
    // alone: a domain is exact (DESIGN.md sec:type_language), so D, of a wider domain than G,
    // fits neither G nor any other.
    let pool = [
        "(int) -> 1",
        "(int) -> int",
        "(int) -> int | #z",
        "(int) -> 1 | #z",
        "(String) -> String",
        "(int | #z) -> int",
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
    assert!((0..5).all(|g| !fits[5][g] && !fits[g][5]));
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

/// Where two or more functions of each side meet at one place, each pair of functions whose
/// tuples may share a value is compared, so the comparison is decided as the subtype relation
/// decides it (FAIL-types-loose-pairing-decided).
#[test]
fn functions_at_one_place_are_decided_by_their_pairing() {
    use zedc::check::read::parse_type;
    let pairing = "the checker does not try every way of pairing them";
    let (f, g, h) = ("(int -> int)", "(int -> int | #a)", "(int -> 1)");
    let s = "(String -> String)";
    // (side compared, type expected, true)
    let cases = [
        // `f` fits `g` and `h` fits `f`: `(f, 1)` is in `(g, 1)` and `(h, 2)` in `(f, 2)`.
        (
            format!("({f}, 1) | ({h}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            true,
        ),
        (
            format!("({f}, 1) | ({h}, 2) | ({s}, 4)"),
            format!("({g}, 1) | ({f}, 2) | ({h}, 3) | ({s}, 4)"),
            true,
        ),
        // `s` fits no function the expected type pairs with `2`.
        (
            format!("({f}, 1) | ({s}, 2)"),
            format!("({g}, 1) | ({f}, 2) | ({s}, 3)"),
            false,
        ),
    ];
    for (a, b, holds) in &cases {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        assert!(!x.refused(&y).contains(pairing), "{a} <: {b} is refused");
        assert_eq!(x.subtype(&y), *holds, "{a} <: {b}");
    }
}

/// Each kind of spot where comparing only the star pairs decides (COMPLEXITY.md,
/// PROOF-star-pairs): flat tuples, a left tuple meeting two right tuples, nested tuples at one
/// depth, a nested tuple met at two depths (paired at every depth), `_` on either side,
/// payloads with items and with fields, and payloads inside tuples. Each comparison has two or
/// more functions a side at one place, so its pairs are the star pairs, and is checked three
/// ways: it is not refused for want of a pairing; its verdict is the one written; and it equals
/// the verdict of comparing each member of the side compared alone, which has one function at
/// the place and so pairs it with every function there. A pairing rule that keeps only the
/// first tuple each tuple meets fails the second case.
#[test]
fn star_pairs_decide_as_every_pair_in_each_kind_of_spot() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let pairing = "the checker does not try every way of pairing them";
    // `f` fits `g` and `g2`; `h` fits `f`; `g` fits neither `f` nor `h`.
    let (f, g, g2, h) = (
        "(int -> int)",
        "(int -> int | #a)",
        "(int -> int | #b)",
        "(int -> 1)",
    );
    let check = |members: &[Ty], other: &Ty, holds: bool, label: &str| {
        let t = Ty::union_all(members);
        assert!(!t.refused(other).contains(pairing), "{label}: refused");
        assert_eq!(t.subtype(other), holds, "{label}");
        let each = members.iter().all(|m| m.subtype(other));
        assert_eq!(each, holds, "{label}: member by member");
    };
    // (members of the side compared, type expected, holds)
    let cases: Vec<(Vec<String>, String, bool)> = vec![
        // Flat tuples.
        (
            vec![format!("({f}, 1)"), format!("({h}, 2)")],
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            true,
        ),
        (
            vec![format!("({f}, 1)"), format!("({g}, 2)")],
            format!("({g}, 1) | ({f}, 2) | ({h}, 3)"),
            false,
        ),
        // A left tuple meeting two right tuples, each with one function: both pairs needed.
        (
            vec![format!("({f}, 1 | 2)"), format!("({h}, 3)")],
            format!("({g}, 1) | ({g2}, 2) | ({h}, 3)"),
            true,
        ),
        (
            vec![format!("({f}, 1 | 2)"), format!("({h}, 3)")],
            format!("({g}, 1) | ({h}, 2) | ({h}, 3)"),
            false,
        ),
        // Nested tuples, at depth 1.
        (
            vec![format!("(0, ({f}, 1))"), format!("(0, ({h}, 2))")],
            format!("(0, ({g}, 1)) | (0, ({f}, 2)) | (0, ({h}, 3))"),
            true,
        ),
        (
            vec![format!("(0, ({f}, 1))"), format!("(0, ({g}, 2))")],
            format!("(0, ({g}, 1)) | (0, ({f}, 2)) | (0, ({h}, 3))"),
            false,
        ),
        // `_` on the side compared, in another column.
        (
            vec![format!("(_, {f}, 1)"), format!("(_, {h}, 2)")],
            format!("(_, {g}, 1) | (_, {f}, 2) | (_, {h}, 3)"),
            true,
        ),
        (
            vec![format!("(_, {f}, 1)"), format!("(_, {g}, 2)")],
            format!("(_, {g}, 1) | (_, {f}, 2) | (_, {h}, 3)"),
            false,
        ),
        // `_` on the type expected: in another column, and at the place of the functions.
        (
            vec![format!("({f}, 1, #x)"), format!("({h}, 2, #y)")],
            format!("({g}, _, #x) | ({f}, 2, #y) | ({h}, 3, #y)"),
            true,
        ),
        (
            vec![format!("({f}, 1)"), format!("({h}, 2)")],
            format!("(_, 1) | ({f}, 2) | ({h}, 3)"),
            true,
        ),
        (
            vec![format!("({f}, 1)"), format!("({g}, 2)")],
            format!("(_, 1) | ({f}, 2) | ({h}, 3)"),
            false,
        ),
        // Payloads with items.
        (
            vec![format!("#n({f}, 1)"), format!("#n({h}, 2)")],
            format!("#n({g}, 1) | #n({f}, 2) | #n({h}, 3)"),
            true,
        ),
        (
            vec![format!("#n({f}, 1)"), format!("#n({g}, 2)")],
            format!("#n({g}, 1) | #n({f}, 2) | #n({h}, 3)"),
            false,
        ),
        // Payloads with fields.
        (
            vec![format!("#n({f}, k: 1)"), format!("#n({h}, k: 2)")],
            format!("#n({g}, k: 1) | #n({f}, k: 2) | #n({h}, k: 3)"),
            true,
        ),
        (
            vec![format!("#n({f}, k: 1)"), format!("#n({g}, k: 2)")],
            format!("#n({g}, k: 1) | #n({f}, k: 2) | #n({h}, k: 3)"),
            false,
        ),
        // Payloads inside tuples.
        (
            vec![format!("(#n({f}, 1), #a)"), format!("(#n({h}, 2), #b)")],
            format!("(#n({g}, 1), #a) | (#n({f}, 2), #b) | (#n({h}, 3), #b)"),
            true,
        ),
        (
            vec![format!("(#n({f}, 1), #a)"), format!("(#n({g}, 2), #b)")],
            format!("(#n({g}, 1), #a) | (#n({f}, 2), #b) | (#n({h}, 3), #b)"),
            false,
        ),
    ];
    for (members, other, holds) in &cases {
        let ms: Vec<Ty> = members.iter().map(|m| parse_type(m).unwrap()).collect();
        let label = format!("{} <: {other}", members.join(" | "));
        check(&ms, &parse_type(other).unwrap(), *holds, &label);
    }
    // A tuple met at depth 0 and, as the same node, at depth 1: its place is paired at every
    // depth (`Spot::Any`).
    let r1 = parse_type(&format!("({f}, 1)")).unwrap();
    let r2 = parse_type(&format!("({h}, 2)")).unwrap();
    let outer = Ty::tuple(vec![parse_type("0").unwrap(), r1.clone()]);
    let members = [r1, r2, outer];
    for (other, holds) in [
        (
            format!("({g}, 1) | ({f}, 2) | ({h}, 3) | (0, ({g}, 1))"),
            true,
        ),
        (
            format!("({g}, 1) | ({f}, 2) | ({h}, 3) | (0, ({h}, 1))"),
            false,
        ),
    ] {
        let label = format!("shared ({f}, 1) <: {other}");
        check(&members, &parse_type(&other).unwrap(), holds, &label);
    }
}

/// A payload with fields and one with no fields and one item more never share a value, whatever
/// the last item: the mark of the field names, which stands last in the form of a payload with
/// fields, is no value of `_` there (COMPLEXITY.md, PROOF-star-pairs, the place lemma). Before,
/// `#n(1, x: 2) <: #n(1, 2, _)` held.
#[test]
fn a_payload_with_fields_never_meets_one_more_item_of_any_value() {
    use zedc::check::read::parse_type;
    let f = "(int -> int)";
    let cases = [
        ("#n(1, x: 2)".to_string(), "#n(1, 2, _)".to_string(), false),
        ("#n(1, x: 2)".to_string(), "#n(1, 2, #_)".to_string(), false),
        ("#n(1, 2, #q)".to_string(), "#n(1, x: 2)".to_string(), false),
        (
            format!("#n({f}, x: 1)"),
            format!("#n(({f} | #a), 1, _)"),
            false,
        ),
        // Where the shapes agree, `_` at the end still holds every value.
        ("#n(1, 2)".to_string(), "#n(1, _)".to_string(), true),
        ("#n(1, x: 2)".to_string(), "#n(1, x: _)".to_string(), true),
        ("#n(1, x: 2)".to_string(), "#n(_, x: 2)".to_string(), true),
        (
            format!("#n({f}, x: 1)"),
            format!("#n(({f} | #a), x: 1)"),
            true,
        ),
        (
            "#n(1, x: 2)".to_string(),
            "#n(1, 2, _) | #n(1, x: int)".to_string(),
            true,
        ),
    ];
    for (a, b, holds) in &cases {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        assert_eq!(x.subtype(&y), *holds, "{a} <: {b}");
    }
}

#[test]
fn a_cofinite_atom_set_minus_one_pair_is_a_subtype_of_a_union_holding_a_function() {
    use zedc::check::read::parse_type;
    let l = parse_type("(#_, 1) \\ (#a, 1)").unwrap();
    for r in [
        "(#_, 1) | (1, (int -> int))",
        "(#_, int) | (1, (int -> int))",
        "(#_, 1)",
    ] {
        assert!(
            l.subtype(&parse_type(r).unwrap()),
            "(#_, 1) \\ (#a, 1) <: {r}"
        );
    }
}

/// Each case: the type checked, the type expected, whether it is a subtype.
fn judge(cases: &[(&str, &str, bool)]) {
    use zedc::check::read::parse_type;
    let bad: Vec<String> = (cases.iter())
        .filter(|(a, b, holds)| parse_type(a).unwrap().subtype(&parse_type(b).unwrap()) != *holds)
        .map(|(a, b, holds)| format!("{a} <: {b} should be {holds}"))
        .collect();
    assert!(bad.is_empty(), "{bad:#?}");
}

/// A set of every atom nested in a tuple or an atom's payload holds no function, as at the
/// top level: before (FAIL-forms-nested-marks) the nested set kept the marks that stand for
/// functions in the forms compared, so a function was taken to be an atom there.
#[test]
fn marks_nested_in_sets_of_every_atom_stand_for_no_function() {
    judge(&[
        ("((int -> int), 1)", "(#_, 1) \\ (#a, 1)", false),
        ("((int -> int), 1)", "((#_, 1) \\ (#a, 1)) | (1, 2)", false),
        ("(((int -> int), 1), 2)", "((#_, 1), 2)", false),
        ("(((int -> int), 1), 2)", "((#_, 1) \\ (#a, 1), 2)", false),
        ("#q((int -> int), 1)", "#q(#_, 1) \\ #q(#a, 1)", false),
        (
            "((int -> int), 1) | (1, 1)",
            "((#_, 1) \\ (#a, 1)) | (1, 1)",
            false,
        ),
        ("#q(#b, 1)", "#q(#_, 1) \\ #q(#a, 1)", true),
        ("(#b, 1)", "((#_, 1) \\ (#a, 1)) | (1, (int -> int))", true),
        // `(..)` holds every function, nested too.
        ("((int -> int), 1)", "(..) \\ (#a, 1)", true),
        ("(((int -> int), 1), 2)", "((..) \\ (#a, 1), 2)", true),
    ]);
}

/// The unknown `_` of the type checked holds every value, `(#a, 1)` among them: before
/// (FAIL-forms-nested-marks) its form was a mark of its own, which a set of every value minus
/// `(#a, 1)` held.
#[test]
fn the_unknown_checked_is_every_value_not_a_value_of_its_own() {
    judge(&[
        ("(_, 1)", "(..) \\ (#a, 1)", false),
        ("((_, 1), 2)", "((..) \\ (#a, 1), 2)", false),
        ("(_, 1)", "((#_, 1) \\ (#a, 1)) | (1, 1)", false),
        ("(_, 1)", "(_, 1)", true),
        ("(_, 1)", "(..)", true),
    ]);
}

// The three tests below (TEST-nested-marks-struct-parts) cover the parts `Forms::level` keeps
// whole: a function's parameter and result types, and the struct part (COMPLEXITY.md,
// PROOF-nested-marks, last case of Lemma N). Each judgment is written in both directions,
// with its answer derived from DESIGN.md sec:type_language alone:
// - "Subtyping is semantic": `S <: T` holds exactly when every value of `S` is a value of `T`.
// - "Relation to semantic subtyping" (1) and "Morphism types carry two domain bounds": `K -> V`
//   is exact, its values the total functions whose domain is exactly `K`, each value in `V`.
//   So for an inhabited `K` and an inhabited `V`, `K -> V <: K' -> V'` holds exactly when `K`
//   and `K'` are one set and `V <: V'`, and two function types that differ so share no value.
// - L1.40d: `#_` is every atom, with any payload; `#a` is the bare atom `#a` alone; `(..)` is
//   every tuple and `{..}` every struct. At layer L1 a struct type is `{..}` or none
//   (`zed_kernel::types`, "Structs join at L2"): a struct type with fields cannot be written
//   until step L2.5, and its tests are row TEST-nested-marks-struct-fields.
// Write `D` for `(#_, 1) \ (#a, 1)`, the pairs `(x, 1)` of an atom `x` other than `#a`. It is
// the set `(#_ \ #a, 1)`, since `#_ \ #a` is every atom but `#a`. `(#_, 1)` is `D` and
// `(#a, 1)` besides.

/// A function's parameter type holding a set of every atom nested in a tuple, beside a set of
/// every atom nested in the same tuple as the function, and beside a function inside the
/// parameter: the parameter is compared as a whole, by its own subtyping.
///
/// The false judgments compare parameters neither of which holds the other, so they are false
/// whichever way a parameter is compared. Parameters of which one holds the other, `D` and
/// `(#_, 1)`, are in `a_function_type_has_an_exact_domain` (FAIL-types-fn-param-exact-domain).
#[test]
fn a_set_of_every_atom_nested_in_a_parameter_type_is_compared_as_a_set() {
    let d_param = "(((#_, 1) \\ (#a, 1)) -> int, (#_, 2) \\ (#a, 2))";
    // The same function type with `D` written `(#_ \ #a, 1)`, and the same second component.
    let d_param_again = "(((#_ \\ #a, 1)) -> int, (#_ \\ #a, 2))";
    // A parameter of `(#_ \ #b, 1)`, which holds `(#a, 1)`, not in `D`, and lacks `(#b, 1)`,
    // which is in `D`: neither set holds the other.
    let other_param = "(((#_ \\ #b, 1)) -> int, (#_, 2) \\ (#a, 2))";
    // The same function type as `d_param`, and a second component of every atom, `#a` too.
    let wider_second = "(((#_ \\ #a, 1)) -> int, (#_, 2))";
    // Parameters that hold a function too: `D | ((int) -> int, 1)` written two ways, and
    // `(#_ \ #b, 1) | ((int) -> int, 1)`, which holds `(#a, 1)` and lacks `(#b, 1)`.
    let fn_param = "((((#_, 1) \\ (#a, 1)) | ((int -> int), 1)) -> int)";
    let fn_param_again = "(((#_ \\ #a, 1) | ((int -> int), 1)) -> int)";
    let fn_param_other = "(((#_ \\ #b, 1) | ((int -> int), 1)) -> int)";
    judge(&[
        // Equal parameters, `D` both, and equal second components: one set, both ways.
        (d_param, d_param_again, true),
        (d_param_again, d_param, true),
        // Parameters `(#_ \ #b, 1)` and `D` are two sets, so no function is in both types.
        (other_param, d_param, false),
        (d_param, other_param, false),
        // Same functions; `(#_ \ #a, 2) <: (#_, 2)` and not back, `(#a, 2)` the difference.
        (d_param, wider_second, true),
        (wider_second, d_param, false),
        // A parameter holding a function beside `D`: one set written two ways, both ways.
        // Before, each was a definite no: inside the comparison of the two function types the
        // function in the parameter is read as a variable, so the forms were not made.
        (fn_param, fn_param_again, true),
        (fn_param_again, fn_param, true),
        // Against `(#_ \ #b, 1) | ((int) -> int, 1)`, another set: no function in both.
        (fn_param, fn_param_other, false),
        (fn_param_other, fn_param, false),
    ]);
}

/// A function's result type holding a set of every atom nested in a tuple, and a function
/// beside it: the results are compared by their own subtyping, the domains being one set.
#[test]
fn a_set_of_every_atom_nested_in_a_result_type_is_compared_as_a_set() {
    // Results `D` and `(#_ \ #a, 1)`, one set; each function in a pair with `D` at 2.
    let d_result = "((int -> ((#_, 1) \\ (#a, 1))), (#_, 2) \\ (#a, 2))";
    let d_result_again = "((int -> (#_ \\ #a, 1)), (#_ \\ #a, 2))";
    // Result `(#_, 1) | (1, (int) -> int)`, which holds `D` and more: `(#a, 1)`, for one.
    let wider_result = "((int -> ((#_, 1) | (1, (int -> int)))), (#_, 2) \\ (#a, 2))";
    // Result `((int) -> int, 1)`, which shares no value with `D`: a function is no atom.
    let fn_result = "((int -> ((int -> int), 1)), (#_, 2) \\ (#a, 2))";
    judge(&[
        (d_result, d_result_again, true),
        (d_result_again, d_result, true),
        // Domains both `int`; result `D <: (#_, 1) | (1, (int) -> int)`, and not back. Before,
        // the first was a definite no, for the reason in the test above.
        (d_result, wider_result, true),
        (wider_result, d_result, false),
        // Results inhabited and disjoint: a function of either type is not of the other.
        (fn_result, d_result, false),
        (d_result, fn_result, false),
    ]);
}

/// A function whose signature holds a type variable, beside a set of every atom nested in a
/// tuple, in a function's result or parameter type (TEST-nested-marks-fn-vars): the results
/// are compared by their own subtyping, and the parameters as one set, as above. The function
/// beside `D` is generic in a variable of its own, `(T -> T for T in int)`, which reads alike
/// in every environment. Before, five of the six judgments true here were a definite no (all
/// but `own_d_again <: own_d`). One that holds the variable of the function type around it, `T -> T` in
/// `(T -> … for T in int)`, is read by the environment and is not put back
/// (FAIL-closed-form-outer-variable).
#[test]
fn a_set_of_every_atom_beside_a_function_holding_a_variable_is_compared_as_a_set() {
    // Results `D` and `(#_, 1) | (1, g)`, `g` the generic `(T -> T for T in int)`: the second
    // holds `D` and `(#a, 1)` besides.
    let d_result = "(int -> ((#_, 1) \\ (#a, 1)))";
    let own_wider = "(int -> ((#_, 1) | (1, (T -> T for T in int))))";
    // Results `D | (1, g)`, written two ways, and `(#_, 1) | (1, g)`, which holds it.
    let own_d = "(int -> (((#_, 1) \\ (#a, 1)) | (1, (T -> T for T in int))))";
    let own_d_again = "(int -> ((#_ \\ #a, 1) | (1, (T -> T for T in int))))";
    // Parameters `D | (g, 1)` written two ways, and `(#_ \ #b, 1) | (g, 1)`, which holds
    // `(#a, 1)` and lacks `(#b, 1)`: neither parameter holds the other.
    let own_param = "((((#_, 1) \\ (#a, 1)) | ((T -> T for T in int), 1)) -> int)";
    let own_param_again = "(((#_ \\ #a, 1) | ((T -> T for T in int), 1)) -> int)";
    let own_param_other = "(((#_ \\ #b, 1) | ((T -> T for T in int), 1)) -> int)";
    judge(&[
        // Domains both `int`; `D <: (#_, 1) | (1, g)`, and not back (`(#a, 1)`).
        (d_result, own_wider, true),
        (own_wider, d_result, false),
        // One set written two ways, both ways; within `(#_, 1) | (1, g)`, and not back.
        (own_d, own_d_again, true),
        (own_d_again, own_d, true),
        (own_d, own_wider, true),
        (own_wider, own_d, false),
        // Parameters one set, both ways; two sets, no function in both types.
        (own_param, own_param_again, true),
        (own_param_again, own_param, true),
        (own_param, own_param_other, false),
        (own_param_other, own_param, false),
    ]);
}

/// The struct part `{..}`, which the forms keep whole, beside functions and sets of every atom
/// nested in tuples and payloads.
#[test]
fn every_struct_beside_functions_and_nested_sets_of_every_atom_is_compared_as_a_set() {
    // The pairs `(s, 1)` of a struct `s`, and `(f, 2)` of a function `f` of `(int) -> int`.
    let structs = "({..}, 1) | ((int -> int), 2)";
    judge(&[
        // Every tuple but `(#a, 1)` holds both kinds of pair; it holds `(#b, 1)` besides.
        (structs, "(..) \\ (#a, 1)", true),
        ("(..) \\ (#a, 1)", structs, false),
        // `(s, 1)` is in `(#_ | {..}, 1) \ (#a, 1)` (`s` is no atom); `(f, 2)` is in the row
        // after it. The right side holds `(#b, 1)` besides.
        (
            structs,
            "((#_ | {..}, 1) \\ (#a, 1)) | ((int -> int), 2)",
            true,
        ),
        (
            "((#_ | {..}, 1) \\ (#a, 1)) | ((int -> int), 2)",
            structs,
            false,
        ),
        // A struct is no atom, and an atom no struct: `(s, 2)` is not in `D`, nor `(#b, 1)`
        // in `({..}, 1)`.
        ("({..}, 1)", "(#_, 1) \\ (#a, 1)", false),
        ("(#_, 1) \\ (#a, 1)", "({..}, 1)", false),
        // A payload `(s, f)` of a struct and a function: `s` is not `#a`, so it is in
        // `#q(#_ | {..}, f) \ #q(#a, f)`, which holds `#q(#b, f)` besides.
        (
            "#q({..}, (int -> int))",
            "#q(#_ | {..}, (int -> int)) \\ #q(#a, (int -> int))",
            true,
        ),
        (
            "#q(#_ | {..}, (int -> int)) \\ #q(#a, (int -> int))",
            "#q({..}, (int -> int))",
            false,
        ),
        // A function is no atom, an atom no function: both inhabited, they share no value.
        ("({..}, (int -> int))", "({..}, #_ \\ #a)", false),
        ("({..}, #_ \\ #a)", "({..}, (int -> int))", false),
        // A function from every struct, in a pair: parameters both `{..}`, so the result
        // decides it, `#_ \ #a <: #_` and not back (`#a`).
        ("(({..} -> (#_ \\ #a)), 1)", "(({..} -> #_), 1)", true),
        ("(({..} -> #_), 1)", "(({..} -> (#_ \\ #a)), 1)", false),
    ]);
}

/// A union of `n` rows `((#_, i) \ (#a, i), (int -> int))`, each a set of every atom nested
/// beside a function, and the type `((#_, int), (int -> int))` that holds it.
fn nested_cut_rows(n: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let rows: Vec<String> = (0..n)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), (int -> int))"))
        .collect();
    let left = parse_type(&rows.join(" | ")).unwrap();
    (left, parse_type("((#_, int), (int -> int))").unwrap())
}

/// The small instance of `bench::nested_sets_of_every_atom_are_cut_in_linear_time`.
#[test]
fn many_nested_sets_of_every_atom_beside_functions_are_decided() {
    let (left, right) = nested_cut_rows(4);
    assert!(left.subtype(&right));
    assert!(!right.subtype(&left));
}

/// `nested_cut_rows(n)` as the results of two functions of `int`: the left result holds `n`
/// functions, each read as a variable inside the comparison of the two function types, and
/// each replaced by its function for the forms (TEST-nested-marks-struct-parts). The domains
/// are one set, so the left is a subtype exactly when its result is within the right's. The
/// right result is one shape: with `| (1, 2)` beside it, `Ty::subtype` on the rows alone
/// grows faster than linearly in `n`, with no function anywhere, row
/// PERF-types-cut-rows-union-scaling.
fn nested_cut_results(n: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let rows: Vec<String> = (0..n)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), (int -> int))"))
        .collect();
    let left = parse_type(&format!("(int -> ({}))", rows.join(" | "))).unwrap();
    let right = "(int -> ((#_, int), (int -> int)))";
    (left, parse_type(right).unwrap())
}

/// The small instance of `bench::nested_sets_of_every_atom_in_results_are_cut_in_linear_time`.
#[test]
fn many_nested_sets_of_every_atom_beside_functions_in_a_result_are_decided() {
    let (left, right) = nested_cut_results(4);
    assert!(left.subtype(&right));
    assert!(!right.subtype(&left));
}

/// Two function types `(T -> N(n, last) for T in int)`, `N(0, last)` the pair `(T, last)` and
/// `N(k + 1, last)` the pair `((int -> int), N(k, last))`, with `last` `1` on the left and
/// `int` on the right (BENCH-closed-form-late-variable). Inside the comparison of the two
/// function types each `int -> int` is read as a variable that stands for a function with no
/// variable, and `T` as a variable that is no function's, last in the walk of each level: the
/// results are compared at each of their `n` levels, each a pair holding `T` at its bottom.
/// The left is a subtype, as `1` is in `int`, and not back.
fn late_variable_results(n: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let nest = |last: &str| {
        let inner = (0..n).fold(format!("(T, {last})"), |s, _| {
            format!("((int -> int), {s})")
        });
        parse_type(&format!("(T -> {inner} for T in int)")).unwrap()
    };
    (nest("1"), nest("int"))
}

/// The small instance of
/// `bench::results_with_a_variable_late_beside_closed_functions_are_compared_in_linear_time`.
#[test]
fn results_with_a_variable_late_beside_closed_functions_are_decided() {
    for n in [0, 1, 4] {
        let (left, right) = late_variable_results(n);
        assert!(left.subtype(&right), "{n}");
        assert!(!right.subtype(&left), "{n}");
    }
}

/// A nest of `n` function types `G(n - 1)`, `G(0)` being `(int -> last)` and `G(k + 1)`
/// `(int -> (1, G(k)))`, with `last` `1` on the left and `int` on the right
/// (BENCH-closed-form-late-variable). Inside the comparison of the outer two, each `G(k)` is
/// read as a variable that stands for a function with no variable, so `closed_form` puts it
/// back and `form_verdict` compares the pair as written, and when they do not fit, the search
/// for a cover compares the same two results again. The left is a subtype, and not back.
fn nested_function_results(n: usize, last: &str) -> zedc::check::ty::Ty {
    use zedc::check::read::parse_type;
    let mut text = format!("type G0 = (int -> {last});\n");
    for k in 1..n {
        text.push_str(&format!("type G{k} = (int -> (1, G{}));\n", k - 1));
    }
    text.push_str(&format!("(int -> (1, G{}))", n - 1));
    parse_type(&text).unwrap()
}

/// `nested_function_results` with each result holding besides a row `R(n)` of `n + 1`
/// functions, shared by every level: `R(0)` is `((int -> int), 1)` and `R(i + 1)`
/// `((int -> int), R(i))`. Each of the `n` comparisons of function types reads `R(n)` again.
fn nested_function_results_beside_a_row(n: usize, last: &str) -> zedc::check::ty::Ty {
    use zedc::check::read::parse_type;
    let mut text = "type R0 = ((int -> int), 1);\n".to_string();
    for i in 1..=n {
        text.push_str(&format!("type R{i} = ((int -> int), R{});\n", i - 1));
    }
    text.push_str(&format!("type G0 = (int -> (R{n}, {last}));\n"));
    for k in 1..n {
        let g = format!("type G{k} = (int -> (R{n}, ((int -> int), G{})));\n", k - 1);
        text.push_str(&g);
    }
    text.push_str(&format!("(int -> (R{n}, ((int -> int), G{})))", n - 1));
    parse_type(&text).unwrap()
}

/// The small instances of `bench::nested_function_results_are_compared_in_linear_time` and
/// its row of functions beside each level. Before `Cx::fitted_written`, the false judgments
/// cost O(2^n): `n` 12 took 1.1 s without the row and 13.2 s with it.
#[test]
fn nested_function_results_beside_closed_functions_are_decided() {
    for n in [1, 2, 3, 6] {
        let (left, right) = (
            nested_function_results(n, "1"),
            nested_function_results(n, "int"),
        );
        assert!(left.subtype(&right), "{n}");
        assert!(!right.subtype(&left), "{n}");
        let left = nested_function_results_beside_a_row(n, "1");
        let right = nested_function_results_beside_a_row(n, "int");
        assert!(left.subtype(&right), "row {n}");
        assert!(!right.subtype(&left), "row {n}");
    }
}

/// A set of every atom nested in a result beside a function that holds the variable of the
/// function type around it (FAIL-closed-form-outer-variable).
#[test]
fn a_set_of_every_atom_beside_a_function_holding_an_outer_variable_is_compared_as_a_set() {
    // For each carrier of `T`, the results are `D | (1, T -> T)` written two ways and
    // `(#_, 1) | (1, T -> T)`, `D` being `(#_, 1) \ (#a, 1)`.
    let outer_d = "(T -> (((#_, 1) \\ (#a, 1)) | (1, (T -> T))) for T in int)";
    let outer_d_again = "(T -> ((#_ \\ #a, 1) | (1, (T -> T))) for T in int)";
    let outer_wider = "(T -> ((#_, 1) | (1, (T -> T))) for T in int)";
    judge(&[
        (outer_d, outer_d_again, true),
        (outer_d_again, outer_d, true),
        (outer_d, outer_wider, true),
        (outer_wider, outer_d, false),
    ]);
}

/// A function that reads alike in every environment (`int -> int`) beside one that holds the
/// outer variable (`T -> T`), on either side, over two carriers: compared by the variables
/// they are read as, where one of them holds `T` (`Comparing::fits_named`). An attempt to
/// break `reads_alike_anywhere`: a function written alike on both sides is equal only where
/// both read alike, so `T -> T` read on each side is never taken for `int -> int`, and the
/// carrier `f64` of `T` makes the two differ. The cases with `T -> T` on the left and
/// `int -> int` on the right are wrong on main for another cause and are left to row
/// FAIL-types-result-fn-outer-binding.
#[test]
fn functions_reading_alike_or_holding_the_outer_variable_are_compared_by_their_readings() {
    let d = "((#_, 1) \\ (#a, 1))";
    let generic =
        |inner: &str, set: &str| format!("(T -> ({set} | (1, ({inner}))) for T in int | f64)");
    let (s_tt, s_ii) = (generic("T -> T", d), generic("int -> int", d));
    let (q_tt, q_ii) = (
        generic("T -> T", "(#_, 1)"),
        generic("int -> int", "(#_, 1)"),
    );
    let (p_tt, p_ii) = (generic("T -> T", "(1, 1)"), generic("int -> int", "(1, 1)"));
    judge(&[
        (&p_ii, &p_tt, false),
        (&s_tt, &q_tt, true),
        (&s_ii, &q_ii, true),
        (&s_ii, &q_tt, false),
        (&q_tt, &s_tt, false),
    ]);
}

/// A generic function over `(#k0 | #k1, T)` within one arrow per atom
/// (FAIL-types-generic-arrow-overload-cover).
#[test]
fn a_generic_function_is_within_an_arrow_for_each_atom_of_its_domain() {
    judge(&[
        (
            "((#k0 | #k1, int) -> int)",
            "((#k0, int) -> int) & ((#k1, int) -> int)",
            true,
        ),
        (
            "((#k0 | #k1, T) -> int for T in int)",
            "((#k0, int) -> int) & ((#k1, int) -> int)",
            true,
        ),
        (
            "((#k0 | #k1, T) -> int for T in int)",
            "((#k0, T) -> int for T in int) & ((#k1, U) -> int for U in int)",
            true,
        ),
        // A key no arrow of `q` takes.
        (
            "((#k0 | #k1 | #k2, T) -> int for T in int)",
            "((#k0, int) -> int) & ((#k1, int) -> int)",
            false,
        ),
        // One parameter, the instance's keys those of two arrows.
        (
            "((T | bool) -> int for T in int)",
            "(int -> int) & (bool -> int)",
            true,
        ),
        (
            "((T | bool) -> int for T in int)",
            "(int -> int) & (f64 -> int)",
            false,
        ),
        // At `#k1` both arrows of `s` apply, and rule 6 of sec:type_resolution intersects their
        // results, `int & String`, which holds no value and so is within `String`: the
        // generic arrow agrees with the one written without `T`.
        (
            "((#k0 | #k1, int) -> int) & ((#k1, int) -> String)",
            "((#k0, int) -> int) & ((#k1, int) -> String)",
            true,
        ),
        (
            "((#k0 | #k1, T) -> int for T in int) & ((#k1, U) -> String for U in int)",
            "((#k0, int) -> int) & ((#k1, int) -> String)",
            true,
        ),
    ]);
}

/// A union of `n` rows `((#_, i) \ (#a, i), x)`, each a set of every atom nested beside `x`,
/// and the union `((#_, int), x) | (1, 2)` that holds it. The row `(1, 2)` shares no value
/// with a left row, but it splits the first components into two classes, the nested sets and
/// `1`, and the class of the nested sets holds `n + 1` cells (PERF-types-cut-rows-union-scaling).
fn nested_cut_rows_beside_a_pair(n: usize, x: &str) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let rows: Vec<String> = (0..n)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), {x})"))
        .collect();
    let left = parse_type(&rows.join(" | ")).unwrap();
    let right = parse_type(&format!("(((#_, int), {x}) | (1, 2))")).unwrap();
    (left, right)
}

/// The small instance of `bench::nested_sets_of_every_atom_against_a_union_are_cut_in_linear_time`,
/// beside a function, an integer and an atom with a payload. The left holds no `(1, 2)` and the
/// right holds `(#a, 0)` in its first component, so neither holds the other. A left row with
/// a string in its nested set is outside the right, which holds only integers there, and that
/// value is found on the piece of the class of the nested sets.
#[test]
fn many_nested_sets_of_every_atom_beside_a_pair_are_decided() {
    use zedc::check::read::parse_type;
    for x in ["(int -> int)", "3", "#c(1)"] {
        let (left, right) = nested_cut_rows_beside_a_pair(4, x);
        assert!(left.subtype(&right), "{x}");
        assert!(!right.subtype(&left), "{x}");
        let rows: Vec<String> = (0..4)
            .map(|i| format!("((#_, {i}) \\ (#a, {i}), {x})"))
            .collect();
        let wider = parse_type(&format!("{} | ((#_, \"s\"), {x})", rows.join(" | "))).unwrap();
        assert!(!wider.subtype(&right), "{x}");
        assert!(left.subtype(&wider), "{x}");
    }
}

/// The left rows `((#_, i) \ (#a, i), 1)` for `i` in `0..k`, and the right union
/// `((#_, int), 1) | (1, 2)` with `m` rows `(cell, _)` beside it, `cell` with `{i}` replaced
/// by `i` in `0..m` (TEST-split-classes-uncut-bench). The `m` rows cut the first component
/// of the box into a union of `m` cells; the left rows form one class of `k + 1` cells there.
fn nested_rows_against_cut_rows(
    k: usize,
    m: usize,
    cell: &str,
) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let left: Vec<String> = (0..k)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), 1)"))
        .collect();
    let cut: Vec<String> = (0..m)
        .map(|i| format!("({}, _)", cell.replace("{i}", &i.to_string())))
        .collect();
    let right = format!("((#_, int), 1) | (1, 2) | {}", cut.join(" | "));
    (
        parse_type(&left.join(" | ")).unwrap(),
        parse_type(&right).unwrap(),
    )
}

/// The small instances of `bench::a_large_first_component_beside_a_small_class_is_decided_in_linear_time`
/// and of its mirror. A left row whose first component meets one of the `m` rows is held only
/// when its second component is within `_` there: `((#b, 3), 2)` is held by `((#b, 3), _)`,
/// `((#b, 7), 2)` by nothing, since 7 is not among `0..4` and the shape holds only `1`.
#[test]
fn nested_sets_against_a_first_component_cut_by_rows_are_decided() {
    use zedc::check::read::parse_type;
    for (k, m, cell) in [(2, 4, "(#b, {i})"), (4, 2, "({i}, {i})")] {
        let (left, right) = nested_rows_against_cut_rows(k, m, cell);
        assert!(left.subtype(&right), "{k} {m}");
        assert!(!right.subtype(&left), "{k} {m}");
    }
    let (_, right) = nested_rows_against_cut_rows(2, 4, "(#b, {i})");
    let left = "((#_, 0) \\ (#a, 0), 1) | ((#_, 1) \\ (#a, 1), 1)";
    for (extra, held) in [
        ("((#b, 3), 2)", true),
        ("((#b, 7), 2)", false),
        ("((#_, \"s\"), 1)", false),
    ] {
        let wider = parse_type(&format!("{left} | {extra}")).unwrap();
        assert_eq!(wider.subtype(&right), held, "{extra}");
    }
}

/// `n` rows `((#_, i) \ (#a, i), 1)`, each a set of every atom nested beside `1`, and the one
/// shape `((#_, int), 1 | 2)`, whose second component is wider than the rows' `1`
/// (PERF-types-nested-rows-wider-second).
fn nested_rows_wider_second(n: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let rows: Vec<String> = (0..n)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), 1)"))
        .collect();
    (
        parse_type(&rows.join(" | ")).unwrap(),
        parse_type("((#_, int), 1 | 2)").unwrap(),
    )
}

/// `n` rows `((#_, i) \ (#a, i), 1)` against `((#_, int), 1 | 2) | ((#_, int), 2 | 3)`, whose
/// two shapes cross on the second component (`1 | 2` and `2 | 3` meet in `2`), so their pieces
/// are not cut at once there; DESIGN.md L1.23 takes out the piece `3` of the second component
/// (outside the rows' `1`) and then the piece `2`, and the rows' `1` is left
/// (TEST-may-cover-piece-removal).
fn crossing_rows_wider_second(n: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let rows: Vec<String> = (0..n)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), 1)"))
        .collect();
    (
        parse_type(&rows.join(" | ")).unwrap(),
        parse_type("((#_, int), 1 | 2) | ((#_, int), 2 | 3)").unwrap(),
    )
}

/// The small instance of `bench::crossing_sets_against_a_wider_second_component_are_decided_in_linear_time`.
/// The rows are within the two shapes; the shapes are not within the rows (`((#a, 0), 1)` and
/// `((#b, 0), 3)` are in them and in no row); a row with `4` beside it, or with a string in its
/// nested set, is not within them; `((#b, 2), 3)` is.
#[test]
fn crossing_sets_against_a_wider_second_component_are_decided() {
    use zedc::check::read::parse_type;
    let (left, right) = crossing_rows_wider_second(4);
    assert!(left.subtype(&right));
    assert!(!right.subtype(&left));
    let rows = "((#_, 0) \\ (#a, 0), 1) | ((#_, 1) \\ (#a, 1), 1)";
    for (extra, held) in [
        ("((#b, 2), 3)", true),
        ("((#b, 2), 4)", false),
        ("((#_, \"s\"), 1)", false),
        ("((#_, 5) \\ (#a, 5), 1 | 3)", true),
    ] {
        let wider = parse_type(&format!("{rows} | {extra}")).unwrap();
        assert_eq!(wider.subtype(&right), held, "{extra}");
    }
}

/// The small instance of `bench::nested_sets_against_a_wider_second_component_are_decided_in_linear_time`.
/// The rows are within the shape; the shape is not within the rows (`((#a, 0), 1)` and
/// `((#b, 0), 2)` are in it and in no row); a row with `3` beside it, or with a string in its
/// nested set, is not within the shape; `((#b, 2), 2)` is.
#[test]
fn nested_sets_against_a_wider_second_component_are_decided() {
    use zedc::check::read::parse_type;
    let (left, right) = nested_rows_wider_second(4);
    assert!(left.subtype(&right));
    assert!(!right.subtype(&left));
    let rows = "((#_, 0) \\ (#a, 0), 1) | ((#_, 1) \\ (#a, 1), 1)";
    for (extra, held) in [
        ("((#b, 2), 2)", true),
        ("((#b, 2), 3)", false),
        ("((#_, \"s\"), 1)", false),
        ("((#_, 5) \\ (#a, 5), 1 | 2)", true),
    ] {
        let wider = parse_type(&format!("{rows} | {extra}")).unwrap();
        assert_eq!(wider.subtype(&right), held, "{extra}");
    }
}

/// DESIGN.md sec:type_language, "Morphism types carry two domain bounds": plain `K -> V` is
/// exact (`L = U = K`), `K ->? V` has `L = {}` and `U = K`, and `<:` holds iff `L2 <: L1`,
/// `U1 <: U2` and `V1 <: V2`. "Because a domain is observable (`::domain`, `.count`), a wider
/// exact domain is not a subtype of a narrower one: `int -> int` is not `<: int[0..<10] ->
/// int`." The same text gives `{"a","b"} -> int <: Utf8String ->? int`. Before
/// (FAIL-types-fn-param-exact-domain) the checker compared parameters contravariantly and
/// read `K ->? V` as `K -> (V | #notFound)`, so four of these failed. Each answer is derived
/// from the rule, `L1`, `U1` of the left and `L2`, `U2` of the right.
#[test]
fn a_function_type_has_an_exact_domain() {
    judge(&[
        // L1 = U1 = int, L2 = U2 = 1 | 2: U1 <: U2 fails.
        ("(int -> int)", "((1 | 2) -> int)", false),
        // L2 = int, L1 = 1 | 2: L2 <: L1 fails.
        ("((1 | 2) -> int)", "(int -> int)", false),
        // The same with a set of every atom nested in the parameter (D = (#_, 1) \ (#a, 1)).
        ("(((#_, 1)) -> int)", "(((#_, 1) \\ (#a, 1)) -> int)", false),
        ("(((#_, 1) \\ (#a, 1)) -> int)", "(((#_, 1)) -> int)", false),
        // DESIGN's own example: L2 = {} <: L1, U1 = {"a","b"} <: String, V1 <: V2.
        ("((\"a\" | \"b\") -> int)", "(String ->? int)", true),
        // An exact domain is not a partial one: L2 = int is not within L1 = {}.
        ("(int ->? 1)", "(int -> (1 | #notFound))", false),
        // Each holds itself.
        ("(int -> int)", "(int -> int)", true),
    ]);
}

/// Results that are tuples of functions and values with no variable, which a comparison of
/// function types reads once and compares row by row, component by component
/// (PERF-types-shared-row-each-level): a yes needs each component within the one at its
/// place, and a no comes from one component that is not, at any depth of nested rows. A row
/// of another length, or a union of rows on the right, is compared as before.
#[test]
fn rows_of_functions_in_results_are_compared_by_component() {
    judge(&[
        (
            "(int -> ((int -> int), 1))",
            "(int -> ((int -> int), int))",
            true,
        ),
        (
            "(int -> ((int -> int), int))",
            "(int -> ((int -> int), 1))",
            false,
        ),
        (
            "(int -> ((int -> 1), 1))",
            "(int -> ((int -> int), 1))",
            true,
        ),
        (
            "(int -> ((int -> int), 1))",
            "(int -> ((int -> 1), 1))",
            false,
        ),
        // An exact domain: `int -> int` is not within `1 -> int`.
        (
            "(int -> ((int -> int), 1))",
            "(int -> ((1 -> int), 1))",
            false,
        ),
        (
            "(int -> ((int -> int), ((int -> int), 1)))",
            "(int -> ((int -> int), ((int -> int), int)))",
            true,
        ),
        (
            "(int -> ((int -> int), ((int -> int), int)))",
            "(int -> ((int -> int), ((int -> int), 1)))",
            false,
        ),
        (
            "(int -> ((int -> int), 1))",
            "(int -> ((int -> int), 1, 1))",
            false,
        ),
        (
            "(int -> ((int -> int), 1))",
            "(int -> (((int -> int), 1) | ((int -> int), 2)))",
            true,
        ),
        (
            "(int -> (((int -> int), 1) | ((int -> int), 2)))",
            "(int -> ((int -> int), 1))",
            false,
        ),
    ]);
}

/// A function in the result holding the variable the parameters bind is compared at the
/// binding the parameters made, not bound again (FAIL-types-result-fn-outer-binding): a
/// call fixes a bounded variable to one carrier (DESIGN sec:type_resolution rule 6), so
/// `T -> (T -> T) for T in int | f64` at `T = f64` is `f64 -> (f64 -> f64)`, whose result
/// is not within `int -> int` (sec:type_language: a function type's domain is exact).
#[test]
fn a_function_in_a_result_holds_the_variable_at_the_binding_of_the_parameters() {
    let d = "((#_, 1) \\ (#a, 1))";
    let generic =
        |inner: &str, set: &str| format!("(T -> ({set} | (1, ({inner}))) for T in int | f64)");
    judge(&[
        // At T = f64 the result is f64 -> f64, not within int -> int.
        (
            "(T -> (T -> T) for T in int | f64)",
            "(f64 -> (int -> int))",
            false,
        ),
        (
            "(T -> (T -> T) for T in int | f64)",
            "(T -> (int -> int) for T in int | f64)",
            false,
        ),
        // At T = f64 the domain f64 is not int.
        (
            "(T -> (T -> int) for T in int | f64)",
            "(T -> (int -> int) for T in int | f64)",
            false,
        ),
        // The same inside a tuple.
        (
            "(T -> (1, (T -> T)) for T in int | f64)",
            "(T -> (1, (int -> int)) for T in int | f64)",
            false,
        ),
        // The same beside a row of numbers.
        (
            &generic("T -> T", "(1, 1)"),
            &generic("int -> int", "(1, 1)"),
            false,
        ),
        // The same beside a set of every atom.
        (
            &generic("T -> T", d),
            &generic("int -> int", "(#_, 1)"),
            false,
        ),
        // Two functions deep: the binding reaches the function in the result's result.
        (
            "(T -> (int -> (T -> T)) for T in int | f64)",
            "(T -> (int -> (int -> int)) for T in int | f64)",
            false,
        ),
        // An unbounded variable: the parameter binds it to `int`, so the result is
        // `int -> int`, not within `f64 -> f64`.
        ("(T -> (T -> T))", "(int -> (f64 -> f64))", false),
        // Controls.
        ("(T -> (T -> T))", "(int -> (int -> int))", true),
        (
            "(T -> (int -> (T -> T)) for T in int)",
            "(T -> (int -> (int -> int)) for T in int)",
            true,
        ),
        (
            "(T -> (int -> T) for T in int | f64)",
            "(T -> (int -> int) for T in int | f64)",
            false,
        ),
        (
            "(T -> (1, T) for T in int | f64)",
            "(T -> (1, int) for T in int | f64)",
            false,
        ),
        (
            "(T -> (T -> T) for T in int)",
            "(T -> (int -> int) for T in int)",
            true,
        ),
        (
            "(T -> (T -> T) for T in int | f64)",
            "(T -> (T -> T) for T in int | f64)",
            true,
        ),
    ]);
}

/// Each tuple of the side compared meets two tuples expected, so the pairs of nodes that may
/// share a value at the function's place form no stars; they are 4, no more than the 5
/// functions there, so each pair is compared and the comparison decided
/// (FAIL-types-loose-pairing-non-star; both were refused). With `h` = `int -> 1`, `(f, 1)` is
/// in `(g, 1 | 2)` (`f` fits `g`) and `(h, 1 | 2)` in `(f, 1 | 2)` (`h` fits `f`): true. With
/// `h` = `(int | String) -> int`, as the row was first written, `h` fits neither `f` nor `g`,
/// since a domain is exact and `int | String` is not within `int` (DESIGN.md
/// sec:type_language, FAIL-types-fn-param-exact-domain): a definite no.
#[test]
fn functions_at_one_place_whose_tuples_meet_two_each_are_decided() {
    use zedc::check::read::parse_type;
    let (f, g) = ("(int -> int)", "(int -> int | #a)");
    for (h, holds) in [("(int -> 1)", true), ("((int | String) -> int)", false)] {
        let a = parse_type(&format!("({f}, 1) | ({h}, 1 | 2)")).unwrap();
        let b = parse_type(&format!("({g}, 1 | 2) | ({f}, 1 | 2) | ({h}, 3)")).unwrap();
        assert_eq!(a.subtype(&b), holds, "h = {h}");
        assert_eq!(a.refused(&b), "", "h = {h}");
    }
}

/// `Never -> v` (guarantee and permission `Never`) and `Never ->? v` (permission `Never`, no
/// guarantee) hold the same one function, the one of empty domain (DESIGN.md
/// sec:type_language, "Morphism types carry two domain bounds"), so each is within the other
/// (FAIL-types-exact-never-domain: the exact form was within the partial one, not back).
#[test]
fn an_exact_and_a_partial_arrow_over_never_are_one_type() {
    use zedc::check::read::parse_type;
    for v in ["int", "(rat, f64)", "Never"] {
        let exact = parse_type(&format!("Never -> {v}")).unwrap();
        let partial = parse_type(&format!("Never ->? {v}")).unwrap();
        assert!(
            exact.subtype(&partial),
            "`Never -> {v}` is not within `Never ->? {v}`"
        );
        assert!(
            partial.subtype(&exact),
            "`Never ->? {v}` is not within `Never -> {v}`"
        );
    }
}

/// The meet of two exact functions over domains that share no value is empty (DESIGN.md
/// sec:type_language, "two exact arrows over different domains share no value and their
/// intersection is empty"), a function-typed domain among them (FAIL-types-meet-fn-param-
/// domains: the meet was read as the overload `((_ -> ()) -> _) & (rat -> f64)`).
#[test]
fn a_meet_of_functions_over_a_function_domain_and_another_domain_is_empty() {
    use zedc::check::read::parse_type;
    for text in [
        "((_ -> ()) -> _) & ((rat -> f64) | ())",
        "((_ -> ()) -> _) & ((rat .. (rat | #a) -> f64) | ())",
        // Data the one side's domain holds, where the other takes only functions. (`&` of two
        // arrows writes an overload; `| ()` makes it a meet.)
        "((_ -> ()) ->? _) & ((rat -> f64) | ())",
        // A partial arrow's function type holds the function of no key.
        "((#a ->? Never) -> _) & ((rat ->? f64) | ())",
    ] {
        let t = parse_type(text).unwrap();
        assert!(t.is_empty(), "`{text}` reads as `{t}`, not `Never`");
    }
    // Two partial arrows share the function of no key, so their meet is not empty; nor is the
    // meet of an exact and a partial arrow over one function domain.
    for text in [
        "((_ -> ()) ->? _) & ((rat ->? f64) | ())",
        "((#a -> ()) -> _) & (((#a -> ()) ->? f64) | ())",
    ] {
        let t = parse_type(text).unwrap();
        assert!(!t.is_empty(), "`{text}` reads as `Never`");
    }
    // The meet of a function with a union holding it is that function.
    let text = "((_ -> ()) -> _) & (((_ -> ()) -> _) | (rat -> f64))";
    let (t, want) = (
        parse_type(text).unwrap(),
        parse_type("(_ -> ()) -> _").unwrap(),
    );
    assert!(
        t.subtype(&want) && want.subtype(&t),
        "`{text}` reads as `{t}`"
    );
}
