//! The decider of recursive groups' inhabitation (cross-review X14, `split_bdw2`), on the
//! graph families it was measured with: every answer it gives matches the classical Büchi
//! game reference, answers do not depend on how nodes are numbered, and its work grows
//! linearly, also when one node is widened (the widened variants made the first version,
//! which counted distinct children by searching a list, quadratic).

use super::bes_families::{FAMILIES, G, K, family, reference};
use zed_kernel::types::bes::{Answer, Bes, Kind, decide};
use zed_tests::scaling;

/// The widened variants that came nearest to quadratic work in the first version.
const WIDENED: [&str; 5] = [
    "exring:6:1",
    "defeatgsr:6:42:and",
    "indirect_alt_ladder:6:7",
    "g_codex_adversary:6:24:mor",
    "tiles:6:0:mor",
];

/// The decider's answers, checked against the reference; the number refused.
pub(super) fn checked(name: &str, g: &G) -> usize {
    let got = decide(&g.bes()).answers;
    let want = reference::answers(g);
    let mut refused = 0;
    for (v, (a, w)) in got.iter().zip(&want).enumerate() {
        match a {
            Answer::Refused => refused += 1,
            Answer::Empty => assert!(!w, "{name}: node {v} decided empty, is inhabited"),
            Answer::Inhabited => assert!(w, "{name}: node {v} decided inhabited, is empty"),
        }
    }
    refused
}

/// `g` with its nodes numbered in reverse.
pub(super) fn reversed(g: &G) -> G {
    let n = g.k.len() as u32;
    let mut h = G::new();
    for v in (0..n as usize).rev() {
        h.add(g.k[v], g.c[v].iter().map(|&w| n - 1 - w).collect());
    }
    h.seal();
    h
}

#[test]
fn every_decided_answer_is_right_and_independent_of_numbering() {
    let names = FAMILIES.iter().copied().chain(WIDENED);
    for name in names {
        for n in [3, 8, 24] {
            let g = family(name, n);
            let label = format!("{name} at {n}");
            checked(&label, &g);
            let a = decide(&g.bes()).answers;
            let mut b = decide(&reversed(&g).bes()).answers;
            b.reverse();
            assert_eq!(a, b, "{label}: answers depend on numbering");
        }
    }
}

/// `S = (int) -> S` is inhabited (a morphism's value type may recur), `E = (int, E)` is
/// empty (a tuple's may not), `W = (W) -> int` is inhabited, and `G = (int) -> empty` is
/// empty.
#[test]
fn a_cycle_through_a_morphism_is_inhabited_and_one_through_a_tuple_is_not() {
    let mut b = Bes::new();
    let s = b.add(Kind::Mor, vec![0]);
    let top = b.add(Kind::Top, vec![]);
    let e = b.add(Kind::And, vec![top, 2]);
    let w = b.add(Kind::Mor, vec![top]);
    let bot = b.add(Kind::Bot, vec![]);
    let g = b.add(Kind::Mor, vec![bot]);
    b.seal();
    let d = decide(&b);
    assert_eq!(d.answers[s as usize], Answer::Inhabited);
    assert_eq!(d.answers[e as usize], Answer::Empty);
    assert_eq!(d.answers[w as usize], Answer::Inhabited);
    assert_eq!(d.answers[g as usize], Answer::Empty);
    assert!(d.refusals.is_empty());
}

/// A refused group: a tuple cycle with two ways around it, an `And` node needing two
/// undecided children, and two morphism types inside. The refusal names the cycle's shape,
/// and every node whose answer depends on it is refused too.
#[test]
fn a_refusal_names_its_cause() {
    let g = family("indirect_alt_ladder", 6);
    let d = decide(&g.bes());
    let r = d.refusals.first().expect("the ladder is refused");
    assert!(
        r.cyclomatic >= 2 && r.branching_and >= 1 && r.gates >= 2,
        "{r:?}"
    );
    assert!(d.answers.contains(&Answer::Refused));
}

/// The port refuses exactly as many nodes as the cross-measured split_bdw2 does.
#[test]
fn the_refusals_match_the_cross_measure() {
    let d = decide(&family("indirect_alt_ladder", 512).bes());
    let refused = d.answers.iter().filter(|a| **a == Answer::Refused).count();
    assert_eq!(refused, 2555);
    for name in FAMILIES.iter().filter(|f| **f != "indirect_alt_ladder") {
        let d = decide(&family(name, 512).bes());
        assert!(!d.answers.contains(&Answer::Refused), "{name}");
    }
}

fn scales(name: &str, n: usize) {
    // Inputs are built before timing, by `check_order_inputs` only at the sizes each process
    // runs. Built at both sizes before the first run, they took the whole first phase where
    // each run is counted under DynamoRIO in a new process that builds its input again: the
    // 12 benchmarks of this helper and `a_long_run_of_union_edges_scales` stopped at their
    // 20 s limit on hm4 (job f25 on main b43e6d8bb), and with no limit they counted 8.00 times
    // the instructions at 8n and took 38 to 46 s (job f27; BENCH-main-43-pieces-v5e4).
    scaling::check_order_inputs(
        &format!("deciding {name}"),
        n,
        1,
        |m| family(name, m).bes(),
        |g| {
            std::hint::black_box(decide(std::hint::black_box(g)));
        },
    );
}

/// A ring of `kinds` (each node's first child the next node, the last's the first), with the
/// edges `extra` added, as `(from, to)` by place, and for each `(v, w)` of `mors` a morphism
/// node, a child of the node at place `v`, whose child is the node at place `w`. The morphism
/// nodes come after the ring, in the order of `mors`.
pub(super) fn ring(kinds: &[K], extra: &[(usize, usize)], mors: &[(usize, usize)]) -> G {
    let n = kinds.len();
    let mut kids: Vec<Vec<u32>> = (0..n).map(|i| vec![((i + 1) % n) as u32]).collect();
    for &(v, w) in extra {
        kids[v].push(w as u32);
    }
    for (k, &(v, _)) in mors.iter().enumerate() {
        kids[v].push((n + k) as u32);
    }
    let mut g = G::new();
    for (&k, c) in kinds.iter().zip(kids) {
        g.add(k, c);
    }
    for &(_, w) in mors {
        g.add(K::Mor, vec![w as u32]);
    }
    g.seal();
    g
}

/// Unions at places 0 to 2 and a tuple at 3; the tuple has a morphism child back to 0, and
/// union 0 one to the tuple.
const FOUR: [K; 4] = [K::Or, K::Or, K::Or, K::And];

/// [`FOUR`] with two more unions after the tuple.
const SIX: [K; 6] = [K::Or, K::Or, K::Or, K::And, K::Or, K::Or];

/// The morphism children of [`FOUR`] and [`SIX`].
const EXITS: [(usize, usize); 2] = [(3, 0), (0, 3)];

/// A union edge `v -> w` along the cycle: `v`'s successor reaches `w` through unions alone, so
/// the edge changes no answer and the ring is one cycle, which the deletion cascade decides
/// (item GROUP-cycle-dup-across). Before the item, the second cycle the edge made refused each
/// of these rings.
#[test]
fn a_union_edge_along_the_cycle_leaves_one_cycle() {
    for (kinds, edge) in [(&FOUR[..], (0, 2)), (&SIX, (0, 2)), (&SIX, (4, 0))] {
        let g = ring(kinds, &[edge], &EXITS);
        let label = format!("{kinds:?} with {edge:?}");
        assert_eq!(checked(&label, &g), 0, "{label}: refused");
        assert!(decide(&g.bes()).refusals.is_empty(), "{label}");
    }
}

/// Edges the test keeps, each leaving the ring refused for its two cycles: `2 -> 0` and
/// `1 -> 0` close a cycle of unions; `0 -> 4`, `2 -> 4`, `2 -> 5` and `1 -> 4` pass the tuple
/// at 3, so the union's choice skips a choice of the other player.
#[test]
fn edges_that_are_not_union_chords_stay_refused() {
    let cases = [
        (&FOUR[..], (2, 0)),
        (&FOUR, (1, 0)),
        (&SIX, (0, 4)),
        (&SIX, (2, 4)),
        (&SIX, (2, 5)),
        (&SIX, (1, 4)),
    ];
    for (kinds, edge) in cases {
        let g = ring(kinds, &[edge], &EXITS);
        let label = format!("{kinds:?} with {edge:?}");
        checked(&label, &g);
        let d = decide(&g.bes());
        let r = (d.refusals.first()).unwrap_or_else(|| panic!("{label}: not refused"));
        assert!(r.cyclomatic >= 2 && r.branching_and >= 1, "{label}: {r:?}");
    }
}

/// Random rings of unions and tuples with random morphism children and random union edges,
/// most along the cycle and some not: every answer matches the Büchi reference and does not
/// depend on numbering, and a ring whose added edges all run along the cycle is not refused
/// (3318 of 20000 rings of the old fixed seed had such edges; 329 of those were refused before
/// the item).
///
/// It ran 20,000 rings drawn from one fixed xorshift seed (0.52 s alone); now it runs 5,000
/// rings drawn from a new seed each run, printed (TEST-bench-move-l0123, author P169: random
/// tests run fewer cases). The draws and checks on each ring are as before. The shares of rings
/// along the cycle and of those with added edges, measured at about 0.29 and 0.16, are printed
/// and no longer held to a bound; a ring built with an added edge along the cycle is checked on
/// every run instead (PROOF-test-count-thresholds).
#[test]
fn random_rings_with_union_chords_are_decided_right() {
    let (mut rng, seed) = zed_tests::instances::Rng::fresh("rings with union chords");
    let mut rnd = |m: usize| rng.below(m);
    // The places from place `i` to the first tuple along the ring of `kinds`, its length if
    // there is none.
    let ahead = |kinds: &[K], i: usize| {
        let n = kinds.len();
        (0..n).find(|&k| kinds[(i + k) % n] != K::Or).unwrap_or(n)
    };
    // Checks the ring and returns whether its added edges all run along the cycle: each edge
    // `v -> w` leaves a union, and `w` lies within the unions from `v`'s successor `s` to the
    // first tuple after it, and is not `v`.
    let check = |kinds: &[K], extra: &[(usize, usize)], mors: &[(usize, usize)], run: &str| {
        let n = kinds.len();
        let chords_only = extra.iter().all(|&(v, w)| {
            let s = (v + 1) % n;
            let d = (w + n - s) % n;
            w != v && d <= ahead(kinds, s) && ahead(kinds, s) < n
        });
        let g = ring(kinds, extra, mors);
        let label = format!("{run}: {kinds:?} edges {extra:?} morphisms {mors:?}");
        let refused = checked(&label, &g);
        let a = decide(&g.bes()).answers;
        let mut b = decide(&reversed(&g).bes()).answers;
        b.reverse();
        assert_eq!(a, b, "{label}: answers depend on numbering");
        if chords_only {
            assert_eq!(refused, 0, "{label}: refused");
        }
        chords_only
    };
    let (mut rings, mut along, mut kept) = (0, 0, 0);
    for _ in 0..5_000 {
        let n = 2 + rnd(10);
        let kinds: Vec<K> = (0..n)
            .map(|_| if rnd(3) == 0 { K::And } else { K::Or })
            .collect();
        let mors: Vec<(usize, usize)> = (0..rnd(4)).map(|_| (rnd(n), rnd(n))).collect();
        let mut extra = Vec::new();
        for (v, &kind) in kinds.iter().enumerate() {
            if kind != K::Or || rnd(2) == 0 {
                continue;
            }
            let s = (v + 1) % n;
            let w = if rnd(4) == 0 {
                rnd(n)
            } else {
                (s + 1 + rnd(ahead(&kinds, s).clamp(1, n - 1))) % n
            };
            extra.push((v, w));
        }
        rings += 1;
        if check(&kinds, &extra, &mors, &format!("ZED_TEST_SEED={seed}")) {
            along += 1;
            kept += usize::from(!extra.is_empty());
        }
    }
    eprintln!(
        "ZED_TEST_SEED={seed}: {along} rings along the cycle, {kept} with added edges, of {rings}"
    );
    // A ring with an added edge along the cycle on every run, built (PROOF-test-count-thresholds):
    // in `[Or, Or, And]` the edge `0 -> 2` leaves the union 0, whose successor 1 is a union with
    // the tuple 2 one place ahead, so the edge reaches `w = 2` at distance 1, no more than that
    // one place, and is along the cycle; the check then asserts the ring is not refused.
    let built = check(&[K::Or, K::Or, K::And], &[(0, 2)], &[], "built");
    assert!(built, "the built ring runs along the cycle");
}

/// A ring of `n` unions and a tuple, with the morphism children of [`FOUR`] (the tuple to the
/// first union, the first union to the tuple) and a union edge from each union but the last two
/// to the last: every edge runs along the cycle, the longest across `n - 2` unions.
fn long_run(n: usize) -> G {
    let mut kinds = vec![K::Or; n];
    kinds.push(K::And);
    let extra: Vec<(usize, usize)> = (0..n - 2).map(|v| (v, n - 1)).collect();
    ring(&kinds, &extra, &[(n, 0), (0, n)])
}

/// [`long_run`] is one cycle, decided right and the same however numbered.
#[test]
fn a_long_run_of_union_edges_is_one_cycle() {
    for n in [3, 4, 10, 100] {
        let g = long_run(n);
        let label = format!("a run of {n} unions");
        assert_eq!(checked(&label, &g), 0, "{label}: refused");
        let a = decide(&g.bes()).answers;
        let mut b = decide(&reversed(&g).bes()).answers;
        b.reverse();
        assert_eq!(a, b, "{label}: answers depend on numbering");
    }
}

mod bench;

/// Four tuple cycles, `C0` (`x0 y0 z0`), `C1` (`x y1 z1`), `C2` (`a b c`) and `C3` (`d e f`),
/// none with a way out, so every node is empty: a value is finite, and a morphism type whose
/// value type is empty is empty. `C0` feeds `C1` through the union `u` over the morphism
/// `m0 = (…) -> x0`, `C1` feeds `C2` through the union `w` over `m = (…) -> x`, and `C2`
/// alone feeds `C3`, through `d`'s child `a`; the morphisms `p1`..`p4` back to `a` and `q`
/// from `b` to `d` put `C2` and `C3` in one component. The deletion cascade receives `C2`,
/// which nothing outside it feeds, and `C3`, whose one seed is `a`: it kills `C2` at its
/// start, and the death of `a` leaves `C3` without its seed, which kills `C3` too (item
/// TEST-types-unreached-paths: before it, no test reached either kill). Without the kills no
/// node the cascade decides here would die, and each would be inhabited.
#[test]
fn a_cycle_left_without_a_seed_is_killed_by_the_cascade() {
    let mut g = G::new();
    // Places: x0 y0 z0 m0 u x y1 z1 m w a b c p1 p2 p3 d e f p4 q.
    let x0 = g.add(K::Or, vec![1]);
    g.add(K::And, vec![2, 15]);
    g.add(K::Or, vec![x0]);
    g.add(K::Mor, vec![x0]);
    g.add(K::Or, vec![3]);
    let x = g.add(K::Or, vec![6, 4]);
    g.add(K::And, vec![7, 14]);
    g.add(K::Or, vec![x]);
    g.add(K::Mor, vec![x]);
    g.add(K::Or, vec![8]);
    let a = g.add(K::Or, vec![9, 11]);
    g.add(K::And, vec![12, 13, 20]);
    g.add(K::Or, vec![a, x]);
    for _ in 0..3 {
        g.add(K::Mor, vec![a]);
    }
    let d = g.add(K::Or, vec![17, a]);
    g.add(K::And, vec![18, 19]);
    g.add(K::Or, vec![d]);
    g.add(K::Mor, vec![a]);
    g.add(K::Mor, vec![d]);
    g.seal();
    let got = decide(&g.bes());
    assert!(got.refusals.is_empty(), "{:?}", got.refusals);
    assert_eq!(got.answers, vec![Answer::Empty; 21]);
    assert_eq!(checked("four cycles", &g), 0);
    assert_eq!(checked("four cycles reversed", &reversed(&g)), 0);
}
