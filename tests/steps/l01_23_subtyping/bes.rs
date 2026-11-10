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
    // Inputs are built before timing.
    let small = family(name, n).bes();
    let large = family(name, scaling::FACTOR * n).bes();
    scaling::check_order(&format!("deciding {name}"), n, 1, |m| {
        let g = if m == n { &small } else { &large };
        std::hint::black_box(decide(std::hint::black_box(g)));
    });
}

#[test]
fn the_families_scale() {
    for name in FAMILIES {
        scales(name, 512);
    }
}

#[test]
fn the_widened_families_scale() {
    for name in WIDENED {
        scales(name, 4096);
    }
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
/// (3318 of the 20000 rings have such edges; 329 of those were refused before the item).
#[test]
fn random_rings_with_union_chords_are_decided_right() {
    let mut x: u64 = 0x2545_F491_4F6C_DD1D;
    let mut rnd = move |m: usize| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        (x % m as u64) as usize
    };
    let (mut rings, mut along, mut kept) = (0, 0, 0);
    for _ in 0..20_000 {
        let n = 2 + rnd(10);
        let kinds: Vec<K> = (0..n)
            .map(|_| if rnd(3) == 0 { K::And } else { K::Or })
            .collect();
        // The places from place `i` to the first tuple along the ring, `n` if there is none.
        let ahead = |i: usize| (0..n).find(|&k| kinds[(i + k) % n] != K::Or).unwrap_or(n);
        let mors: Vec<(usize, usize)> = (0..rnd(4)).map(|_| (rnd(n), rnd(n))).collect();
        let (mut extra, mut chords_only) = (Vec::new(), true);
        for (v, &kind) in kinds.iter().enumerate() {
            if kind != K::Or || rnd(2) == 0 {
                continue;
            }
            let s = (v + 1) % n;
            let w = if rnd(4) == 0 {
                rnd(n)
            } else {
                (s + 1 + rnd(ahead(s).clamp(1, n - 1))) % n
            };
            let d = (w + n - s) % n;
            chords_only &= w != v && d <= ahead(s) && ahead(s) < n;
            extra.push((v, w));
        }
        let g = ring(&kinds, &extra, &mors);
        rings += 1;
        let label = format!("{kinds:?} edges {extra:?} morphisms {mors:?}");
        let refused = checked(&label, &g);
        let a = decide(&g.bes()).answers;
        let mut b = decide(&reversed(&g).bes()).answers;
        b.reverse();
        assert_eq!(a, b, "{label}: answers depend on numbering");
        if chords_only {
            along += 1;
            assert_eq!(refused, 0, "{label}: refused");
            kept += usize::from(!extra.is_empty());
        }
    }
    assert!(
        along > rings / 4 && kept > rings / 8,
        "{along} {kept} of {rings}"
    );
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

/// Deciding [`long_run`] of `n` and `8n` unions: the test of union edges reads each edge once,
/// with the run of unions after each node counted once (`bes::one_cycle_but_union_chords`),
/// where walking each edge along the cycle would take `n` steps an edge.
#[test]
fn a_long_run_of_union_edges_scales() {
    let n = 4096;
    let small = long_run(n).bes();
    let large = long_run(scaling::FACTOR * n).bes();
    scaling::check_order("deciding a run of n unions with union edges", n, 1, |m| {
        let g = if m == n { &small } else { &large };
        std::hint::black_box(decide(std::hint::black_box(g)));
    });
}
