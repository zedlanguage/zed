//! The decider of recursive groups' inhabitation (cross-review X14, `split_bdw2`), on the
//! graph families it was measured with: every answer it gives matches the classical Büchi
//! game reference, answers do not depend on how nodes are numbered, and its work grows
//! linearly, also when one node is widened (the widened variants made the first version,
//! which counted distinct children by searching a list, quadratic).

use super::bes_families::{FAMILIES, G, family, reference};
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
fn checked(name: &str, g: &G) -> usize {
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
fn reversed(g: &G) -> G {
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
