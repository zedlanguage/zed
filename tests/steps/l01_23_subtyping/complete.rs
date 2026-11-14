//! Completeness cases for L1.23 (TEST-complete-types, COMPLETENESS.md): systems that reach a
//! step of the group decider (`zed_kernel::types::bes::decide`) no family and no seeded sweep of
//! `group_oracle` reaches. Every decided answer must match the Büchi game reference.

use super::bes_families::{self, reference};
use zed_kernel::types::bes::{Answer, Bes, Kind, decide};

/// Step 4 of the decider: after the bounds, the undecided nodes split into components, and one
/// of them has no tuple cycle left, or no morphism type inside, so it is settled by one fixed
/// point (`settle` in the loop over `r_scc`). Found by a coverage sweep of 16 000 seeds at
/// sizes 34 and 55; these are the two systems of that sweep that reach it.
#[test]
fn an_undecided_component_without_a_tuple_cycle_is_settled_by_one_fixed_point() {
    for (seed, rate, n) in [(1614, 3, 55), (1414, 7, 55)] {
        let g = bes_families::random(seed, rate, n);
        let want = reference::answers(&g);
        let got = decide(&g.bes()).answers;
        assert_eq!(got.len(), want.len());
        for (v, (a, w)) in got.iter().zip(&want).enumerate() {
            let at = format!("random({seed}, {rate}, {n}): node {v}");
            match a {
                Answer::Empty => assert!(!w, "{at} decided empty, is inhabited"),
                Answer::Inhabited => assert!(w, "{at} decided inhabited, is empty"),
                Answer::Refused => panic!("{at} refused; this system has no refused shape"),
            }
        }
    }
}

/// A system with no node has no answer; one with a node is not empty and answers it.
#[test]
fn a_system_with_no_node_has_no_answer() {
    let mut g = Bes::new();
    assert!(g.is_empty());
    assert_eq!(g.len(), 0);
    assert!(decide(&g).answers.is_empty());
    g.add(Kind::Top, Vec::new());
    assert!(!g.is_empty());
    assert!(matches!(decide(&g).answers[..], [Answer::Inhabited]));
}
