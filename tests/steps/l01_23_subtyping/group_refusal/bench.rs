//! The benchmarks of `group_refusal.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `group_refusal.rs`.

use super::*;

/// A group of n copies of the component and n lists apart: the verdict of every member and the
/// message of every refused one, at n and 8n, within the limit of the scaling test; the lists
/// stay decided by the decider.
#[test]
fn a_group_of_refused_components_scales() {
    let n = 64;
    Type::forget_emptiness();
    let types = group(copies(n));
    assert!(
        types[SIZE * n..]
            .iter()
            .all(|t| t.decided_by_group() == Some(false))
    );
    assert!((types[..SIZE * n].iter()).all(|t| t.verdict() == Verdict::Refused(Refusal::Group)));
    scaling::check_order("refused components and lists, n copies", n, 1, |n| {
        Type::forget_emptiness();
        let types = group(copies(n));
        for t in &types {
            std::hint::black_box(t.verdict());
        }
        for t in &types[..SIZE * n] {
            std::hint::black_box(t.refusal_site(Refusal::Group));
        }
    });
}

/// m refused members that share one decided part of n definitions: their messages together
/// cost O(m + n), not O(m n), at (m, n) and (8m, 8n), since the re-check of the repair does not
/// walk the decided part again for each member (COMPLEXITY.md K85).
#[test]
fn refused_members_sharing_a_decided_part_scale() {
    let n = 128;
    Type::forget_emptiness();
    let types = group(boxes(n, n));
    assert!((types[SIZE..SIZE + n].iter()).all(|t| t.decided_by_group() == Some(false)));
    for t in &types[SIZE + n..] {
        assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
        let site = t.refusal_site(Refusal::Group).expect("a refused member");
        assert!(site.head.starts_with("Box"), "{site:?}");
        // The definitions alone: `B` writes its `(_, _)` in full (MSG-derive-type-size).
        assert_eq!(site.defs.len(), SIZE + 1, "{site:?}");
    }
    scaling::check_order("m refused members sharing a decided part of n", n, 1, |n| {
        Type::forget_emptiness();
        let types = group(boxes(n, n));
        for t in &types[SIZE + n..] {
            std::hint::black_box(t.refusal_site(Refusal::Group));
        }
    });
}

/// m refused members, each reaching n nodes that each reach another refused component:
/// their messages together cost O(m + n) at (m, n) and (8m, 8n) (GROUP-refusal-reach). The
/// message of each names only the definitions its refusal rests on, those of `A0`'s copy.
#[test]
fn refused_members_reaching_many_refused_components_scale() {
    let n = 64;
    Type::forget_emptiness();
    let types = group(reach(n, n));
    let opt = SIZE * n;
    assert!((types[..opt].iter()).all(|t| t.verdict() == Verdict::Refused(Refusal::Group)));
    assert!(
        (types[opt..opt + n].iter())
            .all(|t| (t.decided_by_group(), t.verdict()) == (None, Verdict::Inhabited))
    );
    for t in &types[opt + n..] {
        assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
        let site = t.refusal_site(Refusal::Group).expect("a refused member");
        assert!(site.head.starts_with("Box"), "{site:?}");
        // The definitions alone: `B` writes its `(_, _)` in full (MSG-derive-type-size).
        assert_eq!(site.defs.len(), SIZE + 1, "{site:?}");
    }
    scaling::check_order(
        "m refused members reaching n refused components",
        n,
        1,
        |n| {
            Type::forget_emptiness();
            let types = group(reach(n, n));
            for t in &types[SIZE * n + n..] {
                std::hint::black_box(t.refusal_site(Refusal::Group));
            }
        },
    );
}

/// Deciding every member of the ladder of `n` definitions, which the search decides where the
/// decider refuses, at n and 8n, within the limit of the scaling test.
#[test]
fn the_refused_ladder_scales() {
    scaling::check("the ladder the decider refuses, n definitions", 32, |n| {
        Type::forget_emptiness();
        for t in &group(ladder(n, false)) {
            std::hint::black_box(t.verdict());
        }
    });
}
