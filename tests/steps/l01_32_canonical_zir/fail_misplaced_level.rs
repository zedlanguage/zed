//! FAIL-zir-canon-misplaced-level-binder (TEST-complete-zir, author P189). Drop into
//! tests/steps/l01_32_canonical_zir/ as a module (`mod fail_misplaced_level;` in mod.rs) once
//! the canonicalizer in crates/zedc-zir/src/zir/canon.rs is fixed.
//!
//! DESIGN L1.32: "α-invariant content addressing — test: … address stability under renaming";
//! M0.7: the binder rule renames each binder to its level. A match arm reads its binders by
//! position, so two patterns that differ only in their binders' names are the same graph and
//! must share one address. The canonicalizer keeps any binder already spelled as a level
//! (`$$k`), at whatever position it stands, so `($$5, y)` and `($$1, $$0)` keep a level that
//! is not their position's, and get addresses different from `(a, y)`.

use zedc::zir::canon::{address, canonicalize, key, ranks, step};
use zedc::zir::text::{parse, pattern};

#[test]
fn a_binder_spelled_as_the_wrong_level_is_renamed_to_its_own() {
    let pair = |p: &str| {
        let src = format!(
            "zir 1\nr region function (tuple)\nr.0 match [{p}] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
        );
        address(&parse(&src).expect("the graph reads")).expect("memory for the address")
    };
    let want = pair("(a, y)");
    let wrong: Vec<&str> = ["($$5, y)", "($$1, $$0)", "($$1, y)", "(a, $$0)"]
        .into_iter()
        .filter(|p| pair(p) != want)
        .collect();
    assert!(
        wrong.is_empty(),
        "addresses differ from `(a, y)`'s for {wrong:?}"
    );
}

/// The match of `p` over a pair of integers whose arm adds its two binders.
fn pair_graph(p: &str) -> zedc::zir::Region {
    parse(&format!(
        "zir 1\nr region function (tuple)\nr.0 match [{p}] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
    ))
    .expect("the graph reads")
}

/// The patterns of the first node of the normal form of `g`, as text.
fn normal_patterns(g: &zedc::zir::Region) -> Vec<String> {
    let zedc::zir::Op::Match(ps) = &canonicalize(g).nodes[0].op else {
        panic!("a match")
    };
    ps.iter().map(pattern).collect()
}

/// A binder spelled as another level is renamed by the one pass, by the steps (which count it
/// in the binder rule's rank and reach the one pass's graph) and by the node key; a binder
/// spelled as its own level is left alone, and nested patterns count their binders in preorder.
#[test]
fn neighbors_of_the_misplaced_level() {
    // The one pass gives each binder its own level.
    for p in [
        "($$5, $$1)",
        "($$1, $$0)",
        "(a, $$0)",
        "($$0, $$1)",
        "(a, y)",
    ] {
        assert_eq!(normal_patterns(&pair_graph(p)), ["($$0, $$1)"], "{p}");
    }
    // The binder rule's rank counts the misplaced ones and not the placed ones, and the steps
    // reach the one pass's graph.
    for (p, written) in [
        ("($$5, $$1)", 1),
        ("($$1, $$0)", 2),
        ("($$0, $$1)", 0),
        ("(a, $$1)", 1),
    ] {
        let g = pair_graph(p);
        assert_eq!(ranks(&g)[0], written, "{p}");
        let mut s = g.clone();
        while step(&mut s).is_some() {}
        assert_eq!(s, canonicalize(&g), "{p}");
    }
    // The node key, which the lowering numbers nodes by, agrees.
    let k = |p: &str| key(&pair_graph(p)).expect("memory for the key");
    assert_eq!(k("($$1, $$0)"), k("(a, y)"));
    // Nested: an atom's fields and a tuple inside a tuple count binders in preorder.
    let nested = |p: &str| {
        parse(&format!(
            "zir 1\nr region function (tuple)\nr.0 match [{p}] (r^0) -> (int)\nr.0/0 region match (int; int; int)\nr.0/0 results (r.0/0^2)\nr results (r.0^0)\n"
        ))
        .expect("the graph reads")
    };
    let want = address(&nested("(#a(x), (y, z))")).expect("memory for the address");
    for p in [
        "(#a($$2), ($$0, $$1))",
        "(#a($$0), ($$2, $$2))",
        "(#a(x), ($$0, z))",
    ] {
        assert_eq!(address(&nested(p)).expect("memory"), want, "{p}");
        assert_eq!(
            normal_patterns(&nested(p)),
            ["(#a($$0), ($$1, $$2))"],
            "{p}"
        );
    }
    // A control: changing which binder an arm reads still changes the address.
    let reads_first = parse(
        "zir 1\nr region function (tuple)\nr.0 match [(a, y)] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
    )
    .expect("the graph reads");
    let reads_second = parse(
        "zir 1\nr region function (tuple)\nr.0 match [(a, y)] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0 results (r.0/0^1)\nr results (r.0^0)\n",
    )
    .expect("the graph reads");
    assert_ne!(
        address(&reads_first).expect("memory"),
        address(&reads_second).expect("memory")
    );
}
