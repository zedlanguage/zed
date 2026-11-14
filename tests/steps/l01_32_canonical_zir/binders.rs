//! The binder rule on each pattern form and each place a match can stand (DESIGN M0.7, L1.32):
//! the first written binder in preorder is renamed to its level among its pattern's binders,
//! its written name a hint that the hints rule then drops; the one pass and the steps agree.

use super::graph;
use zedc::zir::canon::{address, canonicalize, ranks, step};
use zedc::zir::text::{pattern, print};
use zedc::zir::{Edge, Op, Region};

/// The rules' names in the order the steps apply them to `g`, and the graph they reach, which
/// must be the one pass's.
fn steps(g: &Region) -> Vec<&'static str> {
    let mut s = g.clone();
    let mut names = Vec::new();
    while let Some(n) = step(&mut s) {
        names.push(n);
    }
    assert_eq!(s, canonicalize(g), "the steps reach the one pass's graph");
    names
}

/// The patterns of the first node of `g`'s normal form, as text.
fn normal_patterns(g: &Region) -> Vec<String> {
    let Op::Match(ps) = &canonicalize(g).nodes[0].op else {
        panic!("a match")
    };
    ps.iter().map(pattern).collect()
}

/// A match of `#none` and a fields pattern `p` that binds two integers; the second arm's first
/// argument carries a hint.
fn fields(p: &str) -> Region {
    graph(&format!(
        "zir 1\nr region function ((| #none #c))\nr.0 match [#none, {p}] (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (0)\nr.0/1 region match (int hint name \"q\"; int)\nr.0/1.0 prim - (r.0/1^0, r.0/1^1) -> (int)\nr.0/1 results (r.0/1.0^0)\nr results (r.0^0)\n"
    ))
}

#[test]
fn a_fields_pattern_s_binders_are_renamed_in_field_order() {
    let a = fields("#c(x: m, y: n)");
    assert_eq!(address(&a), address(&fields("#c(x: lo, y: hi)")));
    assert_eq!(normal_patterns(&a), ["#none", "#c(x: $$0, y: $$1)"]);
    // Two binders renamed, then three hints dropped: the written one and the two the binder
    // rule made, each on the argument its binder binds.
    assert_eq!(steps(&a), ["binders", "binders", "hints", "hints", "hints"]);
    let mut once = a.clone();
    step(&mut once);
    let Edge::Value(v) = &once.nodes[0].regions[1].args[0] else {
        panic!("a value edge")
    };
    assert_eq!(
        v.facets.iter().filter(|f| f.hint).count(),
        2,
        "{}",
        print(&once)
    );
    assert_eq!(ranks(&canonicalize(&a)), [0, 0, 0, 0]);
}

#[test]
fn a_wildcard_or_a_literal_takes_no_level() {
    let one = |p: &str| {
        graph(&format!(
            "zir 1\nr region function ((| #none #c))\nr.0 match [#none, {p}] (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (0)\nr.0/1 region match (int)\nr.0/1 results (r.0/1^0)\nr results (r.0^0)\n"
        ))
    };
    assert_eq!(
        normal_patterns(&one("#c(x: _, y: n)")),
        ["#none", "#c(x: _, y: $$0)"]
    );
    assert_eq!(
        normal_patterns(&one("#c(x: =1, y: n)")),
        ["#none", "#c(x: =1, y: $$0)"]
    );
    assert_eq!(steps(&one("#c(x: _, y: n)")), ["binders", "hints"]);
    // Which field the binder is under changes the graph.
    assert_ne!(
        address(&one("#c(x: _, y: n)")),
        address(&one("#c(x: n, y: _)"))
    );
}

#[test]
fn binders_nested_in_a_field_count_in_preorder() {
    let g = fields("#c(x: (p, q), y: _)");
    assert_eq!(address(&g), address(&fields("#c(x: (a, b), y: _)")));
    assert_eq!(normal_patterns(&g), ["#none", "#c(x: ($$0, $$1), y: _)"]);
    let g = fields("#c(x: #d(p), y: q)");
    assert_eq!(normal_patterns(&g), ["#none", "#c(x: #d($$0), y: $$1)"]);
}

#[test]
fn each_arm_counts_its_binders_from_0() {
    let g = |a: &str, b: &str| {
        graph(&format!(
            "zir 1\nr region function ((| (#a (tuple int)) (#b (tuple int int))))\nr.0 match [#a({a}), #b(_, {b})] (r^0) -> (int)\nr.0/0 region match (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region match (int)\nr.0/1 results (r.0/1^0)\nr results (r.0^0)\n"
        ))
    };
    assert_eq!(normal_patterns(&g("x", "y")), ["#a($$0)", "#b(_, $$0)"]);
    assert_eq!(address(&g("x", "y")), address(&g("u", "u")));
    assert_eq!(
        steps(&g("x", "y")),
        ["binders", "binders", "hints", "hints"]
    );
}

#[test]
fn a_match_inside_a_match_arm_is_renamed_too() {
    let g = |a: &str, b: &str| {
        graph(&format!(
            "zir 1\nr region function ((| #none (#some (tuple tuple))))\nr.0 match [#some({a}), #none] (r^0) -> (int)\nr.0/0 region match (tuple)\nr.0/0.0 match [({b}, _)] (r.0/0^0) -> (int)\nr.0/0.0/0 region match (int)\nr.0/0.0/0 results (r.0/0.0/0^0)\nr.0/0 results (r.0/0.0^0)\nr.0/1 region match ()\nr.0/1 results (0)\nr results (r.0^0)\n"
        ))
    };
    let n = canonicalize(&g("pair", "first"));
    let Op::Match(inner) = &n.nodes[0].regions[0].nodes[0].op else {
        panic!("a match")
    };
    // Each pattern counts its own binders: the inner one's first binder is level 0 as well.
    assert_eq!(pattern(&inner[0]), "($$0, _)");
    assert_eq!(address(&g("pair", "first")), address(&g("p", "f")));
    assert_eq!(
        steps(&g("pair", "first")),
        ["binders", "binders", "hints", "hints"]
    );
}

#[test]
fn canonical_binders_are_already_normal() {
    let pair = |p: &str| {
        graph(&format!(
            "zir 1\nr region function (tuple)\nr.0 match [{p}] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
        ))
    };
    let normal = pair("($$0, $$1)");
    assert_eq!(steps(&normal), Vec::<&str>::new());
    assert_eq!(canonicalize(&normal), normal);
    assert_eq!(address(&normal), address(&pair("(a, y)")));
    // A written binder after a canonical one counts it.
    assert_eq!(steps(&pair("($$0, y)")), ["binders", "hints"]);
    assert_eq!(address(&pair("($$0, y)")), address(&pair("(a, y)")));
}

#[test]
fn a_graph_with_no_match_has_nothing_for_the_binder_rule() {
    let g = graph(
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, \"hi\") -> (_; state out)\nr results (r.0^1)\n",
    );
    assert_eq!(ranks(&g), [0, 0, 0, 0]);
    assert_eq!(steps(&g), Vec::<&str>::new());
    // A state edge has no facts, and is left alone.
    assert_eq!(canonicalize(&g), g);
}
