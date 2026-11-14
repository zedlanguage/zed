//! A graph nested 20,000 deep, whose deepest region matches a value against a pattern that
//! binds a written name: the canonicalizer renames the binder, normalizes, ranks and keys the
//! graph on a thread of the default 2 MiB stack, in time linear in its depth. An edge of many
//! facets in reverse order is canonicalized and keyed in `O(F log F)`, its facets sorted once.
//! The benchmarks in `bench/scaling.rs` hold both orders; here each is checked at small sizes.
//! A plain recursion takes at least 112 bytes a level (measured at opt-level 2), so 20,000
//! levels, 2.2 MB, would overflow the 2 MiB stack.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zedc::canon::Facet;
use zedc::zir::canon::{address, canonicalize, key, ranks, step};
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src};

use zed_tests::step_helpers::l01_31_zir::nested_ifs;

/// [`nested_ifs`] with the deepest `then` region holding `match 0 { binder => binder }`.
pub(super) fn deep_match(depth: usize, binder: &str) -> Region {
    let mut g = nested_ifs(depth);
    let mut r = &mut g;
    while !r.nodes.is_empty() {
        r = Arc::get_mut(&mut r.nodes[0].regions[0]).expect("the graph is not shared");
    }
    let int = Edge::value(Type::int());
    let arm = Region {
        kind: RegionKind::Match,
        args: vec![int.clone()],
        nodes: Vec::new(),
        results: vec![Src::Arg(0)],
    };
    r.nodes = vec![Node {
        op: Op::Match(vec![Pattern::Bind(binder.into())]),
        inputs: vec![Src::Const(Value::Int(0))],
        outputs: vec![int],
        regions: vec![Arc::new(arm)],
    }];
    r.results = vec![Src::Out(0, 0)];
    g
}

#[test]
fn a_graph_nested_20000_deep_is_canonicalized_on_a_2_mib_stack() {
    on_small_stack(|| {
        let mut g = deep_match(20_000, "x");
        assert_eq!(ranks(&g)[0], 1, "one written binder");
        assert_eq!(
            address(&g).expect("memory for the address"),
            address(&deep_match(20_000, "y")).expect("memory for the address")
        );
        assert_eq!(
            key(&canonicalize(&g)).expect("memory for the key"),
            key(&canonicalize(&deep_match(20_000, "y"))).expect("memory for the key")
        );
        let normal = canonicalize(&g);
        while step(&mut g).is_some() {}
        assert_eq!(g, normal);
    });
}

/// A function region whose one argument is an `int` with `n` facets in reverse order: units
/// and locales, each value twice, and every third facet a hint.
pub(super) fn many_facets(n: usize) -> Region {
    let facets = (0..n).rev().map(|i| Facet {
        hint: i % 3 == 0,
        kind: if i % 2 == 0 { "units" } else { "locale" }.into(),
        value: Value::Int(i as i64 / 4),
    });
    let mut arg = Edge::value(Type::int());
    if let Edge::Value(v) = &mut arg {
        v.facets = facets.collect();
    }
    Region {
        kind: RegionKind::Function,
        args: vec![arg],
        nodes: Vec::new(),
        results: vec![Src::Arg(0)],
    }
}

/// The edge of `g`'s argument, canonicalized: its facets strictly sorted and none a hint.
pub(super) fn sorts_its_facets(g: &Region) {
    let g = canonicalize(g);
    let Edge::Value(v) = &g.args[0] else {
        panic!("a value edge")
    };
    assert!(v.facets.windows(2).all(|w| w[0] < w[1]));
    assert!(v.facets.iter().all(|f| !f.hint));
}

/// A shallow graph is canonicalized, keyed and ranked, and its binder renamed to the normal form;
/// the time of each is held linear in its depth in `bench/scaling.rs`.
#[test]
fn a_shallow_graph_is_canonicalized_keyed_and_ranked() {
    for d in [1, 2, 9] {
        let mut g = deep_match(d, "x");
        assert_eq!(ranks(&g)[0], 1, "one written binder");
        let y = deep_match(d, "y");
        assert_eq!(
            address(&g).expect("memory for the address"),
            address(&y).expect("memory for the address")
        );
        assert_eq!(
            key(&canonicalize(&g)).expect("memory for the key"),
            key(&canonicalize(&y)).expect("memory for the key")
        );
        key(&g).expect("memory for the key");
        let normal = canonicalize(&g);
        while step(&mut g).is_some() {}
        assert_eq!(g, normal);
    }
}

/// An edge of a few facets in reverse order is canonicalized with its facets sorted and keyed;
/// the time is held to `O(F log F)` in `bench/scaling.rs`.
#[test]
fn an_edge_of_a_few_facets_is_sorted_and_keyed() {
    for n in [0, 1, 2, 9] {
        let g = many_facets(n);
        sorts_its_facets(&g);
        key(&g).expect("memory for the key");
    }
}
