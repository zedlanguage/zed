//! A graph nested 100,000 deep, whose deepest region matches a value against a pattern that
//! binds a written name: the canonicalizer renames the binder, normalizes, ranks and keys the
//! graph on a thread of the default 2 MiB stack, in time linear in its depth.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::canon::{address, canonicalize, key, ranks, step};
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src};

use crate::l01_31_zir::scaling::nested_ifs;

/// [`nested_ifs`] with the deepest `then` region holding `match 0 { binder => binder }`.
fn deep_match(depth: usize, binder: &str) -> Region {
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
fn a_graph_nested_100000_deep_is_canonicalized_on_a_2_mib_stack() {
    on_small_stack(|| {
        let mut g = deep_match(100_000, "x");
        assert_eq!(ranks(&g)[0], 1, "one written binder");
        assert_eq!(address(&g), address(&deep_match(100_000, "y")));
        assert_eq!(
            key(&canonicalize(&g)),
            key(&canonicalize(&deep_match(100_000, "y")))
        );
        let normal = canonicalize(&g);
        while step(&mut g).is_some() {}
        assert_eq!(g, normal);
    });
}

#[test]
fn canonicalizing_a_deep_graph_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (deep_match(12_500, "x"), deep_match(100_000, "x"));
        let pick = |k| if k == 12_500 { &small } else { &large };
        check_order("canonicalizing nested `if` regions", 12_500, 1, |k| {
            canonicalize(pick(k));
        });
        check_order("keying nested `if` regions", 12_500, 1, |k| {
            key(pick(k));
        });
        check_order("ranking nested `if` regions", 12_500, 1, |k| {
            ranks(pick(k));
        });
        check_order(
            "renaming the binder of nested `if` regions",
            12_500,
            1,
            |k| {
                let mut g = pick(k).clone();
                while step(&mut g).is_some() {}
            },
        );
    });
}
