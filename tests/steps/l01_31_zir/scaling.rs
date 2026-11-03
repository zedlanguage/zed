//! Graphs nested 100,000 deep: an `if` whose `then` region holds the next `if`, as a chain of
//! `else if` branches lowers. Each pass over the graph keeps its own stack on the heap, so such
//! a graph is checked, compared, written and read back on a thread of the default 2 MiB stack,
//! in time linear in its depth.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, validate};

/// `if true then (if true then ... 0 else 0) else 0`, `depth` branches deep, built from the
/// bottom up.
pub(crate) fn nested_ifs(depth: usize) -> Region {
    let region = |kind, nodes, results| Region {
        kind,
        args: Vec::new(),
        nodes,
        results,
    };
    let zero = || {
        region(
            RegionKind::Match,
            Vec::new(),
            vec![Src::Const(Value::Int(0))],
        )
    };
    let branch = |then: Region| Node {
        op: Op::If,
        inputs: vec![Src::Const(Value::Bool(true))],
        outputs: vec![Edge::value(Type::int())],
        regions: vec![Arc::new(then), Arc::new(zero())],
    };
    let mut arm = zero();
    for _ in 1..depth {
        arm = region(RegionKind::Match, vec![branch(arm)], vec![Src::Out(0, 0)]);
    }
    region(
        RegionKind::Function,
        vec![branch(arm)],
        vec![Src::Out(0, 0)],
    )
}

#[test]
fn a_graph_nested_100000_deep_is_checked_compared_and_freed_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = nested_ifs(100_000);
        validate(&g).unwrap();
        assert_eq!(g, nested_ifs(100_000));
        assert_ne!(g, nested_ifs(99_999));
    });
}

#[test]
fn an_error_deep_in_a_graph_is_named_by_its_path() {
    on_small_stack(|| {
        let mut g = nested_ifs(3);
        let then = Arc::get_mut(&mut g.nodes[0].regions[0]).expect("the graph is not shared");
        let inner = Arc::get_mut(&mut then.nodes[0].regions[0]).expect("not shared");
        inner.results = vec![Src::Arg(0)];
        assert_eq!(
            validate(&g).unwrap_err(),
            "r.0/0.0/0: result 0: r.0/0.0/0^0: the region has 0 arguments, numbered from 0"
        );
    });
}

#[test]
fn checking_a_deep_graph_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        let twins = (nested_ifs(12_500), nested_ifs(100_000));
        check_order("checking nested `if` regions", 12_500, 1, |k| {
            validate(if k == 12_500 { &small } else { &large }).unwrap();
        });
        check_order("comparing nested `if` regions", 12_500, 1, |k| {
            let (g, h) = if k == 12_500 {
                (&small, &twins.0)
            } else {
                (&large, &twins.1)
            };
            assert!(g == h);
        });
    });
}
