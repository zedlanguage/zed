//! ZIR helpers of step L1.31 (tests/steps/l01_31_zir).

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src};

/// `if true then (if true then ... 0 else 0) else 0`, `depth` branches deep, built from the
/// bottom up.
pub fn nested_ifs(depth: usize) -> Region {
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
