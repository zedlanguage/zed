//! Lowering helpers of step L1.33 (tests/steps/l01_33_lowering).

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, World};
use zedc::zir::Region;
use zedc::zir::lower::{lower, raise};

/// The value of `t` with no ports, printed, or its error.
pub fn eval(t: &Term) -> Result<String, String> {
    Evaluator::new(World::new())
        .run(t)
        .map(|v| v.to_string())
        .map_err(|e| e.to_string())
}

/// The value of `t` lowered and raised back.
pub fn round_trip(t: &Term) -> Result<String, String> {
    let g = lower(t)?;
    eval(&raise(&g)?)
}

/// The number of nodes of `g` and its regions whose operation is named `op`.
pub fn count(g: &Region, op: &str) -> usize {
    g.nodes
        .iter()
        .map(|n| {
            usize::from(zedc::zir::op_name(&n.op) == op)
                + n.regions.iter().map(|r| count(r, op)).sum::<usize>()
        })
        .sum()
}

/// `if i < d then (let y{i} = (if ...) + 1 in y{i}) else i`, `d` deep: each level a match node
/// whose arm holds the next, its edge carrying the hint of a `let`.
pub fn nest(d: usize) -> Term {
    let mut t = lit(0);
    for i in 0..d {
        let y = format!("y{i}");
        let inner = let_(&y, prim(Prim::Add, vec![t, lit(1)]), var(&y));
        t = if_(
            prim(Prim::Lt, vec![lit(i as i64), lit(d as i64)]),
            inner,
            lit(i as i64),
        );
    }
    t
}

/// `if 0 < 1 then (if ... push stdout 0 ...) else 0`, `d` deep: the push at the bottom takes
/// the state edge through every region above it.
pub fn push_under_ifs(d: usize) -> Term {
    (0..d).fold(Term::Push("stdout".into(), lit(0i64).into()), |t, _| {
        if_(prim(Prim::Lt, vec![lit(0i64), lit(1i64)]), t, lit(0i64))
    })
}
