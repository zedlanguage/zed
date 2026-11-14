//! A plan whose lambda node lists no regions, so the lambda's body has no plan, called by an
//! `apply`: the machine says the body has no plan, as it does for an arm with no plan, whether
//! or not the `apply`'s plan resolves its callee (FAIL-memory-callee-no-plan, found by
//! TEST-complete-native). Before the fix, an `apply` whose plan resolved its callee said
//! "the plan calls `r.0/0`, and the callee is `r.0/0`", one region named twice.

use zed_kernel::Prim;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zedc::zir::Region;
use zedc::zir::memory::Plan;

use super::{cat, planned, run};

/// `g = x -> (x, 1); g("a" ++ "b")`, planned with fusion.
fn call() -> (Region, Plan) {
    let g = lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1)]));
    let t = let_("g", g, app(var("g"), vec![cat("a", "b")]));
    planned(&t, true)
}

#[test]
fn a_called_body_with_no_plan_is_reported_as_one() {
    let (g, mut p) = call();
    p["r"].nodes[0].regions.clear();
    assert_eq!(
        run(&g, &p).unwrap_err(),
        "memory: region `r.0/0` has no plan; only the root, lambda bodies and arms do"
    );
}

#[test]
fn a_called_body_with_no_plan_and_no_resolved_callee_is_reported_the_same() {
    let (g, mut p) = call();
    p["r"].nodes[0].regions.clear();
    for n in &mut p["r"].nodes {
        n.callee = None;
    }
    assert_eq!(
        run(&g, &p).unwrap_err(),
        "memory: region `r.0/0` has no plan; only the root, lambda bodies and arms do"
    );
}

#[test]
fn the_unchanged_plan_runs() {
    let (g, p) = call();
    assert_eq!(run(&g, &p).map(|(v, _)| v), Ok("(\"ab\", 1)".to_string()));
}
