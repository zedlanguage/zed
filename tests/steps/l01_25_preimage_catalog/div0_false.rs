//! FAIL-preimage-div0-false-exact, found by TEST-complete-preimage (author P189): a comparison
//! under `==` or `!=` of an operand that may fail with one that is certainly an integer.
//! `x div 0` is `#divByZero` at every `x`, and `==` compares a failure as data, so
//! `(x div 0) == 0` is false at every point: under the demand false the preimage is every
//! integer, and exact. The transfer gave the right box, `[..]`, but marked it necessary, since
//! its forward transfer of `==` kept both outcomes for any operand that may fail. DESIGN.md step
//! L1.25: "A failure such as `#divByZero` meets no demand ... since `==` and `!=` compare
//! failures as data, a comparison whose operands may fail ... keeps its whole box ...,
//! necessary, except a comparison with a constant integer, under which a failing operand meets
//! an ordered comparison and `==` nowhere"; and "A necessary box that the forward transfer
//! shows meets the demand everywhere is marked exact."

use zed_kernel::Prim::{Eq, IntDiv, Lt, Mod, Ne};
use zed_kernel::Term;
use zed_kernel::term::build::{lit, prim, var};
use zedc::store::preimage::{Demand, preimage};

use super::{check, doms, shown};

fn p2(p: zed_kernel::Prim, a: Term, b: Term) -> Term {
    prim(p, vec![a, b])
}

#[test]
fn a_comparison_of_a_division_by_zero_that_always_holds_is_exact() {
    let x = || var("x");
    let ds = doms(&[("x", None, None)]);
    for (t, d) in [
        (p2(Eq, p2(IntDiv, x(), lit(0)), lit(0)), Demand::Bool(false)),
        (p2(Ne, p2(IntDiv, x(), lit(0)), lit(0)), Demand::Bool(true)),
        (p2(Eq, p2(Mod, x(), lit(0)), lit(0)), Demand::Bool(false)),
        // The integer on the left: the same by the other operand.
        (p2(Eq, lit(0), p2(IntDiv, x(), lit(0))), Demand::Bool(false)),
        // The integer an input, not a constant.
        (p2(Ne, x(), p2(Mod, x(), lit(0))), Demand::Bool(true)),
    ] {
        let p = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &p, (-40, 40));
        assert_eq!(shown(&p), "x [..]; exact", "{t} under {d:?}");
    }
}

/// The neighbors of [`a_comparison_of_a_division_by_zero_that_always_holds_is_exact`]: each box
/// is checked against the interpreter, so none is marked exact where a point in it fails the
/// demand.
#[test]
fn comparisons_of_operands_that_may_fail_keep_sound_boxes() {
    let (x, y) = (|| var("x"), || var("y"));
    let ds = doms(&[("x", Some(-6), Some(6)), ("y", Some(-2), Some(2))]);
    for (t, d, want) in [
        // A failure equals a failure: `(x div 0) == (x mod 0)` holds at every point, so the
        // forward transfer may not say it is false; the box stays necessary.
        (
            p2(Eq, p2(IntDiv, x(), lit(0)), p2(Mod, x(), lit(0))),
            Demand::Bool(true),
            "x [-6..=6]; y [-2..=2]; necessary",
        ),
        // A divisor that is 0 at one point only: the comparison holds or differs elsewhere.
        (
            p2(Eq, p2(IntDiv, x(), y()), lit(0)),
            Demand::Bool(false),
            "x [-6..=6]; y [-2..=2]; necessary",
        ),
        // An ordered comparison passes the failure through, which meets no demand.
        (
            p2(Lt, p2(IntDiv, x(), lit(0)), lit(0)),
            Demand::Bool(false),
            "x []; y []; exact",
        ),
        // The control: a division that cannot fail.
        (
            p2(Eq, p2(IntDiv, x(), lit(2)), lit(0)),
            Demand::Bool(false),
            "x [-6..=-1, 2..=6]; y [-2..=2]; exact",
        ),
    ] {
        let p = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &p, (-8, 8));
        assert_eq!(shown(&p), want, "{t} under {d:?}");
    }
}
