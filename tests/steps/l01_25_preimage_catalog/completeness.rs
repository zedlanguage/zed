//! The completeness pass over the preimage catalog (row TEST-complete-preimage, author P189):
//! each entry of the catalog reached in each way a term can reach it, with the constant on
//! either side, under each demand, nested in each other entry, and next to each stop. The
//! cases are listed in `COMPLETENESS.md` beside this file.
//!
//! Every case is checked against the interpreter over the window `-40..=40` ([`check`]): each
//! point that meets the demand lies in the preimage, and where the preimage is marked exact,
//! each point in it meets the demand. The printed preimage is then compared with the one
//! DESIGN.md gives (sec:domains, "Backward transfer, and `@ensure`"): affine maps, Euclidean
//! `div` and `mod` by a constant, `min` and `max` invert exactly; a branch is the union of its
//! arms under their guards; nonlinear arithmetic and a divisor that is not a constant are
//! read by interval revision, necessary only; hashes, string operations other than `len` and
//! foreign calls stop the transfer, and the stop is reported. A case DESIGN.md gives no
//! single answer for (a demand of the wrong type, which the checker never asks; a term the
//! catalog reads as necessary only) is checked for soundness alone ([`sound`]).

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim};
use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, preimage};

use super::{check, doms, listed, pre_listed, shown};

use Prim::*;

fn x() -> Term {
    Term::Var("x".into())
}

fn y() -> Term {
    Term::Var("y".into())
}

fn k(i: i64) -> Term {
    lit(i)
}

fn p1(p: Prim, a: Term) -> Term {
    prim(p, vec![a])
}

fn p2(p: Prim, a: Term, b: Term) -> Term {
    prim(p, vec![a, b])
}

/// `x` over every integer.
fn any_x() -> Domains {
    doms(&[("x", None, None)])
}

/// `x` over `[lo..=hi]`.
fn x_in(lo: i64, hi: i64) -> Domains {
    doms(&[("x", Some(lo), Some(hi))])
}

/// `x` and `y` over every integer.
fn any_xy() -> Domains {
    doms(&[("x", None, None), ("y", None, None)])
}

/// `x` and `y` over `[lo..=hi]` each.
fn xy_in(lo: i64, hi: i64) -> Domains {
    doms(&[("x", Some(lo), Some(hi)), ("y", Some(lo), Some(hi))])
}

/// The integers in `[lo..=hi]`, `None` for an unbounded end.
fn ints(lo: Option<i64>, hi: Option<i64>) -> IntervalSet {
    IntervalSet::range(
        lo.map_or(End::NegInf, End::of),
        hi.map_or(End::PosInf, End::of),
    )
}

const T: Demand = Demand::Bool(true);
const F: Demand = Demand::Bool(false);

/// One case: what it covers, the term, the box, the demand, and the preimage DESIGN.md gives.
type Case = (&'static str, Term, Domains, Demand, &'static str);

/// Checks each case against the interpreter, then against its expected preimage, and reports
/// every case that differs at once.
fn table(cases: Vec<Case>) {
    let mut wrong = Vec::new();
    for (what, t, ds, d, want) in cases {
        let p = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &p, (-40, 40));
        let got = shown(&p);
        if got != want {
            wrong.push(format!(
                "{what}: {t} under {d:?}\n  got  {got}\n  want {want}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Checks each case against the interpreter alone: sound, and exact only where it holds.
fn sound(cases: Vec<(&'static str, Term, Domains, Demand)>) {
    for (_, t, ds, d) in cases {
        let p = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &p, (-40, 40));
    }
}

#[test]
fn a_plain_input_meets_each_kind_of_demand() {
    table(vec![
        (
            "point",
            x(),
            any_x(),
            Demand::Ints(ints(Some(5), Some(5))),
            "x [5..=5]; exact",
        ),
        (
            "empty",
            x(),
            any_x(),
            Demand::Ints(IntervalSet::empty()),
            "x []; exact",
        ),
        (
            "every integer",
            x(),
            any_x(),
            Demand::Ints(IntervalSet::top()),
            "x [..]; exact",
        ),
        (
            "ray over a bounded domain",
            x(),
            x_in(-10, 10),
            Demand::Ints(ints(Some(8), None)),
            "x [8..=10]; exact",
        ),
        (
            "two pieces over a bounded domain",
            x(),
            x_in(-10, 10),
            Demand::Ints(ints(None, Some(-3)).join(&ints(Some(3), None))),
            "x [-10..=-3, 3..=10]; exact",
        ),
        (
            "demand outside the domain",
            x(),
            x_in(-10, 10),
            Demand::Ints(ints(Some(11), None)),
            "x []; exact",
        ),
    ]);
}

#[test]
fn a_closed_term_keeps_the_whole_box_or_none_of_it() {
    table(vec![
        ("true", p2(Lt, k(1), k(2)), any_x(), T, "x [..]; exact"),
        ("false", p2(Lt, k(2), k(1)), any_x(), T, "x []; exact"),
        (
            "false under false",
            p2(Lt, k(2), k(1)),
            any_x(),
            F,
            "x [..]; exact",
        ),
        (
            "a failure",
            p2(Eq, p2(IntDiv, k(1), k(0)), k(0)),
            any_x(),
            T,
            "x []; exact",
        ),
        // `==` compares a failure as data (DESIGN L1.25): `#divByZero == 0` is false.
        (
            "a failure under false",
            p2(Eq, p2(IntDiv, k(1), k(0)), k(0)),
            any_x(),
            F,
            "x [..]; exact",
        ),
        // An ordered comparison of a failure meets no demand.
        (
            "an ordered failure under false",
            p2(Lt, p2(IntDiv, k(1), k(0)), k(0)),
            any_x(),
            F,
            "x []; exact",
        ),
        (
            "an integer in the demand",
            p2(Add, k(2), k(3)),
            any_x(),
            Demand::Ints(ints(Some(5), Some(5))),
            "x [..]; exact",
        ),
        (
            "an integer outside the demand",
            p2(Add, k(2), k(3)),
            any_x(),
            Demand::Ints(ints(Some(6), None)),
            "x []; exact",
        ),
        (
            "a closed operand of an input's test",
            p2(Gt, x(), p2(Mul, k(2), k(3))),
            any_x(),
            T,
            "x [7..]; exact",
        ),
    ]);
}

#[test]
fn an_input_the_term_does_not_read_keeps_its_set() {
    table(vec![(
        "y unread",
        p2(Gt, x(), k(0)),
        doms(&[("x", None, None), ("y", Some(0), Some(3))]),
        T,
        "x [1..]; y [0..=3]; exact",
    )]);
    // No point meets the term: `x` is empty, and the box holds no point whatever `y` keeps.
    let ds = doms(&[("x", Some(-5), Some(0)), ("y", Some(0), Some(3))]);
    let t = p2(Gt, x(), k(0));
    let p = preimage(&t, &ds, &T);
    check(&t, &ds, &T, &p, (-40, 40));
    assert!(p.exact && p.domains["x"].is_empty(), "{}", shown(&p));
}

#[test]
fn a_demand_of_the_wrong_type_holds_at_no_point() {
    // The checker never asks these, since a term has one type; the answer is sound.
    sound(vec![
        ("an integer input under true", x(), any_x(), T),
        ("a sum under true", p2(Add, x(), k(1)), any_x(), T),
        ("min under true", p2(Min, x(), k(1)), any_x(), T),
        (
            "a test under an integer demand",
            p2(Lt, x(), k(3)),
            any_x(),
            Demand::Ints(IntervalSet::top()),
        ),
        (
            "a negation under an integer demand",
            p1(Not, p2(Lt, x(), k(3))),
            any_x(),
            Demand::Ints(IntervalSet::top()),
        ),
        (
            "a conjunction under an integer demand",
            p2(And, p2(Lt, x(), k(3)), p2(Gt, x(), k(0))),
            any_x(),
            Demand::Ints(IntervalSet::top()),
        ),
    ]);
}

#[test]
fn shifts_and_scalings_invert_with_the_constant_on_either_side() {
    table(vec![
        (
            "k + x",
            p2(Ge, p2(Add, k(3), x()), k(10)),
            any_x(),
            T,
            "x [7..]; exact",
        ),
        (
            "x + k",
            p2(Ge, p2(Add, x(), k(3)), k(10)),
            any_x(),
            T,
            "x [7..]; exact",
        ),
        (
            "x + negative k",
            p2(Ge, p2(Add, x(), k(-3)), k(10)),
            any_x(),
            T,
            "x [13..]; exact",
        ),
        (
            "x - k",
            p2(Le, p2(Sub, x(), k(4)), k(0)),
            any_x(),
            T,
            "x [..=4]; exact",
        ),
        (
            "k - x",
            p2(Le, p2(Sub, k(4), x()), k(0)),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "k * x",
            p2(Ge, p2(Mul, k(3), x()), k(10)),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "x * k",
            p2(Le, p2(Mul, x(), k(3)), k(10)),
            any_x(),
            T,
            "x [..=3]; exact",
        ),
        (
            "x * negative k",
            p2(Ge, p2(Mul, x(), k(-3)), k(10)),
            any_x(),
            T,
            "x [..=-4]; exact",
        ),
        (
            "x * 1",
            p2(Eq, p2(Mul, x(), k(1)), k(7)),
            any_x(),
            T,
            "x [7..=7]; exact",
        ),
        (
            "x * -1",
            p2(Eq, p2(Mul, x(), k(-1)), k(7)),
            any_x(),
            T,
            "x [-7..=-7]; exact",
        ),
        (
            "x * 0 meets 0",
            p2(Eq, p2(Mul, x(), k(0)), k(0)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "k * x off its multiples",
            p2(Eq, p2(Mul, k(3), x()), k(7)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "x * k in a range",
            p2(Mul, x(), k(3)),
            any_x(),
            Demand::Ints(ints(Some(1), Some(10))),
            "x [1..=3]; exact",
        ),
        (
            "nested shifts and scalings",
            p2(Ge, p2(Sub, p2(Mul, p2(Add, x(), k(3)), k(2)), k(1)), k(9)),
            any_x(),
            T,
            "x [2..]; exact",
        ),
        (
            "a reflection scaled by a negative constant",
            p2(Le, p2(Mul, p2(Sub, k(5), x()), k(-2)), k(-4)),
            any_x(),
            T,
            "x [..=3]; exact",
        ),
        (
            "under false",
            p2(Ge, p2(Add, x(), k(3)), k(10)),
            any_x(),
            F,
            "x [..=6]; exact",
        ),
        (
            "over a bounded domain",
            p2(Ge, p2(Mul, k(2), x()), k(10)),
            x_in(-10, 10),
            T,
            "x [5..=10]; exact",
        ),
    ]);
}

#[test]
fn euclidean_div_and_mod_by_each_kind_of_constant() {
    table(vec![
        (
            "div by 1",
            p2(Eq, p2(IntDiv, x(), k(1)), k(4)),
            any_x(),
            T,
            "x [4..=4]; exact",
        ),
        (
            "div by -1",
            p2(Eq, p2(IntDiv, x(), k(-1)), k(4)),
            any_x(),
            T,
            "x [-4..=-4]; exact",
        ),
        (
            "div by 3, a ray",
            p2(Ge, p2(IntDiv, x(), k(3)), k(2)),
            any_x(),
            T,
            "x [6..]; exact",
        ),
        // x = -3q + r with 0 <= r <= 2: q >= 2 is x <= -4.
        (
            "div by -3, a ray",
            p2(Ge, p2(IntDiv, x(), k(-3)), k(2)),
            any_x(),
            T,
            "x [..=-4]; exact",
        ),
        (
            "div by 3 below 0",
            p2(Lt, p2(IntDiv, x(), k(3)), k(0)),
            any_x(),
            T,
            "x [..=-1]; exact",
        ),
        (
            "div by 0",
            p2(Eq, p2(IntDiv, x(), k(0)), k(0)),
            any_x(),
            T,
            "x []; exact",
        ),
        // `#divByZero < 0` is a failure, which meets no demand (DESIGN L1.25). `#divByZero == 0`
        // is false, so `(x div 0) == 0` under false holds everywhere: that case is row
        // FAIL-preimage-div0-false-exact (the box is right, marked necessary).
        (
            "div by 0, ordered",
            p2(Lt, p2(IntDiv, x(), k(0)), k(5)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "div by 0, ordered, false",
            p2(Lt, p2(IntDiv, x(), k(0)), k(5)),
            any_x(),
            F,
            "x []; exact",
        ),
        (
            "mod 1 is 0",
            p2(Eq, p2(Mod, x(), k(1)), k(0)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "mod 1 is never 1",
            p2(Eq, p2(Mod, x(), k(1)), k(1)),
            any_x(),
            T,
            "x []; exact",
        ),
        // Euclidean: the remainder of a negative divisor is not negative either.
        (
            "mod -4",
            p2(Eq, p2(Mod, x(), k(-4)), k(1)),
            x_in(0, 7),
            T,
            "x [1..=1, 5..=5]; exact",
        ),
        (
            "mod past the remainders",
            p2(Eq, p2(Mod, x(), k(4)), k(5)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "mod below 0",
            p2(Lt, p2(Mod, x(), k(4)), k(0)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "mod over every remainder",
            p2(Ge, p2(Mod, x(), k(4)), k(0)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "mod within one period",
            p2(Le, p2(Mod, x(), k(4)), k(1)),
            x_in(0, 3),
            T,
            "x [0..=1]; exact",
        ),
        (
            "mod over negative values",
            p2(Eq, p2(Mod, x(), k(4)), k(3)),
            x_in(-8, -1),
            T,
            "x [-5..=-5, -1..=-1]; exact",
        ),
        (
            "mod of a quotient",
            p2(Eq, p2(Mod, p2(IntDiv, x(), k(3)), k(2)), k(1)),
            x_in(0, 11),
            T,
            "x [3..=5, 9..=11]; exact",
        ),
        (
            "a shifted remainder",
            p2(Eq, p2(Add, p2(Mod, x(), k(5)), k(1)), k(3)),
            x_in(0, 9),
            T,
            "x [2..=2, 7..=7]; exact",
        ),
        (
            "mod under false",
            p2(Eq, p2(Mod, x(), k(4)), k(0)),
            x_in(0, 7),
            F,
            "x [1..=3, 5..=7]; exact",
        ),
        (
            "a quotient in a range",
            p2(IntDiv, x(), k(4)),
            any_x(),
            Demand::Ints(ints(Some(-1), Some(1))),
            "x [-4..=7]; exact",
        ),
    ]);
}

#[test]
fn a_divisor_that_is_not_a_constant_is_read_by_revision() {
    // DESIGN.md: rung 2 alone; the box is necessary, and holds every point that meets it.
    sound(vec![
        (
            "a constant over an input",
            p2(Eq, p2(IntDiv, k(12), x()), k(4)),
            x_in(-5, 5),
            T,
        ),
        (
            "an input over an input",
            p2(Eq, p2(IntDiv, x(), y()), k(2)),
            xy_in(-6, 6),
            T,
        ),
        (
            "a remainder by an input",
            p2(Eq, p2(Mod, x(), y()), k(1)),
            xy_in(-6, 6),
            T,
        ),
        (
            "a product of two inputs",
            p2(Le, p2(Mul, x(), y()), k(4)),
            xy_in(-6, 6),
            T,
        ),
        (
            "a product of two inputs under false",
            p2(Le, p2(Mul, x(), y()), k(4)),
            xy_in(-6, 6),
            F,
        ),
    ]);
    // The points meeting `x div y == 2` are not a box, so the box cannot be exact.
    let t = p2(Eq, p2(IntDiv, x(), y()), k(2));
    let p = preimage(&t, &xy_in(0, 6), &T);
    assert!(!p.exact, "{}", shown(&p));
}

#[test]
fn negation_abs_and_powers_invert_at_their_endpoints() {
    table(vec![
        (
            "-x",
            p2(Gt, p1(Neg, x()), k(3)),
            any_x(),
            T,
            "x [..=-4]; exact",
        ),
        (
            "--x",
            p2(Gt, p1(Neg, p1(Neg, x())), k(3)),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "abs at 0",
            p2(Eq, p1(Abs, x()), k(0)),
            any_x(),
            T,
            "x [0..=0]; exact",
        ),
        (
            "abs below 0",
            p2(Lt, p1(Abs, x()), k(0)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "abs at least 0",
            p2(Ge, p1(Abs, x()), k(0)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "abs of a shift",
            p2(Le, p1(Abs, p2(Sub, x(), k(10))), k(2)),
            any_x(),
            T,
            "x [8..=12]; exact",
        ),
        (
            "abs under false",
            p2(Le, p1(Abs, x()), k(2)),
            any_x(),
            F,
            "x [..=-3, 3..]; exact",
        ),
        (
            "x ^ 0 is 1",
            p2(Eq, p2(Pow, x(), k(0)), k(1)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "x ^ 0 is never 2",
            p2(Eq, p2(Pow, x(), k(0)), k(2)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "x ^ 1",
            p2(Ge, p2(Pow, x(), k(1)), k(5)),
            any_x(),
            T,
            "x [5..]; exact",
        ),
        (
            "x ^ 2 at a point",
            p2(Eq, p2(Pow, x(), k(2)), k(49)),
            any_x(),
            T,
            "x [-7..=-7, 7..=7]; exact",
        ),
        (
            "x ^ 2 off the squares",
            p2(Eq, p2(Pow, x(), k(2)), k(50)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "x ^ 2 below 0",
            p2(Lt, p2(Pow, x(), k(2)), k(0)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "x ^ 3",
            p2(Le, p2(Pow, x(), k(3)), k(-8)),
            any_x(),
            T,
            "x [..=-2]; exact",
        ),
        (
            "x ^ 3 in a range",
            p2(Pow, x(), k(3)),
            any_x(),
            Demand::Ints(ints(Some(-27), Some(8))),
            "x [-3..=2]; exact",
        ),
        (
            "a square of a shift",
            p2(Le, p2(Pow, p2(Add, x(), k(1)), k(2)), k(4)),
            any_x(),
            T,
            "x [-3..=1]; exact",
        ),
        (
            "x * x under false",
            p2(Le, p2(Mul, x(), x()), k(99)),
            any_x(),
            F,
            "x [..=-10, 10..]; exact",
        ),
        (
            "an exponent that is a closed term",
            p2(Le, p2(Pow, x(), p2(Add, k(1), k(1))), k(9)),
            any_x(),
            T,
            "x [-3..=3]; exact",
        ),
    ]);
    // An exponent that reads an input, and a negative one (which the checker refuses, DESIGN.md
    // POW domains): only the points where both operands are integers; sound.
    sound(vec![
        ("2 ^ x", p2(Eq, p2(Pow, k(2), x()), k(8)), x_in(-3, 6), T),
        ("x ^ y", p2(Le, p2(Pow, x(), y()), k(8)), xy_in(-3, 3), T),
        ("x ^ -1", p2(Eq, p2(Pow, x(), k(-1)), k(1)), x_in(-3, 3), T),
    ]);
}

#[test]
fn min_and_max_with_a_constant_invert_exactly() {
    table(vec![
        (
            "min, constant right, up",
            p2(Ge, p2(Min, x(), k(5)), k(3)),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "min, constant left, up",
            p2(Ge, p2(Min, k(5), x()), k(3)),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "min above the constant",
            p2(Ge, p2(Min, x(), k(5)), k(6)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "min at the constant",
            p2(Eq, p2(Min, x(), k(5)), k(5)),
            any_x(),
            T,
            "x [5..]; exact",
        ),
        (
            "min, down",
            p2(Le, p2(Min, x(), k(5)), k(2)),
            any_x(),
            T,
            "x [..=2]; exact",
        ),
        (
            "min, down past the constant",
            p2(Le, p2(Min, x(), k(5)), k(7)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "max, constant right, down",
            p2(Le, p2(Max, x(), k(5)), k(7)),
            any_x(),
            T,
            "x [..=7]; exact",
        ),
        (
            "max below the constant",
            p2(Le, p2(Max, x(), k(5)), k(4)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "max at the constant, constant left",
            p2(Eq, p2(Max, k(5), x()), k(5)),
            any_x(),
            T,
            "x [..=5]; exact",
        ),
        (
            "max, up",
            p2(Gt, p2(Max, x(), k(5)), k(6)),
            any_x(),
            T,
            "x [7..]; exact",
        ),
        (
            "max, up below the constant",
            p2(Ge, p2(Max, x(), k(5)), k(3)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "min under false",
            p2(Ge, p2(Min, x(), k(5)), k(3)),
            any_x(),
            F,
            "x [..=2]; exact",
        ),
        (
            "a closed constant",
            p2(Ge, p2(Min, x(), p2(Add, k(2), k(3))), k(3)),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "a clamp",
            p2(Eq, p2(Max, p2(Min, x(), k(10)), k(0)), k(10)),
            any_x(),
            T,
            "x [10..]; exact",
        ),
    ]);
}

#[test]
fn min_and_max_of_two_terms() {
    table(vec![
        (
            "min of two inputs, up: both",
            p2(Ge, p2(Min, x(), y()), k(3)),
            any_xy(),
            T,
            "x [3..]; y [3..]; exact",
        ),
        (
            "max of two inputs, down: both",
            p2(Le, p2(Max, x(), y()), k(3)),
            any_xy(),
            T,
            "x [..=3]; y [..=3]; exact",
        ),
        // Either input may meet it: not a box, so the box is necessary only.
        (
            "min of two inputs, down: either",
            p2(Le, p2(Min, x(), y()), k(3)),
            xy_in(0, 5),
            T,
            "x [0..=5]; y [0..=5]; necessary",
        ),
        (
            "max of two inputs, up: either",
            p2(Ge, p2(Max, x(), y()), k(3)),
            xy_in(0, 5),
            T,
            "x [0..=5]; y [0..=5]; necessary",
        ),
        (
            "max of two inputs, up, where one cannot",
            p2(Ge, p2(Max, x(), y()), k(3)),
            doms(&[("x", Some(0), Some(2)), ("y", Some(0), Some(5))]),
            T,
            "x [0..=2]; y [3..=5]; exact",
        ),
        // The points of `min(x, y) == 3` hold `x` and `y` in `[3..=5]` and are not a box.
        (
            "min of two inputs at a point",
            p2(Eq, p2(Min, x(), y()), k(3)),
            xy_in(0, 5),
            T,
            "x [3..=5]; y [3..=5]; necessary",
        ),
        (
            "min of an input and its shift",
            p2(Ge, p2(Min, x(), p2(Add, x(), k(1))), k(3)),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "max of an input and its reflection",
            p2(Le, p2(Max, x(), p1(Neg, x())), k(3)),
            any_x(),
            T,
            "x [-3..=3]; exact",
        ),
    ]);
    // A failing operand fails the term (DESIGN.md sec:failure).
    sound(vec![(
        "max with an operand that fails at y == 0",
        p2(Ge, p2(Max, x(), p2(Mod, k(0), y())), k(8)),
        doms(&[("x", Some(8), Some(12)), ("y", Some(-2), Some(2))]),
        T,
    )]);
}

#[test]
fn each_comparison_with_a_constant_on_either_side_inverts_exactly() {
    // Over a bounded domain inside the window, an exact preimage checked by the interpreter is
    // the set of points that meet the demand.
    let mut cases = Vec::new();
    for p in [Lt, Le, Gt, Ge, Eq, Ne] {
        for left in [false, true] {
            for d in [T, F] {
                let t = if left {
                    p2(p, k(3), x())
                } else {
                    p2(p, x(), k(3))
                };
                cases.push((p, left, d, t));
            }
        }
    }
    for (p, left, d, t) in cases {
        let ds = x_in(-10, 10);
        let r = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &r, (-40, 40));
        assert!(
            r.exact && r.stops.is_empty(),
            "{p:?}, constant on the left {left}, under {d:?}: {}",
            shown(&r)
        );
    }
    table(vec![
        (
            "!= over every integer",
            p2(Ne, x(), k(3)),
            any_x(),
            T,
            "x [..=2, 4..]; exact",
        ),
        (
            "== constant left",
            p2(Eq, k(3), x()),
            any_x(),
            T,
            "x [3..=3]; exact",
        ),
        (
            "< constant left",
            p2(Lt, k(3), x()),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "<= constant left under false",
            p2(Le, k(3), x()),
            any_x(),
            F,
            "x [..=2]; exact",
        ),
        ("x <= x", p2(Le, x(), x()), any_x(), T, "x [..]; exact"),
        ("x < x", p2(Lt, x(), x()), any_x(), T, "x []; exact"),
        (
            "x + 1 == x",
            p2(Eq, p2(Add, x(), k(1)), x()),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "a shifted difference of two inputs",
            p2(Le, p2(Add, x(), k(2)), y()),
            xy_in(0, 5),
            T,
            "x [0..=3]; y [2..=5]; necessary",
        ),
    ]);
}

#[test]
fn a_comparison_of_two_tests_is_the_union_of_their_agreements() {
    table(vec![
        (
            "== over one input",
            p2(Eq, p2(Gt, x(), k(0)), p2(Gt, x(), k(5))),
            any_x(),
            T,
            "x [..=0, 6..]; exact",
        ),
        (
            "!= over one input",
            p2(Ne, p2(Gt, x(), k(0)), p2(Gt, x(), k(5))),
            any_x(),
            T,
            "x [1..=5]; exact",
        ),
        (
            "== over two inputs",
            p2(Eq, p2(Gt, x(), k(0)), p2(Gt, y(), k(0))),
            any_xy(),
            T,
            "x [..]; y [..]; necessary",
        ),
        (
            "== true",
            p2(Eq, p2(Gt, x(), k(3)), lit(true)),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "== false",
            p2(Eq, p2(Gt, x(), k(3)), lit(false)),
            any_x(),
            T,
            "x [..=3]; exact",
        ),
        (
            "true ==, under false",
            p2(Eq, lit(true), p2(Gt, x(), k(3))),
            any_x(),
            F,
            "x [..=3]; exact",
        ),
    ]);
}

#[test]
fn not_and_or_meet_join_and_swap_under_each_demand() {
    table(vec![
        (
            "!",
            p1(Not, p2(Gt, x(), k(3))),
            any_x(),
            T,
            "x [..=3]; exact",
        ),
        (
            "!!",
            p1(Not, p1(Not, p2(Gt, x(), k(3)))),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "! under false",
            p1(Not, p2(Gt, x(), k(3))),
            any_x(),
            F,
            "x [4..]; exact",
        ),
        (
            "&& under false",
            p2(And, p2(Gt, x(), k(0)), p2(Lt, x(), k(10))),
            any_x(),
            F,
            "x [..=0, 10..]; exact",
        ),
        (
            "|| under false",
            p2(Or, p2(Lt, x(), k(0)), p2(Gt, x(), k(9))),
            any_x(),
            F,
            "x [0..=9]; exact",
        ),
        (
            "&& of two inputs under false",
            p2(And, p2(Gt, x(), k(0)), p2(Gt, y(), k(0))),
            any_xy(),
            F,
            "x [..]; y [..]; necessary",
        ),
        (
            "|| of two inputs under false",
            p2(Or, p2(Gt, x(), k(0)), p2(Gt, y(), k(0))),
            any_xy(),
            F,
            "x [..=0]; y [..=0]; exact",
        ),
        (
            "|| inside &&",
            p2(
                And,
                p2(Or, p2(Gt, x(), k(0)), p2(Lt, x(), k(-5))),
                p2(Lt, x(), k(3)),
            ),
            any_x(),
            T,
            "x [..=-6, 1..=2]; exact",
        ),
        (
            "&& inside ||",
            p2(
                Or,
                p2(And, p2(Gt, x(), k(0)), p2(Lt, x(), k(3))),
                p2(Gt, x(), k(10)),
            ),
            any_x(),
            T,
            "x [1..=2, 11..]; exact",
        ),
        (
            "true &&",
            p2(And, lit(true), p2(Gt, x(), k(2))),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "false ||",
            p2(Or, lit(false), p2(Gt, x(), k(2))),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "|| true",
            p2(Or, p2(Gt, x(), k(2)), lit(true)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "&& false",
            p2(And, p2(Gt, x(), k(2)), lit(false)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "a contradiction",
            p2(And, p2(Gt, x(), k(5)), p2(Lt, x(), k(3))),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "a tautology",
            p2(Or, p2(Gt, x(), k(2)), p2(Le, x(), k(2))),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "! over &&",
            p1(Not, p2(And, p2(Ge, x(), k(0)), p2(Ge, y(), k(0)))),
            any_xy(),
            F,
            "x [0..]; y [0..]; exact",
        ),
    ]);
    // A side that fails at every point: the strict connectives pass the failure through, so
    // no point meets either demand.
    let fails = p2(Gt, p2(IntDiv, x(), k(0)), k(1));
    sound(vec![
        (
            "&& with a failing side",
            p2(And, p2(Gt, x(), k(0)), fails.clone()),
            any_x(),
            T,
        ),
        (
            "&& with a failing side under false",
            p2(And, p2(Gt, x(), k(0)), fails.clone()),
            any_x(),
            F,
        ),
        ("! of a failing test", p1(Not, fails), any_x(), T),
    ]);
}

#[test]
fn a_branch_is_the_union_of_its_arms_under_their_guards() {
    table(vec![
        (
            "arms of one input",
            p2(Le, if_(p2(Gt, x(), k(0)), x(), p1(Neg, x())), k(3)),
            any_x(),
            T,
            "x [-3..=3]; exact",
        ),
        (
            "guard true",
            p2(Ge, if_(lit(true), x(), k(0)), k(2)),
            any_x(),
            T,
            "x [2..]; exact",
        ),
        (
            "guard false",
            p2(Ge, if_(lit(false), x(), k(0)), k(2)),
            any_x(),
            T,
            "x []; exact",
        ),
        (
            "a closed guard",
            p2(Ge, if_(p2(Lt, k(1), k(2)), x(), k(0)), k(2)),
            any_x(),
            T,
            "x [2..]; exact",
        ),
        (
            "tests as arms",
            if_(p2(Gt, x(), k(0)), p2(Gt, x(), k(5)), p2(Lt, x(), k(-5))),
            any_x(),
            T,
            "x [..=-6, 6..]; exact",
        ),
        (
            "tests as arms under false",
            if_(p2(Gt, x(), k(0)), p2(Gt, x(), k(5)), p2(Lt, x(), k(-5))),
            any_x(),
            F,
            "x [-5..=5]; exact",
        ),
        (
            "an if in an arm",
            p2(
                Eq,
                if_(p2(Gt, x(), k(0)), if_(p2(Gt, x(), k(10)), k(1), k(2)), k(3)),
                k(2),
            ),
            any_x(),
            T,
            "x [1..=10]; exact",
        ),
        (
            "an if in a guard",
            p2(
                Ge,
                if_(
                    if_(p2(Gt, x(), k(0)), p2(Lt, x(), k(5)), lit(false)),
                    x(),
                    k(0),
                ),
                k(2),
            ),
            any_x(),
            T,
            "x [2..=4]; exact",
        ),
        (
            "constant arms",
            p2(Eq, if_(p2(Gt, x(), k(4)), k(1), k(0)), k(1)),
            any_x(),
            T,
            "x [5..]; exact",
        ),
        (
            "equal constant arms",
            p2(Eq, if_(p2(Gt, x(), k(4)), k(1), k(1)), k(1)),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "a guard on y and an arm on x",
            p2(Ge, if_(p2(Gt, y(), k(0)), x(), k(0)), k(5)),
            any_xy(),
            T,
            "x [5..]; y [1..]; exact",
        ),
        // (y > 0, x >= 5) or (y <= 0, x >= -5): not a box.
        (
            "a guard on y and two arms on x",
            p2(Ge, if_(p2(Gt, y(), k(0)), x(), p2(Add, x(), k(10))), k(5)),
            any_xy(),
            T,
            "x [-5..]; y [..]; necessary",
        ),
        (
            "an integer if under an integer demand",
            if_(p2(Gt, x(), k(0)), x(), p1(Neg, x())),
            any_x(),
            Demand::Ints(ints(Some(0), Some(2))),
            "x [-2..=2]; exact",
        ),
    ]);
    sound(vec![(
        "a guard that can fail",
        p2(
            Eq,
            if_(p2(Gt, p2(IntDiv, k(1), x()), k(0)), k(1), k(0)),
            k(1),
        ),
        x_in(-3, 3),
        T,
    )]);
}

#[test]
fn a_let_is_read_through() {
    table(vec![
        (
            "a shift bound to a name",
            let_(
                "y",
                p2(Add, x(), k(1)),
                p2(Ge, p2(Mul, Term::Var("y".into()), k(2)), k(10)),
            ),
            any_x(),
            T,
            "x [4..]; exact",
        ),
        (
            "a constant bound to a name",
            let_("c", k(5), p2(Gt, x(), Term::Var("c".into()))),
            any_x(),
            T,
            "x [6..]; exact",
        ),
        (
            "a name read twice",
            let_(
                "d",
                p2(Sub, x(), k(3)),
                p2(
                    And,
                    p2(Ge, Term::Var("d".into()), k(0)),
                    p2(Le, Term::Var("d".into()), k(4)),
                ),
            ),
            any_x(),
            T,
            "x [3..=7]; exact",
        ),
        (
            "a test bound to a name",
            let_("c", p2(Gt, x(), k(3)), p1(Not, Term::Var("c".into()))),
            any_x(),
            T,
            "x [..=3]; exact",
        ),
    ]);
    sound(vec![(
        "an unread binding that fails",
        let_("u", p2(IntDiv, k(1), k(0)), p2(Gt, x(), k(3))),
        any_x(),
        T,
    )]);
}

#[test]
fn calls_are_read_through_and_foreign_ones_stop() {
    let a = || Term::Var("a".into());
    let b = || Term::Var("b".into());
    let g = || Term::Var("g".into());
    let hash = |t: Term| app(Term::Var("hash".into()), vec![t]);
    table(vec![
        (
            "an operator as the callee",
            p2(Ge, app(Term::PrimFn(Add), vec![x(), k(1)]), k(3)),
            any_x(),
            T,
            "x [2..]; exact",
        ),
        (
            "a lambda of two parameters",
            p2(
                Ge,
                app(lam(&["a", "b"], p2(Sub, a(), b())), vec![x(), k(3)]),
                k(0),
            ),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "a lambda called on a constant",
            app(lam(&["a"], p2(Gt, a(), k(0))), vec![k(5)]),
            any_x(),
            T,
            "x [..]; exact",
        ),
        (
            "a lambda passed to a lambda",
            let_(
                "apply",
                lam(&["g", "a"], app(g(), vec![a()])),
                p2(
                    Ge,
                    app(
                        Term::Var("apply".into()),
                        vec![lam(&["b"], p2(Mul, b(), k(2))), x()],
                    ),
                    k(6),
                ),
            ),
            any_x(),
            T,
            "x [3..]; exact",
        ),
        (
            "a foreign call in an arm",
            p2(Ge, if_(p2(Gt, x(), k(0)), x(), hash(x())), k(3)),
            any_x(),
            T,
            "x [..]; necessary; stop: foreign name `hash` stops the transfer at hash(x)",
        ),
        (
            "a foreign call beside a narrowing test",
            p2(And, p2(Gt, x(), k(3)), p2(Lt, hash(x()), k(10))),
            any_x(),
            T,
            "x [4..]; necessary; stop: foreign name `hash` stops the transfer at hash(x)",
        ),
        (
            "a string operation beside a test",
            p2(Or, p2(Gt, x(), k(3)), p2(Eq, p1(Show, x()), lit("1"))),
            any_x(),
            T,
            "x [..]; necessary; stop: string operation `String` stops the transfer at String(x)",
        ),
    ]);
    // A string operation in an arm that never runs does not narrow the answer: the box is
    // the taken arm's, exact. DESIGN does not say whether the stop in the other arm is
    // reported, so the test does not look at the stops.
    let t = p2(Ge, if_(lit(true), x(), p1(Len, p1(Show, x()))), k(3));
    let p = preimage(&t, &any_x(), &T);
    check(&t, &any_x(), &T, &p, (-40, 40));
    assert_eq!(p.domains["x"].to_string(), "[3..]", "{}", shown(&p));
    assert!(p.exact, "{}", shown(&p));
    // A foreign call on constants is not run and keeps the box, necessary; that its stop is
    // reported too is row FAIL-preimage-foreign-constant-unreported.
    let t = p2(Lt, hash(k(1)), x());
    let p = preimage(&t, &any_x(), &T);
    check(&t, &any_x(), &T, &p, (-40, 40));
    assert_eq!(p.domains["x"].to_string(), "[..]", "{}", shown(&p));
    assert!(!p.exact, "{}", shown(&p));
    // A primitive given the wrong number of operands keeps the whole box, necessary; that its
    // stop is reported too is row FAIL-preimage-arity-stop-unreported.
    let t = p2(Lt, p1(Add, x()), k(3));
    let p = preimage(&t, &any_x(), &T);
    check(&t, &any_x(), &T, &p, (-40, 40));
    assert_eq!(p.domains["x"].to_string(), "[..]", "{}", shown(&p));
    assert!(!p.exact, "{}", shown(&p));
    // A tuple component is outside the scalar catalog; the box is kept.
    let t = p2(Gt, p2(TupleGet, prim(Tuple, vec![x(), k(1)]), k(0)), k(3));
    let p = preimage(&t, &any_x(), &T);
    assert!(!p.stops.is_empty() && !p.exact, "{}", shown(&p));
    check(&t, &any_x(), &T, &p, (-40, 40));
}

#[test]
fn a_listed_box_with_two_inputs_of_several_members_is_not_enumerated() {
    // At most one input with more than one member is enumerated (docs/thresholds.md,
    // replacement 8; COMPLEXITY.md row C18): the product of two lists is left to the catalog.
    let t = p2(Eq, p2(Mul, x(), y()), k(6));
    let ds = listed(&[("x", &[1, 2, 3]), ("y", &[2, 3])]);
    let p = pre_listed(&t, &ds, &T);
    check(&t, &ds, &T, &p, (-40, 40));
    assert!(!p.enumerated, "{}", shown(&p));
    // One input of one member and one of several: enumerated, exact.
    let ds = listed(&[("x", &[2]), ("y", &[1, 2, 3, 4])]);
    let p = pre_listed(&t, &ds, &T);
    check(&t, &ds, &T, &p, (-40, 40));
    // The catalog's answer is exact (`2 * y == 6`), so the box is not enumerated: DESIGN
    // L1.25 enumerates "when the catalog's answer is not exact".
    assert_eq!(shown(&p), "x [2..=2]; y [3..=3]; exact");
    // A listed input under demand false, which the residue classes of `mod` answer exactly,
    // so it is not enumerated.
    let t = p2(Eq, p2(Mod, p2(Mul, x(), x()), k(10)), k(9));
    let ds = listed(&[("x", &[1, 3, 4, 7])]);
    let p = pre_listed(&t, &ds, &F);
    check(&t, &ds, &F, &p, (-40, 40));
    assert_eq!(shown(&p), "x [1..=1, 4..=4]; exact");
    // A listed input under demand false that interval revision answers only as a range:
    // enumerated. `x * x + x` is 2, 12, 20, 56 at 1, 3, 4, 7.
    let t = p2(Eq, p2(Add, p2(Mul, x(), x()), x()), k(12));
    let p = pre_listed(&t, &ds, &F);
    check(&t, &ds, &F, &p, (-40, 40));
    assert_eq!(shown(&p), "x [1..=1, 4..=4, 7..=7]; exact; enumerated");
    // An empty listed input: no point.
    let ds = listed(&[("x", &[])]);
    let p = pre_listed(&t, &ds, &T);
    assert!(p.domains["x"].is_empty() && p.exact, "{}", shown(&p));
}

#[test]
fn an_atom_a_wide_constant_and_a_bool_argument_are_read_exactly() {
    let a = || Term::Var("a".into());
    let b = || Term::Var("b".into());
    let atom_arm = || if_(p2(Gt, x(), k(0)), x(), lit(Value::atom("e")));
    let wide = |n: i64| lit(Value::int((num_bigint::BigInt::from(1u8) << 70) + n));
    table(vec![
        // `#e` is a failure as data, and a failing operand meets an ordered comparison with a
        // constant under neither demand (DESIGN L1.25).
        (
            "an atom in an arm",
            p2(Lt, atom_arm(), k(3)),
            any_x(),
            T,
            "x [1..=2]; exact",
        ),
        (
            "an atom in an arm, false",
            p2(Lt, atom_arm(), k(3)),
            any_x(),
            F,
            "x [3..]; exact",
        ),
        (
            "a constant past 64 bits",
            p2(Lt, p2(Add, x(), wide(0)), wide(5)),
            any_x(),
            T,
            "x [..=4]; exact",
        ),
        (
            "a constant bool argument picks the arm",
            p2(
                Gt,
                app(lam(&["b", "a"], if_(b(), a(), k(0))), vec![lit(true), x()]),
                k(3),
            ),
            any_x(),
            T,
            "x [4..]; exact",
        ),
    ]);
}

/// A residue class is not an interval, so a box of one is its hull, necessary; each spelling
/// the catalog reads through (a `let`, a call of an operator, `!`, a constant past 64 bits)
/// gives the box of the term written plainly.
#[test]
fn a_remainder_spelled_through_a_let_a_call_or_not_reads_as_written_plainly() {
    let y = || Term::Var("y".into());
    let add = |a: Term, b: Term| app(Term::PrimFn(Add), vec![a, b]);
    let guard = |g: Term| p2(Lt, if_(g, x(), k(100)), k(3));
    let is0 = |t: Term, m: i64| p2(Eq, p2(Mod, t, k(m)), k(0));
    let wide = lit(Value::int(num_bigint::BigInt::from(1u8) << 70));
    // 2^70 and 2^40 are both 1 mod 3.
    let pairs = [
        (is0(p2(Add, x(), wide), 3), is0(p2(Add, x(), k(1 << 40)), 3)),
        (is0(add(x(), k(1)), 3), is0(p2(Add, x(), k(1)), 3)),
        (
            is0(let_("y", x(), p2(Add, y(), k(1))), 3),
            is0(p2(Add, x(), k(1)), 3),
        ),
        (
            guard(is0(add(x(), k(1)), 2)),
            guard(is0(p2(Add, x(), k(1)), 2)),
        ),
        (
            guard(p2(Eq, let_("y", x(), p2(Mod, y(), k(3))), k(0))),
            guard(is0(x(), 3)),
        ),
        (
            guard(p1(Not, is0(x(), 2))),
            guard(p2(Ne, p2(Mod, x(), k(2)), k(0))),
        ),
    ];
    for (spelled, plain) in pairs {
        let p = preimage(&spelled, &any_x(), &T);
        check(&spelled, &any_x(), &T, &p, (-40, 40));
        let q = preimage(&plain, &any_x(), &T);
        assert_eq!(shown(&p), shown(&q), "{spelled} and {plain}");
    }
}
