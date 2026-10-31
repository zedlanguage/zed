//! Each reduction on its own, the enumeration of listed sets, and controls: the check of `random`
//! rejects a scope that leaves out a value reaching its arm.

use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term, Value};
use zedc::store::affine::Bounds;
use zedc::store::interval::IntervalSet;
use zedc::store::lattice::{Landmarks, Lattice};
use zedc::store::product::{Product, Scope};

use super::ints;
use super::random::{Shape, check};

fn none() -> zedc::store::cell::Premises {
    zedc::store::cell::Premises::new()
}

/// The scope of `n` within `lo..=hi`.
fn within(lo: i64, hi: i64) -> Scope {
    let range = prim(
        Prim::And,
        vec![
            prim(Prim::Ge, vec![var("n"), lit(lo)]),
            prim(Prim::Le, vec![var("n"), lit(hi)]),
        ],
    );
    ints(&["n".into()]).assume(&range, true, &none())
}

/// `s` with `t` written as holding, reduced.
fn written(mut s: Scope, t: Term) -> Scope {
    s.write(t);
    s.reduce();
    s
}

#[test]
fn a_single_value_fixes_the_congruence_and_the_finite_set() {
    let s = ints(&["n".into()]).assume(&prim(Prim::Eq, vec![var("n"), lit(5)]), true, &none());
    assert_eq!(
        s.get("n").to_string(),
        "ints [5..=5]\ncongruence 5\nfinite {5}\ntype 5\n"
    );
}

#[test]
fn a_congruence_narrows_the_interval_ends() {
    // `n mod 4 == 1` within `2..=20` moves the ends to `5` and `17`.
    let s = within(2, 20).assume(
        &prim(
            Prim::Eq,
            vec![prim(Prim::Mod, vec![var("n"), lit(4)]), lit(1)],
        ),
        true,
        &none(),
    );
    assert_eq!(s.get("n").ints().hull().to_string(), "[5..=17]");
    assert_eq!(s.get("n").cell.congruence.element.to_string(), "1 mod 4");
}

#[test]
fn enumeration_keeps_the_members_a_written_constraint_holds_at() {
    // `n * n mod 5 == 1` among `0..=10`, listed: 1, 4, 6, 9.
    let t = prim(
        Prim::Eq,
        vec![
            prim(
                Prim::Mod,
                vec![prim(Prim::Mul, vec![var("n"), var("n")]), lit(5)],
            ),
            lit(1),
        ],
    );
    let s = written(among(&(0..=10).collect::<Vec<_>>()), t);
    assert_eq!(
        s.get("n").ints().to_string(),
        "[1..=1, 4..=4, 6..=6, 9..=9]"
    );
}

#[test]
fn enumeration_reads_the_other_names_when_they_are_static() {
    // `m` is 3, so `n mod m == 1` among `0..=10`, listed, keeps 1, 4, 7, 10.
    let mut s = among(&(0..=10).collect::<Vec<_>>());
    s.names.insert("m".into(), Product::literal(&Value::Int(3)));
    let t = prim(
        Prim::Eq,
        vec![prim(Prim::Mod, vec![var("n"), var("m")]), lit(1)],
    );
    let s = written(s, t.clone());
    assert_eq!(
        s.get("n").ints().to_string(),
        "[1..=1, 4..=4, 7..=7, 10..=10]"
    );
    // With `m` known only at run time, the constraint has two open names and is not
    // enumerated.
    let mut s = within(0, 10);
    s.names.insert("m".into(), Product::of_type(Type::int()));
    let s = written(s, t);
    assert_eq!(s.get("n").ints().to_string(), "[0..=10]");
}

#[test]
fn a_written_constraint_on_static_names_that_fails_makes_the_scope_bottom() {
    let mut s = Scope::new([("m".into(), Product::literal(&Value::Int(3)))]);
    assert!(!s.bottom);
    s = written(s, prim(Prim::Gt, vec![var("m"), lit(5)]));
    assert!(s.bottom);
}

/// The scope of `n` of the type listing `vs`.
fn among(vs: &[i64]) -> Scope {
    let t = Type::union_all(vs.iter().map(|&v| Type::lit(&Value::Int(v)).unwrap()));
    Scope::new([("n".into(), Product::of_type(t))])
}

#[test]
fn a_listed_set_is_enumerated_and_a_range_is_not() {
    // `n * n mod 7` is 1, 4, 2, 2, 4, 1 at 1..=6.
    let t = prim(
        Prim::Ne,
        vec![
            prim(
                Prim::Mod,
                vec![prim(Prim::Mul, vec![var("n"), var("n")]), lit(7)],
            ),
            lit(2),
        ],
    );
    let s = written(among(&[1, 2, 3, 4, 5, 6]), t.clone());
    assert_eq!(s.get("n").ints().to_string(), "[1..=2, 5..=6]");
    // The same members as a range are left to interval reasoning, however few they are.
    let s = written(within(1, 6), t);
    assert_eq!(s.get("n").ints().to_string(), "[1..=6]");
}

/// `count(k) > 1 || n == 0` for a `count` that takes about `2k` steps.
fn slow_unless_zero(k: Term) -> Term {
    let half = || prim(Prim::IntDiv, vec![var("k"), lit(2)]);
    let me = |arg: Term| app(var("me"), vec![var("me"), arg]);
    let body = if_(
        prim(Prim::Le, vec![var("k"), lit(1)]),
        lit(1),
        prim(
            Prim::Add,
            vec![me(half()), me(prim(Prim::Sub, vec![var("k"), half()]))],
        ),
    );
    let f = lam(&["me", "k"], body);
    let count = app(f.clone(), vec![f, k]);
    // `n == 0` is cheap; at any other `n`, `count` runs first and is false at `k <= 1`.
    if_(
        prim(Prim::Eq, vec![var("n"), lit(0)]),
        lit(true),
        prim(Prim::Gt, vec![count, lit(1)]),
    )
}

#[test]
fn a_constraint_whose_form_does_not_show_it_ends_removes_nothing() {
    // `count` calls itself through its parameter `me`, so however cheap it is at each member
    // (`count(1) = 1`, so the constraint is false at 1), the constraint is not evaluated.
    let s = written(among(&[0, 1, 2, 3]), slow_unless_zero(var("n")));
    assert_eq!(s.get("n").ints().to_string(), "[0..=3]");
    // A constraint whose form shows it ends, over the same members, removes 1 and 3.
    let even = prim(
        Prim::Or,
        vec![
            prim(
                Prim::Eq,
                vec![prim(Prim::Mod, vec![var("n"), lit(2)]), lit(0)],
            ),
            prim(Prim::Eq, vec![var("n"), lit(-1)]),
        ],
    );
    let s = written(among(&[0, 1, 2, 3]), even);
    assert_eq!(s.get("n").ints().to_string(), "[0..=0, 2..=2]");
}

#[test]
fn a_type_widens_to_its_whole_base_type() {
    let one = Type::lit(&Value::Int(1)).unwrap();
    let two = Type::lit(&Value::Int(2)).unwrap();
    let none = Landmarks::none();
    assert_eq!(one.widen(&(&one | &two), &none), &one | &Type::int());
    assert!(one.widen(&(&one | &two), &none).subtype(&Type::int()));
    // A part that does not grow is kept.
    assert_eq!(one.widen(&one, &none), one);
    // A narrowing takes a part only while it is whole: `int` narrows to `1`, and `1 | 2`
    // stays, so a chain of narrowings is finite.
    assert_eq!(Type::int().narrow(&one, &none), one);
    assert_eq!((&one | &two).narrow(&one, &none), &one | &two);
    assert_eq!((&Type::int() | &Type::bool()).narrow(&one, &none), one);
    assert!(Type::bottom().leq(&one) && one.leq(&Type::top()));
}

#[test]
fn an_empty_interval_removes_int_from_the_type() {
    let mut p = Product::of_type(&Type::int() | &Type::bool());
    p.cell.ints.element = Bounds::ints(IntervalSet::empty());
    let s = Scope::new([("v".into(), p)]);
    assert_eq!(s.get("v").ty.element, Type::bool());
    // With only `int`, the product is empty and the scope bottom.
    let mut p = Product::of_type(Type::int());
    p.cell.ints.element = Bounds::ints(IntervalSet::empty());
    assert!(Scope::new([("v".into(), p)]).bottom);
}

#[test]
fn the_check_rejects_a_scope_that_leaves_out_a_reached_value() {
    // `x >= 0` then `y < x`; the first arm holds every `x` in `0..`.
    let s = Shape {
        z: var("x"),
        outer: prim(Prim::Ge, vec![var("x"), lit(0)]),
        inner: prim(Prim::Lt, vec![var("y"), var("x")]),
        c: 0,
    };
    let mut arms = s.arms();
    assert!(check(&s, &arms).is_ok());
    // Leave `x = 3` out of the first arm.
    let x = arms[0].scope.names.get_mut(&Arc::<str>::from("x")).unwrap();
    let cut = IntervalSet::single(3).complement_in(x.ints());
    x.cell.ints.element = Bounds::ints(cut);
    let e = check(&s, &arms).unwrap_err();
    assert!(e.contains("reaches arm 0"), "{e}");
    // Mark the inner arm unreachable: points with `y < x` reach it.
    let mut arms = s.arms();
    arms[1].scope.bottom = true;
    assert!(check(&s, &arms).unwrap_err().contains("reaches arm 1"));
    // Drop the relation's effect: put `y = 4` beside `x = 2` in the inner arm by a wrong
    // relation `y > x`.
    let mut arms = s.arms();
    arms[1].scope.relation = zedc::store::presburger::Formula::and(vec![
        arms[1].scope.relation.clone(),
        zedc::store::presburger::Formula::Con(
            zedc::store::presburger::Con::ge(
                &zedc::store::presburger::Lin::atom(zedc::store::presburger::Atom::Sym("y".into())),
                &zedc::store::presburger::Lin::atom(zedc::store::presburger::Atom::Sym("x".into())),
            )
            .unwrap(),
        ),
    ]);
    assert!(check(&s, &arms).unwrap_err().contains("reaches arm 1"));
}

#[test]
fn an_equality_between_names_of_different_parity_is_unreachable() {
    // `x` even, `y` odd and `x == y`: no value meets all three. Passing the relation and the
    // congruences to each other one at a time moves `x`'s lower bound up by one step per
    // pass, without end; the relation must read the congruences itself.
    let src =
        "ok = (x, y) -> if x mod 2 == 0 && y mod 2 == 1 && x >= 0 && x == y { x } else { 0 };";
    let (_, _, a) = super::arms_of(src);
    let then = super::arm(&a, "(x == y)", true);
    assert!(!then.reachable(), "{}", then.scope);
}
