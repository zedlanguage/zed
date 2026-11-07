//! Whether the two domain bounds of a morphism type in a recursive group are written the same
//! (item GROUP-same, COMPLEXITY.md K27). The admission check asks it at every morphism type of
//! every body: a recursive occurrence in a guarantee that differs from its permission is
//! rejected, and differing bounds constrain the definitions named in them. Each node of a body
//! is numbered by its shape once, when the body's tree is built, so the question costs O(1)
//! however deep the bounds nest.

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group, Rejection};
use zed_tests::scaling;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn ty(t: Type) -> Expr {
    Expr::Type(t)
}

fn m(l: Expr, u: Expr, v: Expr) -> Expr {
    Expr::Morphism(Box::new(l), Box::new(u), Box::new(v))
}

fn pair(a: Expr, b: Expr) -> Expr {
    Expr::Tuple(vec![a, b])
}

/// The group of one definition `W` with this body.
fn group(body: Expr) -> Result<Group, Rejection> {
    Group::new(vec![Def {
        name: "W".into(),
        params: vec![],
        body,
    }])
}

/// `W` itself under `d` morphism types into `int`, each the domain of the next with equal
/// bounds: `((W) -> int) -> int` at depth 2. The two bounds of each level are built apart, so
/// the body has `2^(d+1) - 1` nodes. `leaf` is the innermost permission.
fn nested(d: usize, leaf: impl Fn() -> Expr) -> Expr {
    let (mut l, mut u) = (r(0), leaf());
    for _ in 0..d {
        let next = m(l, u, ty(Type::int()));
        (l, u) = (next.clone(), next);
    }
    l
}

const DIFFER: &str = "the type `W` is not monotone in emptiness: a recursive occurrence stands \
                      in the guaranteed domain of a morphism type whose guarantee and permission \
                      differ";

#[test]
fn equal_bounds_nested_deep_are_the_same() {
    for d in [1, 2, 6] {
        assert!(group(nested(d, || r(0))).is_ok(), "depth {d}");
    }
}

const UNDER: &str = "the type `W` is not monotone in emptiness: a recursive occurrence stands \
                     in the domain of a morphism type that stands under `&`, `\\`, a complement \
                     or differing domain bounds, or in a definition named there";

/// Bounds that differ only at their innermost level: `(W) .. int -> int` alone is rejected for
/// its differing bounds. Nested under equal bounds, those differing bounds name `W`, so `W` is
/// constrained, and the outermost morphism type, whose guarantee is recursive, is rejected
/// first. Had the equal outer bounds been taken for differing ones, the outermost would be
/// rejected with the first message instead.
#[test]
fn bounds_differing_deep_inside_differ() {
    for d in [1, 2, 6] {
        let rejected = group(nested(d, || ty(Type::int()))).unwrap_err();
        let expected = if d == 1 { DIFFER } else { UNDER };
        assert_eq!(rejected.message, expected, "depth {d}");
    }
}

/// `((W, int)) -> int` against `((int, W)) -> int`: the same parts in another order.
#[test]
fn components_in_another_order_differ() {
    let body = m(
        pair(r(0), ty(Type::int())),
        pair(ty(Type::int()), r(0)),
        ty(Type::int()),
    );
    assert_eq!(group(body).unwrap_err().message, DIFFER);
}

/// `int | empty` and `int` are one type, built apart: bounds holding them are the same.
#[test]
fn equal_types_built_apart_are_the_same() {
    let body = m(
        pair(r(0), ty(&Type::int() | &Type::empty())),
        pair(r(0), ty(Type::int())),
        ty(Type::int()),
    );
    assert!(group(body).is_ok());
}

/// A body of `n` nodes whose bounds are equal and nested `log2 n` deep, and one whose bounds
/// differ and are nested `d` deep, each admitted in time linear in its size.
#[test]
fn nested_bounds_scale() {
    let d = 11;
    let equal = scaling::inputs(1 << d, |n| nested(n.trailing_zeros() as usize, || r(0)));
    scaling::check("admitting a group whose equal bounds nest", 1 << d, |n| {
        assert!(group(equal[&n].clone()).is_ok());
    });
    // `(((int) .. int -> int) .. int -> int)`: the guarantee of each level is the level below.
    let differ = |d: usize| {
        (0..d).fold(ty(Type::bool()), |l, _| {
            m(l, ty(Type::int()), ty(Type::int()))
        })
    };
    let n = 512;
    let differing = scaling::inputs(n, differ);
    scaling::check("admitting a group whose differing bounds nest", n, |n| {
        assert!(group(differing[&n].clone()).is_ok());
    });
}
