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

/// Whether `message` refuses `W` for a recursive guarantee that differs from its permission.
fn differ(message: &str) -> bool {
    message.starts_with(
        "the type `W` is outside the form the checker accepts: a recursive occurrence stands in \
         the guarantee of `",
    ) && message.contains("` and permission `")
        && message.contains("` differ; ")
}

#[test]
fn equal_bounds_nested_deep_are_the_same() {
    for d in [1, 2, 6] {
        assert!(group(nested(d, || r(0))).is_ok(), "depth {d}");
    }
}

/// Whether `message` refuses `W` for a recursive guarantee in `W`, which is named in differing
/// domain bounds.
fn under(message: &str) -> bool {
    message.starts_with(
        "the type `W` is outside the form the checker accepts: a recursive occurrence stands in \
         the guarantee of `",
    ) && message.contains(
        "`, in `W`, which is narrowed where it is named: `W` is named in `W`, in the domain \
         bounds of `",
    )
}

/// Bounds that differ only at their innermost level: `(W) .. int -> int` alone is rejected for
/// its differing bounds. Nested under equal bounds, those differing bounds name `W`, so `W` is
/// constrained, and the outermost morphism type, whose guarantee is recursive, is rejected
/// first. Had the equal outer bounds been taken for differing ones, the outermost would be
/// rejected with the first message instead.
#[test]
fn bounds_differing_deep_inside_differ() {
    for d in [1, 2, 6] {
        let rejected = group(nested(d, || ty(Type::int()))).unwrap_err();
        let message = &rejected.message;
        let right = if d == 1 {
            differ(message)
        } else {
            under(message)
        };
        assert!(right, "depth {d}: {message}");
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
    let message = group(body).unwrap_err().message;
    assert!(differ(&message), "{message}");
    assert!(
        message.contains(
            "guarantee of `(W, int) .. (int, W) -> int`, whose guarantee `(W, int)` and \
             permission `(int, W)` differ"
        ),
        "{message}"
    );
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

mod bench;
