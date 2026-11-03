//! The admission check on the named groups of cross-review X14 (wt/xs-cmp/logs/named.txt):
//! a group is accepted only when its emptiness is monotone in the emptiness of its members.
//! `M` is a morphism type with guarantee, permission and value type, `A` a meet, `D` a
//! difference, `T` a pair and `U` a union; `R0` and `R1` are the group's definitions. `M6` and
//! `W_andTop` are monotone but rejected: a refusal, which X14 leaves as known.

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn int() -> Expr {
    Expr::Type(Type::int())
}

fn empty() -> Expr {
    Expr::Type(Type::empty())
}

fn top() -> Expr {
    Expr::Type(Type::top())
}

fn m(l: Expr, u: Expr, v: Expr) -> Expr {
    Expr::Morphism(Box::new(l), Box::new(u), Box::new(v))
}

fn and(a: Expr, b: Expr) -> Expr {
    Expr::And(vec![a, b])
}

fn diff(a: Expr, b: Expr) -> Expr {
    Expr::Diff(Box::new(a), Box::new(b))
}

fn pair(a: Expr, b: Expr) -> Expr {
    Expr::Tuple(vec![a, b])
}

fn accepted(bodies: Vec<Expr>) -> bool {
    let defs = bodies
        .into_iter()
        .enumerate()
        .map(|(i, body)| Def {
            name: format!("R{i}"),
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs).is_ok()
}

#[test]
fn the_named_groups() {
    let f = || m(empty(), empty(), int());
    let cases: Vec<(&str, Vec<Expr>, bool)> = vec![
        ("M0", vec![m(empty(), r(0), r(0))], true),
        ("M1", vec![m(r(0), empty(), int())], false),
        ("M2", vec![and(m(r(0), r(0), int()), f())], false),
        (
            "M3",
            vec![diff(
                m(r(0), r(0), int()),
                diff(m(empty(), top(), int()), f()),
            )],
            false,
        ),
        (
            "M4",
            vec![pair(int(), and(m(r(0), r(0), int()), f()))],
            false,
        ),
        ("M5", vec![m(f(), m(r(0), r(0), int()), int())], false),
        ("M6", vec![m(m(r(0), r(0), int()), empty(), int())], false),
        (
            "M7",
            vec![Expr::Union(vec![int(), pair(int(), r(0))])],
            true,
        ),
        (
            "M5_ref",
            vec![m(r(1), r(1), int()), pair(int(), and(r(0), f()))],
            false,
        ),
        ("M6_dom", vec![m(f(), m(r(0), r(0), int()), int())], false),
        ("CodexXY", vec![and(r(1), f()), m(r(0), r(0), int())], false),
        ("W", vec![m(r(0), r(0), int())], true),
        ("W_and", vec![m(r(0), r(0), int()), and(r(0), f())], false),
        ("W_andTop", vec![and(m(r(0), r(0), int()), top())], false),
    ];
    for (name, bodies, ok) in cases {
        assert_eq!(accepted(bodies), ok, "{name}");
    }
}

#[test]
fn a_rejection_names_its_cause() {
    let defs = vec![
        Def {
            name: "R0".into(),
            params: vec![],
            body: m(r(1), r(1), int()),
        },
        Def {
            name: "R1".into(),
            params: vec![],
            body: pair(int(), and(r(0), m(empty(), empty(), int()))),
        },
    ];
    let e = Group::new(defs).unwrap_err();
    assert_eq!(e.def, 0);
    assert_eq!(
        e.message,
        "the type `R0` is not monotone in emptiness: a recursive occurrence stands in the \
         domain of a morphism type that stands under `&`, `\\`, a complement or differing \
         domain bounds, or in a definition named there"
    );
}
