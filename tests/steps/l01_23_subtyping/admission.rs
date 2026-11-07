//! The admission check on the named groups of cross-review X14 (wt/xs-cmp/logs/named.txt):
//! a group is accepted only in a form whose emptiness is monotone in the emptiness of its
//! members. The check is sufficient, not necessary: `M6` and `W_andTop` are monotone but
//! rejected, a refusal X14 leaves as known, so their messages say the type is outside the form
//! the checker accepts and never that it is not monotone (item GROUP-admit-msg).
//! `M` is a morphism type with guarantee, permission and value type, `A` a meet, `D` a
//! difference, `T` a pair and `U` a union; `R0` and `R1` are the group's definitions.

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
        format!(
            "the type `R0` is outside the form the checker accepts: a recursive occurrence \
             stands in the guarantee of `(R1) -> int`, in `R0`, which is narrowed where it is \
             named: `R0` is named in `R1`, under `&` in `R0 & ((!_) -> int)`{SUFFICIENT}"
        )
    );
}

/// The sentence every refusal of the admission check ends with.
const SUFFICIENT: &str = "; the check is sufficient, not necessary, so a type it refuses may \
                          still be monotone in emptiness";

/// The rejection of the group of `bodies`, named by `names`, each taking `params`.
fn refusal(names: &[&str], params: &[&str], bodies: Vec<Expr>) -> String {
    let defs = bodies
        .into_iter()
        .zip(names)
        .map(|(body, name)| Def {
            name: (*name).into(),
            params: params.iter().map(|p| (*p).into()).collect(),
            body,
        })
        .collect();
    Group::new(defs).unwrap_err().message
}

fn atom(name: &str, items: Vec<Expr>) -> Expr {
    Expr::Atom(name.into(), items)
}

fn not(a: Expr) -> Expr {
    Expr::Not(Box::new(a))
}

/// One refusal per arm of the admission check, each naming its reason and the expression where
/// it holds, in types a user can write back; a definition narrowed where it is named also gets
/// the definitions it is named through.
fn arms() -> Vec<(&'static str, String, String)> {
    let f = || m(empty(), empty(), int());
    let p = || Expr::Param(0);
    let h = || Expr::Ref(0, vec![p()]);
    let ab = and(Expr::Type(Type::atom("a")), Expr::Type(Type::atom("b")));
    let outside = |name: &str, why: &str| {
        format!("the type `{name}` is outside the form the checker accepts: {why}{SUFFICIENT}")
    };
    vec![
        (
            "complement",
            refusal(&["N"], &[], vec![atom("a", vec![not(r(0))])]),
            outside(
                "N",
                "a recursive occurrence stands under a complement, in `!N`, which is not \
                 monotone in `N`: a larger `N` gives a smaller `!N`",
            ),
        ),
        (
            "right of \\",
            refusal(&["N"], &[], vec![diff(int(), atom("b", vec![r(0)]))]),
            outside(
                "N",
                "a recursive occurrence stands to the right of `\\`, in `int \\ #b(N)`, which \
                 is not monotone in `#b(N)`: a larger `#b(N)` gives a smaller `int \\ #b(N)`",
            ),
        ),
        (
            "value type mentions the group",
            refusal(&["U"], &[], vec![m(r(0), r(0), r(0))]),
            outside(
                "U",
                "a recursive occurrence stands in the guarantee of `(U) -> U`, whose value type \
                 `U` mentions the group",
            ),
        ),
        (
            "value type shrinks as a parameter grows",
            refusal(&["H"], &["A"], vec![m(h(), h(), diff(int(), p()))]),
            outside(
                "H",
                "a recursive occurrence stands in the guarantee of `(H(A)) -> (int \\ A)`, whose \
                 value type `int \\ A` has a parameter under a complement or to the right of \
                 `\\`, where a larger argument gives a smaller type, so it may be empty",
            ),
        ),
        (
            "value type empty",
            refusal(&["T"], &[], vec![m(r(0), r(0), ab)]),
            outside(
                "T",
                "a recursive occurrence stands in the guarantee of `(T) -> (#a & #b)`, whose \
                 value type `#a & #b` is empty",
            ),
        ),
        (
            "value type empty at empty parameters",
            refusal(&["F"], &["A"], vec![m(h(), h(), p())]),
            outside(
                "F",
                "a recursive occurrence stands in the guarantee of `(F(A)) -> A`, whose value \
                 type `A` is empty when every parameter is `empty`",
            ),
        ),
        (
            "guarantee and permission differ",
            refusal(&["M6"], &[], vec![m(m(r(0), r(0), int()), empty(), int())]),
            outside(
                "M6",
                "a recursive occurrence stands in the guarantee of `((M6) -> int) .. !_ -> \
                 int`, whose guarantee `(M6) -> int` and permission `!_` differ",
            ),
        ),
        (
            "under &",
            refusal(&["W_andTop"], &[], vec![and(m(r(0), r(0), int()), top())]),
            outside(
                "W_andTop",
                "a recursive occurrence stands in the guarantee of `(W_andTop) -> int`, which \
                 stands under `&` in `((W_andTop) -> int) & _`",
            ),
        ),
        (
            "in an operand of \\",
            refusal(&["W"], &[], vec![diff(m(r(0), r(0), int()), f())]),
            outside(
                "W",
                "a recursive occurrence stands in the guarantee of `(W) -> int`, which stands \
                 in an operand of `\\` in `((W) -> int) \\ ((!_) -> int)`",
            ),
        ),
        (
            "in differing domain bounds",
            refusal(&["M5"], &[], vec![m(f(), m(r(0), r(0), int()), int())]),
            outside(
                "M5",
                "a recursive occurrence stands in the guarantee of `(M5) -> int`, which stands \
                 in the domain bounds of `((!_) -> int) .. ((M5) -> int) -> int`, which differ",
            ),
        ),
        (
            "named under & through two definitions",
            refusal(
                &["A", "B", "C"],
                &[],
                vec![m(r(1), r(1), int()), pair(int(), r(0)), and(r(1), f())],
            ),
            outside(
                "A",
                "a recursive occurrence stands in the guarantee of `(B) -> int`, in `A`, which \
                 is narrowed where it is named: `A` is named in `B`; `B` is named in `C`, under \
                 `&` in `B & ((!_) -> int)`",
            ),
        ),
    ]
}

#[test]
fn each_arm_names_its_reason() {
    for (arm, got, expected) in arms() {
        assert_eq!(got, expected, "{arm}");
    }
}

/// "Not monotone" is said only where it is proved: of a complement and of the right of `\`,
/// each not monotone in its operand. `M6` and `W_andTop` are monotone (X14,
/// wt/xs-cmp/logs/admit_named.log) and are refused without it.
#[test]
fn not_monotone_only_where_proved() {
    for (arm, got, _) in arms() {
        let proved = matches!(arm, "complement" | "right of \\");
        assert_eq!(got.contains("not monotone"), proved, "{arm}: {got}");
        assert!(
            !got.contains("is not monotone in emptiness"),
            "{arm}: {got}"
        );
    }
}

/// `D0 = (D1) -> int`, each `Di = (int, D(i-1))`, and the last `(int, D(n-2) & ((empty) ->
/// int))`: `D0` is narrowed through the `n - 1` definitions after it, each named in the
/// next.
fn chain(n: usize) -> Vec<Def> {
    let f = || m(empty(), empty(), int());
    (0..n)
        .map(|i| Def {
            name: format!("D{i}"),
            params: vec![],
            body: match i {
                0 => m(r(1), r(1), int()),
                _ if i + 1 == n => pair(int(), and(r(i - 1), f())),
                _ => pair(int(), r(i - 1)),
            },
        })
        .collect()
}

#[test]
fn a_refusal_names_the_whole_path() {
    let message = Group::new(chain(4)).unwrap_err().message;
    assert_eq!(
        message,
        format!(
            "the type `D0` is outside the form the checker accepts: a recursive occurrence \
             stands in the guarantee of `(D1) -> int`, in `D0`, which is narrowed where it is \
             named: `D0` is named in `D1`; `D1` is named in `D2`; `D2` is named in `D3`, under \
             `&` in `D2 & ((!_) -> int)`{SUFFICIENT}"
        )
    );
}

/// The refusal of a chain of `n` definitions, whose path names all of them, is found and
/// written in time linear in `n`.
#[test]
fn a_refusal_through_a_long_path_scales() {
    let n = 512;
    let groups = zed_tests::scaling::inputs(n, chain);
    zed_tests::scaling::check("refusing a group narrowed through a chain", n, |n| {
        let message = Group::new(groups[&n].clone()).unwrap_err().message;
        assert!(message.contains(&format!("`D{}` is named in `D{}`", n - 2, n - 1)));
    });
}
