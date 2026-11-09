//! The admission check on the named groups of cross-review X14 (wt/xs-cmp/logs/named.txt):
//! a group is accepted only in a form whose emptiness is monotone in the emptiness of its
//! members. The check is sufficient, not necessary: `M6` and `W_andTop` are monotone but
//! rejected, a refusal X14 leaves as known, so their messages say the type is outside the form
//! the checker accepts and never that it is not monotone (item GROUP-admit-msg).
//! `M` is a morphism type with guarantee, permission and value type, `A` a meet, `D` a
//! difference, `T` a pair and `U` a union; `R0` and `R1` are the group's definitions.

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

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
             named: `R0` is named in `R1`, under `&` in `R0 & ((Never) -> int)`{SUFFICIENT}"
        )
    );
}

/// The sentence every refusal of the admission check ends with.
const SUFFICIENT: &str = "; the check is sufficient, not necessary, so a type it refuses may \
                          still be monotone in emptiness. To repair it, write the type so \
                          that no recursive occurrence stands there; one inside a tuple, an \
                          atom's payload, a union or a function's value type is always \
                          accepted";

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
                "a recursive occurrence stands in the guarantee of `(H(A)) -> int \\ A`, whose \
                 value type `int \\ A` has a parameter under a complement or to the right of \
                 `\\`, where a larger argument gives a smaller type, so it may be empty",
            ),
        ),
        (
            "value type empty",
            refusal(&["T"], &[], vec![m(r(0), r(0), ab)]),
            outside(
                "T",
                "a recursive occurrence stands in the guarantee of `(T) -> #a & #b`, whose \
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
                "a recursive occurrence stands in the guarantee of `((M6) -> int) .. Never -> \
                 int`, whose guarantee `(M6) -> int` and permission `Never` differ",
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
                 in an operand of `\\` in `((W) -> int) \\ ((Never) -> int)`",
            ),
        ),
        (
            "in differing domain bounds",
            refusal(&["M5"], &[], vec![m(f(), m(r(0), r(0), int()), int())]),
            outside(
                "M5",
                "a recursive occurrence stands in the guarantee of `(M5) -> int`, which stands \
                 in the domain bounds of `((Never) -> int) .. ((M5) -> int) -> int`, which differ",
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
                 `&` in `B & ((Never) -> int)`",
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
             `&` in `D2 & ((Never) -> int)`{SUFFICIENT}"
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

/// The one-definition group `name(a) = body` at the argument `arg`.
fn instance(name: &str, body: Expr, arg: Type) -> Type {
    let def = Def {
        name: name.into(),
        params: vec!["a".into()],
        body,
    };
    Group::new(vec![def]).unwrap().instance(vec![arg]).remove(0)
}

/// `#nil | #c(a, N(a))`.
fn list_body() -> Expr {
    let tail = Expr::Ref(0, vec![Expr::Param(0)]);
    Expr::Union(vec![
        Expr::Type(Type::atom("nil")),
        atom("c", vec![Expr::Param(0), tail]),
    ])
}

/// `() | (a, N(a))`.
fn seq_body() -> Expr {
    let tail = Expr::Ref(0, vec![Expr::Param(0)]);
    Expr::Union(vec![
        Expr::Type(Type::tuple(vec![])),
        pair(Expr::Param(0), tail),
    ])
}

/// `#nil | #c(a, (a, N(a)))`: the pair is a part of the group, kept unevaluated.
fn nested_body() -> Expr {
    let tail = Expr::Ref(0, vec![Expr::Param(0)]);
    Expr::Union(vec![
        Expr::Type(Type::atom("nil")),
        atom("c", vec![Expr::Param(0), pair(Expr::Param(0), tail)]),
    ])
}

/// Item PRINT-fmt-audit: a refused group writes each type its definitions hold in the surface
/// syntax, a recursive type by its group's name (`Type::surface_by_name`), its arguments and
/// the parts of the group in the surface syntax too. Before, a type that needed a definition of
/// its own was written in the kernel's internal prefix form, which no program can contain:
///
/// - `L(int | #x)` was `L((| int #x))`
/// - `L(int ->? int)` was `L((->? int int))`
/// - `(int | #x, int | #x)` was `(tuple (| int #x) (| int #x))`
/// - `#c(int | #x, L(int | #x)) & #c(int, _)` was
///   `(#c (& (tuple (| int #x) L((| int #x))) (tuple int _)))`
/// - `#w() | #w(int, P(int))` was `(#w (| (tuple) (tuple int P(int))))`
/// - `#c(int, _) & #c(int, M(int))` was `(#c (& (tuple int M(int)) (tuple int _)))`
/// - `Q(int | #x)` was `Q((| int #x))`
/// - `#c(int | #x, (int | #x, Q(int | #x))) & #c(int, _)` was
///   `(#c (& (tuple (| int #x) ((| int #x), Q((| int #x)))) (tuple int _)))`
///
/// `int | (int ->? int)`, `M(int)` and `P(int)` were written so before too. Each text parses as
/// a type; that the printer's text reads back as the same type is tested at the printer
/// (l01_22 `surface`).
#[test]
fn a_refused_group_writes_the_types_it_holds_as_a_program_would() {
    let int_or_x = &Type::int() | &Type::atom("x");
    let partial = Type::morphism(Type::empty(), Type::int(), Type::int());
    let l = instance("L", list_body(), int_or_x.clone());
    let m = instance("M", list_body(), Type::int());
    let p = instance("P", seq_body(), Type::int());
    let q = instance("Q", nested_body(), int_or_x.clone());
    let c_int = Type::atom_with("c", &Type::tuple(vec![Type::int(), Type::top()]));
    // Each type, its text, and whether the text stands unparenthesized on the left of `\`.
    for (t, text, primary) in [
        (l.clone(), "L(int | #x)", true),
        (
            instance("L", list_body(), partial.clone()),
            "L(int ->? int)",
            true,
        ),
        (
            Type::tuple(vec![int_or_x.clone(), int_or_x.clone()]),
            "(int | #x, int | #x)",
            true,
        ),
        (&l & &c_int, "#c(int | #x, L(int | #x)) & #c(int, _)", false),
        (&Type::int() | &partial, "int | (int ->? int)", false),
        (Type::atom_with("w", &p), "#w() | #w(int, P(int))", false),
        (m.clone(), "M(int)", true),
        (&m & &c_int, "#c(int, _) & #c(int, M(int))", false),
        (p, "P(int)", true),
        (q.clone(), "Q(int | #x)", true),
        (
            &q & &c_int,
            "#c(int | #x, (int | #x, Q(int | #x))) & #c(int, _)",
            false,
        ),
    ] {
        let message = refusal(
            &["N"],
            &[],
            vec![diff(Expr::Type(t), atom("b", vec![r(0)]))],
        );
        let left = match primary {
            true => text.to_string(),
            false => format!("({text})"),
        };
        assert!(
            message.contains(&format!("in `{left} \\ #b(N)`")),
            "{text}: {message}"
        );
        let tokens = lex_fence(text).unwrap();
        parse(text, &tokens, "Type", TOP).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    }
}
