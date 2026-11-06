//! Every form the printer writes, each term at widths 20, 40 and 80 and on one line, compared with
//! the text in forms.txt. That text was written by the recursive printer of step L1.15, before
//! step T2-types-rest rewrote it on a stack of its own, so a change of layout fails here.

use zed_kernel::print::pretty;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{FixKind, Grade, GuardPos, Pattern, Prim, Term, Value, Witness};
use zed_tests::kernel::*;

fn atom_term(name: Term, fields: Option<&[&str]>, payload: Vec<Term>) -> Term {
    let names = match fields {
        Some(fs) => Value::tuple(fs.iter().map(|f| Value::str(f)).collect()),
        None => Value::tuple(vec![]),
    };
    let mut args = vec![name, Term::Lit(names)];
    args.extend(payload);
    prim(Prim::Atom, args)
}

/// One term per form of `Term` and `Pattern`, and per way the printer writes a primitive, each
/// long enough to break at width 20 or 40.
fn forms() -> Vec<(&'static str, Term)> {
    let order = |f: &str| get(var("order"), lit(f));
    let ev: zed_kernel::Evidence = [
        ("associative".into(), Grade::Axiom),
        ("commutative".into(), Grade::Proved),
    ]
    .into();
    let arms = vec![
        (Pattern::Wild, lit("anything")),
        (Pattern::Bind("amount".into()), var("amount")),
        (Pattern::Lit(Value::Int(0)), lit("zero")),
        (Pattern::Lit(Value::str("none")), lit("none")),
        (Pattern::Atom("empty".into(), vec![]), lit("empty")),
        (
            Pattern::Atom(
                "cons".into(),
                vec![Pattern::Bind("head".into()), Pattern::Wild],
            ),
            var("head"),
        ),
        (
            Pattern::Fields(
                "err".into(),
                vec![
                    ("code".into(), Pattern::Bind("c".into())),
                    ("line".into(), Pattern::Lit(Value::Int(3))),
                ],
            ),
            var("c"),
        ),
        (
            Pattern::Tuple(vec![Pattern::Bind("only".into())]),
            var("only"),
        ),
        (Pattern::Tuple(vec![]), lit("unit")),
        (
            Pattern::Tuple(vec![
                Pattern::Bind("x".into()),
                Pattern::Tuple(vec![Pattern::Wild, Pattern::Bind("y".into())]),
            ]),
            add(var("x"), var("y")),
        ),
        (Pattern::AnyAtom, lit("failed")),
        (Pattern::Is(Type::int()), lit("an integer")),
    ];
    vec![
        (
            "literals",
            prim(
                Prim::Tuple,
                vec![
                    lit(42),
                    lit(-7),
                    lit("a \"quoted\" word"),
                    lit(true),
                    Term::Lit(Value::float(2.5)),
                    Term::Lit(Value::tuple(vec![Value::Int(1), Value::str("b")])),
                    Term::Lit(Value::atom("empty")),
                ],
            ),
        ),
        ("a one-parameter lambda", lam(&["order"], order("total"))),
        (
            "a two-parameter lambda",
            lam(&["subtotal", "rate"], mul(var("subtotal"), var("rate"))),
        ),
        (
            "a call of a name",
            app(
                var("discounted"),
                vec![var("subtotal"), lit(10), var("customerTier")],
            ),
        ),
        (
            "a call of an operator and of a primitive function",
            prim(
                Prim::Tuple,
                vec![
                    app(Term::PrimFn(Prim::Add), vec![var("left"), var("right")]),
                    app(Term::PrimFn(Prim::Max), vec![var("left"), var("right")]),
                ],
            ),
        ),
        (
            "a call of a lambda",
            app(
                lam(&["price"], mul(var("price"), lit(2))),
                vec![var("basePrice")],
            ),
        ),
        (
            "a call of a call",
            app(app(var("curried"), vec![var("first")]), vec![var("second")]),
        ),
        (
            "tuples of zero, one and three items",
            prim(
                Prim::Tuple,
                vec![
                    prim(Prim::Tuple, vec![]),
                    prim(Prim::Tuple, vec![var("single")]),
                    prim(Prim::Tuple, vec![var("first"), var("second"), var("third")]),
                ],
            ),
        ),
        (
            "atoms with fields, by position, with a computed name, and with no arguments",
            prim(
                Prim::Tuple,
                vec![
                    atom_term(
                        lit("err"),
                        Some(&["code", "line"]),
                        vec![lit(3), var("lineNumber")],
                    ),
                    atom_term(lit("ok"), None, vec![var("total")]),
                    atom_term(var("which"), None, vec![var("payload")]),
                    prim(Prim::Atom, vec![]),
                ],
            ),
        ),
        (
            "negations and nots",
            prim(
                Prim::Tuple,
                vec![
                    prim(Prim::Neg, vec![var("balance")]),
                    prim(Prim::Neg, vec![add(var("debit"), var("fee"))]),
                    prim(Prim::Neg, vec![lit(-3)]),
                    prim(Prim::Neg, vec![prim(Prim::Neg, vec![var("x")])]),
                    not(eq(var("status"), lit("open"))),
                    not(lam(&["x"], var("x"))),
                ],
            ),
        ),
        (
            "indices on a name, a chain and a block",
            prim(
                Prim::Tuple,
                vec![
                    get(get(var("orders"), lit("alice")), lit("total")),
                    nth(nth(var("matrix"), 2), 3),
                    get(if_(var("c"), var("a"), var("b")), var("key")),
                ],
            ),
        ),
        (
            "infix operators",
            and(
                le(
                    sub(var("total"), sub(var("discount"), var("fee"))),
                    bin(Prim::Pow, prim(Prim::Neg, vec![var("base")]), lit(2)),
                ),
                bin(Prim::Concat, var("prefix"), var("suffix")),
            ),
        ),
        (
            "primitives written by name",
            prim(
                Prim::Tuple,
                vec![
                    prim(Prim::Min, vec![var("left"), var("right")]),
                    count(var("orders")),
                    prim(Prim::Show, vec![var("amount")]),
                    prim(Prim::Add, vec![var("a"), var("b"), var("c")]),
                ],
            ),
        ),
        (
            "primitives as values",
            prim(
                Prim::Tuple,
                vec![
                    Term::PrimFn(Prim::Neg),
                    Term::PrimFn(Prim::Not),
                    Term::PrimFn(Prim::TupleGet),
                    Term::PrimFn(Prim::Get),
                    Term::PrimFn(Prim::Add),
                    Term::PrimFn(Prim::Min),
                ],
            ),
        ),
        (
            "a block of bindings",
            let_(
                "subtotal",
                mul(var("quantity"), var("unitPrice")),
                let_(
                    "tax",
                    mul(var("subtotal"), var("rate")),
                    add(var("subtotal"), var("tax")),
                ),
            ),
        ),
        (
            "an if with an if in its else branch",
            if_(
                le(var("subtotal"), lit(100)),
                var("subtotal"),
                if_(
                    le(var("subtotal"), lit(1000)),
                    app(var("discounted"), vec![var("subtotal"), lit(5)]),
                    app(var("discounted"), vec![var("subtotal"), lit(10)]),
                ),
            ),
        ),
        (
            "a match with every pattern",
            Term::Match(rc(var("value")), arms),
        ),
        (
            "a family",
            fam(var("lines"), "line", mul(var("quantity"), var("price"))),
        ),
        (
            "reindexes with each witness",
            prim(
                Prim::Tuple,
                vec![
                    reindex(
                        var("orders"),
                        lam(
                            &["k", "v"],
                            path(vec![get(var("v"), lit("customer")), var("k")]),
                        ),
                        lam(&["k", "v"], var("v")),
                    ),
                    Term::Reindex {
                        family: rc(var("pairs")),
                        kf: rc(var("swap")),
                        vf: rc(var("same")),
                        witness: Witness::Catalog("swap".into()),
                    },
                ],
            ),
        ),
        (
            "a discard",
            discard(
                var("orders"),
                lam(&["k", "o"], eq(get(var("o"), lit("open")), lit(true))),
            ),
        ),
        (
            "folds with and without an identity",
            prim(
                Prim::Tuple,
                vec![
                    Term::Fold {
                        family: rc(var("lineTotals")),
                        op: rc(Term::PrimFn(Prim::Add)),
                        identity: Some(rc(lit(0))),
                        depth: 2,
                        ev: ev.clone(),
                    },
                    fold(var("prices"), Term::PrimFn(Prim::Max), None),
                ],
            ),
        ),
        (
            "fixes of each kind",
            prim(
                Prim::Tuple,
                vec![
                    Term::Fix {
                        init: rc(var("start")),
                        step: rc(var("reachableStep")),
                        this: "this".into(),
                        key: "k".into(),
                        kind: FixKind::Lattice {
                            join: rc(Term::PrimFn(Prim::Union)),
                        },
                        ev: ev.clone(),
                    },
                    Term::Fix {
                        init: rc(var("indices")),
                        step: rc(app(var("this"), vec![sub(var("k"), lit(1))])),
                        this: "this".into(),
                        key: "k".into(),
                        kind: FixKind::Definedness,
                        ev: zed_kernel::Evidence::new(),
                    },
                ],
            ),
        ),
        (
            "generators with each guard position",
            prim(
                Prim::Tuple,
                vec![
                    Term::Gen {
                        init: rc(lit(10)),
                        step: rc(lam(&["n"], sub(var("n"), lit(1)))),
                        guard: rc(lam(&["n"], lt(lit(0), var("n")))),
                        pos: GuardPos::Before,
                    },
                    Term::Gen {
                        init: rc(var("state")),
                        step: rc(var("advance")),
                        guard: rc(var("running")),
                        pos: GuardPos::After,
                    },
                ],
            ),
        ),
        (
            "reading and pushing ports",
            Term::Push(
                "stdout".into(),
                rc(app(var("report"), vec![Term::Read("stdin".into())])),
            ),
        ),
        (
            "nested forms",
            let_(
                "byRegion",
                reindex(
                    discard(var("sales"), lam(&["s"], eq(var("s"), var("week")))),
                    lam(
                        &["k", "s"],
                        path(vec![get(var("s"), lit("region")), var("k")]),
                    ),
                    lam(&["k", "s"], var("s")),
                ),
                Term::Match(
                    rc(get(var("byRegion"), lit("north"))),
                    vec![
                        (Pattern::AnyAtom, lit(0)),
                        (
                            Pattern::Bind("f".into()),
                            fold(var("f"), Term::PrimFn(Prim::Add), Some(lit(0))),
                        ),
                    ],
                ),
            ),
        ),
    ]
}

/// The text of every form at each width, in the layout of forms.txt.
fn text() -> String {
    let mut out = String::new();
    for (what, t) in forms() {
        let flat = t.to_string();
        assert_eq!(pretty(&t, usize::MAX), flat, "{what}");
        for width in [20, 40, 80] {
            out += &format!("--- {what}, width {width}\n{}\n", pretty(&t, width));
        }
        out += &format!("--- {what}, on one line\n{flat}\n");
    }
    out
}

#[test]
fn every_form_is_written_as_before_at_each_width() {
    let expected = include_str!("forms.txt");
    let actual = text();
    for (i, (a, e)) in actual.lines().zip(expected.lines()).enumerate() {
        assert_eq!(a, e, "line {}", i + 1);
    }
    assert_eq!(actual, expected);
}
