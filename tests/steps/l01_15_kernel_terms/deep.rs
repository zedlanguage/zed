//! `Clone`, `==` and `Debug` of kernel terms keep their own stacks on the heap (COMPLEXITY.md
//! K39), so a term of any depth is copied, compared and written on a small stack, and `Debug`
//! writes the text a derived `Debug` wrote.

use std::collections::BTreeMap;

use zed_kernel::term::{FixKind, Grade, GuardPos, Pattern, Prim, Witness};
use zed_kernel::types::Type;
use zed_kernel::{Shared, Term, Value};
use zed_tests::scaling;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn sh(t: Term) -> Shared {
    Shared::new(t)
}

/// One term with every variant of `Term` and `Pattern`.
fn every_variant() -> Term {
    let ev: BTreeMap<_, _> = [("associative".into(), Grade::Axiom)].into();
    let pats = vec![
        (Pattern::Wild, var("a")),
        (Pattern::Bind("x".into()), var("b")),
        (Pattern::Lit(Value::Int(3)), var("c")),
        (
            Pattern::Atom(
                "cons".into(),
                vec![Pattern::Wild, Pattern::Bind("t".into())],
            ),
            var("d"),
        ),
        (
            Pattern::Fields("node".into(), vec![("next".into(), Pattern::AnyAtom)]),
            var("e"),
        ),
        (
            Pattern::Tuple(vec![Pattern::Is(Type::int()), Pattern::Tuple(vec![])]),
            var("f"),
        ),
    ];
    let parts = vec![
        Term::Lit(Value::str("q\"s")),
        Term::Lam(vec!["x".into(), "y".into()], sh(var("x"))),
        Term::App(sh(var("f")), vec![var("a"), Term::PrimFn(Prim::Add)]),
        Term::Let("x".into(), sh(var("a")), sh(var("x"))),
        Term::If(sh(var("c")), sh(var("a")), sh(var("b"))),
        Term::Match(sh(var("v")), pats),
        Term::Fam {
            domain: sh(var("D")),
            var: "i".into(),
            body: sh(var("i")),
        },
        Term::Reindex {
            family: sh(var("F")),
            kf: sh(var("kf")),
            vf: sh(var("vf")),
            witness: Witness::Catalog("swap".into()),
        },
        Term::Reindex {
            family: sh(var("F")),
            kf: sh(var("kf")),
            vf: sh(var("vf")),
            witness: Witness::Residue,
        },
        Term::Discard {
            family: sh(var("F")),
            sel: sh(var("s")),
        },
        Term::Fold {
            family: sh(var("F")),
            op: sh(Term::PrimFn(Prim::Add)),
            identity: Some(sh(Term::Lit(Value::Int(0)))),
            depth: 2,
            ev: ev.clone(),
        },
        Term::Fold {
            family: sh(var("F")),
            op: sh(var("op")),
            identity: None,
            depth: 1,
            ev: BTreeMap::new(),
        },
        Term::Fix {
            init: sh(var("bot")),
            step: sh(var("st")),
            this: "this".into(),
            key: "k".into(),
            kind: FixKind::Lattice {
                join: sh(Term::PrimFn(Prim::Union)),
            },
            ev: ev.clone(),
        },
        Term::Fix {
            init: sh(var("D")),
            step: sh(var("b")),
            this: "me".into(),
            key: "k".into(),
            kind: FixKind::Definedness,
            ev,
        },
        Term::Gen {
            init: sh(var("i")),
            step: sh(var("s")),
            guard: sh(var("g")),
            pos: GuardPos::After,
        },
        Term::Read("in".into()),
        Term::Push("out".into(), sh(var("v"))),
    ];
    Term::Prim(Prim::Tuple, parts)
}

#[test]
fn debug_writes_the_derived_text() {
    let t = every_variant();
    let expected = include_str!("deep_debug.txt").trim_end();
    assert_eq!(format!("{t:?}"), expected);
    // On one line under `{:#?}` too, as `Value`'s `Debug` writes it.
    assert_eq!(format!("{t:#?}"), expected);
}

/// A term nested `n` deep through each kind of part that nests: lambda bodies (a [`Shared`]),
/// the arguments of a sum (a `Vec`), the arms of a `match`, and a pattern of tuples, each built
/// afresh so that no two builds share a subterm.
fn nested(n: usize) -> Vec<(&'static str, Term)> {
    let lams = (0..n).fold(var("x"), |b, _| Term::Lam(vec!["y".into()], sh(b)));
    let sum = (0..n).fold(var("x"), |a, _| {
        Term::Prim(Prim::Add, vec![a, Term::Lit(Value::Int(1))])
    });
    let arms = (0..n).fold(var("x"), |b, _| {
        Term::Match(sh(var("v")), vec![(Pattern::Wild, b)])
    });
    let pattern = (0..n).fold(Pattern::Bind("p".into()), |p, _| {
        Pattern::Tuple(vec![p, Pattern::Wild])
    });
    let deep_pattern = Term::Match(sh(var("v")), vec![(pattern, var("x"))]);
    vec![
        ("nested lambdas", lams),
        ("a left-nested sum", sum),
        ("nested `match` arms", arms),
        ("a nested tuple pattern", deep_pattern),
    ]
}

#[test]
fn a_term_far_deeper_than_the_stack_copies_compares_and_prints() {
    // A derived `Clone`, `==` or `Debug` overflows a 2 MiB stack near 10,000 levels.
    let n = 100_000;
    zed_tests::deep::on_small_stack(|| {
        for ((what, a), (_, b)) in nested(n).into_iter().zip(nested(n)) {
            let copy = a.clone();
            assert!(copy == a, "{what}: a copy equals its original");
            assert!(a == b, "{what}: two builds are equal");
            let text = format!("{a:?}");
            assert_eq!(text, format!("{b:?}"), "{what}");
            assert_eq!(text, format!("{copy:?}"), "{what}");
            assert!(text.len() > n, "{what}: {} bytes", text.len());
        }
        // One leaf changed at the bottom is found.
        let differ = (0..n).fold(var("z"), |b, _| Term::Lam(vec!["y".into()], sh(b)));
        let (_, lams) = nested(n).swap_remove(0);
        assert!(lams != differ);
    });
}

/// `n` levels of `if s { s } else { s }`, each level's three parts one shared subterm: a DAG
/// of `n + 1` nodes with `3^n` paths.
fn dag(n: usize) -> Term {
    (0..n).fold(var("x"), |t, _| {
        let s = sh(t);
        Term::If(s.clone(), s.clone(), s)
    })
}

#[test]
fn equal_dags_compare_once_per_shared_pair() {
    // Two DAGs built apart share no subterm, so no pair is equal by its id alone: a walk of
    // the paths reads 3^60 of them.
    zed_tests::deep::on_small_stack(|| {
        assert!(dag(60) == dag(60));
        assert!(dag(60) != dag(59));
        // Each level holds its one subterm three times, so the drop of a level was the last
        // holder of the level below inside its own drop, which recursed: a deep DAG
        // overflowed the stack.
        drop(dag(100_000));
    });
}

#[test]
fn copying_comparing_and_printing_scale_with_size() {
    let n = 20_000;
    zed_tests::deep::on_small_stack(|| {
        let built = |k: usize| (nested(k), nested(k));
        let (small, large) = (built(n), built(8 * n));
        let at = |k: usize| if k == n { &small } else { &large };
        for i in 0..small.0.len() {
            let what = small.0[i].0;
            scaling::check(&format!("copying {what}"), n, |k| {
                drop(std::hint::black_box(at(k).0[i].1.clone()));
            });
            scaling::check(&format!("comparing {what}"), n, |k| {
                let (a, b) = at(k);
                assert!(std::hint::black_box(a[i].1 == b[i].1));
            });
            scaling::check(&format!("writing the Debug text of {what}"), n, |k| {
                std::hint::black_box(format!("{:?}", at(k).0[i].1));
            });
        }
        let (small, large) = ((dag(n), dag(n)), (dag(8 * n), dag(8 * n)));
        scaling::check("comparing a DAG of shared subterms", n, |k| {
            let (a, b) = if k == n { &small } else { &large };
            assert!(std::hint::black_box(a == b));
        });
    });
}
