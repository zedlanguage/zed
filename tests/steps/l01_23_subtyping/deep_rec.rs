//! A definition body of any depth is copied, compared, written with `Debug` and checked on a
//! small stack: `Clone`, `==` and `Debug` of `rec::Expr`, and the checks `Group::new` makes,
//! keep their own stacks on the heap (COMPLEXITY.md K39).

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};

fn def(body: Expr) -> Def {
    Def {
        name: "T".into(),
        params: Vec::new(),
        body,
    }
}

fn int() -> Expr {
    Expr::Type(Type::int())
}

#[test]
fn debug_writes_the_derived_text() {
    let e = Expr::Union(vec![
        Expr::Param(0),
        Expr::Ref(1, vec![Expr::Param(2)]),
        int(),
        Expr::And(vec![Expr::Param(0)]),
        Expr::Not(Box::new(Expr::Param(1))),
        Expr::Diff(Box::new(Expr::Param(0)), Box::new(Expr::Param(1))),
        Expr::Tuple(vec![]),
        Expr::Atom("n".into(), vec![Expr::Param(0), Expr::Param(1)]),
        Expr::Morphism(
            Box::new(Expr::Param(0)),
            Box::new(Expr::Param(1)),
            Box::new(Expr::Param(2)),
        ),
    ]);
    let t = Type::int();
    let expected = format!(
        "Union([Param(0), Ref(1, [Param(2)]), Type({t:?}), And([Param(0)]), Not(Param(1)), \
         Diff(Param(0), Param(1)), Tuple([]), Atom(\"n\", [Param(0), Param(1)]), \
         Morphism(Param(0), Param(1), Param(2))])"
    );
    assert_eq!(format!("{e:?}"), expected);
    assert_eq!(format!("{e:#?}"), expected);
    assert!(e.clone() == e);
}

/// A body nested `n` deep through each kind of part, with `bottom` at the bottom.
fn nested(n: usize, bottom: fn() -> Expr) -> Vec<(&'static str, Expr)> {
    let b = |f: fn(Expr) -> Expr| (0..n).fold(bottom(), |e, _| f(e));
    vec![
        ("unions", b(|e| Expr::Union(vec![e, int()]))),
        ("intersections", b(|e| Expr::And(vec![int(), e]))),
        ("complements", b(|e| Expr::Not(Box::new(e)))),
        (
            "differences",
            b(|e| Expr::Diff(Box::new(e), Box::new(int()))),
        ),
        ("tuples", b(|e| Expr::Tuple(vec![e]))),
        ("atoms", b(|e| Expr::Atom("n".into(), vec![e, int()]))),
        ("morphisms", b(|e| Expr::exact(int(), e))),
    ]
}

/// The depth of the bodies of the regular tests: each copy, comparison, text and check goes
/// down and back up through many levels of each part, on the default test thread. The same
/// checks at 20,000 levels, past the depth at which the derived `Clone`, `==` and `Debug`
/// overflowed a 2 MiB stack, are in `bench` (TEST-bench-move-l0123, author P178: a test that
/// needs an unusual depth or stack is a benchmark).
const DEPTH: usize = 20;

/// Each body of `nested`, `DEPTH` deep, is copied, compared, written and admitted.
#[test]
fn a_nested_body_of_each_shape_is_copied_compared_written_and_checked() {
    let other = nested(DEPTH, || Expr::Type(Type::string()));
    let all = nested(DEPTH, int)
        .into_iter()
        .zip(nested(DEPTH, int))
        .zip(other);
    let mut seen = 0;
    for (((what, a), (_, b)), (_, c)) in all {
        seen += 1;
        let copy = a.clone();
        assert!(copy == a, "{what}: a copy equals its original");
        assert!(a == b, "{what}: two builds are equal");
        assert!(a != c, "{what}: a different bottom is found");
        let text = format!("{a:?}");
        assert_eq!(text, format!("{copy:?}"), "{what}");
        assert!(text.len() > DEPTH, "{what}: {} bytes", text.len());
        assert!(Group::new(vec![def(a)]).is_ok(), "{what}");
    }
    assert_eq!(seen, 7);
}

/// A recursive occurrence `DEPTH` constructors down is contractive; one under `DEPTH`
/// complements is not monotone.
#[test]
fn a_nested_recursive_occurrence_is_checked() {
    let guarded = (0..DEPTH).fold(Expr::Ref(0, vec![]), |e, _| Expr::Tuple(vec![e]));
    assert!(Group::new(vec![def(Expr::Union(vec![guarded, int()]))]).is_ok());
    let flipped = (0..DEPTH).fold(Expr::Tuple(vec![Expr::Ref(0, vec![])]), |e, _| {
        Expr::Not(Box::new(e))
    });
    assert!(Group::new(vec![def(flipped)]).is_err());
}

/// A nested type kept only by the thread's emptiness tables is freed when the test's thread
/// ends: a small instance of `bench::a_deep_type_kept_by_the_verdicts_is_freed_when_its_thread_ends`
/// (round 8, X39), on the default test thread.
#[test]
fn a_nested_type_kept_by_the_verdicts_is_freed_when_its_thread_ends() {
    Type::forget_emptiness();
    let t = (0..DEPTH).fold(Type::int(), |t, _| Type::tuple(vec![t, Type::int()]));
    assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
}

mod bench;
