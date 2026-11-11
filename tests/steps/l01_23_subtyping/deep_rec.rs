//! A definition body of any depth is copied, compared, written with `Debug` and checked on a
//! small stack: `Clone`, `==` and `Debug` of `rec::Expr`, and the checks `Group::new` makes,
//! keep their own stacks on the heap (COMPLEXITY.md K39).

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_tests::scaling;

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

#[test]
fn a_body_far_deeper_than_the_stack_is_copied_compared_written_and_checked() {
    // The derived `Clone`, `==` and `Debug`, and the recursive checks, overflowed a 2 MiB
    // stack near 10,000 levels.
    let n = 100_000;
    zed_tests::deep::on_small_stack(|| {
        let other = nested(n, || Expr::Type(Type::string()));
        for (((what, a), (_, b)), (_, c)) in
            nested(n, int).into_iter().zip(nested(n, int)).zip(other)
        {
            let copy = a.clone();
            assert!(copy == a, "{what}: a copy equals its original");
            assert!(a == b, "{what}: two builds are equal");
            assert!(a != c, "{what}: a different bottom is found");
            let text = format!("{a:?}");
            assert_eq!(text, format!("{copy:?}"), "{what}");
            assert!(text.len() > n, "{what}: {} bytes", text.len());
            assert!(Group::new(vec![def(a)]).is_ok(), "{what}");
        }
        // A recursive occurrence n constructors down is contractive; one under n complements
        // is not monotone.
        let guarded = (0..n).fold(Expr::Ref(0, vec![]), |e, _| Expr::Tuple(vec![e]));
        assert!(Group::new(vec![def(Expr::Union(vec![guarded, int()]))]).is_ok());
        let flipped = (0..n).fold(Expr::Tuple(vec![Expr::Ref(0, vec![])]), |e, _| {
            Expr::Not(Box::new(e))
        });
        assert!(Group::new(vec![def(flipped)]).is_err());
    });
}

#[test]
fn copying_comparing_writing_and_checking_scale_with_depth() {
    let n = 20_000;
    zed_tests::deep::on_small_stack(|| {
        let (small, large) = (
            (nested(n, int), nested(n, int)),
            (nested(8 * n, int), nested(8 * n, int)),
        );
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
            // The copy is linear, timed above.
            scaling::check(&format!("checking a body of {what}"), n, |k| {
                assert!(Group::new(vec![def(at(k).0[i].1.clone())]).is_ok());
            });
        }
    });
}

/// Round 8 (X39): a deep type kept only by the thread's emptiness tables is freed when the
/// thread ends. `forget_emptiness` uses those tables before the thread makes any type, so they
/// were dropped after the queue that frees types in a loop, and the type was freed by
/// recursion: `r6two` at `n` 4096 overflowed a 256 MiB stack so.
#[test]
fn a_deep_type_kept_by_the_verdicts_is_freed_when_its_thread_ends() {
    scaling::on_a_thread(1 << 20, || {
        Type::forget_emptiness();
        let t = (0..100_000).fold(Type::int(), |t, _| Type::tuple(vec![t, Type::int()]));
        assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
    });
}
