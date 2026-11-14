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

/// The depth of the deep bodies: twice the depth near which the derived `Clone`, `==` and
/// `Debug`, and the recursive checks, overflowed the 2 MiB stack of `deep::on_small_stack`
/// (near 10,000 levels).
const DEEP: usize = 20_000;

/// The bodies of `nested` from `first` to `last` (in its order), `DEEP` deep, are copied,
/// compared, written and admitted on a 2 MiB stack.
fn shapes_on_a_small_stack(first: &str, last: &str) {
    zed_tests::deep::on_small_stack(|| {
        let other = nested(DEEP, || Expr::Type(Type::string()));
        let all = nested(DEEP, int)
            .into_iter()
            .zip(nested(DEEP, int))
            .zip(other);
        let from = all.skip_while(|(((what, _), _), _)| *what != first);
        let mut seen = 0;
        for (((what, a), (_, b)), (_, c)) in from {
            seen += 1;
            let copy = a.clone();
            assert!(copy == a, "{what}: a copy equals its original");
            assert!(a == b, "{what}: two builds are equal");
            assert!(a != c, "{what}: a different bottom is found");
            let text = format!("{a:?}");
            assert_eq!(text, format!("{copy:?}"), "{what}");
            assert!(text.len() > DEEP, "{what}: {} bytes", text.len());
            assert!(Group::new(vec![def(a)]).is_ok(), "{what}");
            if what == last {
                break;
            }
        }
        assert!(seen > 0, "no shape from {first} to {last}");
    });
}

// The body test ran all seven shapes and the two recursive occurrences at depth 100,000 in one
// test (5.2 s alone); now it runs them at depth `DEEP`, 20,000, twice the depth its comment
// gave for the overflow of the 2 MiB stack, in two tests, the first four shapes and then the
// other three with the recursive occurrences (TEST-bench-move-l0123, author P169: a deep-stack
// test uses the smallest depth that still overflows the stack in the code it guards against).

#[test]
fn a_body_far_deeper_than_the_stack_is_copied_compared_written_and_checked() {
    shapes_on_a_small_stack("unions", "differences");
}

#[test]
fn a_deep_body_of_tuples_atoms_or_morphisms_is_copied_compared_written_and_checked() {
    shapes_on_a_small_stack("tuples", "morphisms");
    zed_tests::deep::on_small_stack(|| {
        // A recursive occurrence `DEEP` constructors down is contractive; one under `DEEP`
        // complements is not monotone.
        let guarded = (0..DEEP).fold(Expr::Ref(0, vec![]), |e, _| Expr::Tuple(vec![e]));
        assert!(Group::new(vec![def(Expr::Union(vec![guarded, int()]))]).is_ok());
        let flipped = (0..DEEP).fold(Expr::Tuple(vec![Expr::Ref(0, vec![])]), |e, _| {
            Expr::Not(Box::new(e))
        });
        assert!(Group::new(vec![def(flipped)]).is_err());
    });
}

/// Round 8 (X39): a deep type kept only by the thread's emptiness tables is freed when the
/// thread ends. `forget_emptiness` uses those tables before the thread makes any type, so they
/// were dropped after the queue that frees types in a loop, and the type was freed by
/// recursion: `r6two` at `n` 4096 overflowed a 256 MiB stack so.
///
/// It freed a tuple 100,000 deep on a 1 MiB stack (1.8 s alone); now it frees one 20,000 deep
/// on a 256 KiB stack (TEST-bench-move-l0123, author P169: the smallest depth that still
/// overflows the stack in the code it guards against). Every level of a free by recursion is
/// at least one call, and a call keeps at least 16 bytes of stack on x86-64 (the return address
/// and the 16-byte alignment of the stack at a call), so 20,000 levels need at least 320,000
/// bytes, more than the 262,144 of the stack, whatever the size of the frames.
#[test]
fn a_deep_type_kept_by_the_verdicts_is_freed_when_its_thread_ends() {
    scaling::on_a_thread(1 << 18, || {
        Type::forget_emptiness();
        let t = (0..20_000).fold(Type::int(), |t, _| Type::tuple(vec![t, Type::int()]));
        assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
    });
}

mod bench;
