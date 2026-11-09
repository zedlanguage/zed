//! A function scrutinee bound by a name, `match f { h -> h(z) }`: the kernel, the counting
//! machine of step L1.34 and native code give the same value, and native code allocates and
//! writes counts as the machine does, with the scrutinee's release fused or not. A pattern
//! that matches a function binds it whole or not at all, since data holds no function, so the
//! binder is the scrutinee itself: one word or edge, whatever the function captured (O(1) per
//! match; `binders_of_a_function_scale` measures it).

use zed_kernel::Shared;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Prim, Term, Value, World};
use zedc::zir::lower::lower;
use zedc::zir::memory;

use super::kernel;
use super::scaling::check_run;

/// `match s { p -> body }`.
fn match1(s: Term, p: Pattern, body: Term) -> Term {
    Term::Match(Shared::new(s), vec![(p, body)])
}

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

/// `f = (y) -> y; g = (z) -> m; (g(0), g(1), …, g(n-1))`, with `m` the match under test.
fn calls(n: usize, m: Term) -> Term {
    let_(
        "f",
        lam(&["y"], var("y")),
        let_(
            "g",
            lam(&["z"], m),
            prim(
                Prim::Tuple,
                (0..n).map(|i| app(var("g"), vec![lit(i as i64)])).collect(),
            ),
        ),
    )
}

/// `(0, 1, …, n-1)`.
fn ints(n: i64) -> Value {
    Value::tuple((0..n).map(Value::Int).collect())
}

/// The value `t` gives in the kernel; asserts that the counting machine and native code give
/// it too, with the release fused and not, and that native code counts as the machine does.
fn agree(t: &Term) -> Result<Value, String> {
    let want = kernel(t);
    let g = zed_native::legalize(lower(t).unwrap_or_else(|e| panic!("{e}")));
    for fuse in [true, false] {
        let p = memory::plan(g.graph(), fuse);
        let machine = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()));
        let native = zed_native::run(&g, &p, &mut Evaluator::new(World::new()));
        match (&want, machine, native) {
            (Ok(v), Ok((m, s)), Ok(o)) => {
                assert_eq!((&m, &o.value), (v, v), "values, fuse {fuse}");
                assert_eq!(
                    (o.stats.increments, o.stats.decrements, o.stats.allocations),
                    (s.increments, s.decrements, s.allocations),
                    "counts, fuse {fuse}"
                );
                assert_eq!(
                    (o.stats.frees, o.stats.peak, o.stats.shared),
                    (s.frees, s.peak, s.shared),
                    "frees, peak and shared, fuse {fuse}"
                );
            }
            (Err(k), Err(m), Err(n)) => {
                assert!(m.ends_with(k.as_str()), "machine, fuse {fuse}: {m} for {k}");
                assert!(n.ends_with(k.as_str()), "native, fuse {fuse}: {n} for {k}");
            }
            (k, m, n) => panic!(
                "fuse {fuse}: kernel {k:?}, machine {:?}, native {:?}",
                m.map(|(v, _)| v),
                n.map(|o| o.value)
            ),
        }
    }
    want
}

/// `(0, 2, …, 2(n-1))`.
fn evens(n: i64) -> Value {
    Value::tuple((0..n).map(|z| Value::Int(2 * z)).collect())
}

/// The scrutinees the tests match, each with the values `(h(0), h(1), h(2))` of its function
/// `h`: `f`, which `g` captures; and `(y) -> y + z`, made in each call and used once, so the
/// match owns it when the arm gives it away.
fn scrutinees() -> [(Term, Value); 2] {
    let fresh = lam(&["y"], prim(Prim::Add, vec![var("y"), var("z")]));
    [(var("f"), ints(3)), (fresh, evens(3))]
}

/// `match s { h -> h(z) }`: the binder is called in the arm.
#[test]
fn a_function_bound_by_a_name_is_called() {
    for (s, want) in scrutinees() {
        let m = match1(s, bind("h"), app(var("h"), vec![var("z")]));
        assert_eq!(agree(&calls(3, m)), Ok(want));
    }
}

/// `match s { h -> z }`: a binder the arm does not use; an owned scrutinee is dropped.
#[test]
fn an_unused_binder_of_a_function_drops_it() {
    for (s, _) in scrutinees() {
        let m = match1(s, bind("h"), var("z"));
        assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
    }
}

/// `match f { h -> h(z) + f(z) }`: the arm reads the scrutinee beside its binder.
#[test]
fn a_function_read_by_its_binder_and_its_name_is_called() {
    let body = prim(
        Prim::Add,
        vec![app(var("h"), vec![var("z")]), app(var("f"), vec![var("z")])],
    );
    let m = match1(var("f"), bind("h"), body);
    assert_eq!(agree(&calls(3, m)), Ok(evens(3)));
}

/// `k = match s { h -> h }; k(z)`: the function leaves the match and is called after it.
#[test]
fn a_function_returned_from_the_match_is_called_later() {
    for (s, want) in scrutinees() {
        let m = let_(
            "k",
            match1(s, bind("h"), var("h")),
            app(var("k"), vec![var("z")]),
        );
        assert_eq!(agree(&calls(3, m)), Ok(want));
    }
}

/// `f = (y) -> y + c` captures `c`, a tuple in a cell; the binder holds the closure and so
/// its capture.
#[test]
fn a_function_with_a_capture_bound_by_a_name_is_called() {
    let c = prim(Prim::Tuple, vec![lit(10), lit(20)]);
    let f = lam(
        &["y"],
        match1(
            var("c"),
            Pattern::Tuple(vec![bind("a"), Pattern::Wild]),
            prim(Prim::Add, vec![var("y"), var("a")]),
        ),
    );
    let m = match1(var("f"), bind("h"), app(var("h"), vec![var("z")]));
    let t = let_(
        "c",
        c,
        let_(
            "f",
            f,
            let_(
                "g",
                lam(&["z"], m),
                prim(
                    Prim::Tuple,
                    (0..3).map(|i| app(var("g"), vec![lit(i)])).collect(),
                ),
            ),
        ),
    );
    let want = Value::tuple((10..13).map(Value::Int).collect());
    assert_eq!(agree(&t), Ok(want));
}

/// A primitive as the scrutinee: `match (-) { h -> h(z, 1) }`.
#[test]
fn a_primitive_bound_by_a_name_is_called() {
    let m = match1(
        Term::PrimFn(Prim::Sub),
        bind("h"),
        app(var("h"), vec![var("z"), lit(1)]),
    );
    assert_eq!(
        agree(&calls(3, m)),
        Ok(Value::tuple(
            vec![-1, 0, 1].into_iter().map(Value::Int).collect()
        ))
    );
}

/// `is` and `_` on a function still pick their arm and bind nothing; an earlier arm that
/// cannot match a function (a tuple pattern) is passed over.
#[test]
fn a_function_under_is_and_under_wild_binds_nothing() {
    for p in [Pattern::Is(Type::top()), Pattern::Wild] {
        let arms = vec![
            (Pattern::Tuple(vec![bind("a"), bind("b")]), var("a")),
            (p, var("z")),
        ];
        let m = Term::Match(Shared::new(var("f")), arms);
        assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
    }
}

/// `match (f, 1) { (h, n) -> h(n) }`: a tuple holds no function, so building the scrutinee
/// is the kernel's type error, and the machine and native code give the same error.
#[test]
fn a_function_inside_a_tuple_pattern_is_the_kernels_error() {
    let s = prim(Prim::Tuple, vec![var("f"), var("z")]);
    let m = match1(
        s,
        Pattern::Tuple(vec![bind("h"), bind("n")]),
        app(var("h"), vec![var("n")]),
    );
    let got = agree(&calls(3, m));
    assert_eq!(
        got,
        Err(zed_kernel::KernelError::Type("`(..)` applied to a function".into()).to_string())
    );
}

/// `n` matches of a function bound by a name and called: O(1) each, so the run is O(n).
#[test]
fn binders_of_a_function_scale() {
    check_run(
        "n matches of a function by a name",
        500,
        |n| {
            calls(
                n,
                match1(var("f"), bind("h"), app(var("h"), vec![var("z")])),
            )
        },
        |_| World::new(),
    );
}
