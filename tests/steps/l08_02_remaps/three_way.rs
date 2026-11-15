//! The folds of functions declared in blocks, each call at its own identity (row
//! REDUCE-generic-identity-rest), checked three ways: the M0 model, `zedc run`, and an
//! executable `zedc build` makes. The model is the kernel term DESIGN.md defines each call by:
//! `xs >< max` is `fold(xs, max)` with the identity of the carrier the call fixes,
//! sec:reduction, "Identity as data": none at `int`, so an empty level folds to `#empty`, and
//! `-inf` at `f64`; `r.where(p)` is `discard(r, p)`.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Family, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};

/// `top` folds by `max`; `mf` and `mi` hold an empty level at "a" and `5` at "b", at `f64`
/// and at `int`. `a` calls a block's `h` at both carriers, directly and through `k`; `b`
/// calls `g`, whose block's `h` is called on `g`'s parameter and on an `f64` level; `main`'s
/// own `h` is called at both carriers.
const PROGRAM: &str = "top(positional xs) = xs >< max;\n\
    mf = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n\
    mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
    g(positional ys) = { h(positional q) = top(q); (h(ys), h(mf[\"a\"])) };\n\
    a = { h(positional q) = top(q); k(positional z) = h(z); \
    (h(mi[\"a\"]), h(mf[\"a\"]), k(mi[\"b\"]), k(mf[\"b\"])) };\n\
    b = (g(mi[\"a\"]), g(mi[\"b\"]));\n\
    main(m: MainArgs) {\n    h(positional q) = top(q);\n    \
    m.stdout <- \"${a}\\n${b}\\n${(h(mi[\"a\"]), h(mf[\"a\"]))}\";\n}\n";

/// The level `[x]` keeps under `where(v -> v > 3)`, at `int` or at `f64`.
fn level(x: Value, three: Value) -> Term {
    let one = lit(Value::Family(Family::of(vec![(Value::Int(0), x)])));
    discard(one, func(|[_, v]| lt(lit(three), v)))
}

/// `top` of the `int` level of `[x]`: no identity.
fn at_int(x: i64) -> Term {
    let max = func(|[a, b]| bin(Prim::Max, a, b));
    fold(level(Value::Int(x), Value::Int(3)), max, None)
}

/// `top` of the `f64` level of `[x]`: identity `-inf`.
fn at_f64(x: f64) -> Term {
    let max = func(|[a, b]| bin(Prim::Max, a, b));
    let three = Value::float(3.0);
    let inf = lit(Value::float(f64::NEG_INFINITY));
    fold(level(Value::float(x), three), max, Some(inf))
}

fn tuple(parts: Vec<Term>) -> Term {
    prim(Prim::Tuple, parts)
}

/// The output the model gives: `a`, `b`, then `main`'s two calls.
fn expected() -> String {
    let a = tuple(vec![at_int(1), at_f64(1.0), at_int(5), at_f64(5.0)]);
    let g = |x| tuple(vec![at_int(x), at_f64(1.0)]);
    let b = tuple(vec![g(1), g(5)]);
    let show = |t: &Term| match eval(t) {
        Ok(v) => v.to_string(),
        Err(e) => panic!("the model failed: {e:?}"),
    };
    format!("{}\n{}\n{}\n", show(&a), show(&b), show(&g(1)))
}

#[test]
fn block_functions_at_two_carriers_agree_with_the_model_interpreted_and_built() {
    let want = expected();
    // The model's own values, as DESIGN gives them, so a wrong model fails here.
    assert_eq!(
        want,
        "(#empty, -inf, 5, 5.0)\n((#empty, -inf), (5, -inf))\n(#empty, -inf)\n"
    );
    let d = dir("l08_02_remaps/three_way");
    let src = d.join("three_way.zed");
    std::fs::write(&src, PROGRAM).unwrap();
    let ran = interpreter(&src, &[], &[]);
    assert_eq!((ran.stderr.as_str(), ran.status), ("", 0));
    assert_eq!(ran.stdout, want, "zedc run");
    let exe = d.join("three_way");
    built(&src, &exe);
    let ran = executable(&exe, &[], &[]);
    assert_eq!((ran.stderr.as_str(), ran.status), ("", 0));
    assert_eq!(ran.stdout, want, "the executable");
}
