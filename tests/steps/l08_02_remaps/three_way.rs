//! The folds of functions declared in blocks, each call at its own identity (row
//! REDUCE-generic-identity-rest), and of functions used as values and folds read under two
//! identities at once (row REDUCE-generic-identity-values), checked three ways: the M0 model,
//! `zedc run`, and an
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

/// `zedc run`'s and the executable's output of `program` are each `want`.
fn runs_both_ways(name: &str, program: &str, want: &str) {
    let d = dir(&format!("l08_02_remaps/{name}"));
    let src = d.join(format!("{name}.zed"));
    std::fs::write(&src, program).unwrap();
    let ran = interpreter(&src, &[], &[]);
    assert_eq!((ran.stderr.as_str(), ran.status), ("", 0));
    assert_eq!(ran.stdout, want, "zedc run");
    let exe = d.join(name);
    built(&src, &exe);
    let ran = executable(&exe, &[], &[]);
    assert_eq!((ran.stderr.as_str(), ran.status), ("", 0));
    assert_eq!(ran.stdout, want, "the executable");
}

/// The forms of REDUCE-generic-identity-values, one line each: a lambda bound to a name in a
/// block (`c`), an alias at the top level (`d`), a function passed as an argument (`e`), a
/// block's function named as a value and passed as one (`g2`), a named lambda in a lambda
/// `.map` runs (`lm`), a fold read under the `.map` at `int` and the one at `f64` (`mm`), and
/// a generic function whose fold and whose `.map`'s fold take two identities (`n`).
const VALUES: &str = "top(positional xs) = xs >< max;\n\
    mf = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n\
    mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
    ap(positional f, positional x) = f(x);\n\
    t = top;\n\
    c = { f = x -> top(x); (f(mi[\"a\"]), f(mf[\"a\"])) };\n\
    d = (t(mi[\"a\"]), t(mf[\"a\"]));\n\
    e = (ap(top, mi[\"a\"]), ap(top, mf[\"a\"]));\n\
    g2 = { h(positional q) = top(q); p = h; (h(mi[\"a\"]), p(mf[\"a\"]), ap(h, mf[\"b\"])) };\n\
    lm = mi.map(r -> { f = x -> top(x); (top(r), f(mf[\"a\"])) });\n\
    mm = mi.map(q -> (top(q), mf.map(r -> (top(r), top(q)))));\n\
    gg(positional ys) = (top(ys), mf.map(r -> top(r)));\n\
    n = gg(mi[\"a\"]);\n\
    main(m: MainArgs) {\n    \
    m.stdout <- \"${c}\\n${d}\\n${e}\\n${g2}\\n${lm}\\n${mm}\\n${n}\";\n}\n";

/// The model of [`VALUES`]: each function value applied is the call it stands for, at the
/// identity of the carrier it is called at.
fn values_expected() -> String {
    let max = || func(|[a, b]| bin(Prim::Max, a, b));
    let top_int = |xs: Term| fold(xs, max(), None);
    let top_f64 = |xs: Term| fold(xs, max(), Some(lit(Value::float(f64::NEG_INFINITY))));
    // `f.map(g)` over the outer keys "a" and "b" of `f` (`map` is `reindex`, which runs on
    // the leaves).
    let by_key = |f: Term, g: &dyn Fn(Term) -> Term| {
        fam_with(lit(Value::Family(Family::set(["a", "b"]))), |k| {
            g(get(f, k))
        })
    };
    // `{"a" -> [1], "b" -> [5]}.map(r -> r.where(v -> v > 3))` at `three`'s carrier.
    let levels = |one: Value, five: Value, three: Value| {
        let row = |x| Value::Family(Family::of(vec![(Value::Int(0), x)]));
        let f = lit(Value::Family(Family::of(vec![
            (s("a"), row(one)),
            (s("b"), row(five)),
        ])));
        by_key(f, &|r| discard(r, func(|[_, v]| lt(lit(three.clone()), v))))
    };
    let mi = || levels(Value::Int(1), Value::Int(5), Value::Int(3));
    let mf = || levels(Value::float(1.0), Value::float(5.0), Value::float(3.0));
    let a = || lit(s("a"));
    let b = || lit(s("b"));
    let pair = |x: Term, y: Term| tuple(vec![x, y]);
    let both = || pair(top_int(get(mi(), a())), top_f64(get(mf(), a())));
    let g2 = tuple(vec![
        top_int(get(mi(), a())),
        top_f64(get(mf(), a())),
        top_f64(get(mf(), b())),
    ]);
    let lm = by_key(mi(), &|r| pair(top_int(r), top_f64(get(mf(), a()))));
    let mm = by_key(mi(), &|q| {
        let inner = by_key(mf(), &|r| pair(top_f64(r), top_int(q.clone())));
        pair(top_int(q), inner)
    });
    let n = pair(top_int(get(mi(), a())), by_key(mf(), &top_f64));
    let show = |t: &Term| match eval(t) {
        Ok(v) => v.to_string(),
        Err(e) => panic!("the model failed: {e:?}"),
    };
    let lines = [both(), both(), both(), g2, lm, mm, n];
    lines.iter().map(|t| show(t) + "\n").collect()
}

#[test]
fn function_values_and_reads_under_two_identities_agree_with_the_model_interpreted_and_built() {
    let want = values_expected();
    // The model's own values, as DESIGN gives them, so a wrong model fails here.
    assert_eq!(
        want,
        "(#empty, -inf)\n(#empty, -inf)\n(#empty, -inf)\n(#empty, -inf, 5.0)\n\
         {\"a\" -> (#empty, -inf), \"b\" -> (5, -inf)}\n\
         {\"a\" -> (#empty, {\"a\" -> (-inf, #empty), \"b\" -> (5.0, #empty)}), \
         \"b\" -> (5, {\"a\" -> (-inf, 5), \"b\" -> (5.0, 5)})}\n\
         (#empty, {\"a\" -> -inf, \"b\" -> 5.0})\n"
    );
    runs_both_ways("three_way_values", VALUES, &want);
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
