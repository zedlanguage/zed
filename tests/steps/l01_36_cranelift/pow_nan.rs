//! Float `^` gives NaN when either operand is NaN, the exponent 0 and the base 1 included,
//! unlike IEEE 754 `pow`, which gives `pow(NaN, 0) = 1` and `pow(1, NaN) = 1` (DESIGN.md
//! sec:domains, NaN rule 5; item FLOAT-pow-nan). The kernel, the counting machine and native
//! code at both of Cranelift's levels agree bit for bit, and native code runs float `^` with
//! no kernel call. Native code tests an operand for NaN before it calls `pow` only when the
//! graph does not rule the NaN out: a constant other than the NaN, or an edge whose type
//! excludes it, needs no test. Integer `^` and a failure operand are unchanged.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, run_at};
use zedc::zir::lower::lower;
use zedc::zir::memory;
use zedc::zir::{Edge, Op, Region};

use super::{float, kernel, planned};

const NAN: f64 = f64::NAN;

/// The bits of a float value.
fn bits(v: &Value) -> u64 {
    match v {
        Value::Float(x) => x.get().to_bits(),
        other => panic!("{other} is no float"),
    }
}

/// `f = params -> body; f(args)`: a let-bound function, which lowering keeps as a `lambda`
/// node and an `apply`, so its parameters are edges and not the constants passed.
fn called(params: &[&str], body: Term, args: Vec<Term>) -> Term {
    let_("f", lam(params, body), app(var("f"), args))
}

/// `a ^ b`.
fn pow(a: Term, b: Term) -> Term {
    prim(Prim::Pow, vec![a, b])
}

/// `a ^ b` on literals, and on the parameters of a function applied to them, so no constant
/// decides the result before the code runs.
fn both_forms(a: f64, b: f64) -> [Term; 2] {
    [
        pow(float(a), float(b)),
        called(
            &["a", "b"],
            pow(var("a"), var("b")),
            vec![float(a), float(b)],
        ),
    ]
}

/// The value of `t` by the kernel, by the counting machine and natively at both levels, all
/// the same; native code makes no kernel call when `native_inline`.
fn agreed(t: &Term, native_inline: bool) -> Value {
    let want = kernel(t).unwrap_or_else(|e| panic!("{t:?}: {e}"));
    let (g, p) = planned(t);
    let (m, _) = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()))
        .unwrap_or_else(|e| panic!("{t:?}: {e}"));
    assert_eq!(m, want, "{t:?} by the counting machine");
    for level in [OptLevel::None, OptLevel::Speed] {
        let o = run_at(level, &g, &p, &mut Evaluator::new(World::new()))
            .unwrap_or_else(|e| panic!("{t:?}: {e}"));
        assert_eq!(o.value, want, "{t:?} at {level:?}");
        if let (Value::Float(_), Value::Float(_)) = (&o.value, &want) {
            assert_eq!(bits(&o.value), bits(&want), "{t:?} at {level:?}");
        }
        if native_inline {
            assert_eq!(o.kernel_calls, 0, "{t:?} at {level:?}");
        }
    }
    want
}

/// The cases IEEE 754 `pow` answers with a number and Zed with NaN, and the plain NaN cases.
const NAN_CASES: [(f64, f64); 9] = [
    (NAN, 0.0),
    (NAN, -0.0),
    (1.0, NAN),
    (NAN, NAN),
    (0.0, NAN),
    (NAN, 1.0),
    (-1.0, NAN),
    (f64::INFINITY, NAN),
    (NAN, f64::NEG_INFINITY),
];

/// The kernel alone, where the counting machine and native code's runtime send float `^`.
#[test]
fn the_kernel_gives_nan_for_a_nan_operand() {
    for (a, b) in NAN_CASES {
        let v = kernel(&pow(float(a), float(b))).unwrap();
        assert_eq!(bits(&v), NAN.to_bits(), "{a} ^ {b}");
    }
}

/// The kernel, the counting machine and native code at both levels.
#[test]
fn a_nan_operand_gives_nan_for_every_exponent_and_base() {
    for (a, b) in NAN_CASES {
        for t in both_forms(a, b) {
            assert_eq!(bits(&agreed(&t, true)), NAN.to_bits(), "{a} ^ {b}");
        }
    }
}

/// With no NaN operand, `^` is IEEE 754 `pow`, the NaN it makes canonical.
#[test]
fn without_a_nan_operand_float_pow_is_ieee_pow() {
    let (inf, ninf) = (f64::INFINITY, f64::NEG_INFINITY);
    let cases = [
        (2.0, 10.0),
        (0.0, 0.0),
        (inf, 0.0),
        (1.0, inf),
        (-1.0, ninf),
        (0.0, -1.0),
        (-0.0, -1.0),
        (-8.0, 1.0 / 3.0),
        (-2.0, 3.0),
        (2.0, -0.5),
        (ninf, 0.5),
    ];
    for (a, b) in cases {
        let want = zed_kernel::F64::new(a.powf(b)).get().to_bits();
        for t in both_forms(a, b) {
            assert_eq!(bits(&agreed(&t, true)), want, "{a} ^ {b}");
        }
    }
}

/// Integer `^` keeps `0 ^ 0 = 1` and runs as before; a failure operand is the result whatever
/// the exponent, `0` included.
#[test]
fn integer_pow_and_failure_operands_are_unchanged() {
    for (a, b, want) in [(5i64, 0i64, 1i64), (0, 0, 1), (-3, 3, -27), (2, 10, 1024)] {
        let t = prim(Prim::Pow, vec![lit(a), lit(b)]);
        assert_eq!(agreed(&t, false), Value::from(want), "{a} ^ {b}");
        let t = called(&["a", "b"], pow(var("a"), var("b")), vec![lit(a), lit(b)]);
        assert_eq!(agreed(&t, false), Value::from(want), "{a} ^ {b}");
    }
    let fail = prim(Prim::IntDiv, vec![lit(10i64), lit(0i64)]);
    for e in [lit(0i64), lit(2i64)] {
        let t = prim(Prim::Pow, vec![fail.clone(), e]);
        assert_eq!(agreed(&t, false).to_string(), "#divByZero");
    }
}

/// The f64 type without the NaN.
fn no_nan() -> Type {
    let nan = Type::lit(&Value::float(NAN)).expect("the NaN is a literal");
    Type::meet_all([Type::f64(), !nan])
}

/// `f = (a, b) -> a ^ b; f(x, y)` lowered, with the parameters' edges typed `ty`.
fn typed_params(x: f64, y: f64, ty: [Option<Type>; 2]) -> Region {
    let t = called(
        &["a", "b"],
        pow(var("a"), var("b")),
        vec![float(x), float(y)],
    );
    let mut g = lower(&t).unwrap_or_else(|e| panic!("{e}"));
    let n = g
        .nodes
        .iter()
        .position(|n| n.op == Op::Lambda)
        .unwrap_or_else(|| panic!("no lambda node in {}", zedc::zir::text::print(&g)));
    let body = Arc::make_mut(&mut g.nodes[n].regions[0]);
    for (i, t) in ty.into_iter().enumerate() {
        if let Some(t) = t {
            body.args[i] = Edge::value(t);
        }
    }
    g
}

/// The number of NaN tests (`fcmp uno`) in the code generated for `g`.
fn nan_tests(g: Region) -> usize {
    let g = zed_native::legalize(g);
    let p = memory::plan(g.graph(), true);
    let ir = zed_native::ir(&g, &p).unwrap_or_else(|e| panic!("{e}"));
    assert!(ir.contains("function"), "{ir}");
    ir.lines().filter(|l| l.contains("fcmp uno")).count()
}

#[test]
fn the_nan_free_type_excludes_only_the_nan() {
    let t = no_nan();
    assert!(!t.contains(&Value::float(NAN)));
    for x in [0.0, -0.0, 1.0, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(t.contains(&Value::float(x)), "{x}");
    }
}

/// Operands proved NaN-free get no NaN test; one NaN-possible operand gets one test, and so
/// do two.
#[test]
fn the_nan_test_is_emitted_only_for_an_operand_that_may_be_nan() {
    let lits = |a, b| lower(&prim(Prim::Pow, vec![float(a), float(b)])).unwrap();
    assert_eq!(nan_tests(lits(2.0, 3.0)), 0, "two constants");
    assert_eq!(nan_tests(lits(NAN, 0.0)), 1, "a NaN constant");
    assert_eq!(
        nan_tests(typed_params(2.0, 3.0, [Some(no_nan()), Some(no_nan())])),
        0
    );
    assert_eq!(nan_tests(typed_params(2.0, 3.0, [None, Some(no_nan())])), 1);
    assert_eq!(nan_tests(typed_params(2.0, 3.0, [Some(no_nan()), None])), 1);
    assert_eq!(nan_tests(typed_params(2.0, 3.0, [None, None])), 1);
    // A parameter and a constant exponent.
    let t = called(&["a"], pow(var("a"), float(0.0)), vec![float(NAN)]);
    assert_eq!(nan_tests(lower(&t).unwrap()), 1);
    assert_eq!(bits(&agreed(&t, true)), NAN.to_bits());
}

/// The typed graphs still run to the kernel's value: the test elided where the edge type
/// rules the NaN out, and kept where it does not.
#[test]
fn typed_parameters_run_to_the_kernel_value() {
    for ty in [[Some(no_nan()), Some(no_nan())], [None, Some(no_nan())]] {
        let g = zed_native::legalize(typed_params(2.0, 0.5, ty));
        let p = memory::plan(g.graph(), true);
        for level in [OptLevel::None, OptLevel::Speed] {
            let o = run_at(level, &g, &p, &mut Evaluator::new(World::new())).unwrap();
            assert_eq!(bits(&o.value), 2f64.sqrt().to_bits());
            assert_eq!(o.kernel_calls, 0);
        }
    }
    let g = zed_native::legalize(typed_params(NAN, 0.0, [None, Some(no_nan())]));
    let p = memory::plan(g.graph(), true);
    let o = run_at(OptLevel::Speed, &g, &p, &mut Evaluator::new(World::new())).unwrap();
    assert_eq!(bits(&o.value), NAN.to_bits());
}
