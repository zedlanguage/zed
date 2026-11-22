//! Float `^` gives NaN when either operand is NaN, the exponent 0 and the base 1 included,
//! unlike IEEE 754 `pow` (IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 9.2;
//! the full comment is in zed-kernel `eval.rs`, fn `prim_on`, at `Prim::Pow`), which gives
//! `pow(NaN, 0) = 1` and `pow(1, NaN) = 1` (DESIGN.md
//! sec:domains, NaN rule 5; item FLOAT-pow-nan). The kernel, the counting machine and native
//! code at both of Cranelift's levels agree bit for bit, and native code runs float `^` with
//! no kernel call. Native code tests an operand for NaN before it calls `pow` only when the
//! graph does not rule out `pow(NaN, 0)` or `pow(1, NaN)`: an operand that cannot be the NaN
//! (a constant other than the NaN, an operation on such operands that cannot make one, an edge
//! whose type excludes it) needs no test, nor does a base when the exponent cannot be 0, nor an
//! exponent when the base cannot be 1 (FLOAT-class-zir). Integer `^` and a failure operand are
//! unchanged.

use std::cell::Cell;
use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, run_at};
use zedc::testing::{test, test_through};
use zedc::zir::lower::lower;
use zedc::zir::memory;
use zedc::zir::{Edge, Op, Region};
use zedc_lattice::float_kinds::Kinds;

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

/// `f = a -> body; f(x)`, lowered, and its NaN tests counted, after checking that it runs to
/// the kernel's value for each argument in `xs`. Kernel calls are allowed, since a cast takes
/// one.
fn one_param(body: Term, xs: &[f64]) -> usize {
    for &x in xs {
        let t = called(&["a"], body.clone(), vec![float(x)]);
        agreed(&t, false);
    }
    let t = called(&["a"], body, vec![float(2.0)]);
    nan_tests(lower(&t).unwrap_or_else(|e| panic!("{e}")))
}

/// With no edge typed, the graph's own constants and operations rule the NaN tests out
/// (FLOAT-class-zir). Float `^` needs one only where IEEE 754 `pow` gives a number for a NaN
/// operand, `NaN ^ 0` and `1 ^ NaN`, so an exponent that cannot be 0 or a base that cannot be 1
/// needs no test of the other operand, and an operand that cannot be the NaN needs none of
/// itself. Each other float operation (`+`, `-`, `*`, `/`, `min`, `max`, negation) makes a
/// NaN result canonical with one test of its own, left out when its result cannot be the NaN.
/// So each count below is the operation's test (0 or 1) plus `^`'s (0 or 1). On origin/main
/// before this row, every case with a parameter or an operation gave at least 1.
#[test]
fn constants_and_operations_rule_the_nan_test_out() {
    let xs = [NAN, 0.0, 1.0, -2.0, f64::INFINITY];
    let neg = |t| prim(Prim::Neg, vec![t]);
    // A constant exponent other than 0, of either sign, or one made by an operation that
    // cannot give the NaN.
    assert_eq!(one_param(pow(var("a"), float(2.0)), &xs), 0, "a ^ 2.0");
    assert_eq!(one_param(pow(var("a"), float(-0.5)), &xs), 0, "a ^ -0.5");
    assert_eq!(
        one_param(pow(var("a"), neg(float(0.5))), &xs),
        0,
        "a ^ -(0.5)"
    );
    let max = prim(Prim::Max, vec![float(0.5), float(3.0)]);
    assert_eq!(one_param(pow(var("a"), max), &xs), 0, "a ^ max(0.5, 3.0)");
    // A constant base other than 1; a cast of an integer is never the NaN, but may be 1.
    assert_eq!(one_param(pow(float(2.0), var("a")), &xs), 0, "2.0 ^ a");
    let cast = prim(Prim::CastF64, vec![lit(3i64)]);
    assert_eq!(one_param(pow(cast, float(0.0)), &xs), 0, "f64(3) ^ 0.0");
    let cast = prim(Prim::CastF64, vec![lit(3i64)]);
    assert_eq!(one_param(pow(cast, var("a")), &xs), 1, "f64(3) ^ a");
    // Where the NaN may meet the exponent 0 or the base 1, the test stays.
    assert_eq!(one_param(pow(var("a"), float(0.0)), &xs), 1, "a ^ 0.0");
    assert_eq!(one_param(pow(float(1.0), var("a")), &xs), 1, "1.0 ^ a");
    // `a + 0.5` may be the NaN: the sum's own test, and none at `^` with the base 3.0.
    let sum = prim(Prim::Add, vec![var("a"), float(0.5)]);
    assert_eq!(one_param(pow(float(3.0), sum), &xs), 1, "3.0 ^ (a + 0.5)");
    // The sum's test, and one test of both operands at `^`.
    let sum = prim(Prim::Add, vec![var("a"), float(0.5)]);
    assert_eq!(one_param(pow(var("a"), sum), &xs), 2, "a ^ (a + 0.5)");
    // An infinity times zero is the NaN (IEEE 754 section 7.2 (b)), so `a * 0.0` may be both
    // the NaN and 0: the product's test and `^`'s.
    let prod = prim(Prim::Mul, vec![var("a"), float(0.0)]);
    assert_eq!(one_param(pow(float(1.0), prod), &xs), 2, "1.0 ^ (a * 0.0)");
    // `inf - inf` is the NaN (section 7.2 (d)): the difference's test and `^`'s.
    let diff = prim(Prim::Sub, vec![float(f64::INFINITY), float(f64::INFINITY)]);
    assert_eq!(one_param(pow(diff, var("a")), &xs), 2, "(inf - inf) ^ a");
    // A sum of two finite constants other than 0 may overflow (section 7.4) but is never the
    // NaN, so the sum has no test. The kinds do not tell `MAX + MAX` from `x + -x`, which is
    // 0, so `^` keeps its one test of the base.
    let sum = prim(Prim::Add, vec![float(f64::MAX), float(f64::MAX)]);
    assert_eq!(one_param(pow(var("a"), sum), &xs), 1, "a ^ (MAX + MAX)");
}

/// The same on real programs: a unit's checks run natively, each row's code holding the NaN
/// tests counted, and each row passing as the kernel runs it.
#[test]
fn real_programs_test_only_where_the_nan_may_meet_zero_or_one() {
    let unit =
        |body: &str, rows: &str| format!("f(positional x: f64) = {body}\ntest {{ {rows} }}\n");
    for (body, rows, want) in [
        ("x ^ 3.0f64", "2.0f64 -> 8.0f64, 0.5f64 -> 0.125f64", 0),
        ("x ^ 0.5f64", "4.0f64 -> 2.0f64", 0),
        ("2.0f64 ^ x", "3.0f64 -> 8.0f64", 0),
        ("x ^ 0.0f64", "4.0f64 -> 1.0f64", 1),
        // The sum's own test, since `x + 1.0` may be the NaN, and `^`'s.
        ("x ^ (x + 1.0f64)", "1.0f64 -> 1.0f64", 2),
    ] {
        let text = unit(body, rows);
        let tests = Cell::new(Vec::new());
        let through = |t: &Term, ev: &mut Evaluator| {
            let g = zed_native::legalize(lower(t)?);
            let p = memory::plan(g.graph(), true);
            let ir = zed_native::ir(&g, &p)?;
            let mut v = tests.take();
            v.push(ir.lines().filter(|l| l.contains("fcmp uno")).count());
            tests.set(v);
            Ok(zed_native::run(&g, &p, ev)?.value)
        };
        let got = test_through(&text, &through);
        assert_eq!(got, test(&text), "{body}");
        assert!(
            got.iter()
                .all(|o| o.failure.is_none() && o.not_run.is_none()),
            "{body}: {got:?}"
        );
        let tests = tests.take();
        assert!(!tests.is_empty(), "{body}: no row ran natively");
        assert!(
            tests.iter().all(|&n| n == want),
            "{body}: {tests:?}, want {want} each"
        );
    }
}

/// Floats of every kind, with the edges of each: both zeros, `±1`, the largest and smallest
/// magnitudes, values that overflow when added or multiplied, and non-integers for `^`.
const SAMPLES: [f64; 16] = [
    NAN,
    f64::INFINITY,
    f64::NEG_INFINITY,
    0.0,
    -0.0,
    1.0,
    -1.0,
    2.0,
    -2.0,
    0.5,
    -0.5,
    3.0,
    f64::MAX,
    -f64::MAX,
    f64::MIN_POSITIVE,
    5e-324,
];

/// The kinds `Kinds::transfer` gives hold every result the kernel gives (FLOAT-class-zir): for
/// each primitive the rules cover and every pair of sample operands, the result's kind is in
/// the set the operands' kinds give. Then the rules are monotone: a set of kinds gives at
/// least what each of its members gives, so the singleton check covers every set. This is what
/// makes leaving out a NaN test safe; a rule that left out a kind the kernel can give fails
/// here. It cannot catch a wrong kind at an operand pair no sample reaches.
#[test]
fn float_kinds_hold_every_result_the_kernel_gives() {
    let binary = [
        Prim::Add,
        Prim::Sub,
        Prim::Mul,
        Prim::Div,
        Prim::Min,
        Prim::Max,
        Prim::Pow,
    ];
    let holds = |p: Prim, ins: &[Kinds], v: &Value| {
        let (k, got) = (Kinds::of(v), Kinds::transfer(p, ins));
        assert_eq!(got.and(k), k, "{p:?} of {ins:?} gave {v:?}, not in {got:?}");
    };
    for &x in &SAMPLES {
        for p in [Prim::Neg, Prim::Abs, Prim::CastF64] {
            if let Ok(v) = kernel(&prim(p, vec![float(x)])) {
                holds(p, &[Kinds::of(&Value::float(x))], &v);
            }
        }
        for &y in &SAMPLES {
            for p in binary {
                let v = kernel(&prim(p, vec![float(x), float(y)]))
                    .unwrap_or_else(|e| panic!("{p:?} {x} {y}: {e}"));
                holds(
                    p,
                    &[Kinds::of(&Value::float(x)), Kinds::of(&Value::float(y))],
                    &v,
                );
            }
        }
    }
    // A cast of an integer and `f64 ^ int`: an integer operand has no float kind.
    for i in [0i64, 1, -1, 3, i64::MAX, i64::MIN] {
        let v = kernel(&prim(Prim::CastF64, vec![lit(i)])).unwrap_or_else(|e| panic!("{e}"));
        holds(Prim::CastF64, &[Kinds::NONE], &v);
        for &x in &SAMPLES {
            if let Ok(v) = kernel(&prim(Prim::Pow, vec![float(x), lit(i)])) {
                holds(Prim::Pow, &[Kinds::of(&Value::float(x)), Kinds::NONE], &v);
            }
        }
    }
    // Monotone: every set of kinds for each operand, against each member of it.
    let sets: Vec<Kinds> = (0..64u8)
        .map(|m| {
            (0..6)
                .filter(|i| m >> i & 1 == 1)
                .fold(Kinds::NONE, |k, i| k.or(Kinds::EACH[i]))
        })
        .collect();
    for p in binary {
        for &a in &sets {
            for &b in &sets {
                let whole = Kinds::transfer(p, &[a, b]);
                for &x in Kinds::EACH.iter().filter(|x| a.meets(**x)) {
                    for &y in Kinds::EACH.iter().filter(|y| b.meets(**y)) {
                        let one = Kinds::transfer(p, &[x, y]);
                        assert_eq!(whole.and(one), one, "{p:?}: {x:?} {y:?} in {a:?} {b:?}");
                    }
                }
            }
        }
    }
}

/// The kinds pass through a chain of operations: 200 products of the constant 2.0 by 1.0,
/// then `^ 0.5`, have no NaN test at any depth, and run to the kernel's value (the chain at
/// 2,000 and 16,000 is timed in `bench/scaling.rs`, `a_chain_of_float_operations_scales`).
#[test]
fn kinds_pass_through_a_chain_of_operations() {
    let t = super::scaling::float_chain(200);
    assert_eq!(bits(&agreed(&t, true)), 2f64.sqrt().to_bits());
    assert_eq!(nan_tests(lower(&t).unwrap_or_else(|e| panic!("{e}"))), 0);
}
