//! The forward transfer of float `^` (item FLOAT-pow-nan; DESIGN.md sec:domains, NaN rule 5
//! and the float-class transfer): a NaN-possible operand gives a NaN-possible result for every
//! exponent and every base, `0` and `1` included, since NaN in, NaN out holds for `^` though
//! IEEE 754 `pow(NaN, 0)` and `pow(1, NaN)` are 1.

use zed_kernel::term::build::{prim, var};
use zed_kernel::types::Type;
use zed_kernel::{F64, Prim, Term, Value};
use zedc::store::product::{Product, Scope, forward};

const NAN: f64 = f64::NAN;

fn float(x: f64) -> Term {
    Term::Lit(Value::Float(F64::new(x)))
}

fn pow(a: Term, b: Term) -> Term {
    prim(Prim::Pow, vec![a, b])
}

/// Whether the float class of `t`'s element, with `x` any f64, admits the NaN.
fn may_be_nan(t: &Term) -> bool {
    let mut s = Scope::new([("x".into(), Product::of_type(Type::f64()))]);
    let p = forward(t, &mut s);
    !p.cell.float.element.excludes_nan()
}

#[test]
fn constant_operands_with_a_nan_give_the_nan_class() {
    for (a, b) in [(NAN, 0.0), (NAN, -0.0), (1.0, NAN), (NAN, NAN), (0.0, NAN)] {
        let t = pow(float(a), float(b));
        let p = forward(&t, &mut Scope::new([]));
        let c = &p.cell.float.element;
        assert!(c.contains(NAN), "{a} ^ {b}: {c}");
        assert!(!c.contains(1.0), "{a} ^ {b}: {c}");
    }
}

#[test]
fn a_nan_possible_operand_gives_a_nan_possible_result_for_every_exponent() {
    for e in [0.0, -0.0, 1.0, 2.0, NAN] {
        assert!(may_be_nan(&pow(var("x"), float(e))), "x ^ {e}");
    }
    for b in [1.0, 0.0, 2.0, NAN] {
        assert!(may_be_nan(&pow(float(b), var("x"))), "{b} ^ x");
    }
}

#[test]
fn without_a_nan_operand_the_class_is_ieee_pow_of_the_constants() {
    for (a, b) in [(2.0, 0.0), (1.0, 5.0), (0.0, 0.0)] {
        let p = forward(&pow(float(a), float(b)), &mut Scope::new([]));
        let c = &p.cell.float.element;
        assert!(c.excludes_nan(), "{a} ^ {b}: {c}");
        assert!(c.contains(a.powf(b)), "{a} ^ {b}: {c}");
    }
}
