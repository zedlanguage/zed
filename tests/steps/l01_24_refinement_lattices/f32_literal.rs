//! FAIL-lattice-f32-literal, found by TEST-complete-lattices (P188, P189): the cell of an `f32`
//! literal.

use zed_kernel::Value;
use zedc::store::cell::Cell;
use zedc::store::float::FloatClass;
use zedc::store::lattice::FiniteSet;

/// An `f32` literal's float class is the singleton class of its value, as an `f64` literal's
/// is (DESIGN.md sec:domains, literal domains: a literal's inferred domain is the singleton
/// containing it; step L1.24: float classes at each of the formats). Before the fix the cell
/// of an `f32` literal left the float class at the top.
#[test]
fn an_f32_literal_fills_the_float_class() {
    for x in [0.5f32, f32::INFINITY, f32::MAX] {
        let c = Cell::literal(&Value::float32(x));
        assert_eq!(c.float.element, FloatClass::of(f64::from(x)), "{x}");
        assert_eq!(c.finite.element, FiniteSet::of([Value::float32(x)]), "{x}");
    }
}

/// The other kinds and edges of `f32`: each sign of infinity and zero, NaN, the smallest
/// subnormal and the smallest normal. Each class is the one its value has as an `f64`, since
/// every `f32` converts to `f64` exactly.
#[test]
fn every_kind_of_f32_literal_fills_the_float_class() {
    for x in [
        f32::NEG_INFINITY,
        f32::NAN,
        0.0f32,
        -0.0f32,
        f32::from_bits(1),
        f32::MIN_POSITIVE,
        f32::MIN,
        0.1f32,
    ] {
        let c = Cell::literal(&Value::float32(x));
        assert_eq!(c.float.element, FloatClass::of(f64::from(x)), "{x}");
        assert_ne!(c.float.element, Cell::top().float.element, "{x}");
    }
}

/// Control: an `f64` literal's class, which was right before the fix.
#[test]
fn an_f64_literal_fills_the_float_class() {
    for x in [0.5f64, f64::INFINITY, f64::MAX, 0.1] {
        let c = Cell::literal(&Value::float(x));
        assert_eq!(c.float.element, FloatClass::of(x), "{x}");
    }
}
