//! The two zeros (sec:type_resolution, "Equality and order corner rules"): `==` and the
//! orders read `0.0 == -0.0`, as IEEE 754 does, and key formation makes them one key. Where
//! a value's identity matters (a law's equation, a content address) they stay two values,
//! since `1.0 / x` separates them.

use crate::l01_16_elaboration::value;

const READINGS: &str = "\
calm = -0.0;
eq = calm == 0.0;
ne = calm != 0.0;
lt = calm < 0.0;
le = calm <= 0.0;
ge = 0.0 >= calm;
pair = (calm, 1) < (0.0, 0);
pairLe = (calm, 1) <= (0.0, 1);
recip = 1.0 / calm;
";

#[test]
fn the_zeros_compare_equal() {
    for (name, want) in [
        ("eq", "true"),
        ("ne", "false"),
        ("lt", "false"),
        ("le", "true"),
        ("ge", "true"),
        ("pair", "false"),
        ("pairLe", "true"),
    ] {
        assert_eq!(value(READINGS, name), want, "{name}");
    }
}

#[test]
fn the_zeros_stay_two_values() {
    assert_eq!(value(READINGS, "calm"), "-0.0");
    assert_eq!(value(READINGS, "recip"), "-inf");
}

#[test]
fn either_zero_finds_the_one_key() {
    // A lookup is copied into key form only when it holds a `-0.0`, at any depth.
    use zed_kernel::{Family, Value};
    let (pos, neg) = (Value::float(0.0), Value::float(-0.0));
    let pair = |z: &Value| Value::Tuple(vec![Value::Int(1), z.clone()]);
    let f = Family::of([(neg.clone(), Value::Int(1)), (pair(&pos), Value::Int(2))]);
    for z in [&pos, &neg] {
        assert_eq!(f.get(z), Some(&Value::Int(1)), "{z:?}");
        assert_eq!(f.get(&pair(z)), Some(&Value::Int(2)), "{z:?}");
    }
    assert_eq!(f.get(&Value::float(1.0)), None);
}
