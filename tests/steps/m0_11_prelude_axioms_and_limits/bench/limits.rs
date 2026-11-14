//! The minimum limits at their size (author P178: an unusual size is a benchmark): a chain of
//! nested calls at the minimum, one past it and fifty times it, and a value of almost a
//! gibibyte. `limits::a_few_nested_calls_and_a_short_doubled_string_are_accepted` runs the
//! same programs at small sizes.

use zed_kernel::eval::{MIN_MEMORY, MIN_NESTED_CALLS};
use zed_kernel::{Value, eval};

use crate::limits::{doubled, nested};

#[test]
fn twenty_thousand_nested_calls_are_accepted() {
    let n = MIN_NESTED_CALLS as i64;
    assert_eq!(eval(&nested(n)), Ok(Value::Int(n)));
    assert_eq!(eval(&nested(n + 1)), Ok(Value::Int(n + 1)));
    assert_eq!(eval(&nested(50 * n)), Ok(Value::Int(50 * n)));
}

#[test]
fn a_value_of_almost_a_gibibyte_is_accepted() {
    // A string doubled 29 times reaches 512 MiB; with the halves the recursion still holds,
    // the strings alive at the end total 2^30 - 1 bytes.
    let out = eval(&doubled(29)).unwrap();
    let Value::Str(s) = out else {
        panic!("{out:?}")
    };
    assert_eq!(s.len() as u64, MIN_MEMORY / 2);
    assert_eq!((1..=29).map(|k| 1u64 << k).sum::<u64>() + 1, MIN_MEMORY - 1);
}
