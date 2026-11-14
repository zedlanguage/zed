//! Plan row TEST-kernel-hash-keys, through the evaluator: a definedness fix finds the entry a
//! read names by a hash lookup, and a read by a key equal to an entry's key in another form
//! finds that entry under every schedule. The lookup itself is checked against the ordered
//! one in the kernel's unit tests (`crates/zed-kernel/src/eval/tests.rs`).

use num_bigint::BigInt;
use zed_kernel::num::Rat;
use zed_kernel::term::build::{if_, lit, var};
use zed_kernel::text::Text;
use zed_kernel::{Evaluator, Family, Term, Value, World};
use zed_tests::kernel::*;

use super::{definedness, every_schedule};

/// `s` joined from its parts cut at `at`.
fn joined(s: &str, at: usize) -> Value {
    Value::Str(Text::join(&Text::from(&s[..at]), &Text::from(&s[at..])).expect("short"))
}

/// Keys in order, each with a value equal to it built another way: `-0.0` for `0.0`, NaN by
/// other bits, 3/4 and 10^19 each read from a decimal, a string joined from two parts, and
/// tuples, one nested, holding these.
fn keys_and_forms() -> Vec<(Value, Value)> {
    let decimal = |t: &str| Rat::decimal(t).expect("memory").expect("a decimal");
    let long = "z".repeat(75);
    let three_quarters = Rat::new(BigInt::from(3), BigInt::from(4)).expect("above 0");
    let ten_to_19 = Value::int_text(&format!("1{}", "0".repeat(19)), 10)
        .expect("memory")
        .expect("digits");
    let other_nan = || Value::float(f64::from_bits(0x7ff8_0000_0000_0042));
    let mut out = vec![
        (Value::float(0.0), Value::float(-0.0)),
        (Value::float(f64::NAN), other_nan()),
        (
            Value::rat(three_quarters.clone()),
            Value::rat(decimal("75e-2")),
        ),
        (ten_to_19, Value::integer(decimal("1e19"))),
        (Value::str(&long), joined(&long, 40)),
        (
            Value::tuple(vec![Value::Int(1), Value::float(0.0)]),
            Value::tuple(vec![Value::Int(1), Value::float(-0.0)]),
        ),
        (
            Value::tuple(vec![
                Value::tuple(vec![Value::float(0.0), s("ab")]),
                Value::rat(three_quarters),
                Value::float(f64::NAN),
            ]),
            Value::tuple(vec![
                Value::tuple(vec![Value::float(-0.0), joined("ab", 1)]),
                Value::rat(decimal("75e-2")),
                other_nan(),
            ]),
        ),
    ];
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

/// The fix over the keys in which entry 0 is 0 and entry `j` is entry `j - 1`, read by the
/// form `forms` holds at `j - 1`, plus 1.
fn chain(keys: &[Value], forms: &[Value]) -> Term {
    let steps = Family::of(keys.iter().cloned().zip(0_i64..));
    let forms = Family::of((0_i64..).zip(forms.iter().cloned()));
    let step = || get(lit(steps.clone()), var("i"));
    let before = get(lit(forms), sub(step(), lit(1)));
    definedness(
        lit(Family::set(keys.iter().cloned())),
        if_(
            eq(step(), lit(0)),
            lit(0),
            add(get(var("this"), before), lit(1)),
        ),
    )
}

/// Each entry reads the entry before it by the key's other form and finds it, under every
/// schedule: the family counts the keys in order.
#[test]
fn a_fix_finds_an_entry_by_every_form_of_its_key() {
    let (keys, forms): (Vec<Value>, Vec<Value>) = keys_and_forms().into_iter().unzip();
    let expected = Value::Family(Family::of(keys.iter().cloned().zip(0_i64..)));
    for schedule in every_schedule() {
        let out = Evaluator::new(World::new())
            .with_schedule(schedule)
            .run(&chain(&keys, &forms));
        assert_eq!(out.unwrap(), expected, "{schedule:?}");
    }
}

/// Negative control: the same fix with the first form replaced by a value close to its key
/// but not equal to it: the second entry reads `#notFound`, and the family is not the count.
#[test]
fn a_fix_read_by_a_close_value_is_not_found() {
    let (keys, mut forms): (Vec<Value>, Vec<Value>) = keys_and_forms().into_iter().unzip();
    forms[0] = match &keys[0] {
        Value::Float(_) => Value::float(-1e-300),
        k => panic!("the first key is a float, not {k}"),
    };
    for schedule in every_schedule() {
        let out = Evaluator::new(World::new())
            .with_schedule(schedule)
            .run(&chain(&keys, &forms))
            .unwrap();
        let Value::Family(f) = &out else {
            panic!("a family, not {out}")
        };
        assert_eq!(f.get(&keys[0]), Some(&Value::Int(0)), "{schedule:?}");
        assert_eq!(
            f.get(&keys[1]).map(Value::to_string).as_deref(),
            Some("#notFound"),
            "{schedule:?}"
        );
    }
}
