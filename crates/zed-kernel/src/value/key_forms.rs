//! Families used as keys of the hash maps keyed by `Value` (plan row PERF-value-key-sites-bench:
//! eval.rs `key_index`, empty.rs `ValueKey`, and the maps of zedc-check and zed-native). Each
//! group holds a family and other values `==` to it built another way; the groups differ from
//! one another, and most have two entries, so that the hash that read only the number of entries
//! (before PERF-family-hash-count-only) put them all in one bucket. The corner cases: a range
//! against its map and against a list made by `++`, `-0.0` and `0.0` as an entry's value (two
//! groups: `==` tells them apart, and only a key made by `Value::as_key` makes them one), a
//! rational in two forms, a key past 64 bits in two forms, a string key flat and joined, a nested
//! family, the same values swapped between the keys, and two families one entry apart. A range
//! with no upper end, `a ..`, is left out: `==` on it stops (`walked_unbounded`), and the
//! checker rejects every program that compares one or holds one in a value (plan row RANGE-open).

use num_bigint::BigInt;

use crate::num::Rat;
use crate::text::Text;
use crate::value::{Family, Value};

/// 3/4 built from 3 and 4, and read as the decimal `75e-2` with its power of 10 kept.
fn three_quarters() -> (Value, Value) {
    let built = Rat::new(BigInt::from(3), BigInt::from(4)).expect("a denominator above 0");
    let decimal = Rat::decimal("75e-2").expect("memory").expect("a decimal");
    (Value::rat(built), Value::rat(decimal))
}

/// 10^19, beyond 64 bits, from its digits and from a decimal exponent.
fn ten_to_19() -> (Value, Value) {
    let digits = Value::int_text(&format!("1{}", "0".repeat(19)), 10)
        .expect("memory")
        .expect("digits");
    let r = Rat::decimal("1e19").expect("memory").expect("a decimal");
    (digits, Value::integer(r))
}

/// `s` joined from its parts cut at `at`, a string held as two pieces.
fn joined(s: &str, at: usize) -> Value {
    Value::Str(Text::join(&Text::from(&s[..at]), &Text::from(&s[at..])).expect("short"))
}

/// The family `{k -> v, 1 -> 1}` (`{0 -> v, 1 -> 1}` when `k` is 0).
fn with_one(k: Value, v: Value) -> Value {
    Value::Family(Family::of([(k, v), (Value::Int(1), Value::Int(1))]))
}

/// The groups of equal families; a value of one group is unequal to every value of another.
pub(crate) fn family_key_groups() -> Vec<Vec<Value>> {
    let (rat, rat_other) = three_quarters();
    let (big, big_other) = ten_to_19();
    let long = format!("{}k", "s".repeat(70));
    let inner = Family::of([(0_i64, 1_i64), (1, 2)]);
    let inner_joined = Family::of([(0_i64, 1_i64)])
        .concat(&Family::of([(0_i64, 2_i64)]))
        .expect("lists join");
    let first_half = Family::of((0..5_i64).map(|i| (i, i)));
    let second_half = Family::of((0..5_i64).map(|i| (i, i + 5)));
    let zero = || Value::Int(0);
    let fam = Value::Family;
    vec![
        // 0..9 as a range, a map and a list made by `++`.
        vec![
            fam(Family::range(0, 9)),
            fam(Family::of((0..10_i64).map(|i| (i, i)))),
            fam(first_half.concat(&second_half).expect("lists join")),
        ],
        // `-0.0` and `0.0` differ under `Value`'s `==` (identity); only a key made by
        // `Value::as_key` turns `-0.0` into `0.0`.
        vec![with_one(zero(), Value::float(0.0))],
        vec![with_one(zero(), Value::float(-0.0))],
        // The values of the group with `0.0`, swapped between the keys.
        vec![fam(Family::of([
            (zero(), Value::Int(1)),
            (Value::Int(1), Value::float(0.0)),
        ]))],
        vec![with_one(zero(), rat), with_one(zero(), rat_other)],
        vec![
            with_one(big, Value::Int(1)),
            with_one(big_other, Value::Int(1)),
        ],
        vec![
            with_one(Value::str(&long), Value::Int(1)),
            with_one(joined(&long, 1), Value::Int(1)),
            with_one(joined(&long, 40), Value::Int(1)),
        ],
        vec![
            with_one(zero(), fam(inner)),
            with_one(zero(), fam(inner_joined)),
        ],
        // One entry apart from the group of the nested family.
        vec![with_one(zero(), fam(Family::of([(0_i64, 1_i64), (1, 3)])))],
        vec![fam(Family::of([(0_i64, 0_i64), (1, 1)]))],
        vec![fam(Family::of([(0_i64, 0_i64), (1, 2)]))],
    ]
}

/// Every value of [`family_key_groups`] with its group's number.
pub(crate) fn family_keys() -> Vec<(Value, usize)> {
    let groups = family_key_groups().into_iter().enumerate();
    groups
        .flat_map(|(g, vs)| vs.into_iter().map(move |v| (v, g)))
        .collect()
}

/// `==` holds between the values of [`family_keys`] exactly within a group, so a map keyed by
/// them is right only if it keeps one entry per group and finds it by each of the group's values.
#[test]
fn the_family_keys_are_equal_exactly_within_a_group() {
    let keys = family_keys();
    for (a, ga) in &keys {
        for (b, gb) in &keys {
            assert_eq!(a == b, ga == gb, "{a} and {b}");
        }
    }
}

/// `n` families of three entries each, all distinct, of one size and with the same first and
/// last entries, the keys of the benchmarks of each site: family `i` is `{0 -> 0, 1 -> i,
/// 2 -> 0}`. A hash that read the size alone, or the size and the end entries (zed-native's
/// `ConstKey` before PERF-value-key-sites-bench), put all of them in one bucket.
pub(crate) fn families_of_one_size(n: usize) -> Vec<Value> {
    (0..n as i64)
        .map(|i| Value::Family(Family::of([(0_i64, 0_i64), (1, i), (2, 0)])))
        .collect()
}
