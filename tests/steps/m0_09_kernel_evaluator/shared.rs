//! Shared values (COMPLEXITY.md K21). A tuple, a keypath and an atom's payload hold their parts
//! behind one reference count, so reading a variable, a literal or a part of a tuple is O(1)
//! whatever the tuple's size, and a value is a DAG: a part can sit in many places at once.
//! Equality, order, keys and the language's `==` must treat a shared part as they treat a copy.
//! The benchmarks of these values are in `bench/shared.rs`; their inputs are built here, and
//! what each asserts besides its ratio is checked here at small sizes (TEST-bench-move-rest).

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Term, Value, World};
use zed_tests::kernel::*;

pub(super) fn run(t: &Term) -> Value {
    Evaluator::new(World::new()).run(t).unwrap()
}

/// The tuple `(0, 1, ..., n - 1)`.
pub(super) fn tuple(n: usize) -> Value {
    Value::tuple((0..n as i64).map(Value::Int).collect())
}

/// The keys `0..n`, each mapped to itself: the sequence a `foldl` runs over.
fn keys(n: usize) -> Value {
    Value::Family(Family::set(0..n as i64))
}

/// `(t -> fam(0..n, k -> t.0))((0, ..., n - 1))`: a function that reads its tuple argument
/// once per element, as a loop over a record's fields reads the record.
pub(super) fn reads(n: usize) -> Term {
    let body = fam_with(lit(keys(n)), |_| nth(var("t"), 0));
    app(lam(&["t"], body), vec![lit(tuple(n))])
}

/// `xs.foldl((), (acc, x) -> (x, acc))` over `0..n`: the list `(n - 1, (..., (0, ())))` built
/// by an accumulator, the form COMPLEXITY.md K21 measured.
pub(super) fn cons_list(n: usize) -> Term {
    let op = lam(&["acc", "x"], prim(Prim::Tuple, vec![var("x"), var("acc")]));
    foldl(lit(keys(n)), lit(Value::tuple(vec![])), op)
}

/// The list `cons_list(n)` computes.
fn expected_list(n: usize) -> Value {
    (0..n as i64).fold(Value::tuple(vec![]), |acc, x| {
        Value::tuple(vec![Value::Int(x), acc])
    })
}

#[test]
fn a_record_read_once_per_field_gives_each_field() {
    let got = run(&reads(5));
    let want = Value::Family(Family::of((0..5).map(|k| (k, Value::Int(0)))));
    assert_eq!(got, want);
}

#[test]
fn an_accumulated_list_holds_every_element_in_order() {
    // On the default stack: the evaluator nests one call per element, so the lists of
    // thousands of elements are in `bench/shared.rs`, on a 256 MiB stack.
    for n in [0, 1, 2, 9] {
        assert_eq!(run(&cons_list(n)), expected_list(n), "n = {n}");
    }
}

#[test]
fn a_tuple_bound_to_two_names_is_one_value() {
    // `let a = (1, "x"); let b = a; (a, b)`
    let t = Value::tuple(vec![Value::Int(1), Value::str("x")]);
    let both = let_(
        "a",
        lit(t.clone()),
        let_("b", var("a"), prim(Prim::Tuple, vec![var("a"), var("b")])),
    );
    assert_eq!(run(&both), Value::tuple(vec![t.clone(), t]));
}

#[test]
fn taking_a_shared_tuple_apart_leaves_the_other_holder_whole() {
    let a = Value::tuple(vec![Value::Int(1), Value::str("two"), tuple(3)]);
    let b = a.clone();
    let Value::Tuple(parts) = b else {
        unreachable!("a tuple")
    };
    let mut parts = parts.into_vec();
    parts.push(Value::Int(4));
    assert_eq!(parts.len(), 4);
    assert_eq!(a, Value::tuple(parts[..3].to_vec()));
    // Held once, the parts are moved out.
    let Value::Tuple(only) = tuple(3) else {
        unreachable!("a tuple")
    };
    assert_eq!(
        only.into_vec(),
        vec![Value::Int(0), Value::Int(1), Value::Int(2)]
    );
}

#[test]
fn a_shared_tuple_holding_nan_is_not_equal_to_itself_under_the_languages_equality() {
    // `let t = (0.0 / 0.0, 1); t == t` is false, and `t < t` is unordered, though `t` is one
    // shared value; as a key it is the same key as itself.
    let t = Value::tuple(vec![Value::float(f64::NAN), Value::Int(1)]);
    let same = t.clone();
    assert!(!t.surface_eq(&same));
    assert_eq!(t.surface_cmp(&same), None);
    assert_eq!(t, same);
    assert_eq!(t.cmp(&same), std::cmp::Ordering::Equal);
    let program = let_("t", lit(t), eq(var("t"), var("t")));
    assert_eq!(run(&program), Value::Bool(false));
}

#[test]
fn a_part_shared_in_two_places_compares_as_two_copies_do() {
    // `p = (1, -0.0)`; `(p, p)` against `((1, -0.0), (1, -0.0))` built apart.
    let p = Value::tuple(vec![Value::Int(1), Value::float(-0.0)]);
    let shared = Value::tuple(vec![p.clone(), p]);
    let apart = || Value::tuple(vec![Value::Int(1), Value::float(-0.0)]);
    let copies = Value::tuple(vec![apart(), apart()]);
    assert_eq!(shared, copies);
    assert!(shared.surface_eq(&copies));
    let other = Value::tuple(vec![
        apart(),
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
    ]);
    assert_ne!(shared, other);
    assert!(shared < other);
    // Its key makes both zeros positive, in both places.
    let zero = Value::tuple(vec![Value::Int(1), Value::float(0.0)]);
    assert!(!shared.is_key());
    assert_eq!(shared.key(), Value::tuple(vec![zero.clone(), zero]));
}

#[test]
fn a_struct_atom_copied_keeps_its_fields() {
    let a = Value::atom_named(
        "err",
        vec![
            ("code".into(), Value::Int(3)),
            ("at".into(), Value::str("f")),
        ],
    )
    .unwrap();
    let b = a.clone();
    assert_eq!(a, b);
    assert_eq!(b.to_string(), r#"#err(at: "f", code: 3)"#);
}

/// `v(0) = bottom`, `v(i + 1) = (v(i), v(i))`: `depth` nodes and `2^depth` paths.
pub(super) fn doubled(depth: usize, bottom: Value) -> Value {
    (0..depth).fold(bottom, |v, _| Value::tuple(vec![v.clone(), v]))
}

/// Two equal values and a value of zeros, each `doubled` to `depth`, the zeros `-0.0`.
pub(super) fn shared_parts(depth: usize) -> [Value; 3] {
    let one = doubled(depth, Value::Int(1));
    let same = doubled(depth, Value::Int(1));
    let zero = doubled(depth, Value::float(-0.0));
    [one, same, zero]
}

/// The two equal values of [`shared_parts`] are equal under each relation, and the value of
/// `-0.0`s is no key, while its key is.
pub(super) fn shared_parts_compare([one, same, zero]: &[Value; 3]) {
    assert!(one == same);
    assert_eq!(one.cmp(same), std::cmp::Ordering::Equal);
    assert!(one.surface_eq(same));
    assert!(!zero.is_key());
    assert!(zero.key().is_key());
}

/// `{({(...,)},)}`, `d` sets each holding a one-tuple of the set beneath, with `0` at the bottom.
pub(super) fn nested_sets(d: usize) -> Value {
    (0..d).fold(Value::Int(0), |v, _| {
        Value::Family(Family::set([Value::tuple(vec![v])]))
    })
}

/// The text of [`nested_sets`]`(d)` holds each of its levels.
pub(super) fn shows_nested_sets(v: &Value, d: usize) {
    assert!(v.to_string().len() > 4 * d);
}

/// `f(0) = bottom`, `f(i + 1) = {x: f(i), y: f(i)}`: a family `depth` levels deep whose levels
/// each hold the one beneath twice, `depth` families and `2^depth` keypaths.
pub(super) fn doubled_family(depth: usize, bottom: Value) -> Value {
    (0..depth).fold(bottom, |v, _| {
        Value::Family(Family::of([("x", v.clone()), ("y", v)]))
    })
}

#[test]
fn families_built_apart_that_share_their_levels_compare_by_their_leaves() {
    let one = doubled_family(12, Value::Int(1));
    let same = doubled_family(12, Value::Int(1));
    assert!(one == same);
    assert_eq!(one.cmp(&same), std::cmp::Ordering::Equal);
    assert!(one.surface_eq(&same));
    assert_eq!(one.surface_cmp(&same), Some(std::cmp::Ordering::Equal));
    // Unequal at the deepest leaf, which every keypath reaches.
    let two = doubled_family(12, Value::Int(2));
    assert!(one != two);
    assert_eq!(one.cmp(&two), std::cmp::Ordering::Less);
    assert!(!one.surface_eq(&two));
    assert_eq!(two.surface_cmp(&one), Some(std::cmp::Ordering::Greater));
    // `-0.0` and `0.0` are two values, and equal under the language's `==`, at every leaf.
    let neg = doubled_family(12, Value::float(-0.0));
    let pos = doubled_family(12, Value::float(0.0));
    assert!(neg != pos);
    assert_eq!(neg.cmp(&pos), std::cmp::Ordering::Less);
    assert!(neg.surface_eq(&pos));
    // A NaN at the bottom is not equal to itself under `==`, though both are one key.
    let nan = doubled_family(12, Value::float(f64::NAN));
    let nan_again = doubled_family(12, Value::float(f64::NAN));
    assert!(nan == nan_again);
    assert!(!nan.surface_eq(&nan_again));
}

#[test]
fn two_empty_families_are_equal_under_every_relation() {
    let a = Value::Family(Family::new());
    let b = Value::Family(Family::of(Vec::<(i64, i64)>::new()));
    assert!(a == b);
    assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal);
    assert!(a.surface_eq(&b));
    assert_eq!(a.surface_cmp(&b), Some(std::cmp::Ordering::Equal));
    let one = doubled_family(1, Value::Int(1));
    assert!(a != one);
    assert!(a < one);
}

#[test]
fn a_part_compared_inside_two_families_is_read_once_per_comparison() {
    // `{0: t, 1: t, ..., n - 1: t}` for one tuple `t` of n numbers, and `(f, f, ..., f)` for
    // one family `f` of n entries, each built twice apart: n places, one part of size n.
    let wide = |n: usize| {
        let t = tuple(n);
        Value::Family(Family::of((0..n as i64).map(|k| (k, t.clone()))))
    };
    let row = |n: usize| {
        let f = Value::Family(Family::set(0..n as i64));
        Value::tuple(vec![f; n])
    };
    assert!(wide(5) == wide(5));
    assert!(row(5).surface_eq(&row(5)));
    assert_eq!(row(5).surface_cmp(&row(5)), Some(std::cmp::Ordering::Equal));
    // Unequal only in the last entry, whose tuple is one longer.
    let last = Family::of((0..5).map(|k| (k, if k == 4 { tuple(6) } else { tuple(5) })));
    assert!(wide(5) != Value::Family(last));
}

/// Two equal families and the families of `-0.0` and of `0.0`, each `doubled_family` to `depth`.
pub(super) fn families(depth: usize) -> [Value; 4] {
    let one = doubled_family(depth, Value::Int(1));
    let same = doubled_family(depth, Value::Int(1));
    let neg = doubled_family(depth, Value::float(-0.0));
    let pos = doubled_family(depth, Value::float(0.0));
    [one, same, neg, pos]
}

/// The equal families of [`families`] are equal under each relation; those of `-0.0` and `0.0`
/// differ as values and are equal under the language's `==`.
pub(super) fn families_compare([one, same, neg, pos]: &[Value; 4]) {
    assert!(one == same);
    assert_eq!(one.cmp(same), std::cmp::Ordering::Equal);
    assert!(one.surface_eq(same));
    assert_eq!(one.surface_cmp(same), Some(std::cmp::Ordering::Equal));
    assert!(neg != pos);
    assert!(neg.surface_eq(pos));
}

/// `{0: t, 1: t, ..., n - 1: t}` for one tuple `t` of n numbers.
pub(super) fn wide(n: usize) -> Value {
    let t = tuple(n);
    Value::Family(Family::of((0..n as i64).map(|k| (k, t.clone()))))
}

/// `(f, f, ..., f)` for one family `f` of n entries.
pub(super) fn row(n: usize) -> Value {
    let f = Value::Family(Family::set(0..n as i64));
    Value::tuple(vec![f; n])
}

/// Two [`wide`] values are equal, and two [`row`] values equal under the language's relations.
pub(super) fn one_part_compares([a, b, c, d]: &[Value; 4]) {
    assert!(a == b);
    assert!(c.surface_eq(d));
    assert_eq!(c.surface_cmp(d), Some(std::cmp::Ordering::Equal));
}

/// A copy of `v` that shares no part, each tuple and family built anew.
fn unshared(v: &Value) -> Value {
    match v {
        Value::Tuple(items) => Value::tuple(items.as_slice().iter().map(unshared).collect()),
        Value::Family(f) => {
            Value::Family(Family::of(f.iter().map(|(k, v)| (k.clone(), unshared(v)))))
        }
        _ => v.clone(),
    }
}

#[test]
fn shared_and_unshared_values_compare_alike_under_every_relation() {
    // Every value two levels deep over five leaves, as a tuple or a family of two parts, the
    // two parts one shared value or two; each pair is compared as built and as unshared copies.
    let leaves = [
        Value::Int(1),
        Value::Int(2),
        Value::float(-0.0),
        Value::float(0.0),
        Value::float(f64::NAN),
    ];
    let two = |a: &Value, b: &Value| {
        [
            Value::tuple(vec![a.clone(), b.clone()]),
            Value::Family(Family::of([("x", a.clone()), ("y", b.clone())])),
        ]
    };
    let mut one_level = Vec::new();
    for a in &leaves {
        for b in &leaves {
            one_level.extend(two(a, b));
        }
    }
    let mut values = Vec::new();
    for a in one_level.iter().step_by(3) {
        for b in one_level.iter().step_by(7) {
            values.extend(two(a, b));
        }
        values.extend(two(a, a));
    }
    let copies: Vec<Value> = values.iter().map(unshared).collect();
    let mut differ = 0;
    for (a, ca) in values.iter().zip(&copies) {
        for (b, cb) in values.iter().zip(&copies) {
            assert_eq!(a == b, ca == cb, "{a} and {b}");
            assert_eq!(a.cmp(b), ca.cmp(cb), "{a} and {b}");
            assert_eq!(a.surface_eq(b), ca.surface_eq(cb), "{a} and {b}");
            assert_eq!(a.surface_cmp(b), ca.surface_cmp(cb), "{a} and {b}");
            differ += usize::from(a != b);
        }
    }
    assert!(values.len() > 100 && differ > values.len() * values.len() / 2);
}

#[test]
fn a_part_read_under_two_relations_in_one_comparison_gets_each_answer() {
    // The language's order reads the first part by its float order (equal) and the family's
    // copy of it by the total order (-0.0 before 0.0), in one comparison.
    let t = Value::tuple(vec![Value::float(-0.0)]);
    let u = Value::tuple(vec![Value::float(0.0)]);
    let a = Value::tuple(vec![t.clone(), Value::Family(Family::of([("x", t)]))]);
    let b = Value::tuple(vec![u.clone(), Value::Family(Family::of([("x", u)]))]);
    assert_eq!(a.surface_cmp(&b), Some(std::cmp::Ordering::Less));
    assert_eq!(a.cmp(&b), std::cmp::Ordering::Less);
    assert!(a != b);
    assert!(a.surface_eq(&b));
}

/// `h_i = h_0 | {1000 + i: i}` for one family `h_0` of 101 entries, one of them the family
/// `{first, ..., first + n - 1}`: the n families have n ids but share the map node that holds
/// that family, so it is met n times though it is held in one entry of one map.
fn made_from(n: usize, first: i64) -> Value {
    let f = Value::Family(Family::set(first..first + n as i64));
    let h0 = Family::of((0..=100i64).map(|k| (k, if k == 0 { f.clone() } else { Value::Int(k) })));
    let h = (0..n as i64).map(|i| Value::Family(h0.union(&Family::of([(1000 + i, i)])).unwrap()));
    Value::tuple(h.collect())
}

/// [`made_from`] the family `0..n`.
pub(super) fn made(n: usize) -> Value {
    made_from(n, 0)
}

/// Two [`made`] values, built apart, are equal under each relation.
pub(super) fn made_compare([a, b]: &[Value; 2]) {
    assert!(a == b);
    assert_eq!(a.cmp(b), std::cmp::Ordering::Equal);
    assert!(a.surface_eq(b));
    assert_eq!(a.surface_cmp(b), Some(std::cmp::Ordering::Equal));
}

/// Families made from one family that holds a family of 3 are equal when built apart, and
/// ordered by that family when it differs.
#[test]
fn families_made_from_one_family_compare_by_what_it_holds() {
    let other = made_from(3, 1);
    assert!(made(3) == made(3));
    assert_eq!(made(3).cmp(&made(3)), std::cmp::Ordering::Equal);
    assert!(made(3) != other);
    assert_eq!(made(3).cmp(&other), std::cmp::Ordering::Less);
    assert!(!made(3).surface_eq(&other));
}

/// What each benchmark of `bench/shared.rs` asserts besides its ratio, at small sizes: values
/// and families that share their parts compare and key alike, nested sets are shown, one part
/// held in many places compares, and families made from one family are equal. Reading a tuple
/// once per element is checked by `a_record_read_once_per_field_gives_each_field`, and a list
/// built by an accumulator by `an_accumulated_list_holds_every_element_in_order`.
#[test]
fn shared_values_compare_and_show_at_small_sizes() {
    assert_eq!(nested_sets(2).to_string(), "{({(0,)},)}");
    for n in [1, 2, 9] {
        shared_parts_compare(&shared_parts(n));
        shows_nested_sets(&nested_sets(n), n);
        families_compare(&families(n));
        one_part_compares(&[wide(n), wide(n), row(n), row(n)]);
        made_compare(&[made(n), made(n)]);
    }
}
