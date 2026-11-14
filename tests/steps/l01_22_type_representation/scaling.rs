//! Types at the rule of low complexity (DESIGN.md Part G). A union or intersection of `n`
//! types was built one type at a time, and each tuple type joined to a decision diagram of the
//! ones before it, so `n` tuple types of one length took `O(n²)`; they are now joined in pairs.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use zed_kernel::types::Type;
use zed_kernel::value::Value;
use zed_tests::scaling;

use zed_tests::step_helpers::l01_16_elaboration::{Checked, checked, elab};

/// A string of 1000 characters ending in `i`, as a type.
fn long(i: usize) -> Type {
    Type::lit(&Value::str(&format!("{}{i}", "s".repeat(1000)))).unwrap()
}

/// The tuple `(… ((long(b), long(b)), long(b + 1)) …, long(b + d - 1))`, nested `d` deep.
fn chain(d: usize, b: usize) -> Type {
    (0..d).fold(long(b), |t, i| Type::tuple(vec![t, long(b + i)]))
}

#[test]
fn the_text_of_a_type_holding_the_complement_of_an_atom_payload_is_made() {
    let t = &Type::top() - &Type::atom_with("a", &Type::tuple(vec![Type::int()]));
    assert_eq!(
        t.to_string(),
        r"(| bool int rat f32 f64 String (\ #_ (#a (tuple int))) tuple struct morphism)"
    );
}

/// `n` distinct pairs of one length.
fn pairs(n: usize) -> Vec<Type> {
    (0..n)
        .map(|i| Type::tuple(vec![Type::atom(&format!("a{i}")), Type::int()]))
        .collect()
}

/// A test of `x` against the union of `n` such pairs.
fn union(n: usize) -> String {
    let arms: Vec<String> = (0..n).map(|i| format!("(#a{i}, int)")).collect();
    format!("f(x) = x is {};\n", arms.join(" | "))
}

/// The morphism type `T(d)`, where `T(0)` is `int` and `T(k + 1)` is `T(k) -> T(k)`: each level
/// holds the one below as its keys and its values, so a comparison that reads the contents of
/// two such types built apart reads every level.
fn arrows(d: usize) -> Type {
    (0..d).fold(Type::int(), |t, _| Type::exact(t.clone(), t))
}

/// The union of the `n` morphism types `#a{i} -> int`.
fn arrow_union(n: usize) -> Type {
    (0..n).fold(Type::empty(), |u, i| {
        &u | &Type::exact(Type::atom(&format!("a{i}")), Type::int())
    })
}

/// Small instance of `bench::the_text_of_a_deeply_nested_type_scales` (TEST-bench-move-l0123,
/// author P169): a tuple of long strings nested 3 deep prints each tuple and each string in
/// full.
#[test]
fn the_text_of_a_nested_type_of_long_strings_is_made() {
    assert!(chain(2, 0).to_string().starts_with("(tuple (tuple \"sss"));
    let text = chain(3, 0).to_string();
    assert!(text.starts_with("(tuple (tuple (tuple \"sss"), "{text}");
    assert!(text.len() > 1000 * 4, "{}", text.len());
    assert_eq!(text.matches("(tuple").count(), 3, "{text}");
}

/// Small instance of `bench::a_union_of_many_tuple_types_scales` (TEST-bench-move-l0123, author
/// P169): `is` against a union of 4 pairs elaborates alike checked or not, and the union of 4
/// pairs and the intersection of their complements are not empty.
#[test]
fn a_union_of_a_few_tuple_types_elaborates_and_builds() {
    let text = union(4);
    let unit = checked(&text);
    assert_eq!(unit.elab().defs, elab(&text).unwrap().defs);
    let f = unit.elab().get("f").unwrap().to_string();
    assert!(f.contains("is (#a0, int) | (#a1, int)"), "{f}");
    assert!(!Type::union_all(pairs(4)).is_empty());
    assert!(!Type::meet_all(pairs(4).iter().map(|p| !p)).is_empty());
}

/// Small instance of `bench::equal_morphism_types_built_apart_compare_in_linear_time`
/// (TEST-bench-move-l0123, author P169): morphism types 6 deep, and unions of 6 morphism
/// types, built apart are equal, and differ from those one level or one member short.
#[test]
fn equal_morphism_types_built_apart_are_equal() {
    assert!(arrows(6) == arrows(6));
    assert!(arrows(5) != arrows(6));
    assert!(arrow_union(6) == arrow_union(6));
    assert!(arrow_union(5) != arrow_union(6));
}

mod bench;
