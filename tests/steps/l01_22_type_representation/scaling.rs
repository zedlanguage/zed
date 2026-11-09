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
fn the_text_of_a_deeply_nested_type_scales() {
    // Each type's text was made from copies of the texts of the types inside it. Each run
    // makes new types, whose texts are not yet made. The text is made in a loop, so the test
    // runs on the stack of a test thread.
    let b = AtomicUsize::new(0);
    scaling::check("the text of a tuple nested n deep", 600, |d| {
        let b = b.fetch_add(1_000_000, Relaxed) + 1_000_000;
        assert!(chain(d, b).to_string().len() > 1000 * d);
    });
    assert!(chain(2, 0).to_string().starts_with("(tuple (tuple \"sss"));
}

#[test]
fn the_text_of_a_type_holding_the_complement_of_an_atom_payload_is_made() {
    let t = &Type::top() - &Type::atom_with("a", &Type::tuple(vec![Type::int()]));
    assert_eq!(
        t.to_string(),
        r"(| bool int rat f64 String (\ #_ (#a (tuple int))) tuple struct morphism)"
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

#[test]
fn a_union_of_many_tuple_types_scales() {
    // Elaboration is timed alone: parsing and checking the unit did nearly three times its
    // work at 250 pairs, enough to hide a quadratic added to it (COMPLEXITY.md F85).
    let units: BTreeMap<usize, Checked> = [250, scaling::FACTOR * 250]
        .into_iter()
        .map(|n| (n, checked(&union(n))))
        .collect();
    assert_eq!(units[&250].elab().defs, elab(&union(250)).unwrap().defs);
    scaling::check("elaborating `is` against a union of n pairs", 250, |n| {
        let u = units[&n].elab();
        assert!(u.get("f").unwrap().to_string().contains("is (#a"));
    });
    let built: Mutex<BTreeMap<usize, Vec<Type>>> = Mutex::default();
    let get = |n| {
        built
            .lock()
            .unwrap()
            .entry(n)
            .or_insert_with(|| pairs(n))
            .clone()
    };
    scaling::check("the union of n pairs", 250, |n| {
        assert!(!Type::union_all(get(n)).is_empty());
    });
    scaling::check("the intersection of n complements of pairs", 250, |n| {
        assert!(!Type::meet_all(get(n).iter().map(|p| !p)).is_empty());
    });
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

#[test]
fn equal_morphism_types_built_apart_compare_in_linear_time() {
    // Item ATOM-intern (COMPLEXITY.md K66): a morphism type equal to one alive, built apart
    // from it, is found equal level by level as it is built, and compared at the top.
    let chains = scaling::inputs(2_000, arrows);
    scaling::check(
        "a morphism type n deep built again and compared",
        2_000,
        |d| {
            let b = arrows(d);
            assert!(chains[&d] == b);
        },
    );
    let unions = scaling::inputs(500, arrow_union);
    scaling::check(
        "a union of n morphism types built again and compared",
        500,
        |n| {
            let b = arrow_union(n);
            assert!(unions[&n] == b);
        },
    );
}
