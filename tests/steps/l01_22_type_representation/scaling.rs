//! Types at the rule of low complexity (DESIGN.md Part G). A union or intersection of `n`
//! types was built one type at a time, and each tuple type joined to a decision diagram of the
//! ones before it, so `n` tuple types of one length took `O(n²)`; they are now joined in pairs.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;

use zed_kernel::types::Type;
use zed_kernel::value::Value;
use zed_tests::scaling;

use crate::l01_16_elaboration::elab;

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
    // makes new types, whose texts are not yet made.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            let b = Cell::new(0);
            scaling::check("the text of a tuple nested n deep", 600, |d| {
                b.set(b.get() + 1_000_000);
                assert!(chain(d, b.get()).to_string().len() > 1000 * d);
            });
            assert!(chain(2, 0).to_string().starts_with("(tuple (tuple \"sss"));
        })
        .unwrap()
        .join()
        .unwrap();
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
    let texts: RefCell<BTreeMap<usize, String>> = RefCell::default();
    scaling::check("is against a union of n pairs", 250, |n| {
        let text = texts
            .borrow_mut()
            .entry(n)
            .or_insert_with(|| union(n))
            .clone();
        let u = elab(&text).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(u.get("f").unwrap().to_string().contains("(is (| "));
    });
    let built: RefCell<BTreeMap<usize, Vec<Type>>> = RefCell::default();
    let get = |n| {
        built
            .borrow_mut()
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

#[test]
#[should_panic(expected = "the rule of low complexity")]
fn the_union_taken_one_type_at_a_time_does_not_scale() {
    // The negative control: the order the test above guards against is caught.
    let built: RefCell<BTreeMap<usize, Vec<Type>>> = RefCell::default();
    scaling::check("the union of n pairs, one at a time", 200, |n| {
        let ts = built
            .borrow_mut()
            .entry(n)
            .or_insert_with(|| pairs(n))
            .clone();
        ts.into_iter().fold(Type::empty(), |a, b| a | b);
    });
}
