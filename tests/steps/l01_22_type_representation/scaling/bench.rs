//! The benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `scaling.rs`.

use super::*;

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
