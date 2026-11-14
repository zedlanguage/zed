//! The benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `scaling.rs`.

use super::*;

#[test]
fn the_text_of_a_deeply_nested_type_scales() {
    // Each type's text was made from copies of the texts of the types inside it. Each run
    // makes new types, whose texts are not yet made. The text is made in a loop, so the test
    // runs on the stack of a test thread.
    // TEST-bench-move-l0123 (author P169): n was 600, now 4,800; 1x measured 151 ms (ns=151400786)
    // at load 25.71 on 2026-11-14.
    let b = AtomicUsize::new(0);
    scaling::check("the text of a tuple nested n deep", 4800, |d| {
        let b = b.fetch_add(1_000_000, Relaxed) + 1_000_000;
        assert!(chain(d, b).to_string().len() > 1000 * d);
    });
    assert!(chain(2, 0).to_string().starts_with("(tuple (tuple \"sss"));
}

// A union of many tuple types scales. The three checks were one test,
// `a_union_of_many_tuple_types_scales`, until TEST-bench-move-l0123 (author P169) split it so
// that each runs within the time of one test.

#[test]
fn elaborating_is_against_a_union_of_many_tuple_types_scales() {
    // Elaboration is timed alone: parsing and checking the unit did nearly three times its
    // work at 250 pairs, enough to hide a quadratic added to it (COMPLEXITY.md F85).
    // TEST-bench-move-l0123 (author P169): n was 250, now 4,000; 1x measured 109 ms (ns=109311183)
    // at load 25.71 on 2026-11-14.
    let n = 4000;
    let units: BTreeMap<usize, Checked> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, checked(&union(n))))
        .collect();
    assert_eq!(units[&n].elab().defs, elab(&union(n)).unwrap().defs);
    scaling::check("elaborating `is` against a union of n pairs", n, |n| {
        let u = units[&n].elab();
        assert!(u.get("f").unwrap().to_string().contains("is (#a"));
    });
}

/// The pairs of [`pairs`] at size `n`, built at the first call for each size and kept.
fn kept_pairs(built: &Mutex<BTreeMap<usize, Vec<Type>>>, n: usize) -> Vec<Type> {
    built
        .lock()
        .unwrap()
        .entry(n)
        .or_insert_with(|| pairs(n))
        .clone()
}

#[test]
fn the_union_of_many_tuple_types_scales() {
    // TEST-bench-move-l0123 (author P169): n was 250, now 10,000; 1x measured 260 ms (ns=260057244)
    // at load 25.41 on 2026-11-14.
    let built = Mutex::default();
    scaling::check("the union of n pairs", 10000, |n| {
        assert!(!Type::union_all(kept_pairs(&built, n)).is_empty());
    });
}

#[test]
fn the_intersection_of_many_complements_of_tuple_types_scales() {
    // TEST-bench-move-l0123 (author P169): n was 250, now 10,000; 1x measured 254 ms (ns=254083315)
    // at load 25.41 on 2026-11-14.
    let built = Mutex::default();
    scaling::check("the intersection of n complements of pairs", 10000, |n| {
        assert!(!Type::meet_all(kept_pairs(&built, n).iter().map(|p| !p)).is_empty());
    });
}

// Equal morphism types built apart compare in linear time. The two checks were one test,
// `equal_morphism_types_built_apart_compare_in_linear_time`, until TEST-bench-move-l0123
// (author P169) split it so that each runs within the time of one test.

#[test]
fn equal_deep_morphism_types_built_apart_compare_in_linear_time() {
    // Item ATOM-intern (COMPLEXITY.md K66): a morphism type equal to one alive, built apart
    // from it, is found equal level by level as it is built, and compared at the top.
    // TEST-bench-move-l0123 (author P169): n was 2,000, now 64,000; 1x measured 160 ms
    // (ns=159742111) at load 25.41 on 2026-11-14.
    let chains = scaling::inputs(64_000, arrows);
    scaling::check(
        "a morphism type n deep built again and compared",
        64_000,
        |d| {
            let b = arrows(d);
            assert!(chains[&d] == b);
        },
    );
}

#[test]
fn equal_unions_of_morphism_types_built_apart_compare_in_linear_time() {
    // Item ATOM-intern (COMPLEXITY.md K66), for a union of morphism types.
    // TEST-bench-move-l0123 (author P169): n was 500, now 13,000; 1x measured 238 ms (ns=238176183)
    // at load 25.41 on 2026-11-14.
    let unions = scaling::inputs(13_000, arrow_union);
    scaling::check(
        "a union of n morphism types built again and compared",
        13_000,
        |n| {
            let b = arrow_union(n);
            assert!(unions[&n] == b);
        },
    );
}
