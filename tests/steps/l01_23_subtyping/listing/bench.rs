//! The benchmarks of `listing.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `listing.rs`.

use super::*;

#[test]
fn finiteness_scales_with_the_types_not_the_values() {
    // Each type is visited once, on an explicit stack: one with no visited set takes `2^d`
    // steps.
    let built: std::collections::HashMap<usize, Type> =
        [500, 4000].into_iter().map(|d| (d, doubling(d))).collect();
    scaling::check_order("the finite test on doubling types, by depth", 500, 1, |d| {
        assert!(built[&d].finite());
    });
    let squares: std::collections::HashMap<usize, Type> = [100, 800]
        .into_iter()
        .map(|n| {
            let s = Type::union_all((0..n).map(lit));
            (n, Type::tuple(vec![s.clone(), s]))
        })
        .collect();
    // The square of `n` literals has `n²` values: listing them is of order `n²`.
    scaling::check_order("listing a square of literals, by n", 100, 2, |n| {
        assert_eq!(squares[&n].each_value().map(|v| v.count()), Some(n * n));
    });
}

#[test]
fn taking_k_values_costs_k_times_the_depth() {
    // Each value of every type is made once and kept for the pairs that read it, so taking
    // `k` values of `doubling(d)` makes about `k` values at each depth; a value is checked
    // against its row without walking the parts the types below it made.
    let take = |t: &Type, k: usize| {
        assert_eq!(t.each_value().expect("finite").take(k).count(), k);
    };
    let t = doubling(48);
    scaling::check(
        "taking the first k values of doubling(48), by k",
        500,
        |k| take(&t, k),
    );
    let built: std::collections::HashMap<usize, Type> =
        [12, 96].into_iter().map(|d| (d, doubling(d))).collect();
    scaling::check(
        "taking the first 500 values of doubling(d), by d",
        12,
        |d| take(&built[&d], 500),
    );
}

#[test]
fn a_tuple_is_found_tried_in_the_time_of_its_length() {
    // Each tuple tried is looked up by its components' numbers, so its depth is not read
    // again at each level; one compared by its values cost the depth at each of the `d`
    // levels, order `d²` per value.
    let take = |t: &Type, k: usize| {
        assert_eq!(t.each_value().expect("finite").take(k).count(), k);
    };
    let t = doubling_two_boxes(48);
    scaling::check(
        "taking the first k values of a type of two boxes at each of 48 depths, by k",
        500,
        |k| take(&t, k),
    );
    let built: std::collections::HashMap<usize, Type> = [12, 96]
        .into_iter()
        .map(|d| (d, doubling_two_boxes(d)))
        .collect();
    scaling::check(
        "taking the first 500 values of a type of two boxes at each depth, by depth",
        12,
        |d| take(&built[&d], 500),
    );
}

/// Each component of a wide tuple is made on demand, and the maker of the tuple waits for
/// each in turn; the scan of the components resumes where it waited (PERF-tuple-print), so
/// the boxes are entered and left with each component checked a bounded number of times.
#[test]
fn listing_one_wide_tuple_scales() {
    let lits = |n: usize| (0..n).map(lit).collect::<Vec<_>>();
    // Nested components, each a pair made by its own maker: one value, in order.
    let nested = Type::tuple((0..5).map(|i| Type::tuple(vec![lit(i), lit(i)])).collect());
    let pairs = (0..5).map(|i| pair(int(i), int(i))).collect();
    assert_eq!(nested.values_listed(), Some(vec![Value::tuple(pairs)]));
    // Components of two values each, a product, which `values_listed` leaves out: every
    // combination once, the last component fastest.
    let two = |i: usize| &lit(i) | &lit(i + 10);
    let three = Type::tuple((0..3).map(two).collect());
    assert_eq!(three.values_listed(), None);
    let values: Vec<Value> = three.each_value().unwrap().collect();
    assert_eq!(values.len(), 8);
    assert_eq!(values[0], Value::tuple(vec![int(0), int(1), int(2)]));
    assert_eq!(values[1], Value::tuple(vec![int(0), int(1), int(12)]));
    assert_eq!(values[7], Value::tuple(vec![int(10), int(11), int(12)]));
    // A component with no value, after nested components made on demand, at the end and
    // first: no value.
    for at in [0, 3, 6] {
        let mut items: Vec<Type> = (0..6).map(|i| Type::tuple(vec![lit(i)])).collect();
        items.insert(at, Type::tuple(vec![Type::empty()]));
        assert_eq!(Type::tuple(items).values_listed(), Some(vec![]), "{at}");
    }
    // A component of two values between nested ones: two values.
    let mut items: Vec<Type> = (0..6).map(|i| Type::tuple(vec![lit(i)])).collect();
    items[3] = Type::tuple(vec![two(3)]);
    assert_eq!(
        Type::tuple(items).each_value().map(Iterator::count),
        Some(2)
    );
    assert_eq!(
        Type::tuple(lits(4)).values_listed().map(|v| v.len()),
        Some(1)
    );
    let one = wide(3).values_listed().unwrap();
    assert_eq!(one.len(), 1);
    assert!(wide(3).contains(&one[0]));
    let n = 400;
    let built = scaling::inputs(n, wide);
    scaling::check("listing the one value of a tuple of n literals", n, |m| {
        let values = built[&m].values_listed().unwrap();
        assert_eq!(values.len(), 1);
    });
}
