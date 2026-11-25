//! The benchmarks of `value`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). What the table benchmark checks besides the ratio, that each
//! pair enters once, that the half taken out are entered again and the rest are found, is
//! checked at small sizes by `the_pairs_of_one_comparison_are_entered_taken_out_and_met_again`
//! in the tests of `value.rs`; the deep value is digested at 12 and 64 levels by
//! `a_deep_shared_value_is_digested_once_per_sequence`.

use super::tests::{drawn_ints, drawn_pairs, neighbors, nested_record, shared, under_tuples};
use super::*;

/// n neighbor pairs of 64-bit integers compared by `cmp` and by `==`, at the top level and
/// beneath tuples whose first components tie: O(1) each, so O(n). The integers are drawn over
/// the whole range, half from -2 to 2 so that equal pairs are met; the inputs are built
/// before timing. The counts are checked at small sizes by
/// `neighbors_are_counted_by_the_integers_order` in the tests of `value.rs`. A comparison
/// allocates nothing, so the bytes are not held.
#[test]
fn comparing_integers_scales() {
    let ints = crate::scaling::inputs(200_000, drawn_ints);
    let tuples: HashMap<usize, Vec<Value>> =
        ints.iter().map(|(&n, xs)| (n, under_tuples(xs))).collect();
    for (what, inputs) in [
        ("comparing n neighbor pairs of integers", &ints),
        (
            "comparing n neighbor pairs of integers beneath tuples",
            &tuples,
        ),
    ] {
        crate::scaling::check_instructions_only(what, 200_000, 1, |n| {
            let (less, equal) = neighbors(&inputs[&n]);
            assert!(less + equal < n);
            std::hint::black_box((less, equal));
        });
    }
}

#[test]
fn the_table_of_pairs_scales() {
    // n pairs entered, every other one taken out again, as a walk that ends at a difference
    // inside another comparison does, and all n met again. Each step is O(1) on average:
    // the slots are at most half full and the hash spreads ids drawn in order.
    let inputs: HashMap<usize, Vec<Pair>> = [1_280_000, 10_240_000]
        .into_iter()
        .map(|n| (n, drawn_pairs(n)))
        .collect();
    crate::scaling::check_order(
        "the table of pairs: n entered, n/2 taken out, n met again",
        1_280_000,
        1,
        |n| {
            let pairs = &inputs[&n];
            let mut table = ReadSet::new();
            for &p in pairs {
                assert!(table.insert(p));
            }
            for &p in pairs.iter().step_by(2) {
                table.remove(p);
            }
            let again = pairs.iter().filter(|&&p| table.insert(p)).count();
            assert_eq!(again, n.div_ceil(2));
            table.clear();
        },
    );
}

/// n families of one size and different entries put in a hash set keyed by `Value`, the key of
/// eval.rs's `key_index`, escape.rs, empty.rs's `ValueKey`, zedc-check's maps and zed-native's
/// `ConstKey` alike, each of which hashes by `Hash for Value`: O(n). With the hash that read the
/// size alone it was O(n^2), every family compared with each one before it
/// (PERF-family-hash-count-only).
#[test]
fn a_hash_set_of_families_of_one_size_scales() {
    let inputs = crate::scaling::inputs(20_000, |n| {
        (0..n as i64)
            .map(|i| Value::Family(Family::of([(1_i64, i), (2, -i), (i + 3, 0)])))
            .collect::<Vec<_>>()
    });
    crate::scaling::check_order(
        "a hash set of n families of three entries",
        20_000,
        1,
        |n| {
            let set: HashSet<&Value> = inputs[&n].iter().collect();
            assert_eq!(set.len(), n);
        },
    );
}

/// A map of n entries changed one entry at a time, hashed after each change: each hash reads
/// the O(log n) entries the change put on its path, the rest kept by the branches
/// (`btree::Map::sum`), so O(n log n) in all; the naive hash read all n each time, O(n^2).
#[test]
fn hashing_a_map_after_each_change_scales() {
    crate::scaling::check_order("n inserts into a map, hashed after each", 20_000, 1, |n| {
        let mut m: btree::Map<Value, Value> = btree::Map::default();
        let mut rng = crate::seed::Rng::new(7);
        for i in 0..n {
            m.insert(Value::Int(rng.int(0, i64::MAX)), Value::Int(i as i64));
            std::hint::black_box(digest(&Value::Family(Family::from_map(m.clone()))));
        }
    });
}

/// n records nested one in the next, each of 17 fields, so its map's root is an inner node of
/// two leaves of 8 and the field `i` between them, which holds the record before; each record
/// is hashed once made. A hash reads the new record's entries and the kept sums beneath
/// (`btree::Map::sum`): O(1) each, O(n) in all. When an inner root kept no sum of its own
/// separators, each hash read `i` again in every record beneath, O(n^2) (BTREE-inner-root-sum).
#[test]
fn hashing_records_nested_at_an_inner_roots_separator_scales() {
    crate::scaling::check_order(
        "n records of 17 fields nested at field i, hashed after each",
        2_000,
        1,
        |n| {
            let mut rec = Family::of([("x", 0_i64)]);
            for d in 0..n as i64 {
                rec = Family::of(nested_record(d, Value::Family(rec)));
                std::hint::black_box(digest(&Value::Family(rec.clone())));
            }
        },
    );
}

/// A list made by n `++` of short lists, hashed after each: each hash reads the O(log n) parts
/// the join made, the rest kept by the chain's nodes (`Chain::sum`), O(n log n) in all.
#[test]
fn hashing_a_list_after_each_join_scales() {
    crate::scaling::check_order("n joins of a list, hashed after each", 5_000, 1, |n| {
        let mut list = Family::of([(0_i64, 0_i64)]);
        for i in 0..n as i64 {
            let part = Family::of([(0_i64, i), (1, -i)]);
            list = list.concat(&part).expect("lists join");
            std::hint::black_box(digest(&Value::Family(list.clone())));
        }
    });
}

/// One map `base` of the n keys `0 ..< n`, joined by `++` to n lists of one entry, on either
/// side. Each join tests that `base` is a list (`Family::may_be_list`): its ends and count, then
/// whether all its keys are integers, which the first join reads from all n keys and every later
/// join from the answers `base`'s branches kept (`btree::Map::all_keys`), O(1); the join itself
/// is O(log n). So O(n log n) in all; testing every key at each join took O(n^2)
/// (PROOF-sweep-zed-kernel).
#[test]
fn joining_one_map_to_many_lists_scales() {
    crate::scaling::check_order("one map of n keys joined to n lists", 20_000, 1, |n| {
        let base = Family::from_map(
            (0..n as i64)
                .map(|k| (Value::Int(k), Value::Int(k)))
                .collect(),
        );
        for i in 0..n as i64 {
            let one = Family::of([(0_i64, i)]);
            std::hint::black_box(base.concat(&one).expect("lists join"));
            std::hint::black_box(one.concat(&base).expect("lists join"));
        }
    });
}

/// A family nested 200,000 levels deep, each family the value of the one above, is digested:
/// the families are summed from the innermost out by `fill`, with no stack per level.
#[test]
fn a_family_200000_levels_deep_is_digested() {
    let mut v = Value::Int(0);
    for i in 0..200_000_i64 {
        v = Value::Family(Family::of([(i, v)]));
    }
    let _ = digest(&v);
}

/// A value 200,000 levels deep, each level holding the one below twice, is digested: the walk
/// keeps its own stack, so the depth is not limited by the thread's (author P178: an unusual
/// depth is a benchmark).
#[test]
fn a_value_200000_levels_deep_is_digested() {
    let deep = shared(200_000);
    let _ = digest(&deep);
}

/// The failures `#e0`, …, `#e(n-1)` merged as a balanced tree, each half merged first, as the
/// product `#e0 * … * #e(n-1)` that l01_20's provenance benchmark evaluates merges them
/// (SCALE-near-prov-members). Proof that the work is O(n log n): the tree has `⌈log2 n⌉`
/// levels; at each, the merges take sets of `n` members in all, and a merge of two sets of
/// `a ≥ b` members keeps the larger and adds the `b` others (`Value::merge_failures`), by
/// inserts when `b · ⌈log2(a + 1)⌉ ≤ a + b` (then `O(a + b)` comparisons) and else by
/// `Family::extend`'s sorted merge, `O(a + b)`; the sets of one level so cost `O(n)`, and the
/// tree `O(n log n)`. Before the merge, each of the `b` was inserted, `O(b log a)`, so
/// `O(n log n)` a level and `O(n log² n)` in all, 8·(ln 8n / ln n)² = 11.37 at n = 50,000
/// against n log n's 9.54. Held to n log n's ratio (`check_n_log_n`). Small instances:
/// `extending_a_family_by_many_entries_merges_and_by_few_inserts` in the tests of `value.rs`.
#[test]
fn merging_a_balanced_tree_of_failures_scales() {
    fn merge(xs: &[Value]) -> Value {
        match xs.len() {
            1 => xs[0].clone(),
            k => Value::merge_failures([merge(&xs[..k / 2]), merge(&xs[k / 2..])]),
        }
    }
    let atoms = crate::scaling::inputs(50_000, |n| {
        (0..n)
            .map(|i| Value::atom(&format!("e{i}")))
            .collect::<Vec<_>>()
    });
    crate::scaling::check_n_log_n("a balanced merge of n failures", 50_000, |n| {
        let all = merge(&atoms[&n]);
        assert_eq!(all.errs().map(|f| f.len()), Some(n));
    });
}
