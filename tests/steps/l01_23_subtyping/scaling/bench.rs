//! The benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `scaling.rs`.

use super::*;

/// Runs `f` on a thread of its own, of the 2 MiB stack a thread has by default, named as the
/// test's thread is. The name is what lets a check count instructions where the hardware has
/// no counter (a Colab VM): each run then goes to a new process of the test, found by that
/// name, under DynamoRIO. A thread with no name, as `std::thread::Builder::new()` made here
/// before, has no test, so its checks fell back to processor time (`work=` in the bench line,
/// with ratios 13.2 and 16.1 for the grid of cells and 10.3 and 12.7 for the pinwheels on hm4,
/// jobs f25 and f27 on main b43e6d8bb; BENCH-main-43-pieces-v5e4).
fn on_thread(f: impl FnOnce() + Send) {
    scaling::on_a_stack(2 << 20, f)
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; at 8192 (1x 479 ms) the
/// test took 17.3 s at load 24, too close to the 20 s limit.
#[test]
fn the_parts_scale() {
    on_thread(|| scaling::check("morphism differences, by count", 4096, |c| run(c, morphism)));
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 2048; 1x 106 ms at load
/// 24.28.
#[test]
fn the_tuple_parts_scale() {
    on_thread(|| scaling::check("tuple differences, by count", 2048, |c| run(c, pair)));
}

/// Size (TEST-bench-move-l0123, author P169): n 512 cells before, now 4096; 1x 165 ms at
/// load 17.44.
#[test]
fn a_product_covered_by_its_cells_scales() {
    // Each cell is disjoint from all but one piece of the split, and contains that piece, so
    // the split of the product makes one piece per cell; splitting on every cell in turn made
    // `n^(n²)` pieces in the worst order (4.3 s at `n = 5`). Building the cells one at a time
    // made `O(n⁴)` nodes (6 s at `n = 32`). Each run takes a new `b`, so no run reads
    // another's results. Below about 512 cells fixed costs dominate building the grid, so
    // its ratio from 64 cells is near 15 alone and passed 24 under the full suite's load.
    on_thread(|| {
        let fresh = std::sync::atomic::AtomicUsize::new(1);
        scaling::check("a grid and its cells, by cell count", 4096, |c| {
            let n = (c as f64).sqrt().round() as usize;
            let (p, cells) = grid(n, 10_000 * fresh.fetch_add(1, Relaxed));
            assert!(
                (&p - &cells).is_empty(),
                "the cells cover the grid at n = {n}"
            );
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 2 before, then 256 (order 2); 1x 117 ms at
/// load 26.19. Now 128 (BENCH-l0123-decoys-near-cap): at 256 the run at 2048 took 17.3 s at
/// load 40 and over the 20 s limit at load 63, with 60.6 times the instructions of the run at
/// 256 (limit 84 for order 2). perf put the time in the emptiness search of `zed_kernel`
/// (`Searching::retest`, `empty_fork`, `any_empty`), spread with no one site above 9%: the
/// `k²` component meets this test is built to make, about 1.7 µs each, not an extra factor.
/// Now 48 (BENCH-main-43-pieces-v5e4): at 128 the run at 1024 took 5.2 s of processor time, 49.6
/// times the run at 128, and the five runs of that meter passed the 20 s phase limit on hm4
/// (job f25 on main b43e6d8bb, 27.3 s with no limit in f27); counted under DynamoRIO, its one
/// run at 1024 passed 20 s alone (job f29). The inputs are built only at the sizes each process
/// runs (`check_order_inputs`). At 48 the `k²` meets are still 2,304 against the `2^48` pieces
/// a split would make.
#[test]
fn passing_over_disjoint_negated_types_scales() {
    // As above with `k` decoys, the first component a tuple of `k` bits so that a meet costs
    // `O(k)`: the decoy `(bits(i), b + 1 + i)` has bit `i` set, and misses `(U, b)` in the
    // second component. The pieces are all met only when the answer is `true`, here once the
    // two halves on bit 0 are reached. Passed over, `k` decoys cost `O(k²)`; split on, `2^k`
    // pieces. Each
    // run takes a new `b`, so no run reads another's results.
    on_thread(|| {
        let n = 48;
        let bit = &lit(0) | &lit(1);
        let bits = |k: usize, i: usize| {
            Type::tuple(
                (0..k)
                    .map(|j| if j == i { lit(1) } else { bit.clone() })
                    .collect(),
            )
        };
        let made = |k: usize| {
            let u = Type::tuple(vec![bit.clone(); k]);
            (k, u, (0..k).map(|i| bits(k, i)).collect::<Vec<_>>())
        };
        let next = std::sync::atomic::AtomicUsize::new(0);
        scaling::check_order_inputs("decoys passed over, by count", n, 2, made, |(k, u, bs)| {
            let k = *k;
            let b = 1_000_100 + next.fetch_add(100, Relaxed);
            let p = Type::tuple(vec![u.clone(), lit(b)]);
            let decoys = Type::union_all(
                bs.iter()
                    .enumerate()
                    .map(|(i, s)| Type::tuple(vec![s.clone(), lit(b + 1 + i)])),
            );
            // The two halves on bit 0 cover `(U, b)`, so every piece must be met.
            let half = |v: usize| {
                let mut c = vec![bit.clone(); k];
                c[0] = lit(v);
                Type::tuple(vec![Type::tuple(c), lit(b)])
            };
            let cover = &(&decoys | &half(0)) | &half(1);
            assert!(!(&p - &decoys).is_empty());
            assert!((&p - &cover).is_empty());
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 1000 before, now 5000; 1x 281 ms at load
/// 27.02.
#[test]
fn many_negated_types_passed_over_scale() {
    // The product `P` of the sets `b + 10_000·k + (0..n)` for `k < 5`, then `b`, less the
    // `n` tuples `T_i` of `b + 10_000·k + i`, then `b - 1`. Each `T_i` meets `P` in the first
    // five components and misses it in the last, so it is passed over, after five non-empty
    // intersections. Each non-empty result discarded every emptiness decided since its query
    // began by scanning all of them: `O(n²)` steps for the `5n` results (ratio 35); the
    // time to build the types hid them at one component. Now the types decided empty are
    // kept in the order decided, and only those since the query began are dropped. Each run
    // takes a new `b`, so no run reads another's results.
    on_thread(|| {
        let fresh = std::sync::atomic::AtomicUsize::new(1);
        scaling::check("a product less n tuples passed over, by n", 5000, |n| {
            let b = 100_000 * fresh.fetch_add(1, Relaxed);
            let meets = |i: usize| (0..5).map(move |k| lit(b + 10_000 * k + i));
            let p = Type::tuple(
                (0..5)
                    .map(|k| Type::union_all((0..n).map(|i| lit(b + 10_000 * k + i))))
                    .chain([lit(b)])
                    .collect(),
            );
            let decoys = Type::union_all(
                (0..n).map(|i| Type::tuple(meets(i).chain([lit(b - 1)]).collect())),
            );
            assert!(
                !(&p - &decoys).is_empty(),
                "the decoys miss the product at n = {n}"
            );
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 400 before, now 4000; 1x 233 ms at load
/// 27.02.
#[test]
fn nested_tuples_scale() {
    // The nodes of a diagram were ordered by their contents, so placing a tuple among those
    // of its thread read down the nested tuples to where they differ: building a tuple
    // nested `d` deep took `O(d²)` steps (ratio 27 to 71 from depth 100). Types and nodes are
    // now ordered by a hash of their contents, kept in each when it is made. From depth 100
    // the small run took a millisecond, and the ratio under the full suite's load reached 43
    // (measured at the old size).
    on_thread(|| {
        let fresh = std::sync::atomic::AtomicUsize::new(1);
        scaling::check("a nested tuple and a query on it, by depth", 4000, |d| {
            let b = 100_000 * fresh.fetch_add(1, Relaxed);
            let x = nested(d, b);
            assert!(x.subtype(&(&nested(d, b) | &lit(1))), "at depth {d}");
            assert!(!x.subtype(&nested(d, b + 1)), "at depth {d}");
        });
    });
}

/// The atom `#a{i}`.
fn atom_a(i: usize) -> Type {
    Type::atom(&format!("a{i}"))
}

/// Literals joined one at a time; atoms in [`atoms_joined_one_at_a_time_scale`], and both
/// removed one at a time in [`literals_and_atoms_removed_one_at_a_time_scale`].
///
/// Size (TEST-bench-move-l0123, author P169): n 1000 before, now 50000; 1x 313 ms at load
/// 28.57.
#[test]
fn literals_and_atoms_joined_one_at_a_time_scale() {
    // A union or difference copied both sets of literals or atom names, and a type's hash
    // read every one, so joining `n` of them one at a time took `O(n²)` steps (ratio 66).
    // The sets are now persistent, each operation walks the smaller one, and the hash of a
    // set is a sum kept as it changes.
    scaling::check("literals joined one at a time, by count", 50000, |n| {
        let u = (0..n).fold(Type::empty(), |u, i| &u | &lit(i));
        assert!(lit(n / 2).subtype(&u) && !lit(n).subtype(&u));
        assert_eq!(u, Type::union_all((0..n).rev().map(lit)));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 1000 before, now 50000; 1x 294 ms at load
/// 18.78.
#[test]
fn atoms_joined_one_at_a_time_scale() {
    scaling::check("atoms joined one at a time, by count", 50000, |n| {
        let u = (0..n).fold(Type::empty(), |u, i| &u | &atom_a(i));
        assert!(atom_a(n / 2).subtype(&u) && !atom_a(n).subtype(&u));
        assert_eq!(u, Type::union_all((0..n).rev().map(atom_a)));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 1000 before, now 30000; 1x 296 ms at load
/// 27.02.
#[test]
fn literals_and_atoms_removed_one_at_a_time_scale() {
    scaling::check(
        "literals and atoms removed one at a time, by count",
        30000,
        |n| {
            let all = &Type::union_all((0..n).map(lit)) | &Type::union_all((0..n).map(atom_a));
            let left = (1..n).fold(all, |u, i| &(&u - &lit(i)) - &atom_a(i));
            assert_eq!(left, &lit(0) | &atom_a(0));
        },
    );
}

/// Builds the second type of a pair from the count and the base.
type Other = fn(usize, usize) -> Type;

/// `odd_tuples(c)` against `other(c)`, a type not equal to it, at `c = n` and `8n`; case `k` of
/// the pool's bases. Each timed run compares `pairs` pairs, each at a base of its own, so a run's
/// count averages the constant that the integers in the types set (PERF-xor-tuple-compare).
fn comparing_exclusive_ors(what: &str, n: usize, pairs: usize, k: usize, other: Other) {
    let make = |c: usize, i: usize| -> Vec<(Type, Type)> {
        (i * pairs..(i + 1) * pairs)
            .map(|j| {
                let b = base(c, k, j);
                (odd_tuples(c, b), other(c, b))
            })
            .collect()
    };
    scaling::check_order_fresh(what, n, 1, make, |c, run_pairs: Vec<(Type, Type)>| {
        for (x, y) in &run_pairs {
            Type::forget_emptiness();
            assert!(!x.equiv(y), "c = {c}");
        }
        run_pairs
    });
}

/// Size (PERF-xor-tuple-compare, author P169): n 512 and 4 pairs per run, its 1 s size; 1x
/// 920 ms at load 69.5, 5,078.5M to 40,462.8M instructions, 7.97 times. With one pair per run
/// (A160: each size runs once) it failed at n 64 (131.9M to 1,397.6M, 10.60 times) and at 1024
/// (2,084M to 25,830M, 12.39 times) but passed at 512 (7.73 times): the instructions per
/// `c ln c` show no upward trend from c 64 to 2048, and callgrind finds no function whose own
/// count grows more than 10.2 times from 512 to 4096 (`c log c` predicts 10.67), but they
/// vary by about 25% with the integers in the types (1.43 times between two bases at c 512,
/// the excess spread over the whole emptiness search, which the digests of those integers
/// order). So one pair compared two inputs' constants; 4 pairs at 4 bases per run average
/// them. Negative controls, run once and not committed: the old setting fails at 10.60 times,
/// and repeating each comparison `c / 512` times fails its 8n phase on time (37.1 s, limit
/// 37 s). Details in COMPLEXITY.md K57.
#[test]
fn comparing_exclusive_ors_of_tuple_types_scales() {
    // `odd_tuples(c)` and `odd_tuples(c + 1)` differ by the one value `(b + c, b + c)`, so they
    // are not equal, and `odd_tuples(c)` built in the reverse order is equal to it (in
    // `comparing_equal_exclusive_ors_of_tuple_types_scales`). Each run compares a pair built
    // before any run is timed, at bases no other run uses. Cross-review xe round 3
    // (docs/reviews/xe-round3.md, Q7) proposed exclusive-or nodes for diagrams that are pure
    // parities, on a measurement of the false comparison at 12.9 s at `c = 512`; on main the
    // split of a tuple part into classes of disjoint cells (COMPLEXITY.md K36) decides both
    // comparisons in about `c log c` (the false one about 8 times the instructions at 8 times
    // `c`, the equal one about 12 times), so the diagrams have no such nodes (COMPLEXITY.md K57).
    comparing_exclusive_ors(
        "an exclusive or of tuple types against one with one more, by count",
        512,
        4,
        0,
        |c, b| odd_tuples(c + 1, b),
    );
}

/// `odd_tuples(c)` built in reverse and compared with its build in turn, made before the run, at
/// `c = n` and `8n`.
#[test]
fn comparing_equal_exclusive_ors_of_tuple_types_scales() {
    // FAIL-l0123-exclusive-or-benches-allocate-nothing: through `comparing_exclusive_ors` the
    // timed run was the comparison alone, of two builds that are one node (item
    // CHAIN-zip-size), constant work (about 33,000 instructions at both sizes) and from
    // 3706656c3 no bytes, which the check of the bytes refuses. The reverse build is timed
    // now, the work that ends at that node; the comparison alone is held to constant time by
    // `one_pass::bench::two_builds_of_an_exclusive_or_are_compared_in_constant_time`.
    let make = |c: usize, i: usize| {
        let b = base(c, 1, i);
        (odd_tuples(c, b), b)
    };
    scaling::check_order_fresh(
        "an exclusive or of tuple types built in reverse and compared with itself, by count",
        N_EQUAL,
        1,
        make,
        |c, (x, b): (Type, usize)| {
            Type::forget_emptiness();
            let y = odd_tuples_reversed(c, b);
            assert!(x.equiv(&y), "c = {c}");
            (x, y)
        },
    );
}

/// Size of [`comparing_equal_exclusive_ors_of_tuple_types_scales`]: 1x 196 ms at load 25,
/// 1,311M to 11,378M instructions, 8.68 times; at 2048 it was 9.06 times, over `PREFERRED`, the
/// ratio falling with `c` as one of `c log c` does.
const N_EQUAL: usize = 8192;

/// Size (TEST-bench-move-l0123, author P169): n 512 before, now 4096; 1x 291 ms at load
/// 18.57.
#[test]
fn listing_a_diagram_with_exponentially_many_paths_scales() {
    // Listing walked every path of the diagram: `2^(c - 1)` at `c` tuple types. Every listing
    // below and in the tests after this one has its small instance in
    // `small_exclusive_ors_and_meets_are_listed`.
    let n = 4096;
    let built = scaling::inputs(n, |c| odd_tuples(c, 0));
    // A parity is an expression over the `c` tuple types, and checking each of the `c` values
    // on all of it was order `c²` (BDD-xor-parity measured 33 M and 2,088 M instructions at `c`
    // 64 and 512); a value is checked on the expression restricted to the tuple types that may
    // hold it, found by its components (LIST-parity-quad, COMPLEXITY.md K57).
    scaling::check("listing an exclusive or of tuple types, by count", n, |c| {
        assert_eq!(built[&c].each_value().map(|v| v.count()), Some(c));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; 1x 510 ms at load
/// 22.31.
#[test]
fn listing_an_exclusive_or_of_nested_tuple_types_scales() {
    // The same with each value one level down, `((b + i, b + i),)`: such a column is found by
    // the first components of its tuples.
    let n = 4096;
    let nested = scaling::inputs(n, nested_parity);
    scaling::check(
        "listing an exclusive or of nested tuple types, by count",
        n,
        |c| {
            assert_eq!(nested[&c].each_value().map(|v| v.count()), Some(c));
        },
    );
}

// Columns no one kind or length lists ([`listing_shape`], LIST-parity-rest): shapes 0, 1
// and 2. Each tuple type is filed by its parts, as the class split does (K36); unfiled,
// each was read for every value (60.3, 60.3 and 45.7 times the instructions from `c` 64 to
// 512). In shapes 4 and 3 (LIST-parity-tail) each row was read for every tuple, and the
// meet of the tuple types was made one by one along a path: from `c` 64 to 512, 50.1 times
// the instructions and 30.4 times the bytes. Such a row is now filed by its second column,
// and the meets along a path are made in balanced runs (`Type::boxes`): 9.4 and 9.7 times
// the instructions.

/// The listing of [`listing_shape`] `which` at `c = n` and `8n`: `per * c` values.
fn listing_a_shape(which: usize, what: &str, per: usize, n: usize) {
    let built = scaling::inputs(n, |c| listing_shape(c, which));
    scaling::check(what, n, |c| {
        assert_eq!(built[&c].each_value().map(|v| v.count()), Some(per * c));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 2048; 1x 121 ms at load
/// 15.71.
#[test]
fn listing_an_exclusive_or_of_integer_or_pair_columns_scales() {
    listing_a_shape(
        0,
        "listing an exclusive or of integer-or-pair columns, by count",
        2,
        2048,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 2048; 1x 151 ms at load
/// 15.71.
#[test]
fn listing_an_exclusive_or_of_columns_of_two_tuple_lengths_scales() {
    listing_a_shape(
        1,
        "listing an exclusive or of columns of two tuple lengths, by count",
        2,
        2048,
    );
}

/// Size (TEST-bench-move-l0123, author P169): left at n 64 because the ratio failed above it:
/// 12.67 times the instructions from 1024 and 26.89 from 8192, 12.22 from 1024 again on
/// 2026-11-22. Each tuple's check walked the open rows again to see whether its kinds decide
/// them all (PERF-listing-complement-meets, `zed_kernel::types` `RowIndex::holds_in`), order
/// `c²`. With that kept per kinds (b22-kernelb5, 2026-11-22, v5e3): 9.01 from 1024, 8.76 from
/// 8192 and 8.83 from 32768, so n is 4096.
#[test]
fn listing_a_meet_of_tuple_types_given_by_their_complements_scales() {
    listing_a_shape(
        2,
        "listing a meet of tuple types given by their complements, by count",
        1,
        4096,
    );
}

/// Size (TEST-bench-move-l0123, author P169): left at n 64 because the ratio failed above it:
/// 12.31 times the instructions from 1024 and 19.24 from 4096, 11.74 from 1024 again on
/// 2026-11-22; the same cause as the test above (PERF-listing-complement-meets). Fixed
/// (b22-kernelb5, 2026-11-22, v5e3): 8.92 from 1024, 8.81 from 8192 and 8.77 from 32768, so n
/// is 4096.
#[test]
fn listing_a_meet_of_pairs_with_a_complement_first_scales() {
    listing_a_shape(
        4,
        "listing a meet of pairs with a complement first, by count",
        1,
        4096,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 8192; 1x 293 ms at load
/// 18.60.
#[test]
fn listing_a_meet_with_a_complement_first_in_a_pair_scales() {
    listing_a_shape(
        3,
        "listing a meet of tuple types with a complement first in a pair, by count",
        1,
        8192,
    );
}

/// Size (TEST-bench-move-l0123, author P169): sizes 64 and 512 before, now 8192 and 65536; 1x
/// 346 ms at load 18.71.
#[test]
fn listing_a_meet_with_tuple_types_of_many_keys_each_scales() {
    // Rows each with keys of their own in a column they could absorb ([`listing_regions`],
    // LIST-parity-tail). Absorbing every second column makes a region, and so a class reading
    // every row, per key: order `c²`, 27.5 times the bytes when it was tried. Such a column is
    // filed by its keys instead. Row `i` takes `x = 2i + 1` out of the first column, which
    // holds only `x = 1` of them, so `3c + 2` values are listed for `c > 1`.
    let n = 8192;
    let regions = scaling::inputs(n, listing_regions);
    let count = |c: usize| regions[&c].each_value().map(|v| v.count());
    // Each tuple was checked on the decision list restricted to the smallest range of halves
    // holding the rows with a key of it, and those rows, two per tuple, are in the order of
    // their hashes, so the range held most rows: 20.3 times the instructions from `c` 64 to
    // 512. The list is read from the blocks those rows change (LIST-parity-keys): 9.5 times,
    // under the limit of 10.5 (measured at the old sizes, 64 and 512).
    let large = scaling::FACTOR * n;
    scaling::compare(
        &format!(
            "listing a meet with tuple types of many keys each, by count: sizes {n} and {large}"
        ),
        1,
        || assert_eq!(count(n), Some(3 * n + 2)),
        || assert_eq!(count(large), Some(3 * large + 2)),
    );
}

/// The listing of [`pairs_off_first`] `which`, whose second component is `x`, at `c = n` and
/// `8n`.
fn listing_pairs_off_first(which: usize, x: &str, n: usize) {
    let built = scaling::inputs(n, |c| pairs_off_first(c, which));
    let what = format!("listing pairs off their first components, the second {x}, by count");
    scaling::check(&what, n, |c| {
        let want = if which == 1 { 1 } else { c };
        assert_eq!(built[&c].each_value().map(|v| v.count()), Some(want));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; 1x 335 ms at load
/// 28.57.
#[test]
fn listing_tuples_that_differ_off_their_first_components_scales() {
    // `((2i, i),)` for `i < c` met with each `((int - (2k + 1), x),)` for `k < c`. Each box of
    // the meet held the meet of all `c + 1` tuple types as a diagram of `c + 1` rows, order
    // `c²` to build and to list, and each tuple was a class of its own, reading every row:
    // from `c` 64 to 256, 16.5 times the instructions for `x` int and 0, and 17.3 times for
    // `x` int - (c + k) (LIST-parity-keys). One-row tuple types now meet column by column, and
    // the scalars there are read by their regions. The types are [`pairs_off_first`]; small
    // instance `a_few_tuples_that_differ_off_their_first_components_are_listed`. Here `x` is
    // every integer; one literal and a complement are the two tests after this one.
    listing_pairs_off_first(0, "all integers", 4096);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; at 8192 (1x 334 ms) the
/// test took 15.0 s at load 24, too close to the 20 s limit.
#[test]
fn listing_tuples_off_their_first_components_the_second_one_literal_scales() {
    listing_pairs_off_first(1, "one literal", 4096);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; 1x 347 ms at load
/// 28.57.
#[test]
fn listing_tuples_off_their_first_components_the_second_a_complement_scales() {
    listing_pairs_off_first(2, "a complement", 4096);
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 128 (order 2); 1x 30 ms at
/// load 17.13.
#[test]
fn a_decision_tree_is_decided_in_polynomial_time() {
    // Splitting the product on every row in turn made `3^c` pieces: 1.14 s at `c = 64` and
    // cubic from there once the split took a column whose cells are disjoint. Narrowing every
    // row on every column at each of the `c` splits was `O(c³)`, `N^1.5` in the `N ≈ 2c²`
    // components written: 2.1 s at `c = 128`. A split now tests again only the rows open on
    // the column it changed: `O(c²)`, linear in `N`.
    on_thread(|| {
        let fresh = std::sync::atomic::AtomicUsize::new(1);
        scaling::check_order("a decision tree, by column count", 128, 2, |c| {
            let (p, rows) = decision_tree(c, 1000 * fresh.fetch_add(1, Relaxed));
            assert!(
                (&p - &Type::union_all(rows)).is_empty(),
                "the rows cover the product at c = {c}"
            );
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 512 before, now 8192; 1x 133 ms at load
/// 17.13.
#[test]
fn a_key_past_many_excluded_tuples_is_found_and_scales() {
    // Each tuple type tried as the key's representative was tested against every other. Small
    // instance `a_key_past_a_few_excluded_tuples_is_found`.
    let promised = |c: usize| Type::exact(past_excluded(c, Type::int()), Type::empty());
    let n = 8192;
    let built = scaling::inputs(n, promised);
    scaling::check(
        "a key's representative past excluded tuple types, by count",
        n,
        |c| {
            Type::forget_emptiness();
            assert!(built[&c].is_empty());
        },
    );
}

/// [`cofinite_scalar_pinwheels`] at `k = n` and `8n`, `full` or not, built before timing.
fn cofinite_scalar_pinwheels_scale(n: usize, full: bool, want: Verdict, how: &'static str) {
    on_thread(move || {
        let built = scaling::inputs(n, |k| cofinite_scalar_pinwheels(k, full));
        scaling::check(
            &format!("k pinwheels, a cofinite scalar end beside #e/#f ends, {how}, by k"),
            n,
            |k| {
                Type::forget_emptiness();
                assert_eq!(built[&k].verdict(), want);
            },
        );
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 523 ms at load
/// 25.24.
#[test]
fn pinwheels_with_a_cofinite_scalar_end_beside_payload_ends_scale() {
    // The cofinite end lists the k - 1 integers of the other pinwheels' scalar ends, and each
    // of those is a finite cell of the integers beside it. When every finite cell of integers
    // joined a cofinite one, all k pinwheels fell in one class (COMPLEXITY K36, T6 repair 7); a
    // finite cell now joins it only when it holds an integer the cofinite one leaves out. The
    // atom ends are keyed by name and payload, apart from the integers. Inputs are built before
    // timing. Measured from k = 16 to 128, empty: 106M to 891M instructions (8.4 times); with
    // the old rule, 441M to 23,266M (52.8 times) and 46.4 times the bytes. With a middle in the
    // test after this one.
    cofinite_scalar_pinwheels_scale(512, true, Verdict::Empty, "empty");
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 1024; at 2048 (1x 749 ms) the
/// test took 17.0 s at load 25, too close to the 20 s limit.
#[test]
fn pinwheels_with_a_cofinite_scalar_end_and_a_middle_scale() {
    cofinite_scalar_pinwheels_scale(1024, false, Verdict::Inhabited, "with a middle");
}

/// [`pinwheels`] of `end` ends at `k = n` and `8n`: empty when `full`, else inhabited.
fn payload_pinwheels_scale(end: End, full: bool, n: usize) {
    on_thread(move || {
        let (how, want) = match full {
            true => ("", Verdict::Empty),
            false => (" with a middle", Verdict::Inhabited),
        };
        let what = match full {
            true => format!("k pinwheels of {end:?} ends, empty, by k"),
            false => format!("k pinwheels of {end:?} ends{how}, by k"),
        };
        scaling::check(&what, n, |k| {
            Type::forget_emptiness();
            assert_eq!(pinwheels(k, full, end).verdict(), want);
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): left at n 64, 1x 275 ms at load 26.19.
#[test]
fn payload_and_one_tuple_pinwheels_scale() {
    // Each value sought in a class of pinwheels was sought on a box holding half of all the
    // ends in the split component, and each test of a cell against it cost that half. Each
    // piece now holds only its own class. The union of the classes was built one class at a
    // time, which is quadratic in the nodes of the diagram: with one-tuple ends and a middle,
    // 25.1 times the work from k = 64 to 512. It is built by halves. Payload ends, empty, here;
    // the other three checks are the three tests after this one.
    payload_pinwheels_scale(End::Payload, true, 64);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 1024; 1x 310 ms at load
/// 26.19.
#[test]
fn payload_pinwheels_with_a_middle_scale() {
    payload_pinwheels_scale(End::Payload, false, 1024);
}

/// Size (TEST-bench-move-l0123, author P169): left at n 64, 1x 343 ms at load 26.06.
#[test]
fn one_tuple_pinwheels_scale() {
    payload_pinwheels_scale(End::OneTuple, true, 64);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 1024; 1x 423 ms at load
/// 26.06.
#[test]
fn one_tuple_pinwheels_with_a_middle_scale() {
    payload_pinwheels_scale(End::OneTuple, false, 1024);
}

/// [`repeating_pinwheels`] at `k = n` and `8n`: empty when `full`, else with a middle.
fn repeating_pinwheels_scale(full: bool, pair: bool, shared: bool, n: usize) {
    on_thread(move || {
        let (what, want) = match full {
            true => (
                format!(
                    "k pinwheels repeating an integer, pair {pair}, shared {shared}, empty, by k"
                ),
                Verdict::Empty,
            ),
            false => (
                "k pinwheels repeating an integer, shared, with a middle, by k".to_string(),
                Verdict::Inhabited,
            ),
        };
        scaling::check(&what, n, |k| {
            Type::forget_emptiness();
            let t = repeating_pinwheels(k, full, pair, shared);
            assert_eq!(t.verdict(), want);
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 446 ms at load
/// 24.38.
#[test]
fn pinwheels_whose_ends_repeat_an_integer_scale() {
    // With the two `b + 1` one shared type: 662M, 9,051M and 36,294M instructions at k = 16,
    // 64 and 128 for `#e((b + 1, b + 5))`; built apart, 145M, 598M and 1,235M. Pair false,
    // shared true here; the other three checks are the three tests after this one.
    repeating_pinwheels_scale(true, false, true, 512);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 412 ms at load
/// 25.38.
#[test]
fn pinwheels_whose_ends_repeat_an_integer_in_a_shared_pair_scale() {
    repeating_pinwheels_scale(true, true, true, 512);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 398 ms at load
/// 25.38.
#[test]
fn pinwheels_whose_ends_repeat_an_integer_in_pairs_built_apart_scale() {
    repeating_pinwheels_scale(true, true, false, 512);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 1024; 1x 231 ms at load
/// 23.79.
#[test]
fn pinwheels_whose_ends_repeat_an_integer_with_a_middle_scale() {
    repeating_pinwheels_scale(false, false, true, 1024);
}

// The checks of [`check_pinwheels`] as scaling checks on `k` pinwheels on `ends(k)`, one test
// each: the verdict of the full union, the two subtype checks, and the union less a box, empty
// and not. Until TEST-bench-move-l0123 (author P169) they were one helper in `scaling.rs`,
// `pinwheels_scale`, at k = 32 and 256, 64 and 512, and 16 and 128.

/// The verdict of the full union of `k` pinwheels on `ends(k)` at `k = n` and `8n`.
fn pinwheels_empty_scale(what: &'static str, ends: fn(usize) -> Vec<[Type; 3]>, n: usize) {
    on_thread(move || {
        scaling::check(&format!("k pinwheels, {what}, empty, by k"), n, |k| {
            Type::forget_emptiness();
            assert_eq!(pinwheels_on(ends(k), true).verdict(), Verdict::Empty);
        });
    });
}

/// The full and the open union of `k` pinwheels on `ends(k)` compared as subtypes at `k = n`
/// and `8n`.
fn pinwheels_subtypes_scale(what: &'static str, ends: fn(usize) -> Vec<[Type; 3]>, n: usize) {
    on_thread(move || {
        scaling::check(&format!("k pinwheels, {what}, subtypes, by k"), n, |k| {
            Type::forget_emptiness();
            let (full, open) = (pinwheels_on(ends(k), true), pinwheels_on(ends(k), false));
            assert!(full.subtype(&open) && !open.subtype(&full));
        });
    });
}

/// The union of `k` pinwheels on `ends(k)`, `full` or not, less [`far_box`] at `k = n` and `8n`.
fn pinwheels_less_a_box_scale(
    what: &'static str,
    ends: fn(usize) -> Vec<[Type; 3]>,
    outside: bool,
    full: bool,
    n: usize,
) {
    on_thread(move || {
        let name = format!("k pinwheels, {what}, full = {full}, less a box, by k");
        scaling::check(&name, n, |k| {
            Type::forget_emptiness();
            let want = match full {
                true => Verdict::Empty,
                false => Verdict::Inhabited,
            };
            assert_eq!(
                (&pinwheels_on(ends(k), full) - &far_box(outside)).verdict(),
                want
            );
        });
    });
}

/// Size (PERF-pinwheel-end-outside): n 32 before, now 256; 1x 0.69 s by `ns` on a Colab VM
/// (v5e2, 2026-11-22), 7.84 times the work at 8n. At TEST-bench-move-l0123 the ratio was 9.61
/// at 32 and 10.70 at 64; on main at 96f8fde43, with no change of this row to the kernel, it
/// was 7.73 at 64 and 7.72 at 256, so the cost was fixed by an earlier row.
#[test]
fn pinwheels_with_an_end_outside_every_tuple_type_scale() {
    // An end outside every tuple type held every one-tuple, so all k pinwheels fell in one
    // class, and the checks below whose top is a meet cost order k^2: from k = 16 to 128,
    // 59.7 times the bytes allocated for the subtype checks and 49.5 times for the union
    // less a box, full. `overlaps` now places such an end at the first components it can
    // hold, which meet only its own pinwheel. COMPLEXITY.md K36. The verdict of the full union
    // here; the subtype checks and the union less a box in the three tests after this one.
    pinwheels_empty_scale("one end outside", negated_ends, 256);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 418 ms at load
/// 25.24.
#[test]
fn pinwheels_with_an_end_outside_every_tuple_type_are_compared_and_scale() {
    pinwheels_subtypes_scale("one end outside", negated_ends, 512);
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 32; 1x 229 ms at load
/// 18.27.
#[test]
fn full_pinwheels_with_an_end_outside_less_a_box_scale() {
    pinwheels_less_a_box_scale("one end outside", negated_ends, true, true, 32);
}

/// Size (PERF-pinwheel-end-outside): n 16 before, now 2048; 1x 0.72 s by `ns` on a Colab VM
/// (v5e2, 2026-11-22), 9.74 times the work at 8n, bytes 8.0 times. At TEST-bench-move-l0123
/// the ratio was 8.76 at 16, 10.85 at 32 and 12.04 at 64; on main at 96f8fde43, with no change
/// of this row to the kernel, it was 7.58 at 64 and 9.35 at 256, so the cost was fixed by an
/// earlier row.
#[test]
fn open_pinwheels_with_an_end_outside_less_a_box_scale() {
    pinwheels_less_a_box_scale("one end outside", negated_ends, true, false, 2048);
}

/// Size (TEST-bench-move-l0123, author P169): n 32 before, now 64; 1x 264 ms at load
/// 23.79.
#[test]
fn pinwheels_whose_ends_share_a_first_component_scale() {
    // Ends that share a first component shared its key, so all k pinwheels fell in one
    // class: from k = 16 to 128, 57.9 times the bytes for the subtype checks and 47.3 times
    // for the union less a box, full. `overlaps` now refines the classes on each later
    // component. COMPLEXITY.md K36. The verdict of the full union here; the subtype checks and
    // the union less a box in the three tests after this one.
    pinwheels_empty_scale("one first component", first_component_ends, 64);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 284 ms at load
/// 23.79.
#[test]
fn pinwheels_whose_ends_share_a_first_component_are_compared_and_scale() {
    pinwheels_subtypes_scale("one first component", first_component_ends, 512);
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 64; 1x 307 ms at load
/// 18.27.
#[test]
fn full_pinwheels_whose_ends_share_a_first_component_less_a_box_scale() {
    pinwheels_less_a_box_scale("one first component", first_component_ends, false, true, 64);
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 1024; 1x 465 ms at load
/// 26.30.
#[test]
fn open_pinwheels_whose_ends_share_a_first_component_less_a_box_scale() {
    pinwheels_less_a_box_scale(
        "one first component",
        first_component_ends,
        false,
        false,
        1024,
    );
}

/// [`squares_less_boxes`] on `k` [`plain_ends`] at `k = n` and `8n`, built before the runs:
/// empty when `full`, else inhabited.
fn disjoint_pinwheels_scale(what: &'static str, cofinite: bool, full: bool, n: usize) {
    on_thread(move || {
        let built = scaling::inputs(n, |k| squares_less_boxes(full, &plain_ends(k, cofinite)));
        scaling::check(what, n, |k| {
            Type::forget_emptiness();
            if full {
                assert!(built[&k].is_empty());
            } else {
                assert!(!built[&k].is_empty());
                assert_eq!(built[&k].verdict(), Verdict::Inhabited);
            }
        });
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 116 ms at load
/// 17.81.
#[test]
fn a_union_of_disjoint_pinwheels_is_decided_piece_by_piece() {
    // The pinwheels are written as their squares less all their boxes (`squares_less_boxes`).
    // No component splits the boxes into disjoint pieces, so without the split into classes
    // each open tuple type is a piece decided against the whole part: from k = 64 to 512, 58.6
    // times the instructions empty, 57.9 times with the cofinite end, and 26.6 times the bytes
    // with a middle (negative control, run once, not committed: `classes` answering `None`).
    // Their cells on the first component fall into one class per pinwheel, sharing no integer,
    // and the halves of the classes are decided and searched apart: 8.8, 8.9 and 8.2 times
    // (limit 13.20, load about 35, 2026-11-12; measured at the old size, k = 64 to 512). The
    // union of the pinwheels (`pinwheels`) is decided one pinwheel at a time by the rule for
    // unions of parts that share no tuple type (K80) too: without the split it took 8.0 times
    // empty and 7.1 times with a middle, from k = 16 to 128, so it does not test the split.
    // Empty here; one end cofinite and with a middle in the two tests after this one.
    disjoint_pinwheels_scale("k disjoint pinwheels, empty, by k", false, true, 512);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 1024; 1x 269 ms at load
/// 18.78.
#[test]
fn a_union_of_disjoint_pinwheels_with_a_cofinite_end_is_decided_piece_by_piece() {
    // A cofinite type lists the integers it leaves out. When any cofinite cell joined
    // its whole universe, all k pinwheels fell in one class: 62.6 times the work from
    // k = 64 to 512. A finite cell now joins it only when it holds an integer the
    // cofinite one does not leave out.
    disjoint_pinwheels_scale(
        "k disjoint pinwheels, one end cofinite, empty, by k",
        true,
        true,
        1024,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 512; 1x 107 ms at load
/// 18.78.
#[test]
fn a_union_of_disjoint_pinwheels_with_a_middle_is_decided_piece_by_piece() {
    disjoint_pinwheels_scale(
        "k disjoint pinwheels with a middle, by k",
        false,
        false,
        512,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 16384; 1x 510 ms at load
/// 17.44.
#[test]
fn a_list_of_two_cycles_is_shown_in_the_size_of_its_type() {
    // The lists whose length is -1 modulo `n` and modulo `n + 1`: the shortest has `n * (n + 1)
    // - 1` links, and `2n + 1` definitions write the type. The list shown is kept as a length
    // the rule on residues picks, so the work is that of walking the two cycles, order `n`;
    // building the list link by link was order `n^2`.
    scaling::check("lengths -1 modulo n and n + 1, by n", 16384, |n| {
        Type::forget_emptiness();
        let t = &period(n, n - 1) & &period(n + 1, n);
        assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; 1x 217 ms at load
/// 17.81.
#[test]
fn a_tuple_that_shapes_hold_only_together_is_checked_in_the_size_of_the_union() {
    // `g` takes `(#a_i, #c)` for each of `n` atoms, and `h` passes it `(#a_0 | … | #a_n-1,
    // #c)`, which no one shape holds: the checker builds each side's kernel type once and
    // the kernel decides it by splitting the first component. The program is
    // [`shapes_program`]; small instance `a_tuple_held_by_a_few_shapes_together_or_by_none`.
    let program = |n: usize| shapes_program(n, "#c");
    // The checker is timed alone, on statements parsed and resolved before the timing
    // (COMPLEXITY.md F85).
    let n = 4096;
    let units = scaling::inputs(n, |n| zed_tests::deep::resolved(&program(n)));
    scaling::check("a tuple held by n shapes together, by n", n, |n| {
        Type::forget_emptiness();
        let (stmts, res) = &units[&n];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 2048; 1x 375 ms at load
/// 17.44.
#[test]
fn a_tuple_that_no_shapes_hold_is_rejected_in_the_size_of_the_union() {
    // As above, with `#d` for `#c`: the kernel shows a value outside every shape, so the
    // shapes are not each tried, which costs every shape times the components. Small instance,
    // with the error message: `a_tuple_held_by_a_few_shapes_together_or_by_none`.
    let program = |n: usize| shapes_program(n, "#d");
    scaling::check("a tuple held by no shape, by n", 2048, |n| {
        Type::forget_emptiness();
        assert!(zedc::run::load(program(n).as_bytes()).is_err());
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 243 ms at load
/// 24.74.
#[test]
fn the_members_of_two_cycles_are_decided_in_the_size_of_their_types() {
    // Every member of a group is decided together, and each reads the cycle through the next
    // member: a cycle walked is kept for every type on it, so each group is walked once, order
    // `n`; walked again for each member, it was order `n^2` (VERDICT-group-readers).
    scaling::check(
        "the members of cycles of n and n + 1 definitions, by n",
        8192,
        |n| {
            Type::forget_emptiness();
            let (a, b) = (period(n, n - 1), period(n + 1, n));
            assert_eq!(a.verdict(), Verdict::Inhabited);
            assert_eq!(b.verdict(), Verdict::Inhabited);
        },
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 1024 before, now 131072; each side about 1 s:
/// 1080 ms for the verdict and 1027 ms for the emptiness, at load 24.28.
#[test]
fn the_verdict_of_a_meet_of_two_cycles_costs_what_its_emptiness_does() {
    // The meet of two cycles is decided by the rule on residues and reads no member's verdict
    // or value, so its verdict decides neither group and does the work `is_empty` does; at n
    // 1024, 13.1M instructions and 0.90M bytes against 13.1M and 0.90M. Those were the least of
    // two runs, the second reusing the unfoldings of the first; this harness counts a first run
    // in a new process, which at a68a99d46 was 45.35M and 7.71M for the emptiness (knownf1,
    // 2026-11-21). On main 74.2M and 11.98M at n 1024, both sides: 1.12 times from REC-cycle
    // 0bfb0cf12 (`forget_emptiness` frees the unfoldings, K68), 1.33 times from 377e39a95 (no
    // ThinLTO in the profile the tests build with), about 1.1 times over later commits with
    // no single step (not bisected). Deciding every member
    // of both groups first (VERDICT-group-readers) cost 87.5M and 10.5M, 6.7 and 11.7 times
    // the emptiness (plan item VERDICT-meet-cost). Running first the deciders of both groups,
    // which the meet's search never reads, cost 15.62G instructions and 2.35G bytes at n 131072
    // against 10.20G and 1.53G, 1.53 times (plan item FAIL-meet-cycles-verdict-cost); with the
    // deciders run when a search reads a member (`Type::judged_read`), 10.20G and 1.53G on both
    // sides. The emptiness is held to the verdict by the test after this one. This is a
    // comparison of two costs at one size, not a scaling test: it runs no second size and checks
    // no ratio between sizes. It stays here as a measurement (TEST-bench-move-l0123, author
    // P169); its answers have a small instance in `small_lists_of_two_cycles_are_decided`.
    let n = 131072;
    let t = &period(n, n - 1) & &period(n + 1, n);
    scaling::compare_costs(
        &format!(
            "the verdict against the emptiness of the lists of lengths -1 modulo {n} and {}",
            n + 1
        ),
        "the verdict reads no group of a type that reads no member's verdict or value",
        1.5,
        || {
            Type::forget_emptiness();
            assert!(!t.is_empty());
        },
        || {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited);
        },
    );
}

/// The test before this one, the other way: about 1 s a side at n 131072.
#[test]
fn the_emptiness_of_a_meet_of_two_cycles_costs_what_its_verdict_does() {
    // The meet's search reads no member of either group, so `is_empty` decides neither group:
    // a group is decided when a search first reads one of its members (`fill_own`). Searching
    // both groups first (`fill_own` from dc96284ee) cost 23.87G instructions and 3.83G bytes
    // at n 131072 against 15.65G and 2.35G for the verdict, which the test before this one did
    // not catch, as it holds only the verdict to the emptiness; with the groups decided when
    // read, 10.20G and 1.53G on both sides (plan item FAIL-meet-cycles-verdict-cost). A
    // comparison of two costs at one size, as the test before this one.
    let n = 131072;
    let t = &period(n, n - 1) & &period(n + 1, n);
    scaling::compare_costs(
        &format!(
            "the emptiness against the verdict of the lists of lengths -1 modulo {n} and {}",
            n + 1
        ),
        "the emptiness decides no group of a type whose search reads no member",
        1.5,
        || {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited);
        },
        || {
            Type::forget_emptiness();
            assert!(!t.is_empty());
        },
    );
}

// `((u, 0),)`, `u = 0..w`, met with the exclusive or of `((int - (2k + 1), int),)` for
// `k < n`, and the exclusive or of each of those met with `((u, 0),)` first: `n` rows and a
// finite side of `w` values. Neither was known finite, since an expression gave each of its
// tuple types as a box (LIST-xor-finite). Every `x < w` is in the `n` rows but the one of
// `2k + 1 = x` when `x` is odd, so for `w ≤ 2n` the even `x` are listed when `n` is odd and
// the odd ones when `n` is even. Built before timing.
//
// The boxes of the second are `n` of `w - 1` values each, order `n²` at `w = n`. Finding
// them compared each `u - (2k + 1)`, made once in the type and again in a box, literal by
// literal: 10.4M and 174M instructions at 64 and 512 rows; two sets made from one set are
// now found equal by `==`, which skips their shared nodes, so it is found finite at
// `w = n`: 9.1M, 78.6M, 720M at 64, 512 and 4096. Listing it read every box, and checked
// each tuple along the chain of `n` exclusive ors of meets, 105M and 6.17G at 64 and 512
// for `n / 2` values (LIST-box-overlap); its boxes are now merged into one box of `u`, the
// chain is read as one exclusive or, and the side, which every tuple changes, is applied
// once: 19.0M, 162M, 1.43G at 64, 512 and 4096. Without the merge 2.0G at 512, without the
// exclusive or 1.40G, without applying the side once 0.98G, with the union of literal sets
// that copies the smaller set 0.42G, each growing as `n²`. Measured at 64, 512 and 4096
// rows: finding the first finite 3.4M, 26.7M, 221M; listing the first 13.2M, 122M, 1.12G.

/// The one-tuple of `t`.
fn one(t: Type) -> Type {
    Type::tuple(vec![t])
}

/// The exclusive or of `x` and `t`.
fn xor(x: Type, t: Type) -> Type {
    &(&x - &t) | &(&t - &x)
}

/// The side `((u, 0),)` for `u < w` met with the exclusive or of the `n` rows, or with `each`
/// the exclusive or of the side met with each row.
fn boxes_family(n: usize, w: usize, each: bool) -> Type {
    let side = one(Type::tuple(vec![Type::union_all((0..w).map(lit)), lit(0)]));
    let rows = (0..n).map(|k| {
        one(Type::tuple(vec![
            &Type::int() - &lit(2 * k + 1),
            Type::int(),
        ]))
    });
    if each {
        rows.fold(Type::empty(), |x, r| xor(x, &side & &r))
    } else {
        &side & &rows.fold(Type::empty(), xor)
    }
}

/// The number of values [`boxes_family`] lists for `w ≤ 2n`.
fn listed(n: usize, w: usize) -> usize {
    if n.is_multiple_of(2) {
        w / 2
    } else {
        w.div_ceil(2)
    }
}

/// [`boxes_family`] at `n` and `8n` rows, `w = n`: found finite, or with `list` listed.
fn boxes_family_scale(what: &str, n: usize, each: bool, list: bool) {
    let met = scaling::inputs(n, |n| boxes_family(n, n, each));
    scaling::check(what, n, |n| {
        if list {
            assert_eq!(met[&n].each_value().map(|v| v.count()), Some(listed(n, n)));
        } else {
            assert!(met[&n].finite());
        }
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 122 ms at load
/// 18.64.
#[test]
fn finding_the_boxes_of_a_meet_with_an_exclusive_or_scales() {
    boxes_family_scale(
        "finding the boxes of a finite type met with the exclusive or",
        8192,
        false,
        false,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 4096; 1x 204 ms at load
/// 18.60.
#[test]
fn listing_a_meet_with_an_exclusive_or_scales() {
    boxes_family_scale(
        "listing a finite type met with the exclusive or",
        4096,
        false,
        true,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 332 ms at load
/// 18.27.
#[test]
fn finding_the_boxes_of_each_row_met_first_scales() {
    boxes_family_scale(
        "finding the boxes of a finite type each row met first",
        8192,
        true,
        false,
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 4096; 1x 397 ms at load
/// 24.85.
#[test]
fn listing_each_row_met_first_scales() {
    boxes_family_scale("listing a finite type each row met first", 4096, true, true);
}

/// The union of `n` exclusive ors `((3k | 3k + 1, 0),) ^ ((3k + 1 | 3k + 2, 0),)`, made one
/// at a time: a chain of `n` unions, whose boxes are kept as a union of persistent sets, and
/// whose listing reads the chain as one union. Each lists `3k` and `3k + 2`. Measured at
/// 128 and 1024: finding it finite 17.4M and 144M instructions, listing it 47M and 396M;
/// copying both sets at each union took 28M and 1.05G, and evaluating each union of the
/// chain again for each tuple 67M and 1.68G.
fn chain_of_unions(n: usize) -> Type {
    let pair = |a: usize, b: usize| one(Type::tuple(vec![&lit(a) | &lit(b), lit(0)]));
    (0..n).fold(Type::empty(), |u, k| {
        &u | &xor(pair(3 * k, 3 * k + 1), pair(3 * k + 1, 3 * k + 2))
    })
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 4096; 1x 116 ms at load
/// 18.64.
#[test]
fn finding_the_boxes_of_a_chain_of_unions_scales() {
    let n = 4096;
    let chain = scaling::inputs(n, chain_of_unions);
    scaling::check("finding the boxes of a chain of unions", n, |n| {
        assert!(chain[&n].finite())
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 2048; 1x 169 ms at load
/// 18.57.
#[test]
fn listing_a_chain_of_unions_scales() {
    let n = 2048;
    let chain = scaling::inputs(n, chain_of_unions);
    scaling::check("listing a chain of unions", n, |n| {
        assert_eq!(chain[&n].each_value().map(|v| v.count()), Some(2 * n));
    });
}

/// The product of 8192 values less 13 decoys. Moved from `scaling.rs` (TEST-bench-move-l0123,
/// author P178): a set of 8192 literals is an unusual size for a regular test. Small instance
/// `negated_types_disjoint_from_a_small_product_are_passed_over`, at 16 values and 4 decoys.
#[test]
fn negated_types_disjoint_from_the_product_are_passed_over() {
    negated_types_disjoint_from_the_product(13);
}

/// [`nested_meets`] at `n` and `8n`, built before the runs: found finite, which asks the nested
/// questions, each once, its walk stopping at the questions answered before. Measured at 4096
/// and 32768: 0.71G and 5.81G instructions, 8.2 times. Before
/// FAIL-group-oracle-order-stack-overflow-seed the questions were asked again at each level,
/// 10 ms at 16 and 17 s at 32, and overflowed the thread's stack at 3000; with the answers
/// kept but each walk reading every type below it, 7.4 ms at 32 and 2.5 s at 512 (order n²).
#[test]
fn finding_the_boxes_of_nested_meets_scales() {
    let n = 4096;
    let nested = scaling::inputs(n, nested_meets);
    scaling::check("finding the boxes of nested meets", n, |n| {
        assert!(nested[&n].finite())
    });
}

/// [`nested_meets`] at `n` and `8n`, built before the runs: listed, `n + 2` values, which are
/// one-tuples nested up to `n` deep, order `n²` in all (power 2). Measured at 32 and 256: 0.13G
/// and 8.57G instructions, 65.9 times, 4.7 s (debug build, load 66, 2026-11-15). Before
/// PERF-list-nested-meets each tuple was read again to its bottom at each level, order `n³`,
/// and this test ran past its 45 s limit. At 64 and 512 it took 27 s, over the 20 s piece limit.
#[test]
fn listing_nested_meets_scales() {
    let n = 32;
    let nested = scaling::inputs(n, nested_meets);
    scaling::check_order("listing nested meets", n, 2, |n| {
        assert_eq!(nested[&n].each_value().map(|v| v.count()), Some(n + 2))
    });
}

/// [`split_row`] at `n` and `8n`, built before the runs: the row is within the rows it splits
/// into, proved by splitting it at its first column (COMPLEXITY.md K120). Unsplit, the row met
/// each of the `n` rows, and each pair met each shape of the column, `n²` pairs, and the proof
/// failed, leaving the difference to decide: 1.7 s at n = 320 (found by
/// FAIL-types-fn-param-exact-domain, through `l01_26_type_resolution`'s
/// `one_variable_takes_n_tuple_shapes_in_linear_time`).
#[test]
fn a_row_of_a_union_of_shapes_is_split_in_linear_time() {
    let n = 2000;
    let pairs = scaling::inputs(n, |m| split_row(m, 7));
    scaling::check("a row of a union of n shapes within its rows", n, |m| {
        let (row, rows) = &pairs[&m];
        assert_eq!(row.subtype_verdict(rows), Verdict::Empty);
    });
}
