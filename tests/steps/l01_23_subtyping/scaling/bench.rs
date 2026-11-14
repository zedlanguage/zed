//! The benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `scaling.rs`.

use super::*;

#[test]
fn the_parts_scale() {
    std::thread::Builder::new()
        .spawn(|| {
            scaling::check("morphism differences, by count", 16, |c| run(c, morphism));
            scaling::check("tuple differences, by count", 16, |c| run(c, pair));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_product_covered_by_its_cells_scales() {
    // Each cell is disjoint from all but one piece of the split, and contains that piece, so
    // the split of the product makes one piece per cell; splitting on every cell in turn made
    // `n^(n²)` pieces in the worst order (4.3 s at `n = 5`). Building the cells one at a time
    // made `O(n⁴)` nodes (6 s at `n = 32`). Each run takes a new `b`, so no run reads
    // another's results. Below about 512 cells fixed costs dominate building the grid, so
    // its ratio from 64 cells is near 15 alone and passed 24 under the full suite's load.
    std::thread::Builder::new()
        .spawn(|| {
            let fresh = std::sync::atomic::AtomicUsize::new(1);
            scaling::check("a grid and its cells, by cell count", 512, |c| {
                let n = (c as f64).sqrt().round() as usize;
                let (p, cells) = grid(n, 10_000 * fresh.fetch_add(1, Relaxed));
                assert!(
                    (&p - &cells).is_empty(),
                    "the cells cover the grid at n = {n}"
                );
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn passing_over_disjoint_negated_types_scales() {
    // As above with `k` decoys, the first component a tuple of `k` bits so that a meet costs
    // `O(k)`: the decoy `(bits(i), b + 1 + i)` has bit `i` set, and misses `(U, b)` in the
    // second component. The pieces are all met only when the answer is `true`, here once the
    // two halves on bit 0 are reached. Passed over, `k` decoys cost `O(k²)`; split on, `2^k`
    // pieces. Each
    // run takes a new `b`, so no run reads another's results.
    std::thread::Builder::new()
        .spawn(|| {
            let bit = &lit(0) | &lit(1);
            let bits = |k: usize, i: usize| {
                Type::tuple(
                    (0..k)
                        .map(|j| if j == i { lit(1) } else { bit.clone() })
                        .collect(),
                )
            };
            let made: std::collections::BTreeMap<usize, (Type, Vec<Type>)> = [2, 16]
                .into_iter()
                .map(|k| {
                    let u = Type::tuple(vec![bit.clone(); k]);
                    (k, (u, (0..k).map(|i| bits(k, i)).collect()))
                })
                .collect();
            let next = std::sync::atomic::AtomicUsize::new(0);
            scaling::check_order("decoys passed over, by count", 2, 2, |k| {
                let b = 1_000_100 + next.fetch_add(100, Relaxed);
                let (u, bs) = &made[&k];
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
        })
        .unwrap()
        .join()
        .unwrap();
}

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
    std::thread::Builder::new()
        .spawn(|| {
            let fresh = std::sync::atomic::AtomicUsize::new(1);
            scaling::check("a product less n tuples passed over, by n", 1000, |n| {
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
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn nested_tuples_scale() {
    // The nodes of a diagram were ordered by their contents, so placing a tuple among those
    // of its thread read down the nested tuples to where they differ: building a tuple
    // nested `d` deep took `O(d²)` steps (ratio 27 to 71 from depth 100). Types and nodes are
    // now ordered by a hash of their contents, kept in each when it is made. From depth 100
    // the small run took a millisecond, and the ratio under the full suite's load reached 43.
    std::thread::Builder::new()
        .spawn(|| {
            let fresh = std::sync::atomic::AtomicUsize::new(1);
            scaling::check("a nested tuple and a query on it, by depth", 400, |d| {
                let b = 100_000 * fresh.fetch_add(1, Relaxed);
                let x = nested(d, b);
                assert!(x.subtype(&(&nested(d, b) | &lit(1))), "at depth {d}");
                assert!(!x.subtype(&nested(d, b + 1)), "at depth {d}");
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn literals_and_atoms_joined_one_at_a_time_scale() {
    // A union or difference copied both sets of literals or atom names, and a type's hash
    // read every one, so joining `n` of them one at a time took `O(n²)` steps (ratio 66).
    // The sets are now persistent, each operation walks the smaller one, and the hash of a
    // set is a sum kept as it changes.
    let atom = |i: usize| Type::atom(&format!("a{i}"));
    scaling::check("literals joined one at a time, by count", 1000, |n| {
        let u = (0..n).fold(Type::empty(), |u, i| &u | &lit(i));
        assert!(lit(n / 2).subtype(&u) && !lit(n).subtype(&u));
        assert_eq!(u, Type::union_all((0..n).rev().map(lit)));
    });
    scaling::check("atoms joined one at a time, by count", 1000, |n| {
        let u = (0..n).fold(Type::empty(), |u, i| &u | &atom(i));
        assert!(atom(n / 2).subtype(&u) && !atom(n).subtype(&u));
        assert_eq!(u, Type::union_all((0..n).rev().map(atom)));
    });
    scaling::check(
        "literals and atoms removed one at a time, by count",
        1000,
        |n| {
            let all = &Type::union_all((0..n).map(lit)) | &Type::union_all((0..n).map(atom));
            let left = (1..n).fold(all, |u, i| &(&u - &lit(i)) - &atom(i));
            assert_eq!(left, &lit(0) | &atom(0));
        },
    );
}

#[test]
fn comparing_exclusive_ors_of_tuple_types_scales() {
    // `odd_tuples(c)` and `odd_tuples(c + 1)` differ by the one value `(b + c, b + c)`, so they
    // are not equal, and `odd_tuples(c)` built in the reverse order is equal to it. Each run
    // compares a pair built before any run is timed, at bases no other run uses. Cross-review
    // xe round 3 (docs/reviews/xe-round3.md, Q7) proposed exclusive-or nodes for diagrams that
    // are pure parities, on a measurement of the false comparison at 12.9 s at `c = 512`; on
    // main the split of a tuple part into classes of disjoint cells (COMPLEXITY.md K36)
    // decides the false comparison in time about linear in `c` and the equal one in about
    // `c log c` (about 8 and 12 times the instructions at 8 times `c`), so the diagrams have no
    // such nodes (COMPLEXITY.md K57).
    let (n, (small_runs, large_runs)) = (64, scaling::Meter::new().runs());
    // Builds the second type of a pair from the count and the base.
    type Other = fn(usize, usize) -> Type;
    let cases: [(&str, Other, bool); 2] = [
        (
            "an exclusive or of tuple types against one with one more, by count",
            |c, b| odd_tuples(c + 1, b),
            false,
        ),
        (
            "an exclusive or of tuple types against itself built in reverse, by count",
            odd_tuples_reversed,
            true,
        ),
    ];
    for (k, (what, other, equal)) in cases.into_iter().enumerate() {
        let make = |c, b| (odd_tuples(c, b), other(c, b));
        let pools = [
            (n, pool(n, small_runs, k, make)),
            (8 * n, pool(8 * n, large_runs, k, make)),
        ];
        scaling::check(what, n, |c| {
            let (_, pool) = pools.iter().find(|(size, _)| *size == c).expect("a size");
            let (x, y) = pool
                .lock()
                .expect("the pool")
                .pop()
                .expect("one pair per run");
            Type::forget_emptiness();
            assert_eq!(x.equiv(&y), equal, "c = {c}");
        });
    }
}

#[test]
fn listing_a_diagram_with_exponentially_many_paths_scales() {
    // Listing walked every path of the diagram: `2^(c - 1)` at `c` tuple types. Every listing
    // below has its small instance in `small_exclusive_ors_and_meets_are_listed`.
    let built: std::collections::HashMap<usize, Type> = [512, 4096]
        .into_iter()
        .map(|c| (c, odd_tuples(c, 0)))
        .collect();
    // A parity is an expression over the `c` tuple types, and checking each of the `c` values
    // on all of it was order `c²` (BDD-xor-parity measured 33 M and 2,088 M instructions at `c`
    // 64 and 512); a value is checked on the expression restricted to the tuple types that may
    // hold it, found by its components (LIST-parity-quad, COMPLEXITY.md K57).
    scaling::check(
        "listing an exclusive or of tuple types, by count",
        512,
        |c| {
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(c));
        },
    );
    // The same with each value one level down, `((b + i, b + i),)`: such a column is found by
    // the first components of its tuples.
    let nested: std::collections::HashMap<usize, Type> = [64, 512]
        .into_iter()
        .map(|c| (c, nested_parity(c)))
        .collect();
    scaling::check(
        "listing an exclusive or of nested tuple types, by count",
        64,
        |c| {
            assert_eq!(nested[&c].each_value().map(|v| v.count()), Some(c));
        },
    );
    // Columns no one kind or length lists ([`listing_shape`], LIST-parity-rest): shapes 0, 1
    // and 2. Each tuple type is filed by its parts, as the class split does (K36); unfiled,
    // each was read for every value (60.3, 60.3 and 45.7 times the instructions from `c` 64 to
    // 512). In shapes 4 and 3 (LIST-parity-tail) each row was read for every tuple, and the
    // meet of the tuple types was made one by one along a path: from `c` 64 to 512, 50.1 times
    // the instructions and 30.4 times the bytes. Such a row is now filed by its second column,
    // and the meets along a path are made in balanced runs (`Type::boxes`): 9.4 and 9.7 times
    // the instructions.
    for (which, what, per) in [
        (
            0,
            "listing an exclusive or of integer-or-pair columns, by count",
            2,
        ),
        (
            1,
            "listing an exclusive or of columns of two tuple lengths, by count",
            2,
        ),
        (
            2,
            "listing a meet of tuple types given by their complements, by count",
            1,
        ),
        (
            4,
            "listing a meet of pairs with a complement first, by count",
            1,
        ),
        (
            3,
            "listing a meet of tuple types with a complement first in a pair, by count",
            1,
        ),
    ] {
        let built: std::collections::HashMap<usize, Type> = [64, 512]
            .into_iter()
            .map(|c| (c, listing_shape(c, which)))
            .collect();
        scaling::check(what, 64, |c| {
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(per * c));
        });
    }
    // Rows each with keys of their own in a column they could absorb ([`listing_regions`],
    // LIST-parity-tail). Absorbing every second column makes a region, and so a class reading
    // every row, per key: order `c²`, 27.5 times the bytes when it was tried. Such a column is
    // filed by its keys instead. Row `i` takes `x = 2i + 1` out of the first column, which
    // holds only `x = 1` of them, so `3c + 2` values are listed for `c > 1`.
    let regions: std::collections::HashMap<usize, Type> = [64, 512]
        .into_iter()
        .map(|c| (c, listing_regions(c)))
        .collect();
    let count = |c: usize| regions[&c].each_value().map(|v| v.count());
    // Each tuple was checked on the decision list restricted to the smallest range of halves
    // holding the rows with a key of it, and those rows, two per tuple, are in the order of
    // their hashes, so the range held most rows: 20.3 times the instructions from `c` 64 to
    // 512. The list is read from the blocks those rows change (LIST-parity-keys): 9.5 times,
    // under the limit of 10.5.
    scaling::compare(
        "listing a meet with tuple types of many keys each, by count: sizes 64 and 512",
        1,
        || assert_eq!(count(64), Some(3 * 64 + 2)),
        || assert_eq!(count(512), Some(3 * 512 + 2)),
    );
}

#[test]
fn listing_tuples_that_differ_off_their_first_components_scales() {
    // `((2i, i),)` for `i < c` met with each `((int - (2k + 1), x),)` for `k < c`. Each box of
    // the meet held the meet of all `c + 1` tuple types as a diagram of `c + 1` rows, order
    // `c²` to build and to list, and each tuple was a class of its own, reading every row:
    // from `c` 64 to 256, 16.5 times the instructions for `x` int and 0, and 17.3 times for
    // `x` int - (c + k) (LIST-parity-keys). One-row tuple types now meet column by column, and
    // the scalars there are read by their regions. The types are [`pairs_off_first`]; small
    // instance `a_few_tuples_that_differ_off_their_first_components_are_listed`.
    for (which, x) in ["all integers", "one literal", "a complement"]
        .into_iter()
        .enumerate()
    {
        let built = scaling::inputs(64, |c| pairs_off_first(c, which));
        let what = format!("listing pairs off their first components, the second {x}, by count");
        scaling::check(&what, 64, |c| {
            let want = if which == 1 { 1 } else { c };
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(want));
        });
    }
}

#[test]
fn a_decision_tree_is_decided_in_polynomial_time() {
    // Splitting the product on every row in turn made `3^c` pieces: 1.14 s at `c = 64` and
    // cubic from there once the split took a column whose cells are disjoint. Narrowing every
    // row on every column at each of the `c` splits was `O(c³)`, `N^1.5` in the `N ≈ 2c²`
    // components written: 2.1 s at `c = 128`. A split now tests again only the rows open on
    // the column it changed: `O(c²)`, linear in `N`.
    std::thread::Builder::new()
        .spawn(|| {
            let fresh = std::sync::atomic::AtomicUsize::new(1);
            scaling::check_order("a decision tree, by column count", 16, 2, |c| {
                let (p, rows) = decision_tree(c, 1000 * fresh.fetch_add(1, Relaxed));
                assert!(
                    (&p - &Type::union_all(rows)).is_empty(),
                    "the rows cover the product at c = {c}"
                );
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_key_past_many_excluded_tuples_is_found_and_scales() {
    // Each tuple type tried as the key's representative was tested against every other. Small
    // instance `a_key_past_a_few_excluded_tuples_is_found`.
    let promised = |c: usize| Type::exact(past_excluded(c, Type::int()), Type::empty());
    let built: std::collections::HashMap<usize, Type> =
        [512, 4096].into_iter().map(|c| (c, promised(c))).collect();
    scaling::check(
        "a key's representative past excluded tuple types, by count",
        512,
        |c| {
            Type::forget_emptiness();
            assert!(built[&c].is_empty());
        },
    );
}

#[test]
fn pinwheels_with_a_cofinite_scalar_end_beside_payload_ends_scale() {
    // The cofinite end lists the k - 1 integers of the other pinwheels' scalar ends, and each
    // of those is a finite cell of the integers beside it. When every finite cell of integers
    // joined a cofinite one, all k pinwheels fell in one class (COMPLEXITY K36, T6 repair 7); a
    // finite cell now joins it only when it holds an integer the cofinite one leaves out. The
    // atom ends are keyed by name and payload, apart from the integers. Inputs are built before
    // timing. Measured from k = 16 to 128, empty: 106M to 891M instructions (8.4 times); with
    // the old rule, 441M to 23,266M (52.8 times) and 46.4 times the bytes.
    std::thread::Builder::new()
        .spawn(|| {
            for (full, want, how) in [
                (true, Verdict::Empty, "empty"),
                (false, Verdict::Inhabited, "with a middle"),
            ] {
                let built: std::collections::HashMap<usize, Type> = [64, 512]
                    .into_iter()
                    .map(|k| (k, cofinite_scalar_pinwheels(k, full)))
                    .collect();
                scaling::check(
                    &format!("k pinwheels, a cofinite scalar end beside #e/#f ends, {how}, by k"),
                    64,
                    |k| {
                        Type::forget_emptiness();
                        assert_eq!(built[&k].verdict(), want);
                    },
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn payload_and_one_tuple_pinwheels_scale() {
    // Each value sought in a class of pinwheels was sought on a box holding half of all the
    // ends in the split component, and each test of a cell against it cost that half. Each
    // piece now holds only its own class. The union of the classes was built one class at a
    // time, which is quadratic in the nodes of the diagram: with one-tuple ends and a middle,
    // 25.1 times the work from k = 64 to 512. It is built by halves.
    std::thread::Builder::new()
        .spawn(|| {
            for end in [End::Payload, End::OneTuple] {
                scaling::check(
                    &format!("k pinwheels of {end:?} ends, empty, by k"),
                    64,
                    |k| {
                        Type::forget_emptiness();
                        assert_eq!(pinwheels(k, true, end).verdict(), Verdict::Empty);
                    },
                );
                scaling::check(
                    &format!("k pinwheels of {end:?} ends with a middle, by k"),
                    64,
                    |k| {
                        Type::forget_emptiness();
                        assert_eq!(pinwheels(k, false, end).verdict(), Verdict::Inhabited);
                    },
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pinwheels_whose_ends_repeat_an_integer_scale() {
    // With the two `b + 1` one shared type: 662M, 9,051M and 36,294M instructions at k = 16,
    // 64 and 128 for `#e((b + 1, b + 5))`; built apart, 145M, 598M and 1,235M.
    std::thread::Builder::new()
        .spawn(|| {
            for (pair, shared) in [(false, true), (true, true), (true, false)] {
                scaling::check(
                    &format!("k pinwheels repeating an integer, pair {pair}, shared {shared}, empty, by k"),
                    64,
                    |k| {
                        Type::forget_emptiness();
                        let t = repeating_pinwheels(k, true, pair, shared);
                        assert_eq!(t.verdict(), Verdict::Empty);
                    },
                );
            }
            scaling::check(
                "k pinwheels repeating an integer, shared, with a middle, by k",
                64,
                |k| {
                    Type::forget_emptiness();
                    let t = repeating_pinwheels(k, false, false, true);
                    assert_eq!(t.verdict(), Verdict::Inhabited);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pinwheels_with_an_end_outside_every_tuple_type_scale() {
    // An end outside every tuple type held every one-tuple, so all k pinwheels fell in one
    // class, and the checks below whose top is a meet cost order k^2: from k = 16 to 128,
    // 59.7 times the bytes allocated for the subtype checks and 49.5 times for the union
    // less a box, full. `overlaps` now places such an end at the first components it can
    // hold, which meet only its own pinwheel. COMPLEXITY.md K36.
    std::thread::Builder::new()
        .spawn(|| pinwheels_scale("one end outside", negated_ends, true))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pinwheels_whose_ends_share_a_first_component_scale() {
    // Ends that share a first component shared its key, so all k pinwheels fell in one
    // class: from k = 16 to 128, 57.9 times the bytes for the subtype checks and 47.3 times
    // for the union less a box, full. `overlaps` now refines the classes on each later
    // component. COMPLEXITY.md K36.
    std::thread::Builder::new()
        .spawn(|| pinwheels_scale("one first component", first_component_ends, false))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_union_of_disjoint_pinwheels_is_decided_piece_by_piece() {
    // The pinwheels are written as their squares less all their boxes (`squares_less_boxes`).
    // No component splits the boxes into disjoint pieces, so without the split into classes
    // each open tuple type is a piece decided against the whole part: from k = 64 to 512, 58.6
    // times the instructions empty, 57.9 times with the cofinite end, and 26.6 times the bytes
    // with a middle (negative control, run once, not committed: `classes` answering `None`).
    // Their cells on the first component fall into one class per pinwheel, sharing no integer,
    // and the halves of the classes are decided and searched apart: 8.8, 8.9 and 8.2 times
    // (limit 13.20, load about 35, 2026-11-12). The union of the pinwheels (`pinwheels`) is
    // decided one pinwheel at a time by the rule for unions of parts that share no tuple type
    // (K80) too: without the split it took 8.0 times empty and 7.1 times with a middle, from
    // k = 16 to 128, so it does not test the split.
    std::thread::Builder::new()
        .spawn(|| {
            let built = |cofinite: bool, full: bool| -> std::collections::HashMap<usize, Type> {
                scaling::inputs(64, |k| squares_less_boxes(full, &plain_ends(k, cofinite)))
            };
            let empty = built(false, true);
            scaling::check("k disjoint pinwheels, empty, by k", 64, |k| {
                Type::forget_emptiness();
                assert!(empty[&k].is_empty());
            });
            // A cofinite type lists the integers it leaves out. When any cofinite cell joined
            // its whole universe, all k pinwheels fell in one class: 62.6 times the work from
            // k = 64 to 512. A finite cell now joins it only when it holds an integer the
            // cofinite one does not leave out.
            let cofinite = built(true, true);
            scaling::check(
                "k disjoint pinwheels, one end cofinite, empty, by k",
                64,
                |k| {
                    Type::forget_emptiness();
                    assert!(cofinite[&k].is_empty());
                },
            );
            let open = built(false, false);
            scaling::check("k disjoint pinwheels with a middle, by k", 64, |k| {
                Type::forget_emptiness();
                assert!(!open[&k].is_empty());
                assert_eq!(open[&k].verdict(), Verdict::Inhabited);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_list_of_two_cycles_is_shown_in_the_size_of_its_type() {
    // The lists whose length is -1 modulo `n` and modulo `n + 1`: the shortest has `n * (n + 1)
    // - 1` links, and `2n + 1` definitions write the type. The list shown is kept as a length
    // the rule on residues picks, so the work is that of walking the two cycles, order `n`;
    // building the list link by link was order `n^2`.
    scaling::check("lengths -1 modulo n and n + 1, by n", 128, |n| {
        Type::forget_emptiness();
        let t = &period(n, n - 1) & &period(n + 1, n);
        assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
    });
}

#[test]
fn a_tuple_that_shapes_hold_only_together_is_checked_in_the_size_of_the_union() {
    // `g` takes `(#a_i, #c)` for each of `n` atoms, and `h` passes it `(#a_0 | … | #a_n-1,
    // #c)`, which no one shape holds: the checker builds each side's kernel type once and
    // the kernel decides it by splitting the first component. The program is
    // [`shapes_program`]; small instance `a_tuple_held_by_a_few_shapes_together_or_by_none`.
    let program = |n: usize| shapes_program(n, "#c");
    // The checker is timed alone, on statements parsed and resolved before the timing
    // (COMPLEXITY.md F85).
    let units: std::collections::BTreeMap<usize, _> = [64, scaling::FACTOR * 64]
        .into_iter()
        .map(|n| (n, zed_tests::deep::resolved(&program(n))))
        .collect();
    scaling::check("a tuple held by n shapes together, by n", 64, |n| {
        Type::forget_emptiness();
        let (stmts, res) = &units[&n];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_tuple_that_no_shapes_hold_is_rejected_in_the_size_of_the_union() {
    // As above, with `#d` for `#c`: the kernel shows a value outside every shape, so the
    // shapes are not each tried, which costs every shape times the components. Small instance,
    // with the error message: `a_tuple_held_by_a_few_shapes_together_or_by_none`.
    let program = |n: usize| shapes_program(n, "#d");
    scaling::check("a tuple held by no shape, by n", 64, |n| {
        Type::forget_emptiness();
        assert!(zedc::run::load(program(n).as_bytes()).is_err());
    });
}

#[test]
fn the_members_of_two_cycles_are_decided_in_the_size_of_their_types() {
    // Every member of a group is decided together, and each reads the cycle through the next
    // member: a cycle walked is kept for every type on it, so each group is walked once, order
    // `n`; walked again for each member, it was order `n^2` (VERDICT-group-readers).
    scaling::check(
        "the members of cycles of n and n + 1 definitions, by n",
        128,
        |n| {
            Type::forget_emptiness();
            let (a, b) = (period(n, n - 1), period(n + 1, n));
            assert_eq!(a.verdict(), Verdict::Inhabited);
            assert_eq!(b.verdict(), Verdict::Inhabited);
        },
    );
}

#[test]
fn the_verdict_of_a_meet_of_two_cycles_costs_what_its_emptiness_does() {
    // The meet of two cycles is decided by the rule on residues and reads no member's verdict
    // or value, so its verdict decides neither group and does the work `is_empty` does; at n
    // 1024, 13.1M instructions and 0.90M bytes against 13.1M and 0.90M. Deciding every member
    // of both groups first (VERDICT-group-readers) cost 87.5M and 10.5M, 6.7 and 11.7 times
    // the emptiness (plan item VERDICT-meet-cost). This is a comparison of two costs at one
    // size, not a scaling test: it runs no second size and checks no ratio between sizes. It
    // stays here as a measurement (TEST-bench-move-l0123, author P169); its answers have a small
    // instance in `small_lists_of_two_cycles_are_decided`.
    let n = 1024;
    let t = &period(n, n - 1) & &period(n + 1, n);
    scaling::compare_costs(
        "the verdict against the emptiness of the lists of lengths -1 modulo 1024 and 1025",
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

#[test]
fn finding_the_boxes_of_a_meet_with_an_exclusive_or_scales() {
    // `((u, 0),)`, `u = 0..w`, met with the exclusive or of `((int - (2k + 1), int),)` for
    // `k < n`, and the exclusive or of each of those met with `((u, 0),)` first: `n` rows and a
    // finite side of `w` values. Neither was known finite, since an expression gave each of its
    // tuple types as a box (LIST-xor-finite). Every `x < w` is in the `n` rows but the one of
    // `2k + 1 = x` when `x` is odd, so for `w ≤ 2n` the even `x` are listed when `n` is odd and
    // the odd ones when `n` is even. Built before timing.
    let one = |t: Type| Type::tuple(vec![t]);
    let xor = |x: Type, t: Type| &(&x - &t) | &(&t - &x);
    let family = |n: usize, w: usize, each: bool| -> Type {
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
    };
    let listed = |n: usize, w: usize| {
        if n.is_multiple_of(2) {
            w / 2
        } else {
            w.div_ceil(2)
        }
    };
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
    let met = scaling::inputs(128, |n| family(n, n, false));
    scaling::check(
        "finding the boxes of a finite type met with the exclusive or",
        128,
        |n| assert!(met[&n].finite()),
    );
    scaling::check(
        "listing a finite type met with the exclusive or",
        128,
        |n| {
            assert_eq!(met[&n].each_value().map(|v| v.count()), Some(listed(n, n)));
        },
    );
    let wide = scaling::inputs(128, |n| family(n, n, true));
    scaling::check(
        "finding the boxes of a finite type each row met first",
        128,
        |n| assert!(wide[&n].finite()),
    );
    scaling::check("listing a finite type each row met first", 128, |n| {
        assert_eq!(wide[&n].each_value().map(|v| v.count()), Some(listed(n, n)));
    });
    // The union of `n` exclusive ors `((3k | 3k + 1, 0),) ^ ((3k + 1 | 3k + 2, 0),)`, made one
    // at a time: a chain of `n` unions, whose boxes are kept as a union of persistent sets, and
    // whose listing reads the chain as one union. Each lists `3k` and `3k + 2`. Measured at
    // 128 and 1024: finding it finite 17.4M and 144M instructions, listing it 47M and 396M;
    // copying both sets at each union took 28M and 1.05G, and evaluating each union of the
    // chain again for each tuple 67M and 1.68G.
    let pair = |a: usize, b: usize| one(Type::tuple(vec![&lit(a) | &lit(b), lit(0)]));
    let chain = scaling::inputs(128, |n| {
        (0..n).fold(Type::empty(), |u, k| {
            &u | &xor(pair(3 * k, 3 * k + 1), pair(3 * k + 1, 3 * k + 2))
        })
    });
    scaling::check("finding the boxes of a chain of unions", 128, |n| {
        assert!(chain[&n].finite())
    });
    scaling::check("listing a chain of unions", 128, |n| {
        assert_eq!(chain[&n].each_value().map(|v| v.count()), Some(2 * n));
    });
}
