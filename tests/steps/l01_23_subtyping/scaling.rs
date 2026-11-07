//! The tuple and morphism parts at the rule of low complexity (DESIGN.md Part G). The union of
//! `C` differences `m(i) - m(i + 1000)` has a decision diagram of `2^C` nodes, since every
//! `m(i)` is ordered before every `m(i + 1000)`. A connective whose diagram would have more
//! nodes than its operands keeps its operands instead, so building the union and its
//! complement stay linear in `C`, and the queries on them are decided exactly: `b <: b | a` by
//! expanding on `b`, which both sides share, and `!b & a` by passing over paths whose taken
//! types are disjoint. A product of tuple types covered by many negated ones is split into disjoint pieces, and
//! a negated type disjoint from a piece is passed over.

use std::sync::Mutex;
use std::sync::atomic::Ordering::Relaxed;
use zed_kernel::Value;
use zed_kernel::types::{Type, Universe, Verdict};
use zed_tests::scaling;

fn lit(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).unwrap()
}

fn morphism(i: usize) -> Type {
    Type::morphism(Type::empty(), Type::top(), lit(i))
}

fn pair(i: usize) -> Type {
    Type::tuple(vec![lit(i), Type::top()])
}

/// The union of `c` differences of the atoms `atom` makes.
fn union(c: usize, atom: fn(usize) -> Type) -> Type {
    (0..c).fold(Type::empty(), |u, i| &u | &(&atom(i) - &atom(i + 1000)))
}

fn run(c: usize, atom: fn(usize) -> Type) {
    let b = union(c, atom);
    let n = !&b;
    assert!(!(&n & &atom(5000)).is_empty());
    assert!(b.subtype(&(&b | &atom(5000))));
}

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
fn small_unions_are_still_decided() {
    // The answers `the_parts_scale` times, at a count small enough that unions of diagrams
    // stay diagrams.
    for atom in [morphism as fn(usize) -> Type, pair] {
        let b = union(6, atom);
        assert!(b.subtype(&(&b | &atom(5000))), "{b}");
        assert!(!b.subtype(&atom(0)), "{b}");
        assert!((&b - &b).is_empty(), "{b}");
    }
}

/// The tuples `(i, b + j)` for `i, j < n`, as a product and as the union of its `n²` cells.
fn grid(n: usize, b: usize) -> (Type, Type) {
    let set = |b: usize| Type::union_all((0..n).map(|i| lit(b + i)));
    let cells = Type::union_all((0..n * n).map(|k| Type::tuple(vec![lit(k / n), lit(b + k % n)])));
    (Type::tuple(vec![set(0), set(b)]), cells)
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
fn a_cell_left_out_is_found() {
    for n in [2, 3, 5, 8] {
        let (p, cells) = grid(n, 0);
        let hole = Type::tuple(vec![lit(n / 2), lit(n - 1)]);
        let rest = &(&p - &cells) | &hole;
        assert!(!(&p - &(&cells - &hole)).is_empty(), "n = {n}");
        assert!((&rest - &hole).is_empty(), "n = {n}");
    }
}

#[test]
fn negated_types_disjoint_from_the_product_are_passed_over() {
    // The decoy `(bits(i), 1000 + i)`, with `bits(i)` the numbers below 8192 with bit `i` set,
    // misses `(0..8192, 0)` in the second component, and splitting on it would cut every piece
    // in two in the first: `2^13` pieces for the 13 decoys, unless a disjoint one is passed
    // over. The pieces are all met only when the answer is `true`, here once the two halves
    // of the product are reached.
    let set = |r: std::ops::Range<usize>| Type::union_all(r.map(lit));
    let bits = |i: usize| Type::union_all((0..8192).filter(|x| x >> i & 1 == 1).map(lit));
    let p = Type::tuple(vec![set(0..8192), lit(0)]);
    let halves =
        &Type::tuple(vec![set(0..4096), lit(0)]) | &Type::tuple(vec![set(4096..8192), lit(0)]);
    let decoys = Type::union_all((0..13).map(|i| Type::tuple(vec![bits(i), lit(1000 + i)])));
    assert!(!(&p - &decoys).is_empty());
    assert!((&p - &(&decoys | &halves)).is_empty());
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

/// The tuple `(… ((b, b), b + 1) …, b + d - 1)`, nested `d` deep.
fn nested(d: usize, b: usize) -> Type {
    (0..d).fold(lit(b), |t, i| Type::tuple(vec![t, lit(b + i)]))
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
fn a_type_built_on_another_thread_is_the_same_type() {
    // Each thread keeps its own table of nodes, so the two copies are distinct nodes, and are
    // equal by their contents.
    let here = &nested(20, 7) | &Type::morphism(Type::empty(), Type::top(), nested(5, 3));
    let there = std::thread::spawn(|| {
        &nested(20, 7) | &Type::morphism(Type::empty(), Type::top(), nested(5, 3))
    })
    .join()
    .unwrap();
    assert_eq!(here, there);
    assert_eq!(here.to_string(), there.to_string());
    assert!(here.subtype(&there) && there.subtype(&here));
    assert!(!here.subtype(&nested(20, 8)));
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
fn literal_and_atom_sets_combine_exactly() {
    // Every pair of signs and both connectives, with sets of unequal sizes in either order.
    let atom = |i: usize| Type::atom(&format!("a{i}"));
    let set = |r: std::ops::Range<usize>| {
        &Type::union_all(r.clone().map(lit)) | &Type::union_all(r.map(atom))
    };
    let (a, b) = (set(0..6), set(4..5));
    let both = &lit(4) | &atom(4);
    for (x, y) in [(&a, &b), (&b, &a)] {
        for (nx, ny) in [(false, false), (false, true), (true, false), (true, true)] {
            let x = if nx { !x } else { x.clone() };
            let y = if ny { !y } else { y.clone() };
            let (or, and) = (&x | &y, &x & &y);
            for v in (0..8).flat_map(|i| [lit(i), atom(i)]) {
                let (in_x, in_y) = (v.subtype(&x), v.subtype(&y));
                assert_eq!(v.subtype(&or), in_x || in_y, "{v} in {x} | {y}");
                assert_eq!(v.subtype(&and), in_x && in_y, "{v} in {x} & {y}");
            }
            assert_eq!(&(&or - &and) | &and, or);
        }
    }
    assert_eq!(&a & &b, both);
    assert_eq!(&(&a - &b) | &both, a);
}

/// The exclusive or of `types`, taken in order as `x = (x - t) | (t - x)`: the values in an odd
/// number of them.
fn parity(types: impl IntoIterator<Item = Type>) -> Type {
    types
        .into_iter()
        .fold(Type::empty(), |x, t| &(&x - &t) | &(&t - &x))
}

/// The exclusive or of the `c` tuple types `(b + i, b + i)`: a diagram of about `2c` nodes with
/// `2^(c - 1)` paths to `true`, holding `c` values.
fn odd_tuples(c: usize, b: usize) -> Type {
    parity((0..c).map(|i| Type::tuple(vec![lit(b + i), lit(b + i)])))
}

/// [`odd_tuples`] with its tuple types taken in the reverse order: the same set, built apart.
fn odd_tuples_reversed(c: usize, b: usize) -> Type {
    parity(
        (0..c)
            .rev()
            .map(|i| Type::tuple(vec![lit(b + i), lit(b + i)])),
    )
}

#[test]
fn exclusive_ors_of_none_one_and_more_tuple_types_are_compared_exactly() {
    // A set of switches, each a tuple type: a value is on when an odd number of the types
    // hold it. The parity of no type is empty and that of one is the type itself.
    let one = Type::tuple(vec![lit(0), lit(0)]);
    assert!(odd_tuples(0, 0).is_empty());
    assert!(odd_tuples(1, 0).equiv(&one));
    for c in [0, 1, 2, 7] {
        let (x, y) = (odd_tuples(c, 0), odd_tuples(c + 1, 0));
        // One more tuple type adds its one value: `x <: y` holds and `y <: x` does not.
        assert!(x.subtype(&y), "c = {c}");
        assert!(!y.subtype(&x), "c = {c}");
        assert!(!x.equiv(&y), "c = {c}");
        assert!(x.equiv(&odd_tuples_reversed(c, 0)), "c = {c}");
        assert_eq!(x.each_value().map(|v| v.count()), Some(c), "c = {c}");
    }
    // Tuple types of one column, overlapping: `(0 | 1)` and `(1 | 2)` share `(1)`, which is in
    // both and so in neither's parity; `(0 | 1) ^ (1 | 2) ^ (1)` holds all three values.
    let row = |vs: &[usize]| Type::tuple(vec![Type::union_all(vs.iter().map(|&v| lit(v)))]);
    let two = parity([row(&[0, 1]), row(&[1, 2])]);
    assert!(two.equiv(&(&row(&[0]) | &row(&[2]))));
    assert!(!two.equiv(&row(&[0, 1, 2])));
    assert!(parity([row(&[0, 1]), row(&[1, 2]), row(&[1])]).equiv(&row(&[0, 1, 2])));
    assert!(parity([row(&[0, 1]), row(&[0, 1])]).is_empty());
}

/// The `runs` inputs `make` builds for count `c` in case `k` of a test, each at a base no other
/// input uses, so that no run reads a result another kept.
fn pool<T>(c: usize, runs: usize, k: usize, make: impl Fn(usize, usize) -> T) -> Mutex<Vec<T>> {
    let base = |i: usize| 100_000_000 * k + 1_000_000 * (i + 1) + 1_000 * c;
    Mutex::new((0..runs).map(|i| make(c, base(i))).collect())
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
    // Listing walked every path of the diagram: `2^(c - 1)` at `c` tuple types.
    for c in [1, 2, 7] {
        assert_eq!(
            odd_tuples(c, 0).each_value().map(|v| v.count()),
            Some(c),
            "c = {c}"
        );
    }
    let built: std::collections::HashMap<usize, Type> = [64, 512]
        .into_iter()
        .map(|c| (c, odd_tuples(c, 0)))
        .collect();
    // A parity is an expression over the `c` tuple types, and checking each of the `c` values
    // on all of it was order `c²` (BDD-xor-parity measured 33 M and 2,088 M instructions at `c`
    // 64 and 512); a value is checked on the expression restricted to the tuple types that may
    // hold it, found by its components (LIST-parity-quad, COMPLEXITY.md K57).
    scaling::check(
        "listing an exclusive or of tuple types, by count",
        64,
        |c| {
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(c));
        },
    );
    // The same with each value one level down, `((b + i, b + i),)`: such a column is found by
    // the first components of its tuples.
    let nested: std::collections::HashMap<usize, Type> = [64, 512]
        .into_iter()
        .map(|c| {
            let row = |i: usize| Type::tuple(vec![Type::tuple(vec![lit(i), lit(i)])]);
            (c, parity((0..c).map(row)))
        })
        .collect();
    scaling::check(
        "listing an exclusive or of nested tuple types, by count",
        64,
        |c| {
            assert_eq!(nested[&c].each_value().map(|v| v.count()), Some(c));
        },
    );
    // Columns no one kind or length lists (LIST-parity-rest): `(i | (i, i))`, with tuples and
    // integers in one column; `((i) | (i, i))`, with tuples of two lengths; and `(0..2c)` met
    // with each `(int - (2i + 1))`, tuple types given by their complements. Each tuple type is
    // filed by its parts, as the class split does (K36); unfiled, each was read for every value
    // (60.3, 60.3 and 45.7 times the instructions from `c` 64 to 512).
    let shape = |c: usize, which: usize| -> Type {
        let row = |i: usize| -> Type {
            let pair = Type::tuple(vec![lit(i), lit(i)]);
            match which {
                0 => Type::tuple(vec![&lit(i) | &pair]),
                _ => Type::tuple(vec![&Type::tuple(vec![lit(i)]) | &pair]),
            }
        };
        if which < 2 {
            return parity((0..c).map(row));
        }
        // Shape 4 puts a second column beside each, `(0..2c, 0)` met with each `(int - (2i + 1),
        // 0)`, and shape 3 puts that pair one level down, `((0..2c, 0),)` met with each
        // `((int - (2i + 1), 0),)` (LIST-parity-tail). Each such row was read for every tuple,
        // and the meet of the tuple types was made one by one along a path: from `c` 64 to 512,
        // 50.1 times the instructions and 30.4 times the bytes. Such a row is now filed by its
        // second column, and the meets along a path are made in balanced runs (`Type::boxes`):
        // 9.4 and 9.7 times the instructions.
        let deeper = |t: Type| match which {
            2 => t,
            _ => Type::tuple(vec![t, lit(0)]),
        };
        let wrap = |t: Type| match which {
            4 => t,
            _ => Type::tuple(vec![t]),
        };
        let all = wrap(deeper(Type::union_all((0..2 * c).map(lit))));
        (0..c).fold(all, |t, i| {
            &t & &wrap(deeper(&Type::int() - &lit(2 * i + 1)))
        })
    };
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
            .map(|c| (c, shape(c, which)))
            .collect();
        for c in [1, 2, 7] {
            let small = shape(c, which).each_value().map(|v| v.count());
            assert_eq!(small, Some(per * c), "{what}, c = {c}");
        }
        scaling::check(what, 64, |c| {
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(per * c));
        });
    }
    // Rows each with keys of their own in a column they could absorb (LIST-parity-tail): `(0..3,
    // 0..=c)` met with the union of each `(int - (2i + 1), i | i + 1)`. Absorbing every second
    // column makes a region, and so a class reading every row, per key: order `c²`, 27.5 times
    // the bytes when it was tried. Such a column is filed by its keys instead.
    let regions: std::collections::HashMap<usize, Type> = [1, 2, 7, 64, 512]
        .into_iter()
        .map(|c| {
            let all = Type::tuple(vec![
                Type::union_all((0..3).map(lit)),
                Type::union_all((0..=c).map(lit)),
            ]);
            let row =
                |i: usize| Type::tuple(vec![&Type::int() - &lit(2 * i + 1), &lit(i) | &lit(i + 1)]);
            (c, &all & &Type::union_all((0..c).map(row)))
        })
        .collect();
    // Row `i` takes `x = 2i + 1` out of the first column, which holds only `x = 1` of them:
    // `y = 0` keeps 2 values and every other `y` 3, but at `c = 1`, where `y = 1` keeps 2.
    let count = |c: usize| regions[&c].each_value().map(|v| v.count());
    for (c, n) in [(1, 4), (2, 8), (7, 23)] {
        assert_eq!(count(c), Some(n), "c = {c}");
    }
    // Each tuple was checked on the decision list restricted to the smallest range of halves
    // holding the rows with a key of it, and those rows, two per tuple, are in the order of
    // their hashes, so the range held most rows: 20.3 times the instructions from `c` 64 to
    // 512. The list is read from the blocks those rows change (LIST-parity-keys): 9.5 times,
    // under the 8 log 512 / log 64 = 12 times of order `c log c`.
    scaling::compare(
        "listing a meet with tuple types of many keys each, by count: sizes 64 and 512",
        "for work of order c log c, 8 log 512 / log 64 = 12 times",
        12.0,
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
    // the scalars there are read by their regions.
    let pairs = |c: usize, which: usize| -> Type {
        let firsts = (0..c).map(|i| Type::tuple(vec![Type::tuple(vec![lit(2 * i), lit(i)])]));
        let x = |k: usize| match which {
            0 => Type::int(),
            1 => lit(0),
            _ => &Type::int() - &lit(c + k),
        };
        (0..c).fold(Type::union_all(firsts), |t, k| {
            &t & &Type::tuple(vec![Type::tuple(vec![
                &Type::int() - &lit(2 * k + 1),
                x(k),
            ])])
        })
    };
    for (which, x) in ["all integers", "one literal", "a complement"]
        .into_iter()
        .enumerate()
    {
        let built = scaling::inputs(64, |c| pairs(c, which));
        let what = format!("listing pairs off their first components, the second {x}, by count");
        scaling::check(&what, 64, |c| {
            let want = if which == 1 { 1 } else { c };
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(want));
        });
    }
}

/// The rows of a decision tree on `c` columns of `{b, b + 1, b + 2}`: on column `i`, after
/// `b + 2` in every column before it, `b` and `b + 1` each end a row and `b + 2` goes on; on
/// the last column `b + 2` ends a row too. The rows cover the product of the columns.
fn decision_tree(c: usize, b: usize) -> (Type, Vec<Type>) {
    let column = Type::union_all((b..b + 3).map(lit));
    let row = |i: usize, v: usize| {
        Type::tuple(
            (0..c)
                .map(|j| match j.cmp(&i) {
                    std::cmp::Ordering::Less => lit(b + 2),
                    std::cmp::Ordering::Equal => lit(v),
                    std::cmp::Ordering::Greater => column.clone(),
                })
                .collect(),
        )
    };
    let mut rows: Vec<Type> = (0..c).flat_map(|i| [row(i, b), row(i, b + 1)]).collect();
    rows.push(row(c - 1, b + 2));
    (Type::tuple(vec![column.clone(); c]), rows)
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
fn a_row_left_out_of_a_decision_tree_is_found() {
    for c in [1, 2, 5, 16] {
        let (p, rows) = decision_tree(c, 0);
        assert!(
            (&p - &Type::union_all(rows.iter().cloned())).is_empty(),
            "c = {c}"
        );
        for i in 0..rows.len() {
            let mut less = rows.clone();
            less.remove(i);
            assert!(
                !(&p - &Type::union_all(less)).is_empty(),
                "c = {c}, row {i} left out"
            );
        }
    }
}

/// A type the check does not prove empty may still be empty, so it promises no key: here
/// four pigeons in three holes, a Boolean tuple type that no valuation of its 4096 is in.
#[test]
fn a_type_not_proved_empty_promises_no_key() {
    let (pigeons, holes) = (4, 3);
    let d = pigeons * holes;
    let bit = Type::bool();
    let mut forbidden = Vec::new();
    let row = |hit: &dyn Fn(usize) -> bool, b: bool| {
        let lit = Type::lit(&Value::Bool(b)).unwrap();
        Type::tuple(
            (0..d)
                .map(|j| if hit(j) { lit.clone() } else { bit.clone() })
                .collect(),
        )
    };
    for p in 0..pigeons {
        forbidden.push(row(&|j| j / holes == p, false));
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                forbidden.push(row(&|j| j == p * holes + h || j == q * holes + h, true));
            }
        }
    }
    let unknown = &Type::tuple(vec![bit; d]) - &Type::union_all(forbidden);
    for mask in 0..1usize << d {
        let v = Value::Tuple((0..d).map(|j| Value::Bool(mask >> j & 1 != 0)).collect());
        assert!(
            !unknown.contains(&v),
            "a valuation is in the pigeonhole type"
        );
    }
    assert!(
        !unknown.is_empty(),
        "the check proves the pigeonhole type empty"
    );
    let m = Type::morphism(unknown, Type::empty(), Type::int());
    assert!(!m.is_empty(), "the empty morphism is in it");
    // A key shown in the type is promised: a scalar, a tuple, an atom's payload.
    let pair = Type::tuple(vec![Type::int(), Type::string()]);
    let tagged = Type::atom_with("p", &pair);
    for key in [Type::bool(), pair, tagged] {
        assert!(Type::morphism(key.clone(), Type::empty(), Type::int()).is_empty());
        assert!(Type::exact(key, Type::empty()).is_empty());
    }
}

/// The one-tuples of `ints` but `0` to `c - 1`, each taken out as its own tuple type.
fn past_excluded(c: usize, ints: Type) -> Type {
    &Type::tuple(vec![ints]) - &Type::union_all((0..c).map(|i| Type::tuple(vec![lit(i)])))
}

#[test]
fn a_key_past_many_excluded_tuples_is_found_and_scales() {
    // Each tuple type tried as the key's representative was tested against every other.
    let promised = |c: usize| Type::exact(past_excluded(c, Type::int()), Type::empty());
    for c in [1, 2, 7] {
        assert!(promised(c).is_empty(), "c = {c}");
        // When every one-tuple is taken out, no key is promised, and the empty morphism is in it.
        let all = Type::union_all((0..c).map(lit));
        assert!(
            !Type::exact(past_excluded(c, all), Type::empty()).is_empty(),
            "c = {c}"
        );
    }
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
/// The pinwheel on `ends`: the square of them less four boxes around its middle
/// `(ends[1], ends[1])`, and less the middle too when `full`, which makes it empty.
fn pinwheel(full: bool, ends: [Type; 3]) -> Type {
    let set = |m: u8| Type::union_all((0..3).filter(|i| m >> i & 1 == 1).map(|i| ends[i].clone()));
    let boxes: &[[u8; 2]] = match full {
        false => &[[3, 1], [4, 3], [6, 4], [1, 6]],
        true => &[[3, 1], [4, 3], [6, 4], [1, 6], [2, 2]],
    };
    let square = Type::tuple(vec![set(7); 2]);
    &square
        - &Type::union_all(
            boxes
                .iter()
                .map(|b| Type::tuple(b.iter().map(|&m| set(m)).collect())),
        )
}

fn lit_i(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

/// What the ends of a pinwheel are: the integer `i` itself, the atom `#e((i,))` or the
/// one-tuple `(i,)`.
#[derive(Clone, Copy, Debug)]
enum End {
    Plain,
    Payload,
    OneTuple,
}

impl End {
    const ALL: [End; 3] = [End::Plain, End::Payload, End::OneTuple];

    /// The end made of `t`, a type of integers.
    fn of(self, t: Type) -> Type {
        match self {
            End::Plain => t,
            End::Payload => Type::atom_with("e", &Type::tuple(vec![t])),
            End::OneTuple => Type::tuple(vec![t]),
        }
    }

    fn ends(self, b: i64) -> [Type; 3] {
        [1, 2, 3].map(|j| self.of(lit_i(b + j)))
    }
}

/// The union of `k` pinwheels on disjoint integers, with ends of kind `end`.
fn pinwheels(k: usize, full: bool, end: End) -> Type {
    Type::union_all((0..k as i64).map(|i| pinwheel(full, end.ends(10 * i))))
}

/// [`pinwheels`] with the third end of the last pinwheel cofinite: made of its own integer and
/// every integer no pinwheel uses.
fn cofinite_pinwheels(k: usize, full: bool, end: End) -> Type {
    let k = k as i64;
    let used = Type::union_all((0..k).flat_map(|i| (1..=3).map(move |j| lit_i(10 * i + j))));
    let [a, b, _] = end.ends(10 * (k - 1));
    let third = end.of(&(&Type::int() - &used) | &lit_i(10 * (k - 1) + 3));
    let others = (0..k - 1).map(|i| pinwheel(full, end.ends(10 * i)));
    Type::union_all(others.chain([pinwheel(full, [a, b, third])]))
}

/// The pinwheel on `ends` as the model writes it: the union of the pairs of ends that no box
/// holds. The ends are disjoint, so this is the pinwheel exactly.
fn pinwheel_model(full: bool, ends: &[Type; 3]) -> Type {
    let boxes: &[[u8; 2]] = match full {
        false => &[[3, 1], [4, 3], [6, 4], [1, 6]],
        true => &[[3, 1], [4, 3], [6, 4], [1, 6], [2, 2]],
    };
    let pairs = (0..3).flat_map(|a| (0..3).map(move |b| (a, b)));
    let kept = pairs.filter(|&(a, b)| {
        !boxes
            .iter()
            .any(|m| m[0] >> a & 1 == 1 && m[1] >> b & 1 == 1)
    });
    Type::union_all(kept.map(|(a, b)| Type::tuple(vec![ends[a].clone(), ends[b].clone()])))
}

/// The value of the end of kind `end` made of the integer `i`.
fn end_value(end: End, i: i64) -> Value {
    let one = Value::Tuple(vec![Value::Int(i)].into_iter().collect());
    match end {
        End::Plain => Value::Int(i),
        End::OneTuple => one,
        End::Payload => Value::atom_with("e", vec![Value::Int(i)]),
    }
}

/// Checks the union of the pinwheels on `ends` against the model, `full` and not.
fn check_against_model(what: &str, ends: &[[Type; 3]]) {
    for full in [true, false] {
        let t = Type::union_all(ends.iter().map(|e| pinwheel(full, e.clone())));
        let model = Type::union_all(ends.iter().map(|e| pinwheel_model(full, e)));
        let want = match full || ends.is_empty() {
            true => Verdict::Empty,
            false => Verdict::Inhabited,
        };
        assert_eq!(t.verdict(), want, "{what}, full = {full}");
        assert_eq!(
            t.is_empty(),
            want == Verdict::Empty,
            "{what}, full = {full}"
        );
        assert!(t.equiv(&model), "{what}, full = {full}");
    }
}

#[test]
fn pinwheels_of_payload_and_one_tuple_ends_agree_with_the_model() {
    // An empty union of pinwheels whose ends are atom payloads or one-tuples was refused: the
    // settled form of a tuple part, which may hold more than the part, was read as showing a
    // tuple in it, and all atoms of one name and all tuples of one length fell in one class.
    for end in End::ALL {
        for k in [0, 1, 2, 3, 5] {
            let ends: Vec<[Type; 3]> = (0..k).map(|i| end.ends(10 * i)).collect();
            check_against_model(&format!("{end:?}, k = {k}"), &ends);
            let middles = Type::union_all((0..k).map(|i| {
                let m = end.of(lit_i(10 * i + 2));
                Type::tuple(vec![m.clone(), m])
            }));
            let (full, open) = (
                pinwheels(k as usize, true, end),
                pinwheels(k as usize, false, end),
            );
            assert!((&open - &full).equiv(&middles), "{end:?}, k = {k}");
            // Each pair of ends, of any two pinwheels, is in the open union exactly when the
            // model keeps it: only the middles of the full union are taken out.
            let ints = (0..k).flat_map(|i| (1..=3).map(move |j| 10 * i + j));
            for a in ints.clone() {
                for b in ints.clone() {
                    let v =
                        Value::Tuple([end_value(end, a), end_value(end, b)].into_iter().collect());
                    let same = a / 10 == b / 10;
                    let (x, y) = ((a % 10 - 1) as u8, (b % 10 - 1) as u8);
                    let boxed = [[3u8, 1], [4, 3], [6, 4], [1, 6]]
                        .iter()
                        .any(|m| m[0] >> x & 1 == 1 && m[1] >> y & 1 == 1);
                    let want = same && !boxed;
                    assert_eq!(open.contains(&v), want, "{end:?}, k = {k}, ({a}, {b})");
                    assert!(!full.contains(&v), "{end:?}, k = {k}, ({a}, {b})");
                }
            }
        }
    }
}

#[test]
fn pinwheels_of_nested_payloads_and_cofinite_ends_are_decided() {
    // A payload of a payload: `#e((#e((i,)),))`.
    let nested = |b: i64| [1, 2, 3].map(|j| End::Payload.of(End::Payload.of(lit_i(b + j))));
    for k in [0, 1, 3] {
        let ends: Vec<[Type; 3]> = (0..k).map(|i| nested(10 * i)).collect();
        check_against_model(&format!("nested payloads, k = {k}"), &ends);
    }
    // Ends of different kinds in one union, each pinwheel of one kind.
    let mixed: Vec<[Type; 3]> = (0..6)
        .map(|i| End::ALL[i % 3].ends(10 * i as i64))
        .collect();
    check_against_model("mixed kinds", &mixed);
    // One pinwheel whose ends are of different kinds.
    check_against_model(
        "kinds within a pinwheel",
        &[[
            End::Plain.of(lit_i(1)),
            End::Payload.of(lit_i(2)),
            End::OneTuple.of(lit_i(3)),
        ]],
    );
    // The cofinite end with payload and one-tuple ends.
    for end in End::ALL {
        for k in [1, 2, 4] {
            let full = cofinite_pinwheels(k, true, end);
            let open = cofinite_pinwheels(k, false, end);
            assert_eq!(full.verdict(), Verdict::Empty, "{end:?}, k = {k}");
            assert_eq!(open.verdict(), Verdict::Inhabited, "{end:?}, k = {k}");
            let middles = Type::union_all((0..k as i64).map(|i| {
                let m = end.of(lit_i(10 * i + 2));
                Type::tuple(vec![m.clone(), m])
            }));
            assert!((&open - &full).equiv(&middles), "{end:?}, k = {k}");
        }
    }
}

/// The ends of `k` pinwheels whose first two ends are the atoms `#e((b + 1,))` and
/// `#f((b + 2,))` and whose third end is the integer `b + 3`, with the third end of the last
/// pinwheel cofinite: its own integer and every integer no pinwheel uses.
fn cofinite_scalar_ends(k: usize) -> Vec<[Type; 3]> {
    let k = k as i64;
    let scalar = |i: i64| lit_i(10 * i + 3);
    let used = Type::union_all((0..k).map(scalar));
    (0..k)
        .map(|i| {
            let b = 10 * i;
            let third = match i == k - 1 {
                true => &(&Type::int() - &used) | &scalar(i),
                false => scalar(i),
            };
            [
                Type::atom_with("e", &Type::tuple(vec![lit_i(b + 1)])),
                Type::atom_with("f", &Type::tuple(vec![lit_i(b + 2)])),
                third,
            ]
        })
        .collect()
}

/// The union of the pinwheels on [`cofinite_scalar_ends`].
fn cofinite_scalar_pinwheels(k: usize, full: bool) -> Type {
    Type::union_all(
        cofinite_scalar_ends(k)
            .into_iter()
            .map(|e| pinwheel(full, e)),
    )
}

#[test]
fn pinwheels_with_a_cofinite_scalar_end_beside_payload_ends_agree_with_the_model() {
    for k in [1, 2, 3, 5] {
        check_against_model(
            &format!("a cofinite scalar end beside payload ends, k = {k}"),
            &cofinite_scalar_ends(k),
        );
    }
    // The open union holds each middle `(#f((b + 2,)), #f((b + 2,)))` and no pair of the
    // cofinite end, whose integers no box leaves out.
    let open = cofinite_scalar_pinwheels(3, false);
    let pair = |x: Value, y: Value| Value::Tuple([x, y].into_iter().collect());
    let f = |i: i64| Value::atom_with("f", vec![Value::Int(i)]);
    for b in [0, 10, 20] {
        assert!(open.contains(&pair(f(b + 2), f(b + 2))), "b = {b}");
    }
    assert!(!open.contains(&pair(Value::Int(1000), Value::Int(1000))));
    assert!(!open.contains(&pair(Value::Int(23), f(22))));
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

/// Ends that repeat the integer `b + 1` under a one-tuple and an atom payload: `(b + 1,)`, then
/// `#e((b + 1, b + 5))` when `pair` and `#e((b + 1,))` when not, then `(b + 3,)`. When `shared`
/// the two `b + 1` are one type, and when not two equal ones built apart.
fn repeating_ends(b: i64, pair: bool, shared: bool) -> [Type; 3] {
    let first = lit_i(b + 1);
    let again = match shared {
        true => first.clone(),
        false => lit_i(b + 1),
    };
    let payload = match pair {
        true => vec![again, lit_i(b + 5)],
        false => vec![again],
    };
    [
        Type::tuple(vec![first]),
        Type::atom_with("e", &Type::tuple(payload)),
        End::OneTuple.of(lit_i(b + 3)),
    ]
}

/// The union of `k` pinwheels on [`repeating_ends`].
fn repeating_pinwheels(k: usize, full: bool, pair: bool, shared: bool) -> Type {
    Type::union_all((0..k as i64).map(|i| pinwheel(full, repeating_ends(10 * i, pair, shared))))
}

#[test]
fn pinwheels_whose_ends_repeat_an_integer_agree_with_the_model() {
    // A type met twice inside a cell, the `b + 1` of `(b + 1,)` and of `#e((b + 1,))`, held
    // every value under the node of the second meeting when the two were one shared type, so
    // all pinwheels fell in one class; two equal types built apart were walked apart. The two
    // nodes are now merged, whichever way the type was built.
    for pair in [false, true] {
        for shared in [false, true] {
            for k in [0, 1, 2, 3, 5] {
                let ends: Vec<[Type; 3]> = (0..k)
                    .map(|i| repeating_ends(10 * i, pair, shared))
                    .collect();
                check_against_model(&format!("pair {pair}, shared {shared}, k = {k}"), &ends);
            }
        }
    }
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

/// The ends of `k` pinwheels of one-tuple ends, with the third end of the last one every tuple
/// but the other ends: a tuple type outside any other, which holds every one-tuple outside them.
fn negated_ends(k: usize) -> Vec<[Type; 3]> {
    let mut ends: Vec<[Type; 3]> = (0..k as i64).map(|i| End::OneTuple.ends(10 * i)).collect();
    let n = ends.len() * 3;
    let others = Type::union_all(ends.iter().flatten().take(n.saturating_sub(1)).cloned());
    if let Some(last) = ends.last_mut() {
        last[2] = &Type::universe(Universe::Tuple) - &others;
    }
    ends
}

/// The ends of `k` pinwheels whose ends are pairs with one first component, `(0, b + j)`.
fn first_component_ends(k: usize) -> Vec<[Type; 3]> {
    let end = |b: i64| [1, 2, 3].map(|j| Type::tuple(vec![lit_i(0), lit_i(b + j)]));
    (0..k as i64).map(|i| end(10 * i)).collect()
}

#[test]
fn pinwheels_whose_ends_share_a_first_component_are_decided() {
    // The tradeoff at `overlaps`: tuples are keyed by their first component, so all the ends
    // `(0, b + j)` are in one class and the pinwheels are decided together.
    for k in [1, 2, 4] {
        check_against_model(
            &format!("one first component, k = {k}"),
            &first_component_ends(k),
        );
    }
}

#[test]
fn pinwheels_with_an_end_outside_every_tuple_type_are_decided() {
    for k in [1, 2, 4] {
        check_against_model(&format!("an end outside, k = {k}"), &negated_ends(k));
    }
}

#[test]
fn pinwheels_joined_in_one_class_are_decided_at_quadratic_cost() {
    // The tradeoff at `overlaps`: an end outside every tuple type holds every one-tuple, and
    // ends that share a first component share its key, so all k pinwheels fall in one class
    // and are decided together. Measured for the empty unions, order k^2: one end outside,
    // 1,478M, 19,555M and 78,974M instructions at k = 16, 64 and 128 (with middles 63M, 391M
    // and 803M); one first component, 1,170M, 15,893M and 62,927M. COMPLEXITY.md K36. The
    // family of one first component is the test below, so each test runs under 30 s.
    std::thread::Builder::new()
        .spawn(|| {
            scaling::check_order("k pinwheels, one end outside, empty, by k", 8, 2, |k| {
                Type::forget_emptiness();
                let t = Type::union_all(negated_ends(k).into_iter().map(|e| pinwheel(true, e)));
                assert_eq!(t.verdict(), Verdict::Empty);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pinwheels_sharing_a_first_component_are_decided_at_quadratic_cost() {
    // As above, for the family of one first component.
    std::thread::Builder::new()
        .spawn(|| {
            scaling::check_order("k pinwheels, one first component, empty, by k", 8, 2, |k| {
                Type::forget_emptiness();
                let ends = first_component_ends(k).into_iter();
                let t = Type::union_all(ends.map(|e| pinwheel(true, e)));
                assert_eq!(t.verdict(), Verdict::Empty);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_union_of_disjoint_pinwheels_is_decided_piece_by_piece() {
    // No component splits the pinwheels' boxes into disjoint pieces, so each was decided, and
    // its value sought, against the whole union: 27.7 times the work from k = 16 to 128. Their
    // cells on the first component fall into one class per pinwheel, sharing no integer, and
    // the halves of the classes are decided and searched apart.
    std::thread::Builder::new()
        .spawn(|| {
            scaling::check("k disjoint pinwheels, empty, by k", 64, |k| {
                Type::forget_emptiness();
                assert!(pinwheels(k, true, End::Plain).is_empty());
            });
            // A cofinite type lists the integers it leaves out. When any cofinite cell joined
            // its whole universe, all k pinwheels fell in one class: 62.6 times the work from
            // k = 64 to 512. A finite cell now joins it only when it holds an integer the
            // cofinite one does not leave out.
            scaling::check(
                "k disjoint pinwheels, one end cofinite, empty, by k",
                64,
                |k| {
                    Type::forget_emptiness();
                    assert!(cofinite_pinwheels(k, true, End::Plain).is_empty());
                },
            );
            scaling::check("k disjoint pinwheels with a middle, by k", 64, |k| {
                Type::forget_emptiness();
                let t = pinwheels(k, false, End::Plain);
                assert!(!t.is_empty());
                assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_union_of_disjoint_pinwheels_is_decided() {
    for k in [1, 2, 3, 5] {
        let (full, open) = (
            pinwheels(k, true, End::Plain),
            pinwheels(k, false, End::Plain),
        );
        assert_eq!(full.verdict(), zed_kernel::types::Verdict::Empty, "k = {k}");
        assert_eq!(
            open.verdict(),
            zed_kernel::types::Verdict::Inhabited,
            "k = {k}"
        );
        // The middles are the values of the union outside the full one.
        let middles =
            Type::union_all((0..k).map(|i| Type::tuple(vec![lit_i(10 * i as i64 + 2); 2])));
        assert!((&open - &full).equiv(&middles), "k = {k}");
        assert!(
            middles.subtype(&open) && (&middles & &full).is_empty(),
            "k = {k}"
        );
        assert!(full.subtype(&open) && !open.subtype(&full), "k = {k}");
    }
}

/// The lists of integers whose length is `k` modulo `p`.
fn period(p: usize, k: usize) -> Type {
    use zed_kernel::types::rec::{Def, Expr, Group};
    let defs = (0..p)
        .map(|i| {
            let cons = Expr::Atom(
                "cons".into(),
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            let body = match i == k {
                true => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                false => cons,
            };
            Def {
                name: format!("P{i}"),
                params: vec![],
                body,
            }
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![]).remove(0)
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
    // the kernel decides it by splitting the first component.
    let program = |n: usize| {
        let atoms: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
        let shapes: Vec<String> = atoms.iter().map(|a| format!("({a}, #c)")).collect();
        format!(
            "g(x: {}) = x;\nh(y: ({}, #c)) = g(x: y);\nmain() = 0;\n",
            shapes.join(" | "),
            atoms.join(" | ")
        )
    };
    // The checker is timed alone, on statements parsed and resolved before the timing
    // (COMPLEXITY.md F85).
    let units: std::collections::BTreeMap<usize, _> = [64, scaling::FACTOR * 64]
        .into_iter()
        .map(|n| (n, zed_tests::deep::resolved(&program(n))))
        .collect();
    scaling::check("a tuple held by n shapes together, by n", 64, |n| {
        Type::forget_emptiness();
        let (stmts, res) = &units[&n];
        let info = zedc::check::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_tuple_that_no_shapes_hold_is_rejected_in_the_size_of_the_union() {
    // As above, with `#d` for `#c`: the kernel shows a value outside every shape, so the
    // shapes are not each tried, which costs every shape times the components.
    let program = |n: usize| {
        let atoms: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
        let shapes: Vec<String> = atoms.iter().map(|a| format!("({a}, #c)")).collect();
        format!(
            "g(x: {}) = x;\nh(y: ({}, #d)) = g(x: y);\nmain() = 0;\n",
            shapes.join(" | "),
            atoms.join(" | ")
        )
    };
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

/// Every member of the group of [`period`]: member `i` holds the lists whose length is
/// `k - i` modulo `p`.
fn periods(p: usize, k: usize) -> Vec<Type> {
    use zed_kernel::types::rec::{Def, Expr, Group};
    let defs = (0..p)
        .map(|i| {
            let cons = Expr::Atom(
                "cons".into(),
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            let body = match i == k {
                true => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                false => cons,
            };
            Def {
                name: format!("P{i}"),
                params: vec![],
                body,
            }
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![])
}

#[test]
fn a_cycle_kept_for_each_type_on_it_gives_each_its_own_lengths() {
    // In one search, the meet `P_0 & Q_0` walks both cycles and keeps them for every type on
    // them; the meet `P_i & Q_j` beside it then reads the kept cycles of the types after
    // `P_i` and `Q_j`, whose stops are nearer. A meet is inhabited exactly when some length is
    // `k - i` modulo `p` and `r - j` modulo `q`.
    let meets = |p: usize, k: usize, i: usize, q: usize, r: usize, j: usize| {
        (0..p * q).any(|l| (l + i) % p == k && (l + j) % q == r)
    };
    for p in 2..=5 {
        for q in 2..=5 {
            for (k, r) in (0..p).flat_map(|k| (0..q).map(move |r| (k, r))) {
                let (ps, qs) = (periods(p, k), periods(q, r));
                for (i, j) in (0..p).flat_map(|i| (0..q).map(move |j| (i, j))) {
                    Type::forget_emptiness();
                    let t = Type::tuple(vec![&ps[0] & &qs[0], &ps[i] & &qs[j]]);
                    let want = match meets(p, k, 0, q, r, 0) && meets(p, k, i, q, r, j) {
                        true => Verdict::Inhabited,
                        false => Verdict::Empty,
                    };
                    assert_eq!(t.verdict(), want, "p {p} k {k} i {i}, q {q} r {r} j {j}");
                }
            }
        }
    }
}

#[test]
fn the_verdict_of_a_meet_of_two_cycles_costs_what_its_emptiness_does() {
    // The meet of two cycles is decided by the rule on residues and reads no member's verdict
    // or value, so its verdict decides neither group and does the work `is_empty` does; at n
    // 1024, 13.1M instructions and 0.90M bytes against 13.1M and 0.90M. Deciding every member
    // of both groups first (VERDICT-group-readers) cost 87.5M and 10.5M, 6.7 and 11.7 times
    // the emptiness (plan item VERDICT-meet-cost).
    let n = 1024;
    let t = &period(n, n - 1) & &period(n + 1, n);
    scaling::compare(
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
    // `((u, 0),)`, `u = 0..n`, met with the exclusive or of `((int - (2k + 1), int),)` for
    // `k < n`, and the exclusive or of each of those met with `((u, 0),)` first: `n` rows and a
    // finite side of `n` values. Neither was known finite, since an expression gave each of its
    // tuple types as a box (LIST-xor-finite). Every `x < n` is in the `n` rows but the one of
    // `2k + 1 = x` when `x` is odd, so the even `x` are listed when `n` is odd and the odd ones
    // when `n` is even: `ceil(n / 2)` values. Built before timing.
    let one = |t: Type| Type::tuple(vec![t]);
    let family = |n: usize, each: bool| -> Type {
        let side = one(Type::tuple(vec![Type::union_all((0..n).map(lit)), lit(0)]));
        let rows = (0..n).map(|k| {
            one(Type::tuple(vec![
                &Type::int() - &lit(2 * k + 1),
                Type::int(),
            ]))
        });
        let xor = |x: Type, t: Type| &(&x - &t) | &(&t - &x);
        if each {
            rows.fold(Type::empty(), |x, r| xor(x, &side & &r))
        } else {
            &side & &rows.fold(Type::empty(), xor)
        }
    };
    let met = scaling::inputs(64, |n| family(n, false));
    scaling::check(
        "finding the boxes of a finite type met with the exclusive or",
        64,
        |n| assert!(met[&n].finite()),
    );
    // The second makes `n` boxes, each the side met with one row, and reads each made type for
    // its finiteness; `Type::finite` of one tuple type of `n` literals costs order `n^0.6`
    // already at the base commit (43K and 151K instructions at 64 and 512 literals), so it is
    // bounded here by `n²`: measured 17.9M and 490M instructions at 64 and 512, 27 times. The
    // listing of the first is order `n²`: `RowIndex::holds` reads the `n` rows of the exclusive
    // or for each of the `n` candidates, each held by all rows but at most one; measured 9.4M,
    // 25M, 71M, 209M, 674M and 2.5G instructions at 32 to 1024 rows, each doubling 2.7 to 3.7
    // times. The listing of the second is a union of `n / 2` overlapping boxes of `n`
    // values each, so it reads order `n²` candidates against `n` rows, order `n³`, and is not
    // timed (open, item LIST-xor-finite in STATUS.md).
    let each = scaling::inputs(64, |n| family(n, true));
    scaling::check_order(
        "finding the boxes of a finite type each row met first",
        64,
        2,
        |n| assert!(each[&n].finite()),
    );
    scaling::check_order(
        "listing a finite type met with the exclusive or",
        64,
        2,
        |n| {
            assert_eq!(met[&n].each_value().map(|v| v.count()), Some(n.div_ceil(2)));
        },
    );
}
