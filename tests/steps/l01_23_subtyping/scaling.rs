//! The tuple and morphism parts at the rule of low complexity (DESIGN.md Part G). The union of
//! `C` differences `m(i) - m(i + 1000)` has a decision diagram of `2^C` nodes, since every
//! `m(i)` is ordered before every `m(i + 1000)`. A connective whose diagram would have more
//! nodes than its operands keeps its operands instead, so building the union and its
//! complement stay linear in `C`, and the queries on them are decided exactly: `b <: b | a` by
//! expanding on `b`, which both sides share, and `!b & a` by passing over paths whose taken
//! types are disjoint. A product of tuple types covered by many negated ones is split into disjoint pieces, and
//! a negated type disjoint from a piece is passed over.

use zed_kernel::Value;
use zed_kernel::types::Type;
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
        .stack_size(1 << 28)
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
        .stack_size(1 << 28)
        .spawn(|| {
            let fresh = std::cell::Cell::new(1);
            scaling::check("a grid and its cells, by cell count", 512, |c| {
                let n = (c as f64).sqrt().round() as usize;
                let (p, cells) = grid(n, 10_000 * fresh.replace(fresh.get() + 1));
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
        .stack_size(1 << 28)
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
            let next = std::cell::Cell::new(0);
            scaling::check_order("decoys passed over, by count", 2, 2, |k| {
                next.set(next.get() + 100);
                let b = 1_000_000 + next.get();
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
        .stack_size(1 << 28)
        .spawn(|| {
            let fresh = std::cell::Cell::new(1);
            scaling::check("a product less n tuples passed over, by n", 1000, |n| {
                let b = 100_000 * fresh.replace(fresh.get() + 1);
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
        .stack_size(1 << 29)
        .spawn(|| {
            let fresh = std::cell::Cell::new(1);
            scaling::check("a nested tuple and a query on it, by depth", 400, |d| {
                let b = 100_000 * fresh.replace(fresh.get() + 1);
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

#[test]
fn listing_values_past_the_cap_stops_early() {
    // `(S, S)` for a set `S` of `n` literals has `n²` values, past a cap of `n`. The product of
    // the components' values was built before it was compared with the cap: `n²` rows.
    scaling::check("the values of a square past the cap, by n", 200, |n| {
        let s = Type::union_all((0..n).map(lit));
        let square = Type::tuple(vec![s.clone(), s.clone()]);
        assert_eq!(square.values(n), None, "n = {n}");
        assert_eq!(s.values(n).map(|v| v.len()), Some(n));
    });
    let s = Type::union_all((0..3).map(lit));
    let square = Type::tuple(vec![s.clone(), s]);
    assert_eq!(square.values(9).map(|v| v.len()), Some(9));
    assert_eq!(square.values(8), None);
    // A path is listed when the product of its positive parts is within the cap, before the
    // negated tuples are taken out, so 8 values from a product of 9 need a cap of 9.
    let rest = &square - &Type::tuple(vec![lit(0), lit(0)]);
    assert_eq!(rest.values(8), None);
    assert_eq!(rest.values(9).map(|v| v.len()), Some(8));
}
