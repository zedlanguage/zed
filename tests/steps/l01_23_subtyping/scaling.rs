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

/// The exclusive or of `c` tuple types `(b + i, _)`, `(b + i, b + i)` among them: a diagram of
/// about `2c` nodes with `2^(c - 1)` paths to `true`, holding `c` values.
fn odd_tuples(c: usize, b: usize) -> Type {
    (0..c).fold(Type::empty(), |x, i| {
        let t = Type::tuple(vec![lit(b + i), lit(b + i)]);
        &(&x - &t) | &(&t - &x)
    })
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
    // One pass over the nodes lists the candidates, but each of the `c` rows is still checked
    // along a path of up to `c` nodes: order `c²`, an open item (DESIGN.md L1.23).
    scaling::check_order(
        "listing an exclusive or of tuple types, by count",
        64,
        2,
        |c| {
            assert_eq!(built[&c].each_value().map(|v| v.count()), Some(c));
        },
    );
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
        .stack_size(1 << 28)
        .spawn(|| {
            let fresh = std::cell::Cell::new(1);
            scaling::check_order("a decision tree, by column count", 16, 2, |c| {
                let (p, rows) = decision_tree(c, 1000 * fresh.replace(fresh.get() + 1));
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

/// The pinwheel on `b + 1`, `b + 2` and `third`: the square of them less four boxes around its
/// middle `(b + 2, b + 2)`, and less the middle too when `full`, which makes it empty.
fn pinwheel(b: i64, full: bool, third: Type) -> Type {
    let ends = [lit_i(b + 1), lit_i(b + 2), third];
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

/// The union of `k` pinwheels on disjoint integers.
fn pinwheels(k: usize, full: bool) -> Type {
    Type::union_all((0..k as i64).map(|i| pinwheel(10 * i, full, lit_i(10 * i + 3))))
}

/// [`pinwheels`] with the third end of the last pinwheel cofinite: its own integer and every
/// integer no pinwheel uses.
fn cofinite_pinwheels(k: usize, full: bool) -> Type {
    let k = k as i64;
    let used = Type::union_all((0..k).flat_map(|i| (1..=3).map(move |j| lit_i(10 * i + j))));
    let third = &(&Type::int() - &used) | &lit_i(10 * (k - 1) + 3);
    let others = (0..k - 1).map(|i| pinwheel(10 * i, full, lit_i(10 * i + 3)));
    Type::union_all(others.chain([pinwheel(10 * (k - 1), full, third)]))
}

#[test]
fn a_union_of_disjoint_pinwheels_is_decided_piece_by_piece() {
    // No component splits the pinwheels' boxes into disjoint pieces, so each was decided, and
    // its value sought, against the whole union: 27.7 times the work from k = 16 to 128. Their
    // cells on the first component fall into one class per pinwheel, sharing no integer, and
    // the halves of the classes are decided and searched apart.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("k disjoint pinwheels, empty, by k", 64, |k| {
                Type::forget_emptiness();
                assert!(pinwheels(k, true).is_empty());
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
                    assert!(cofinite_pinwheels(k, true).is_empty());
                },
            );
            scaling::check("k disjoint pinwheels with a middle, by k", 64, |k| {
                Type::forget_emptiness();
                let t = pinwheels(k, false);
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
        let (full, open) = (pinwheels(k, true), pinwheels(k, false));
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
    scaling::check("a tuple held by n shapes together, by n", 64, |n| {
        Type::forget_emptiness();
        assert!(zedc::run::load(program(n).as_bytes()).is_ok());
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
