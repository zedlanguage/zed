//! Witness-catalog bijectivity (DESIGN.md sec:grouping): each of the eight entries that need
//! no layer, run on finite domains. A witnessed key map must never collide, and a map the
//! catalog states with its inverse must give back the family it started from. Each side
//! condition comes with the domain on which dropping it collides or breaks the inverse.
//!
//! The reference evaluator checks the collision rule on every reindex, so a key map is
//! injective on a domain exactly when its reindex of that domain is not a collision.

use zed_kernel::term::build::{if_, lit};
use zed_kernel::{Family, KernelError, Term, Value, eval};
use zed_tests::kernel::*;

/// A one-level family `k -> v` over the integers `lo..=hi`, each entry its key's reading.
fn readings(lo: i64, hi: i64) -> Value {
    Value::Family(Family::of(
        (lo..=hi).map(|k| (Value::Int(k), Value::Int(100 + k))),
    ))
}

/// A two-level family `i -> j -> v` over the box `rows × cols`: a pixel grid whose entry is
/// its brightness.
fn grid(rows: std::ops::RangeInclusive<i64>, cols: std::ops::RangeInclusive<i64>) -> Value {
    let leaves: Vec<_> = rows
        .flat_map(|i| cols.clone().map(move |j| (i, j)))
        .map(|(i, j)| {
            (
                vec![Value::Int(i), Value::Int(j)],
                Value::Int((i * 7 + j * 3).rem_euclid(256)),
            )
        })
        .collect();
    Value::Family(Family::from_leaves(leaves).expect("a box has distinct keypaths"))
}

/// Rekeys `f` by `keys(path)`, keeping each entry's value.
fn rekey(f: Term, keys: impl FnOnce(Term) -> Vec<Term>) -> Term {
    reindex(f, func(|[p, _]| path(keys(p))), func(|[_, v]| v))
}

/// Whether the rekey ran without a collision.
fn injective(t: &Term) -> bool {
    match eval(t) {
        Ok(_) => true,
        Err(KernelError::Collision { .. }) => false,
        Err(e) => panic!("the rekey failed with {e:?}"),
    }
}

/// The rekey's result, which must exist.
fn value(t: &Term) -> Value {
    eval(t).expect("a witnessed rekey evaluates")
}

// Literal key occurrence.

#[test]
fn literal_key_occurrence_keeps_every_key_and_dropping_one_collides() {
    let g = lit(grid(0..=3, 0..=4));
    let same = rekey(g.clone(), |p| vec![key(p.clone(), 0), key(p, 1)]);
    assert_eq!(value(&same), grid(0..=3, 0..=4));
    // Keeping only the row puts the five pixels of a row at one keypath.
    assert!(!injective(&rekey(g, |p| vec![key(p, 0)])));
}

// Tupling and permutation.

#[test]
fn transposing_twice_gives_back_the_grid() {
    let swap = |f: Term| rekey(f, |p| vec![key(p.clone(), 1), key(p, 0)]);
    let g = grid(-2..=2, 0..=3);
    let t = value(&swap(lit(g.clone())));
    assert_eq!(t, moved(&g, |k| vec![k[1].clone(), k[0].clone()]));
    assert_eq!(value(&swap(lit(t))), g);
}

// Componentwise maps.

#[test]
fn componentwise_witnessed_maps_are_injective_and_a_noninjective_component_collides() {
    // Shift the rows by one and double the columns: a product of injections.
    let g = lit(grid(-3..=3, -3..=3));
    let moved = rekey(g.clone(), |p| {
        vec![add(key(p.clone(), 0), lit(1)), mul(key(p, 1), lit(2))]
    });
    assert!(injective(&moved));
    // Back again: subtract one, halve.
    let back = rekey(moved, |p| {
        vec![sub(key(p.clone(), 0), lit(1)), idiv(key(p, 1), lit(2))]
    });
    assert_eq!(value(&back), grid(-3..=3, -3..=3));
    // Squaring a column is not injective on columns of both signs.
    assert!(!injective(&rekey(g, |p| {
        vec![key(p.clone(), 0), mul(key(p.clone(), 1), key(p, 1))]
    })));
}

// Widening.

#[test]
fn widening_by_the_value_keeps_the_old_key_and_never_collides() {
    // File each reading under (station, reading): the new key contains the old one, so two
    // stations with equal readings stay apart.
    let mut entries: Vec<(Value, Value)> =
        (0..6).map(|k| (Value::Int(k), Value::Int(k % 2))).collect();
    entries.push((Value::Int(6), Value::Int(0)));
    let f = lit(Value::Family(Family::of(entries)));
    let widened = reindex(
        f.clone(),
        func(|[p, v]| path(vec![key(p, 0), v])),
        func(|[_, v]| v),
    );
    assert!(injective(&widened));
    // Keying by the reading alone collides on the repeated reading.
    let by_value = reindex(f, func(|[_, v]| path(vec![v])), func(|[_, v]| v));
    assert!(!injective(&by_value));
}

// Strictly monotone arithmetic.

#[test]
fn strictly_monotone_arithmetic_on_a_range_is_injective() {
    let r = lit(readings(-8, 8));
    for step in [
        |k: Term| add(k, lit(1)),
        |k: Term| mul(k, lit(2)),
        |k: Term| sub(mul(k, lit(3)), lit(5)),
    ] {
        assert!(injective(&rekey(r.clone(), |p| vec![step(key(p, 0))])));
    }
    // Monotone but not strictly: halving collides on -8..=8 (k = 0 and k = 1 both give 0).
    assert!(!injective(&rekey(r.clone(), |p| vec![idiv(
        key(p, 0),
        lit(2)
    )])));
    // Strictly monotone on half the range only: squaring collides on -1 and 1.
    assert!(!injective(&rekey(r.clone(), |p| {
        vec![mul(key(p.clone(), 0), key(p, 0))]
    })));
    // Squaring is injective on the nonnegative half, where it is strictly monotone.
    assert!(injective(&rekey(lit(readings(0, 8)), |p| {
        vec![mul(key(p.clone(), 0), key(p, 0))]
    })));
}

// Modulo over a range no wider than the modulus.

#[test]
fn a_ring_buffer_slot_is_injective_on_at_most_p_contiguous_timestamps() {
    // Timestamps go into a ring buffer of p slots by t mod p. Any window of p contiguous
    // timestamps, negative ones included, fills each slot once; one wider, two share a slot.
    for p in 1..=5i64 {
        for base in -7..=3i64 {
            let slot = |w: i64| {
                rekey(lit(readings(base, base + w - 1)), |q| {
                    vec![modulo(key(q, 0), lit(p))]
                })
            };
            for w in 1..=p {
                assert!(injective(&slot(w)), "p = {p}, base = {base}, width {w}");
            }
            assert!(
                !injective(&slot(p + 1)),
                "p = {p}, base = {base}, width {}",
                p + 1
            );
        }
    }
}

// Affine packing and unpacking.

/// `(k1, k2) ↦ k1·s + k2`.
fn pack(f: Term, s: i64) -> Term {
    rekey(f, |p| vec![add(mul(key(p.clone(), 0), lit(s)), key(p, 1))])
}

/// `k ↦ (k div s, k mod s)`.
fn unpack(f: Term, s: i64) -> Term {
    rekey(f, |p| {
        vec![idiv(key(p.clone(), 0), lit(s)), modulo(key(p, 0), lit(s))]
    })
}

#[test]
fn row_major_packing_and_its_euclidean_unpacking_are_inverse_with_negative_rows() {
    // A grid whose rows run from -4, so the packed offsets and the quotients are negative.
    for s in 1..=5i64 {
        let g = grid(-4..=3, 0..=s - 1);
        let packed = pack(lit(g.clone()), s);
        assert!(injective(&packed), "stride {s}");
        assert_eq!(value(&unpack(packed, s)), g, "stride {s}");
        // The other direction: unpack a buffer of offsets -20..=20 and pack it back.
        let buffer = readings(-20, 20);
        assert_eq!(
            value(&pack(unpack(lit(buffer.clone()), s), s)),
            buffer,
            "stride {s}"
        );
    }
}

#[test]
fn a_stride_one_short_of_the_span_collides() {
    // Columns 0..s need stride s; stride s - 1 sends (i, s - 1) and (i + 1, 0) to one offset.
    for s in 2..=5i64 {
        assert!(
            !injective(&pack(lit(grid(-2..=2, 0..=s - 1)), s - 1)),
            "stride {}",
            s - 1
        );
    }
}

#[test]
fn truncated_division_fails_the_inverse_law_on_negative_quotients() {
    // Truncated division rounds the quotient toward zero, and its remainder takes the sign of
    // the dividend: -3 = 0·4 + (-3) instead of (-1)·4 + 1.
    let s = 4;
    let trunc_div = |k: Term| {
        if_(
            lt(k.clone(), lit(0)),
            sub(lit(0), idiv(sub(lit(0), k.clone()), lit(s))),
            idiv(k, lit(s)),
        )
    };
    let trunc_unpack = |f: Term| {
        rekey(f, |p| {
            let k = key(p, 0);
            vec![
                trunc_div(k.clone()),
                sub(k.clone(), mul(trunc_div(k), lit(s))),
            ]
        })
    };
    // On rows 0.. the truncated and Euclidean pairs agree.
    let rows_up = grid(0..=3, 0..=3);
    assert_eq!(value(&trunc_unpack(pack(lit(rows_up.clone()), s))), rows_up);
    // On row -1 they do not: (-1, 1) packs to -3 and comes back as (0, -3).
    let rows_down = grid(-1..=0, 0..=3);
    let back = value(&trunc_unpack(pack(lit(rows_down.clone()), s)));
    assert_ne!(back, rows_down);
    let Value::Family(back) = back else {
        panic!("a family")
    };
    assert!(back.get(&Value::Int(0)).is_some_and(|row| {
        matches!(row, Value::Family(r) if r.get(&Value::Int(-3)).is_some())
    }));
}

#[test]
fn packing_applies_lexicographically_at_depth_three() {
    // A tiled image: (tile row, row in tile, column) with 3 rows a tile and 4 columns,
    // packed to one offset by ((t·3) + r)·4 + c and unpacked by two Euclidean divisions.
    let leaves: Vec<_> = (-2..=1i64)
        .flat_map(|t| (0..3i64).flat_map(move |r| (0..4i64).map(move |c| (t, r, c))))
        .map(|(t, r, c)| {
            (
                vec![Value::Int(t), Value::Int(r), Value::Int(c)],
                Value::Int(t * 12 + r * 4 + c),
            )
        })
        .collect();
    let tiles = Value::Family(Family::from_leaves(leaves).unwrap());
    let packed = rekey(lit(tiles.clone()), |p| {
        let row = add(mul(key(p.clone(), 0), lit(3)), key(p.clone(), 1));
        vec![add(mul(row, lit(4)), key(p, 2))]
    });
    assert!(injective(&packed));
    // Each entry lands at the offset its value records.
    let Value::Family(flat) = value(&packed) else {
        panic!("a family")
    };
    assert!(flat.leaves().into_iter().all(|(k, v)| k[0] == v));
    let unpacked = rekey(packed, |p| {
        let k = key(p, 0);
        let row = idiv(k.clone(), lit(4));
        vec![
            idiv(row.clone(), lit(3)),
            modulo(row, lit(3)),
            modulo(k, lit(4)),
        ]
    });
    assert_eq!(value(&unpacked), tiles);
}

// Integer affine maps of full column rank.

#[test]
fn the_wavefront_skew_is_a_bijection_with_an_integer_inverse() {
    // (i, j) ↦ (i, i + j) has determinant 1; its inverse is (a, c) ↦ (a, c - a). No range
    // condition: it holds on a box of both signs.
    let g = grid(-4..=4, -4..=4);
    let skew = rekey(lit(g.clone()), |p| {
        vec![key(p.clone(), 0), add(key(p.clone(), 0), key(p, 1))]
    });
    assert!(injective(&skew));
    let unskew = rekey(skew, |p| {
        vec![key(p.clone(), 0), sub(key(p.clone(), 1), key(p, 0))]
    });
    assert_eq!(value(&unskew), g);
}

#[test]
fn a_tall_map_of_full_column_rank_is_injective_and_a_rank_deficient_one_collides() {
    let g = lit(grid(-4..=4, -4..=4));
    // (i, j) ↦ (i + j, i - 2j, 3i + j): three rows, two independent columns.
    assert!(injective(&rekey(g.clone(), |p| {
        let (i, j) = (key(p.clone(), 0), key(p, 1));
        vec![
            add(i.clone(), j.clone()),
            sub(i.clone(), mul(j.clone(), lit(2))),
            add(mul(i, lit(3)), j),
        ]
    })));
    // (i, j) ↦ i + j, the anti-diagonal sum, has rank 1 and is rejected: (0, 1) and (1, 0).
    assert!(!injective(&rekey(g.clone(), |p| {
        vec![add(key(p.clone(), 0), key(p, 1))]
    })));
    // (i, j) ↦ (i + j, 2i + 2j): two rows but dependent columns, so still rank 1.
    assert!(!injective(&rekey(g, |p| {
        let s = add(key(p.clone(), 0), key(p, 1));
        vec![s.clone(), mul(s, lit(2))]
    })));
}

/// The family `f` with each leaf moved to `to(keypath)`.
fn moved(f: &Value, to: impl Fn(&[Value]) -> Vec<Value>) -> Value {
    let Value::Family(f) = f else {
        panic!("a family")
    };
    let leaves: Vec<_> = f.leaves().into_iter().map(|(k, v)| (to(&k), v)).collect();
    Value::Family(Family::from_leaves(leaves).unwrap())
}
