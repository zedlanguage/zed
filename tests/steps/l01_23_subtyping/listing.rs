//! Finite listing (T6, SYNTHESIS Q4): `Type::finite` says whether a type is known finite, and
//! `Type::each_value` lists the values of such a type one at a time. Neither compares a size,
//! so the answer depends on the type alone: a square of `n` literals is finite and lists `n²`
//! values at every `n`. The lists are checked against `contains` over every candidate value.

use std::collections::BTreeSet;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_tests::scaling;

fn lit(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).unwrap()
}

fn listed(t: &Type) -> Option<BTreeSet<Value>> {
    let vs: Vec<Value> = t.each_value()?.collect();
    let set: BTreeSet<Value> = vs.iter().cloned().collect();
    assert_eq!(set.len(), vs.len(), "each value once: {t}");
    Some(set)
}

#[test]
fn finite_types_and_their_values() {
    let s = Type::union_all((0..3).map(lit));
    let square = Type::tuple(vec![s.clone(), s.clone()]);
    assert!(square.finite());
    assert_eq!(listed(&square).map(|v| v.len()), Some(9));
    // The negated tuple type is taken out as each tuple is checked.
    let rest = &square - &Type::tuple(vec![lit(0), lit(0)]);
    assert_eq!(listed(&rest).map(|v| v.len()), Some(8));
    // Scalars, bools and a tuple of them.
    let mixed = &(&Type::bool() | &lit(7)) | &Type::tuple(vec![Type::bool(), lit(1)]);
    assert_eq!(listed(&mixed).map(|v| v.len()), Some(5));
    // A type with no value is finite and lists nothing.
    assert_eq!(listed(&Type::empty()).map(|v| v.len()), Some(0));
    let hollow = Type::tuple(vec![s.clone(), Type::empty()]);
    assert_eq!(listed(&hollow).map(|v| v.len()), Some(0));
}

#[test]
fn types_not_known_finite() {
    let s = Type::union_all((0..3).map(lit));
    for t in [
        Type::int(),
        Type::top(),
        !&s,
        Type::tuple(vec![Type::int(), s.clone()]),
        &Type::tuple(vec![s.clone(), s.clone()]) | &Type::tuple(vec![Type::int(), lit(0)]),
        Type::morphism(Type::empty(), Type::top(), lit(1)),
        // One value, `(0, 0)`, but the box `(int, 0)` is read as written: a negated tuple
        // type is not taken out of the box it is met with.
        &Type::tuple(vec![Type::int(), lit(0)])
            - &Type::tuple(vec![&Type::int() - &lit(0), lit(0)]),
    ] {
        assert!(!t.finite(), "{t}");
        assert!(t.each_value().is_none(), "{t}");
    }
    // A negated tuple type met with a finite one is finite: the box is the meet.
    let t = &Type::tuple(vec![lit(0), lit(0)]) - &Type::tuple(vec![Type::int(), lit(1)]);
    assert_eq!(listed(&t).map(|v| v.len()), Some(1));
    // Two tuple types met are finite when their meet is, whichever the diagram tests first:
    // only the box of the last tuple type a path to `true` takes is read (step L1.37a).
    for t in [
        &Type::tuple(vec![Type::int(), lit(0)]) & &Type::tuple(vec![lit(0), lit(0)]),
        &Type::tuple(vec![lit(0), lit(0)]) & &Type::tuple(vec![Type::int(), lit(0)]),
    ] {
        assert_eq!(listed(&t).map(|v| v.len()), Some(1), "{t}");
    }
}

/// A small random type over the literals 0..3 and pairs of them, from `seed`.
fn random(seed: &mut u64, depth: u32) -> Type {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let k = (*seed >> 33) % if depth == 0 { 2 } else { 6 };
    match k {
        0 => lit(((*seed >> 40) % 3) as usize),
        1 => Type::union_all((0..3).filter(|i| (*seed >> (45 + i)) & 1 == 1).map(lit)),
        2 => Type::tuple(vec![random(seed, depth - 1), random(seed, depth - 1)]),
        3 => &random(seed, depth - 1) | &random(seed, depth - 1),
        4 => &random(seed, depth - 1) & &random(seed, depth - 1),
        _ => &random(seed, depth - 1) - &random(seed, depth - 1),
    }
}

#[test]
fn lists_agree_with_membership() {
    // Every value a random type can hold: the literals 0..3 and pairs of them, nested down to
    // the depth `random` builds.
    let lits: Vec<Value> = (0..3).map(Value::Int).collect();
    let mut all = lits.clone();
    for _ in 0..3 {
        let pairs: Vec<Value> = all
            .iter()
            .flat_map(|a| {
                all.iter()
                    .map(move |b| Value::tuple(vec![a.clone(), b.clone()]))
            })
            .collect();
        all = lits
            .iter()
            .cloned()
            .chain(pairs)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
    }
    let mut seed = 1;
    let mut checked = 0;
    for _ in 0..600 {
        let t = random(&mut seed, 3);
        let Some(got) = listed(&t) else {
            continue;
        };
        checked += 1;
        let want: BTreeSet<Value> = all.iter().filter(|v| t.contains(v)).cloned().collect();
        assert_eq!(got, want, "{t}");
    }
    assert!(checked > 300, "{checked} types listed");
}

/// `t(0) = 0 | 1`, `t(i + 1) = (t(i), t(i))`: `d + 1` types, `2^(2^d)` values.
fn doubling(d: usize) -> Type {
    (0..d).fold(&lit(0) | &lit(1), |t, _| Type::tuple(vec![t.clone(), t]))
}

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

/// The first value of `doubling(d)`: the pair of the first value of `doubling(d - 1)` with
/// itself, down to `0`. Checked along its first components, since its tree has `2^d` leaves.
fn assert_first_value(v: &Value, d: usize) {
    let mut at = v;
    for level in (1..=d).rev() {
        let Value::Tuple(items) = at else {
            panic!("level {level} of the first value of t({d}) is not a pair: {at}");
        };
        assert_eq!(items.len(), 2, "level {level} of the first value of t({d})");
        at = &items[0];
    }
    assert_eq!(*at, Value::Int(0), "the first value of t({d}) ends in 0");
}

#[test]
fn the_first_value_of_a_deep_doubling_type_is_made_without_listing_inner_types() {
    // `doubling(6)` has 2^64 values and its components 2^32 each; `doubling(48)` has
    // 2^(2^48). The first value reads one value of each of the `d + 1` types, so both come
    // at once; listing an inner type in full first does not end.
    for d in [6, 48] {
        let t = doubling(d);
        let mut each = t.each_value().expect("a doubling type is finite");
        let first = each.next().expect("a doubling type has a value");
        assert_first_value(&first, d);
        assert!(t.contains(&first), "t({d}) holds its first value");
        // The next values differ in the last component first.
        let more: Vec<Value> = each.take(9).collect();
        assert_eq!(more.len(), 9, "t({d}) gives ten values");
        let distinct: BTreeSet<&Value> = more.iter().chain([&first]).collect();
        assert_eq!(distinct.len(), 10, "t({d}) gives each value once");
        assert!(
            more.iter().all(|v| t.contains(v)),
            "t({d}) holds its values"
        );
    }
    // At a small depth the first values are the start of the full list, in its order.
    let t = doubling(2);
    let all: Vec<Value> = t.each_value().expect("finite").collect();
    assert_eq!(all.len(), 16);
    let firsts: Vec<Value> = t.each_value().expect("finite").take(5).collect();
    assert_eq!(firsts, all[..5]);
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

/// The exclusive or of `types`, taken in order as `x = (x - t) | (t - x)`.
fn parity(types: impl IntoIterator<Item = Type>) -> Type {
    types
        .into_iter()
        .fold(Type::empty(), |x, t| &(&x - &t) | &(&t - &x))
}

fn span(from: usize, to: usize) -> Type {
    Type::union_all((from..to).map(lit))
}

fn int(i: i64) -> Value {
    Value::Int(i)
}

fn pair(a: Value, b: Value) -> Value {
    Value::tuple(vec![a, b])
}

fn one_of(v: Value) -> Value {
    Value::tuple(vec![v])
}

#[test]
fn tuples_are_checked_against_the_tuple_types_that_may_hold_them() {
    // A tuple is checked on the part restricted to the tuple types that may hold it, found by
    // its components, and an earlier box is read only when it may hold the tuple
    // (LIST-parity-quad). Each list is checked against `contains` over the integers 0..8, the
    // pairs of them, those integers and pairs in a one-tuple, and those integers in a one-tuple
    // in a one-tuple; its order is the order of the boxes.
    let ints: Vec<Value> = (0..8).map(int).collect();
    let pairs: Vec<Value> = ints
        .iter()
        .flat_map(|a| ints.iter().map(move |b| pair(a.clone(), b.clone())))
        .collect();
    let all: Vec<Value> = ints
        .iter()
        .chain(&pairs)
        .cloned()
        .chain(
            ints.iter()
                .chain(&pairs)
                .map(|p| Value::tuple(vec![p.clone()])),
        )
        .chain(ints.iter().map(|i| one_of(one_of(i.clone()))))
        .collect();
    let exact = |t: &Type| -> Vec<Value> {
        let got: Vec<Value> = t.each_value().expect("finite").collect();
        let want: BTreeSet<Value> = all.iter().filter(|v| t.contains(v)).cloned().collect();
        assert_eq!(listed(t), Some(want), "{t}");
        got
    };
    let diagonal = |i: usize| Type::tuple(vec![lit(i), lit(i)]);
    // No tuple type, one, and two: the exclusive or of two disjoint types is their union.
    assert!(exact(&parity([])).is_empty());
    assert_eq!(exact(&parity([diagonal(3)])), [pair(int(3), int(3))]);
    assert_eq!(
        exact(&parity([diagonal(3), diagonal(1)])).len(),
        2,
        "two disjoint tuple types"
    );
    // Overlapping one-column tuple types: a value in an even number of them is not listed.
    let ones = parity((0..5).map(|i| Type::tuple(vec![span(i, i + 3)])));
    assert_eq!(exact(&ones).len(), 5);
    // Overlapping two-column tuple types, each keyed by a column the other holds: `(0, 0)` is
    // in both, `(1, 0)` and `(0, 1)` in one each, so each column's lookup finds a type that
    // the other column then rules out.
    let crossed = parity([
        Type::tuple(vec![span(0, 2), lit(0)]),
        Type::tuple(vec![lit(0), span(0, 2)]),
    ]);
    assert_eq!(
        BTreeSet::from_iter(exact(&crossed)),
        BTreeSet::from([pair(int(1), int(0)), pair(int(0), int(1))])
    );
    // A column of tuples is found by their first components.
    let nested = parity((0..4).map(|i| Type::tuple(vec![diagonal(i)])));
    assert_eq!(exact(&nested).len(), 4);
    let one = |t: Type| Type::tuple(vec![t]);
    let crossed_nested = parity([
        one(Type::tuple(vec![span(0, 2), lit(0)])),
        one(Type::tuple(vec![lit(0), span(0, 2)])),
    ]);
    assert_eq!(
        BTreeSet::from_iter(exact(&crossed_nested)),
        BTreeSet::from([one_of(pair(int(1), int(0))), one_of(pair(int(0), int(1)))])
    );
    // A column of tuples and integers, or of tuples of two lengths, is found by its keys at
    // each depth (LIST-parity-rest): `(5)` is in all three tuple types and so in their parity.
    let loose = parity((0..3).map(|i| one(&diagonal(i) | &lit(5))));
    assert_eq!(exact(&loose).len(), 3 + 1);
    let lengths = parity((0..3).map(|i| one(&diagonal(i) | &Type::tuple(vec![lit(i)]))));
    assert_eq!(exact(&lengths).len(), 3 + 3);
    let mixed = &nested | &parity((0..3).map(|i| Type::tuple(vec![span(0, 3), lit(i)])));
    assert_eq!(exact(&mixed).len(), 4 + 9);
    // A parity beside a tuple type that meets every one of its types.
    let wide =
        &parity((0..6).map(diagonal)) | &(&Type::tuple(vec![span(0, 6), lit(0)]) - &diagonal(0));
    assert_eq!(exact(&wide).len(), 6 + 5);
    // Overlapping boxes of one diagram: a tuple two boxes hold is listed once, from the first.
    let boxes =
        &Type::tuple(vec![span(0, 2), span(0, 2)]) | &Type::tuple(vec![span(1, 3), span(1, 3)]);
    assert_eq!(exact(&boxes).len(), 7);
    let squares =
        Type::union_all((0..4).map(|i| Type::tuple(vec![span(i, i + 2), span(i, i + 2)])));
    assert_eq!(exact(&squares).len(), 13);
    // The order: each box in turn, the last component fastest, a tuple an earlier box gave
    // left out.
    let pairs_of = |ps: &[(i64, i64)]| -> Vec<Value> {
        ps.iter().map(|&(a, b)| pair(int(a), int(b))).collect()
    };
    let first = [(1, 1), (1, 2), (2, 1), (2, 2), (0, 0), (0, 1), (1, 0)];
    assert_eq!(exact(&boxes), pairs_of(&first));
    let rest = [(2, 3), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4)];
    assert_eq!(exact(&squares), pairs_of(&[&first[..], &rest[..]].concat()));
    assert_eq!(exact(&crossed), pairs_of(&[(0, 1), (1, 0)]));
}

#[test]
fn every_tuple_type_is_filed_by_its_parts() {
    // A column of several kinds or tuple lengths is filed by the scalars, bare atoms and empty
    // tuples it lists at each depth of first components; a tuple type no column of which lists
    // its values, such as one given by its complement, is filed by the keys of every column,
    // and its value on a tuple with none of them is decided by the tuple's kinds
    // (LIST-parity-rest). Each list is checked against `contains` over the scalars below, the
    // empty tuple, and their one-tuples, pairs, one-tuples of one-tuples and of pairs.
    let v = |x: Value| Type::lit(&x).unwrap();
    let mut scalars: Vec<Value> = (0..6).map(int).collect();
    scalars.extend([
        Value::Bool(false),
        Value::Bool(true),
        Value::str("s"),
        Value::str("t"),
        Value::atom("a"),
        Value::atom("b"),
    ]);
    let u = &Type::union_all(scalars.iter().cloned().map(v)) | &Type::tuple(vec![]);
    scalars.push(Value::tuple(vec![]));
    let mut all = scalars.clone();
    all.extend(scalars.iter().cloned().map(one_of));
    all.extend(
        scalars
            .iter()
            .flat_map(|a| scalars.iter().map(move |b| pair(a.clone(), b.clone()))),
    );
    all.extend(scalars.iter().map(|x| one_of(one_of(x.clone()))));
    all.extend(scalars.iter().map(|x| one_of(pair(x.clone(), int(0)))));
    let exact = |t: &Type| -> usize {
        let want: BTreeSet<Value> = all.iter().filter(|x| t.contains(x)).cloned().collect();
        assert_eq!(listed(t), Some(want.clone()), "{t}");
        want.len()
    };
    let one = |t: Type| Type::tuple(vec![t]);
    let but = |x: Type| &Type::top() - &x;
    let n = scalars.len();
    // Columns of two kinds each: a value in two of the tuple types is not listed.
    let (s, a) = (v(Value::str("s")), v(Value::atom("a")));
    let kinds = parity([
        one(&lit(0) | &s),
        one(&s | &a),
        one(&a | &Type::tuple(vec![])),
        one(&Type::tuple(vec![]) | &v(Value::Bool(true))),
    ]);
    assert_eq!(exact(&kinds), 2, "(0) and (true)");
    // Tuple types given by their complements, in every kind: within the one-tuples of `u`,
    // all but `#a`, `3` and `true`, and the difference keeps `3` alone.
    let within = one(u.clone());
    let met = [a.clone(), lit(3), v(Value::Bool(true))]
        .into_iter()
        .fold(within.clone(), |t, x| &t & &one(but(x)));
    assert_eq!(exact(&met), n - 3);
    assert_eq!(exact(&(&within - &one(but(lit(3))))), 1);
    // Two columns given by their complements, of two kinds: a pair whose first component is
    // not an integer is in no tuple type with `int - 1` first, whatever its keys.
    let pairs = Type::tuple(vec![u.clone(), u.clone()]);
    let co = Type::tuple(vec![&Type::int() - &lit(1), but(s.clone())]);
    let co2 = Type::tuple(vec![but(lit(0)), &Type::int() - &lit(2)]);
    assert_eq!(exact(&(&(&pairs & &co) - &co2)), 5 * (n - 1) - 4 * 5);
    // A complement one level down, in the only tuple type of length 1 of its column.
    let nested = &one(one(u.clone())) & &one(one(&Type::int() - &lit(2)));
    assert_eq!(exact(&nested), 5);
    // A complement first in a pair: its kinds leave its value unknown, and it is read for every
    // tuple of the class; the list is still exact.
    let open = &one(Type::tuple(vec![u.clone(), lit(0)]))
        & &one(Type::tuple(vec![&Type::int() - &lit(2), lit(0)]));
    assert_eq!(exact(&open), 5);
    // The empty tuple is a key where a column holds it.
    let empty = parity([one(&Type::tuple(vec![]) | &lit(1)), one(&lit(1) | &lit(2))]);
    assert_eq!(exact(&empty), 2, "(()) and (2)");
}

#[test]
fn a_tuple_type_with_a_complement_column_is_filed_by_it() {
    // A tuple type with a column given by its complement and a column whose keys more tuple
    // types share, such as each `(int - i, w)` of a meet, is filed by the complement and
    // absorbs the other column: a scalar there is read once per region of scalars the
    // absorbing tuple types hold alike, and a tuple there by its keys (LIST-parity-tail).
    // Each list is checked against `contains` over pairs of the values below, their
    // one-tuples, and pairs with a one-tuple on either side.
    // The empty tuple is no literal: it is the tuple type of no columns.
    let v = |x: Value| Type::lit(&x).unwrap_or_else(|| Type::tuple(vec![]));
    let mut scalars: Vec<Value> = (0..6).map(int).collect();
    scalars.extend([
        Value::Bool(false),
        Value::Bool(true),
        Value::str("s"),
        Value::str("t"),
        Value::atom("a"),
        Value::atom("b"),
        Value::float(0.5),
        Value::rat(zed_kernel::Rat::int(7.into())),
        Value::tuple(vec![]),
    ]);
    let one = |t: Type| Type::tuple(vec![t]);
    let u = &Type::union_all(scalars.iter().cloned().map(v)) | &one(&lit(0) | &lit(1));
    let mut values = scalars.clone();
    values.extend([one_of(int(0)), one_of(int(1)), one_of(int(2))]);
    let mut all: Vec<Value> = values
        .iter()
        .flat_map(|a| values.iter().map(move |b| pair(a.clone(), b.clone())))
        .collect();
    all.extend(all.clone().into_iter().map(one_of));
    let exact = |t: &Type| -> usize {
        let want: BTreeSet<Value> = all.iter().filter(|x| t.contains(x)).cloned().collect();
        assert_eq!(listed(t), Some(want.clone()), "{t}");
        want.len()
    };
    let but = |x: Type| &Type::top() - &x;
    // The second columns share most of their keys, so they are absorbed: `0`, `1`, `2`, `"t"`
    // and `0.5` are in all of them, one region; `true` and `()` in the even ones and `"s"`, `7`
    // and `(0)` in the odd ones, two more.
    let second = |i: usize| -> Type {
        let common = [int(0), int(1), int(2), Value::str("t"), Value::float(0.5)];
        let mut w = Type::union_all(common.into_iter().map(v));
        w = &w
            | &match i % 2 {
                0 => &v(Value::Bool(true)) | &Type::tuple(vec![]),
                _ => {
                    &(&v(Value::str("s")) | &v(Value::rat(zed_kernel::Rat::int(7.into()))))
                        | &one(lit(0))
                }
            };
        w
    };
    let rows: Vec<Type> = (0..6)
        .map(|i| Type::tuple(vec![but(lit(i)), second(i)]))
        .collect();
    let pairs = Type::tuple(vec![u.clone(), u.clone()]);
    for k in [2, 4, 6] {
        let met = rows[..k].iter().fold(pairs.clone(), |t, r| &t & r);
        exact(&met);
        exact(&one(met));
        exact(
            &rows[..k - 1]
                .iter()
                .fold(&pairs - &rows[k - 1], |t, r| &t & r),
        );
        exact(&(&pairs - &Type::union_all(rows[..k].iter().cloned())));
    }
    // The meet of the scaling test: `(0..2c, 0)` met with each `(int - (2i + 1), 0)`.
    let c = 5;
    let all_firsts = Type::tuple(vec![Type::union_all((0..2 * c).map(lit)), lit(0)]);
    let met = (0..c).fold(all_firsts, |t, i| {
        &t & &Type::tuple(vec![&Type::int() - &lit(2 * i + 1), lit(0)])
    });
    assert_eq!(listed(&met).map(|s| s.len()), Some(c));
    assert_eq!(listed(&one(met)).map(|s| s.len()), Some(c));
}

#[test]
fn tuples_of_one_spine_are_one_class_per_region_of_their_scalars() {
    // `((2i, i),)` met with each `((int - (2k + 1), x),)`: the tuples differ only in scalars
    // that are not first components, and each is read by the region of its scalar there, the
    // set of the open rows' types there that list it, not by its value (LIST-parity-keys). The
    // meets along a path are made column by column where both sides are one row, nested ones
    // too. Each list is checked against `contains` over the candidates below.
    let v = |x: Value| Type::lit(&x).expect("a literal");
    let scalars: Vec<Value> = (0..8)
        .map(int)
        .chain([
            Value::Bool(true),
            Value::str("s"),
            Value::str("t"),
            Value::atom("a"),
            Value::atom("b"),
            Value::float(0.5),
        ])
        .collect();
    let mut all: Vec<Value> = Vec::new();
    for a in &scalars {
        for b in &scalars {
            all.push(one_of(pair(a.clone(), b.clone())));
            all.push(one_of(pair(one_of(a.clone()), b.clone())));
        }
    }
    let exact = |t: &Type| -> usize {
        let want: BTreeSet<Value> = all.iter().filter(|x| t.contains(x)).cloned().collect();
        assert_eq!(listed(t), Some(want.clone()), "{t}");
        want.len()
    };
    let one = |t: Type| Type::tuple(vec![t]);
    let but = |x: Type| &Type::top() - &x;
    let u = Type::union_all(scalars.iter().cloned().map(v));
    let firsts = |c: usize| {
        one(Type::union_all(
            (0..c).map(|i| Type::tuple(vec![lit(2 * i), lit(i)])),
        ))
    };
    let meet = |start: Type, xs: &[Type]| {
        xs.iter().enumerate().fold(start, |t, (k, x)| {
            &t & &one(Type::tuple(vec![&Type::int() - &lit(2 * k + 1), x.clone()]))
        })
    };
    let c = 4;
    // Second columns of every kind: all integers, one literal, a list shared by every row, a
    // complement, lists of other kinds, and a column that lists strings and atoms.
    let xs = [
        Type::int(),
        lit(0),
        Type::union_all((0..c).map(lit)),
        &Type::int() - &lit(2),
        &v(Value::str("s")) | &lit(1),
        but(v(Value::atom("a"))),
        &(&v(Value::atom("b")) | &v(Value::str("t"))) | &Type::union_all((1..3).map(lit)),
        &u - &v(Value::float(0.5)),
    ];
    for x in &xs {
        let same: Vec<Type> = (0..c).map(|_| x.clone()).collect();
        exact(&meet(firsts(c), &same));
    }
    // Each row its own second column, so the scalars there fall in many regions: all of them,
    // which meet to nothing, and five that keep three of the four `(2i, i)`.
    let own = xs.to_vec();
    exact(&meet(firsts(c), &own));
    let some = [0, 2, 3, 5, 7].map(|k| xs[k].clone());
    assert_eq!(exact(&meet(firsts(c), &some)), 3);
    // Pairs of every scalar with the first column a complement too, and its exclusive or.
    let square = one(Type::tuple(vec![u.clone(), u.clone()]));
    let met = meet(square.clone(), &some);
    assert!(exact(&met) > 1);
    exact(&meet(square.clone(), &own));
    exact(&parity([square.clone(), met.clone()]));
    // A nested first column, `((((i), i)),)`, met column by column at depth two, and a meet
    // that is empty in one column.
    let nested = one(Type::tuple(vec![one(u.clone()), u.clone()]));
    let deep = meet(nested.clone(), &own);
    exact(&deep);
    exact(&(&deep & &one(Type::tuple(vec![one(lit(0)), lit(1)]))));
    exact(&(&deep & &one(Type::tuple(vec![one(lit(0)), but(Type::int())]))));
    assert_eq!(
        exact(&(&meet(firsts(c), &[lit(0)]) & &one(Type::tuple(vec![lit(0), lit(1)])))),
        0
    );
    // Expected counts at the sizes the scaling test checks the shape of: every `(2i, i)` is
    // in each row where `x` holds `i`.
    for c in [1, 2, 7] {
        let count = |x: &dyn Fn(usize) -> Type| {
            let xs: Vec<Type> = (0..c).map(x).collect();
            meet(firsts(c), &xs).each_value().map(|vs| vs.count())
        };
        assert_eq!(count(&|_| Type::int()), Some(c), "c = {c}");
        assert_eq!(count(&|_| lit(0)), Some(1), "c = {c}");
        assert_eq!(
            count(&|_| Type::union_all((0..c).map(lit))),
            Some(c),
            "c = {c}"
        );
        assert_eq!(count(&|k| &Type::int() - &lit(c + k)), Some(c), "c = {c}");
        // `x` without `2k + 1` keeps the even `i` and the odd ones of `2k + 1 >= c`.
        assert_eq!(
            count(&|k| &Type::int() - &lit(2 * k + 1)),
            Some(c.div_ceil(2)),
            "c = {c}"
        );
    }
}

/// The exclusive or of `x` and `y`, as `(x - y) | (y - x)`.
fn xor(x: &Type, y: &Type) -> Type {
    &(x - y) | &(y - x)
}

#[test]
fn finiteness_sees_through_meets_and_exclusive_ors() {
    // `((u, u),)`, `u = 0..8`, met with the exclusive or of the infinite `((int - (2k + 1),
    // int),)` for `k < 3`, and the exclusive or of each of those met with the square first,
    // are finite: a meet gives the boxes of one operand met with the join of the other's, and
    // an exclusive or the boxes of its operands (LIST-xor-finite). Both were not known finite.
    // A pair is in all three rows unless its first component is 1, 3 or 5, when it is in two,
    // so 5 * 8 pairs are listed.
    let one = |t: Type| Type::tuple(vec![t]);
    let u = span(0, 8);
    let square = one(Type::tuple(vec![u.clone(), u.clone()]));
    let rows: Vec<Type> = (0..3)
        .map(|k| {
            one(Type::tuple(vec![
                &Type::int() - &lit(2 * k + 1),
                Type::int(),
            ]))
        })
        .collect();
    let candidates: Vec<Value> = (0..10)
        .flat_map(|a| (0..10).map(move |b| one_of(pair(int(a), int(b)))))
        .collect();
    let exact = |t: &Type| -> usize {
        let want: BTreeSet<Value> = candidates
            .iter()
            .filter(|v| t.contains(v))
            .cloned()
            .collect();
        assert!(t.finite(), "{t}");
        assert_eq!(listed(t), Some(want.clone()), "{t}");
        want.len()
    };
    let met = &square & &parity(rows.clone());
    assert_eq!(exact(&met), 5 * 8);
    let each = parity(rows.iter().map(|r| &square & r));
    assert_eq!(exact(&each), 5 * 8);
    // The same with the meet on the other side, through a complement, and with a union.
    assert_eq!(exact(&(&parity(rows.clone()) & &square)), 5 * 8);
    assert_eq!(exact(&(&square - &parity(rows.clone()))), 3 * 8);
    let wider = &square | &one(Type::tuple(vec![lit(9), lit(9)]));
    assert_eq!(exact(&(&wider & &parity(rows.clone()))), 5 * 8 + 1);
    // Each still holds infinitely many tuples outside the square.
    for t in [
        parity(rows.clone()),
        &parity(rows.clone()) - &square,
        &square | &rows[0],
    ] {
        assert!(!t.finite(), "{t}");
        assert!(t.each_value().is_none(), "{t}");
    }
}

/// A small random type over the integers 0..3, `int` and its complements of one literal, pairs
/// and one-tuples of such types nested `level` deep, joined, met, differenced and taken in
/// exclusive or, from `seed`. Many are infinite.
fn random_mixed(seed: &mut u64, depth: u32, level: u32) -> Type {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let leaf = depth == 0;
    let k = (*seed >> 33) % if leaf { 4 } else { 9 };
    let bits = *seed >> 40;
    match k {
        0 => lit((bits % 3) as usize),
        1 => Type::union_all((0..3).filter(|i| (bits >> i) & 1 == 1).map(lit)),
        2 => Type::int(),
        3 => &Type::int() - &lit((bits % 3) as usize),
        4 | 5 if level > 0 => {
            let a = random_mixed(seed, depth - 1, level - 1);
            if k == 4 {
                Type::tuple(vec![a, random_mixed(seed, depth - 1, level - 1)])
            } else {
                Type::tuple(vec![a])
            }
        }
        4 | 5 => lit((bits % 3) as usize),
        6 => &random_mixed(seed, depth - 1, level) | &random_mixed(seed, depth - 1, level),
        7 => &random_mixed(seed, depth - 1, level) & &random_mixed(seed, depth - 1, level),
        _ if bits & 1 == 0 => {
            &random_mixed(seed, depth - 1, level) - &random_mixed(seed, depth - 1, level)
        }
        _ => xor(
            &random_mixed(seed, depth - 1, level),
            &random_mixed(seed, depth - 1, level),
        ),
    }
}

#[test]
fn each_value_agrees_with_a_search_of_all_points() {
    // Every value of the shapes `random_mixed` builds: the integers 0..3 and 7, pairs and
    // one-tuples of them, and pairs and one-tuples of those. The types name only 0..3, so 7
    // stands for every other integer: a type that holds a value with a 7 in it holds infinitely
    // many, and must not be listed, and one that holds none is finite and must list exactly
    // the values it holds. A type that is finite but not known finite is counted.
    let ints: Vec<Value> = [0, 1, 2, 7].map(int).to_vec();
    let up = |vs: &[Value]| -> Vec<Value> {
        let mut out = ints.clone();
        for a in vs {
            out.push(one_of(a.clone()));
            for b in vs {
                out.push(pair(a.clone(), b.clone()));
            }
        }
        out
    };
    let all = up(&up(&ints));
    let mentions_seven = |v: &Value| v.to_string().contains('7');
    let (mut listed_count, mut infinite, mut missed) = (0, 0, 0);
    let mut seed = 7;
    for _ in 0..1500 {
        let t = random_mixed(&mut seed, 4, 2);
        let holds: Vec<&Value> = all.iter().filter(|v| t.contains(v)).collect();
        let finite = !holds.iter().any(|v| mentions_seven(v));
        match listed(&t) {
            Some(got) => {
                assert!(finite, "an infinite type listed: {t}");
                assert!(t.finite(), "{t}");
                let want: BTreeSet<Value> = holds.into_iter().cloned().collect();
                assert_eq!(got, want, "{t}");
                listed_count += 1;
            }
            None if finite => missed += 1,
            None => infinite += 1,
        }
    }
    eprintln!("listed {listed_count}, infinite {infinite}, finite but not known finite {missed}");
    assert!(
        listed_count > 300 && infinite > 300,
        "{listed_count} listed, {infinite} infinite"
    );
}
