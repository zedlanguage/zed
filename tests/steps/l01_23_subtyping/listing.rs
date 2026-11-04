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
