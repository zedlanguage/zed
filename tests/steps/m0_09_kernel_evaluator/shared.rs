//! Shared values (COMPLEXITY.md K21). A tuple, a keypath and an atom's payload hold their parts
//! behind one reference count, so reading a variable, a literal or a part of a tuple is O(1)
//! whatever the tuple's size, and a value is a DAG: a part can sit in many places at once.
//! Equality, order, keys and the language's `==` must treat a shared part as they treat a copy.

use std::collections::HashMap;
use std::thread;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Term, Value, World};
use zed_tests::kernel::*;
use zed_tests::scaling::check_order;

fn run(t: &Term) -> Value {
    Evaluator::new(World::new()).run(t).unwrap()
}

/// The tuple `(0, 1, ..., n - 1)`.
fn tuple(n: usize) -> Value {
    Value::tuple((0..n as i64).map(Value::Int).collect())
}

/// The keys `0..n`, each mapped to itself: the sequence a `foldl` runs over.
fn keys(n: usize) -> Value {
    Value::Family(Family::set(0..n as i64))
}

/// `(t -> fam(0..n, k -> t.0))((0, ..., n - 1))`: a function that reads its tuple argument
/// once per element, as a loop over a record's fields reads the record.
fn reads(n: usize) -> Term {
    let body = fam_with(lit(keys(n)), |_| nth(var("t"), 0));
    app(lam(&["t"], body), vec![lit(tuple(n))])
}

/// `xs.foldl((), (acc, x) -> (x, acc))` over `0..n`: the list `(n - 1, (..., (0, ())))` built
/// by an accumulator, the form COMPLEXITY.md K21 measured.
fn cons_list(n: usize) -> Term {
    let op = lam(&["acc", "x"], prim(Prim::Tuple, vec![var("x"), var("acc")]));
    foldl(lit(keys(n)), lit(Value::tuple(vec![])), op)
}

/// The list `cons_list(n)` computes.
fn expected_list(n: usize) -> Value {
    (0..n as i64).fold(Value::tuple(vec![]), |acc, x| {
        Value::tuple(vec![Value::Int(x), acc])
    })
}

/// Runs `f` on a thread with a 256 MiB stack: `foldl` is a definedness fix whose accumulators
/// each read the one before, so the evaluator nests one call per element.
fn on_large_stack(f: impl FnOnce() + Send) {
    thread::scope(|scope| {
        let t = thread::Builder::new().stack_size(1 << 28);
        t.spawn_scoped(scope, f).unwrap().join().unwrap()
    })
}

#[test]
fn a_record_read_once_per_field_gives_each_field() {
    let got = run(&reads(5));
    let want = Value::Family(Family::of((0..5).map(|k| (k, Value::Int(0)))));
    assert_eq!(got, want);
}

#[test]
fn an_accumulated_list_holds_every_element_in_order() {
    on_large_stack(|| {
        for n in [0, 1, 5, 50] {
            assert_eq!(run(&cons_list(n)), expected_list(n), "n = {n}");
        }
    });
}

#[test]
fn a_tuple_bound_to_two_names_is_one_value() {
    // `let a = (1, "x"); let b = a; (a, b)`
    let t = Value::tuple(vec![Value::Int(1), Value::str("x")]);
    let both = let_(
        "a",
        lit(t.clone()),
        let_("b", var("a"), prim(Prim::Tuple, vec![var("a"), var("b")])),
    );
    assert_eq!(run(&both), Value::tuple(vec![t.clone(), t]));
}

#[test]
fn taking_a_shared_tuple_apart_leaves_the_other_holder_whole() {
    let a = Value::tuple(vec![Value::Int(1), Value::str("two"), tuple(3)]);
    let b = a.clone();
    let Value::Tuple(parts) = b else {
        unreachable!("a tuple")
    };
    let mut parts = parts.into_vec();
    parts.push(Value::Int(4));
    assert_eq!(parts.len(), 4);
    assert_eq!(a, Value::tuple(parts[..3].to_vec()));
    // Held once, the parts are moved out.
    let Value::Tuple(only) = tuple(3) else {
        unreachable!("a tuple")
    };
    assert_eq!(
        only.into_vec(),
        vec![Value::Int(0), Value::Int(1), Value::Int(2)]
    );
}

#[test]
fn a_shared_tuple_holding_nan_is_not_equal_to_itself_under_the_languages_equality() {
    // `let t = (0.0 / 0.0, 1); t == t` is false, and `t < t` is unordered, though `t` is one
    // shared value; as a key it is the same key as itself.
    let t = Value::tuple(vec![Value::float(f64::NAN), Value::Int(1)]);
    let same = t.clone();
    assert!(!t.surface_eq(&same));
    assert_eq!(t.surface_cmp(&same), None);
    assert_eq!(t, same);
    assert_eq!(t.cmp(&same), std::cmp::Ordering::Equal);
    let program = let_("t", lit(t), eq(var("t"), var("t")));
    assert_eq!(run(&program), Value::Bool(false));
}

#[test]
fn a_part_shared_in_two_places_compares_as_two_copies_do() {
    // `p = (1, -0.0)`; `(p, p)` against `((1, -0.0), (1, -0.0))` built apart.
    let p = Value::tuple(vec![Value::Int(1), Value::float(-0.0)]);
    let shared = Value::tuple(vec![p.clone(), p]);
    let apart = || Value::tuple(vec![Value::Int(1), Value::float(-0.0)]);
    let copies = Value::tuple(vec![apart(), apart()]);
    assert_eq!(shared, copies);
    assert!(shared.surface_eq(&copies));
    let other = Value::tuple(vec![
        apart(),
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
    ]);
    assert_ne!(shared, other);
    assert!(shared < other);
    // Its key makes both zeros positive, in both places.
    let zero = Value::tuple(vec![Value::Int(1), Value::float(0.0)]);
    assert!(!shared.is_key());
    assert_eq!(shared.key(), Value::tuple(vec![zero.clone(), zero]));
}

#[test]
fn a_struct_atom_copied_keeps_its_fields() {
    let a = Value::atom_named(
        "err",
        vec![
            ("code".into(), Value::Int(3)),
            ("at".into(), Value::str("f")),
        ],
    )
    .unwrap();
    let b = a.clone();
    assert_eq!(a, b);
    assert_eq!(b.to_string(), r#"#err(at: "f", code: 3)"#);
}

/// Inputs for `check_order`, built before any timing: `make(n)` and `make(8n)`.
fn built(n: usize, make: impl Fn(usize) -> Term) -> HashMap<usize, Term> {
    [n, 8 * n].into_iter().map(|m| (m, make(m))).collect()
}

#[test]
fn reading_a_tuple_once_per_element_scales() {
    // Each read copied the tuple: 100 reads of an n-tuple took 14.5, 127.6 and 1098 ms at
    // n = 1000, 8000 and 64000 (T11).
    let terms = built(2000, reads);
    check_order("a tuple read once per element, by elements", 2000, 1, |n| {
        run(&terms[&n]);
    });
}

#[test]
fn copying_a_tuple_once_per_element_scales() {
    let tuples: HashMap<usize, Value> = [2000, 16000].map(|n| (n, tuple(n))).into();
    check_order("n copies of a tuple of n, by n", 2000, 1, |n| {
        let t = &tuples[&n];
        let copies: Vec<Value> = (0..n).map(|_| t.clone()).collect();
        assert_eq!(copies.len(), n);
    });
}

#[test]
fn a_list_built_by_an_accumulator_scales() {
    // Each step copied the accumulator: through `zedc run`, 6,400, 12,800 and 25,600 elements
    // took 1.60, 7.77 and 37.13 s (COMPLEXITY.md K21).
    on_large_stack(|| {
        let terms = built(1000, cons_list);
        check_order(
            "a foldl that conses onto its accumulator, by elements",
            1000,
            1,
            |n| {
                run(&terms[&n]);
            },
        );
    });
}

/// `v(0) = bottom`, `v(i + 1) = (v(i), v(i))`: `depth` nodes and `2^depth` paths.
fn doubled(depth: usize, bottom: Value) -> Value {
    (0..depth).fold(bottom, |v, _| Value::tuple(vec![v.clone(), v]))
}

#[test]
fn comparing_and_keying_values_that_share_their_parts_scales() {
    // Read path by path, each walk took time 2^depth: past 60 s at depth 1,000,000.
    let values: HashMap<usize, [Value; 3]> = [5000, 40000]
        .map(|n| {
            let one = doubled(n, Value::Int(1));
            let same = doubled(n, Value::Int(1));
            let zero = doubled(n, Value::float(-0.0));
            (n, [one, same, zero])
        })
        .into();
    check_order(
        "equality, order and keys of shared parts, by depth",
        5000,
        1,
        |n| {
            let [one, same, zero] = &values[&n];
            assert!(one == same);
            assert_eq!(one.cmp(same), std::cmp::Ordering::Equal);
            assert!(one.surface_eq(same));
            assert!(!zero.is_key());
            assert!(zero.key().is_key());
        },
    );
}

#[test]
fn showing_sets_nested_inside_tuples_scales() {
    // `{({(...,)},)}`: each set's member is its own key, so the test that writes a set by its
    // members compares one shared value with itself, O(1) at each level.
    let nest = |d: usize| {
        (0..d).fold(Value::Int(0), |v, _| {
            Value::Family(Family::set([Value::tuple(vec![v])]))
        })
    };
    let values: HashMap<usize, Value> = [2000, 16000].map(|n| (n, nest(n))).into();
    assert_eq!(nest(2).to_string(), "{({(0,)},)}");
    check_order(
        "Display of sets nested inside tuples, by depth",
        2000,
        1,
        |n| {
            assert!(values[&n].to_string().len() > 4 * n);
        },
    );
}

/// `f(0) = bottom`, `f(i + 1) = {x: f(i), y: f(i)}`: a family `depth` levels deep whose levels
/// each hold the one beneath twice, `depth` families and `2^depth` keypaths.
fn doubled_family(depth: usize, bottom: Value) -> Value {
    (0..depth).fold(bottom, |v, _| {
        Value::Family(Family::of([("x", v.clone()), ("y", v)]))
    })
}

#[test]
fn families_built_apart_that_share_their_levels_compare_by_their_leaves() {
    let one = doubled_family(12, Value::Int(1));
    let same = doubled_family(12, Value::Int(1));
    assert!(one == same);
    assert_eq!(one.cmp(&same), std::cmp::Ordering::Equal);
    assert!(one.surface_eq(&same));
    assert_eq!(one.surface_cmp(&same), Some(std::cmp::Ordering::Equal));
    // Unequal at the deepest leaf, which every keypath reaches.
    let two = doubled_family(12, Value::Int(2));
    assert!(one != two);
    assert_eq!(one.cmp(&two), std::cmp::Ordering::Less);
    assert!(!one.surface_eq(&two));
    assert_eq!(two.surface_cmp(&one), Some(std::cmp::Ordering::Greater));
    // `-0.0` and `0.0` are two values, and equal under the language's `==`, at every leaf.
    let neg = doubled_family(12, Value::float(-0.0));
    let pos = doubled_family(12, Value::float(0.0));
    assert!(neg != pos);
    assert_eq!(neg.cmp(&pos), std::cmp::Ordering::Less);
    assert!(neg.surface_eq(&pos));
    // A NaN at the bottom is not equal to itself under `==`, though both are one key.
    let nan = doubled_family(12, Value::float(f64::NAN));
    let nan_again = doubled_family(12, Value::float(f64::NAN));
    assert!(nan == nan_again);
    assert!(!nan.surface_eq(&nan_again));
}

#[test]
fn two_empty_families_are_equal_under_every_relation() {
    let a = Value::Family(Family::new());
    let b = Value::Family(Family::of(Vec::<(i64, i64)>::new()));
    assert!(a == b);
    assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal);
    assert!(a.surface_eq(&b));
    assert_eq!(a.surface_cmp(&b), Some(std::cmp::Ordering::Equal));
    let one = doubled_family(1, Value::Int(1));
    assert!(a != one);
    assert!(a < one);
}

#[test]
fn a_part_compared_inside_two_families_is_read_once_per_comparison() {
    // `{0: t, 1: t, ..., n - 1: t}` for one tuple `t` of n numbers, and `(f, f, ..., f)` for
    // one family `f` of n entries, each built twice apart: n places, one part of size n.
    let wide = |n: usize| {
        let t = tuple(n);
        Value::Family(Family::of((0..n as i64).map(|k| (k, t.clone()))))
    };
    let row = |n: usize| {
        let f = Value::Family(Family::set(0..n as i64));
        Value::tuple(vec![f; n])
    };
    assert!(wide(5) == wide(5));
    assert!(row(5).surface_eq(&row(5)));
    assert_eq!(row(5).surface_cmp(&row(5)), Some(std::cmp::Ordering::Equal));
    // Unequal only in the last entry, whose tuple is one longer.
    let last = Family::of((0..5).map(|k| (k, if k == 4 { tuple(6) } else { tuple(5) })));
    assert!(wide(5) != Value::Family(last));
}

#[test]
fn comparing_families_that_share_their_levels_scales() {
    // With no read set for pairs of families, a comparison read every keypath: 2^depth.
    let values: HashMap<usize, [Value; 4]> = [2000, 16000]
        .map(|n| {
            let one = doubled_family(n, Value::Int(1));
            let same = doubled_family(n, Value::Int(1));
            let neg = doubled_family(n, Value::float(-0.0));
            let pos = doubled_family(n, Value::float(0.0));
            (n, [one, same, neg, pos])
        })
        .into();
    check_order(
        "equality, order and the language's relations of families, by depth",
        2000,
        1,
        |n| {
            let [one, same, neg, pos] = &values[&n];
            assert!(one == same);
            assert_eq!(one.cmp(same), std::cmp::Ordering::Equal);
            assert!(one.surface_eq(same));
            assert_eq!(one.surface_cmp(same), Some(std::cmp::Ordering::Equal));
            assert!(neg != pos);
            assert!(neg.surface_eq(pos));
        },
    );
}

#[test]
fn comparing_one_part_held_in_many_places_scales() {
    let wide = |n: usize| {
        let t = tuple(n);
        Value::Family(Family::of((0..n as i64).map(|k| (k, t.clone()))))
    };
    let row = |n: usize| {
        let f = Value::Family(Family::set(0..n as i64));
        Value::tuple(vec![f; n])
    };
    let values: HashMap<usize, [Value; 4]> = [1000, 8000]
        .map(|n| (n, [wide(n), wide(n), row(n), row(n)]))
        .into();
    check_order(
        "equality of n entries holding one tuple of n, and the language's relations on a \
         tuple of n copies of one family of n, by n",
        1000,
        1,
        |n| {
            let [a, b, c, d] = &values[&n];
            assert!(a == b);
            assert!(c.surface_eq(d));
            assert_eq!(c.surface_cmp(d), Some(std::cmp::Ordering::Equal));
        },
    );
}

/// A copy of `v` that shares no part, each tuple and family built anew.
fn unshared(v: &Value) -> Value {
    match v {
        Value::Tuple(items) => Value::tuple(items.as_slice().iter().map(unshared).collect()),
        Value::Family(f) => {
            Value::Family(Family::of(f.iter().map(|(k, v)| (k.clone(), unshared(v)))))
        }
        _ => v.clone(),
    }
}

#[test]
fn shared_and_unshared_values_compare_alike_under_every_relation() {
    // Every value two levels deep over five leaves, as a tuple or a family of two parts, the
    // two parts one shared value or two; each pair is compared as built and as unshared copies.
    let leaves = [
        Value::Int(1),
        Value::Int(2),
        Value::float(-0.0),
        Value::float(0.0),
        Value::float(f64::NAN),
    ];
    let two = |a: &Value, b: &Value| {
        [
            Value::tuple(vec![a.clone(), b.clone()]),
            Value::Family(Family::of([("x", a.clone()), ("y", b.clone())])),
        ]
    };
    let mut one_level = Vec::new();
    for a in &leaves {
        for b in &leaves {
            one_level.extend(two(a, b));
        }
    }
    let mut values = Vec::new();
    for a in one_level.iter().step_by(3) {
        for b in one_level.iter().step_by(7) {
            values.extend(two(a, b));
        }
        values.extend(two(a, a));
    }
    let copies: Vec<Value> = values.iter().map(unshared).collect();
    let mut differ = 0;
    for (a, ca) in values.iter().zip(&copies) {
        for (b, cb) in values.iter().zip(&copies) {
            assert_eq!(a == b, ca == cb, "{a} and {b}");
            assert_eq!(a.cmp(b), ca.cmp(cb), "{a} and {b}");
            assert_eq!(a.surface_eq(b), ca.surface_eq(cb), "{a} and {b}");
            assert_eq!(a.surface_cmp(b), ca.surface_cmp(cb), "{a} and {b}");
            differ += usize::from(a != b);
        }
    }
    assert!(values.len() > 100 && differ > values.len() * values.len() / 2);
}

#[test]
fn a_part_read_under_two_relations_in_one_comparison_gets_each_answer() {
    // The language's order reads the first part by its float order (equal) and the family's
    // copy of it by the total order (-0.0 before 0.0), in one comparison.
    let t = Value::tuple(vec![Value::float(-0.0)]);
    let u = Value::tuple(vec![Value::float(0.0)]);
    let a = Value::tuple(vec![t.clone(), Value::Family(Family::of([("x", t)]))]);
    let b = Value::tuple(vec![u.clone(), Value::Family(Family::of([("x", u)]))]);
    assert_eq!(a.surface_cmp(&b), Some(std::cmp::Ordering::Less));
    assert_eq!(a.cmp(&b), std::cmp::Ordering::Less);
    assert!(a != b);
    assert!(a.surface_eq(&b));
}

#[test]
fn comparing_families_made_from_one_family_scales() {
    // `h_i = h_0 | {1000 + i: i}` for one family `h_0` of 101 entries, one of them a family `f`
    // of n entries: the n families have n ids but share the map node that holds `f`, so `f` is
    // met n times though it is held in one entry of one map. Each side is built apart.
    let made = |n: usize| {
        let f = Value::Family(Family::set(0..n as i64));
        let h0 =
            Family::of((0..=100i64).map(|k| (k, if k == 0 { f.clone() } else { Value::Int(k) })));
        let h =
            (0..n as i64).map(|i| Value::Family(h0.union(&Family::of([(1000 + i, i)])).unwrap()));
        Value::tuple(h.collect())
    };
    assert!(made(3) == made(3));
    assert_eq!(made(3).cmp(&made(3)), std::cmp::Ordering::Equal);
    let other = |n: usize| {
        let f = Value::Family(Family::set(1..=n as i64));
        let h0 =
            Family::of((0..=100i64).map(|k| (k, if k == 0 { f.clone() } else { Value::Int(k) })));
        Value::tuple(
            (0..n as i64)
                .map(|i| Value::Family(h0.union(&Family::of([(1000 + i, i)])).unwrap()))
                .collect(),
        )
    };
    assert!(made(3) != other(3));
    assert_eq!(made(3).cmp(&other(3)), std::cmp::Ordering::Less);
    assert!(!made(3).surface_eq(&other(3)));
    let values: HashMap<usize, [Value; 2]> = [1000, 8000].map(|n| (n, [made(n), made(n)])).into();
    check_order(
        "equality, order and the language's relations of n families made from one family \
         that holds a family of n, by n",
        1000,
        1,
        |n| {
            let [a, b] = &values[&n];
            assert!(a == b);
            assert_eq!(a.cmp(b), std::cmp::Ordering::Equal);
            assert!(a.surface_eq(b));
            assert_eq!(a.surface_cmp(b), Some(std::cmp::Ordering::Equal));
        },
    );
}
