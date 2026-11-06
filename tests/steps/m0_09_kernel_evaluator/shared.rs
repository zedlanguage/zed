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
