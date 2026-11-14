//! Values nested a few levels deep: compared, copied, printed, made keys, read by surface
//! equality, used as keypaths, tested for membership, compared by a program, built by a
//! recursion, ordered in a map, traced, shared at every level and freed from either end. The
//! same values past the minimum of 20,000 nested calls (DESIGN.md step M0.11) are in
//! `bench/deep_values.rs`, a module of this program because they take many gigabytes at once.

#[path = "bench/deep_values.rs"]
mod bench;

use std::cmp::Ordering;
use std::collections::BTreeMap;

use zed_kernel::term::build::{let_, lit, var};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Family, KernelError, Value, World, eval};
use zed_tests::deep::*;
use zed_tests::kernel::*;

#[test]
fn printing_a_shallow_value_is_as_it_was() {
    let v = Value::tuple(vec![
        Value::Int(1),
        Value::path(vec![Value::str("a"), Value::Bool(true)]),
        Value::atom_with("cons", vec![Value::Int(2)]),
    ]);
    assert_eq!(v.to_string(), "(1, [\"a\" -> true], #cons(2))");
    assert_eq!(
        format!("{v:?}"),
        "Tuple([Int(1), Path([Str(\"a\"), Bool(true)]), \
         Atom(Atom { name: \"cons\", fields: [], payload: Some([Int(2)]) })])"
    );
    assert_eq!(format!("{:?}", Value::tuple(vec![])), "Tuple([])");
}

/// Each check of `bench/deep_values.rs` at depths 1, 2 and 9, on the default stack.
#[test]
fn each_operation_on_a_value_a_few_levels_deep() {
    for depth in [1, 2, 9] {
        for (shape, wrap) in SHAPES {
            let (one, same, two) = (
                nested(wrap, depth, Value::Int(1)),
                nested(wrap, depth, Value::Int(1)),
                nested(wrap, depth, Value::Int(2)),
            );
            assert!(one == same && one != two, "{shape}");
            assert_eq!(one.cmp(&two), Ordering::Less, "{shape}");
            assert_eq!(two.cmp(&one), Ordering::Greater, "{shape}");
            let copy = one.clone();
            let second = copy.clone();
            drop(copy);
            assert!(second == same, "{shape}");
            assert!(!format!("{one:?}").is_empty(), "{shape}");
        }

        let shown = int_list(depth, Value::Int(7)).to_string();
        assert_eq!(shown.matches('(').count(), depth);
        assert!(shown.ends_with(&format!("(0, 7){}", ")".repeat(depth - 1))));
        let debug = format!("{:?}", int_list(depth, Value::Int(7)));
        assert_eq!(debug.matches("Tuple([").count(), depth);

        let negative = int_list(depth, Value::float(-0.0));
        let positive = int_list(depth, Value::float(0.0));
        let nan = int_list(depth, Value::float(f64::NAN));
        assert!(negative != positive && negative.key() == positive.key());
        assert!(positive.is_key() && !negative.is_key());
        let family = Family::of([(positive.clone(), 1)]);
        assert_eq!(family.get(&negative), Some(&Value::Int(1)));
        assert!(negative.surface_eq(&positive) && !nan.surface_eq(&nan));
        assert_eq!(nan.surface_cmp(&nan), None);
        let other = int_list(depth, Value::float(1.0));
        assert_eq!(positive.surface_cmp(&other), Some(Ordering::Less));

        let at = |last: i64, leaf: i64| {
            let mut path = vec![Value::Int(0); depth];
            path.push(Value::Int(last));
            Family::from_leaves([(path, Value::Int(leaf))]).unwrap()
        };
        let both = at(1, 10).union(&at(2, 20)).unwrap();
        assert_eq!(both.leaves().len(), 2);
        assert_eq!(at(1, 10).leaves()[0].0.len(), depth + 1);
        assert!(matches!(
            both.union(&at(1, 30)),
            Err(KernelError::Collision { .. })
        ));

        assert!(list_type().contains(&nested(in_atom, depth, Value::atom("nil"))));
        assert!(!list_type().contains(&nested(in_atom, depth, Value::Int(0))));
        let tuples = Type::tuple(vec![Type::int(), Type::top()]);
        assert!(tuples.contains(&int_list(depth, Value::Int(0))));

        let (a, b) = (
            int_list(depth, Value::Int(1)),
            int_list(depth, Value::Int(2)),
        );
        assert_eq!(
            eval(&lt(lit(a.clone()), lit(b.clone()))),
            Ok(Value::Bool(true))
        );
        assert_eq!(eval(&eq(lit(a), lit(b))), Ok(Value::Bool(false)));
        let list = linked_list(depth as i64);
        assert_eq!(
            eval(&let_("x", list, eq(var("x"), var("x")))),
            Ok(Value::Bool(true))
        );
        let v = eval(&linked_list(depth as i64)).unwrap();
        assert!(matches!(&v, Value::Tuple(xs) if xs[0] == Value::Int(depth as i64)));

        let mut map = BTreeMap::new();
        for bottom in [3, 1, 2] {
            map.insert(int_list(depth, Value::Int(bottom)), bottom);
        }
        assert_eq!(map.into_values().collect::<Vec<_>>(), [1, 2, 3]);

        let failure = Value::atom("missing");
        let mut run = Evaluator::new(World::new()).with_provenance(vec![]);
        let deep = int_list(depth, failure.clone());
        assert_eq!(
            run.run(&add(lit(failure), lit(deep))),
            Ok(Value::atom("missing"))
        );
        let trace = run.provenance().unwrap();
        assert!(!trace.origins(trace.facts().len() - 1).is_empty());

        let doubled =
            |bottom: Value| (0..depth).fold(bottom, |v, _| Value::tuple(vec![v.clone(), v]));
        let (one, two) = (doubled(Value::Int(1)), doubled(Value::Int(2)));
        assert!(one == doubled(Value::Int(1)) && one < two && one.is_key());
        assert!(doubled(Value::float(-0.0)).key() == doubled(Value::float(0.0)));

        let mut tails = Vec::new();
        let list = (0..depth).fold(Value::Int(0), |rest, k| {
            tails.push(rest.clone());
            in_tuple(rest, k)
        });
        drop(list);
        let longest = tails.split_off(depth / 2);
        drop(tails);
        drop(longest.into_iter().rev().collect::<Vec<_>>());
    }
}
