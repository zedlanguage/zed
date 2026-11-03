//! Values far deeper than the minimum of 20,000 nested calls (DESIGN.md step M0.11), each
//! operation run on a thread with the 8 MiB stack of a main thread. Only memory limits the depth
//! of a value, so none of these operations may nest on the thread's stack. This is a test
//! program of its own because it takes many gigabytes at once, which disturbs the timing of
//! the scaling tests beside it.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::sync::LazyLock;

use zed_kernel::term::build::{let_, lit, var};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Family, KernelError, Term, Value, World, eval};
use zed_tests::deep::*;
use zed_tests::kernel::*;

/// The two depths every operation runs at: the minimum, and far past it.
const DEPTHS: [usize; 2] = [20_000, 1_000_000];

/// Three values of one shape and depth; the last differs from the others at the bottom.
struct Deep {
    shape: &'static str,
    one: Value,
    same: Value,
    two: Value,
}

/// Every shape at every depth, built once for the tests that only read them. A nest of families
/// takes far more memory a level, so past the minimum a keypath test below holds it alone and
/// the shape that takes turns holds a quarter of its levels as families.
static BUILT: LazyLock<Vec<Deep>> = LazyLock::new(|| {
    let mut all = Vec::new();
    for depth in DEPTHS {
        for (shape, wrap) in SHAPES {
            if depth > DEPTHS[0] && shape == "families" {
                continue;
            }
            all.push(Deep {
                shape,
                one: nested(wrap, depth, Value::Int(1)),
                same: nested(wrap, depth, Value::Int(1)),
                two: nested(wrap, depth, Value::Int(2)),
            });
        }
    }
    all
});

#[test]
fn equality_and_order_find_a_difference_at_the_bottom() {
    on_main_sized_stack(|| {
        for Deep {
            shape,
            one,
            same,
            two,
        } in &*BUILT
        {
            assert!(one == same, "{shape}");
            assert!(one != two, "{shape}");
            assert_eq!(one.cmp(same), Ordering::Equal, "{shape}");
            assert_eq!(one.cmp(two), Ordering::Less, "{shape}");
            assert_eq!(two.cmp(one), Ordering::Greater, "{shape}");
        }
    });
}

#[test]
fn a_copy_equals_what_it_copied_and_outlives_it() {
    on_main_sized_stack(|| {
        for Deep {
            shape, one, same, ..
        } in &*BUILT
        {
            let copy = one.clone();
            let second = copy.clone();
            drop(copy);
            assert!(second == *same, "{shape}");
        }
    });
}

#[test]
fn printing_shows_every_level() {
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let list = int_list(depth, Value::Int(7));
            let shown = list.to_string();
            assert_eq!(shown.matches('(').count(), depth);
            assert!(shown.starts_with(&format!("({}, (", depth - 1)));
            assert!(shown.ends_with(&format!("(0, 7){}", ")".repeat(depth - 1))));
            let debug = format!("{list:?}");
            assert_eq!(debug.matches("Tuple([").count(), depth);
        }
        for Deep { shape, one, .. } in &*BUILT {
            assert!(!one.to_string().is_empty(), "{shape}");
            assert!(!format!("{one:?}").is_empty(), "{shape}");
        }
    });
}

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
         Atom(Atom { name: \"cons\", fields: [], args: [Int(2)] })])"
    );
    assert_eq!(format!("{:?}", Value::tuple(vec![])), "Tuple([])");
}

#[test]
fn a_key_is_made_from_a_deep_value() {
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let negative = int_list(depth, Value::float(-0.0));
            let positive = int_list(depth, Value::float(0.0));
            assert!(negative != positive);
            assert!(negative.key() == positive.key());
            assert!(positive.is_key());
            assert!(!negative.is_key());
            // A family used as a key, its key the only entry at each level.
            let family = Family::of([(positive, 1)]);
            assert_eq!(family.len(), 1);
            assert_eq!(family.get(&negative), Some(&Value::Int(1)));
        }
    });
}

#[test]
fn surface_equality_follows_numbers_to_the_bottom() {
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let negative = int_list(depth, Value::float(-0.0));
            let positive = int_list(depth, Value::float(0.0));
            let nan = int_list(depth, Value::float(f64::NAN));
            assert!(negative.surface_eq(&positive));
            assert!(!nan.surface_eq(&nan));
            assert_eq!(negative.surface_cmp(&positive), Some(Ordering::Equal));
            assert_eq!(nan.surface_cmp(&nan), None);
            let other = int_list(depth, Value::float(1.0));
            assert_eq!(positive.surface_cmp(&other), Some(Ordering::Less));
        }
    });
}

#[test]
fn a_keypath_a_million_long_is_built_read_and_merged() {
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let path = vec![Value::Int(0); depth];
            let at = |last: i64, leaf: i64| {
                let mut path = path.clone();
                path.push(Value::Int(last));
                Family::from_leaves([(path, Value::Int(leaf))]).unwrap()
            };
            let (left, right) = (at(1, 10), at(2, 20));
            assert_eq!(left.leaves()[0].0.len(), depth + 1);
            let both = left.union(&right).unwrap();
            let leaves: Vec<i64> = both
                .leaves()
                .iter()
                .map(|(_, v)| v.as_int().unwrap())
                .collect();
            assert_eq!(leaves, [10, 20]);
            assert!(left != right && left == at(1, 10));
            assert!(matches!(
                both.union(&at(1, 30)),
                Err(KernelError::Collision { .. })
            ));
        }
    });
}

#[test]
fn membership_of_a_long_list_reads_to_its_end() {
    let list = list_type();
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let good = nested(in_atom, depth, Value::atom("nil"));
            assert!(list.contains(&good));
            assert!(!list.contains(&nested(in_atom, depth, Value::Int(0))));
            let tuples = Type::tuple(vec![Type::int(), Type::top()]);
            assert!(tuples.contains(&int_list(depth, Value::Int(0))));
            assert!(!Type::int().contains(&int_list(depth, Value::Int(0))));
        }
    });
}

#[test]
fn a_program_compares_values_a_million_deep() {
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let (a, b) = (
                int_list(depth, Value::Int(1)),
                int_list(depth, Value::Int(2)),
            );
            let is = |t: Term, want: bool| {
                assert_eq!(eval(&t), Ok(Value::Bool(want)));
            };
            is(eq(lit(a.clone()), lit(a.clone())), true);
            is(eq(lit(a.clone()), lit(b.clone())), false);
            is(lt(lit(a.clone()), lit(b.clone())), true);
            is(lt(lit(b), lit(a)), false);
            let list = linked_list(depth as i64);
            is(let_("x", list, eq(var("x"), var("x"))), true);
        }
    });
}

#[test]
fn a_recursive_program_returns_a_list_and_frees_it() {
    on_main_sized_stack(|| {
        for depth in [140_000, 200_000, 1_000_000] {
            let v = eval(&linked_list(depth)).unwrap();
            assert!(matches!(&v, Value::Tuple(xs) if xs[0] == Value::Int(depth)));
            drop(v);
        }
    });
}

#[test]
fn a_map_holds_deep_keys_in_order() {
    on_main_sized_stack(|| {
        let depth = DEPTHS[1];
        let mut map = BTreeMap::new();
        for bottom in [3, 1, 2] {
            map.insert(int_list(depth, Value::Int(bottom)), bottom);
        }
        let order: Vec<i64> = map.into_values().collect();
        assert_eq!(order, [1, 2, 3]);
    });
}

#[test]
fn the_origin_of_a_failure_is_found_at_the_bottom_of_a_value() {
    on_main_sized_stack(|| {
        for depth in DEPTHS {
            let failure = Value::atom("missing");
            let deep = int_list(depth, failure.clone());
            let mut run = Evaluator::new(World::new()).with_provenance(vec![]);
            assert_eq!(
                run.run(&add(lit(failure), lit(deep))),
                Ok(Value::atom("missing"))
            );
            let trace = run.provenance().unwrap();
            let last = trace.facts().len() - 1;
            assert!(!trace.origins(last).is_empty());
        }
    });
}

/// `v(0) = bottom`, `v(i + 1) = (v(i), v(i))`: `depth` levels, each part shared in two places,
/// so the value has `depth` nodes and `2^depth` paths, as `x = (x, x)` repeated builds it.
fn doubled(depth: usize, bottom: Value) -> Value {
    (0..depth).fold(bottom, |v, _| Value::tuple(vec![v.clone(), v]))
}

#[test]
fn a_value_shared_a_million_levels_deep_is_compared_keyed_and_freed() {
    // Each walk keeps the pairs of shared parts it has read, so each costs O(depth), not
    // O(2^depth), on two such values built apart.
    on_main_sized_stack(|| {
        let depth = DEPTHS[1];
        let one = doubled(depth, Value::Int(1));
        let same = doubled(depth, Value::Int(1));
        let two = doubled(depth, Value::Int(2));
        assert!(one == same);
        assert!(one != two);
        assert_eq!(one.cmp(&two), Ordering::Less);
        assert!(one.surface_eq(&same));
        assert_eq!(one.surface_cmp(&two), Some(Ordering::Less));
        assert!(one.is_key());
        assert!(one.key() == same);
        let negative = doubled(depth, Value::float(-0.0));
        assert!(!negative.is_key());
        assert!(negative.key() == doubled(depth, Value::float(0.0)));
        drop((one, same, two, negative));
    });
}

#[test]
fn a_list_whose_every_tail_is_held_elsewhere_is_freed_from_either_end() {
    on_main_sized_stack(|| {
        let depth = DEPTHS[1];
        let mut tails = Vec::with_capacity(depth);
        let list = (0..depth).fold(Value::Int(0), |rest, k| {
            tails.push(rest.clone());
            in_tuple(rest, k)
        });
        // The list goes first: each tail is still held, so nothing below the top is freed.
        drop(list);
        // The shortest tail first, then the longest first: each frees one level at a time.
        let longest = tails.split_off(depth / 2);
        drop(tails);
        drop(longest.into_iter().rev().collect::<Vec<_>>());
    });
}
