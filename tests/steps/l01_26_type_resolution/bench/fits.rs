use std::collections::BTreeMap;

use zed_kernel::Value;
use zed_tests::scaling;
use zedc::check::ty::{Carrier, EVERY, Ty, fits_sig};

use super::super::fits::own_sig;

/// n tuples `(Y(2i) | Y(2i+1), i)`, each split across the shapes `(X(2i), i) | (X(2i+1), i)`,
/// the variables bounded to several carriers, so no one shape holds a tuple: each split costs
/// its two pieces, each found by the lookup on the key `i`, so the whole is linear. Besides its
/// ratio: the function fits at each size. Small instance:
/// `fits::a_joined_tuple_gets_the_verdict_of_its_split_union` (one key).
#[test]
fn a_joined_component_split_across_shapes_scales() {
    let what = "n tuples with a component of two variables, each split across two shapes";
    let make = |n: usize| {
        let key = |i: usize| Ty::lit(&Value::int((i as i64).into()));
        let x = |i: usize| Ty::var(format!("X{i}").into());
        let y = |i: usize| Ty::var(format!("Y{i}").into());
        let union = |ts: Vec<Ty>| ts.into_iter().reduce(|a, b| a.union(&b)).unwrap();
        let split = union(
            (0..2 * n)
                .map(|j| Ty::tuple(vec![x(j), key(j / 2)]))
                .collect(),
        );
        let joined = union(
            (0..n)
                .map(|i| Ty::tuple(vec![y(2 * i).union(&y(2 * i + 1)), key(i)]))
                .collect(),
        );
        let int = Ty::carrier(Carrier::Int);
        (
            own_sig("X", 2 * n, Some(EVERY), split, int.clone()),
            own_sig("Y", 2 * n, Some(EVERY), joined, int),
        )
    };
    let n = 300;
    let sigs: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, make(n)))
        .collect();
    scaling::check_order(what, n, 1, |n| {
        let (s, q) = &sigs[&n];
        assert!(fits_sig(s, q), "{what} at {n}");
    });
}
