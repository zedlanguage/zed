use std::collections::BTreeMap;

use zed_kernel::Value;
use zed_tests::scaling;
use zedc::check::ty::{Carrier, EVERY, Ty, fits_sig};

use super::super::fits::{k_joined_rows, own_sig};

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

/// n shapes `(X_i,)` against themselves renamed `(Y_i,)`, written out and as the one joined
/// tuple `(Y_0 | … | Y_{n-1},)`, every variable bounded to several carriers, so each `X_i`
/// holds `Y_i` alone: each member passes the one shape bound before it and is held by the next,
/// later members skipping the shapes pinned by their bindings, so the whole is n log n. Before
/// (FAIL-types-bounded-shapes-renamed-refused) the third member was refused. Besides its
/// ratio: the function fits at each size. Small instance:
/// `fits::three_shapes_of_bounded_variables_fit_themselves_renamed`.
#[test]
fn n_bounded_shapes_fit_themselves_renamed_scales() {
    let what = "n shapes of bounded variables against themselves renamed, written out and joined";
    let make = |n: usize| {
        let union = |ts: Vec<Ty>| ts.into_iter().reduce(|a, b| a.union(&b)).unwrap();
        let var = |p: &str, i: usize| Ty::var(format!("{p}{i}").into());
        let split = |p: &str| union((0..n).map(|i| Ty::tuple(vec![var(p, i)])).collect());
        let joined = Ty::tuple(vec![union((0..n).map(|i| var("Y", i)).collect())]);
        let int = Ty::carrier(Carrier::Int);
        let s = own_sig("X", n, Some(EVERY), split("X"), int.clone());
        let q = own_sig("Y", n, Some(EVERY), split("Y"), int.clone());
        let j = own_sig("Y", n, Some(EVERY), joined, int);
        (s, q, j)
    };
    let n = 1000;
    let sigs: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, make(n)))
        .collect();
    scaling::check_order(what, n, 1, |n| {
        let (s, q, j) = &sigs[&n];
        assert!(fits_sig(s, q), "{what} at {n}: written out");
        assert!(fits_sig(s, j), "{what} at {n}: joined");
    });
}

/// n tuples, each a row of k joined components (k = 2, 3, 4) against the two shapes that
/// hold it only split at its last component, and the same rows written out: the joined form
/// is split at the component the shapes differ on ([`Comparing::split_at`] in ty.rs), so it
/// makes 2 rows for each tuple, where splitting at the first joined component made 2^k
/// (PERF-types-joined-split-many-components: 2.4, 4.4, 8.2 and 15.4 times the work of the
/// rows written out for k = 2 to 5 before; 1.6 after, for each k). Besides its ratio: each
/// form fits at each size. Small instances:
/// `fits::k_joined_components_fit_shapes_that_differ_on_some_of_them`.
#[test]
fn k_joined_components_split_where_the_shapes_differ_scales() {
    for k in 2..=4 {
        let what = format!("n rows of {k} joined components split across two shapes each");
        let n = 100;
        let sigs: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|n| (n, k_joined_rows(n, k, &[k - 1], false)))
            .collect();
        scaling::check_order(&what, n, 1, |n| {
            let [s, written, joined] = &sigs[&n];
            assert!(fits_sig(s, written), "{what} at {n}: written out");
            assert!(fits_sig(s, joined), "{what} at {n}: joined");
        });
    }
}

/// The joined rows of `k_joined_components_split_where_the_shapes_differ_scales` at k = 4
/// cost at most twice the rows written out: each joined row costs its failed search, the
/// shapes tried compared once more to find the component to split at, and the 2 rows written
/// out (measured 1.66). Before the split at the component the shapes differ on, 8.2.
#[test]
fn k_joined_components_cost_at_most_twice_the_rows_written_out() {
    let [s, written, joined] = k_joined_rows(100, 4, &[3], false);
    scaling::compare_costs(
        "4 joined components against the same rows written out, 100 tuples",
        "a joined row costs its failed search, one comparison more and its 2 split rows; \
         measured 1.66, 8.2 before PERF-types-joined-split-many-components",
        2.0,
        || assert!(fits_sig(&s, &written)),
        || assert!(fits_sig(&s, &joined)),
    );
}
