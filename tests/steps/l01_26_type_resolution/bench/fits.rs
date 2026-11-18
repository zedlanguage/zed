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

/// A row of 6 joined components against the 2^m shapes that differ on its last m components,
/// m = 1 to 5, costs a bounded factor of the same rows written out
/// (PERF-types-joined-split-several-differing). The split rows form a binary tree of 2^m
/// leaves, each held whole, and 2^m - 1 inner rows, each tried in the shapes of its bucket
/// before it is split. The shapes are variables, which the filing cannot tell apart. Before
/// PERF-types-variable-shapes-one-bucket each row written out was also searched through the
/// bucket: the fits counted per tuple were 2, 5, 16, 60, 240, 976 and 3968 written out and 5,
/// 17, 60, 225, 874, 3451 and 13724 joined for m = 1 to 7, a ratio of 2.5 to 3.75 that does
/// not grow with m, and the instructions 1.26, 2.02, 2.35, 2.68, 2.99, 3.30 and 3.45 times.
/// Since then a row finds its shape by the pins at all its places, and the instructions are
/// 1.26, 2.09, 2.41, 2.66 and 2.79 times for m = 1 to 5 (load 65); measured, not proved.
#[test]
fn k_joined_components_differing_on_m_components_cost_a_bounded_factor() {
    for m in 1..=5 {
        let alone: Vec<usize> = (6 - m..6).collect();
        let [s, written, joined] = k_joined_rows(20, 6, &alone, false);
        scaling::compare_costs(
            &format!("6 joined components split across 2^{m} shapes, against the rows written out"),
            "the split tree's 2^m - 1 inner rows are each tried in the bucket, as each row \
             written out is searched through it: about 3.5 times the fits for every m; \
             measured 1.26 to 2.99 times the instructions for m = 1 to 5, 3.45 at m = 7",
            3.5,
            || assert!(fits_sig(&s, &written)),
            || assert!(fits_sig(&s, &joined)),
        );
    }
}

/// N = 2^m shapes of variables for each of 2 tuples of 8 components, differing on their last m
/// components, against the same rows written out, N = 16 and 128
/// (PERF-types-variable-shapes-one-bucket). The shapes fall in one bucket, as variables are
/// not filed; a binding pins a shape at each place where its component is one variable bound
/// alone ([`Bound`] in ty.rs), so a row finds the shapes that agree with it at every place
/// pinned by one lookup in each set of places pinned, and tries one shape. Before, a shape was
/// pinned at the first such place only, and row r tried the shapes before it that agree with
/// it there, N²/4 fits for N rows (2, 5, 16, 60, 240, 976, 3968 for N = 2 to 128). Besides its
/// ratio: each form fits at each size. Small instances:
/// `fits::k_joined_components_fit_shapes_that_differ_on_some_of_them`.
#[test]
fn shapes_of_variables_differing_on_m_components_are_found_by_their_pins_scales() {
    let what =
        "N shapes of variables differing on log N of 8 components, against the rows written out";
    let n = 16;
    let sigs: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|n| {
            let m = n.trailing_zeros() as usize;
            (
                n,
                k_joined_rows(2, 8, &(8 - m..8).collect::<Vec<_>>(), false),
            )
        })
        .collect();
    scaling::check_order(what, n, 1, |n| {
        let [s, written, _] = &sigs[&n];
        assert!(fits_sig(s, written), "{what} at {n}");
    });
}

/// The signatures `(x0: shapes) -> int` and `(x0: written) -> int` for `n` shapes of one tuple
/// of 10 components: shape r has one variable at each place whose bit is set in r + 1 and two
/// variables, `X_a | X_b`, at the others, so no two shapes are pinned at the same set of
/// places and each at one place at least; `written` is the same rows of the variables `Y`.
/// (A shape of two variables at every place, with two others after it, is refused: the
/// members that need the later shapes both fail the first, FAIL-types-joined-shape-first.)
fn shapes_at_different_sets_of_places(n: usize) -> [zedc::check::ty::Sig; 2] {
    const K: usize = 10;
    assert!(n < 1 << K);
    let var = |p: &str, r: usize, j: usize, s: usize| {
        Ty::var(format!("{p}{}", (r * K + j) * 2 + s).into())
    };
    let row = |p: &str, r: usize| {
        let cs = (0..K)
            .map(|j| match ((r + 1) >> j) & 1 {
                1 => var(p, r, j, 0),
                _ => var(p, r, j, 0).union(&var(p, r, j, 1)),
            })
            .collect();
        Ty::tuple(cs)
    };
    let rows = |p: &str| {
        (0..n)
            .map(|r| row(p, r))
            .reduce(|a, b| a.union(&b))
            .expect("one shape at least")
    };
    let int = Ty::carrier(Carrier::Int);
    let c = 2 * K * n;
    [
        own_sig("X", c, Some(EVERY), rows("X"), int.clone()),
        own_sig("Y", c, Some(EVERY), rows("Y"), int),
    ]
}

/// N shapes of variables in one bucket, each pinned by the bindings at a different set of its
/// 10 places, against the same rows written out, N = 64 and 512
/// (TEST-types-bound-pin-sets-adversarial). When `Bound` in ty.rs filed a pinned shape by its
/// set of places, a row paid one lookup for each set pinned so far, a number bounded only by
/// the shapes: here row r met r sets, N²/2 lookups in all (16.9 times the instructions at 8n),
/// where [`shapes_of_variables_differing_on_m_components_are_found_by_their_pins_scales`] has
/// the sets fall to one. In its trie a row of fresh variables follows one edge a place.
/// Besides its ratio: the rows fit at each size.
#[test]
fn shapes_pinned_at_n_different_sets_of_places_scale() {
    let what = "N shapes of variables, each pinned at a different set of 10 places, against the \
                rows written out";
    let n = 64;
    let sigs: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, shapes_at_different_sets_of_places(n)))
        .collect();
    scaling::check_order(what, n, 1, |n| {
        let [s, written] = &sigs[&n];
        assert!(fits_sig(s, written), "{what} at {n}");
    });
}

/// [`k_joined_components_differing_on_m_components_cost_a_bounded_factor`] at m = 3, n and 8n
/// tuples: linear in the tuples.
#[test]
fn k_joined_components_split_across_eight_shapes_scales() {
    let what = "n rows of 6 joined components split across eight shapes each";
    let n = 10;
    let sigs: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, k_joined_rows(n, 6, &[3, 4, 5], false)))
        .collect();
    scaling::check_order(what, n, 1, |n| {
        let [s, written, joined] = &sigs[&n];
        assert!(fits_sig(s, written), "{what} at {n}: written out");
        assert!(fits_sig(s, joined), "{what} at {n}: joined");
    });
}
