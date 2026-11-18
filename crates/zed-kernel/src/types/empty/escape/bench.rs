//! The benchmark of the escape solve's maps keyed by `Value`, run by `tools/run_tests.sh --bench`
//! and left out of its default run (TEST-bench-move-crates). What it checks besides the ratio,
//! that equal integers built two ways are one key and the parents come out right, is checked at
//! small sizes by `forest_tests` in `escape.rs`.

use std::collections::BTreeSet;

use num_bigint::BigInt;

use super::forest;
use super::forest_tests::{cofinite, finite};
use crate::value::Value;

/// Plan row PERF-value-key-sites-bench: [`forest`] over n finite atoms `{x_k, y_k}` and n
/// singletons `{x_k}`, under one cofinite atom that leaves out n other integers, half the values
/// 64-bit and half past 64 bits. `first_out` takes n keys and `owner` 2n, each found or missed by
/// one hash and O(1) expected compares, and the atoms are sorted, so O(n log n) in all. Each
/// singleton's parent is its pair, and each pair's the cofinite atom. The value sets are built
/// before timing; an atom (`Ints`) holds an `Rc`, which a timed run, shared between threads, may
/// not, so the run builds the atoms from the sets, O(n) hashes, below the forest's sort.
#[test]
fn the_forest_of_atoms_of_wide_and_small_integers_scales() {
    let int = |k: usize| -> Value {
        let k = k as i64;
        match k % 2 {
            0 => Value::Int(k),
            _ => Value::int(BigInt::from(u64::MAX) * 4 + k),
        }
    };
    let inputs = crate::scaling::inputs(20_000, |n| {
        let mut sets: Vec<(bool, BTreeSet<Value>)> =
            vec![(true, (0..n).map(|k| int(4 * k + 3)).collect())];
        sets.extend((0..n).map(|k| (false, [int(4 * k), int(4 * k + 1)].into())));
        sets.extend((0..n).map(|k| (false, [int(4 * k)].into())));
        sets
    });
    crate::scaling::check_order(
        "the forest of n pairs and n singletons of integers under one cofinite atom",
        20_000,
        1,
        |n| {
            let atom: Vec<_> = (inputs[&n].iter())
                .map(|(cof, vals)| match cof {
                    true => (0, cofinite(vals.iter().cloned())),
                    false => (0, finite(vals.iter().cloned())),
                })
                .collect();
            let list: Vec<usize> = (0..atom.len()).collect();
            let mut parent = vec![None; atom.len()];
            assert_eq!(forest(&list, &atom, &mut parent), Some(()));
            assert_eq!(parent[1], Some(0));
            assert_eq!(parent[1 + n], Some(1));
            assert_eq!(parent[2 * n], Some(n));
        },
    );
}
