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

/// PERF-escape-big-heads-scaling: the escape decision on lists whose heads are big integers,
/// `2^64 + k` (distinct hashes) or `2^64 + k (2^61 - 1)` (one residue mod `2^61 - 1`, so one
/// hash). `Heads \ (Avoid_2 | ... | Avoid_m)`, where `Heads` is a list of m cons cells with
/// heads `{b_j, anchor}` and `Avoid_e = cons(int \ {b_e}, Avoid_(e-1))`. Red before the fix
/// (`on_path` in `cells_windows`): 20.2 and 20.3 times the instructions at 8m with distinct
/// hashes (b22-kernel5), the cons cells of `Heads` filling the pair lists of way P.
/// With tied heads the work is O(m log m), not O(m): the head types `{b_j, anchor}` and
/// `int \ {b_e}` all tie in `name_digest`, so the `ByType` maps of `Nodes` keep them in one
/// ordered bucket of about 2m types (`TiedMap`, PERF-typeset-tied-digest), `O(log m)`
/// comparisons of keys of two values for each of the O(m) lookups. An n log n ratio meets
/// 10.5 only from n = 777 (COMPLEXITY.md, the scaling limit), so the sizes are 1024 and 8192:
/// at 128 and 1024 the tied variant measured 11.50 times the instructions (callgrind:
/// `BigInt::cmp` 12.05 times, against 8 ln 2048 / ln 256 = 11.0 for the bucket), 8.28 untied.
/// The operation count that bounds the tied ratio at 1024 by 10.18 is at `decide_counted`
/// (escape.rs, PROOF-escape-tied-log-only); `the_big_heads_family_reads_its_cells_in_its_size`
/// checks the cell count it starts from.
/// Measured with `TreapSet`'s `==` on inline stacks (TREAP-eq-alloc; b22-free2 prof19 on a
/// Colab VM, 2026-11-25, debug build, m = 1024 and 8192, before 72c01321c ordered the hash-cons
/// buckets by the forms as held): tied, 509.3M and 5119.9M instructions (10.05) and 19.12M and
/// 152.20M bytes (7.96); untied, 181.0M and 1540.9M (8.52) and 19.87M and 158.80M bytes (7.99);
/// a release build, 10.08 tied and 8.55 untied. The cost `m (a + b log2 m)` fitted at m = 1024,
/// 2048 and 4096 predicts 10.30 at 8192; the bytes, about 18.6K a head, predict 8.0.
#[test]
fn the_escape_decision_on_lists_of_big_integers_scales() {
    use crate::scaling;
    use crate::types::Type;

    let n = 1024;
    for tied in [false, true] {
        let types = scaling::inputs(n, |m| big_heads(m, tied));
        let what = format!("the escape decision on lists of big integers (tied: {tied}), by heads");
        scaling::check(&what, n, |m| {
            Type::forget_emptiness();
            assert!(!types[&m].is_empty());
        });
    }
}

/// FAIL-main-escape-input-build: building the tied family of
/// [`the_escape_decision_on_lists_of_big_integers_scales`] ([`big_heads`]) at `m` = 1024 and 8192.
/// Each of the O(m) literal sets the build makes passes through the thread's `HashConsTable`
/// in `Type::new` (TYPE-hashcons, ce49a6c44), and every set of these heads had one seeded sum, so
/// one bucket. With the bucket a list of weak handles, each set scanned it, `O(m^2)`: the
/// build at 1024 took 332,096,696 instructions at 0d00d5daa, before ce49a6c44, and 1,712,314,013
/// at f7b931553, and the bisect between them (one VM, DynamoRIO's `zed_icount`, b22-free2,
/// 2026-11-25) named ce49a6c44 as the first commit over their geometric mean. The bucket is now
/// ordered, `O(log m)` comparisons a set, `O(m log m)`; an n log n ratio meets 10.5 from n = 777
/// (COMPLEXITY.md), so the sizes are 1024 and 8192.
#[test]
fn building_the_tied_big_heads_family_scales() {
    crate::scaling::check_order_fresh(
        "building the escape family of lists of tied big integers, by heads",
        1024,
        1,
        |m, _| m,
        |_, m| big_heads(m, true),
    );
}

/// The family of [`the_escape_decision_on_lists_of_big_integers_scales`] at `m` cons cells:
/// `Heads \ (Avoid_2 | ... | Avoid_m)`, heads `b_j = 2^64 + j s` with `s = 2^61 - 1` when
/// `tied` (one residue mod `2^61 - 1`, so one hash) and `s = 1` otherwise, and `anchor = b_(m+1)`.
fn big_heads(m: usize, tied: bool) -> crate::types::Type {
    use crate::types::Type;
    use crate::types::rec::{Def, Expr as RecExpr, Group};

    let step: BigInt = match tied {
        true => (BigInt::from(1u8) << 61u32) - 1u8,
        false => BigInt::from(1u8),
    };
    let base: BigInt = BigInt::from(1u8) << 64u32;
    let big = |k: usize| Type::lit(&Value::int(&base + &step * (k as u64 + 1))).expect("a literal");
    let anchor = big(m + 2);
    let nil = || RecExpr::Type(Type::atom("nil"));
    let cons = |h: RecExpr, next: RecExpr| RecExpr::Atom("cons".into(), vec![h, next]);
    let mut defs = vec![Def {
        name: "Ints".into(),
        params: vec![],
        body: RecExpr::Union(vec![
            nil(),
            cons(RecExpr::Type(Type::int()), RecExpr::Ref(0, vec![])),
        ]),
    }];
    for e in 1..=m {
        let head = &Type::int() - &if e == 1 { anchor.clone() } else { big(e) };
        defs.push(Def {
            name: format!("Avoid{e}"),
            params: vec![],
            body: cons(RecExpr::Type(head), RecExpr::Ref(e - 1, vec![])),
        });
    }
    let mut list = nil();
    for j in (1..=m).rev() {
        list = cons(RecExpr::Type(&big(j) | &anchor), list);
    }
    defs.push(Def {
        name: "Heads".into(),
        params: vec![],
        body: list,
    });
    let ts = Group::new(defs).expect("a group").instance(vec![]);
    let avoided = (2..=m).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[m + 1] - &avoided
}

/// PROOF-escape-tied-log-only: the first step of the count at `decide_counted`. The escape
/// decision decides the family (the search is not reached), and the cells it reads, tied or not,
/// are the same number, linear in `m`: refused row `e` (`Avoid_e`) meets `Heads` in the atom
/// `{anchor}` at place `e` and, when `e` is odd, in `{b_j}` at place `j = (e + 1) / 2`, so
/// `(m - 1) + (m - 1) / 2` cells, none empty. The count holds from `m = 12`: a sweep of every m
/// from 2 to 160, tied and untied (b22-kernel8, 2026-11-23), found it at 2, 3 and each m from 12
/// to 160, and not at each m from 4 to 11, where a window prices the pair listing's method A
/// cheaper and A reads empty cells too ((6, 2) at 4, (19, 9) at 8, (22, 7) at 11). So the sizes
/// are the first two from 12, two between, and the bench's 1024. A pin of the proof's premise.
#[test]
fn the_big_heads_family_reads_its_cells_in_its_size() {
    for m in [12usize, 13, 64, 160, 1024] {
        let counts: Vec<(usize, usize)> = [false, true]
            .into_iter()
            .map(|tied| {
                let t = big_heads(m, tied);
                assert!(
                    matches!(super::decide(&t), Some(super::ChainPlan::Inhabited { .. })),
                    "m = {m}, tied: {tied}"
                );
                super::cell_counts(&t)
            })
            .collect();
        assert_eq!(counts[0], counts[1], "m = {m}: tied and untied read alike");
        assert_eq!(counts[0], ((m - 1) + (m - 1) / 2, 0), "m = {m}");
    }
}
