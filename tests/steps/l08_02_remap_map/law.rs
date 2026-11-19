//! The law that a `map` commutes with a remap that moves only keys: `xs.map(f) as K` equals
//! `(xs as K).map(f)` (sec:remap_law, sec:keypaths: `map` is a `reindex` that keeps every
//! keypath and a key-only remap one that keeps every value, so the two reindexes compose either
//! way to the same leaves). Checked on random two-level families against the M0 model, for a
//! transpose and for a flattening to a tuple key with an affine component. Every draw meets
//! the law, so a draw asserts it whole; the seed is printed and `ZED_TEST_SEED` repeats it.

use std::collections::BTreeSet;

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Family, Prim, Term, Value};
use zed_tests::kernel::*;
use zed_tests::seed::{Rng, seed};

use super::models;

/// Families drawn per run.
const DRAWS: usize = 24;

/// Up to `most` distinct keys from `0..span`, at least one.
fn keys(d: &mut Rng, most: usize, span: i64) -> BTreeSet<i64> {
    let want = 1 + d.below(most);
    let mut ks = BTreeSet::new();
    while ks.len() < want {
        ks.insert(d.int(0, span - 1));
    }
    ks
}

/// A two-level family of int keys and values, as leaves.
fn family(d: &mut Rng) -> Vec<(Vec<Value>, Value)> {
    let mut leaves = Vec::new();
    for p in keys(d, 5, 20) {
        for q in keys(d, 4, 10) {
            let v = d.int(-50, 50);
            leaves.push((vec![Value::Int(p), Value::Int(q)], Value::Int(v)));
        }
    }
    leaves
}

/// The family's display, as a program writes it.
fn display(leaves: &[(Vec<Value>, Value)]) -> String {
    let mut rows: Vec<(String, Vec<String>)> = Vec::new();
    for (path, v) in leaves {
        let (p, q) = (path[0].to_string(), path[1].to_string());
        match rows.last_mut() {
            Some((last, entries)) if *last == p => entries.push(format!("{q} -> {v}")),
            _ => rows.push((p, vec![format!("{q} -> {v}")])),
        }
    }
    let rows = rows
        .iter()
        .map(|(p, es)| format!("{p} -> {{ {} }}", es.join(", ")))
        .collect::<Vec<_>>();
    format!("{{ {} }}", rows.join(", "))
}

/// `v * 3 + 1`.
fn f(v: Term) -> Term {
    add(mul(v, lit(3)), lit(1))
}

#[test]
fn map_commutes_with_a_key_only_remap_on_random_families() {
    let mut d = Rng::new(seed(
        "map_commutes_with_a_key_only_remap_on_random_families",
    ));
    for _ in 0..DRAWS {
        let leaves = family(&mut d);
        let m = || lit(Value::Family(Family::from_leaves(leaves.clone()).unwrap()));
        let src = format!(
            "m = {};\n\
             a = m.map(r -> r.map(v -> v * 3 + 1)) as (p -> q -> v) into (q -> p -> v);\n\
             b = (m as (p -> q -> v) into (q -> p -> v)).map(r -> r.map(v -> v * 3 + 1));\n\
             c = m.map(r -> r.map(v -> v * 3 + 1)) as (p -> q -> v) into ((q, p + 7) -> v);\n\
             d = (m as (p -> q -> v) into ((q, p + 7) -> v)).map(v -> v * 3 + 1);\n",
            display(&leaves)
        );
        let transpose = |t: Term| {
            reindex(
                t,
                func(|[p, _]| path(vec![key(p.clone(), 1), key(p, 0)])),
                func(|[_, v]| v),
            )
        };
        let flatten = |t: Term| {
            reindex(
                t,
                func(|[p, _]| {
                    let pair = vec![key(p.clone(), 1), add(key(p, 0), lit(7))];
                    path(vec![prim(Prim::Tuple, pair)])
                }),
                func(|[_, v]| v),
            )
        };
        models(&src, "a", &transpose(map(m(), f)));
        models(&src, "b", &transpose(map(m(), f)));
        models(&src, "c", &flatten(map(m(), f)));
        models(&src, "d", &flatten(map(m(), f)));
    }
}
