//! The metatheory smoke cases (DESIGN.md sec:kernel, "Metatheory targets"): each target the
//! M0.9 evaluator can execute, run on finite models. Keypath uniqueness and progress with
//! preservation get one case per data generator (reindex, discard, fold); confluence is run
//! over permuted arrival orders here and over schedules in `recursion`. Termination of the
//! canonicalization rewrites waits for the rewrites themselves (step L5), and the dependency
//! theorem's agreement across schedules is `recursion`.

use std::cell::Cell;
use std::collections::BTreeMap;

use zed_kernel::term::build::lit;
use zed_kernel::{Family, KernelError, Prim, Term, Value, eval};
use zed_tests::check::property;
use zed_tests::kernel::*;

use super::{IntMap, int_maps, ints};

/// A key map of a one-level integer family, as a term and as the Rust function it computes.
struct KeyMap {
    name: &'static str,
    term: fn(Term, Term) -> Term,
    rust: fn(i64, i64) -> i64,
}

/// Key maps from the witness catalog (strictly monotone arithmetic) and outside it, the
/// last three not injective on every family.
fn key_maps() -> Vec<KeyMap> {
    vec![
        KeyMap {
            name: "k + 1",
            term: |k, _| add(k, lit(1)),
            rust: |k, _| k + 1,
        },
        KeyMap {
            name: "2k",
            term: |k, _| mul(k, lit(2)),
            rust: |k, _| 2 * k,
        },
        KeyMap {
            name: "3k - 5",
            term: |k, _| sub(mul(k, lit(3)), lit(5)),
            rust: |k, _| 3 * k - 5,
        },
        KeyMap {
            name: "k div 2",
            term: |k, _| idiv(k, lit(2)),
            rust: |k, _| k.div_euclid(2),
        },
        KeyMap {
            name: "v",
            term: |_, v| v,
            rust: |_, v| v,
        },
        KeyMap {
            name: "k mod 3",
            term: |k, _| modulo(k, lit(3)),
            rust: |k, _| k.rem_euclid(3),
        },
    ]
}

#[test]
fn keypath_uniqueness_a_reindex_never_merges_and_collides_exactly_when_its_map_does() {
    // Well-typedness implies unique keypaths, carried by T-Reindex: a reindex either returns
    // a family with one entry per source entry or is a collision, and it is a collision
    // exactly when the key map sends two source keys to one. The source keys being distinct
    // does not prevent that, which is why injectivity is the rule's premise.
    let (kept, collided) = (Cell::new(0), Cell::new(0));
    for km in key_maps() {
        property(int_maps(31), |m: &IntMap| {
            let t = reindex(
                ints(m),
                func(|[p, v]| path(vec![(km.term)(key(p, 0), v)])),
                func(|[_, v]| v),
            );
            let image: BTreeMap<i64, i64> = m.iter().map(|&(k, v)| ((km.rust)(k, v), v)).collect();
            match eval(&t) {
                Ok(Value::Family(f)) if image.len() == m.len() => {
                    kept.set(kept.get() + 1);
                    let want = Family::of(image);
                    (f == want).then_some(()).ok_or(format!("{}: {f}", km.name))
                }
                Err(KernelError::Collision { .. }) if image.len() < m.len() => {
                    collided.set(collided.get() + 1);
                    Ok(())
                }
                other => Err(format!(
                    "{}: {other:?} with {} image keys",
                    km.name,
                    image.len()
                )),
            }
        });
    }
    let (kept, collided) = (kept.get(), collided.get());
    assert!(kept > 0 && collided > 0, "{kept} kept, {collided} collided");
}

#[test]
fn progress_and_preservation_for_discard_a_well_typed_filter_returns_a_subfamily() {
    // A selector returning a bool on every entry: the result is a value, and it is the
    // sub-family of the entries whose verdict is true.
    for c in -2..=2 {
        property(int_maps(32), |m: &IntMap| {
            let t = discard_with(ints(m), |_, v| lt(lit(c), v));
            let want: IntMap = m.iter().copied().filter(|&(_, v)| c < v).collect();
            let got = eval(&t).map_err(|e| format!("{e:?}"))?;
            (got == eval(&ints(&want)).unwrap())
                .then_some(())
                .ok_or(format!("threshold {c}: {got}"))
        });
    }
}

#[test]
fn progress_and_preservation_for_fold_an_operator_with_its_identity_returns_a_scalar() {
    // Sum, max and min over every map: an int, and the identity on the empty map. Without an
    // identity the empty map folds to `#empty`, a value, never a stuck term.
    type Op = (Prim, i64, fn(i64, i64) -> i64);
    let ops: [Op; 3] = [
        (Prim::Add, 0, |a, b| a + b),
        (Prim::Max, i64::MIN, i64::max),
        (Prim::Min, i64::MAX, i64::min),
    ];
    for (p, e, f) in ops {
        property(int_maps(33), |m: &IntMap| {
            let with = eval(&fold(ints(m), Term::PrimFn(p), Some(lit(e))));
            let want = m.iter().map(|&(_, v)| v).fold(e, f);
            if with != Ok(Value::Int(want)) {
                return Err(format!("{p:?} with identity: {with:?}"));
            }
            let without = eval(&fold(ints(m), Term::PrimFn(p), None));
            let want = if m.is_empty() {
                Value::atom("empty")
            } else {
                Value::Int(want)
            };
            (without == Ok(want))
                .then_some(())
                .ok_or(format!("{p:?}: {without:?}"))
        });
    }
}

/// Every permutation of `xs`, in lexicographic order of positions.
fn permutations<T: Clone>(xs: &[T]) -> Vec<Vec<T>> {
    if xs.len() <= 1 {
        return vec![xs.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..xs.len() {
        let mut rest = xs.to_vec();
        let x = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, x.clone());
            out.push(p);
        }
    }
    out
}

#[test]
fn confluence_a_pure_pipeline_gives_one_result_for_every_arrival_order() {
    // Sales arrive in any order; revenue by region is grouped and summed in floats, whose
    // canonical tree follows key order, so all 120 arrival orders of five sales agree to the
    // bit.
    let sales = [
        (1, "east", 0.1),
        (2, "west", 0.2),
        (3, "east", 0.3),
        (4, "east", 1e16),
        (5, "west", -0.0),
    ];
    let pipeline = |order: &[(i64, &str, f64)]| {
        let f = Family::of(
            order
                .iter()
                .map(|&(id, r, x)| (Value::Int(id), Value::Tuple(vec![s(r), Value::float(x)]))),
        );
        let by_region = group_by(lit(Value::Family(f)), |v| nth(v, 0));
        let amounts = reindex(by_region, func(|[p, _]| p), func(|[_, v]| nth(v, 1)));
        eval(&fold_at(amounts, 2, Term::PrimFn(Prim::Add), None)).unwrap()
    };
    let first = pipeline(&sales);
    let n = property(permutations(&sales), |order| {
        let got = pipeline(order);
        (got == first).then_some(()).ok_or(format!("{got}"))
    });
    assert_eq!(n, 120);
    // And the result is the exact sums, rounded once: 0.1 + 0.3 + 1e16 and 0.2 + -0.0.
    assert_eq!(
        first.to_string(),
        r#"{"east" -> 10000000000000000.0, "west" -> 0.2}"#
    );
}
