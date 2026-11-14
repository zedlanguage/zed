//! The benchmarks of `rec.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `rec.rs`.

use super::*;

/// Writing an irregular occurrence whose argument is `d` levels deep, a function's result, a
/// tuple component and a member of a union in turn, decides each part's parentheses once.
#[test]
fn writing_an_irregular_occurrence_scales_with_its_depth() {
    let a = || Expr::Param(0);
    let arg = |d: usize| {
        (0..d).fold(a(), |x, k| match k % 3 {
            0 => Expr::exact(a(), x),
            1 => Expr::Tuple(vec![x, a()]),
            _ => or(vec![x, bare("x")]),
        })
    };
    let nest = |d: usize| {
        def(
            "Nest",
            &["A"],
            or(vec![
                atom("leaf", vec![a()]),
                atom("node", vec![r(0, vec![arg(d)])]),
            ]),
        )
    };
    assert!(rejected(vec![nest(3)]).contains("`Nest(((A) -> A, A) | #x)`"));
    zed_tests::scaling::check("writing an irregular occurrence, by depth", 200, |d| {
        assert!(!rejected(vec![nest(d)]).is_empty());
    });
}

#[test]
fn recursive_definitions_scale() {
    // The check for contractiveness searched from each definition in turn, so a chain of `d`
    // definitions took `O(d²)` steps (ratio 31); one pass of Tarjan's components now finds
    // the cycles. A body nested `d` deep had each part kept unevaluated copied, walked for
    // recursive occurrences and named in full, and an atom's payload was copied to test a
    // value, each once per level: `O(d²)` (ratio 68). The body is now a shared tree whose
    // nodes know whether they mention the group, a part's name is made when it is printed,
    // and a payload is tested in place. Unfolding the chain dominates its time, so the checks
    // made when the definitions are given are also timed alone, on a longer chain.
    use zed_tests::scaling;
    fn chain(d: usize) -> Vec<Def> {
        (0..d)
            .map(|i| {
                let body = if i + 1 < d {
                    or(vec![r(i + 1, vec![]), bare(&format!("a{i}"))])
                } else {
                    bare("end")
                };
                def(&format!("T{i}"), &[], body)
            })
            .collect()
    }
    std::thread::Builder::new()
        .spawn(|| {
            scaling::check("chain of definitions", 100, |d| {
                let t = one(chain(d));
                assert!(t.contains(&Value::atom("end")));
            });
            scaling::check("checking a chain of definitions", 1000, |d| {
                assert!(Group::new(chain(d)).is_ok());
            });
            scaling::check("nested body", 100, |d| {
                let mut body = Expr::Tuple(vec![r(0, vec![]), ty(Type::int())]);
                for _ in 0..d {
                    body = atom("n", vec![body]);
                }
                let t = one(vec![def("T", &[], or(vec![body, bare("z")]))]);
                let mut v = Value::tuple(vec![Value::atom("z"), Value::Int(1)]);
                for _ in 0..d {
                    v = Value::atom_with("n", vec![v]);
                }
                assert!(t.contains(&v));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A value `d` levels deep whose two halves are one shared value at every level has `2^d`
/// paths and `d` sequences; membership tests each sequence once, by its id, so the work is of
/// order `d`. Without the kept tests it is of order `2^d` and does not end at depth 512.
#[test]
fn membership_of_a_value_whose_halves_share_scales() {
    let t = tree().instance(vec![Type::int()]).remove(0);
    let shared = |d: usize, x: Value| (0..d).fold(x, |v, _| fork(v.clone(), v));
    let built: std::collections::HashMap<usize, (Value, Value)> = [64, 512]
        .into_iter()
        .map(|d| {
            let good = shared(d, leaf(Value::Int(1)));
            let bad = shared(d, leaf(Value::str("x")));
            (d, (good, bad))
        })
        .collect();
    zed_tests::scaling::check(
        "membership of a value whose halves share, by depth",
        64,
        |d| {
            let (good, bad) = &built[&d];
            assert!(t.contains(good));
            assert!(!t.contains(bad));
        },
    );
}

/// `type X = #nil | #cons(int, X) | #cons(int, Y)`, and `Y` the same: each item of a list may
/// be read under either definition, so a list of `l` ints has `2^l` readings. Each tail is
/// tested once under each of the two definitions, so membership is of order `l`. A list of
/// ints that ends in a string, not in `#nil`, is in neither, and every reading must be refuted.
#[test]
fn membership_in_two_mutual_definitions_scales() {
    let body = || {
        or(vec![
            bare("nil"),
            atom("cons", vec![ty(Type::int()), r(0, vec![])]),
            atom("cons", vec![ty(Type::int()), r(1, vec![])]),
        ])
    };
    let t = one(vec![def("X", &[], body()), def("Y", &[], body())]);
    let ending = |l: usize, end: Value| {
        (0..l).fold(end, |v, i| {
            Value::atom_with("cons", vec![Value::Int(i as i64), v])
        })
    };
    assert!(t.contains(&ending(5, Value::atom("nil"))));
    assert!(!t.contains(&ending(5, Value::str("end"))));
    assert!(!t.contains(&Value::str("end")));
    let built: std::collections::HashMap<usize, Value> = [1000, 8000]
        .into_iter()
        .map(|l| (l, ending(l, Value::str("end"))))
        .collect();
    zed_tests::scaling::check(
        "membership in two mutual definitions, by length",
        1000,
        |l| {
            assert!(!t.contains(&built[&l]));
        },
    );
}
